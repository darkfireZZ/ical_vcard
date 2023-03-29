//! Line folding and unfolding.
//!
//! Implements the folding (and unfolding) procedure described in [section 3.1 of RFC
//! 5545][rfc5545sec3_1] and [section 3.2 of RFC 6350][rfc6350sec3_2].
//!
//! [rfc5545sec3_1]: https://www.rfc-editor.org/rfc/rfc5545#section-3.1
//! [rfc6350sec3_2]: https://www.rfc-editor.org/rfc/rfc6350#section-3.2

use std::{
    io::{self, Read, Write},
    str,
};

/// Unfolding implementation.
///
/// # Usage
///
/// This is implemented as a streaming iterator. Call [`UnfoldingReader::next_line()`] to get a
/// reference to the next unfolded line. That reference will only be valid until
/// [`UnfoldingReader::next_line()`] as it takes a mutable borrow of the [`UnfoldingReader`].
///
/// This implementation will correctly restore lines that were folded in the middle of a UTF-8
/// multi-octet sequence.
///
/// # Security
///
/// [`UnfoldingReader::next_line()`] reads the next line of the underlying [`Read`] into memory. If
/// an [`UnfoldingReader`] is constructed from a [`Read`] that doesn't contain any (CRLF) line
/// breaks and is sufficiently large (or infinite), attempting to read the next line will cause the
/// heap to fill up completely.
#[derive(Debug)]
pub struct UnfoldingReader<R: Read> {
    reader: io::Bytes<R>,
    buffer: Vec<u8>,
    overflow: Option<u8>,
}

impl<R: Read> UnfoldingReader<R> {
    /// Creates a new [`UnfoldingReader`].
    pub fn new(reader: R) -> Self {
        Self {
            reader: reader.bytes(),
            buffer: Vec::new(),
            overflow: None,
        }
    }
}

impl<R: Read> UnfoldingReader<R> {
    /// Reads and returns the next line
    ///
    /// # Errors
    ///
    /// Fails if the underlying [`Read`] returns an error or if invalid UTF-8 is encountered.
    pub fn next_line(&mut self) -> Option<Result<&str, io::Error>> {
        #[derive(Eq, PartialEq)]
        enum State {
            None,
            Cr,
            Crlf,
        }

        self.buffer.clear();

        let mut state = State::None;

        if let Some(overflow) = self.overflow {
            if overflow == b'\r' {
                state = State::Cr;
            } else {
                self.buffer.push(overflow);
            }

            self.overflow = None;
        }

        for byte in &mut self.reader {
            let byte = match byte {
                Ok(byte) => byte,
                Err(err) => return Some(Err(err)),
            };

            match state {
                State::None => {
                    if byte == b'\r' {
                        state = State::Cr;
                    } else {
                        self.buffer.push(byte);
                    }
                }
                State::Cr => {
                    if byte == b'\n' {
                        state = State::Crlf;
                    } else {
                        self.buffer.push(b'\r');
                        self.buffer.push(byte);
                        state = State::None;
                    }
                }
                State::Crlf => {
                    if byte == b' ' || byte == b'\t' {
                        state = State::None;
                    } else {
                        self.overflow = Some(byte);
                        return Some(self.string_from_buffer());
                    }
                }
            }
        }

        if state == State::Cr {
            self.buffer.push(b'\r');
        }

        if !self.buffer.is_empty() || state == State::Crlf {
            Some(self.string_from_buffer())
        } else {
            None
        }
    }

    /// Helper function that creates a string from the buffer and returns it.
    fn string_from_buffer(&self) -> io::Result<&str> {
        str::from_utf8(&self.buffer).map_err(|err| io::Error::new(io::ErrorKind::InvalidData, err))
    }
}

const FOLDING_LINE_LENGTH: usize = 75;

/// Writes lines to a [`Write`] and folds them as necessary.
///
/// Guarantees that only valid UTF-8 is written to the underlying [`Write`].
#[derive(Debug)]
pub struct FoldingWriter<W: Write> {
    writer: W,
    current_line_length: u8,
}

impl<W: Write> FoldingWriter<W> {
    /// Create a new [`FoldingWriter`].
    pub fn new(writer: W) -> Self {
        Self {
            writer,
            current_line_length: 0,
        }
    }

    /// Appends a string to the current line.
    ///
    /// Expects that the first character of the string is not a space (`' '`) and not a tab (`'\t'`)
    /// and that the string contains no control characters other than tabs. This function will
    /// behave unexpectedly if above conditions are not met.
    ///
    /// # Errors
    ///
    /// Fails if the underlying [`Write`] returns an error.
    pub fn write(&mut self, mut string: &str) -> io::Result<()> {
        debug_assert!(!string.starts_with([' ', '\t']));
        debug_assert!(!string.contains(crate::is_control));

        while string.len() + usize::from(self.current_line_length) > FOLDING_LINE_LENGTH {
            let fold_index = floor_char_boundary(
                string,
                FOLDING_LINE_LENGTH - usize::from(self.current_line_length),
            );

            self.writer.write_all(string[..fold_index].as_bytes())?;
            string = &string[fold_index..];

            self.writer.write_all(b"\r\n ")?;
            self.current_line_length = 1;
        }

        self.current_line_length += u8::try_from(string.len())
            .expect("string.len() + self.current_line_length <= FOLDING_LINE_LENGTH = 75");
        self.writer.write_all(string.as_bytes())
    }

    /// Ends the current line.
    ///
    /// # Errors
    ///
    /// Fails if the underlying [`Write`] returns an error.
    pub fn end_line(&mut self) -> io::Result<()> {
        self.current_line_length = 0;
        self.writer.write_all(b"\r\n")
    }

    /// Calls flush on the underlying [`Write`] instance.
    pub fn flush(&mut self) -> io::Result<()> {
        self.writer.flush()
    }

    /// Returns a reference to the inner [`Write`].
    pub fn inner(&self) -> &W {
        &self.writer
    }

    /// Returns a mutable reference to the inner [`Write`].
    pub fn inner_mut(&mut self) -> &mut W {
        &mut self.writer
    }

    /// Returns the inner [`Write`].
    pub fn into_inner(self) -> W {
        self.writer
    }
}

// TODO replace all uses of this function with std::str::floor_char_boundary()
// as soon as it is stable
/// Finds the smallest char_boundary `<= index`.
fn floor_char_boundary(s: &str, index: usize) -> usize {
    let mut char_boundary = index;

    while !s.is_char_boundary(char_boundary) {
        char_boundary -= 1;
    }

    char_boundary
}

#[cfg(test)]
mod tests {
    mod unfold {
        use crate::folding::UnfoldingReader;

        #[test]
        fn empty() {
            assert!(UnfoldingReader::new("".as_bytes()).next_line().is_none());
        }

        #[test]
        fn first_line_empty() {
            let file = "\r\nsecond line is not empty";

            let expected_line_1 = "";
            let expected_line_2 = "second line is not empty";

            let mut reader = UnfoldingReader::new(file.as_bytes());

            let actual_line_1 = reader.next_line().unwrap().unwrap().to_owned();
            assert_eq!(actual_line_1, expected_line_1);

            let actual_line_2 = reader.next_line().unwrap().unwrap().to_owned();
            assert_eq!(actual_line_2, expected_line_2);

            assert!(reader.next_line().is_none());
        }

        #[test]
        fn just_newlines() {
            for num_lines in [0, 1, 2, 3, 4, 7, 14, 543, 2345] {
                let file = "\r\n".repeat(num_lines);
                let mut reader = UnfoldingReader::new(file.as_bytes());

                let mut counter = 0;
                while let Some(next_line) = reader.next_line() {
                    assert!(next_line.unwrap().is_empty());
                    counter += 1;
                }

                assert_eq!(counter, num_lines);
            }
        }

        #[test]
        fn single_line_spaces() {
            let expected = "NOTE:This is a long description that exists on a long line.";

            let folded =
                "NOTE:This is a long descrip\r\n tion that\r\n  exists o\r\n n a long line.";

            let mut unfold = UnfoldingReader::new(folded.as_bytes());

            assert_eq!(unfold.next_line().unwrap().unwrap(), expected);
            assert!(unfold.next_line().is_none());
        }

        #[test]
        fn single_line_tabs() {
            let expected = "NOTE:This is a long description that exists on a long line.";

            let folded =
                "NOTE:This is a long descrip\r\n\ttion that\r\n\t exists o\r\n\tn a long line.";

            let mut unfold = UnfoldingReader::new(folded.as_bytes());

            assert_eq!(unfold.next_line().unwrap().unwrap(), expected);
            assert!(unfold.next_line().is_none());
        }

        #[test]
        fn invalid_utf8_0() {
            let expected = "愿原力与你同在";

            let shitty_vcard = {
                let mut builder = Vec::new();
                builder.extend_from_slice("愿原力".as_bytes());
                builder.push(228);
                builder.extend_from_slice(b"\r\n\t");
                builder.push(184);
                builder.push(142);
                builder.extend_from_slice("你同在".as_bytes());
                builder
            };

            let mut unfold = UnfoldingReader::new(shitty_vcard.as_slice());

            assert_eq!(unfold.next_line().unwrap().unwrap(), expected);
            assert!(unfold.next_line().is_none());
        }

        #[test]
        fn invalid_utf8_1() {
            let not_so_funny =
                ['\u{f0}', '\u{9f}', '\r', '\n', '\t', '\u{98}', '\u{82}'].map(|c| c as u8);

            let mut reader = UnfoldingReader::new(not_so_funny.as_slice());
            let unfolded = reader.next_line().unwrap().unwrap();

            assert_eq!(unfolded, "😂");
        }

        #[test]
        fn multiple_lines() {
            let folded = "\
NOTE:This is a long descrip\r
\ttion that exists o\r
 n a long line.\r
NOTE:And here goes another\r
  long description on anoth\r
\ter long line.";

            let unfolded = [
                "NOTE:This is a long description that exists on a long line.",
                "NOTE:And here goes another long description on another long line.",
            ];

            let mut reader = UnfoldingReader::new(folded.as_bytes());
            for expected in unfolded {
                let actual = reader.next_line().unwrap().unwrap();
                assert_eq!(actual, expected);
            }
            assert!(reader.next_line().is_none());
        }

        #[test]
        fn a_bunch_of_crlfs() {
            let expected_count = 10;

            let mut counter = 0;

            let string = "\r\n".repeat(expected_count);
            let mut reader = UnfoldingReader::new(string.as_bytes());
            while let Some(next_line) = reader.next_line() {
                assert_eq!(next_line.unwrap(), "");
                counter += 1;
            }

            assert_eq!(counter, expected_count);
        }
    }

    mod fold {
        use {crate::folding::FoldingWriter, std::str};

        #[test]
        fn empty() {
            let mut buffer = Vec::new();

            let mut writer = FoldingWriter::new(&mut buffer);
            for _ in 0..100 {
                writer.write("").unwrap();
            }

            assert!(buffer.is_empty());
        }

        #[test]
        fn write_75_bytes() {
            let before = "abcdefghijklmno".repeat(5);
            assert_eq!(before.len(), 75);

            let after = {
                let mut buffer = Vec::new();
                let mut writer = FoldingWriter::new(&mut buffer);
                writer.write(&before).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(after, before);
        }

        #[test]
        fn write_once_ascii() {
            let first_line = "abcde".repeat(15);
            assert_eq!(first_line.len(), 75);

            let line = "ab".repeat(37);
            assert_eq!(line.len(), 74);

            let folded_line = {
                let mut folded_line = line.clone();
                folded_line.push_str("\r\n ");
                folded_line
            };

            let last_line = "this is the last line...";

            for num_lines in [1, 2, 3, 4, 5, 10, 20, 33, 47, 98, 155, 200] {
                let file = {
                    let mut file = String::new();
                    file.push_str(&first_line);
                    file.push_str(&line.repeat(num_lines - 1));
                    file.push_str(last_line);
                    file
                };

                let expected = {
                    let mut expected = String::new();
                    expected.push_str(&first_line);
                    expected.push_str("\r\n ");
                    expected.push_str(&folded_line.repeat(num_lines - 1));
                    expected.push_str(last_line);
                    expected
                };

                let actual = {
                    let mut buffer = Vec::new();
                    let mut writer = FoldingWriter::new(&mut buffer);
                    writer.write(&file).unwrap();
                    str::from_utf8(&buffer).unwrap().to_owned()
                };

                assert_eq!(actual, expected);
            }
        }

        #[test]
        fn write_once_utf8() {
            let num_chars_on_last_line = 7;

            let line = {
                // 🧪 is 4 bytes long, 18 * 4 = 72 bytes should be on each line
                let mut line = "🧪".repeat(18);
                line.push_str("\r\n ");
                line
            };

            let last_line = "🧪".repeat(num_chars_on_last_line);

            for num_lines in [1, 2, 3, 4, 5, 11, 54, 101] {
                let file = "🧪".repeat(18 * num_lines + num_chars_on_last_line);

                let expected = {
                    let mut expected = line.repeat(num_lines);
                    expected.push_str(&last_line);
                    expected
                };

                let actual = {
                    let mut buffer = Vec::new();
                    let mut writer = FoldingWriter::new(&mut buffer);
                    writer.write(&file).unwrap();
                    str::from_utf8(&buffer).unwrap().to_owned()
                };

                assert_eq!(actual, expected);
            }
        }
    }

    mod proptests {
        use {
            crate::{FoldingWriter, UnfoldingReader},
            proptest::{prop_assert, prop_assert_eq, proptest},
            std::str,
        };

        /// A regex that will match any line that can be written by a [`FoldingWriter`].
        ///
        /// See [`FoldingWriter::write`] for more information.
        const VALID_LINE: &'static str = r"(?:[^\p{C} ][\P{C}\t]*)?";

        proptest! {
            #[test]
            fn folding_is_correct(lines in proptest::collection::vec(VALID_LINE, 1..100)) {
                let written = {
                    let mut buffer = Vec::new();
                    let mut writer = FoldingWriter::new(&mut buffer);
                    for line in &lines {
                        writer.write(line).unwrap();
                        writer.end_line().unwrap();
                    }

                    str::from_utf8(&buffer).unwrap().to_owned()
                };

                let mut previous_line_length = 0;
                for line in written.split("\r\n") {
                    assert!(line.len() <= 75);

                    // if the line is folded
                    if line.starts_with([' ', '\t']) {
                        let first_char_len = line[1..].chars().next().map_or(0, char::len_utf8);
                        assert!(first_char_len + previous_line_length > 75);
                    }

                    previous_line_length = line.len();
                }
            }
        }

        proptest! {
            #[test]
            fn fold_and_unfold_random(lines in proptest::collection::vec(VALID_LINE, 1..100)) {
                let written = {
                    let mut buffer = Vec::new();
                    let mut writer = FoldingWriter::new(&mut buffer);
                    for line in &lines {
                        writer.write(line).unwrap();
                        writer.end_line().unwrap();
                    }
                    prop_assert!(str::from_utf8(&buffer).is_ok());
                    buffer
                };

                let mut reader = UnfoldingReader::new(written.as_slice());
                for original_line in &lines {
                    let read_line = reader.next_line().unwrap().unwrap();
                    prop_assert_eq!(read_line, original_line);
                }

                prop_assert!(reader.next_line().is_none());
            }
        }
    }
}
