//! Line folding and unfolding.
//!
//! Implements the folding (and unfolding) procedure described in [section 3.1 of RFC
//! 5545][rfc5545sec3_1] and [section 3.2 of RFC 6350][rfc6350sec3_2].
//!
//! [rfc5545sec3_1]: https://www.rfc-editor.org/rfc/rfc5545#section-3.1
//! [rfc6350sec3_2]: https://www.rfc-editor.org/rfc/rfc6350#section-3.2

use std::{
    io::{self, BufRead, ErrorKind, Write},
    str,
};

// TODO improve documentation
/// Unfolding implementation.
///
/// # Usage
///
/// This is implemented as a streaming iterator. Call [`UnfoldingReader::next_line()`] to get a
/// reference to the next unfolded line. That reference will only be valid until
/// [`UnfoldingReader::next_line()`] is called again. This means that [`UnfoldingReader`]
/// cannot implement [`Iterator`], but it can still be used in a very similar manner.
///
/// # Some Notes on the Implementation
///
/// ###### Unfolding Incorrectly Folded UTF-8
///
/// This implementation will correctly restore lines that were folded in the middle of a UTF-8
/// multi-octet sequence.
///
/// ###### Line Terminators
///
//TODO get rid of this
///
/// Note that this implementation is not entirely compliant with [RFC 6350][sec3_2]. [RFC
/// 6350][sec3_2] specifies that CRLF is the only allowed line terminator while this implementation
/// also considers LF a line terminator.
///
/// [sec3_2]: https://www.rfc-editor.org/rfc/rfc6350#section-3.2
#[derive(Debug)]
pub struct UnfoldingReader<R: BufRead> {
    reader: R,
    buffer: Vec<u8>,
    ended: bool,
}

impl<R: BufRead> UnfoldingReader<R> {
    /// Creates a new [`UnfoldingReader`].
    pub fn new(reader: R) -> Self {
        Self {
            reader,
            buffer: Vec::new(),
            ended: false,
        }
    }
}

impl<R: BufRead> From<R> for UnfoldingReader<R> {
    fn from(reader: R) -> Self {
        Self::new(reader)
    }
}

impl<R: BufRead> UnfoldingReader<R> {
    // TODO what to do if a line never ends
    fn read_next_line_into_buffer(&mut self) -> Option<Result<(), io::Error>> {
        debug_assert!(self.buffer.is_empty());
        let mut last_was_newline = false;
        loop {
            let next_bytes = match self.reader.fill_buf() {
                Ok(next_bytes) => next_bytes,
                Err(err) => {
                    if err.kind() == ErrorKind::Interrupted {
                        continue;
                    }

                    return Some(Err(err));
                }
            };

            match next_bytes.first() {
                Some(byte) => {
                    if last_was_newline {
                        if *byte == b' ' || *byte == b'\t' {
                            self.reader.consume(1);
                            last_was_newline = false;
                            continue;
                        }

                        return Some(Ok(()));
                    }
                }
                // stream is exhausted
                None => return None,
            }

            let consumed = match memchr::memchr(b'\n', next_bytes) {
                Some(index) => {
                    self.buffer.extend_from_slice(&next_bytes[..index]);
                    if self.buffer.last() == Some(&b'\r') {
                        self.buffer.pop();
                    }
                    last_was_newline = true;

                    index + 1
                }
                None => {
                    self.buffer.extend_from_slice(next_bytes);
                    last_was_newline = false;

                    next_bytes.len()
                }
            };

            self.reader.consume(consumed);
        }
    }

    /// Returns the next line. Returns `None` if the end is reached.
    ///
    /// # Errors
    ///
    /// Will fail if ...
    ///  - ... an [`io::Error`] occurred.
    ///  - ... the line is invalid UTF-8.
    pub fn next_line(&mut self) -> Option<Result<&str, io::Error>> {
        if self.ended {
            return None;
        }

        self.buffer.clear();

        match self.read_next_line_into_buffer() {
            // everything fine
            Some(Ok(())) => (),
            // an error occurred => return the error
            Some(Err(err)) => return Some(Err(err)),
            // reached end of stream, return once more & in next iteration return None
            None => {
                self.ended = true;
            }
        }

        Some(str::from_utf8(&self.buffer).map_err(|_| io::Error::from(io::ErrorKind::InvalidData)))
    }
}

const FOLDING_LINE_LENGTH: usize = 75;

/// Writes lines to a [`Write`] and folds them as necessary.
///
/// Will only write valid UTF-8 to the underlying [`Write`].
#[derive(Debug)]
pub struct FoldingWriter<W: Write> {
    writer: W,
    // TODO this could be a u8
    current_line_length: usize,
}

impl<W: Write> FoldingWriter<W> {
    /// Create a new [`FoldingWriter`].
    pub fn new(writer: W) -> Self {
        Self { writer, current_line_length: 0 }
    }

    // TODO document
    pub fn write(&mut self, mut string: &str) -> io::Result<()> {
        debug_assert!(!string.contains(crate::is_control));

        while string.len() >= FOLDING_LINE_LENGTH {
            let fold_index = floor_char_boundary(string, self.current_line_length + FOLDING_LINE_LENGTH);

            self.writer.write_all(string[..fold_index].as_bytes())?;
            string = &string[fold_index..];

            self.end_line()?;
        }

        self.current_line_length += string.len();
        self.writer.write_all(string.as_bytes())
    }

    pub fn end_line(&mut self) -> io::Result<()> {
        self.current_line_length = 0;
        self.writer.write_all(b"\r\n")
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
        fn lf_whitespace() {
            let expected = "NOTE:This is a long description that exists on a long line.";

            let folded = "NOTE:This is a long descrip\n tion that\n  exists o\n n a long line.";

            let mut unfold = UnfoldingReader::new(folded.as_bytes());
            assert_eq!(
                unfold.next_line().expect("is some").expect("is ok"),
                expected
            );
            assert!(unfold.next_line().is_none());
        }

        #[test]
        fn crlf_tab() {
            let expected = "NOTE:This is a long description that exists on a long line.";

            let folded =
                "NOTE:This is a long descrip\r\n\ttion that\r\n\t exists o\r\n\tn a long line.";

            let mut unfold = UnfoldingReader::new(folded.as_bytes());
            assert_eq!(
                unfold.next_line().expect("is some").expect("is ok"),
                expected
            );
            assert!(unfold.next_line().is_none());
        }

        #[test]
        fn crlf_lf_whitespace_tab_mixed() {
            let expected = "NOTE:This is a long description that exists on a long line.";

            let folded =
                "NOTE:This is a long descrip\n\ttion that\r\n  exists o\r\n\tn a long line.";

            let mut unfold = UnfoldingReader::new(folded.as_bytes());
            assert_eq!(
                unfold.next_line().expect("is some").expect("is ok"),
                expected
            );
            assert!(unfold.next_line().is_none());
        }

        // This tests a note in 3.2 of RFC 6350:
        //
        // ```
        // Note: It is possible for very simple implementations to generate
        // improperly folded lines in the middle of a UTF-8 multi-octet
        // sequence. For this reason, implementations SHOULD unfold lines in
        // such a way as to properly restore the original sequence.
        // ```
        #[test]
        fn invalid_utf8_parsed_correctly() {
            let expected = "愿原力与你同在";

            let shitty_vcard = {
                let mut builder = "愿原力".as_bytes().to_owned();
                builder.push(228);
                builder.extend_from_slice(b"\n\t");
                builder.push(184);
                builder.push(142);
                builder.extend_from_slice("你同在".as_bytes());
                builder
            };

            let mut unfold = UnfoldingReader::new(shitty_vcard.as_slice());
            assert_eq!(
                unfold.next_line().expect("is some").expect("is ok"),
                expected
            );
            assert!(unfold.next_line().is_none());
        }

        #[test]
        fn invalid_utf8_2() {
            let not_so_funny =
                ['\u{f0}', '\u{9f}', '\r', '\n', ' ', '\u{98}', '\u{82}'].map(|c| c as u8);

            let mut reader = UnfoldingReader::new(not_so_funny.as_slice());
            let unfolded = reader
                .next_line()
                .expect("there is a line")
                .expect("no errors occurred");

            assert_eq!(unfolded, "😂");
        }

        #[test]
        fn test() {
            let example = "\
NOTE:This is a long descrip
 tion that exists o
 n a long line.
NOTE:And here goes another
  long description on anoth
 er long line.";

            let mut expected = [
                "NOTE:This is a long description that exists on a long line.",
                "NOTE:And here goes another long description on another long line.",
            ]
            .into_iter();

            let mut reader = UnfoldingReader::new(example.as_bytes());
            while let Some(next_line) = reader.next_line() {
                assert_eq!(next_line.unwrap(), expected.next().unwrap());
            }
        }

        #[test]
        fn multi_line_test() {
            let expected = vec![
                "NOTE:This is a long description that exists on a long line.",
                "ANOTHER-NOTE:This is another long description that exists on a long line",
            ];

            let folded = "\
NOTE:This is a long descripti\n\ton that exists on a long line.
ANOTHER-NOTE:This is another \r\n long description that exists on a\n  long line";

            let mut unfold = UnfoldingReader::new(folded.as_bytes());
            assert_eq!(
                unfold.next_line().expect("is some").expect("is ok"),
                expected[0]
            );
            assert_eq!(
                unfold.next_line().expect("is some").expect("is ok"),
                expected[1]
            );
            assert!(unfold.next_line().is_none());
        }
    }
}
