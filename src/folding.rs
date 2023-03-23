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

// TODO improve documentation
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
    // TODO what to do if a line never ends
    pub fn next_line(&mut self) -> Option<Result<&str, io::Error>> {
        enum Info {
            None,
            Cr,
            Crlf,
        }

        self.buffer.clear();

        if let Some(overflow) = self.overflow {
            self.buffer.push(overflow);
            self.overflow = None;
        }

        let mut last_byte = Info::None;

        for byte in &mut self.reader {
            let byte = match byte {
                Ok(byte) => byte,
                Err(err) => return Some(Err(err)),
            };

            match last_byte {
                Info::None => {
                    if byte == b'\r' {
                        last_byte = Info::Cr;
                    } else {
                        self.buffer.push(byte);
                    }
                }
                Info::Cr => {
                    if byte == b'\n' {
                        last_byte = Info::Crlf;
                    } else {
                        self.buffer.push(b'\r');
                        self.buffer.push(byte);
                        last_byte = Info::None;
                    }
                }
                Info::Crlf => {
                    if byte == b' ' || byte == b'\t' {
                        last_byte = Info::None;
                    } else {
                        self.overflow = Some(byte);
                        return Some(self.string_from_buffer());
                    }
                }
            }
        }

        match last_byte {
            Info::None => {}
            Info::Cr => self.buffer.push(b'\r'),
            Info::Crlf => {}
        }

        if self.buffer.is_empty() {
            None
        } else {
            Some(self.string_from_buffer())
        }
    }

    fn string_from_buffer(&self) -> io::Result<&str> {
        str::from_utf8(&self.buffer).map_err(|err| io::Error::new(io::ErrorKind::InvalidData, err))
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
        Self {
            writer,
            current_line_length: 0,
        }
    }

    // TODO document
    pub fn write(&mut self, mut string: &str) -> io::Result<()> {
        debug_assert!(!string.contains(crate::is_control));

        while string.len() >= FOLDING_LINE_LENGTH {
            let fold_index =
                floor_char_boundary(string, self.current_line_length + FOLDING_LINE_LENGTH);

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

// TODO rewrite tests
#[cfg(test)]
mod tests {
    mod unfold {
        use crate::folding::UnfoldingReader;

        #[test]
        fn lf_whitespace() {
            let expected = "NOTE:This is a long description that exists on a long line.";

            let folded =
                "NOTE:This is a long descrip\r\n tion that\r\n  exists o\r\n n a long line.";

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
                "NOTE:This is a long descrip\r\n\ttion that\r\n  exists o\r\n\tn a long line.";

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
                builder.extend_from_slice(b"\r\n\t");
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
NOTE:This is a long descrip\r
 tion that exists o\r
 n a long line.\r
NOTE:And here goes another\r
  long description on anoth\r
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
NOTE:This is a long descripti\r\n\ton that exists on a long line.\r
ANOTHER-NOTE:This is another \r\n long description that exists on a\r\n  long line";

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
