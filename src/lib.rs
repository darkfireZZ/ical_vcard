#![doc = include_str!("../README.md")]
#![deny(unsafe_code)]
#![deny(clippy::all)]
#![warn(clippy::cargo)]
#![warn(missing_docs)]

use {
    crate::folding::{FoldingWriter, UnfoldingReader},
    std::{
        borrow::{Borrow, Cow},
        fmt::{self, Display},
        hash::{Hash, Hasher},
        io::{self, Read, Write},
        iter::Iterator,
    },
    thiserror::Error,
};

mod folding;

/// Parses an iCalendar or vCard file.
///
/// To achieve minimal memory usage, parsing is done one content line at a time. Use
/// [`Parser::parse_next_line()`] to parse the next content line.
///
/// [`Parser`] also implements [`Iterator`]. This makes it possible to use [`Parser`] in
/// `for`-loops and apply all of the different [`Iterator`] adapters such as [`Iterator::map()`] and
/// [`Iterator::filter()`]. Note however that this comes at a cost in performance.
/// [`Parser::parse_next_line()`] makes a minimal number of heap allocations by reusing the same
/// internal buffer for all content lines. As the [`Iterator`] trait does not allow items to borrow
/// from the iterator itself, all items returned by the [`Iterator`] implementation need to be
/// allocated on the heap.
///
/// Depending on the [`Read`] implementation used, each call to [`reader::read()`][Read::read] (of
/// which this function does many), may involve a system call, and therefore, using something that
/// implements [`io::BufRead`], such as [`io::BufReader`], to construct the [`Parser`] will be more
/// efficient.
///
/// This implementation will unfold content lines correctly. Even if they were folded in the middle
/// of a UTF-8 multi-byte character.
///
// TODO also allow LF line breaks
/// Only CRLF sequences are interpreted as linebreaks, both for unfolding and as indicator of the
/// end of a content line.
///
/// # Security
///
/// [`Parser::parse_next_line()`] (and hence [`Parser::next()`] too) reads the next line of the
/// underlying [`Read`] instance into memory to parse it. If the next line is very long (or
/// infinitely long), attempting to read the next content line will completely fill up the heap
/// memory.
///
/// # Example
///
/// The following example illustrates how to parse a simple vCard file:
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use ical_vcard::{Contentline, Identifier, Param, ParamValue, Parser, Value};
///
/// let vcard_file = String::from("\
/// BEGIN:VCARD\r
/// VERSION:4.0\r
/// namegroup.FN:Michelle de Pierre\r
/// namegroup.N:de Pierre;Michelle;;;B.Sc.\r
/// EMAIL;TYPE=work:michelle.depierre@example.com\r
/// GENDER:F\r
/// BDAY:--0707\r
/// END:VCARD\r
/// ");
///
/// let contentlines = Parser::new(vcard_file.as_bytes()).collect::<Result<Vec<_>, _>>()?;
///
/// let email_line = contentlines.iter().find(|contentline| contentline.name == "EMAIL").unwrap();
/// assert_eq!(email_line.value, "michelle.depierre@example.com");
///
/// let third_line = &contentlines[2];
/// assert_eq!(third_line.name, "FN");
/// assert_eq!(third_line.value, "Michelle de Pierre");
/// #
/// # Ok(())
/// # }
/// ```
#[derive(Debug)]
pub struct Parser<R: Read> {
    unfolder: UnfoldingReader<R>,
}

impl<R: Read> Parser<R> {
    /// Creates a new [`Parser`].
    pub fn new(reader: R) -> Self {
        Self {
            unfolder: UnfoldingReader::new(reader),
        }
    }

    /// Parses the next content line.
    ///
    /// Returns [`None`] if the [`Parser`] is exhausted.
    ///
    /// # Errors
    ///
    /// A [`ParseError`] will be returned if an [`io::Error`] occurred or if a syntactically invalid
    /// content line was encountered.
    pub fn parse_next_line(&mut self) -> Option<Result<Contentline, ParseError>> {
        match self.unfolder.next_line()? {
            Ok(next_line) => Some(Contentline::parse(next_line).map_err(|err| err.into())),
            Err(err) => Some(Err(err.into())),
        }
    }
}

impl<R: Read> Iterator for Parser<R> {
    type Item = Result<Contentline<'static>, ParseError>;
    fn next(&mut self) -> Option<Self::Item> {
        self.parse_next_line()
            .map(|result| result.map(|contentline| contentline.into_owned()))
    }
}

/// The error type returned if parsing fails.
#[derive(Debug, Error)]
pub enum ParseError {
    /// An IO error occurred while parsing.
    #[error(transparent)]
    IoError(#[from] io::Error),
    /// An invalid content line was encountered.
    #[error(transparent)]
    InvalidContentline(#[from] ParseContentlineError),
}

/// Writes an iCalendar or vCard file.
///
/// Folds all content lines to lines that are no longer than 75 bytes (not including line breaks). A
/// CRLF line break is appended to each content line.
///
/// [`Writer`] will always output valid UTF-8 to the underlying [`Write`].
///
/// # Performance
///
/// It can be excessively inefficient to work directly with something that implements [`Write`]. For
/// example, every call to write on [`std::net::TcpStream`] results in a system call. Wrapping
/// `writer` in a [`io::BufWriter`] may improve performance significantly.
///
/// # Example
///
/// The following example illustrates how to write a simple vCard file:
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// #
/// use ical_vcard::{Contentline, Identifier, Param, ParamValue, Value, Writer};
///
/// let contentlines = [
///     Contentline {
///         group: None,
///         name: Identifier::new_borrowed("BEGIN")?,
///         params: Vec::new(),
///         value: Value::new_borrowed("VCARD")?,
///     },
///     Contentline {
///         group: None,
///         name: Identifier::new_borrowed("FN")?,
///         params: Vec::new(),
///         value: Value::new_borrowed("Mr. John Example")?,
///     },
///     Contentline {
///         group: None,
///         name: Identifier::new_borrowed("BDAY")?,
///         params: vec![Param::new(
///             Identifier::new_borrowed("VALUE")?,
///             vec![ParamValue::new_borrowed("date-and-or-time")?],
///         )?],
///         value: Value::new_borrowed("20230326")?,
///     },
///     Contentline {
///         group: None,
///         name: Identifier::new_borrowed("END")?,
///         params: Vec::new(),
///         value: Value::new_borrowed("VCARD")?,
///     },
/// ];
///
/// // For the sake of simplicity and testability, the vCard is written to a Vec. However, in a
/// // real application, one would probably write it to disk or do some further processing (e.g.
/// // compression)
/// let vcard = {
///     let mut buffer = Vec::new();
///     let mut writer = Writer::new(&mut buffer);
///     writer.write_all(contentlines)?;
///     buffer
/// };
///
/// let expected = "\
/// BEGIN:VCARD\r
/// FN:Mr. John Example\r
/// BDAY;VALUE=date-and-or-time:20230326\r
/// END:VCARD\r
/// ".as_bytes();
///
/// assert_eq!(vcard, expected);
/// #
/// # Ok(())
/// # }
/// ```
pub struct Writer<W: Write> {
    folder: FoldingWriter<W>,
}

impl<W: Write> Writer<W> {
    /// Creates a new [`Writer`].
    ///
    /// Note that you can also pass `&mut W` instead of `W` for any `W` that implements [`Write`].
    pub fn new(writer: W) -> Self {
        Self {
            folder: FoldingWriter::new(writer),
        }
    }

    /// Writes a single content line.
    ///
    /// Flushes the underlying [`Write`] afterwards.
    ///
    /// # Errors
    ///
    /// Fails in case of an [`io::Error`].
    pub fn write(&mut self, contentline: &Contentline) -> io::Result<()> {
        contentline.write(|s| self.folder.write(s))?;
        self.folder.end_line()?;
        self.folder.flush()
    }

    /// Writes a sequence of contentlines.
    ///
    /// Flushes the underlying [`Write`] afterwards.
    ///
    /// # Errors
    ///
    /// Fails in case of an [`io::Error`].
    pub fn write_all<'a, C, I>(&mut self, contentlines: I) -> io::Result<()>
    where
        C: Borrow<Contentline<'a>>,
        I: IntoIterator<Item = C>,
    {
        for line in contentlines {
            line.borrow().write(|s| self.folder.write(s))?;
            self.folder.end_line()?;
        }

        self.folder.flush()
    }

    /// Returns a reference to the inner [`Write`].
    pub fn inner(&self) -> &W {
        self.folder.inner()
    }

    /// Returns a mutable reference to the inner [`Write`].
    pub fn inner_mut(&mut self) -> &mut W {
        self.folder.inner_mut()
    }

    /// Returns the inner [`Write`]
    pub fn into_inner(self) -> W {
        self.folder.into_inner()
    }
}

/// The basic unit of a vCard or iCalendar file.
///
/// A content line consists of 4 parts:
///
/// 1. A `name`
/// 2. A `value`
/// 3. Optionally, a `group` which can be used to group related content lines
/// 4. Optionally, a list of parameters to add meta-information or additional details that don't fit
///    into the `value` field particularly well
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Contentline<'a> {
    /// The group of the content line.
    pub group: Option<Identifier<'a>>,
    /// The name of the content line.
    pub name: Identifier<'a>,
    /// The parameters of the content line.
    pub params: Vec<Param<'a>>,
    /// The value of the content line.
    pub value: Value<'a>,
}

impl<'a> Contentline<'a> {
    /// Parses a [`Contentline`].
    ///
    /// # Errors
    ///
    /// Fails if the given content line is incorrectly formatted.
    fn parse(mut contentline: &'a str) -> Result<Self, ParseContentlineError> {
        let error = || ParseContentlineError {
            invalid_contentline: contentline.to_owned(),
        };

        let (group, name) = parse_group_and_name(&mut contentline).map_err(|_| error())?;
        let params = parse_params(&mut contentline).map_err(|_| error())?;

        if !contentline.starts_with(':') {
            return Err(error());
        }
        contentline = &contentline[1..];

        let value = parse_value(&mut contentline).map_err(|_| error())?;

        Ok(Contentline {
            group,
            name,
            params,
            value,
        })
    }

    /// Writes this [`Contentline`] using a given function.
    ///
    /// This implementation has the advantage to be compatible with both the [`io::Write`] trait
    /// and the [`fmt::Write`] trait. Therefore, this implementation can be used to write a
    /// [`Contentline`] to a file or any other [`io::Write`], but also to implement
    /// [`fmt::Display`].
    ///
    /// # Errors
    ///
    /// Fails if the writer function fails.
    fn write<E, W>(&self, mut writer: W) -> Result<(), E>
    where
        W: FnMut(&str) -> Result<(), E>,
    {
        if let Some(group) = &self.group {
            write_identifier(group, &mut writer)?;
            writer(".")?;
        }

        write_identifier(&self.name, &mut writer)?;
        write_params(&self.params, &mut writer)?;

        writer(":")?;

        write_value(&self.value, &mut writer)?;

        Ok(())
    }

    /// Allocates the fields of this [`Contentline`].
    pub fn into_owned(self) -> Contentline<'static> {
        Contentline {
            group: self.group.map(Identifier::into_static),
            name: self.name.into_static(),
            // TODO do this in-place
            params: self.params.into_iter().map(Param::into_owned).collect(),
            value: self.value.into_static(),
        }
    }
}

// TODO implement FromStr for Contentline

impl<'a> Display for Contentline<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.write(|s| f.write_str(s))
    }
}

/// Indicates a failure to parse a [`Contentline`].
#[derive(Debug, Error)]
pub struct ParseContentlineError {
    invalid_contentline: String,
}

impl ParseContentlineError {
    /// Returns the contentline that caused the error.
    pub fn invalid_contentline(&self) -> &str {
        &self.invalid_contentline
    }
}

impl Display for ParseContentlineError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO: There could be different error messages explaining which part of the contentline
        // is invalid
        write!(f, "invalid contentline")
    }
}

macro_rules! empty {
    () => {};
}

macro_rules! cow_wrapper {
    (
        @metainfo {
            case_sensitive: true,
            $($metainfo:tt)*
        };

        $($remainder:tt)*
    ) => {
        cow_wrapper! {
            @metainfo {
                is_case_sensitive: empty!{},
                $($metainfo)*
            };

            $($remainder)*
        }
    };
    (
        @metainfo {
            case_sensitive: false,
            $($metainfo:tt)*
        };

        $($remainder:tt)*
    ) => {
        cow_wrapper! {
            @metainfo {
                is_not_case_sensitive: empty!{},
                $($metainfo)*
            };

            $($remainder)*
        }
    };
    (
        @metainfo {
            $(is_case_sensitive: $is_case_sensitive:item,)?
            $(is_not_case_sensitive: $is_not_case_sensitive:item,)?
            param_name: $param_name:ident,
            doc_name: $doc_name:literal,
            error_name: $error_name:ident,
            error_message: $error_message:literal,
            valid_if: $valid_if:literal,
        };

        pub struct $type_name:ident { ... }

        impl $_type_name:ident {
            pub const fn is_valid($_param_name:ident: &str) -> bool {
                $( $is_valid_impl:tt )+
            }
        }
    ) => {
        $( /* if */ $is_not_case_sensitive
            #[derive(Hash)]
        )*
        #[doc = concat!("A [`Cow<str>`] wrapper that is guaranteed to be a valid ", $doc_name, ".")]
        ///
        #[doc = concat!("A ", $doc_name, " is considered valid if it ", $valid_if, ".")]
        #[derive(Clone, Debug, Eq)]
        pub struct $type_name<'a> {
            value: Cow<'a, str>,
        }

        impl $type_name<'static> {
            #[doc = concat!("Creates a new [`", stringify!($type_name), "`] from an owned [`String`].")]
            ///
            #[doc = concat!("This is a shorthand for `", stringify!($type_name), "::new(Cow::Owned(", stringify!($param_name), ")`.")]
            ///
            /// # Errors
            ///
            #[doc = concat!("Fails if `", stringify!($param_name), "` is not a valid ", $doc_name, ".")]
            pub fn new_owned($param_name: String) -> Result<Self, $error_name> {
                Self::new(Cow::Owned($param_name))
            }
        }

        impl<'a> $type_name<'a> {
            #[doc = concat!("Creates a new [`", stringify!($type_name), "`] from a string slice.")]
            ///
            #[doc = concat!("This is a shorthand for `", stringify!($type_name), "::new(Cow::Borrowed(", stringify!($param_name), ")`.")]
            ///
            /// # Errors
            ///
            #[doc = concat!("Fails if `", stringify!($param_name), "` is not a valid ", $doc_name, ".")]
            pub const fn new_borrowed($param_name: &'a str) -> Result<Self, $error_name> {
                if Self::is_valid($param_name) {
                    Ok(Self {
                        value: Cow::Borrowed($param_name),
                    })
                } else {
                    Err($error_name)
                }
            }

            #[doc = concat!("Creates a new [`", stringify!($type_name), "`].")]
            ///
            /// # Errors
            ///
            #[doc = concat!("Fails if `", stringify!($param_name), "` is not a valid ", $doc_name, ".")]
            pub fn new($param_name: Cow<'a, str>) -> Result<Self, $error_name> {
                if Self::is_valid(&$param_name) {
                    Ok(Self { value: $param_name })
                } else {
                    Err($error_name)
                }
            }

            #[doc = concat!("Creates a new [`", stringify!($type_name), "`]. Does not check if `", stringify!($param_name), "` is valid.")]
            ///
            #[doc = concat!("It is up to the caller to ensure that `", stringify!($param_name), "` is a valid ", $doc_name, ".")]
            #[doc = concat!("See also [`", stringify!($type_name), "::is_valid()`].")]
            pub const fn new_unchecked($param_name: Cow<'a, str>) -> Self {
                Self { value: $param_name }
            }

            $( /* if */ $is_not_case_sensitive
                #[doc = concat!("Extracts a string slice containing the ", $doc_name, ".")]
                pub fn as_str(&self) -> &str {
                    &self.value
                }
            )?

            #[doc = concat!("Converts this ", $doc_name, " to an [`", stringify!($type_name), "`] with a `'static` lifetime.")]
            ///
            #[doc = concat!("Allocates this [`", stringify!($type_name), "`] if necessary.")]
            pub fn into_static(self) -> $type_name<'static> {
                $type_name::<'static> {
                    value: Cow::Owned(self.value.into_owned()),
                }
            }

            #[doc = concat!("Returns true if `", stringify!($param_name), "` is a valid ", $doc_name, ".")]
            ///
            #[doc = concat!("A ", $doc_name, " is considered valid if it ", $valid_if, ".")]
            pub const fn is_valid($param_name: &str) -> bool {
                $( $is_valid_impl )+
            }
        }

        impl<'a> PartialEq for $type_name<'a> {
            fn eq(&self, other: &Self) -> bool {
                *self == other.value.as_ref()
            }
        }

        impl<'a> PartialEq<String> for $type_name<'a> {
            fn eq(&self, other: &String) -> bool {
                self == other.as_str()
            }
        }

        impl<'a> PartialEq<&str> for $type_name<'a> {
            fn eq(&self, other: &&str) -> bool {
                self == *other
            }
        }

        impl<'a> PartialEq<str> for $type_name<'a> {
            fn eq(&self, other: &str) -> bool {
                $( /* if */ $is_case_sensitive
                    self.value.eq_ignore_ascii_case(other)
                )?
                $( /* if */ $is_not_case_sensitive
                    self.value == other
                )?
            }
        }

        $( /* if */ $is_case_sensitive
            impl<'a> Hash for $type_name<'a> {
                fn hash<H: Hasher>(&self, state: &mut H) {
                    // implementation is mostly the same as in std::str
                    for c in self.value.as_bytes() {
                        c.to_ascii_uppercase().hash(state);
                    }
                    state.write_u8(0xff);
                }
            }
        )?

        impl<'a> TryFrom<Cow<'a, str>> for $type_name<'a> {
            type Error = $error_name;
            fn try_from($param_name: Cow<'a, str>) -> Result<Self, Self::Error> {
                Self::new($param_name)
            }
        }

        impl<'a> TryFrom<&'a str> for $type_name<'a> {
            type Error = $error_name;
            fn try_from($param_name: &'a str) -> Result<Self, Self::Error> {
                Self::new_borrowed($param_name)
            }
        }

        impl TryFrom<String> for $type_name<'static> {
            type Error = $error_name;
            fn try_from($param_name: String) -> Result<Self, Self::Error> {
                Self::new_owned($param_name)
            }
        }

        $( /* if */ $is_not_case_sensitive
            impl<'a> AsRef<str> for $type_name<'a> {
                fn as_ref(&self) -> &str {
                    self.as_str()
                }
            }

            impl<'a> From<$type_name<'a>> for Cow<'a, str> {
                fn from($param_name: $type_name<'a>) -> Self {
                    $param_name.value
                }
            }
        )?

        impl From<$type_name<'_>> for String {
            fn from($param_name: $type_name) -> Self {
                $( /* if */ $is_case_sensitive
                    $param_name.value.to_ascii_uppercase()
                )?
                $( /* if */ $is_not_case_sensitive
                    $param_name.value.into_owned()
                )?
            }
        }

        impl<'a> Display for $type_name<'a> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                let value = {
                    $( /* if */ $is_case_sensitive
                       &self.value.to_ascii_uppercase()
                    )*
                    $( /* if */ $is_not_case_sensitive
                       &self.value
                    )?
                };
                write!(f, "{}", value)
            }
        }

        #[doc = concat!("Indicates an attempt to create a [`", stringify!($type_name), "`] from an invalid ", $doc_name, ".")]
        ///
        #[doc = concat!("A [`", stringify!($type_name), "`] is considered valid if ", $valid_if, ".")]
        #[derive(Debug, Error)]
        pub struct $error_name;

        impl Display for $error_name {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, $error_message)
            }
        }
    };
}

cow_wrapper! {
    @metainfo {
        case_sensitive: true,
        param_name: identifier,
        doc_name: "identifier",
        error_name: InvalidIdentifier,
        error_message: "an identifier can only contain alphanumeric characters and dashes ('-')",
        valid_if: "is not empty and all characters are alphanumeric ascii characters or dashes (`-`)",
    };

    pub struct Identifier { ... }

    impl Identifier {
        pub const fn is_valid(identifier: &str) -> bool {
            if identifier.is_empty() {
                return false;
            }

            let identifier = identifier.as_bytes();

            let mut index = 0;
            while index < identifier.len() {
                if !is_identifier_char(identifier[index]) {
                    return false;
                }
                index += 1;
            }

            true
        }
    }
}

/// A single parameter of a [`Contentline`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Param<'a> {
    name: Identifier<'a>,
    values: Vec<ParamValue<'a>>,
}

impl<'a> Param<'a> {
    /// Creates a new [`Param`].
    ///
    /// # Errors
    ///
    /// Fails if the values [`Vec`] is empty.
    pub fn new(name: Identifier<'a>, values: Vec<ParamValue<'a>>) -> Result<Self, InvalidParam> {
        if values.is_empty() {
            Err(InvalidParam)
        } else {
            Ok(Self { name, values })
        }
    }

    /// Allocates the fields of this [`Param`].
    fn into_owned(self) -> Param<'static> {
        Param {
            name: self.name.into_static(),
            // TODO do this in-place
            values: self
                .values
                .into_iter()
                .map(ParamValue::into_static)
                .collect(),
        }
    }
}

/// Indicates a failed attempt to create a [`Param`].
///
/// This happens when it is attempted to create a [`Param`] without any value.
#[derive(Debug, Error)]
pub struct InvalidParam;

impl Display for InvalidParam {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "a parameter must have at least 1 value")
    }
}

cow_wrapper! {
    @metainfo {
        case_sensitive: false,
        param_name: value,
        doc_name: "parameter value",
        error_name: InvalidParamValue,
        error_message: "a parameter value cannot contain any ascii control characters except horizontal tabs and linefeeds",
        valid_if: r"contains no ascii control characters except horizontal tabs (`'\t'`) and linefeeds (`'\n'`)",
    };

    pub struct ParamValue { ... }

    impl ParamValue {
        pub const fn is_valid(value: &str) -> bool {
            let value = value.as_bytes();

            let mut index = 0;
            while index < value.len() {
                if is_control(value[index]) && value[index] != b'\n' {
                    return false;
                }
                index += 1;
            }

            true
        }
    }
}

cow_wrapper! {
    @metainfo {
        case_sensitive: false,
        param_name: value,
        doc_name: "value",
        error_name: InvalidValue,
        error_message: "a value cannot contain any ascii control characters except horizontal tabs",
        valid_if: r"contains no ascii control characters except horizontal tabs (`'\t'`)",
    };

    pub struct Value { ... }

    impl Value {
        pub const fn is_valid(value: &str) -> bool {
            let value = value.as_bytes();

            let mut index = 0;
            while index < value.len() {
                if is_control(value[index]) {
                    return false;
                }
                index += 1;
            }

            true
        }
    }
}

//====================// contentline parsing //====================//

/// Parses group and name of a content line.
///
/// # Errors
///
/// Fails if the group or the name of the content line are incorrectly formatted.
fn parse_group_and_name<'a>(
    contentline: &mut &'a str,
) -> Result<(Option<Identifier<'a>>, Identifier<'a>), IntermediateParsingError> {
    let identifier = parse_identifier(contentline)?;

    if contentline.starts_with('.') {
        *contentline = &contentline[1..];
        let group = Some(identifier);
        let name = parse_identifier(contentline)?;

        Ok((group, name))
    } else {
        let group = None;
        let name = identifier;

        Ok((group, name))
    }
}

/// Parses a list of [`Param`]s.
///
/// # Errors
///
/// Fails if any parameter is incorrectly formatted.
fn parse_params<'a>(contentline: &mut &'a str) -> Result<Vec<Param<'a>>, IntermediateParsingError> {
    let mut params = Vec::new();

    while contentline.starts_with(';') {
        *contentline = &contentline[1..];
        params.push(parse_param(contentline)?);
    }

    Ok(params)
}

/// Parses a [`Param`].
///
/// # Errors
///
/// Fails if the parameter is incorrectly formatted.
fn parse_param<'a>(contentline: &mut &'a str) -> Result<Param<'a>, IntermediateParsingError> {
    let param_name = parse_identifier(contentline)?;

    if !contentline.starts_with('=') {
        return Err(IntermediateParsingError);
    }
    *contentline = &contentline[1..];

    let param_values = parse_param_values(contentline)?;

    Ok(Param {
        name: param_name,
        values: param_values,
    })
}

/// Parses a list of [`ParamValue`]s.
///
/// # Errors
///
/// Fails if the list is empty or if there is an error parsing a [`ParamValue`].
fn parse_param_values<'a>(
    contentline: &mut &'a str,
) -> Result<Vec<ParamValue<'a>>, IntermediateParsingError> {
    let mut param_values = vec![parse_param_value(contentline)?];

    while contentline.starts_with(',') {
        *contentline = &contentline[1..];
        param_values.push(parse_param_value(contentline)?);
    }

    Ok(param_values)
}

/// Parses a [`ParamValue`].
///
/// # Errors
///
/// Fails if the first character is a double quote (`"`) but there is not closing double quote.
fn parse_param_value<'a>(
    contentline: &mut &'a str,
) -> Result<ParamValue<'a>, IntermediateParsingError> {
    let param_value = if contentline.starts_with('"') {
        parse_quoted_string(contentline)?
    } else {
        parse_paramtext(contentline)
    };

    Ok(ParamValue { value: param_value })
}

/// Parses a `quoted-string`.
///
/// Expects that the first character of the argument is a double quote (`"`). Will behave
/// unexpectedly if the first character is NOT a double quote.
///
/// ABNF from [RFC 5545][rfc5545]:
///
/// ```text
/// quoted-string = DQUOTE *QSAFE-CHAR DQUOTE
/// ```
///
/// [rfc5545]: https://www.rfc-editor.org/rfc/rfc5545
fn parse_quoted_string<'a>(
    contentline: &mut &'a str,
) -> Result<Cow<'a, str>, IntermediateParsingError> {
    debug_assert!(contentline.starts_with('"'));

    *contentline = &contentline[1..];

    let quoted_string_length = contentline
        .bytes()
        .position(|c| !is_qsafe_char(c))
        .ok_or(IntermediateParsingError)?;
    if &contentline[quoted_string_length..quoted_string_length + 1] == "\"" {
        let quoted_string = parse_param_value_rfc6868(&contentline[..quoted_string_length]);
        *contentline = &contentline[quoted_string_length + 1..];
        Ok(quoted_string)
    } else {
        Err(IntermediateParsingError)
    }
}

/// Parses a `paramtext`.
///
/// ABNF from [RFC 5545][rfc5545]:
///
/// ```text
/// paramtext = *SAFE-CHAR
/// ```
///
/// [rfc5545]: https://www.rfc-editor.org/rfc/rfc5545
fn parse_paramtext<'a>(contentline: &mut &'a str) -> Cow<'a, str> {
    let paramtext_length = contentline
        .bytes()
        .position(|c| !is_safe_char(c))
        .unwrap_or(contentline.len());

    let paramtext = parse_param_value_rfc6868(&contentline[..paramtext_length]);

    *contentline = &contentline[paramtext_length..];

    paramtext
}

/// Takes a `paramtext` of the value of a `quoted-string` and returns a [`String`] where all the
/// escape sequences defined in [RFC 6868][rfc6868] are parsed correctly.
///
/// [rfc6868]: https://www.rfc-editor.org/rfc/rfc6868
fn parse_param_value_rfc6868(param_value: &str) -> Cow<str> {
    debug_assert!(param_value.bytes().all(is_qsafe_char));

    let param_value = match param_value.find('^') {
        Some(next_index) => {
            let mut result = String::with_capacity(param_value.len());
            let mut param_value = param_value;
            let mut next_index = Some(next_index);

            while let Some(index) = next_index {
                result.push_str(&param_value[..index]);
                match param_value.get(index + 1..index + 2) {
                    Some(escaped_char) => {
                        match escaped_char {
                            "n" => result.push('\n'),
                            "'" => result.push('\"'),
                            "^" => result.push('^'),
                            other => {
                                result.push('^');
                                result.push_str(other);
                            }
                        }
                        param_value = &param_value[index + 2..];
                    }
                    None => {
                        result.push('^');
                        param_value = &param_value[index + 1..];
                    }
                }
                next_index = param_value.find('^');
            }

            result.push_str(param_value);

            Cow::Owned(result)
        }
        None => Cow::Borrowed(param_value),
    };

    debug_assert!(ParamValue::is_valid(&param_value));

    param_value
}

/// Parses a [`Value`].
///
/// # Errors
///
/// Fails if the argument contains control characters other than horizontal tabs.
fn parse_value<'a>(contentline: &mut &'a str) -> Result<Value<'a>, IntermediateParsingError> {
    if Value::is_valid(contentline) {
        let value = Value {
            value: Cow::Borrowed(contentline),
        };
        *contentline = "";

        Ok(value)
    } else {
        Err(IntermediateParsingError)
    }
}

/// Parses an [`Identifier`].
///
/// # Errors
///
/// Fails if the first char of the argument is not [`is_identifier_char()`].
fn parse_identifier<'a>(
    contentline: &mut &'a str,
) -> Result<Identifier<'a>, IntermediateParsingError> {
    let identifier_length = contentline
        .bytes()
        .position(|c| !is_identifier_char(c))
        .unwrap_or(contentline.len());

    // identifier cannot be an empty string
    if identifier_length == 0 {
        Err(IntermediateParsingError)
    } else {
        let identifier = &contentline[..identifier_length];
        *contentline = &contentline[identifier_length..];

        debug_assert!(Identifier::is_valid(identifier));
        let identifier = Identifier {
            value: Cow::Borrowed(identifier),
        };

        Ok(identifier)
    }
}

/// An zero-sized error type used internally to indicate parsing errors.
struct IntermediateParsingError;

//====================// contentline writing //====================//

/// Writes a parameter list.
///
/// # Errors
///
/// Fails if the writer function returns an error.
fn write_params<E, W>(params: &Vec<Param>, writer: &mut W) -> Result<(), E>
where
    W: FnMut(&str) -> Result<(), E>,
{
    for param in params {
        writer(";")?;
        write_identifier(&param.name, writer)?;
        writer("=")?;
        write_param_values(&param.values, writer)?;
    }

    Ok(())
}

/// Writes a list of parameter values.
///
/// Expects that `values` is non-empty.
///
/// # Errors
///
/// Fails if the writer function returns an error.
fn write_param_values<E, W>(values: &Vec<ParamValue>, writer: &mut W) -> Result<(), E>
where
    W: FnMut(&str) -> Result<(), E>,
{
    debug_assert!(!values.is_empty());

    write_param_value(&values[0], writer)?;

    for param_value in &values[1..] {
        writer(",")?;
        write_param_value(param_value, writer)?;
    }

    Ok(())
}

/// Writes a single parameter value.
///
/// # Errors
///
/// Fails if the writer function returns an error.
fn write_param_value<E, W>(value: &ParamValue, writer: &mut W) -> Result<(), E>
where
    W: FnMut(&str) -> Result<(), E>,
{
    if value.value.contains(|c| c == ';' || c == ':' || c == '.') {
        writer("\"")?;
        write_param_value_rfc6868(&value.value, writer)?;
        writer("\"")
    } else {
        write_param_value_rfc6868(&value.value, writer)
    }
}

/// Writes a `paramtext` or a `quoted-string` and escapes characters as specified in [RFC
/// 6868][rfc6868].
///
/// # Errors
///
/// Fails if the writer function returns an error.
///
/// [rfc6868]: https://www.rfc-editor.org/rfc/rfc6868
fn write_param_value_rfc6868<E, W>(mut value: &str, writer: &mut W) -> Result<(), E>
where
    W: FnMut(&str) -> Result<(), E>,
{
    while let Some(index) = value.find(['\n', '^', '"']) {
        writer(&value[..index])?;
        match &value[index..index + 1] {
            "\n" => writer("^n"),
            "^" => writer("^^"),
            "\"" => writer("^'"),
            _ => unreachable!(),
        }?;
        value = &value[index + 1..];
    }

    writer(value)
}

/// Writes a [`Value`].
///
/// # Errors
///
/// Fails if the writer function returns an error.
fn write_value<E, W>(value: &Value, writer: &mut W) -> Result<(), E>
where
    W: FnMut(&str) -> Result<(), E>,
{
    writer(&value.value)
}

/// Writes an [`Identifier`].
///
/// # Errors
///
/// Fails if the writer function returns an error.
fn write_identifier<E, W>(identifier: &Identifier, writer: &mut W) -> Result<(), E>
where
    W: FnMut(&str) -> Result<(), E>,
{
    writer(&identifier.value.to_ascii_uppercase())
}

//====================// helper functions for parsing //====================//

/// Checks whether a character is a `SAFE_CHAR`.
///
/// ABNF from [RFC 5545][rfc5545]:
///
/// ```text
/// SAFE-CHAR     = WSP / %x21 / %x23-2B / %x2D-39 / %x3C-7E
///               / NON-US-ASCII
/// ; Any character except CONTROL, DQUOTE, ";", ":", ","
/// ```
///
/// [rfc5545]: https://www.rfc-editor.org/rfc/rfc5545
const fn is_safe_char(c: u8) -> bool {
    !is_control(c) && (c != b'"') && (c != b';') && (c != b':') && (c != b',')
}

/// Checks whether a character is a `QSAFE_CHAR`.
///
/// ABNF from [RFC 5545][rfc5545]:
///
/// ```text
/// QSAFE-CHAR    = WSP / %x21 / %x23-7E / NON-US-ASCII
/// ; Any character except CONTROL and DQUOTE
/// ```
///
/// [rfc5545]: https://www.rfc-editor.org/rfc/rfc5545
const fn is_qsafe_char(c: u8) -> bool {
    !is_control(c) && (c != b'"')
}

/// Checks whether a character is a `CONTROL` character.
///
/// Note that in [RFC 5545][rfc5545] and [RFC 6350][rfc6350] the definition of a control character
/// excludes the horizontal tab (`'\t'`).
///
/// ABNF from [RFC 5545][rfc5545]:
///
/// ```text
/// CONTROL       = %x00-08 / %x0A-1F / %x7F
/// ; All the controls except HTAB
/// ```
///
/// [rfc5545]: https://www.rfc-editor.org/rfc/rfc5545
/// [rfc6350]: https://www.rfc-editor.org/rfc/rfc6350
const fn is_control(c: u8) -> bool {
    c.is_ascii_control() && (c != b'\t')
}

/// Checks whether a character is alphanumeric or a dash (`'-'`).
const fn is_identifier_char(c: u8) -> bool {
    c.is_ascii_alphanumeric() || (c == b'-')
}

#[cfg(test)]
mod tests {
    mod parse {
        use {
            crate::{Contentline, Identifier, Param, ParamValue, Parser, Value},
            std::iter,
        };

        #[test]
        fn name_and_value() {
            let contentline = "NOTE:This is a note.";
            let mut parser = Parser::new(contentline.as_bytes());

            assert_eq!(
                parser.parse_next_line().unwrap().unwrap(),
                Contentline {
                    group: None,
                    name: Identifier::new_borrowed("NOTE").unwrap(),
                    params: Vec::new(),
                    value: Value::new_borrowed("This is a note.").unwrap(),
                }
            );
            assert!(parser.parse_next_line().is_none());
        }

        #[test]
        fn group_name_params_value() {
            let contentline =
                "test-group.TEST-CASE;test-param=PARAM1;another-test-param=PARAM2:value";
            let mut parser = Parser::new(contentline.as_bytes());

            assert_eq!(
                parser.parse_next_line().unwrap().unwrap(),
                Contentline {
                    group: Some(Identifier::new_borrowed("test-group").unwrap()),
                    name: Identifier::new_borrowed("TEST-CASE").unwrap(),
                    params: vec![
                        Param::new(
                            Identifier::new_borrowed("test-param").unwrap(),
                            vec![ParamValue::new_borrowed("PARAM1").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::new_borrowed("another-test-param").unwrap(),
                            vec![ParamValue::new_borrowed("PARAM2").unwrap()]
                        )
                        .unwrap(),
                    ],
                    value: Value::new_borrowed("value").unwrap(),
                }
            );
            assert!(parser.parse_next_line().is_none());
        }

        #[test]
        fn empty_value() {
            let empty_value = "EMPTY-VALUE:";
            let mut parser = Parser::new(empty_value.as_bytes());

            assert_eq!(
                parser.parse_next_line().unwrap().unwrap(),
                Contentline {
                    group: None,
                    name: Identifier::new_borrowed("EMPTY-VALUE").unwrap(),
                    params: Vec::new(),
                    value: Value::new_borrowed("").unwrap(),
                }
            );
            assert!(parser.parse_next_line().is_none());
        }

        #[test]
        fn empty_param() {
            let empty_param = "EMPTY-PARAM;paramtext=;quoted-string=\"\";multiple=,,,,\"\",\"\",,\"\",,,\"\":value";
            let mut parser = Parser::new(empty_param.as_bytes());

            assert_eq!(
                parser.parse_next_line().unwrap().unwrap(),
                Contentline {
                    group: None,
                    name: Identifier::new_borrowed("EMPTY-PARAM").unwrap(),
                    params: vec![
                        Param::new(
                            Identifier::new_borrowed("paramtext").unwrap(),
                            vec![ParamValue::new_borrowed("").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::new_borrowed("quoted-string").unwrap(),
                            vec![ParamValue::new_borrowed("").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::new_borrowed("multiple").unwrap(),
                            iter::repeat(ParamValue::new_borrowed("").unwrap())
                                .take(11)
                                .collect()
                        )
                        .unwrap(),
                    ],
                    value: Value::new_borrowed("value").unwrap(),
                }
            );
            assert!(parser.parse_next_line().is_none());
        }

        #[test]
        fn case_insensitivity() {
            let contentline0 = "Group.lowerUPPER;PaRaM=parameter value:value";
            let contentline1 = "group.LOWERupper;PARAm=parameter value:value";

            let parsed0 = Parser::new(contentline0.as_bytes())
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            let parsed1 = Parser::new(contentline1.as_bytes())
                .collect::<Result<Vec<_>, _>>()
                .unwrap();

            assert_eq!(parsed0, parsed1);
            assert_eq!(parsed0.len(), 1);
        }

        #[test]
        fn rfc6868() {
            let contentline = "RFC6868-TEST;caret=^^;newline=^n;double-quote=^';all-in-quotes=\"^^^n^'\";weird=^^^^n;others=^g^5^k^?^%^&^a:value";
            let mut parser = Parser::new(contentline.as_bytes());

            assert_eq!(
                parser.parse_next_line().unwrap().unwrap(),
                Contentline {
                    group: None,
                    name: Identifier::new_borrowed("RFC6868-TEST").unwrap(),
                    params: vec![
                        Param::new(
                            Identifier::new_borrowed("caret").unwrap(),
                            vec![ParamValue::new_borrowed("^").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::new_borrowed("newline").unwrap(),
                            vec![ParamValue::new_borrowed("\n").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::new_borrowed("double-quote").unwrap(),
                            vec![ParamValue::new_borrowed("\"").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::new_borrowed("all-in-quotes").unwrap(),
                            vec![ParamValue::new_borrowed("^\n\"").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::new_borrowed("weird").unwrap(),
                            vec![ParamValue::new_borrowed("^^n").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::new_borrowed("others").unwrap(),
                            vec![ParamValue::new_borrowed("^g^5^k^?^%^&^a").unwrap()]
                        )
                        .unwrap(),
                    ],
                    value: Value::new_borrowed("value").unwrap(),
                }
            );
            assert!(parser.parse_next_line().is_none());
        }
    }

    mod write {
        use {
            crate::{Contentline, Identifier, Param, ParamValue, Value, Writer},
            std::{iter, str},
        };

        #[test]
        fn name_and_value() {
            let contentline = Contentline {
                group: None,
                name: Identifier::new_borrowed("NAME").unwrap(),
                params: Vec::new(),
                value: Value::new_borrowed("VALUE").unwrap(),
            };

            let expected = "NAME:VALUE\r\n";

            let actual = {
                let mut buffer = Vec::new();
                let mut writer = Writer::new(&mut buffer);
                writer.write(&contentline).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(&actual, expected);
        }

        #[test]
        fn group_name_params_value() {
            let contentline = Contentline {
                group: Some(Identifier::new_borrowed("TEST-GROUP").unwrap()),
                name: Identifier::new_borrowed("TEST-NAME").unwrap(),
                params: vec![
                    Param::new(
                        Identifier::new_borrowed("PARAM-1").unwrap(),
                        vec![ParamValue::new_borrowed("param value 1").unwrap()],
                    )
                    .unwrap(),
                    Param::new(
                        Identifier::new_borrowed("PARAM-2").unwrap(),
                        vec![ParamValue::new_borrowed("param value of parameter: 2").unwrap()],
                    )
                    .unwrap(),
                ],
                value: Value::new_borrowed("test value \"with quotes\"").unwrap(),
            };

            let expected = "\
TEST-GROUP.TEST-NAME;PARAM-1=param value 1;PARAM-2=\"param value of paramete\r
 r: 2\":test value \"with quotes\"\r
";

            let actual = {
                let mut buffer = Vec::new();
                let mut writer = Writer::new(&mut buffer);
                writer.write(&contentline).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(&actual, expected);
        }

        #[test]
        fn identfiers_converted_to_uppercase() {
            let contentline = Contentline {
                group: Some(Identifier::new_borrowed("lower-group").unwrap()),
                name: Identifier::new_borrowed("name").unwrap(),
                params: vec![Param::new(
                    Identifier::new_borrowed("PaRaM").unwrap(),
                    vec![ParamValue::new_borrowed("param value").unwrap()],
                )
                .unwrap()],
                value: Value::new_borrowed("value").unwrap(),
            };

            let expected = "LOWER-GROUP.NAME;PARAM=param value:value\r\n";

            let actual = {
                let mut buffer = Vec::new();
                let mut writer = Writer::new(&mut buffer);
                writer.write(&contentline).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(&actual, expected);
        }

        #[test]
        fn empty_value() {
            let contentline = Contentline {
                group: None,
                name: Identifier::new_borrowed("NAME").unwrap(),
                params: Vec::new(),
                value: Value::new_borrowed("").unwrap(),
            };

            let expected = "NAME:\r\n";

            let actual = {
                let mut buffer = Vec::new();
                let mut writer = Writer::new(&mut buffer);
                writer.write(&contentline).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(&actual, expected);
        }

        #[test]
        fn empty_param() {
            let num_params = 15;

            let contentline = Contentline {
                group: None,
                name: Identifier::new_borrowed("NAME").unwrap(),
                params: vec![Param::new(
                    Identifier::new_borrowed("PARAM").unwrap(),
                    iter::repeat(ParamValue::new_borrowed("").unwrap())
                        .take(num_params)
                        .collect(),
                )
                .unwrap()],
                value: Value::new_borrowed("value").unwrap(),
            };

            let expected = {
                let mut expected = String::from("NAME;PARAM=");
                expected.push_str(&",".repeat(num_params - 1));
                expected.push_str(":value\r\n");
                expected
            };

            let actual = {
                let mut buffer = Vec::new();
                let mut writer = Writer::new(&mut buffer);
                writer.write(&contentline).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(actual, expected);
        }

        #[test]
        fn rfc6868() {
            let contentline = Contentline {
                group: None,
                name: Identifier::new_borrowed("RFC6868-TEST").unwrap(),
                params: vec![
                    Param::new(
                        Identifier::new_borrowed("CARET").unwrap(),
                        vec![ParamValue::new_borrowed("^").unwrap()],
                    )
                    .unwrap(),
                    Param::new(
                        Identifier::new_borrowed("NEWLINE").unwrap(),
                        vec![ParamValue::new_borrowed("\n").unwrap()],
                    )
                    .unwrap(),
                    Param::new(
                        Identifier::new_borrowed("DOUBLE-QUOTE").unwrap(),
                        vec![ParamValue::new_borrowed("\"").unwrap()],
                    )
                    .unwrap(),
                    Param::new(
                        Identifier::new_borrowed("ALL-IN-QUOTES").unwrap(),
                        vec![ParamValue::new_borrowed("^;\n;\"").unwrap()],
                    )
                    .unwrap(),
                    Param::new(
                        Identifier::new_borrowed("WEIRD").unwrap(),
                        vec![ParamValue::new_borrowed("^^n").unwrap()],
                    )
                    .unwrap(),
                ],
                value: Value::new_borrowed("value").unwrap(),
            };

            let expected = "RFC6868-TEST;CARET=^^;NEWLINE=^n;DOUBLE-QUOTE=^';ALL-IN-QUOTES=\"^^;^n;^'\";W\r\n EIRD=^^^^n:value\r\n";

            let actual = {
                let mut buffer = Vec::new();
                let mut writer = Writer::new(&mut buffer);
                writer.write(&contentline).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(&actual, expected);
        }
    }
}
