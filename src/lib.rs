#![doc = include_str!("../README.md")]
#![deny(unsafe_code)]
#![deny(clippy::all)]
#![warn(clippy::cargo)]
#![warn(missing_docs)]

use {
    crate::folding::{FoldingWriter, UnfoldingReader},
    std::{
        borrow::Borrow,
        error::Error,
        fmt::{self, Debug, Display, Formatter},
        hash::{Hash, Hasher},
        io::{self, Read, Write},
        iter::Iterator,
        str::FromStr,
    },
};

mod folding;

/// Parses an iCalendar or vCard file.
///
/// [`Parser`] is an [`Iterator`].
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
/// let email_line = contentlines.iter().find(|contentline| contentline.name() == "EMAIL").unwrap();
/// assert_eq!(email_line.value(), "michelle.depierre@example.com");
///
/// let third_line = &contentlines[2];
/// assert_eq!(third_line.name(), "FN");
/// assert_eq!(third_line.value(), "Michelle de Pierre");
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
}

impl<R: Read> Iterator for Parser<R> {
    type Item = Result<Contentline, ParseError>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.unfolder.next_line()? {
            Ok(next_line) => {
                Some(Contentline::parse(next_line).map_err(ParseError::InvalidContentline))
            }
            Err(err) => Some(Err(ParseError::IoError(err))),
        }
    }
}

/// The error type returned if parsing fails.
#[derive(Debug)]
pub enum ParseError {
    /// An IO error occurred while parsing.
    IoError(io::Error),
    /// An invalid content line was encountered.
    InvalidContentline(ParseContentlineError),
}

impl Display for ParseError {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::IoError(err) => Display::fmt(err, f),
            Self::InvalidContentline(err) => Display::fmt(err, f),
        }
    }
}

impl Error for ParseError {}

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
///     Contentline::try_new("BEGIN", "VCARD")?,
///     Contentline::try_new("FN", "Mr. John Example")?,
///     Contentline::try_new("BDAY", "20230326")?
///         .try_add_param("VALUE", ["date-and-or-time"])?,
///     Contentline::try_new("END", "VCARD")?,
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
    pub fn write_all<C, I>(&mut self, contentlines: I) -> io::Result<()>
    where
        C: Borrow<Contentline>,
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
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Contentline {
    /// The group of the content line.
    group: Option<Identifier<String>>,
    /// The name of the content line.
    name: Identifier<String>,
    /// The parameters of the content line.
    params: Vec<Param>,
    /// The value of the content line.
    value: Value<String>,
}

impl Contentline {
    /// Get the group of the content line.
    pub fn group(&self) -> Option<&str> {
        self.group.as_ref().map(|group| group.as_ref())
    }

    /// Get the name of the content line.
    pub fn name(&self) -> &str {
        self.name.as_ref()
    }

    /// Get the parameters of the content line.
    pub fn params(&self) -> &[Param] {
        &self.params
    }

    /// Get the value of the content line.
    pub fn value(&self) -> &str {
        self.value.as_ref()
    }

    /// Creates a new [`Contentline`].
    ///
    /// See [`Contentline::try_new`] for a non-panicking version.
    ///
    /// # Panics
    ///
    /// Panics whenever [`Contentline::try_new`] would return an error.
    pub fn new<N, V>(name: N, value: V) -> Self
    where
        N: AsRef<str>,
        V: AsRef<str>,
    {
        Self::try_new(name, value).unwrap()
    }

    /// Creates a new [`Contentline`].
    ///
    /// See [`Contentline::new`] for a panicking version.
    ///
    /// # Errors
    ///
    /// Fails if either name is not a valid [`Identifier`] or value is not a valid [`Value`].
    pub fn try_new<N, V>(name: N, value: V) -> Result<Self, InvalidContentline>
    where
        N: AsRef<str>,
        V: AsRef<str>,
    {
        let name =
            Identifier::new(name.as_ref().to_owned()).map_err(InvalidContentline::InvalidName)?;
        let value =
            Value::new(value.as_ref().to_owned()).map_err(InvalidContentline::InvalidValue)?;

        Ok(Self {
            group: None,
            name,
            params: Vec::new(),
            value,
        })
    }

    /// Sets the group of the [`Contentline`].
    ///
    /// See [`Contentline::try_set_group`] for a non-panicking version.
    ///
    /// # Panics
    ///
    /// Panics whenever [`Contentline::try_set_group`] would return an error.
    pub fn set_group<G>(self, group: G) -> Self
    where
        G: AsRef<str>,
    {
        Self::try_set_group(self, group).unwrap()
    }

    /// Sets the group of the [`Contentline`].
    ///
    /// See [`Contentline::set_group`] for a panicking version.
    ///
    /// # Errors
    ///
    /// Fails if the group is not a valid [`Identifier`].
    pub fn try_set_group<G>(self, group: G) -> Result<Self, InvalidContentline>
    where
        G: AsRef<str>,
    {
        let group = Some(
            Identifier::new(group.as_ref().to_owned()).map_err(InvalidContentline::InvalidGroup)?,
        );

        Ok(Self { group, ..self })
    }

    /// Unsets the group of the [`Contentline`].
    pub fn unset_group(self) -> Self {
        Self {
            group: None,
            ..self
        }
    }

    /// Adds a parameter to the [`Contentline`].
    ///
    /// See [`Contentline::try_add_param`] for a non-panicking version.
    ///
    /// # Panics
    ///
    /// Panics whenever [`Contentline::try_add_param`] would return an error.
    pub fn add_param<I, N, V>(self, name: N, values: I) -> Self
    where
        I: IntoIterator<Item = V>,
        N: AsRef<str>,
        V: AsRef<str>,
    {
        Self::try_add_param(self, name, values).unwrap()
    }

    /// Adds a parameter to the [`Contentline`].
    ///
    /// See [`Contentline::add_param`] for a panicking version.
    ///
    /// # Errors
    ///
    /// Fails if the parameter is invalid.
    pub fn try_add_param<I, N, V>(self, name: N, values: I) -> Result<Self, InvalidParam>
    where
        I: IntoIterator<Item = V>,
        N: AsRef<str>,
        V: AsRef<str>,
    {
        let param = Param::try_new(name, values)?;

        Ok(Self {
            params: {
                let mut params = self.params;
                params.push(param);
                params
            },
            ..self
        })
    }

    /// Sets the parameters of the [`Contentline`].
    ///
    /// See [`Contentline::try_set_params`] for a non-panicking version.
    ///
    /// # Panics
    ///
    /// Panics whenever [`Contentline::try_set_params`] would return an error.
    pub fn set_params<I, P>(self, params: I) -> Self
    where
        I: IntoIterator<Item = P>,
        P: TryInto<Param>,
        P::Error: Debug,
    {
        self.try_set_params(params).unwrap()
    }

    /// Sets the parameters of the [`Contentline`].
    ///
    /// See [`Contentline::set_params`] for a panicking version.
    ///
    /// # Errors
    ///
    /// Fails if any parameter is invalid.
    pub fn try_set_params<I, P>(self, params: I) -> Result<Self, P::Error>
    where
        I: IntoIterator<Item = P>,
        P: TryInto<Param>,
    {
        Ok(Self {
            params: params
                .into_iter()
                .map(TryInto::try_into)
                .collect::<Result<_, _>>()?,
            ..self
        })
    }

    /// Parses a [`Contentline`].
    ///
    /// # Errors
    ///
    /// Fails if the given content line is incorrectly formatted.
    fn parse(mut contentline: &str) -> Result<Self, ParseContentlineError> {
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
}

// TODO: Test this
impl FromStr for Contentline {
    type Err = ParseContentlineError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Contentline::parse(s)
    }
}

impl Display for Contentline {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.write(|s| f.write_str(s))
    }
}

/// Indicates an invalid [`Contentline`].
#[derive(Debug)]
pub enum InvalidContentline {
    /// The group is invalid.
    InvalidGroup(InvalidIdentifier),
    /// The name is invalid.
    InvalidName(InvalidIdentifier),
    /// The value is invalid.
    InvalidValue(InvalidValue),
    /// A parameter is invalid.
    InvalidParam(InvalidParam),
}

impl Display for InvalidContentline {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Self::InvalidGroup(err) => write!(f, "Invalid group: {}", err),
            Self::InvalidName(err) => write!(f, "Invalid name: {}", err),
            Self::InvalidValue(err) => write!(f, "Invalid value: {}", err),
            Self::InvalidParam(err) => write!(f, "Invalid parameter: {}", err),
        }
    }
}

impl Error for InvalidContentline {}

/// Indicates a failure to parse a [`Contentline`].
#[derive(Debug)]
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

impl Error for ParseContentlineError {}

macro_rules! empty {
    () => {};
}

macro_rules! as_str_wrapper {
    (
        @metainfo {
            case_sensitive: true,
            $($metainfo:tt)*
        };

        $($remainder:tt)*
    ) => {
        as_str_wrapper! {
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
        as_str_wrapper! {
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
        // TODO: Case sensitivity is wrong
        $( /* if */ $is_not_case_sensitive
            #[derive(Hash)]
        )*
        #[doc = concat!("A wrapper of a [`AsRef<str>`] that is guaranteed to be a valid ", $doc_name, ".")]
        ///
        #[doc = concat!("A ", $doc_name, " is considered valid if it ", $valid_if, ".")]
        #[derive(Clone, Debug)]
        pub struct $type_name<T> {
            value: T,
        }

        impl<T: AsRef<str>> $type_name<T> {
            #[doc = concat!("Creates a new [`", stringify!($type_name), "`].")]
            ///
            /// # Errors
            ///
            #[doc = concat!("Fails if `", stringify!($param_name), "` is not a valid ", $doc_name, ".")]
            pub fn new($param_name: T) -> Result<Self, $error_name> {
                if Self::is_valid($param_name.as_ref()) {
                    Ok(Self::new_unchecked($param_name))
                } else {
                    Err($error_name)
                }
            }

            #[doc = concat!("Creates a new [`", stringify!($type_name), "`]. Does not check if `", stringify!($param_name), "` is valid.")]
            ///
            #[doc = concat!("It is up to the caller to ensure that `", stringify!($param_name), "` is a valid ", $doc_name, ".")]
            pub fn new_unchecked($param_name: T) -> Self {
                debug_assert!(Self::is_valid($param_name.as_ref()));
                Self { value: $param_name }
            }

            #[doc = concat!("Extracts a string slice containing the ", $doc_name, ".")]
            pub fn as_str(&self) -> &str {
                self.value.as_ref()
            }

            #[doc = concat!("Returns true if `", stringify!($param_name), "` is a valid ", $doc_name, ".")]
            ///
            #[doc = concat!("A ", $doc_name, " is considered valid if it ", $valid_if, ".")]
            fn is_valid($param_name: &str) -> bool {
                $( $is_valid_impl )+
            }
        }

        impl<T: AsRef<str>> Eq for $type_name<T> {}

        impl<T, U> PartialEq<$type_name<U>> for $type_name<T>
        where
            T: AsRef<str>,
            U: AsRef<str>,
        {
            fn eq(&self, other: &$type_name<U>) -> bool {
                self == other.value.as_ref()
            }
        }

        impl<T: AsRef<str>> PartialEq<String> for $type_name<T> {
            fn eq(&self, other: &String) -> bool {
                self == other.as_str()
            }
        }

        impl<T: AsRef<str>> PartialEq<&str> for $type_name<T> {
            fn eq(&self, other: &&str) -> bool {
                self == *other
            }
        }

        impl<T: AsRef<str>> PartialEq<str> for $type_name<T> {
            fn eq(&self, other: &str) -> bool {
                $( /* if */ $is_case_sensitive
                    self.value.as_ref().eq_ignore_ascii_case(other)
                )?
                $( /* if */ $is_not_case_sensitive
                    self.value.as_ref() == other
                )?
            }
        }

        $( /* if */ $is_case_sensitive
            impl<T: AsRef<str>> Hash for $type_name<T> {
                fn hash<H: Hasher>(&self, state: &mut H) {
                    // implementation is mostly the same as in std::str
                    for c in self.value.as_ref().as_bytes() {
                        c.to_ascii_uppercase().hash(state);
                    }
                    state.write_u8(0xff);
                }
            }
        )?

        impl<T: AsRef<str>> AsRef<str> for $type_name<T> {
            fn as_ref(&self) -> &str {
                self.value.as_ref()
            }
        }

        impl<T: AsRef<str>> From<$type_name<T>> for String {
            fn from($param_name: $type_name<T>) -> Self {
                $param_name.value.as_ref().to_owned()
            }
        }

        impl<T: AsRef<str>> Display for $type_name<T> {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", self.value.as_ref())
            }
        }

        #[doc = concat!("Indicates an attempt to create a [`", stringify!($type_name), "`] from an invalid ", $doc_name, ".")]
        ///
        #[doc = concat!("A [`", stringify!($type_name), "`] is considered valid if ", $valid_if, ".")]
        #[derive(Debug)]
        pub struct $error_name;

        impl Display for $error_name {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, $error_message)
            }
        }

        impl Error for $error_name {}
    };
}

as_str_wrapper! {
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
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Param {
    name: Identifier<String>,
    values: Vec<ParamValue<String>>,
}

impl Param {
    /// Get the name of the parameter.
    pub fn name(&self) -> &str {
        self.name.as_ref()
    }

    // TODO: It would be better to not return `ParamValue`s but rather some standard library type
    /// Get the values of the parameter.
    ///
    /// The values are guaranteed to be non-empty.
    pub fn values(&self) -> &[ParamValue<String>] {
        &self.values
    }

    /// Creates a new [`Param`].
    ///
    /// See [`Param::try_new`] for a non-panicking version.
    ///
    /// # Errors
    ///
    /// Fails whenever [`Param::try_new`] would return an error.
    pub fn new<I, N, V>(name: N, values: I) -> Self
    where
        I: IntoIterator<Item = V>,
        N: AsRef<str>,
        V: AsRef<str>,
    {
        Self::try_new(name, values).unwrap()
    }

    /// Creates a new [`Param`].
    ///
    /// # Errors
    ///
    /// Fails in any of the following cases:
    /// - The parameter name is invalid.
    /// - A parameter value is invalid.
    /// - `values` is empty.
    pub fn try_new<I, N, V>(name: N, values: I) -> Result<Self, InvalidParam>
    where
        I: IntoIterator<Item = V>,
        N: AsRef<str>,
        V: AsRef<str>,
    {
        let values = values
            .into_iter()
            .map(|value| ParamValue::new(value.as_ref().to_owned()))
            .collect::<Result<Vec<_>, InvalidParamValue>>()
            .map_err(InvalidParam::InvalidValue)?;
        if values.is_empty() {
            return Err(InvalidParam::EmptyValues);
        }

        let name = Identifier::new(name.as_ref().to_owned()).map_err(InvalidParam::InvalidName)?;

        Ok(Self { name, values })
    }
}

impl<I, N, V> TryFrom<(N, I)> for Param
where
    I: IntoIterator<Item = V>,
    N: AsRef<str>,
    V: AsRef<str>,
{
    type Error = InvalidParam;

    fn try_from((name, values): (N, I)) -> Result<Self, Self::Error> {
        Param::try_new(name, values)
    }
}

/// Indicates a failed attempt to create a [`Param`].
///
/// This happens when it is attempted to create a [`Param`] without any value.
#[derive(Debug)]
pub enum InvalidParam {
    /// Empty parameter values.
    EmptyValues,
    /// The parameter name is invalid.
    InvalidName(InvalidIdentifier),
    /// A parameter value is invalid.
    InvalidValue(InvalidParamValue),
}

impl Display for InvalidParam {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::EmptyValues => write!(f, "Empty parameter values"),
            Self::InvalidName(err) => write!(f, "Invalid parameter name: {}", err),
            Self::InvalidValue(err) => write!(f, "Invalid parameter value: {}", err),
        }
    }
}

impl Error for InvalidParam {}

as_str_wrapper! {
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

as_str_wrapper! {
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
fn parse_group_and_name(
    contentline: &mut &str,
) -> Result<(Option<Identifier<String>>, Identifier<String>), IntermediateParsingError> {
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
fn parse_params(contentline: &mut &str) -> Result<Vec<Param>, IntermediateParsingError> {
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
fn parse_param(contentline: &mut &str) -> Result<Param, IntermediateParsingError> {
    let name = parse_identifier(contentline)?;

    if !contentline.starts_with('=') {
        return Err(IntermediateParsingError);
    }
    *contentline = &contentline[1..];

    let values = parse_param_values(contentline)?;

    Ok(Param { name, values })
}

/// Parses a list of [`ParamValue`]s.
///
/// # Errors
///
/// Fails if the list is empty or if there is an error parsing a [`ParamValue`].
fn parse_param_values(
    contentline: &mut &str,
) -> Result<Vec<ParamValue<String>>, IntermediateParsingError> {
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
fn parse_param_value(
    contentline: &mut &str,
) -> Result<ParamValue<String>, IntermediateParsingError> {
    let value = if contentline.starts_with('"') {
        parse_quoted_string(contentline)?
    } else {
        parse_paramtext(contentline)
    };

    Ok(ParamValue::new_unchecked(value))
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
fn parse_quoted_string(contentline: &mut &str) -> Result<String, IntermediateParsingError> {
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
fn parse_paramtext(contentline: &mut &str) -> String {
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
fn parse_param_value_rfc6868(param_value: &str) -> String {
    debug_assert!(param_value.bytes().all(is_qsafe_char));

    match param_value.find('^') {
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

            result
        }
        None => param_value.to_owned(),
    }
}

/// Parses a [`Value`].
///
/// # Errors
///
/// Fails if the argument contains control characters other than horizontal tabs.
fn parse_value(contentline: &mut &str) -> Result<Value<String>, IntermediateParsingError> {
    if Value::<&str>::is_valid(contentline) {
        let value = Value::new_unchecked(contentline.to_owned());
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
fn parse_identifier(
    contentline: &mut &str,
) -> Result<Identifier<String>, IntermediateParsingError> {
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

        let identifier = Identifier::new_unchecked(identifier.to_owned());

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
fn write_param_values<E, T, W>(values: &[ParamValue<T>], writer: &mut W) -> Result<(), E>
where
    T: AsRef<str>,
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
fn write_param_value<E, T, W>(value: &ParamValue<T>, writer: &mut W) -> Result<(), E>
where
    T: AsRef<str>,
    W: FnMut(&str) -> Result<(), E>,
{
    let value = value.value.as_ref();
    if value.contains([';', ':', '.']) {
        writer("\"")?;
        write_param_value_rfc6868(value, writer)?;
        writer("\"")
    } else {
        write_param_value_rfc6868(value, writer)
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
fn write_value<E, T, W>(value: &Value<T>, writer: &mut W) -> Result<(), E>
where
    T: AsRef<str>,
    W: FnMut(&str) -> Result<(), E>,
{
    writer(value.value.as_ref())
}

/// Writes an [`Identifier`].
///
/// The identifier is written in uppercase as is recommended in [RFC 6350, section
/// 3.3](https://www.rfc-editor.org/rfc/rfc6350#section-3.3).
///
/// # Errors
///
/// Fails if the writer function returns an error.
fn write_identifier<E, T, W>(identifier: &Identifier<T>, writer: &mut W) -> Result<(), E>
where
    T: AsRef<str>,
    W: FnMut(&str) -> Result<(), E>,
{
    // TODO: The allocation here is unnecessary
    let identifier = identifier.value.as_ref().to_uppercase();
    writer(&identifier)
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
        use crate::{Contentline, Parser};

        #[test]
        fn name_and_value() {
            let contentline = "NOTE:This is a note.";
            let mut parser = Parser::new(contentline.as_bytes());

            assert_eq!(
                parser.next().unwrap().unwrap(),
                Contentline::new("NOTE", "This is a note."),
            );
            assert!(parser.next().is_none());
        }

        #[test]
        fn group_name_params_value() {
            let contentline =
                "test-group.TEST-CASE;test-param=PARAM1;another-test-param=PARAM2:value";
            let mut parser = Parser::new(contentline.as_bytes());

            assert_eq!(
                parser.next().unwrap().unwrap(),
                Contentline::new("TEST-CASE", "value")
                    .set_group("test-group")
                    .set_params([
                        ("test-param", ["PARAM1"]),
                        ("another-test-param", ["PARAM2"])
                    ])
            );
            assert!(parser.next().is_none());
        }

        #[test]
        fn empty_value() {
            let empty_value = "EMPTY-VALUE:";
            let mut parser = Parser::new(empty_value.as_bytes());

            assert_eq!(
                parser.next().unwrap().unwrap(),
                Contentline::new("EMPTY-VALUE", "")
            );
            assert!(parser.next().is_none());
        }

        #[test]
        fn empty_param() {
            let empty_param = "EMPTY-PARAM;paramtext=;quoted-string=\"\";multiple=,,,,\"\",\"\",,\"\",,,\"\":value";
            let mut parser = Parser::new(empty_param.as_bytes());

            assert_eq!(
                parser.next().unwrap().unwrap(),
                Contentline::new("EMPTY-PARAM", "value").set_params([
                    ("paramtext", [""].as_slice()),
                    ("quoted-string", &[""]),
                    ("multiple", &[""; 11])
                ])
            );
            assert!(parser.next().is_none());
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
                parser.next().unwrap().unwrap(),
                Contentline::new("RFC6868-TEST", "value").set_params([
                    ("caret", ["^"]),
                    ("newline", ["\n"]),
                    ("double-quote", ["\""]),
                    ("all-in-quotes", ["^\n\""]),
                    ("weird", ["^^n"]),
                    ("others", ["^g^5^k^?^%^&^a"]),
                ])
            );
            assert!(parser.next().is_none());
        }
    }

    mod write {
        use {
            crate::{Contentline, Writer},
            std::{iter, str},
        };

        #[test]
        fn name_and_value() {
            let contentline = Contentline::new("NAME", "VALUE");

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
            let contentline = Contentline::new("TEST-NAME", "test value \"with quotes\"")
                .set_group("TEST-GROUP")
                .set_params([
                    ("PARAM-1", ["param value 1"]),
                    ("PARAM-2", ["param value of parameter: 2"]),
                ]);

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
        fn identifiers_converted_to_uppercase() {
            let contentline = Contentline::new("name", "value")
                .set_group("lower-group")
                .add_param("PaRaM", ["param value"]);

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
            let contentline = Contentline::new("NAME", "");

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

            let contentline = Contentline::new("NAME", "value")
                .add_param("PARAM", iter::repeat("").take(num_params));

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
            let contentline = Contentline::new("RFC6868-TEST", "value").set_params([
                ("CARET", ["^"]),
                ("NEWLINE", ["\n"]),
                ("DOUBLE-QUOTE", ["\""]),
                ("ALL-IN-QUOTES", ["^;\n;\""]),
                ("WEIRD", ["^^n"]),
            ]);

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
