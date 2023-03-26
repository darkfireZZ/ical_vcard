#![doc = include_str!("../README.md")]
#![deny(unsafe_code)]
#![deny(clippy::all)]
// TODO implement cargo lints: #![warn(clippy::cargo)]
#![warn(missing_docs)]

use {
    crate::folding::{FoldingWriter, UnfoldingReader},
    std::{
        borrow::Borrow,
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
/// Returns an [`Iterator`] of [`Result<Contentline, ParseError>`].
///
/// The following example illustrates how to parse a simple vCard file:
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use ical_vcard::{Contentline, Identifier, Param, ParamValue, Value};
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
/// let contentlines = ical_vcard::parse(vcard_file.as_bytes()).collect::<Result<Vec<_>, _>>()?;
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
///
/// # Performance
///
/// Depending on the [`Read`] implementation used, each call to [`reader::read()`][Read::read] (of
/// which this function does many), may involve a system call, and therefore, using something that
/// implements [`io::BufRead`], such as [`io::BufReader`], will be more efficient.
///
/// # Security
///
/// [`Parse`] reads the next line of the underlying [`Read`] into memory to parse it. If
/// `reader` doesn't contain any (CRLF) line breaks and is sufficiently large (or infinite),
/// attempting to read the next contentline will completely fill up the heap memory.
///
/// # Errors
///
/// A [`ParseError`] will be returned by the iterator if `reader` returned an [`io::Error`] or if
/// an invalid contentline was encountered.
pub fn parse<R: Read>(reader: R) -> Parse<R> {
    Parse::new(reader)
}

/// Writes an iCalendar or vCard file.
///
/// The following example illustrates how to write a simple vCard file:
///
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// #
/// use ical_vcard::{Contentline, Identifier, Param, ParamValue, Value};
///
/// let contentlines = [
///     Contentline {
///         group: None,
///         name: Identifier::try_from("BEGIN")?,
///         params: Vec::new(),
///         value: Value::try_from("VCARD")?,
///     },
///     Contentline {
///         group: None,
///         name: Identifier::try_from("FN")?,
///         params: Vec::new(),
///         value: Value::try_from("Mr. John Example")?,
///     },
///     Contentline {
///         group: None,
///         name: Identifier::try_from("BDAY")?,
///         params: vec![Param::new(
///             Identifier::try_from("VALUE")?,
///             vec![ParamValue::try_from("date-and-or-time")?],
///         )?],
///         value: Value::try_from("20230326")?,
///     },
///     Contentline {
///         group: None,
///         name: Identifier::try_from("END")?,
///         params: Vec::new(),
///         value: Value::try_from("VCARD")?,
///     },
/// ];
///
/// // For the sake of simplicity and testability, the vCard is written to a Vec. However, in a
/// // real application, one would probably write it to disk or do some further processing (e.g.
/// // compression)
/// let vcard = {
///     let mut buffer = Vec::new();
///     ical_vcard::write(contentlines.iter(), &mut buffer)?;
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
///
/// # Performance
///
/// It can be excessively inefficient to work directly with something that implements [`Write`]. For
/// example, every call to write on [`std::net::TcpStream`] results in a system call. Wrapping
/// `writer` in a [`io::BufWriter`] may improve performance significantly.
///
/// # Errors
///
/// Fails if `writer` returns an error.
pub fn write<C, I, W>(contentlines: C, mut writer: W) -> io::Result<()>
where
    C: IntoIterator<Item = I>,
    I: Borrow<Contentline>,
    W: Write,
{
    let mut folder = FoldingWriter::new(&mut writer);

    for line in contentlines {
        line.borrow().write(|s| folder.write(s))?;
        folder.end_line()?;
    }

    writer.flush()?;

    Ok(())
}

/// An [`Iterator`] over [`Contentline`]s.
///
/// This struct is generally created by calling [`parse()`]. See the documentation of [`parse()`] for
/// more information.
#[derive(Debug)]
pub struct Parse<R: Read> {
    unfolder: UnfoldingReader<R>,
}

impl<R: Read> Parse<R> {
    /// Creates a new [`Parse`].
    fn new(reader: R) -> Self {
        Self {
            unfolder: UnfoldingReader::new(reader),
        }
    }
}

impl<R: Read> Iterator for Parse<R> {
    type Item = Result<Contentline, ParseError>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.unfolder.next_line()? {
            Ok(next_line) => Some(Contentline::parse(next_line).map_err(|err| err.into())),
            Err(err) => Some(Err(err.into())),
        }
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
pub struct Contentline {
    /// The group of the content line.
    pub group: Option<Identifier>,
    /// The name of the content line.
    pub name: Identifier,
    /// The parameters of the content line.
    pub params: Vec<Param>,
    /// The value of the content line.
    pub value: Value,
}

impl Contentline {
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

impl Display for Contentline {
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

// TODO check that identifiers have length >= 1
/// A [`String`] wrapper that may only contain alphabetic chars, digits and dashes (`-`).
#[derive(Clone, Debug, Eq, Ord, PartialOrd)]
pub struct Identifier {
    value: String,
}

impl Identifier {
    /// Creates a new [`Identifier`].
    ///
    /// # Errors
    ///
    /// Fails if the argument contains any characters which are
    /// neither alphabetic, digits or dash (`-`).
    pub fn new(identifier: String) -> Result<Self, InvalidIdentifier> {
        if identifier.chars().all(is_identifier_char) {
            Ok(Self { value: identifier })
        } else {
            Err(InvalidIdentifier)
        }
    }

    /// Returns the string value of this [`ParamValue`].
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{identifier}", identifier = self.value)
    }
}

impl TryFrom<String> for Identifier {
    type Error = InvalidIdentifier;
    fn try_from(identifier: String) -> Result<Self, Self::Error> {
        Self::new(identifier)
    }
}

impl TryFrom<&str> for Identifier {
    type Error = InvalidIdentifier;
    fn try_from(identifier: &str) -> Result<Self, Self::Error> {
        Self::new(identifier.to_owned())
    }
}

impl Hash for Identifier {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // implementation is mostly the same as in std::str
        for c in self.value.as_bytes() {
            c.to_ascii_uppercase().hash(state);
        }
        state.write_u8(0xff);
    }
}

impl PartialEq for Identifier {
    fn eq(&self, other: &Self) -> bool {
        *self == other.value
    }
}

impl PartialEq<String> for Identifier {
    fn eq(&self, other: &String) -> bool {
        *self == other.as_str()
    }
}

impl PartialEq<&str> for Identifier {
    fn eq(&self, other: &&str) -> bool {
        *self == **other
    }
}

impl PartialEq<str> for Identifier {
    fn eq(&self, other: &str) -> bool {
        self.value.eq_ignore_ascii_case(other)
    }
}

/// Indicates a failed attempt to create an [`Identifier`].
///
/// An [`Identifier`] can only contain alphanumeric characters and dashes (`-`). An
/// [`InvalidIdentifier`] error is the result of not respecting this restriction.
#[derive(Debug, Error)]
pub struct InvalidIdentifier;

impl Display for InvalidIdentifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "an identifier can only contain alphanumeric characters and dashes ('-')"
        )
    }
}

/// A single parameter of a [`Contentline`].
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct Param {
    name: Identifier,
    values: Vec<ParamValue>,
}

impl Param {
    /// Creates a new [`Param`].
    ///
    /// # Errors
    ///
    /// Fails if the values [`Vec`] is empty.
    pub fn new(name: Identifier, values: Vec<ParamValue>) -> Result<Self, InvalidParam> {
        if values.is_empty() {
            Err(InvalidParam)
        } else {
            Ok(Self { name, values })
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

/// A value of a [`Param`].
///
/// This is a wrapper around a [`String`] that contains no control characters except horizontal
/// tabs (`'\t'`) and linefeeds (`'\n'`).
#[derive(Clone, Debug, Eq, Ord, PartialOrd)]
pub struct ParamValue {
    value: String,
}

impl ParamValue {
    /// Creates a new [`ParamValue`].
    ///
    /// # Errors
    ///
    /// Fails if the argument contains control characters other than horizontal tabs (`'\t'`) and
    /// linefeeds (`'\n'`).
    pub fn new(value: String) -> Result<Self, InvalidParamValue> {
        if value.contains(|c| is_control(c) && c != '\n') {
            Err(InvalidParamValue)
        } else {
            Ok(Self { value })
        }
    }

    /// Returns the string value of this [`ParamValue`].
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl Display for ParamValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.value)
    }
}

impl TryFrom<String> for ParamValue {
    type Error = InvalidParamValue;
    fn try_from(value: String) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}

impl TryFrom<&str> for ParamValue {
    type Error = InvalidParamValue;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Self::new(value.to_owned())
    }
}

impl Hash for ParamValue {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

impl PartialEq for ParamValue {
    fn eq(&self, other: &Self) -> bool {
        *self == other.value
    }
}

impl PartialEq<String> for ParamValue {
    fn eq(&self, other: &String) -> bool {
        *self == other.as_str()
    }
}

impl PartialEq<&str> for ParamValue {
    fn eq(&self, other: &&str) -> bool {
        *self == **other
    }
}

impl PartialEq<str> for ParamValue {
    fn eq(&self, other: &str) -> bool {
        self.value == other
    }
}

/// Indicates a failed attempt to create a [`ParamValue`].
///
/// This error type is returned if one attempts to create a [`ParamValue`] from a string that
/// contains control characters other than horizontal tabs (`'\t'`).
#[derive(Debug, Error)]
pub struct InvalidParamValue;

impl Display for InvalidParamValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "param value may not contain any control characters")
    }
}

/// The value of a [`Contentline`].
///
/// This is a wrapper around a [`String`] that contains no control characters except horizontal
/// tabs (`'\t'`).
#[derive(Clone, Debug, Eq, Ord, PartialOrd)]
pub struct Value {
    value: String,
}

impl Value {
    /// Creates a new [`Value`].
    ///
    /// Fails if the argument contains control characters other than horizontal tabs (`'\t'`).
    pub fn new(value: String) -> Result<Self, InvalidValue> {
        if value.contains(is_control) {
            Err(InvalidValue)
        } else {
            Ok(Self { value })
        }
    }

    /// Returns the string value of this [`Value`].
    pub fn value(&self) -> &str {
        &self.value
    }
}

impl Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", &self.value)
    }
}

impl TryFrom<String> for Value {
    type Error = InvalidValue;
    fn try_from(value: String) -> Result<Self, Self::Error> {
        Self::new(value)
    }
}

impl TryFrom<&str> for Value {
    type Error = InvalidValue;
    fn try_from(value: &str) -> Result<Self, Self::Error> {
        Self::new(value.to_owned())
    }
}

impl Hash for Value {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.value.hash(state)
    }
}

impl PartialEq for Value {
    fn eq(&self, other: &Self) -> bool {
        *self == other.value
    }
}

impl PartialEq<String> for Value {
    fn eq(&self, other: &String) -> bool {
        *self == other.as_str()
    }
}

impl PartialEq<&str> for Value {
    fn eq(&self, other: &&str) -> bool {
        *self == **other
    }
}

impl PartialEq<str> for Value {
    fn eq(&self, other: &str) -> bool {
        self.value == other
    }
}

/// Indicates a failed attempt to create a [`Value`].
///
/// This error type is returned if one attempts to create a [`Value`] from a string that contains
/// control characters other than horizontal tabs (`'\t'`).
#[derive(Debug, Error)]
pub struct InvalidValue;

impl Display for InvalidValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "value may not contain any control characters")
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
) -> Result<(Option<Identifier>, Identifier), IntermediateParsingError> {
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
fn parse_param_values(contentline: &mut &str) -> Result<Vec<ParamValue>, IntermediateParsingError> {
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
fn parse_param_value(contentline: &mut &str) -> Result<ParamValue, IntermediateParsingError> {
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
fn parse_quoted_string(contentline: &mut &str) -> Result<String, IntermediateParsingError> {
    debug_assert!(contentline.starts_with('"'));

    *contentline = &contentline[1..];

    let quoted_string_length = contentline
        .find(|c| !is_qsafe_char(c))
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
        .find(|c| !is_safe_char(c))
        .unwrap_or(contentline.len());

    let paramtext = parse_param_value_rfc6868(&contentline[..paramtext_length]);

    *contentline = &contentline[paramtext_length..];

    paramtext
}

/// Takes a `paramtext` of the value of a `quoted-string` and returns a [`String`] where all the
/// escape sequences defined in [RFC 6868][rfc6868] are parsed correctly.
///
/// [rfc6868]: https://www.rfc-editor.org/rfc/rfc6868
fn parse_param_value_rfc6868(mut param_value: &str) -> String {
    debug_assert!(param_value.chars().all(is_qsafe_char));

    let mut result = String::with_capacity(param_value.len());

    while let Some(index) = param_value.find('^') {
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
    }

    result.push_str(param_value);

    result
}

/// Parses a [`Value`].
///
/// # Errors
///
/// Fails if the argument contains control characters other than horizontal tabs (see also
/// [`is_control()`]).
fn parse_value(contentline: &mut &str) -> Result<Value, IntermediateParsingError> {
    if contentline.contains(is_control) {
        Err(IntermediateParsingError)
    } else {
        let value = Value {
            value: contentline.to_owned(),
        };
        *contentline = "";

        Ok(value)
    }
}

/// Parses an [`Identifier`].
///
/// # Errors
///
/// Fails if the first char of the argument is not [`is_identifier_char()`].
fn parse_identifier(contentline: &mut &str) -> Result<Identifier, IntermediateParsingError> {
    let identifier_length = contentline
        .find(|c| !is_identifier_char(c))
        .unwrap_or(contentline.len());

    // identifier cannot be an empty string
    if identifier_length == 0 {
        Err(IntermediateParsingError)
    } else {
        let identifier = Identifier {
            value: contentline[..identifier_length].to_owned(),
        };
        *contentline = &contentline[identifier_length..];

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

/// Checks whether a [`char`] is a `SAFE_CHAR`.
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
fn is_safe_char(c: char) -> bool {
    !is_control(c) && (c != '"') && (c != ';') && (c != ':') && (c != ',')
}

/// Checks whether a [`char`] is a `QSAFE_CHAR`.
///
/// ABNF from [RFC 5545][rfc5545]:
///
/// ```text
/// QSAFE-CHAR    = WSP / %x21 / %x23-7E / NON-US-ASCII
/// ; Any character except CONTROL and DQUOTE
/// ```
///
/// [rfc5545]: https://www.rfc-editor.org/rfc/rfc5545
fn is_qsafe_char(c: char) -> bool {
    !is_control(c) && (c != '"')
}

/// Checks whether a [`char`] is a `CONTROL`.
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
fn is_control(c: char) -> bool {
    char::is_control(c) && (c != '\t')
}

/// Checks whether a [`char`] is alphanumeric or a dash (`'-'`).
fn is_identifier_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '-'
}

#[cfg(test)]
mod tests {
    mod parse {
        use {
            crate::{Contentline, Identifier, Param, ParamValue, Value},
            std::iter,
        };

        #[test]
        fn name_and_value() {
            let contentline = "NOTE:This is a note.";
            let parsed = crate::parse(contentline.as_bytes())
                .collect::<Result<Vec<_>, _>>()
                .unwrap();

            assert_eq!(parsed.len(), 1);
            assert_eq!(
                parsed[0],
                Contentline {
                    group: None,
                    name: Identifier::try_from("NOTE").unwrap(),
                    params: Vec::new(),
                    value: Value::try_from("This is a note.").unwrap(),
                }
            );
        }

        #[test]
        fn group_name_params_value() {
            let contentline =
                "test-group.TEST-CASE;test-param=PARAM1;another-test-param=PARAM2:value";
            let parsed = crate::parse(contentline.as_bytes())
                .collect::<Result<Vec<_>, _>>()
                .unwrap();

            assert_eq!(parsed.len(), 1);
            assert_eq!(
                parsed[0],
                Contentline {
                    group: Some(Identifier::try_from("test-group").unwrap()),
                    name: Identifier::try_from("TEST-CASE").unwrap(),
                    params: vec![
                        Param::new(
                            Identifier::try_from("test-param").unwrap(),
                            vec![ParamValue::try_from("PARAM1").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::try_from("another-test-param").unwrap(),
                            vec![ParamValue::try_from("PARAM2").unwrap()]
                        )
                        .unwrap(),
                    ],
                    value: Value::try_from("value").unwrap(),
                }
            );
        }

        #[test]
        fn empty_value() {
            let empty_value = "EMPTY-VALUE:";
            let parsed = crate::parse(empty_value.as_bytes())
                .collect::<Result<Vec<_>, _>>()
                .unwrap();

            assert_eq!(parsed.len(), 1);
            assert_eq!(
                parsed[0],
                Contentline {
                    group: None,
                    name: Identifier::try_from("EMPTY-VALUE").unwrap(),
                    params: Vec::new(),
                    value: Value::try_from("").unwrap(),
                }
            );
        }

        #[test]
        fn empty_param() {
            let empty_param = "EMPTY-PARAM;paramtext=;quoted-string=\"\";multiple=,,,,\"\",\"\",,\"\",,,\"\":value";
            let parsed = crate::parse(empty_param.as_bytes())
                .collect::<Result<Vec<_>, _>>()
                .unwrap();

            assert_eq!(parsed.len(), 1);
            assert_eq!(
                parsed[0],
                Contentline {
                    group: None,
                    name: Identifier::try_from("EMPTY-PARAM").unwrap(),
                    params: vec![
                        Param::new(
                            Identifier::try_from("paramtext").unwrap(),
                            vec![ParamValue::try_from("").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::try_from("quoted-string").unwrap(),
                            vec![ParamValue::try_from("").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::try_from("multiple").unwrap(),
                            iter::repeat(ParamValue::try_from("").unwrap())
                                .take(11)
                                .collect()
                        )
                        .unwrap(),
                    ],
                    value: Value::try_from("value").unwrap(),
                }
            );
        }

        #[test]
        fn case_insensitivity() {
            let contentline0 = "Group.lowerUPPER;PaRaM=parameter value:value";
            let contentline1 = "group.LOWERupper;PARAm=parameter value:value";

            let parsed0 = crate::parse(contentline0.as_bytes())
                .collect::<Result<Vec<_>, _>>()
                .unwrap();
            let parsed1 = crate::parse(contentline1.as_bytes())
                .collect::<Result<Vec<_>, _>>()
                .unwrap();

            assert_eq!(parsed0, parsed1);
            assert_eq!(parsed0.len(), 1);
        }

        #[test]
        fn rfc6868() {
            let contentline = "RFC6868-TEST;caret=^^;newline=^n;double-quote=^';all-in-quotes=\"^^^n^'\";weird=^^^^n;others=^g^5^k^?^%^&^a:value";
            let parsed = crate::parse(contentline.as_bytes())
                .collect::<Result<Vec<_>, _>>()
                .unwrap();

            assert_eq!(parsed.len(), 1);
            assert_eq!(
                parsed[0],
                Contentline {
                    group: None,
                    name: Identifier::try_from("RFC6868-TEST").unwrap(),
                    params: vec![
                        Param::new(
                            Identifier::try_from("caret").unwrap(),
                            vec![ParamValue::try_from("^").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::try_from("newline").unwrap(),
                            vec![ParamValue::try_from("\n").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::try_from("double-quote").unwrap(),
                            vec![ParamValue::try_from("\"").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::try_from("all-in-quotes").unwrap(),
                            vec![ParamValue::try_from("^\n\"").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::try_from("weird").unwrap(),
                            vec![ParamValue::try_from("^^n").unwrap()]
                        )
                        .unwrap(),
                        Param::new(
                            Identifier::try_from("others").unwrap(),
                            vec![ParamValue::try_from("^g^5^k^?^%^&^a").unwrap()]
                        )
                        .unwrap(),
                    ],
                    value: Value::try_from("value").unwrap(),
                }
            );
        }
    }

    mod write {
        use {
            crate::{Contentline, Identifier, Param, ParamValue, Value},
            std::{iter, str},
        };

        #[test]
        fn name_and_value() {
            let contentline = Contentline {
                group: None,
                name: Identifier::try_from("NAME").unwrap(),
                params: Vec::new(),
                value: Value::try_from("VALUE").unwrap(),
            };

            let expected = "NAME:VALUE\r\n";

            let actual = {
                let mut buffer = Vec::new();
                crate::write(iter::once(&contentline), &mut buffer).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(&actual, expected);
        }

        #[test]
        fn group_name_params_value() {
            let contentline = Contentline {
                group: Some(Identifier::try_from("TEST-GROUP").unwrap()),
                name: Identifier::try_from("TEST-NAME").unwrap(),
                params: vec![
                    Param::new(
                        Identifier::try_from("PARAM-1").unwrap(),
                        vec![ParamValue::try_from("param value 1").unwrap()],
                    )
                    .unwrap(),
                    Param::new(
                        Identifier::try_from("PARAM-2").unwrap(),
                        vec![ParamValue::try_from("param value of parameter: 2").unwrap()],
                    )
                    .unwrap(),
                ],
                value: Value::try_from("test value \"with quotes\"").unwrap(),
            };

            let expected = "\
TEST-GROUP.TEST-NAME;PARAM-1=param value 1;PARAM-2=\"param value of paramete\r
 r: 2\":test value \"with quotes\"\r
";

            let actual = {
                let mut buffer = Vec::new();
                crate::write(iter::once(&contentline), &mut buffer).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(&actual, expected);
        }

        #[test]
        fn identfiers_converted_to_uppercase() {
            let contentline = Contentline {
                group: Some(Identifier::try_from("lower-group").unwrap()),
                name: Identifier::try_from("name").unwrap(),
                params: vec![Param::new(
                    Identifier::try_from("PaRaM").unwrap(),
                    vec![ParamValue::try_from("param value").unwrap()],
                )
                .unwrap()],
                value: Value::try_from("value").unwrap(),
            };

            let expected = "LOWER-GROUP.NAME;PARAM=param value:value\r\n";

            let actual = {
                let mut buffer = Vec::new();
                crate::write(iter::once(&contentline), &mut buffer).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(&actual, expected);
        }

        #[test]
        fn empty_value() {
            let contentline = Contentline {
                group: None,
                name: Identifier::try_from("NAME").unwrap(),
                params: Vec::new(),
                value: Value::try_from("").unwrap(),
            };

            let expected = "NAME:\r\n";

            let actual = {
                let mut buffer = Vec::new();
                crate::write(iter::once(&contentline), &mut buffer).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(&actual, expected);
        }

        #[test]
        fn empty_param() {
            let num_params = 15;

            let contentline = Contentline {
                group: None,
                name: Identifier::try_from("NAME").unwrap(),
                params: vec![Param::new(
                    Identifier::try_from("PARAM").unwrap(),
                    iter::repeat(ParamValue::try_from("").unwrap())
                        .take(num_params)
                        .collect(),
                )
                .unwrap()],
                value: Value::try_from("value").unwrap(),
            };

            let expected = {
                let mut expected = String::from("NAME;PARAM=");
                expected.push_str(&",".repeat(num_params - 1));
                expected.push_str(":value\r\n");
                expected
            };

            let actual = {
                let mut buffer = Vec::new();
                crate::write(iter::once(&contentline), &mut buffer).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(actual, expected);
        }

        #[test]
        fn rfc6868() {
            let contentline = Contentline {
                group: None,
                name: Identifier::try_from("RFC6868-TEST").unwrap(),
                params: vec![
                    Param::new(
                        Identifier::try_from("CARET").unwrap(),
                        vec![ParamValue::try_from("^").unwrap()],
                    )
                    .unwrap(),
                    Param::new(
                        Identifier::try_from("NEWLINE").unwrap(),
                        vec![ParamValue::try_from("\n").unwrap()],
                    )
                    .unwrap(),
                    Param::new(
                        Identifier::try_from("DOUBLE-QUOTE").unwrap(),
                        vec![ParamValue::try_from("\"").unwrap()],
                    )
                    .unwrap(),
                    Param::new(
                        Identifier::try_from("ALL-IN-QUOTES").unwrap(),
                        vec![ParamValue::try_from("^;\n;\"").unwrap()],
                    )
                    .unwrap(),
                    Param::new(
                        Identifier::try_from("WEIRD").unwrap(),
                        vec![ParamValue::try_from("^^n").unwrap()],
                    )
                    .unwrap(),
                ],
                value: Value::try_from("value").unwrap(),
            };

            let expected = "RFC6868-TEST;CARET=^^;NEWLINE=^n;DOUBLE-QUOTE=^';ALL-IN-QUOTES=\"^^;^n;^'\";W\r\n EIRD=^^^^n:value\r\n";

            let actual = {
                let mut buffer = Vec::new();
                crate::write(iter::once(&contentline), &mut buffer).unwrap();
                str::from_utf8(&buffer).unwrap().to_owned()
            };

            assert_eq!(&actual, expected);
        }
    }
}
