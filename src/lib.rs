// TODO add documentation
//!

#![deny(unsafe_code)]
#![deny(clippy::all)]
// TODO implement cargo lints: #![warn(clippy::cargo)]
#![warn(missing_docs)]

use {
    crate::folding::UnfoldingReader,
    std::{
        fmt::{self, Display},
        io::{self, BufRead},
        iter::Iterator,
    },
    thiserror::Error,
};

pub mod folding;

// TODO improve documentation & add examples
/// Parses a vCard or iCalendar file.
///
/// Returns an [`Iterator`] of [`Contentline`]s.
pub fn read<R: BufRead>(vcard_or_ical_file: R) -> ContentlineParser<R> {
    ContentlineParser::new(vcard_or_ical_file)
}

/// A iCalendar or vCard parser.
///
/// Using the parser is very straightforward as it implements [`Iterator`]:
///
/// ```
/// use ical_vcard::{Contentline, ContentlineParser, Identifier, Param, ParamValue, ParseError, Value};
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
/// let parsed_vcard = ContentlineParser::new(vcard_file.as_bytes()).collect::<Result<Vec<_>, _>>().unwrap();
///
/// assert_eq!(parsed_vcard[2], Contentline {
///     group: Some(Identifier::new(String::from("namegroup")).unwrap()),
///     name: Identifier::new(String::from("FN")).unwrap(),
///     params: Vec::new(),
///     value: Value::new(String::from("Michelle de Pierre")).unwrap(),
/// });
///
/// assert_eq!(parsed_vcard[4], Contentline {
///     group: None,
///     name: Identifier::new(String::from("EMAIL")).unwrap(),
///     params: vec![Param::new(
///         Identifier::new(String::from("TYPE")).unwrap(),
///         vec![ParamValue::new(String::from("work")).unwrap()]
///     ).unwrap()],
///     value: Value::new(String::from("michelle.depierre@example.com")).unwrap(),
/// });
/// ```
pub struct ContentlineParser<R: BufRead> {
    unfolder: UnfoldingReader<R>,
}

impl<R: BufRead> ContentlineParser<R> {
    /// Creates a new [`ContentlineParser`].
    pub fn new(reader: R) -> Self {
        Self {
            unfolder: UnfoldingReader::new(reader),
        }
    }
}

impl<R: BufRead> Iterator for ContentlineParser<R> {
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
/// 4. Optionally, a list of parameters to add metainformation or additional details that don't fit
///    into `value` field particularly well
#[derive(Clone, Debug, Eq, PartialEq)]
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
    pub fn parse(mut contentline: &str) -> Result<Self, ParseContentlineError> {
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
}

// TODO maybe also add some contextual information.
/// Indicates a failure to parse a [`Contentline`].
#[derive(Debug, Error)]
pub struct ParseContentlineError {
    invalid_contentline: String,
}

impl Display for ParseContentlineError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        // TODO cap size of contentline in display
        write!(f, "invalid contentline: \"{}\"", self.invalid_contentline)
    }
}

/// A [`String`] wrapper that may only contain alphabetic chars, digits and dashes (`-`).
#[derive(Clone, Debug, Eq)]
pub struct Identifier {
    identifier: String,
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
            Ok(Self { identifier })
        } else {
            Err(InvalidIdentifier)
        }
    }
}

impl Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{identifier}", identifier = self.identifier)
    }
}

impl PartialEq for Identifier {
    fn eq(&self, other: &Self) -> bool {
        self.identifier.eq_ignore_ascii_case(&other.identifier)
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
#[derive(Clone, Debug, Eq, PartialEq)]
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
/// tabs (`'\t').
///
/// Implements [RFC 6868][rfc6868].
///
/// [rfc6868]: https://www.rfc-editor.org/rfc/rfc6868
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParamValue {
    value: String,
}

impl ParamValue {
    /// Creates a new [`ParamValue`].
    ///
    /// # Errors
    ///
    /// Fails if the argument contains control characters other than horizontal tabs (`'\t'`).
    pub fn new(value: String) -> Result<Self, InvalidParamValue> {
        // TODO implement RFC 6868 conversion
        if value.contains(is_control) {
            Err(InvalidParamValue)
        } else {
            Ok(Self { value })
        }
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
#[derive(Clone, Debug, Eq, PartialEq)]
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

    Ok(ParamValue {
        value: param_value.to_owned(),
    })
}

// TODO implement RFC 6868
/// Parses a `quoted-string`.
///
/// ABNF from [RFC 5545][rfc5545]:
///
/// ```text
/// quoted-string = DQUOTE *QSAFE-CHAR DQUOTE
/// ```
///
/// # Errors
///
/// Fails if the first character of the argument is not a double quote (`"`) or if there is no
/// closing double quote.
///
/// [rfc5545]: https://www.rfc-editor.org/rfc/rfc5545
fn parse_quoted_string<'a, 'b>(
    contentline: &'a mut &'b str,
) -> Result<&'b str, IntermediateParsingError> {
    if !contentline.starts_with('"') {
        return Err(IntermediateParsingError);
    }
    *contentline = &contentline[1..];

    let quoted_string_length = contentline
        .find(|c| !is_qsafe_char(c))
        .ok_or(IntermediateParsingError)?;
    if &contentline[quoted_string_length..quoted_string_length + 1] == "\"" {
        let quoted_string = &contentline[..quoted_string_length];
        *contentline = &contentline[quoted_string_length + 1..];
        Ok(quoted_string)
    } else {
        Err(IntermediateParsingError)
    }
}

// TODO implement RFC 6868
/// Parses a `paramtext`.
///
/// ABNF from [RFC 5545][rfc5545]:
///
/// ```text
/// paramtext = *SAFE-CHAR
/// ```
///
/// [rfc5545]: https://www.rfc-editor.org/rfc/rfc5545
fn parse_paramtext<'a, 'b>(contentline: &'a mut &'b str) -> &'b str {
    let paramtext_length = contentline
        .find(|c| !is_safe_char(c))
        .unwrap_or(contentline.len());
    let paramtext = &contentline[..paramtext_length];
    *contentline = &contentline[paramtext_length..];

    paramtext
}

/// Parses a [`Value`].
///
/// # Errors
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
            identifier: contentline[..identifier_length].to_owned(),
        };
        *contentline = &contentline[identifier_length..];

        Ok(identifier)
    }
}

/// An zero-sized error type used internally to indicate parsing errors.
struct IntermediateParsingError;

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
