
[![crates.io](https://img.shields.io/crates/v/ical_vcard?style=flat-square)](https://crates.io/crates/ical_vcard)
[![build status](https://img.shields.io/github/actions/workflow/status/darkfirezz/ical_vcard/ci.yml?style=flat-square)](https://github.com/darkfireZZ/ical_vcard/actions/workflows/ci.yml)
[![docs.rs](https://img.shields.io/docsrs/ical_vcard?style=flat-square)](https://docs.rs/ical_vcard)
[![codecov](https://img.shields.io/codecov/c/github/darkfirezz/ical_vcard?style=flat-square)](https://app.codecov.io/gh/darkfireZZ/ical_vcard)

# ical_vcard

[ical_vcard][crate] provides a parser and a writer implementation for the content line format that is
the base of both the iCalendar ([RFC 5545][rfc5545]) and the vCard ([RFC 6350][rfc6350]) data
formats. It is NOT a full implementation of either of the standards. Rather, [ical_vcard][crate] is
intended as a foundation on top of which a full-fledged iCalendar or vCard parser and writer can be
built.

This crate can of course be used to parse iCalendar or vCard files. However, it cannot provide the
convenience or all of the features a specialized iCalendar or vCard library could.

## Features

 * Content line parser
 * Content line writer / formatter
 * Conforms to [RFC 5545][rfc5545] and [RFC 6350][rfc6350]. In particular, the parser and the writer
   adhere to [section 3.1 of RFC5545][rfc5545_sec3_1] and [section 3 of RFC 6350][rfc6350_sec3],
   which describe the content line format.
 * Conforms to [RFC 6868][rfc6868], which updates [RFC 5545][rfc5545] and [RFC 6350][rfc6350] with
   escape rules for encoding double quotes and line breaks in parameter values.
 * No unsafe code

### Example: Parsing Birthdays

This example shows how to transform a vCard file into a [`HashMap`][hashmap] that maps names to
birthdays.

```rust
use {
    ical_vcard::Parser,
    std::collections::HashMap,
};

let vcard_file = "\
BEGIN:VCARD\r
FN:Mark Daniels\r
BDAY:19830525\r
END:VCARD\r
BEGIN:VCARD\r
FN:Peter Smith\r
BDAY:19770525\r
EMAIL:peter.smith@example.com\r
END:VCARD\r
BEGIN:VCARD\r
BDAY:19800521\r
FN:Jack Black\r
END:VCARD\r
".as_bytes();

let birthdays: HashMap<_, _> = Parser::new(vcard_file)
    .collect::<Result<Vec<_>, _>>()
    .expect("valid vcard file")
    .split(|contentline| contentline.name() == "BEGIN" && contentline.value() == "VCARD")
    .flat_map(|vcard| {
        let name = vcard
            .iter()
            .find(|contentline| contentline.name() == "FN")?
            .value()
            .to_string();
        let birthday = vcard
            .iter()
            .find(|contentline| contentline.name() == "BDAY")?
            .value()
            .to_string();

        Some((name, birthday))
    })
    .collect();

assert_eq!(birthdays["Peter Smith"], "19770525");
assert_eq!(birthdays["Jack Black"], "19800521");
assert_eq!(birthdays["Mark Daniels"], "19830525");
```

### Example: Names & Email Addresses

This example illustrates how to write a vCard file.

```rust
use ical_vcard::{Contentline, Identifier, Param, ParamValue, Value, Writer};

let names = [
    "Aristotle",
    "Plato",
    "Pythagoras",
    "Thales",
];

let contentlines = names.into_iter()
    .flat_map(|name| [
        Contentline::new("BEGIN", "VCARD"),
        Contentline::new("FN", name),
        Contentline::new("N", format!(";{name};;;")),
        Contentline::new("EMAIL", format!("{name}@ancient-philosophers.gr", name = name.to_lowercase()))
            .add_param("TYPE", ["work"]),
        Contentline::new("END", "VCARD"),
    ]);

let vcard = {
    let mut buffer = Vec::new();
    let mut writer = Writer::new(&mut buffer);
    writer.write_all(contentlines).expect("write to Vec should cause no errors");
    String::from_utf8(buffer).expect("Output is valid UTF-8")
};

let expected = "\
BEGIN:VCARD\r
FN:Aristotle\r
N:;Aristotle;;;\r
EMAIL;TYPE=work:aristotle@ancient-philosophers.gr\r
END:VCARD\r
BEGIN:VCARD\r
FN:Plato\r
N:;Plato;;;\r
EMAIL;TYPE=work:plato@ancient-philosophers.gr\r
END:VCARD\r
BEGIN:VCARD\r
FN:Pythagoras\r
N:;Pythagoras;;;\r
EMAIL;TYPE=work:pythagoras@ancient-philosophers.gr\r
END:VCARD\r
BEGIN:VCARD\r
FN:Thales\r
N:;Thales;;;\r
EMAIL;TYPE=work:thales@ancient-philosophers.gr\r
END:VCARD\r
";

assert_eq!(vcard, expected);
```

## License

This project is licensed under the [MIT License](./LICENSE-MIT) or
[version 2.0 of the Apache License](./LICENSE-APACHE).

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

[crate]: #
[hashmap]: https://doc.rust-lang.org/stable/std/collections/struct.HashMap.html
[iterator]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
[read]: https://doc.rust-lang.org/stable/std/io/trait.Read.html
[rfc5545]: https://www.rfc-editor.org/rfc/rfc5545
[rfc5545_sec3_1]: https://www.rfc-editor.org/rfc/rfc5545#section-3.1
[rfc6350]: https://www.rfc-editor.org/rfc/rfc6350
[rfc6350_sec3]: https://www.rfc-editor.org/rfc/rfc6350#section-3
[rfc6868]: https://www.rfc-editor.org/rfc/rfc6868
[write]: https://doc.rust-lang.org/stable/std/io/trait.Write.html
