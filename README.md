
# ical_vcard

[ical_vcard][crate] provides a parser and a writer implementation for the content line format that is
the base of both the iCalendar ([RFC 5545][rfc5545]) and the vCard ([RFC 6350][rfc6350]) data
formats. It is NOT a full implementation of either of the standards. Rather, [ical_vcard][crate] is
intended as a foundation on top of which a full-fledged iCalendar or vCard parser and writer can be
built.

This crate can of course be used to parse iCalendar or vCard files. However, it cannot provide the
convenience or all of the features a specialized iCalendar or vCard library could.

## Usage

The main functionality of this crate is provided by 2 functions:
 * [`parse()`], which takes an [`io::Read`][read] and parses it to an [`Iterator`][iterator] of
   content lines.
 * [`write()`], which takes an [`Iterator`][iterator] of content lines and writes them to an
   [`io::Write`][write].

For more detailed information, have a look at the documentation of the respective functions.

### Example: Parsing Birthdays

This example shows how to transform a vCard file into a [`HashMap`][hashmap] that maps names to
birthdays.

```rust
use std::collections::HashMap;

# fn main() -> Result<(), Box<dyn std::error::Error>> {
let vcard_file = "\
BEGIN:VCARD\r
FN:Mark Daniels\r
BDAY:19830525\r
END:VCARD\r
BEGIN:VCARD\r
FN:Peter Smith\r
BDAY:19770525\r
EMAIL:peter.smith@sw.com\r
END:VCARD\r
BEGIN:VCARD\r
BDAY:19800521\r
FN:Jack Black\r
END:VCARD\r
".as_bytes();

let birthdays: HashMap<_, _> = ical_vcard::parse(vcard_file)
    .collect::<Result<Vec<_>, _>>()?
    .split(|contentline| contentline.name == "BEGIN" && contentline.value == "VCARD")
    .flat_map(|vcard| {
        let name = vcard
            .iter()
            .find(|contentline| contentline.name == "FN")?
            .value
            .value()
            .to_owned();
        let birthday = vcard
            .iter()
            .find(|contentline| contentline.name == "BDAY")?
            .value
            .value()
            .to_owned();

        Some((name, birthday))
    })
    .collect();

assert_eq!(birthdays["Peter Smith"], "19770525");
assert_eq!(birthdays["Jack Black"], "19800521");
assert_eq!(birthdays["Mark Daniels"], "19830525");
#
# Ok(())
# }
```

### Example: Names & Email Addresses

This example illustrates how to write a vCard file.

```rust
use ical_vcard::{Contentline, Identifier, Param, ParamValue, Value};

# fn main() -> Result<(), Box<dyn std::error::Error>> {
let names = [
    "Aristotle",
    "Plato",
    "Pythagoras",
    "Thales",
];

let contentlines = names.into_iter().flat_map(|name| [
    Contentline {
        group: None,
        name: Identifier::try_from("BEGIN").unwrap(),
        params: Vec::new(),
        value: Value::try_from("VCARD").unwrap(),
    },
    Contentline {
        group: None,
        name: Identifier::try_from("FN").unwrap(),
        params: Vec::new(),
        value: Value::try_from(name).unwrap(),
    },
    Contentline {
        group: None,
        name: Identifier::try_from("N").unwrap(),
        params: Vec::new(),
        value: Value::new(format!(";{name};;;")).unwrap(),
    },
    Contentline {
        group: None,
        name: Identifier::try_from("EMAIL").unwrap(),
        params: vec![Param::new(
            Identifier::try_from("TYPE").unwrap(),
            vec![ParamValue::try_from("work").unwrap()]
        ).unwrap()],
        value: Value::new(
            format!("{name}@ancient-philosophers.gr", name = name.to_lowercase())
        ).unwrap(),
    },
    Contentline {
        group: None,
        name: Identifier::try_from("END").unwrap(),
        params: Vec::new(),
        value: Value::try_from("VCARD").unwrap(),
    },
]);

let vcard = {
    let mut buffer = Vec::new();
    ical_vcard::write(contentlines, &mut buffer)?;
    buffer
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
".as_bytes();

assert_eq!(vcard, expected);
#
# Ok(())
# }
```

[crate]: #
[hashmap]: https://doc.rust-lang.org/stable/std/collections/struct.HashMap.html
[iterator]: https://doc.rust-lang.org/stable/std/iter/trait.Iterator.html
[read]: https://doc.rust-lang.org/stable/std/io/trait.Read.html
[rfc5545]: https://www.rfc-editor.org/rfc/rfc5545
[rfc6350]: https://www.rfc-editor.org/rfc/rfc6350
[write]: https://doc.rust-lang.org/stable/std/io/trait.Write.html
