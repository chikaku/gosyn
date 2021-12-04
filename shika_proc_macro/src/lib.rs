#![feature(bool_to_option)]

use proc_macro::TokenStream;
use syn::parse_macro_input;
use syn::punctuated::Punctuated;
use syn::token::Comma;
use syn::Data;
use syn::DataEnum;
use syn::DeriveInput;
use syn::Field;
use syn::Fields;
use syn::Ident;

mod enum_from;
mod enum_from_wrapped;
mod enum_into_wrapped;

use enum_from::EnumFrom;
use enum_from_wrapped::EnumFromWrapped;
use enum_into_wrapped::EnumIntoWrapped;

#[proc_macro_derive(EnumFrom, attributes(enum_from))]
pub fn enum_from(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let (id, data) = assert_enum("EnumFrom", input);
    let mut handler = EnumFrom::new(id, data);
    handler.parse_attributes();
    handler.write_output().into()
}

#[proc_macro_derive(EnumFromWrapped)]
pub fn enum_from_wrapped(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let (id, data) = assert_enum("EnumFromWrapped", input);
    EnumFromWrapped::new(id, data).write_output().into()
}

#[proc_macro_derive(EnumIntoWrapped)]
pub fn enum_into_wrapped(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let (id, data) = assert_enum("EnumIntoWrapped", input);
    EnumIntoWrapped::new(id, data).write_output().into()
}

fn assert_enum(name: &str, input: DeriveInput) -> (Ident, DataEnum) {
    let ident = input.ident.clone();
    match input.data {
        Data::Enum(data) => (ident, data),
        _ => panic!("{} must be an enum to use {}", &ident, name),
    }
}

fn get_wrapped_unnamed(
    macro_name: &str,
    enum_name: &Ident,
    fields: Fields,
) -> Punctuated<Field, Comma> {
    let err = format!("{}: can not use {}", enum_name, macro_name);
    match fields {
        Fields::Unnamed(field) => field.unnamed,
        Fields::Unit => panic!("{} with unit variant", err),
        Fields::Named(_) => panic!("{} with named variant", err),
    }
}
