#![feature(bool_to_option)]

use proc_macro::TokenStream;
use syn::parse_macro_input;
use syn::Data;
use syn::DataEnum;
use syn::DeriveInput;
use syn::Ident;

mod enum_from;
mod enum_from_wrapped;

use enum_from::EnumFrom;
use enum_from_wrapped::EnumFromWrapped;

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

fn assert_enum(name: &str, input: DeriveInput) -> (Ident, DataEnum) {
    let ident = input.ident.clone();
    match input.data {
        Data::Enum(data) => (ident, data),
        _ => panic!("{} must be an enum to use {}", &ident, name),
    }
}
