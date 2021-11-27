#![feature(bool_to_option)]

use proc_macro::TokenStream;
use syn::parse_macro_input;
use syn::DeriveInput;

mod enum_from;
use enum_from::EnumFrom;

#[proc_macro_derive(EnumFrom, attributes(enum_from))]
pub fn enum_from(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let mut handler = EnumFrom::new(input);
    handler.parse_attributes();
    handler.write_output().into()
}
