mod enum_variant;
use enum_variant::variant_attr_args;

use proc_macro::TokenStream;
use quote::quote;
use syn::parse_macro_input;
use syn::Data;
use syn::DeriveInput;

#[proc_macro_derive(EnumFrom, attributes(enum_from))]
pub fn enum_from(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let enum_name = input.ident;
    let vars = match input.data {
        Data::Enum(data) => variant_attr_args(data, "enum_from", "str"),
        _ => panic!("{} is not an enum", enum_name),
    };

    let from_str = vars
        .iter()
        .map(|(variant, value)| {
            format!("{} => Ok(Self::{})", value, variant)
                .parse()
                .unwrap()
        })
        .collect::<Vec<proc_macro2::TokenStream>>();

    let to_str = vars
        .iter()
        .map(|(variant, value)| format!("Self::{} => {}", variant, value).parse().unwrap())
        .collect::<Vec<proc_macro2::TokenStream>>();

    (quote! {
        impl ::std::str::FromStr for #enum_name {
            type Err = &'static str;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                match s {
                    #(#from_str,)*
                    _ => Err("not found"),
                }
            }
        }

        impl #enum_name {
            fn to_str(&self) -> &'static str {
                match self {
                    #(#to_str,)*
                }
            }
        }
    })
    .into()
}
