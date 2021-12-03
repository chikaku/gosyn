use proc_macro2::TokenStream;
use quote::quote;
use syn::punctuated::Punctuated;
use syn::token::Comma;
use syn::DataEnum;
use syn::Field;
use syn::Fields;
use syn::Ident;

pub(crate) struct EnumFromWrapped {
    enum_name: Ident,
    enum_data: DataEnum,
}

impl EnumFromWrapped {
    pub fn new(enum_name: Ident, enum_data: DataEnum) -> Self {
        EnumFromWrapped {
            enum_name,
            enum_data,
        }
    }

    fn get_wrapped(&self, fields: Fields) -> Punctuated<Field, Comma> {
        let err = format!("{}: can not use EnumFromWrapped", self.enum_name);
        match fields {
            Fields::Unnamed(field) => field.unnamed,
            Fields::Unit => panic!("{} with unit variant", err),
            Fields::Named(_) => panic!("{} with named variant", err),
        }
    }

    pub fn write_output(&self) -> TokenStream {
        self.enum_data
            .variants
            .iter()
            .map(|var| {
                let var_name = &var.ident;
                let enum_name = &self.enum_name;
                let wrapped = self.get_wrapped(var.fields.clone());

                quote! {
                    impl From<#wrapped> for #enum_name {
                        fn from(inner: #wrapped) -> Self {
                            Self::#var_name(inner)
                        }
                    }
                }
            })
            .collect()
    }
}
