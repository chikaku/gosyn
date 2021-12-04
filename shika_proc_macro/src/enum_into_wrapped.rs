use crate::get_wrapped_unnamed;
use proc_macro2::TokenStream;
use quote::quote;
use syn::DataEnum;
use syn::Ident;

pub(crate) struct EnumIntoWrapped {
    enum_name: Ident,
    enum_data: DataEnum,
}

impl EnumIntoWrapped {
    pub fn new(enum_name: Ident, enum_data: DataEnum) -> Self {
        EnumIntoWrapped {
            enum_name,
            enum_data,
        }
    }

    pub fn write_output(&self) -> TokenStream {
        self.enum_data
            .variants
            .iter()
            .map(|var| {
                let var_name = &var.ident;
                let enum_name = &self.enum_name;
                let wrapped = get_wrapped_unnamed("EnumIntoWrapped", enum_name, var.fields.clone());

                quote! {
                    impl ::std::convert::TryFrom<#enum_name> for #wrapped {
                        type Error = ();
                    
                        fn try_from(value: #enum_name) -> ::core::result::Result<Self, Self::Error> {
                            match value {
                                #enum_name::#var_name(res) => Ok(res),
                                _ => Err(()),
                            }
                        }
                    }
                }
            })
            .collect()
    }
}