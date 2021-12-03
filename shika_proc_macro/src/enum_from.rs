use proc_macro2::TokenStream;
use quote::quote;
use std::collections::HashMap;
use syn::DataEnum;
use syn::Fields;
use syn::Ident;
use syn::Lit;
use syn::Meta;
use syn::NestedMeta;

pub(crate) struct EnumFrom {
    enum_name: Ident,
    enum_data: DataEnum,
    variants: Vec<Ident>,

    from_str: HashMap<Ident, String>,
    from_inner_enum: Vec<Ident>,
}

impl EnumFrom {
    pub fn new(enum_name: Ident, enum_data: DataEnum) -> Self {
        EnumFrom {
            enum_name,
            enum_data,
            variants: vec![],
            from_str: HashMap::new(),
            from_inner_enum: vec![],
        }
    }

    pub fn parse_attributes(&mut self) {
        let var_iters = || self.enum_data.variants.iter();
        self.variants = var_iters().map(|var| var.ident.clone()).collect();

        var_iters()
            // filter enum_from attributes
            .filter_map(|var| {
                var.attrs
                    .iter()
                    .find(|attr| attr.path.is_ident("enum_from"))
                    .and_then(|attr| Some((var.ident.clone(), attr.parse_meta())))
            })
            // map to variant name and attribute list
            .for_each(|(var_name, meta)| {
                let title = format!(
                    "enum_from attributes for {}::{} parse error",
                    self.enum_name, var_name,
                );

                let var_name = var_name.clone();
                let panic = |reason| panic!("{}: {}", title, reason);
                let meta = meta.unwrap_or_else(|err| panic!("{}: {}", title, err.to_string()));
                let meta_list = match meta {
                    Meta::List(items) => items.nested,
                    _ => panic!("{}: {}", title, "expected enum_from(a, b..)"),
                };

                // parse available attribute
                meta_list.iter().for_each(|item| match item {
                    NestedMeta::Lit(_) => panic("unexpected literal attributes"),
                    NestedMeta::Meta(meta) => match meta {
                        Meta::List(_) => panic("unexpected nested attributes"),
                        Meta::Path(path) => {
                            if path.is_ident("inner") {
                                self.from_inner_enum.push(var_name.clone());
                            } else {
                                panic("unknown path attributes, support only: [inner]");
                            }
                        }
                        Meta::NameValue(kv) => {
                            if kv.path.is_ident("str") {
                                match &kv.lit {
                                    Lit::Str(lit) => {
                                        self.from_str.insert(var_name.clone(), lit.value());
                                    }
                                    _ => panic("str attribute value must be a literal string"),
                                }
                            } else {
                                panic("unknown NameValue attributes, support only: [str]")
                            }
                        }
                    },
                })
            });
    }

    pub fn write_output(&self) -> TokenStream {
        let mut output = TokenStream::new();
        let vars_from_str = self.from_str.len();
        if vars_from_str > 0 {
            assert_eq!(
                vars_from_str,
                self.variants.len(),
                "EnumFrom for {}: from_str attribute must be used for all variants",
                self.enum_name.to_string()
            );

            output.extend(self.write_from_str());
        }

        output.extend(self.write_from_inner());
        output
    }

    fn write_from_str(&self) -> TokenStream {
        let enum_name = &self.enum_name;
        let from_str = self.from_str.iter().map(|(variant, value)| {
            quote! { #value => Ok(Self::#variant) }
        });

        let to_str = self.from_str.iter().map(|(variant, value)| {
            quote! { Self::#variant => #value }
        });

        quote! {
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
        }
    }

    fn write_from_inner(&self) -> Vec<TokenStream> {
        let enum_name = &self.enum_name;
        self.from_inner_enum
            .iter()
            .map(|var_name| {
                let inner_type = self
                    .enum_data
                    .variants
                    .iter()
                    .find(|var| var.ident.eq(var_name))
                    .map(|var| match var.fields.clone() {
                        Fields::Unnamed(field) => field.unnamed,
                        _ => panic!("inner should used on variant with unnamed field"),
                    });

                quote! {
                    impl From<#inner_type> for #enum_name {
                        fn from(inner: #inner_type) -> Self {
                            Self::#var_name(inner)
                        }
                    }
                }
            })
            .collect()
    }
}
