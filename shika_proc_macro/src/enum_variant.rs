use proc_macro2::TokenTree;
use syn::DataEnum;

pub fn variant_attr_args(data: DataEnum, attr_name: &str, arg_name: &str) -> Vec<(String, String)> {
    data.variants
        .iter()
        .map(|var| {
            let variant_name = var.ident.to_string();
            let token_tree = var
                .attrs
                .iter()
                .find(|attr| &attr.path.segments.first().unwrap().ident == attr_name)
                .expect(format!("attribute {} not in variant {}", attr_name, variant_name).as_str())
                .tokens
                .clone()
                .into_iter()
                .next()
                .expect(
                    format!(
                        "arguments {} not found in {}.{}",
                        arg_name, variant_name, attr_name
                    )
                    .as_str(),
                );

            let mut stream = match token_tree {
                TokenTree::Group(group) => group.stream(),
                _ => panic!("arguments {} is not token tree group", arg_name),
            }
            .into_iter()
            .skip_while(|token| match token {
                TokenTree::Ident(id) => id.to_string().as_str() == arg_name,
                _ => false,
            });

            assert!(
                matches!(stream.next(), Some(TokenTree::Punct(_))),
                "must be a TokenTree::Punct after TokenTree::Ident"
            );

            let arg_value = match stream.next() {
                Some(TokenTree::Literal(val)) => val.to_string(),
                _ => panic!("must be a TokenTree::Literal after TokenTree::Punct"),
            };

            (variant_name, arg_value)
        })
        .collect()
}
