extern crate proc_macro;
#[macro_use]
extern crate quote;

use syn::{parse_macro_input, DeriveInput, FieldsNamed, FieldsUnnamed};

use proc_macro::TokenStream;

#[proc_macro_derive(Streamable)]
pub fn chia_streamable_macro(input: TokenStream) -> TokenStream {
    let DeriveInput { ident, data, .. } = parse_macro_input!(input);

    let mut fnames = Vec::<syn::Ident>::new();
    let mut findices = Vec::<syn::Index>::new();
    let mut ftypes = Vec::<syn::Type>::new();
    match data {
        syn::Data::Enum(_) => {
            panic!("Streamable does not support Enums");
        }
        syn::Data::Union(_) => {
            panic!("Streamable does not support Unions");
        }
        syn::Data::Struct(s) => match s.fields {
            syn::Fields::Unnamed(FieldsUnnamed { unnamed, .. }) => {
                for (index, f) in unnamed.iter().enumerate() {
                    findices.push(syn::Index::from(index));
                    ftypes.push(f.ty.clone());
                }
            }
            syn::Fields::Unit => {
                panic!("Streamable does not support the unit type");
            }
            syn::Fields::Named(FieldsNamed { named, .. }) => {
                for f in named.iter() {
                    fnames.push(f.ident.as_ref().unwrap().clone());
                    ftypes.push(f.ty.clone());
                }
            }
        },
    };

    if !fnames.is_empty() {
        let ret = quote! {
            impl Streamable for #ident {
                fn update_digest(&self, digest: &mut clvmr::sha2::Sha256) {
                    #(self.#fnames.update_digest(digest);)*
                }
                fn stream(&self, out: &mut Vec<u8>) -> chia_error::Result<()> {
                    #(self.#fnames.stream(out)?;)*
                    Ok(())
                }
                fn parse(input: &mut std::io::Cursor<&[u8]>) -> chia_error::Result<Self> {
                    Ok(#ident{ #( #fnames: <#ftypes as Streamable>::parse(input)?, )* })
                }
            }
        };
        ret.into()
    } else if !findices.is_empty() {
        let ret = quote! {
            impl Streamable for #ident {
                fn update_digest(&self, digest: &mut clvmr::sha2::Sha256) {
                    #(self.#findices.update_digest(digest);)*
                }
                fn stream(&self, out: &mut Vec<u8>) -> chia_error::Result<()> {
                    #(self.#findices.stream(out)?;)*
                    Ok(())
                }
                fn parse(input: &mut std::io::Cursor<&[u8]>) -> chia_error::Result<Self> {
                    Ok(#ident( #( <#ftypes as Streamable>::parse(input)?, )* ))
                }
            }
        };
        ret.into()
    } else {
        panic!("unknown error");
    }
}
