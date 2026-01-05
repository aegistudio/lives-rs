use proc_macro::TokenStream;
use quote::quote;
use syn::{DeriveInput, GenericParam, parse_macro_input, spanned::Spanned};

fn derive_life_inner(input: DeriveInput) -> anyhow::Result<TokenStream> {
    // XXX: we don't support where clauses for now. Maybe we can open
    // the door in the future.
    if let Some(where_clause) = input.generics.where_clause {
        if !where_clause.predicates.is_empty() {
            return Err(anyhow::anyhow!("Too complex, please do it yourself."));
        }
    }

    // We erase all lifetime parameters into our provided one.
    // impl<#impl_generics> Life for $ident<#impl_params> {
    //     type Timed<'b> = #timed_params;
    // }
    let mut impl_generics: Vec<proc_macro2::TokenStream> = Vec::new();
    let mut impl_params: Vec<proc_macro2::TokenStream> = Vec::new();
    let mut timed_params: Vec<proc_macro2::TokenStream> = Vec::new();
    for param in input.generics.params {
        match param.clone() {
            GenericParam::Const(c) => {
                let ident = &c.ident;
                impl_generics.push(quote! { #param }.into());
                impl_params.push(quote! { #ident }.into());
                timed_params.push(quote! { #ident }.into());
            }
            GenericParam::Type(t) => {
                let ident = &t.ident;
                impl_generics.push(quote! { #param }.into());
                impl_params.push(quote! { #ident }.into());
                timed_params.push(quote! { #ident }.into());
            }
            GenericParam::Lifetime(_) => {
                impl_generics.push(quote! { 'a }.into());
                impl_params.push(quote! { 'a }.into());
                timed_params.push(quote! { 'b }.into());
            }
        }
    }

    let ident = &input.ident;
    let generics_clause = if impl_generics.len() > 0 {
        quote! { <#(#impl_generics),*> }
    } else {
        quote! {}
    };
    let impl_type_clause = if impl_params.len() > 0 {
        quote! { <#(#impl_params),*> }
    } else {
        quote! {}
    };
    let timed_param_clause = if timed_params.len() > 0 {
        quote! { <#(#timed_params),*> }
    } else {
        quote! {}
    };

    let result = quote! {
        impl #generics_clause Life for #ident #impl_type_clause {
            type Timed<'b> = #ident #timed_param_clause;

            fn covariance<'c, 'b: 'c>(a: Self::Timed<'b>) -> Self::Timed<'c> {
                a
            }
        }
    };
    Ok(result.into())
}

#[proc_macro_derive(Life)]
pub fn derive_life(input: TokenStream) -> TokenStream {
    let input = parse_macro_input!(input as DeriveInput);
    let span = input.span();
    match derive_life_inner(input) {
        Ok(result) => result,
        Err(err) => {
            let err = syn::Error::new(span, err);
            err.into_compile_error().into()
        }
    }
}
