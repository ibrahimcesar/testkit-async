//! Procedural macros for testkit-async

use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

/// Test attribute macro for async tests
///
/// ```rust,ignore
/// #[testkit_async::test]
/// async fn my_test() {
///     // test code
/// }
/// ```
#[proc_macro_attribute]
pub fn test(_attr: TokenStream, item: TokenStream) -> TokenStream {
    let input = parse_macro_input!(item as ItemFn);
    let name = &input.sig.ident;
    let body = &input.block;
    let attrs = &input.attrs;

    // Generate test function
    let expanded = quote! {
        #[::core::prelude::v1::test]
        #(#attrs)*
        fn #name() {
            // TODO: Initialize test runtime
            // For now, just use tokio
            let rt = tokio::runtime::Runtime::new().unwrap();
            rt.block_on(async #body)
        }
    };

    TokenStream::from(expanded)
}
