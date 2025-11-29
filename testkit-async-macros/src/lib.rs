//! Procedural macros for testkit-async
//!
//! This crate provides the `#[testkit_async::test]` attribute macro for writing
//! async tests with virtual time control.
//!
//! # Example
//!
//! ```rust,ignore
//! use testkit_async::prelude::*;
//!
//! #[testkit_async::test]
//! async fn my_test(clock: MockClock) {
//!     clock.advance(Duration::from_secs(10));
//!     assert_eq!(clock.now(), Duration::from_secs(10));
//! }
//! ```

use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use syn::{
    parse::{Parse, ParseStream},
    parse_macro_input, FnArg, Ident, ItemFn, Lit, Pat, Token, Type,
};

/// Configuration options for the test macro.
#[derive(Default)]
struct TestConfig {
    /// Which async runtime to use ("tokio" or "async-std")
    runtime: Option<String>,
    /// Whether to start time paused (default: false)
    start_paused: bool,
    /// Initial time for the mock clock
    start_time_secs: Option<u64>,
    /// Flavor for tokio runtime ("current_thread" or "multi_thread")
    flavor: Option<String>,
}

impl Parse for TestConfig {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        let mut config = TestConfig::default();

        while !input.is_empty() {
            let ident: Ident = input.parse()?;
            input.parse::<Token![=]>()?;

            match ident.to_string().as_str() {
                "runtime" => {
                    let lit: Lit = input.parse()?;
                    if let Lit::Str(s) = lit {
                        config.runtime = Some(s.value());
                    }
                }
                "start_paused" => {
                    let lit: Lit = input.parse()?;
                    if let Lit::Bool(b) = lit {
                        config.start_paused = b.value();
                    }
                }
                "start_time" => {
                    let lit: Lit = input.parse()?;
                    if let Lit::Int(i) = lit {
                        config.start_time_secs = Some(i.base10_parse()?);
                    }
                }
                "flavor" => {
                    let lit: Lit = input.parse()?;
                    if let Lit::Str(s) = lit {
                        config.flavor = Some(s.value());
                    }
                }
                _ => {
                    return Err(syn::Error::new(
                        ident.span(),
                        format!("unknown attribute: {ident}"),
                    ));
                }
            }

            if input.peek(Token![,]) {
                input.parse::<Token![,]>()?;
            }
        }

        Ok(config)
    }
}

/// Determines if a function parameter is requesting a MockClock.
fn is_clock_param(arg: &FnArg) -> bool {
    if let FnArg::Typed(pat_type) = arg {
        if let Type::Path(type_path) = &*pat_type.ty {
            if let Some(segment) = type_path.path.segments.last() {
                return segment.ident == "MockClock";
            }
        }
    }
    false
}

/// Extracts the parameter name from a function argument.
fn get_param_name(arg: &FnArg) -> Option<&Pat> {
    if let FnArg::Typed(pat_type) = arg {
        Some(&pat_type.pat)
    } else {
        None
    }
}

/// Test attribute macro for async tests with virtual time control.
///
/// This macro transforms an async test function to run with a mock clock,
/// enabling deterministic time control without real delays.
///
/// # Basic Usage
///
/// ```rust,ignore
/// use testkit_async::prelude::*;
/// use std::time::Duration;
///
/// #[testkit_async::test]
/// async fn test_basic() {
///     // Test runs with tokio by default
///     assert!(true);
/// }
/// ```
///
/// # With MockClock Injection
///
/// Add a `clock: MockClock` parameter to automatically receive a mock clock:
///
/// ```rust,ignore
/// use testkit_async::prelude::*;
/// use std::time::Duration;
///
/// #[testkit_async::test]
/// async fn test_with_clock(clock: MockClock) {
///     let sleep = clock.sleep(Duration::from_secs(60));
///     clock.advance(Duration::from_secs(60));
///     sleep.await;
///     assert_eq!(clock.now(), Duration::from_secs(60));
/// }
/// ```
///
/// # Configuration Options
///
/// - `runtime = "tokio"` or `runtime = "async-std"` - Select the async runtime
/// - `start_paused = true` - Start with the clock paused
/// - `start_time = 100` - Start time in seconds (default: 0)
/// - `flavor = "multi_thread"` - Tokio runtime flavor
///
/// ```rust,ignore
/// #[testkit_async::test(runtime = "tokio", start_paused = true)]
/// async fn test_paused(clock: MockClock) {
///     assert!(clock.is_paused());
/// }
///
/// #[testkit_async::test(start_time = 1000)]
/// async fn test_start_time(clock: MockClock) {
///     assert_eq!(clock.now(), Duration::from_secs(1000));
/// }
/// ```
#[proc_macro_attribute]
pub fn test(attr: TokenStream, item: TokenStream) -> TokenStream {
    let config = parse_macro_input!(attr as TestConfig);
    let input = parse_macro_input!(item as ItemFn);

    expand_test(config, input)
        .unwrap_or_else(syn::Error::into_compile_error)
        .into()
}

fn expand_test(config: TestConfig, input: ItemFn) -> syn::Result<TokenStream2> {
    let name = &input.sig.ident;
    let body = &input.block;
    let attrs = &input.attrs;
    let vis = &input.vis;

    // Check if function is async
    if input.sig.asyncness.is_none() {
        return Err(syn::Error::new_spanned(
            &input.sig,
            "test function must be async",
        ));
    }

    // Check for clock parameter
    let needs_clock = input.sig.inputs.iter().any(is_clock_param);
    let clock_param_name = input
        .sig
        .inputs
        .iter()
        .find(|arg| is_clock_param(arg))
        .and_then(get_param_name);

    // Generate clock initialization
    let clock_init = if needs_clock {
        let start_time = config.start_time_secs.unwrap_or(0);
        let clock_name = clock_param_name.unwrap();

        if config.start_paused {
            quote! {
                let #clock_name = ::testkit_async::clock::MockClock::with_start_time(
                    ::std::time::Duration::from_secs(#start_time)
                );
                #clock_name.pause();
            }
        } else if start_time > 0 {
            quote! {
                let #clock_name = ::testkit_async::clock::MockClock::with_start_time(
                    ::std::time::Duration::from_secs(#start_time)
                );
            }
        } else {
            quote! {
                let #clock_name = ::testkit_async::clock::MockClock::new();
            }
        }
    } else {
        quote! {}
    };

    // Determine runtime and generate wrapper
    let runtime = config.runtime.as_deref().unwrap_or("tokio");
    let flavor = config.flavor.as_deref().unwrap_or("current_thread");

    let runtime_wrapper = match runtime {
        "tokio" => {
            let flavor_attr = match flavor {
                "multi_thread" => quote! { #[::tokio::test(flavor = "multi_thread")] },
                _ => quote! { #[::tokio::test] },
            };
            quote! {
                #flavor_attr
                #(#attrs)*
                #vis async fn #name() {
                    #clock_init
                    #body
                }
            }
        }
        "async-std" => {
            quote! {
                #[::async_std::test]
                #(#attrs)*
                #vis async fn #name() {
                    #clock_init
                    #body
                }
            }
        }
        _ => {
            return Err(syn::Error::new(
                proc_macro2::Span::call_site(),
                format!("unsupported runtime: {runtime}. Use \"tokio\" or \"async-std\""),
            ));
        }
    };

    Ok(runtime_wrapper)
}

#[cfg(test)]
mod tests {
    use super::TestConfig;

    #[::core::prelude::v1::test]
    fn test_config_parse_empty() {
        let config: TestConfig = syn::parse_str("").unwrap();
        assert!(config.runtime.is_none());
        assert!(!config.start_paused);
        assert!(config.start_time_secs.is_none());
    }

    #[::core::prelude::v1::test]
    fn test_config_parse_runtime() {
        let config: TestConfig = syn::parse_str("runtime = \"tokio\"").unwrap();
        assert_eq!(config.runtime, Some("tokio".to_string()));
    }

    #[::core::prelude::v1::test]
    fn test_config_parse_multiple() {
        let config: TestConfig =
            syn::parse_str("runtime = \"async-std\", start_paused = true, start_time = 100")
                .unwrap();
        assert_eq!(config.runtime, Some("async-std".to_string()));
        assert!(config.start_paused);
        assert_eq!(config.start_time_secs, Some(100));
    }
}
