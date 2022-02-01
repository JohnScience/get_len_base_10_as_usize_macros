#![cfg_attr(
    any(doc, test, doctest, feature = "const_trait_impl"),
    feature(const_trait_impl)
)]

use get_len_base_10_as_usize::MaxLenBase10AsUsize;
use is_signed_trait::IsSigned;
use proc_macro::TokenStream;
use proc_macro2::TokenTree as TokenTree2;
use quote::quote;

macro_rules! get_is_signed_and_max_len {
    ($type_name:ident in @PRIM_INTS) => {
        get_is_signed_and_max_len!($type_name in [u8,u16,u32,u64,u128,usize,i8,i16,i32,i64,i128,isize])
    };
    ($type_name:ident in [$($t:ty),+]) => {
        match $type_name.as_str() {
            $(
                stringify!($t) => (<$t>::IS_SIGNED, <$t>::MAX_LEN_BASE_10_AS_USIZE),
            )+
            _ => panic!("unexpected type"),
        }
    };
}

#[cfg(any(doc, test, doctest, feature = "const_trait_impl"))]
fn get_implementation_for_unsigned(type_token: &TokenTree2, 
    lengths: &Vec<usize>,
    smallest_numbers_with_corresponding_lengths: &Vec<usize>
) -> TokenStream {
    quote! {
        impl const GetLenBase10AsUsizeViaDivigingWithPowsOf2 for #type_token {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) -> usize {
                let mut number: Self = *self;
                let mut length = 1usize;
                #(
                    if (number >= #smallest_numbers_with_corresponding_lengths) {
                        length += #lengths;
                        number /= #smallest_numbers_with_corresponding_lengths;
                    }
                )*
                length
            }
        }
    }.into()
}

#[cfg(not(any(doc, test, doctest, feature = "const_trait_impl")))]
fn get_implementation_for_unsigned(type_token: &TokenTree2, 
    lengths: &Vec<usize>,
    smallest_numbers_with_corresponding_lengths: &Vec<usize>
) -> TokenStream {
    quote! {
        impl GetLenBase10AsUsizeViaDivigingWithPowsOf2 for #type_token {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) -> usize {
                let mut number: Self = *self;
                let mut length = 1usize;
                #(
                    if (number >= #smallest_numbers_with_corresponding_lengths) {
                        length += #lengths;
                        number /= #smallest_numbers_with_corresponding_lengths;
                    }
                )*
                length
            }
        }
    }.into()
}

#[cfg(any(doc, test, doctest, feature = "const_trait_impl"))]
fn get_implementation_for_signed(type_token: &TokenTree2, 
    lengths: &Vec<usize>,
    smallest_numbers_with_corresponding_lengths: &Vec<usize>
) -> TokenStream {
    quote! {
        impl const GetLenBase10AsUsizeViaDivigingWithPowsOf2 {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) -> usize {
            }
        }
    }.into()
}

#[cfg(not(any(doc, test, doctest, feature = "const_trait_impl")))]
fn get_implementation_for_signed(type_token: &TokenTree2, 
    lengths: &Vec<usize>,
    smallest_numbers_with_corresponding_lengths: &Vec<usize>
) -> TokenStream {
    quote! {
        impl const GetLenBase10AsUsizeViaDivigingWithPowsOf2 {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) {

            }
        }
    }.into()
}

#[proc_macro]
pub fn impl_get_len_base_10_as_usize_via_dividing_with_pows_of_2(ts: TokenStream) -> TokenStream {
    let ts = proc_macro2::TokenStream::from(ts);
    let type_name = ts.clone().to_string();
    let (is_signed, max_len): (bool, usize) = get_is_signed_and_max_len!(type_name in @PRIM_INTS);
    let type_token: TokenTree2 = ts.into_iter().next().unwrap().into();
    let max_exponent_of_2: u32 = (1u32..)
        .map(|exponent_of_2| 2usize.pow(exponent_of_2))
        // TODO: verify correctness
        .take_while(|power_of_2| *power_of_2 < max_len)
        .count() as u32;
    let (lengths, smallest_numbers_with_corresponding_lengths) = (1u32..max_exponent_of_2)
        .rev()
        .map(|exponent_of_2| 2u32.pow(exponent_of_2))
        .map(|power_of_2| (power_of_2 as usize, 10usize.pow(power_of_2)))
        .unzip::<usize, usize, Vec<_>, Vec<_>>();
    if is_signed {
        get_implementation_for_signed(&type_token, &lengths, &smallest_numbers_with_corresponding_lengths)
    }
    else {
        get_implementation_for_unsigned(&type_token, &lengths, &smallest_numbers_with_corresponding_lengths)
    }
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
