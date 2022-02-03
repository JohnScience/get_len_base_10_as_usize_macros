#![cfg_attr(
    any(doc, test, doctest, feature = "const_trait_impl"),
    feature(const_trait_impl)
)]

use is_signed_trait::IsSigned;
use max_len_base_10_as_usize::MaxLenBase10AsUsize;
use proc_macro::TokenStream;
use proc_macro2::TokenTree as TokenTree2;
use quote::quote;

macro_rules! get_is_signed_and_max_len_wo_sign {
    ($type_name:ident in @PRIM_INTS) => {
        get_is_signed_and_max_len_wo_sign!($type_name in [u8,u16,u32,u64,u128,usize,i8,i16,i32,i64,i128,isize])
    };
    ($type_name:ident in [$($t:ty),+]) => {
        match $type_name.as_str() {
            $(
                stringify!($t) => (
                    <$t>::IS_SIGNED,
                    if <$t>::IS_SIGNED {
                        <$t>::MAX_LEN_BASE_10_AS_USIZE - 1
                    } else {
                        <$t>::MAX_LEN_BASE_10_AS_USIZE
                    }
                ),
            )+
            _ => panic!("unexpected type"),
        }
    };
}

#[cfg(any(doc, test, doctest, feature = "const_trait_impl"))]
fn get_implementation_via_pows_of_2_for_unsigned(
    type_token: &TokenTree2,
    lengths: &Vec<usize>,
    smallest_numbers_with_corresponding_lengths: &Vec<u128>,
) -> TokenStream {
    quote! {
        impl const GetLenBase10AsUsizeViaDivigingWithPowsOf2 for #type_token {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) -> usize {
                let mut number: Self = *self;
                let mut length = 1usize;
                #(
                    if (number >= (#smallest_numbers_with_corresponding_lengths as #type_token)) {
                        length += #lengths;
                        number /= (#smallest_numbers_with_corresponding_lengths as #type_token);
                    }
                )*
                length
            }
        }
    }
    .into()
}

#[cfg(not(any(doc, test, doctest, feature = "const_trait_impl")))]
fn get_implementation_via_pows_of_2_for_unsigned(
    type_token: &TokenTree2,
    lengths: &Vec<usize>,
    smallest_numbers_with_corresponding_lengths: &Vec<u128>,
) -> TokenStream {
    quote! {
        impl GetLenBase10AsUsizeViaDivigingWithPowsOf2 for #type_token {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) -> usize {
                let mut number: Self = *self;
                let mut length = 1usize;
                #(
                    if (number >= (#smallest_numbers_with_corresponding_lengths as #type_token)) {
                        length += #lengths;
                        number /= (#smallest_numbers_with_corresponding_lengths as #type_token);
                    }
                )*
                length
            }
        }
    }
    .into()
}

#[cfg(any(doc, test, doctest, feature = "const_trait_impl"))]
fn get_implementation_via_pows_of_2_for_signed(
    type_token: &TokenTree2,
    lengths: &Vec<usize>,
    smallest_numbers_with_corresponding_lengths: &Vec<u128>,
) -> TokenStream {
    quote! {
        impl const GetLenBase10AsUsizeViaDivigingWithPowsOf2 for #type_token {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) -> usize {
                let number: Self = *self;
                let mut length: usize = if number < 0 { 2 } else { 1 };
                let mut neg_abs = number.wrapping_abs().wrapping_neg();
                #(
                    if (neg_abs <= (#smallest_numbers_with_corresponding_lengths as #type_token).wrapping_neg()) {
                        length += #lengths;
                        neg_abs /= (#smallest_numbers_with_corresponding_lengths as #type_token);
                    }
                )*
                length
            }
        }
    }.into()
}

#[cfg(not(any(doc, test, doctest, feature = "const_trait_impl")))]
fn get_implementation_via_pows_of_2_for_signed(
    type_token: &TokenTree2,
    lengths: &Vec<usize>,
    smallest_numbers_with_corresponding_lengths: &Vec<u128>,
) -> TokenStream {
    quote! {
        impl GetLenBase10AsUsizeViaDivigingWithPowsOf2 for #type_token {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) -> usize {
                let number: Self = *self;
                let mut length: usize = if number < 0 { 2 } else { 1 };
                let mut neg_abs = number.wrapping_abs().wrapping_neg();
                #(
                    if (neg_abs <= (#smallest_numbers_with_corresponding_lengths as #type_token).wrapping_neg()) {
                        length += #lengths;
                        neg_abs /= (#smallest_numbers_with_corresponding_lengths as #type_token);
                    }
                )*
                length
            }
        }
    }.into()
}

fn get_max_exponent_of_2_leq_max_len_wo_sign(max_len_wo_sign: &usize) -> u32 {
    (0u32..)
        .map(|exponent_of_2| 2usize.pow(exponent_of_2))
        .take_while(|power_of_2| power_of_2 <= max_len_wo_sign)
        .count() as u32
}

fn make_lens_and_smallest_nums_with_corresponding_lens_pair(
    max_exponent_of_2: &u32,
) -> (Vec<usize>, Vec<u128>) {
    (0u32..*max_exponent_of_2)
        .rev()
        .map(|exponent_of_2| 2u32.pow(exponent_of_2))
        .map(|power_of_2| (power_of_2 as usize, 10u128.pow(power_of_2)))
        .unzip::<usize, u128, Vec<_>, Vec<_>>()
}

// Bulk approach would make the macro considerably more efficient, yet it would make
// implementing the trait for non-primitive types harder
#[proc_macro]
pub fn impl_get_len_base_10_as_usize_via_dividing_with_pows_of_2(ts: TokenStream) -> TokenStream {
    let ts = proc_macro2::TokenStream::from(ts);
    let type_name = ts.clone().to_string();
    let (is_signed, max_len_wo_sign): (bool, usize) =
        get_is_signed_and_max_len_wo_sign!(type_name in @PRIM_INTS);
    let type_token: TokenTree2 = ts.into_iter().next().unwrap().into();
    let max_exponent_of_2: u32 = get_max_exponent_of_2_leq_max_len_wo_sign(&max_len_wo_sign);
    let (lens, smallest_nums_with_corresponding_lens) =
        make_lens_and_smallest_nums_with_corresponding_lens_pair(&max_exponent_of_2);
    if is_signed {
        get_implementation_via_pows_of_2_for_signed(
            &type_token,
            &lens,
            &smallest_nums_with_corresponding_lens,
        )
    } else {
        get_implementation_via_pows_of_2_for_unsigned(
            &type_token,
            &lens,
            &smallest_nums_with_corresponding_lens,
        )
    }
}
