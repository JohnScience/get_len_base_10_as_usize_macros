#![cfg_attr(
    any(doc, test, doctest, feature = "const_trait_impl"),
    feature(const_trait_impl)
)]

use is_signed_trait::IsSigned;
use max_len_base_10_as_usize::MaxLenBase10AsUsize;
use midpoint::NaiveMidpointExt;
use proc_macro::TokenStream;
use proc_macro2::{
    Ident as Ident2, Literal as Literal2, Span as Span2, TokenStream as TokenStream2,
    TokenTree as TokenTree2,
};
use quote::quote;

// Consider creating a separate crate for apply trait.
trait Apply: Sized {
    fn apply<B, F: FnMut(Self) -> B>(self, f: &mut F) -> B;
}

macro_rules! impl_apply_fn_for_t {
    () => {
        fn apply<B, F: FnMut(Self) -> B>(self, f: &mut F) -> B {
            f(self)
        }
    };
}

macro_rules! impl_trait_for_sized_t {
    ($trait_name: ident, $macro_name: ident) => {
        impl<T: Sized> $trait_name for T {
            $macro_name!();
        }
    };
}

impl_trait_for_sized_t!(Apply, impl_apply_fn_for_t);

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
    lens: &Vec<Literal2>,
    smallest_nums_with_corresponding_lens: &Vec<Literal2>,
) -> TokenStream {
    quote! {
        impl const GetLenBase10AsUsizeViaDivigingWithPowsOf2 for #type_token {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) -> usize {
                let mut number: Self = *self;
                let mut length = 1usize;
                #(
                    if (number >= (#smallest_nums_with_corresponding_lens as #type_token)) {
                        length += #lens;
                        number /= (#smallest_nums_with_corresponding_lens as #type_token);
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
    lens: &Vec<Literal2>,
    smallest_nums_with_corresponding_lens: &Vec<Literal2>,
) -> TokenStream {
    quote! {
        impl GetLenBase10AsUsizeViaDivigingWithPowsOf2 for #type_token {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) -> usize {
                let mut number: Self = *self;
                let mut length = 1usize;
                #(
                    if (number >= (#smallest_nums_with_corresponding_lens as #type_token)) {
                        length += #lens;
                        number /= (#smallest_nums_with_corresponding_lens as #type_token);
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
    lens: &Vec<Literal2>,
    smallest_nums_with_corresponding_lens: &Vec<Literal2>,
) -> TokenStream {
    quote! {
        impl const GetLenBase10AsUsizeViaDivigingWithPowsOf2 for #type_token {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) -> usize {
                let number: Self = *self;
                let mut length: usize = if number < 0 { 2 } else { 1 };
                let mut neg_abs = number.wrapping_abs().wrapping_neg();
                #(
                    if (neg_abs <= (#smallest_nums_with_corresponding_lens as #type_token).wrapping_neg()) {
                        length += #lens;
                        neg_abs /= (#smallest_nums_with_corresponding_lens as #type_token);
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
    lens: &Vec<Literal2>,
    smallest_nums_with_corresponding_lens: &Vec<Literal2>,
) -> TokenStream {
    quote! {
        impl GetLenBase10AsUsizeViaDivigingWithPowsOf2 for #type_token {
            fn get_len_base_10_as_usize_via_dividing_with_pows_of_2(&self) -> usize {
                let number: Self = *self;
                let mut length: usize = if number < 0 { 2 } else { 1 };
                let mut neg_abs = number.wrapping_abs().wrapping_neg();
                #(
                    if (neg_abs <= (#smallest_nums_with_corresponding_lens as #type_token).wrapping_neg()) {
                        length += #lens;
                        neg_abs /= (#smallest_nums_with_corresponding_lens as #type_token);
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
) -> (Vec<Literal2>, Vec<Literal2>) {
    (0u32..*max_exponent_of_2)
        .rev()
        .map(|exponent_of_2| 2u32.pow(exponent_of_2))
        .map(|power_of_2| (power_of_2, 10u128.pow(power_of_2)))
        .map(|(len, smallest_num_with_corresponding_len)| {
            (
                Literal2::u32_unsuffixed(len),
                Literal2::u128_unsuffixed(smallest_num_with_corresponding_len),
            )
        })
        .unzip::<Literal2, Literal2, Vec<_>, Vec<_>>()
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

/// The function assumes that the sum of lengths can't overflow
// "if"-token tree
unsafe fn get_unsigned_if_ts_for_len_intvl(number_ident: &Ident2, l: &u8, r: &u8) -> TokenStream2 {
    let diff = r - l;
    match diff {
        0 => TokenTree2::Literal(Literal2::u8_unsuffixed(*l)).into(),
        1 => {
            let l_val_lit = TokenTree2::Literal(Literal2::u128_unsuffixed(10u128.pow(*l as u32)));
            let (l_len_lit, r_len_lit) = (Literal2::u8_unsuffixed(*l), Literal2::u8_unsuffixed(*r));
            quote! { if #number_ident < #l_val_lit { #l_len_lit } else { #r_len_lit } }
        }
        _ => {
            debug_assert!(*l < 100 && *r < 100);
            let mp_len = l.naive_midpoint(r);
            let mp_val_lit =
                TokenTree2::Literal(Literal2::u128_unsuffixed(10u128.pow(mp_len as u32)));
            let (l_branch, r_branch) = (
                get_unsigned_if_ts_for_len_intvl(&number_ident, l, &mp_len),
                get_unsigned_if_ts_for_len_intvl(&number_ident, &(mp_len + 1), r),
            );
            quote! {
                if #number_ident < #mp_val_lit {
                    #l_branch
                } else {
                    #r_branch
                }
            }
        }
    }
}

#[cfg(any(doc, test, doctest, features = "const_trait_impl"))]
fn wrap_in_impl_block(
    trait_name: &Ident2,
    type_token: &TokenTree2,
    fn_ts: &TokenStream2,
) -> TokenStream2 {
    quote! {
        impl const #trait_name for #type_token {
            #fn_ts
        }
    }
}

#[cfg(not(any(doc, test, doctest, features = "const_trait_impl")))]
fn wrap_in_impl_block(
    trait_name: &Ident2,
    type_token: &TokenTree2,
    fn_ts: &TokenStream2,
) -> TokenStream2 {
    quote! {
        impl #trait_name for #type_token {
            #fn_ts
        }
    }
}

fn get_implementation_via_divide_and_conquer_approach_for_u_prim_ints(
    max_len_wo_sign: &u8,
    type_token: &TokenTree2,
) -> TokenStream2 {
    let trait_name = Ident2::new(
        "GetLenBase10AsUsizeViaDivideAndConquerApproach",
        Span2::call_site(),
    );
    let number_ident = Ident2::new("number", Span2::call_site());
    debug_assert!(u128::MAX_LEN_BASE_10_AS_USIZE * 2 < 100);
    let if_ts: TokenStream2 =
        unsafe { get_unsigned_if_ts_for_len_intvl(&number_ident, &1, &max_len_wo_sign) };

    let fn_ts: TokenStream2 = quote! {
        fn get_len_base_10_as_usize_via_divide_and_conquer_approach(&self) -> usize {
            let #number_ident = *self;
            #if_ts
        }
    };

    wrap_in_impl_block(&trait_name, type_token, &fn_ts)
}

unsafe fn get_signed_if_ts_for_len_intvl(neg_abs_ident: &Ident2, l: &u8, r: &u8) -> TokenStream2 {
    let diff = r - l;
    match diff {
        0 => TokenTree2::Literal(Literal2::u8_unsuffixed(*l)).into(),
        1 => {
            let l_val_lit = TokenTree2::Literal(Literal2::i128_unsuffixed(-10i128.pow(*l as u32)));
            let (l_len_lit, r_len_lit) = (Literal2::u8_unsuffixed(*l), Literal2::u8_unsuffixed(*r));
            quote! { if #neg_abs_ident > #l_val_lit { #l_len_lit } else { #r_len_lit } }
        }
        _ => {
            debug_assert!(*l < 100 && *r < 100);
            let mp_len = l.naive_midpoint(r);
            let mp_val_lit =
                TokenTree2::Literal(Literal2::i128_unsuffixed(-10i128.pow(mp_len as u32)));
            let (l_branch, r_branch) = (
                get_signed_if_ts_for_len_intvl(&neg_abs_ident, l, &mp_len),
                get_signed_if_ts_for_len_intvl(&neg_abs_ident, &(mp_len + 1), r),
            );
            quote! {
                if #neg_abs_ident > #mp_val_lit {
                    #l_branch
                } else {
                    #r_branch
                }
            }
        }
    }
}

fn get_implementation_via_divide_and_conquer_approach_for_s_prim_ints(
    max_len_wo_sign: &u8,
    type_token: &TokenTree2,
) -> TokenStream2 {
    let trait_name = Ident2::new(
        "GetLenBase10AsUsizeViaDivideAndConquerApproach",
        Span2::call_site(),
    );
    let neg_abs_ident = Ident2::new("neg_abs", Span2::call_site());
    debug_assert!(i128::MAX_LEN_BASE_10_AS_USIZE * 2 < 100);
    let if_ts = unsafe { get_signed_if_ts_for_len_intvl(&neg_abs_ident, &1, &max_len_wo_sign) };
    let fn_ts: TokenStream2 = quote! {
        fn get_len_base_10_as_usize_via_divide_and_conquer_approach(&self) -> usize {
            let maybe_minus_length = if *self < 0 { 1 } else { 0 };
            let #neg_abs_ident = self.wrapping_abs().wrapping_neg();
            maybe_minus_length + #if_ts
        }
    };
    wrap_in_impl_block(&trait_name, type_token, &fn_ts)
}

#[proc_macro]
pub fn impl_get_len_base_10_as_usize_via_divide_and_conquer_approach(
    ts: TokenStream,
) -> TokenStream {
    let ts = proc_macro2::TokenStream::from(ts);
    let type_name = ts.clone().to_string();
    let (is_signed, max_len_wo_sign) = get_is_signed_and_max_len_wo_sign!(type_name in @PRIM_INTS)
        .apply(&mut |(is_signed, max_len_wo_sign): (bool, usize)| {
            (
                is_signed,
                // Length of all primitive integers will fit into u8
                max_len_wo_sign as u8,
            )
        });
    let type_token: TokenTree2 = ts.into_iter().next().unwrap().into();
    if is_signed {
        get_implementation_via_divide_and_conquer_approach_for_s_prim_ints(
            &max_len_wo_sign,
            &type_token,
        )
        .into()
    } else {
        get_implementation_via_divide_and_conquer_approach_for_u_prim_ints(
            &max_len_wo_sign,
            &type_token,
        )
        .into()
    }
}
