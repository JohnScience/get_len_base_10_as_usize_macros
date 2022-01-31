use proc_macro::TokenStream;
use is_signed_trait::IsSigned;
use get_len_base_10_as_usize::MaxLenBase10AsUsize;

#[proc_macro]
pub fn impl_get_len_base_10_as_usize_via_dividing_with_pows_of_2(ts: TokenStream) -> TokenStream {
    let type_name = ts.to_string();
    let (is_signed, max_len): (bool, usize) = match type_name.as_str() {
        "u8" => (u8::IS_SIGNED, u8::MAX_LEN_BASE_10_AS_USIZE),
        "u16" => (u16::IS_SIGNED, u16::MAX_LEN_BASE_10_AS_USIZE),
        "u32" => (u32::IS_SIGNED, u32::MAX_LEN_BASE_10_AS_USIZE),
        "u64" => (u64::IS_SIGNED, u64::MAX_LEN_BASE_10_AS_USIZE),
        "u128" => (u128::IS_SIGNED, u128::MAX_LEN_BASE_10_AS_USIZE),
        "usize" => (usize::IS_SIGNED, usize::MAX_LEN_BASE_10_AS_USIZE),
        "i8" => (i8::IS_SIGNED, i8::MAX_LEN_BASE_10_AS_USIZE),
        "i16" => (i16::IS_SIGNED, i16::MAX_LEN_BASE_10_AS_USIZE),
        "i32" => (i32::IS_SIGNED, i32::MAX_LEN_BASE_10_AS_USIZE),
        "i64" => (i64::IS_SIGNED, i64::MAX_LEN_BASE_10_AS_USIZE),
        "i128" => (i128::IS_SIGNED, i128::MAX_LEN_BASE_10_AS_USIZE),
        "isize" => (isize::IS_SIGNED, isize::MAX_LEN_BASE_10_AS_USIZE),
        _ => panic!("unexpected type"),
    };
    // 0..255
    unimplemented!();
}

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        let result = 2 + 2;
        assert_eq!(result, 4);
    }
}
