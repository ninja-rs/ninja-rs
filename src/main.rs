extern crate libc;

use libc::{c_char, c_int};
use std::ffi::CString;

extern "C" {
    fn exported_main(argc: c_int, argv: *const *const c_char) -> c_int;
}

fn main() {
    let argv: Vec<CString> = std::env::args()
        .map(|arg| CString::new(arg).unwrap())
        .collect();
    let args: Vec<*const c_char> = argv.iter().map(|arg| arg.as_ptr()).collect();
    let r = unsafe { exported_main(args.len() as c_int, args.as_ptr() as *const *const c_char) };
    std::process::exit(r);
}
