extern crate libc;
extern crate errno;
#[cfg(windows)]
extern crate winapi;
#[cfg(windows)]
extern crate kernel32;
#[macro_use]
extern crate clap;
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate nom;

extern crate num_cpus;

#[macro_use]
mod utils;
#[cfg(test)]
mod test;
mod build;
mod graph;
mod build_log;
mod deps_log;
mod timestamp;
mod debug_flags;
mod version;
mod lexer;
mod eval_env;
mod manifest_parser;
mod disk_interface;
#[macro_use]
mod metrics;
mod state;
mod ninja;

use libc::{c_char, c_int};
use std::ffi::CString;

extern "C" {
    fn exported_main(argc: c_int, argv: *const *const c_char) -> c_int;
}

fn main() {
    if false {
        let argv: Vec<CString> = std::env::args()
            .map(|arg| CString::new(arg).unwrap())
            .collect();
        let args: Vec<*const c_char> = argv.iter().map(|arg| arg.as_ptr()).collect();
        let r = unsafe { exported_main(args.len() as c_int, args.as_ptr() as *const *const c_char) };
        std::process::exit(r);
    } else {
        let errcode = ninja::ninja_entry().err().unwrap_or(0);
        std::process::exit(errcode as _);
    }
}
