extern crate libc;
extern crate libc_stdhandle;
extern crate errno;
#[cfg(windows)]
extern crate winapi;
#[cfg(windows)]
extern crate kernel32;
#[cfg(windows)]
extern crate widestring;
#[macro_use]
extern crate clap;
#[macro_use]
extern crate lazy_static;
#[macro_use]
extern crate nom;

extern crate num_cpus;

#[cfg(windows)]
#[macro_use]
extern crate wstr;

#[macro_use]
pub mod utils;
#[cfg(test)]
pub mod test;
pub mod exit_status;
pub mod build;
pub mod graph;
pub mod build_log;
pub mod deps_log;
pub mod timestamp;
pub mod debug_flags;
pub mod version;
pub mod lexer;
pub mod eval_env;
pub mod manifest_parser;
pub mod disk_interface;
#[macro_use]
pub mod metrics;
pub mod state;
pub mod subprocess;
pub mod line_printer;
