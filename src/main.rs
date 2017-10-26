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
mod exit_status;
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

fn main() {
    let errcode = ninja::ninja_entry().err().unwrap_or(0);
    std::process::exit(errcode as _);
}
