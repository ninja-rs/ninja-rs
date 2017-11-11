// Copyright 2011 Google Inc. All Rights Reserved.
// Copyright 2017 The Ninja-rs Project Developers. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

extern crate libc;
extern crate libc_stdhandle;
#[cfg(unix)]
extern crate libc_spawn;
extern crate errno;
#[macro_use]
extern crate cfg_if;
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
