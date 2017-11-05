// Copyright 2013 Google Inc. All Rights Reserved.
// Copyright 2017 Ninja-rs Authors. All Rights Reserved.
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

pub const NINJA_VERSION: &'static str = crate_version!{};

pub fn parse_version(version: &str) -> (u8, u8) {
    let mut split = version.split('.');
    let (major, minor) = (split.next(), split.next());
    let major = major.and_then(|s| s.parse::<u8>().ok()).unwrap_or(0);
    let minor = minor.and_then(|s| s.parse::<u8>().ok()).unwrap_or(0);

    (major, minor)
}

pub fn check_ninja_version(version: &str) {
    let (bin_major, bin_minor) = parse_version(NINJA_VERSION);
    let (file_major, file_minor) = parse_version(version);
    if bin_major > file_major {
        warning!(concat!("ninja executable version ({}) greater than build file ",
                "ninja_required_version ({}); versions may be incompatible."),
                NINJA_VERSION, version);
        return;
    }

    if (bin_major == file_major && bin_minor < file_minor) ||
        bin_major < file_major {
        fatal!(concat!("ninja version ({}) incompatible with build file ",
            "ninja_required_version version ({})."),
            NINJA_VERSION, version);
    }
}

#[test]
fn test_parse_version() {
    assert_eq!(parse_version(""), (0, 0));
    assert_eq!(parse_version("1"), (1, 0));
    assert_eq!(parse_version("1.2"), (1, 2));
    assert_eq!(parse_version("1.2.3"), (1, 2));
    assert_eq!(parse_version("1.2.3.git"), (1, 2));
    assert_eq!(parse_version("1.2.3-git"), (1, 2));
}