
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