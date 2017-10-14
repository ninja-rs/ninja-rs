

pub enum BuildConfigVerbosity {
    NORMAL,
    QUIET,  // No output -- used when testing.
    VERBOSE,
}

pub struct BuildConfig {
    pub verbosity: BuildConfigVerbosity,
    pub dry_run: bool,
    pub parallelism: isize,
    pub failures_allowed: isize,
    pub max_load_average: f64,
}

impl BuildConfig {
    pub fn new() -> Self {
        BuildConfig {
            verbosity: BuildConfigVerbosity::NORMAL,
            dry_run: false,
            parallelism: 1,
            failures_allowed: 1,
            max_load_average: -0.0f64,
        }
    }
}