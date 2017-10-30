use std::sync::Mutex;
use super::metrics::Metrics;

pub static EXPLAINING: bool = false;

pub static KEEP_DEPFILE: bool = false;

pub static KEEP_RSP: bool = false;

pub static EXPERIMENTAL_STATCACHE: bool = true;

pub static METRICS: Option<Mutex<Metrics>> = None;

// explain!{} moved to utils.rs
