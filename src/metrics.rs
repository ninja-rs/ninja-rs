// Copyright 2011 Google Inc. All Rights Reserved.
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

use std::sync::{Arc, Mutex};

/// The Metrics module is used for the debug mode that dumps timing stats of
/// various actions.  To use, see METRIC_RECORD below.

/// A single metrics we're tracking, like "depfile load time".
pub struct Metric {
    name: String,
    /// Number of times we've hit the code path.
    count: usize,
    /// Total time (in micros) we've spent on the code path.
    sum: u64,
}

/// A scoped object for recording a metric across the body of a function.
/// Used by the METRIC_RECORD macro.
pub struct ScopedMetric<'a> {
    metric: Option<&'a mut Metric>,
    /// Timestamp when the measurement started.
    /// Value is platform-dependent.
    start: u64,
}

impl<'a> ScopedMetric<'a> {
    pub fn new(metric: Option<&'a mut Metric>) -> Self {
        let mut v = ScopedMetric {
            metric,
            start: 0,
        };
        if v.metric.is_some() {
           v.start = high_res_timer();
        }
        v
    }
}

impl<'a> Drop for ScopedMetric<'a> {
    fn drop(&mut self) {
        if let Some(ref mut metric) = self.metric {
            metric.count += 1;
            let dt = timer_to_micros(high_res_timer() - self.start);
            metric.sum += dt;
        }
    }
}


/// The singleton that stores metrics and prints the report.
pub struct Metrics {
    metrics: Vec<Arc<Mutex<Metric>>>,
}

impl Metrics {
    pub fn new_metric(&mut self, name: &'static str) -> Arc<Mutex<Metric>> {
        let metric = Metric {
            name: name.into(),
            count: 0,
            sum: 0,
        };

        let metric = Arc::new(Mutex::new(metric));
        self.metrics.push(metric.clone());
        metric
    }
}

/*

/// The singleton that stores metrics and prints the report.
struct Metrics {
  Metric* NewMetric(const string& name);

  /// Print a summary report to stdout.
  void Report();

private:
  vector<Metric*> metrics_;
};
*/

/// Get the current time as relative to some epoch.
/// Epoch varies between platforms; only useful for measuring elapsed time.
pub fn get_time_millis() -> u64 {
    timer_to_micros(high_res_timer()) / 1000
}


/// A simple stopwatch which returns the time
/// in seconds since Restart() was called.
pub struct Stopwatch {
    started: u64
}

impl Stopwatch {
    pub fn new() -> Self {
        Stopwatch {
          started: 0
        }
    }

    /// Seconds since Restart() call.
    pub fn elapsed(&self) -> f64 {
        1e-6 * (Self::now() - self.started) as f64
    }

    pub fn restart(&mut self) {
        self.started = Self::now()
    }

    fn now() -> u64 {
        timer_to_micros(high_res_timer())
    }

}


/// Compute a platform-specific high-res timer value that fits into an int64.
#[cfg(not(windows))]
fn high_res_timer() -> u64 {
    use std::ptr;
    use errno;

    let mut tv = libc::timeval { tv_sec: 0, tv_usec: 0 };
    if unsafe { libc::gettimeofday(&mut tv, ptr::null_mut()); } < 0 {
        fatal!("gettimeofday:{}", errno::errno());
    }
    return tv.tv_sec * 1000 * 1000 + tv.tv_usec;
}

#[cfg(windows)]
fn high_res_timer() -> u64 {
    use winapi;
    use kernel32;
    use std::mem;
    use errno;

    let mut counter = unsafe { mem::zeroed::<winapi::LARGE_INTEGER>() };
    if 0 == unsafe { kernel32::QueryPerformanceCounter(&mut counter as _)} {
        fatal!("QueryPerformanceCounter: {}", errno::errno());
    }

    counter as u64
}

/// Convert a delta of HighResTimer() values to microseconds.
#[cfg(not(windows))]
fn timer_to_micros(dt: u64) -> u64 {
    // No conversion necessary.
    dt
}

#[cfg(windows)]
fn timer_to_micros(dt: u64) -> u64 {
    use std::mem;
    use kernel32;
    use errno;
    use winapi;

    lazy_static! {
      static ref TICKS_PER_SEC : u64 = {
          let mut freq = unsafe { mem::zeroed::<winapi::LARGE_INTEGER>() };
          if 0 == unsafe { kernel32::QueryPerformanceFrequency(&mut freq as _)} {
              fatal!("QueryPerformanceFrequency: {}", errno::errno());
          };
          freq as _
      };
    };

    // dt is in ticks.  We want microseconds.
    dt * 1000000 / *TICKS_PER_SEC
}

/*

void Metrics::Report() {
  int width = 0;
  for (vector<Metric*>::iterator i = metrics_.begin();
       i != metrics_.end(); ++i) {
    width = max((int)(*i)->name.size(), width);
  }

  printf("%-*s\t%-6s\t%-9s\t%s\n", width,
         "metric", "count", "avg (us)", "total (ms)");
  for (vector<Metric*>::iterator i = metrics_.begin();
       i != metrics_.end(); ++i) {
    Metric* metric = *i;
    double total = metric->sum / (double)1000;
    double avg = metric->sum / (double)metric->count;
    printf("%-*s\t%-6d\t%-8.1f\t%.1f\n", width, metric->name.c_str(),
           metric->count, avg, total);
  }
}

*/