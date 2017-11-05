// Copyright 2011 Google Inc. All Rights Reserved.
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

use std;
use libc;
use libc_stdhandle;
use errno;
use num_cpus;
use std::path::PathBuf;

/// The primary interface to metrics.  Use METRIC_RECORD("foobar") at the top
/// of a function to get timing stats recorded for each call of the function.
macro_rules! metric_record {
    ($metric: expr) => {
        metric_record!($metric, METRIC_VAR, metric_borrow);
    };
    ($metric: expr, $metric_var: ident, $metric_borrow: ident) => {
    lazy_static! {
        static ref $metric_var :
            Option<::std::sync::Arc<::std::sync::Mutex<$crate::metrics::Metric>>> =
                $crate::debug_flags::METRICS.as_ref()
                    .map(|m| m.lock().unwrap().new_metric($metric));
        }
        let mut $metric_borrow = $metric_var.as_ref().map(|r| r.lock().unwrap());
        let _ = $crate::metrics::ScopedMetric::new($metric_borrow.as_mut().map(|r| &mut **r));
    };
}

#[macro_export]
macro_rules! explain {
    ($fmt:expr) =>
        (if $crate::debug_flags::EXPLAINING {
            eprint!(concat!("ninja explain: ", $fmt, "\n"))
        });
    ($fmt:expr, $($arg:tt)*) =>
        (if $crate::debug_flags::EXPLAINING {
            eprint!(concat!("ninja explain: ", $fmt, "\n"), $($arg)*)
        });
}

/// Log a fatal message and exit.
#[macro_export]
macro_rules! fatal {
    ($fmt:expr) =>
        ({
            eprint!(concat!("ninja fatal: ", $fmt, "\n"));
            $crate::utils::exit();
        });
    ($fmt:expr, $($arg:tt)*) =>
        ({
            eprint!(concat!("ninja fatal: ", $fmt, "\n"), $($arg)*);
            $crate::utils::exit();
        });
}

/// Log a warning message.
#[macro_export]
macro_rules! warning {
    ($fmt:expr) =>
        (eprint!(concat!("ninja warning: ", $fmt, "\n")));
    ($fmt:expr, $($arg:tt)*) =>
        (eprint!(concat!("ninja warning: ", $fmt, "\n"), $($arg)*));
}

/// Log an error message.
#[macro_export]
macro_rules! error {
    ($fmt:expr) =>
        (eprint!(concat!("ninja error: ", $fmt, "\n")));
    ($fmt:expr, $($arg:tt)*) =>
        (eprint!(concat!("ninja error: ", $fmt, "\n"), $($arg)*));
}

#[cfg(windows)]
pub fn exit() -> ! {
    use kernel32;
    use std::io::Write;

    // On Windows, some tools may inject extra threads.
    // exit() may block on locks held by those threads, so forcibly exit.
    let _ = std::io::stderr().flush();
    let _ = std::io::stdout().flush();
    unsafe {
        kernel32::ExitProcess(1);
    }
    unreachable!()
}

#[cfg(not(windows))]
pub fn exit() -> ! {
    unsafe {
        libc::exit(1);
    }
    unreachable!()
}

pub trait ZeroOrErrnoResult {
    fn as_zero_errno_result(self) -> Result<(), errno::Errno>;
}

impl ZeroOrErrnoResult for libc::c_int {
    fn as_zero_errno_result(self) -> Result<(), errno::Errno> {
        if self == 0 {
            Ok(())
        } else {
            Err(errno::errno())
        }
    }
}


pub fn set_stdout_linebuffered() {
    unsafe {
        libc::setvbuf(
            libc_stdhandle::stdout(),
            std::ptr::null_mut(),
            libc::_IOLBF,
            libc::BUFSIZ as _,
        );
    }
}

pub fn get_processor_count() -> usize {
    num_cpus::get()
}

#[cfg(unix)]
fn pathbuf_from_bytes_os(bytes: Vec<u8>) -> Result<PathBuf, Vec<u8>> {
    Ok(PathBuf::from(OsString::from_vec(bytes)))
}

#[cfg(not(unix))]
fn pathbuf_from_bytes_os(bytes: Vec<u8>) -> Result<PathBuf, Vec<u8>> {
    Err(bytes)
}

pub fn pathbuf_from_bytes(mut bytes: Vec<u8>) -> Result<PathBuf, Vec<u8>> {
    bytes = match String::from_utf8(bytes) {
        Ok(r) => {
            return Ok(PathBuf::from(r));
        }
        Err(e) => e.into_bytes(),
    };
    return pathbuf_from_bytes_os(bytes);
}

pub trait RangeContains<T> {
    fn contains_stable(&self, item: T) -> bool;
}

impl<Idx: PartialOrd<Idx>> RangeContains<Idx> for std::ops::Range<Idx> {
    fn contains_stable(&self, item: Idx) -> bool {
        (self.start <= item) && (item < self.end)
    }
}
/*

/// Canonicalize a path like "foo/../bar.h" into just "bar.h".
/// |slash_bits| has bits set starting from lowest for a backslash that was
/// normalized to a forward slash. (only used on Windows)
bool CanonicalizePath(string* path, uint64_t* slash_bits, string* err);
bool CanonicalizePath(char* path, size_t* len, uint64_t* slash_bits,
                      string* err);

/// Appends |input| to |*result|, escaping according to the whims of either
/// Bash, or Win32's CommandLineToArgvW().
/// Appends the string directly to |result| without modification if we can
/// determine that it contains no problematic characters.
void GetShellEscapedString(const string& input, string* result);
void GetWin32EscapedString(const string& input, string* result);

/// Read a file to a string (in text mode: with CRLF conversion
/// on Windows).
/// Returns -errno and fills in \a err on error.
int ReadFile(const string& path, string* contents, string* err);

/// Mark a file descriptor to not be inherited on exec()s.
void SetCloseOnExec(int fd);

/// Given a misspelled string and a list of correct spellings, returns
/// the closest match or NULL if there is no close enough match.
const char* SpellcheckStringV(const string& text,
                              const vector<const char*>& words);

/// Like SpellcheckStringV, but takes a NULL-terminated list.
const char* SpellcheckString(const char* text, ...);

bool islatinalpha(int c);

/// Removes all Ansi escape codes (http://www.termsys.demon.co.uk/vtansi.htm).
string StripAnsiEscapeCodes(const string& in);

/// @return the number of processors on the machine.  Useful for an initial
/// guess for how many jobs to run in parallel.  @return 0 on error.
int GetProcessorCount();

/// @return the load average of the machine. A negative value is returned
/// on error.
double GetLoadAverage();

/// Elide the given string @a str with '...' in the middle if the length
/// exceeds @a width.
string ElideMiddle(const string& str, size_t width);

/// Truncates a file to the given size.
bool Truncate(const string& path, size_t size, string* err);

#ifdef _MSC_VER
#define snprintf _snprintf
#define fileno _fileno
#define unlink _unlink
#define chdir _chdir
#define strtoull _strtoui64
#define getcwd _getcwd
#define PATH_MAX _MAX_PATH
#endif

#ifdef _WIN32
/// Convert the value returned by GetLastError() into a string.
string GetLastErrorString();

/// Calls Fatal() with a function name and GetLastErrorString.
NORETURN void Win32Fatal(const char* function);
#endif


#include "util.h"

#ifdef __CYGWIN__
#include <windows.h>
#include <io.h>
#elif defined( _WIN32)
#include <windows.h>
#include <io.h>
#include <share.h>
#endif

#include <assert.h>
#include <errno.h>
#include <fcntl.h>c
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>

#ifndef _WIN32
#include <unistd.h>
#include <sys/time.h>
#endif

#include <vector>

#if defined(__APPLE__) || defined(__FreeBSD__)
#include <sys/sysctl.h>
#elif defined(__SVR4) && defined(__sun)
#include <unistd.h>
#include <sys/loadavg.h>
#elif defined(_AIX)
#include <libperfstat.h>
#elif defined(linux) || defined(__GLIBC__)
#include <sys/sysinfo.h>
#endif

#include "edit_distance.h"
#include "metrics.h"
*/

/*
static bool IsPathSeparator(char c) {
#ifdef _WIN32
  return c == '/' || c == '\\';
#else
  return c == '/';
#endif
}
*/

#[cfg(windows)]
pub const WINDOWS_PATH: bool = true;
#[cfg(not(windows))]
pub const WINDOWS_PATH: bool = false;

fn is_path_separator(c: u8) -> bool {
    c == b'/' || WINDOWS_PATH && c == b'\\'
}


pub fn canonicalize_path(path: &mut Vec<u8>) -> Result<u64, String> {
    metric_record!("canonicalize str");
    let (newsize, slash_bits) = canonicalize_path_slice(path.as_mut_slice())?;
    path.truncate(newsize);
    Ok(slash_bits)
}

pub fn canonicalize_path_slice(path: &mut [u8]) -> Result<(usize, u64), String> {
    // WARNING: this function is performance-critical; please benchmark
    // any changes you make to it.
    metric_record!("canonicalize path");
    if path.is_empty() {
        return Err("empty path".to_owned());
    }

    const MAX_PATH_COMPONENTS: usize = 60usize;
    let mut components = [0usize; MAX_PATH_COMPONENTS];
    let mut component_count = 0usize;

    let len = path.len();

    let start = 0;
    let end = len;
    let mut dst = 0;
    let mut src = 0;

    if is_path_separator(path[0]) {
        if WINDOWS_PATH && len >= 2 && is_path_separator(path[1]) {
            src += 1;
            dst += 1;
        }
        src += 1;
        dst += 1;
    }

    while src < end {
        if path[src] == b'.' && (src + 1 == end || is_path_separator(path[src + 1])) {
            // '.' component; eliminate.
            src += 2;
        } else if path[src] == b'.' && path[src + 1] == b'.' &&
                   (src + 2 == end || is_path_separator(path[src + 2]))
        {
            if component_count == 0 {
                path[dst] = path[src];
                path[dst + 1] = path[src + 1];
                path[dst + 2] = path[src + 2];
                dst += 3;
            } else {
                dst = components[component_count - 1];
                component_count -= 1;
            }
            src += 3;
        } else if is_path_separator(path[src]) {
            src += 1;
        } else {
            if component_count == MAX_PATH_COMPONENTS {
                fatal!(
                    "path has too many components : {}",
                    String::from_utf8_lossy(path)
                );
            }

            components[component_count] = dst;
            component_count += 1;

            while {
                path[dst] = path[src];
                dst += 1;
                src += 1;
                src < end && !is_path_separator(path[dst - 1])
            }
            {}
        }
    }

    if dst == start {
        path[dst] = b'.';
        dst += 1;
    }

    let new_len = dst - start;
    let mut slash_bits = 0u64;
    if WINDOWS_PATH {
        let mut mask = 1u64;
        for i in 0..new_len {
            if path[i] == b'\\' {
                slash_bits |= mask;
                path[i] = b'/';
                mask <<= 1;
            } else if path[i] == b'/' {
                mask <<= 1;
            }
        }
    }
    Ok((new_len, slash_bits))
}


// static
pub fn decanonicalize_path(path: &[u8], slash_bits: u64) -> Vec<u8> {
    let mut result = path.to_owned();
    if WINDOWS_PATH {
        let mut mask = 1u64;
        for c in result.iter_mut().filter(|c| **c == b'/') {
            if (slash_bits & mask) != 0 {
                *c = b'\\';
            }
            mask <<= 1;
        }
    }
    result
}

pub trait ExtendFromEscapedSlice<T> {
    fn extend_from_shell_escaped_slice(&mut self, other: &[T]);
    fn extend_from_win32_escaped_slice(&mut self, other: &[T]);
}

/*
static inline bool IsKnownShellSafeCharacter(char ch) {
  if ('A' <= ch && ch <= 'Z') return true;
  if ('a' <= ch && ch <= 'z') return true;
  if ('0' <= ch && ch <= '9') return true;

  switch (ch) {
    case '_':
    case '+':
    case '-':
    case '.':
    case '/':
      return true;
    default:
      return false;
  }
}
*/

fn is_known_win32_safe_char(ch: u8) -> bool {
    match ch {
        b' ' | b'"' => false,
        _ => true,
    }
}

/*
static inline bool StringNeedsShellEscaping(const string& input) {
  for (size_t i = 0; i < input.size(); ++i) {
    if (!IsKnownShellSafeCharacter(input[i])) return true;
  }
  return false;
}
*/
fn slice_needs_win32_escaping(input: &[u8]) -> bool {
    !input.iter().cloned().all(is_known_win32_safe_char)
}

/*
void GetShellEscapedString(const string& input, string* result) {
  assert(result);

  if (!StringNeedsShellEscaping(input)) {
    result->append(input);
    return;
  }

  const char kQuote = '\'';
  const char kEscapeSequence[] = "'\\'";

  result->push_back(kQuote);

  string::const_iterator span_begin = input.begin();
  for (string::const_iterator it = input.begin(), end = input.end(); it != end;
       ++it) {
    if (*it == kQuote) {
      result->append(span_begin, it);
      result->append(kEscapeSequence);
      span_begin = it;
    }
  }
  result->append(span_begin, input.end());
  result->push_back(kQuote);
}


void GetWin32EscapedString(const string& input, string* result) {
  assert(result);
  if (!StringNeedsWin32Escaping(input)) {
    result->append(input);
    return;
  }

  const char kQuote = '"';
  const char kBackslash = '\\';

  result->push_back(kQuote);
  size_t consecutive_backslash_count = 0;
  string::const_iterator span_begin = input.begin();
  for (string::const_iterator it = input.begin(), end = input.end(); it != end;
       ++it) {
    switch (*it) {
      case kBackslash:
        ++consecutive_backslash_count;
        break;
      case kQuote:
        result->append(span_begin, it);
        result->append(consecutive_backslash_count + 1, kBackslash);
        span_begin = it;
        consecutive_backslash_count = 0;
        break;
      default:
        consecutive_backslash_count = 0;
        break;
    }
  }
  result->append(span_begin, input.end());
  result->append(consecutive_backslash_count, kBackslash);
  result->push_back(kQuote);
}
*/

impl ExtendFromEscapedSlice<u8> for Vec<u8> {
    fn extend_from_shell_escaped_slice(&mut self, input: &[u8]) {
        unimplemented!()
    }
    fn extend_from_win32_escaped_slice(&mut self, input: &[u8]) {
        if !slice_needs_win32_escaping(input) {
            self.extend_from_slice(input);
            return;
        }
        /*
  const char kQuote = '"';
  const char kBackslash = '\\';

  result->push_back(kQuote);
  size_t consecutive_backslash_count = 0;
  string::const_iterator span_begin = input.begin();
  for (string::const_iterator it = input.begin(), end = input.end(); it != end;
       ++it) {
    switch (*it) {
      case kBackslash:
        ++consecutive_backslash_count;
        break;
      case kQuote:
        result->append(span_begin, it);
        result->append(consecutive_backslash_count + 1, kBackslash);
        span_begin = it;
        consecutive_backslash_count = 0;
        break;
      default:
        consecutive_backslash_count = 0;
        break;
    }
  }
  result->append(span_begin, input.end());
  result->append(consecutive_backslash_count, kBackslash);
  result->push_back(kQuote);
*/


        unimplemented!()
    }
}

/*
int ReadFile(const string& path, string* contents, string* err) {
#ifdef _WIN32
  // This makes a ninja run on a set of 1500 manifest files about 4% faster
  // than using the generic fopen code below.
  err->clear();
  HANDLE f = ::CreateFile(path.c_str(),
                          GENERIC_READ,
                          FILE_SHARE_READ,
                          NULL,
                          OPEN_EXISTING,
                          FILE_FLAG_SEQUENTIAL_SCAN,
                          NULL);
  if (f == INVALID_HANDLE_VALUE) {
    err->assign(GetLastErrorString());
    return -ENOENT;
  }

  for (;;) {
    DWORD len;
    char buf[64 << 10];
    if (!::ReadFile(f, buf, sizeof(buf), &len, NULL)) {
      err->assign(GetLastErrorString());
      contents->clear();
      return -1;
    }
    if (len == 0)
      break;
    contents->append(buf, len);
  }
  ::CloseHandle(f);
  return 0;
#else
  FILE* f = fopen(path.c_str(), "rb");
  if (!f) {
    err->assign(strerror(errno));
    return -errno;
  }

  char buf[64 << 10];
  size_t len;
  while ((len = fread(buf, 1, sizeof(buf), f)) > 0) {
    contents->append(buf, len);
  }
  if (ferror(f)) {
    err->assign(strerror(errno));  // XXX errno?
    contents->clear();
    fclose(f);
    return -errno;
  }
  fclose(f);
  return 0;
#endif
}

void SetCloseOnExec(int fd) {
#ifndef _WIN32
  int flags = fcntl(fd, F_GETFD);
  if (flags < 0) {
    perror("fcntl(F_GETFD)");
  } else {
    if (fcntl(fd, F_SETFD, flags | FD_CLOEXEC) < 0)
      perror("fcntl(F_SETFD)");
  }
#else
  HANDLE hd = (HANDLE) _get_osfhandle(fd);
  if (! SetHandleInformation(hd, HANDLE_FLAG_INHERIT, 0)) {
    fprintf(stderr, "SetHandleInformation(): %s", GetLastErrorString().c_str());
  }
#endif  // ! _WIN32
}


const char* SpellcheckStringV(const string& text,
                              const vector<const char*>& words) {
  const bool kAllowReplacements = true;
  const int kMaxValidEditDistance = 3;

  int min_distance = kMaxValidEditDistance + 1;
  const char* result = NULL;
  for (vector<const char*>::const_iterator i = words.begin();
       i != words.end(); ++i) {
    int distance = EditDistance(*i, text, kAllowReplacements,
                                kMaxValidEditDistance);
    if (distance < min_distance) {
      min_distance = distance;
      result = *i;
    }
  }
  return result;
}

const char* SpellcheckString(const char* text, ...) {
  // Note: This takes a const char* instead of a string& because using
  // va_start() with a reference parameter is undefined behavior.
  va_list ap;
  va_start(ap, text);
  vector<const char*> words;
  const char* word;
  while ((word = va_arg(ap, const char*)))
    words.push_back(word);
  va_end(ap);
  return SpellcheckStringV(text, words);
}

#ifdef _WIN32
string GetLastErrorString() {
  DWORD err = GetLastError();

  char* msg_buf;
  FormatMessageA(
        FORMAT_MESSAGE_ALLOCATE_BUFFER |
        FORMAT_MESSAGE_FROM_SYSTEM |
        FORMAT_MESSAGE_IGNORE_INSERTS,
        NULL,
        err,
        MAKELANGID(LANG_NEUTRAL, SUBLANG_DEFAULT),
        (char*)&msg_buf,
        0,
        NULL);
  string msg = msg_buf;
  LocalFree(msg_buf);
  return msg;
}

void Win32Fatal(const char* function) {
  Fatal("%s: %s", function, GetLastErrorString().c_str());
}
#endif

bool islatinalpha(int c) {
  // isalpha() is locale-dependent.
  return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z');
}

string StripAnsiEscapeCodes(const string& in) {
  string stripped;
  stripped.reserve(in.size());

  for (size_t i = 0; i < in.size(); ++i) {
    if (in[i] != '\33') {
      // Not an escape code.
      stripped.push_back(in[i]);
      continue;
    }

    // Only strip CSIs for now.
    if (i + 1 >= in.size()) break;
    if (in[i + 1] != '[') continue;  // Not a CSI.
    i += 2;

    // Skip everything up to and including the next [a-zA-Z].
    while (i < in.size() && !islatinalpha(in[i]))
      ++i;
  }
  return stripped;
}

*/

#[cfg(windows)]
pub fn get_load_average() -> Option<f64> {
    use std::mem::zeroed;
    use winapi;
    use kernel32;

    use winapi::FILETIME;

    fn filetime_to_tickcount(ft: &FILETIME) -> u64 {
        ((ft.dwHighDateTime as u64) << 32) | (ft.dwLowDateTime as u64)
    }

    fn calculate_processor_load(idle_ticks: u64, total_ticks: u64) -> Option<f64> {
        static mut PREVIOUS_IDLE_TICKS: u64 = 0;
        static mut PREVIOUS_TOTAL_TICKS: u64 = 0;
        static mut PREVIOUS_LOAD: Option<f64> = None;

        let (previous_idle_ticks, previous_total_ticks, previous_load) =
            unsafe { (PREVIOUS_IDLE_TICKS, PREVIOUS_TOTAL_TICKS, PREVIOUS_LOAD) };

        let idle_ticks_since_last_time = idle_ticks - previous_idle_ticks;
        let total_ticks_since_last_time = total_ticks - previous_total_ticks;

        let first_call = previous_total_ticks == 0;
        let ticks_not_updated_since_last_call = total_ticks_since_last_time == 0;

        let load;
        if first_call || ticks_not_updated_since_last_call {
            load = previous_load;
        } else {
            // Calculate load.
            let idle_to_total_ratio = idle_ticks_since_last_time as f64 /
                total_ticks_since_last_time as f64;
            let load_since_last_call = 1.0f64 - idle_to_total_ratio;

            // Filter/smooth result when possible.
            load = Some(if let Some(previous_load) = previous_load {
                0.9 * previous_load + 0.1 * load_since_last_call
            } else {
                load_since_last_call
            });
        }

        unsafe {
            PREVIOUS_LOAD = load;
            PREVIOUS_TOTAL_TICKS = total_ticks;
            PREVIOUS_IDLE_TICKS = idle_ticks;
        }

        load
    }

    unsafe {
        let mut idle_time = zeroed::<FILETIME>();
        let mut kernel_time = zeroed::<FILETIME>();
        let mut user_time = zeroed::<FILETIME>();

        if kernel32::GetSystemTimes(&mut idle_time, &mut kernel_time, &mut user_time) ==
            winapi::FALSE
        {
            return None;
        };

        let idle_ticks = filetime_to_tickcount(&idle_time);
        let total_ticks = filetime_to_tickcount(&kernel_time) + filetime_to_tickcount(&user_time);

        if let Some(processor_load) = calculate_processor_load(idle_ticks, total_ticks) {
            Some(processor_load * get_processor_count() as f64)
        } else {
            None
        }
    }
}
/*
double GetLoadAverage() {
  FILETIME idle_time, kernel_time, user_time;
  BOOL get_system_time_succeeded =
      GetSystemTimes(&idle_time, &kernel_time, &user_time);

  double posix_compatible_load;
  if (get_system_time_succeeded) {
    uint64_t idle_ticks = FileTimeToTickCount(idle_time);

    // kernel_time from GetSystemTimes already includes idle_time.
    uint64_t total_ticks =
        FileTimeToTickCount(kernel_time) + FileTimeToTickCount(user_time);

    double processor_load = CalculateProcessorLoad(idle_ticks, total_ticks);
    posix_compatible_load = processor_load * GetProcessorCount();

  } else {
    posix_compatible_load = -0.0;
  }

  return posix_compatible_load;
}
#elif defined(_AIX)
double GetLoadAverage() {
  perfstat_cpu_total_t cpu_stats;
  if (perfstat_cpu_total(NULL, &cpu_stats, sizeof(cpu_stats), 1) < 0) {
    return -0.0f;
  }

  // Calculation taken from comment in libperfstats.h
  return double(cpu_stats.loadavg[0]) / double(1 << SBITS);
}
#elif defined(__UCLIBC__)
double GetLoadAverage() {
  struct sysinfo si;
  if (sysinfo(&si) != 0)
    return -0.0f;
  return 1.0 / (1 << SI_LOAD_SHIFT) * si.loads[0];
}
#else
*/
#[cfg(unix)]
pub fn get_load_average() -> Option<f64> {
    let mut load_avg: [f64; 3] = [0.0f64, 0.0f64, 0.0f64];
    unsafe {
        if libc::getloadavg(load_avg.as_mut().ptr_mut(), 3) < 0 {
            return None;
        }
    }
    load_avg[0]
}

/*
double GetLoadAverage() {
  double loadavg[3] = { 0.0f, 0.0f, 0.0f };
  if (getloadavg(loadavg, 3) < 0) {
    // Maybe we should return an error here or the availability of
    // getloadavg(3) should be checked when ninja is configured.
    return -0.0f;
  }
  return loadavg[0];
}
#endif // _WIN32

string ElideMiddle(const string& str, size_t width) {
  const int kMargin = 3;  // Space for "...".
  string result = str;
  if (result.size() + kMargin > width) {
    size_t elide_size = (width - kMargin) / 2;
    result = result.substr(0, elide_size)
      + "..."
      + result.substr(result.size() - elide_size, elide_size);
  }
  return result;
}

bool Truncate(const string& path, size_t size, string* err) {
#ifdef _WIN32
  int fh = _sopen(path.c_str(), _O_RDWR | _O_CREAT, _SH_DENYNO,
                  _S_IREAD | _S_IWRITE);
  int success = _chsize(fh, size);
  _close(fh);
#else
  int success = truncate(path.c_str(), size);
#endif
  // Both truncate() and _chsize() return 0 on success and set errno and return
  // -1 on failure.
  if (success < 0) {
    *err = strerror(errno);
    return false;
  }
  return true;
}

*/

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canonicalize_path_path_samples() {
        struct TestItem {
            path: &'static [u8],
            result: &'static [u8],
        }

        assert_eq!(canonicalize_path(&mut vec![]), Err("empty path".to_owned()));

        let test_items = vec![
            TestItem {
                path: b"foo.h",
                result: b"foo.h",
            },
        ];

        for test_item in test_items {
            let mut path = test_item.path.to_owned();
            assert!(canonicalize_path(&mut path).is_ok());
            assert_eq!(path.as_slice(), test_item.result);
        }
    }

}

/*

namespace {

bool CanonicalizePath(string* path, string* err) {
  uint64_t unused;
  return ::CanonicalizePath(path, &unused, err);
}

}  // namespace

TEST(CanonicalizePath, PathSamples) {
  string path;
  string err;

  EXPECT_FALSE(CanonicalizePath(&path, &err));
  EXPECT_EQ("empty path", err);

  path = "foo.h"; err = "";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo.h", path);

  path = "./foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo.h", path);

  path = "./foo/./bar.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo/bar.h", path);

  path = "./x/foo/../bar.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("x/bar.h", path);

  path = "./x/foo/../../bar.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("bar.h", path);

  path = "foo//bar";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo/bar", path);

  path = "foo//.//..///bar";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("bar", path);

  path = "./x/../foo/../../bar.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("../bar.h", path);

  path = "foo/./.";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo", path);

  path = "foo/bar/..";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo", path);

  path = "foo/.hidden_bar";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo/.hidden_bar", path);

  path = "/foo";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("/foo", path);

  path = "//foo";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
#ifdef _WIN32
  EXPECT_EQ("//foo", path);
#else
  EXPECT_EQ("/foo", path);
#endif

  path = "/";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("", path);

  path = "/foo/..";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("", path);

  path = ".";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ(".", path);

  path = "./.";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ(".", path);

  path = "foo/..";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ(".", path);
}

#ifdef _WIN32
TEST(CanonicalizePath, PathSamplesWindows) {
  string path;
  string err;

  EXPECT_FALSE(CanonicalizePath(&path, &err));
  EXPECT_EQ("empty path", err);

  path = "foo.h"; err = "";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo.h", path);

  path = ".\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo.h", path);

  path = ".\\foo\\.\\bar.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo/bar.h", path);

  path = ".\\x\\foo\\..\\bar.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("x/bar.h", path);

  path = ".\\x\\foo\\..\\..\\bar.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("bar.h", path);

  path = "foo\\\\bar";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo/bar", path);

  path = "foo\\\\.\\\\..\\\\\\bar";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("bar", path);

  path = ".\\x\\..\\foo\\..\\..\\bar.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("../bar.h", path);

  path = "foo\\.\\.";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo", path);

  path = "foo\\bar\\..";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo", path);

  path = "foo\\.hidden_bar";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("foo/.hidden_bar", path);

  path = "\\foo";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("/foo", path);

  path = "\\\\foo";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("//foo", path);

  path = "\\";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("", path);
}

TEST(CanonicalizePath, SlashTracking) {
  string path;
  string err;
  uint64_t slash_bits;

  path = "foo.h"; err = "";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("foo.h", path);
  EXPECT_EQ(0, slash_bits);

  path = "a\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/foo.h", path);
  EXPECT_EQ(1, slash_bits);

  path = "a/bcd/efh\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/bcd/efh/foo.h", path);
  EXPECT_EQ(4, slash_bits);

  path = "a\\bcd/efh\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/bcd/efh/foo.h", path);
  EXPECT_EQ(5, slash_bits);

  path = "a\\bcd\\efh\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/bcd/efh/foo.h", path);
  EXPECT_EQ(7, slash_bits);

  path = "a/bcd/efh/foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/bcd/efh/foo.h", path);
  EXPECT_EQ(0, slash_bits);

  path = "a\\./efh\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/efh/foo.h", path);
  EXPECT_EQ(3, slash_bits);

  path = "a\\../efh\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("efh/foo.h", path);
  EXPECT_EQ(1, slash_bits);

  path = "a\\b\\c\\d\\e\\f\\g\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/b/c/d/e/f/g/foo.h", path);
  EXPECT_EQ(127, slash_bits);

  path = "a\\b\\c\\..\\..\\..\\g\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("g/foo.h", path);
  EXPECT_EQ(1, slash_bits);

  path = "a\\b/c\\../../..\\g\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("g/foo.h", path);
  EXPECT_EQ(1, slash_bits);

  path = "a\\b/c\\./../..\\g\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/g/foo.h", path);
  EXPECT_EQ(3, slash_bits);

  path = "a\\b/c\\./../..\\g/foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/g/foo.h", path);
  EXPECT_EQ(1, slash_bits);

  path = "a\\\\\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/foo.h", path);
  EXPECT_EQ(1, slash_bits);

  path = "a/\\\\foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/foo.h", path);
  EXPECT_EQ(0, slash_bits);

  path = "a\\//foo.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ("a/foo.h", path);
  EXPECT_EQ(1, slash_bits);
}

TEST(CanonicalizePath, CanonicalizeNotExceedingLen) {
  // Make sure searching \/ doesn't go past supplied len.
  char buf[] = "foo/bar\\baz.h\\";  // Last \ past end.
  uint64_t slash_bits;
  string err;
  size_t size = 13;
  EXPECT_TRUE(::CanonicalizePath(buf, &size, &slash_bits, &err));
  EXPECT_EQ(0, strncmp("foo/bar/baz.h", buf, size));
  EXPECT_EQ(2, slash_bits);  // Not including the trailing one.
}

TEST(CanonicalizePath, TooManyComponents) {
  string path;
  string err;
  uint64_t slash_bits;

  // 64 is OK.
  path = "a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./"
         "a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./x.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ(slash_bits, 0x0);

  // Backslashes version.
  path =
      "a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\"
      "a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\"
      "a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\"
      "a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\x.h";

  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ(slash_bits, 0xffffffff);

  // 65 is OK if #component is less than 60 after path canonicalization.
  err = "";
  path = "a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./"
         "a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./a/./x/y.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ(slash_bits, 0x0);

  // Backslashes version.
  err = "";
  path =
      "a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\"
      "a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\"
      "a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\"
      "a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\a\\.\\x\\y.h";
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ(slash_bits, 0x1ffffffff);


  // 59 after canonicalization is OK.
  err = "";
  path = "a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/"
         "a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/a/x/y.h";
  EXPECT_EQ(58, std::count(path.begin(), path.end(), '/'));
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ(slash_bits, 0x0);

  // Backslashes version.
  err = "";
  path =
      "a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\"
      "a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\"
      "a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\a\\"
      "a\\a\\a\\a\\a\\a\\a\\a\\a\\x\\y.h";
  EXPECT_EQ(58, std::count(path.begin(), path.end(), '\\'));
  EXPECT_TRUE(CanonicalizePath(&path, &slash_bits, &err));
  EXPECT_EQ(slash_bits, 0x3ffffffffffffff);
}
#endif

TEST(CanonicalizePath, UpDir) {
  string path, err;
  path = "../../foo/bar.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("../../foo/bar.h", path);

  path = "test/../../foo/bar.h";
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("../foo/bar.h", path);
}

TEST(CanonicalizePath, AbsolutePath) {
  string path = "/usr/include/stdio.h";
  string err;
  EXPECT_TRUE(CanonicalizePath(&path, &err));
  EXPECT_EQ("/usr/include/stdio.h", path);
}

TEST(CanonicalizePath, NotNullTerminated) {
  string path;
  string err;
  size_t len;
  uint64_t unused;

  path = "foo/. bar/.";
  len = strlen("foo/.");  // Canonicalize only the part before the space.
  EXPECT_TRUE(CanonicalizePath(&path[0], &len, &unused, &err));
  EXPECT_EQ(strlen("foo"), len);
  EXPECT_EQ("foo/. bar/.", string(path));

  path = "foo/../file bar/.";
  len = strlen("foo/../file");
  EXPECT_TRUE(CanonicalizePath(&path[0], &len, &unused, &err));
  EXPECT_EQ(strlen("file"), len);
  EXPECT_EQ("file ./file bar/.", string(path));
}

TEST(PathEscaping, TortureTest) {
  string result;

  GetWin32EscapedString("foo bar\\\"'$@d!st!c'\\path'\\", &result);
  EXPECT_EQ("\"foo bar\\\\\\\"'$@d!st!c'\\path'\\\\\"", result);
  result.clear();

  GetShellEscapedString("foo bar\"/'$@d!st!c'/path'", &result);
  EXPECT_EQ("'foo bar\"/'\\''$@d!st!c'\\''/path'\\'''", result);
}

TEST(PathEscaping, SensiblePathsAreNotNeedlesslyEscaped) {
  const char* path = "some/sensible/path/without/crazy/characters.c++";
  string result;

  GetWin32EscapedString(path, &result);
  EXPECT_EQ(path, result);
  result.clear();

  GetShellEscapedString(path, &result);
  EXPECT_EQ(path, result);
}

TEST(PathEscaping, SensibleWin32PathsAreNotNeedlesslyEscaped) {
  const char* path = "some\\sensible\\path\\without\\crazy\\characters.c++";
  string result;

  GetWin32EscapedString(path, &result);
  EXPECT_EQ(path, result);
}

TEST(StripAnsiEscapeCodes, EscapeAtEnd) {
  string stripped = StripAnsiEscapeCodes("foo\33");
  EXPECT_EQ("foo", stripped);

  stripped = StripAnsiEscapeCodes("foo\33[");
  EXPECT_EQ("foo", stripped);
}

TEST(StripAnsiEscapeCodes, StripColors) {
  // An actual clang warning.
  string input = "\33[1maffixmgr.cxx:286:15: \33[0m\33[0;1;35mwarning: "
                 "\33[0m\33[1musing the result... [-Wparentheses]\33[0m";
  string stripped = StripAnsiEscapeCodes(input);
  EXPECT_EQ("affixmgr.cxx:286:15: warning: using the result... [-Wparentheses]",
            stripped);
}

TEST(ElideMiddle, NothingToElide) {
  string input = "Nothing to elide in this short string.";
  EXPECT_EQ(input, ElideMiddle(input, 80));
}

TEST(ElideMiddle, ElideInTheMiddle) {
  string input = "01234567890123456789";
  string elided = ElideMiddle(input, 10);
  EXPECT_EQ("012...789", elided);
}
*/
