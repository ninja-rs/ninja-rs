// Copyright 2012 Google Inc. All Rights Reserved.
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

use std::collections::{VecDeque, HashMap};
use std::cell::Cell;

use super::exit_status::ExitStatus;

/*

#ifndef NINJA_SUBPROCESS_H_
#define NINJA_SUBPROCESS_H_

#include <string>
#include <vector>
#include <queue>
using namespace std;

#ifdef _WIN32
#include <windows.h>
#else
#include <signal.h>
#endif

// ppoll() exists on FreeBSD, but only on newer versions.
#ifdef __FreeBSD__
#  include <sys/param.h>
#  if defined USE_PPOLL && __FreeBSD_version < 1002000
#    undef USE_PPOLL
#  endif
#endif

#include "exit_status.h"
*/

#[cfg(windows)]
struct SubprocessOs {
    pub child: ::winapi::HANDLE,
    pub pipe:  ::winapi::HANDLE,
    pub overlapped: ::winapi::OVERLAPPED,
    pub overlapped_buf: [u8; 4096],
    pub is_reading: bool,
}

#[cfg(windows)]
impl Default for SubprocessOs {
    fn default() -> Self {
        unsafe { ::std::mem::zeroed() }
    }
}


#[cfg(unix)]
#[derive(Default)]
struct SubprocessOs {
    pub fd: Option<::libc::c_int>,
    pub pid: Option<::libc::pid_t>,
}

/// Subprocess wraps a single async subprocess.  It is entirely
/// passive: it expects the caller to notify it when its fds are ready
/// for reading, as well as call Finish() to reap the child once done()
/// is true.
pub struct Subprocess {
    use_console: bool,
    buf: Vec<u8>,
    extra: Box<SubprocessOs>,
}

impl Subprocess {

    // always boxed to make sure pointer to self is not changed.
    pub(super) fn new(use_console: bool) -> Box<Self> {
        Box::new(Subprocess {
            use_console,
            buf: Vec::new(),
            extra: Default::default(),
        })
    }

    pub fn output(&self) -> &[u8] {
        &self.buf
    }    
}

#[cfg(windows)]
impl Drop for Subprocess {
    fn drop(&mut self) {
        use winapi;
        use errno;
        use kernel32;

        if !self.extra.pipe.is_null() {
            if unsafe { kernel32::CloseHandle(self.extra.pipe) } == winapi::FALSE {
                fatal!("CloseHandle: {}", errno::errno());
            }
        }

        // Reap child if forgotten.
        if self.exist() {
            self.finish();
        }
    }
}

#[cfg(windows)]
impl Subprocess {
    pub(super) fn exist(&self) -> bool {
        !self.extra.child.is_null()
    }

    pub(super) fn start<T>(&mut self, set: &mut SubprocessSet<T>, command: &[u8]) -> bool {
        use winapi;
        use kernel32;
        use std::ptr::null_mut;
        use std::mem::{zeroed, size_of};

        let child_pipe = self.setup_pipe(set.extra.ioport());

        let mut security_attributes = unsafe { zeroed::<winapi::SECURITY_ATTRIBUTES>() };
        security_attributes.nLength = size_of::<winapi::SECURITY_ATTRIBUTES>() as _;
        security_attributes.bInheritHandle = winapi::TRUE;

        let nul_name = wstrz!("NUL");

        let nul = unsafe { kernel32::CreateFileW(nul_name.as_ptr(), 
            winapi::GENERIC_READ,
            winapi::FILE_SHARE_READ | winapi::FILE_SHARE_WRITE | winapi::FILE_SHARE_DELETE,
            &mut security_attributes as _, winapi::OPEN_EXISTING, 0, null_mut()) };
        
        if nul == winapi::INVALID_HANDLE_VALUE {
            fatal!("couldn't open nul");
        }

        let mut startup_info = unsafe { zeroed::<winapi::STARTUPINFOW>() };
        startup_info.cb = size_of::<winapi::STARTUPINFOW>() as _;
        if !self.use_console {
            startup_info.dwFlags = winapi::STARTF_USESTDHANDLES;
            startup_info.hStdInput = nul;
            startup_info.hStdOutput = child_pipe;
            startup_info.hStdError = child_pipe;
        }

        // In the console case, child_pipe is still inherited by the child and closed
        // when the subprocess finishes, which then notifies ninja.
        let mut process_info = unsafe { zeroed::<winapi::PROCESS_INFORMATION>() };

        // Ninja handles ctrl-c, except for subprocesses in console pools.
        let process_flags = if self.use_console { 0 } else { winapi::CREATE_NEW_PROCESS_GROUP };

        // Do not prepend 'cmd /c' on Windows, this breaks command
        // lines greater than 8,191 chars.
        let cmd_unicode = ::std::str::from_utf8(command);
        let create_process_result = match &cmd_unicode {
            &Err(_) => Err(None),
            &Ok (ref cmd_unicode) => {
                if let Ok(cmd) = ::widestring::WideCString::from_str(cmd_unicode) {
                    let mut cmd = cmd.into_vec();
                    if unsafe { 
                          kernel32::CreateProcessW(null_mut(), 
                                cmd.as_mut_ptr(), null_mut(), null_mut(),
                                winapi::TRUE, process_flags, null_mut(), 
                                null_mut(), &mut startup_info as _, &mut process_info as _) }
                           != winapi::FALSE {
                        Ok(())
                    } else {
                        Err(Some(unsafe {kernel32::GetLastError()}))
                    }
                } else {
                    Err(None)
                }
            }
        };

        if !child_pipe.is_null() {
            unsafe { kernel32::CloseHandle(child_pipe) };
        }

        unsafe { kernel32::CloseHandle(nul) };

        match create_process_result {
            Ok(()) => {
                unsafe { kernel32::CloseHandle(process_info.hThread) };
                self.extra.child = process_info.hProcess;
                true
            },
            Err(e @ Some(winapi::ERROR_FILE_NOT_FOUND)) | Err(e @ None) => {
                // File (program) not found error is treated as a normal build
                // action failure.
                unsafe { kernel32::CloseHandle(self.extra.pipe) };
                self.extra.pipe = null_mut();
                // child_ is already NULL;
                self.buf = if e.is_some() {
                    b"CreateProcess failed: The system cannot find the file specified.\n".as_ref().to_owned()
                } else {
                    b"CreateProcess failed: The command is not valid UTF-8 string.\n".as_ref().to_owned()
                };
                true
            }
            Err(Some(e)) => {
                fatal!("CreateProcess : {}", ::errno::Errno(e as _))
            },
        }
    }


    /// Set up pipe_ as the parent-side pipe of the subprocess; return the
    /// other end of the pipe, usable in the child process.
    fn setup_pipe(&mut self, ioport: ::winapi::HANDLE) -> ::winapi::HANDLE {
        use winapi;
        use kernel32;
        use errno;
        use std::mem::zeroed;
        use std::ptr::null_mut;
        use widestring::WideCString;
        let pipe_name = format!("\\\\.\\pipe\\ninja_pid{}_sp{:p}", 
            unsafe { kernel32::GetCurrentProcessId() },
            self);

        let pipe_name = WideCString::from_str(pipe_name).unwrap().into_vec();

        self.extra.pipe = unsafe {
          kernel32::CreateNamedPipeW(
            pipe_name.as_ptr(),
            winapi::PIPE_ACCESS_INBOUND | winapi::FILE_FLAG_OVERLAPPED,
            winapi::PIPE_TYPE_BYTE,
            winapi::PIPE_UNLIMITED_INSTANCES,
            0, 0, winapi::INFINITE, null_mut())
        };

        if self.extra.pipe == winapi::INVALID_HANDLE_VALUE {
            fatal!("CreateNamedPipe : {}", errno::errno());
        }

        let create_port_result = unsafe {
            kernel32::CreateIoCompletionPort(self.extra.pipe, ioport, self as * mut _ as usize as _, 0)
        };
        if create_port_result.is_null() {
            fatal!("CreateIoCompletionPort : {}", errno::errno());
        }

        self.extra.overlapped = unsafe { zeroed() };
        if unsafe {
            kernel32::ConnectNamedPipe(self.extra.pipe, &mut self.extra.overlapped as _ )
        } == winapi::FALSE && unsafe { kernel32::GetLastError() } != winapi::ERROR_IO_PENDING {
            fatal!("ConnectNamedPipe : {}", errno::errno());
        }

        // Get the write end of the pipe as a handle inheritable across processes.
        let output_write_handle = unsafe { 
          kernel32::CreateFileW(pipe_name.as_ptr(), winapi::GENERIC_WRITE, 0, null_mut(), 
                                winapi::OPEN_EXISTING, 0, null_mut())
        };
        let mut output_write_child = null_mut();
        if unsafe { kernel32::DuplicateHandle(
            kernel32::GetCurrentProcess(), output_write_handle,
            kernel32::GetCurrentProcess(), &mut output_write_child as _,
            0, winapi::TRUE, winapi::DUPLICATE_SAME_ACCESS) } == winapi::FALSE {
            
            fatal!("DuplicateHandle : {}", errno::errno());
        }

        unsafe {
            kernel32::CloseHandle(output_write_handle);
        }

        output_write_child
    }

    pub fn on_pipe_ready(&mut self) {
        use winapi;
        use kernel32;
        use errno;
        use std::mem::{zeroed, size_of_val};
        use std::ptr::null_mut;

        let mut bytes = 0 as winapi::DWORD;
        if unsafe { kernel32::GetOverlappedResult(
            self.extra.pipe, 
            &mut self.extra.overlapped as * mut _,
            &mut bytes as * mut _,
            winapi::TRUE)} == winapi::FALSE {
            
            if unsafe {kernel32::GetLastError()} == winapi::ERROR_BROKEN_PIPE {
                unsafe { kernel32::CloseHandle(self.extra.pipe) };
                self.extra.pipe = null_mut();
            }
            else {
                fatal!("GetOverlappedResult: {}", errno::errno());
            }
            return;
        }
        if self.extra.is_reading && bytes > 0 {
          self.buf.extend_from_slice(&self.extra.overlapped_buf[0..(bytes as usize)]);
        }

        self.extra.overlapped = unsafe { zeroed() };
        self.extra.is_reading = true;

        if unsafe { kernel32::ReadFile(
            self.extra.pipe, 
            self.extra.overlapped_buf.as_mut_ptr() as usize as _, 
            size_of_val(&self.extra.overlapped_buf) as _,
            &mut bytes as * mut _,
            &mut self.extra.overlapped as * mut _) } == winapi::FALSE {

            match unsafe { kernel32::GetLastError() } {
                winapi::ERROR_IO_PENDING => { },
                winapi::ERROR_BROKEN_PIPE => {
                    unsafe { kernel32::CloseHandle(self.extra.pipe) };
                    self.extra.pipe = null_mut();
                },
                e => {
                    fatal!("ReadFile : {}", errno::errno());
                }
            }
            return;
        }

        // Even if we read any bytes in the readfile call, we'll enter this
        // function again later and get them at that point.
    }

    /// Returns ExitSuccess on successful process exit, ExitInterrupted if
    /// the process was interrupted, ExitFailure if it otherwise failed.
    pub fn finish(&mut self) -> ExitStatus {
        use winapi;
        use kernel32;

        if !self.exist() {
            return ExitStatus::ExitFailure;
        }

        // TODO: add error handling for all of these.
        unsafe {
            kernel32::WaitForSingleObject(self.extra.child, winapi::INFINITE);
        }

        let mut exit_code = 0 as winapi::DWORD;
        unsafe { kernel32::GetExitCodeProcess(self.extra.child, &mut exit_code as _) };
        unsafe { kernel32::CloseHandle(self.extra.child) };

        self.extra.child = ::std::ptr::null_mut();

        match exit_code as _ {
          0 => ExitStatus::ExitSuccess,
          winapi::STATUS_CONTROL_C_EXIT => ExitStatus::ExitInterrupted,
          _ => ExitStatus::ExitFailure,
        }
    }
    
    fn done(&self) -> bool {
        self.extra.pipe.is_null()
    }
}

#[cfg(unix)]
impl Subprocess {
    pub(super) fn exist(&self) -> bool {
        true
    }

    pub(super) fn start<T>(&mut self, set: &mut SubprocessSet<T>, command: &[u8]) -> bool {
        unimplemented!()
    }

    fn done(&self) -> bool {
        self.extra.fd.is_none()
    }
}

/*
struct Subprocess {
  ~Subprocess();

  /// Returns ExitSuccess on successful process exit, ExitInterrupted if
  /// the process was interrupted, ExitFailure if it otherwise failed.
  ExitStatus Finish();

  bool Done() const;

  const string& GetOutput() const;

 private:
  Subprocess(bool use_console);
  bool Start(struct SubprocessSet* set, const string& command);
  void OnPipeReady();

  string buf_;

#ifdef _WIN32

  HANDLE child_;
  HANDLE pipe_;
  OVERLAPPED overlapped_;
  char overlapped_buf_[4 << 10];
  bool is_reading_;
#else
  int fd_;
  pid_t pid_;
#endif
  bool use_console_;

  friend struct SubprocessSet;
};
*/

#[cfg(windows)]
struct SubprocessSetOs {

}

#[cfg(windows)]
thread_local! {
    static IOPORT : ::std::cell::Cell<::winapi::HANDLE> = ::std::cell::Cell::new(::std::ptr::null_mut());
}

#[cfg(windows)]
unsafe extern "system" fn notify_interrupted(_: ::winapi::DWORD) -> ::winapi::BOOL {
    unimplemented!{}
}

#[cfg(windows)]
impl SubprocessSetOs {
    pub fn new() -> Self {
        use winapi;
        use kernel32;
        use errno; 
        use std::ptr::null_mut;

        let v = SubprocessSetOs{};
        let ioport = unsafe { kernel32::CreateIoCompletionPort(
              winapi::INVALID_HANDLE_VALUE, 
              null_mut(),
              0,
              1)};
        if ioport.is_null() {
            fatal!("CreateIoCompletionPort: {}", errno::errno());
        }
        v.set_ioport(ioport);
        if unsafe { kernel32::SetConsoleCtrlHandler(Some(notify_interrupted), winapi::TRUE)} 
            == winapi::FALSE {
            fatal!("SetConsoleCtrlHandler: {}", errno::errno());
        }
        v
    }

    pub fn ioport(&self) -> ::winapi::HANDLE {
        IOPORT.with(|p| p.get())
    }

    pub fn set_ioport(&self, ioport: ::winapi::HANDLE) {
        IOPORT.with(|p| p.set(ioport))
    }
}


#[cfg(unix)]
struct SubprocessSetOs {

}


/// SubprocessSet runs a ppoll/pselect() loop around a set of Subprocesses.
/// DoWork() waits for any state change in subprocesses; finished_
/// is a queue of subprocesses as they finish.
pub struct SubprocessSet<Data = ()> {
    running: HashMap<usize, (Box<Subprocess>, Data)>,
    finished: VecDeque<(Box<Subprocess>, Data)>,
    extra: SubprocessSetOs,
}

type Iter<'a, Data> = ::std::iter::Chain<
    ::std::collections::vec_deque::Iter<'a, (Box<Subprocess>, Data)>,
    ::std::collections::hash_map::Values<'a, usize, (Box<Subprocess>, Data)>>;

impl<Data> SubprocessSet<Data> {
    pub fn new() -> Self {
        SubprocessSet {
            running: HashMap::new(),
            finished: VecDeque::new(),
            extra: SubprocessSetOs::new(),
        }
    }

    pub fn running(&self) -> &HashMap<usize, (Box<Subprocess>,Data)> {
        &self.running
    }

    pub fn finished(&self) -> &VecDeque<(Box<Subprocess>,Data)> {
        &self.finished
    }

    pub fn add(&mut self, command: &[u8], use_console: bool, data: Data) 
        -> Option<&mut(Box<Subprocess>, Data)> {
            
        let mut subprocess = Subprocess::new(use_console);
        if !subprocess.start(self, command) {
            return None;
        }

        if subprocess.exist() {
            let key = subprocess.as_ref() as * const _ as usize;
            self.running.insert(key, (subprocess, data));
            return self.running.get_mut(&key);
        } else {
            self.finished.push_back((subprocess, data));
            return self.finished.back_mut();
        }
    }

    pub fn next_finished(&mut self) -> Option<(Box<Subprocess>, Data)> {
        self.finished.pop_front()
    }

    pub fn iter<'a>(&'a self) -> Iter<'a, Data> {
        self.finished.iter().chain(self.running.values())
    }

    pub fn clear(&mut self) {
        self.running.clear();
        return;
        unimplemented!{}
    }
}

#[cfg(windows)]
impl<Data> SubprocessSet<Data> {

    // return Err(()) if interrupted.
    pub fn do_work(&mut self) -> Result<(), ()> {
        use winapi;
        use kernel32;
        use errno;
        use std::ptr::null_mut;

        let mut bytes_read = 0 as winapi::DWORD;
        let mut subproc = null_mut::<Subprocess>();
        let mut overlapped = null_mut::<winapi::OVERLAPPED>();

        if unsafe { kernel32::GetQueuedCompletionStatus(self.extra.ioport(), 
                    &mut bytes_read as _, 
                    &mut subproc as * mut _ as usize as _, 
                    &mut overlapped as * mut _,
                    winapi::INFINITE)} == winapi::FALSE {
            if unsafe { kernel32::GetLastError() } != winapi::ERROR_BROKEN_PIPE {
                fatal!("GetQueuedCompletionStatus: {}", errno::errno());
            }
        }

        let done = if let Some(subproc) = unsafe { subproc.as_mut() } {
            subproc.on_pipe_ready();

            subproc.done()
        } else {
            // A NULL subproc indicates that we were interrupted and is
            // delivered by NotifyInterrupted above.
            return Err(());
        };

        if done {
            self.finished.extend(self.running.remove(&(subproc as usize)).into_iter());
        }

        return Ok(());
    }
}

/*
struct SubprocessSet {
  SubprocessSet();
  ~SubprocessSet();

  Subprocess* Add(const string& command, bool use_console = false);
  bool DoWork();
  Subprocess* NextFinished();
  void Clear();

  vector<Subprocess*> running_;
  queue<Subprocess*> finished_;

#ifdef _WIN32
  static BOOL WINAPI NotifyInterrupted(DWORD dwCtrlType);
  static HANDLE ioport_;
#else
  static void SetInterruptedFlag(int signum);
  static void HandlePendingInterruption();
  /// Store the signal number that causes the interruption.
  /// 0 if not interruption.
  static int interrupted_;

  static bool IsInterrupted() { return interrupted_ != 0; }

  struct sigaction old_int_act_;
  struct sigaction old_term_act_;
  struct sigaction old_hup_act_;
  sigset_t old_mask_;
#endif
};

#endif // NINJA_SUBPROCESS_H_

*/

#[cfg(windows)]
mod imp {
/*
// Copyright 2012 Google Inc. All Rights Reserved.
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

#include "subprocess.h"

#include <assert.h>
#include <stdio.h>

#include <algorithm>

#include "util.h"

Subprocess::Subprocess(bool use_console) : child_(NULL) , overlapped_(),
                                           is_reading_(false),
                                           use_console_(use_console) {
}

Subprocess::~Subprocess() {
  if (pipe_) {
    if (!CloseHandle(pipe_))
      Win32Fatal("CloseHandle");
  }
  // Reap child if forgotten.
  if (child_)
    Finish();
}

HANDLE Subprocess::SetupPipe(HANDLE ioport) {
  char pipe_name[100];
  snprintf(pipe_name, sizeof(pipe_name),
           "\\\\.\\pipe\\ninja_pid%lu_sp%p", GetCurrentProcessId(), this);

  pipe_ = ::CreateNamedPipeA(pipe_name,
                             PIPE_ACCESS_INBOUND | FILE_FLAG_OVERLAPPED,
                             PIPE_TYPE_BYTE,
                             PIPE_UNLIMITED_INSTANCES,
                             0, 0, INFINITE, NULL);
  if (pipe_ == INVALID_HANDLE_VALUE)
    Win32Fatal("CreateNamedPipe");

  if (!CreateIoCompletionPort(pipe_, ioport, (ULONG_PTR)this, 0))
    Win32Fatal("CreateIoCompletionPort");

  memset(&overlapped_, 0, sizeof(overlapped_));
  if (!ConnectNamedPipe(pipe_, &overlapped_) &&
      GetLastError() != ERROR_IO_PENDING) {
    Win32Fatal("ConnectNamedPipe");
  }

  // Get the write end of the pipe as a handle inheritable across processes.
  HANDLE output_write_handle = CreateFile(pipe_name, GENERIC_WRITE, 0,
                                          NULL, OPEN_EXISTING, 0, NULL);
  HANDLE output_write_child;
  if (!DuplicateHandle(GetCurrentProcess(), output_write_handle,
                       GetCurrentProcess(), &output_write_child,
                       0, TRUE, DUPLICATE_SAME_ACCESS)) {
    Win32Fatal("DuplicateHandle");
  }
  CloseHandle(output_write_handle);

  return output_write_child;
}

void Subprocess::OnPipeReady() {
  DWORD bytes;
  if (!GetOverlappedResult(pipe_, &overlapped_, &bytes, TRUE)) {
    if (GetLastError() == ERROR_BROKEN_PIPE) {
      CloseHandle(pipe_);
      pipe_ = NULL;
      return;
    }
    Win32Fatal("GetOverlappedResult");
  }

  if (is_reading_ && bytes)
    buf_.append(overlapped_buf_, bytes);

  memset(&overlapped_, 0, sizeof(overlapped_));
  is_reading_ = true;
  if (!::ReadFile(pipe_, overlapped_buf_, sizeof(overlapped_buf_),
                  &bytes, &overlapped_)) {
    if (GetLastError() == ERROR_BROKEN_PIPE) {
      CloseHandle(pipe_);
      pipe_ = NULL;
      return;
    }
    if (GetLastError() != ERROR_IO_PENDING)
      Win32Fatal("ReadFile");
  }

  // Even if we read any bytes in the readfile call, we'll enter this
  // function again later and get them at that point.
}

ExitStatus Subprocess::Finish() {
  if (!child_)
    return ExitFailure;

  // TODO: add error handling for all of these.
  WaitForSingleObject(child_, INFINITE);

  DWORD exit_code = 0;
  GetExitCodeProcess(child_, &exit_code);

  CloseHandle(child_);
  child_ = NULL;

  return exit_code == 0              ? ExitSuccess :
         exit_code == CONTROL_C_EXIT ? ExitInterrupted :
                                       ExitFailure;
}


HANDLE SubprocessSet::ioport_;

SubprocessSet::SubprocessSet() {
  ioport_ = ::CreateIoCompletionPort(INVALID_HANDLE_VALUE, NULL, 0, 1);
  if (!ioport_)
    Win32Fatal("CreateIoCompletionPort");
  if (!SetConsoleCtrlHandler(NotifyInterrupted, TRUE))
    Win32Fatal("SetConsoleCtrlHandler");
}

SubprocessSet::~SubprocessSet() {
  Clear();

  SetConsoleCtrlHandler(NotifyInterrupted, FALSE);
  CloseHandle(ioport_);
}

BOOL WINAPI SubprocessSet::NotifyInterrupted(DWORD dwCtrlType) {
  if (dwCtrlType == CTRL_C_EVENT || dwCtrlType == CTRL_BREAK_EVENT) {
    if (!PostQueuedCompletionStatus(ioport_, 0, 0, NULL))
      Win32Fatal("PostQueuedCompletionStatus");
    return TRUE;
  }

  return FALSE;
}

Subprocess *SubprocessSet::Add(const string& command, bool use_console) {
  Subprocess *subprocess = new Subprocess(use_console);
  if (!subprocess->Start(this, command)) {
    delete subprocess;
    return 0;
  }
  if (subprocess->child_)
    running_.push_back(subprocess);
  else
    finished_.push(subprocess);
  return subprocess;
}

bool SubprocessSet::DoWork() {
  DWORD bytes_read;
  Subprocess* subproc;
  OVERLAPPED* overlapped;

  if (!GetQueuedCompletionStatus(ioport_, &bytes_read, (PULONG_PTR)&subproc,
                                 &overlapped, INFINITE)) {
    if (GetLastError() != ERROR_BROKEN_PIPE)
      Win32Fatal("GetQueuedCompletionStatus");
  }

  if (!subproc) // A NULL subproc indicates that we were interrupted and is
                // delivered by NotifyInterrupted above.
    return true;

  subproc->OnPipeReady();

  if (subproc->Done()) {
    vector<Subprocess*>::iterator end =
        remove(running_.begin(), running_.end(), subproc);
    if (running_.end() != end) {
      finished_.push(subproc);
      running_.resize(end - running_.begin());
    }
  }

  return false;
}

void SubprocessSet::Clear() {
  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ++i) {
    // Since the foreground process is in our process group, it will receive a
    // CTRL_C_EVENT or CTRL_BREAK_EVENT at the same time as us.
    if ((*i)->child_ && !(*i)->use_console_) {
      if (!GenerateConsoleCtrlEvent(CTRL_BREAK_EVENT,
                                    GetProcessId((*i)->child_))) {
        Win32Fatal("GenerateConsoleCtrlEvent");
      }
    }
  }
  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ++i)
    delete *i;
  running_.clear();
}

*/
}

#[cfg(unix)]
mod imp {
/*
// Copyright 2012 Google Inc. All Rights Reserved.
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

#include "subprocess.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <unistd.h>
#include <stdio.h>
#include <string.h>
#include <sys/wait.h>
#include <spawn.h>

extern char** environ;

#include "util.h"

Subprocess::Subprocess(bool use_console) : fd_(-1), pid_(-1),
                                           use_console_(use_console) {
}

Subprocess::~Subprocess() {
  if (fd_ >= 0)
    close(fd_);
  // Reap child if forgotten.
  if (pid_ != -1)
    Finish();
}

bool Subprocess::Start(SubprocessSet* set, const string& command) {
  int output_pipe[2];
  if (pipe(output_pipe) < 0)
    Fatal("pipe: %s", strerror(errno));
  fd_ = output_pipe[0];
#if !defined(USE_PPOLL)
  // If available, we use ppoll in DoWork(); otherwise we use pselect
  // and so must avoid overly-large FDs.
  if (fd_ >= static_cast<int>(FD_SETSIZE))
    Fatal("pipe: %s", strerror(EMFILE));
#endif  // !USE_PPOLL
  SetCloseOnExec(fd_);

  posix_spawn_file_actions_t action;
  if (posix_spawn_file_actions_init(&action) != 0)
    Fatal("posix_spawn_file_actions_init: %s", strerror(errno));

  if (posix_spawn_file_actions_addclose(&action, output_pipe[0]) != 0)
    Fatal("posix_spawn_file_actions_addclose: %s", strerror(errno));

  posix_spawnattr_t attr;
  if (posix_spawnattr_init(&attr) != 0)
    Fatal("posix_spawnattr_init: %s", strerror(errno));

  short flags = 0;

  flags |= POSIX_SPAWN_SETSIGMASK;
  if (posix_spawnattr_setsigmask(&attr, &set->old_mask_) != 0)
    Fatal("posix_spawnattr_setsigmask: %s", strerror(errno));
  // Signals which are set to be caught in the calling process image are set to
  // default action in the new process image, so no explicit
  // POSIX_SPAWN_SETSIGDEF parameter is needed.

  if (!use_console_) {
    // Put the child in its own process group, so ctrl-c won't reach it.
    flags |= POSIX_SPAWN_SETPGROUP;
    // No need to posix_spawnattr_setpgroup(&attr, 0), it's the default.

    // Open /dev/null over stdin.
    if (posix_spawn_file_actions_addopen(&action, 0, "/dev/null", O_RDONLY,
                                         0) != 0) {
      Fatal("posix_spawn_file_actions_addopen: %s", strerror(errno));
    }

    if (posix_spawn_file_actions_adddup2(&action, output_pipe[1], 1) != 0)
      Fatal("posix_spawn_file_actions_adddup2: %s", strerror(errno));
    if (posix_spawn_file_actions_adddup2(&action, output_pipe[1], 2) != 0)
      Fatal("posix_spawn_file_actions_adddup2: %s", strerror(errno));
    if (posix_spawn_file_actions_addclose(&action, output_pipe[1]) != 0)
      Fatal("posix_spawn_file_actions_addclose: %s", strerror(errno));
    // In the console case, output_pipe is still inherited by the child and
    // closed when the subprocess finishes, which then notifies ninja.
  }
#ifdef POSIX_SPAWN_USEVFORK
  flags |= POSIX_SPAWN_USEVFORK;
#endif

  if (posix_spawnattr_setflags(&attr, flags) != 0)
    Fatal("posix_spawnattr_setflags: %s", strerror(errno));

  const char* spawned_args[] = { "/bin/sh", "-c", command.c_str(), NULL };
  if (posix_spawn(&pid_, "/bin/sh", &action, &attr,
                  const_cast<char**>(spawned_args), environ) != 0)
    Fatal("posix_spawn: %s", strerror(errno));

  if (posix_spawnattr_destroy(&attr) != 0)
    Fatal("posix_spawnattr_destroy: %s", strerror(errno));
  if (posix_spawn_file_actions_destroy(&action) != 0)
    Fatal("posix_spawn_file_actions_destroy: %s", strerror(errno));

  close(output_pipe[1]);
  return true;
}

void Subprocess::OnPipeReady() {
  char buf[4 << 10];
  ssize_t len = read(fd_, buf, sizeof(buf));
  if (len > 0) {
    buf_.append(buf, len);
  } else {
    if (len < 0)
      Fatal("read: %s", strerror(errno));
    close(fd_);
    fd_ = -1;
  }
}

ExitStatus Subprocess::Finish() {
  assert(pid_ != -1);
  int status;
  if (waitpid(pid_, &status, 0) < 0)
    Fatal("waitpid(%d): %s", pid_, strerror(errno));
  pid_ = -1;

  if (WIFEXITED(status)) {
    int exit = WEXITSTATUS(status);
    if (exit == 0)
      return ExitSuccess;
  } else if (WIFSIGNALED(status)) {
    if (WTERMSIG(status) == SIGINT || WTERMSIG(status) == SIGTERM
        || WTERMSIG(status) == SIGHUP)
      return ExitInterrupted;
  }
  return ExitFailure;
}

bool Subprocess::Done() const {
  return fd_ == -1;
}

const string& Subprocess::GetOutput() const {
  return buf_;
}

int SubprocessSet::interrupted_;

void SubprocessSet::SetInterruptedFlag(int signum) {
  interrupted_ = signum;
}

void SubprocessSet::HandlePendingInterruption() {
  sigset_t pending;
  sigemptyset(&pending);
  if (sigpending(&pending) == -1) {
    perror("ninja: sigpending");
    return;
  }
  if (sigismember(&pending, SIGINT))
    interrupted_ = SIGINT;
  else if (sigismember(&pending, SIGTERM))
    interrupted_ = SIGTERM;
  else if (sigismember(&pending, SIGHUP))
    interrupted_ = SIGHUP;
}

SubprocessSet::SubprocessSet() {
  sigset_t set;
  sigemptyset(&set);
  sigaddset(&set, SIGINT);
  sigaddset(&set, SIGTERM);
  sigaddset(&set, SIGHUP);
  if (sigprocmask(SIG_BLOCK, &set, &old_mask_) < 0)
    Fatal("sigprocmask: %s", strerror(errno));

  struct sigaction act;
  memset(&act, 0, sizeof(act));
  act.sa_handler = SetInterruptedFlag;
  if (sigaction(SIGINT, &act, &old_int_act_) < 0)
    Fatal("sigaction: %s", strerror(errno));
  if (sigaction(SIGTERM, &act, &old_term_act_) < 0)
    Fatal("sigaction: %s", strerror(errno));
  if (sigaction(SIGHUP, &act, &old_hup_act_) < 0)
    Fatal("sigaction: %s", strerror(errno));
}

SubprocessSet::~SubprocessSet() {
  Clear();

  if (sigaction(SIGINT, &old_int_act_, 0) < 0)
    Fatal("sigaction: %s", strerror(errno));
  if (sigaction(SIGTERM, &old_term_act_, 0) < 0)
    Fatal("sigaction: %s", strerror(errno));
  if (sigaction(SIGHUP, &old_hup_act_, 0) < 0)
    Fatal("sigaction: %s", strerror(errno));
  if (sigprocmask(SIG_SETMASK, &old_mask_, 0) < 0)
    Fatal("sigprocmask: %s", strerror(errno));
}

Subprocess *SubprocessSet::Add(const string& command, bool use_console) {
  Subprocess *subprocess = new Subprocess(use_console);
  if (!subprocess->Start(this, command)) {
    delete subprocess;
    return 0;
  }
  running_.push_back(subprocess);
  return subprocess;
}

#ifdef USE_PPOLL
bool SubprocessSet::DoWork() {
  vector<pollfd> fds;
  nfds_t nfds = 0;

  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ++i) {
    int fd = (*i)->fd_;
    if (fd < 0)
      continue;
    pollfd pfd = { fd, POLLIN | POLLPRI, 0 };
    fds.push_back(pfd);
    ++nfds;
  }

  interrupted_ = 0;
  int ret = ppoll(&fds.front(), nfds, NULL, &old_mask_);
  if (ret == -1) {
    if (errno != EINTR) {
      perror("ninja: ppoll");
      return false;
    }
    return IsInterrupted();
  }

  HandlePendingInterruption();
  if (IsInterrupted())
    return true;

  nfds_t cur_nfd = 0;
  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ) {
    int fd = (*i)->fd_;
    if (fd < 0)
      continue;
    assert(fd == fds[cur_nfd].fd);
    if (fds[cur_nfd++].revents) {
      (*i)->OnPipeReady();
      if ((*i)->Done()) {
        finished_.push(*i);
        i = running_.erase(i);
        continue;
      }
    }
    ++i;
  }

  return IsInterrupted();
}

#else  // !defined(USE_PPOLL)
bool SubprocessSet::DoWork() {
  fd_set set;
  int nfds = 0;
  FD_ZERO(&set);

  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ++i) {
    int fd = (*i)->fd_;
    if (fd >= 0) {
      FD_SET(fd, &set);
      if (nfds < fd+1)
        nfds = fd+1;
    }
  }

  interrupted_ = 0;
  int ret = pselect(nfds, &set, 0, 0, 0, &old_mask_);
  if (ret == -1) {
    if (errno != EINTR) {
      perror("ninja: pselect");
      return false;
    }
    return IsInterrupted();
  }

  HandlePendingInterruption();
  if (IsInterrupted())
    return true;

  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ) {
    int fd = (*i)->fd_;
    if (fd >= 0 && FD_ISSET(fd, &set)) {
      (*i)->OnPipeReady();
      if ((*i)->Done()) {
        finished_.push(*i);
        i = running_.erase(i);
        continue;
      }
    }
    ++i;
  }

  return IsInterrupted();
}
#endif  // !defined(USE_PPOLL)

Subprocess* SubprocessSet::NextFinished() {
  if (finished_.empty())
    return NULL;
  Subprocess* subproc = finished_.front();
  finished_.pop();
  return subproc;
}

void SubprocessSet::Clear() {
  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ++i)
    // Since the foreground process is in our process group, it will receive
    // the interruption signal (i.e. SIGINT or SIGTERM) at the same time as us.
    if (!(*i)->use_console_)
      kill(-(*i)->pid_, interrupted_);
  for (vector<Subprocess*>::iterator i = running_.begin();
       i != running_.end(); ++i)
    delete *i;
  running_.clear();
}

*/
}

/*

// Copyright 2012 Google Inc. All Rights Reserved.
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

#include "subprocess.h"

#include "test.h"

#ifndef _WIN32
// SetWithLots need setrlimit.
#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <unistd.h>
#endif

namespace {

#ifdef _WIN32
const char* kSimpleCommand = "cmd /c dir \\";
#else
const char* kSimpleCommand = "ls /";
#endif

struct SubprocessTest : public testing::Test {
  SubprocessSet subprocs_;
};

}  // anonymous namespace

// Run a command that fails and emits to stderr.
TEST_F(SubprocessTest, BadCommandStderr) {
  Subprocess* subproc = subprocs_.Add("cmd /c ninja_no_such_command");
  ASSERT_NE((Subprocess *) 0, subproc);

  while (!subproc->Done()) {
    // Pretend we discovered that stderr was ready for writing.
    subprocs_.DoWork();
  }

  EXPECT_EQ(ExitFailure, subproc->Finish());
  EXPECT_NE("", subproc->GetOutput());
}

// Run a command that does not exist
TEST_F(SubprocessTest, NoSuchCommand) {
  Subprocess* subproc = subprocs_.Add("ninja_no_such_command");
  ASSERT_NE((Subprocess *) 0, subproc);

  while (!subproc->Done()) {
    // Pretend we discovered that stderr was ready for writing.
    subprocs_.DoWork();
  }

  EXPECT_EQ(ExitFailure, subproc->Finish());
  EXPECT_NE("", subproc->GetOutput());
#ifdef _WIN32
  ASSERT_EQ("CreateProcess failed: The system cannot find the file "
            "specified.\n", subproc->GetOutput());
#endif
}

#ifndef _WIN32

TEST_F(SubprocessTest, InterruptChild) {
  Subprocess* subproc = subprocs_.Add("kill -INT $$");
  ASSERT_NE((Subprocess *) 0, subproc);

  while (!subproc->Done()) {
    subprocs_.DoWork();
  }

  EXPECT_EQ(ExitInterrupted, subproc->Finish());
}

TEST_F(SubprocessTest, InterruptParent) {
  Subprocess* subproc = subprocs_.Add("kill -INT $PPID ; sleep 1");
  ASSERT_NE((Subprocess *) 0, subproc);

  while (!subproc->Done()) {
    bool interrupted = subprocs_.DoWork();
    if (interrupted)
      return;
  }

  ASSERT_FALSE("We should have been interrupted");
}

TEST_F(SubprocessTest, InterruptChildWithSigTerm) {
  Subprocess* subproc = subprocs_.Add("kill -TERM $$");
  ASSERT_NE((Subprocess *) 0, subproc);

  while (!subproc->Done()) {
    subprocs_.DoWork();
  }

  EXPECT_EQ(ExitInterrupted, subproc->Finish());
}

TEST_F(SubprocessTest, InterruptParentWithSigTerm) {
  Subprocess* subproc = subprocs_.Add("kill -TERM $PPID ; sleep 1");
  ASSERT_NE((Subprocess *) 0, subproc);

  while (!subproc->Done()) {
    bool interrupted = subprocs_.DoWork();
    if (interrupted)
      return;
  }

  ASSERT_FALSE("We should have been interrupted");
}

TEST_F(SubprocessTest, InterruptChildWithSigHup) {
  Subprocess* subproc = subprocs_.Add("kill -HUP $$");
  ASSERT_NE((Subprocess *) 0, subproc);

  while (!subproc->Done()) {
    subprocs_.DoWork();
  }

  EXPECT_EQ(ExitInterrupted, subproc->Finish());
}

TEST_F(SubprocessTest, InterruptParentWithSigHup) {
  Subprocess* subproc = subprocs_.Add("kill -HUP $PPID ; sleep 1");
  ASSERT_NE((Subprocess *) 0, subproc);

  while (!subproc->Done()) {
    bool interrupted = subprocs_.DoWork();
    if (interrupted)
      return;
  }

  ASSERT_FALSE("We should have been interrupted");
}

TEST_F(SubprocessTest, Console) {
  // Skip test if we don't have the console ourselves.
  if (isatty(0) && isatty(1) && isatty(2)) {
    Subprocess* subproc =
        subprocs_.Add("test -t 0 -a -t 1 -a -t 2", /*use_console=*/true);
    ASSERT_NE((Subprocess*)0, subproc);

    while (!subproc->Done()) {
      subprocs_.DoWork();
    }

    EXPECT_EQ(ExitSuccess, subproc->Finish());
  }
}

#endif

TEST_F(SubprocessTest, SetWithSingle) {
  Subprocess* subproc = subprocs_.Add(kSimpleCommand);
  ASSERT_NE((Subprocess *) 0, subproc);

  while (!subproc->Done()) {
    subprocs_.DoWork();
  }
  ASSERT_EQ(ExitSuccess, subproc->Finish());
  ASSERT_NE("", subproc->GetOutput());

  ASSERT_EQ(1u, subprocs_.finished_.size());
}

TEST_F(SubprocessTest, SetWithMulti) {
  Subprocess* processes[3];
  const char* kCommands[3] = {
    kSimpleCommand,
#ifdef _WIN32
    "cmd /c echo hi",
    "cmd /c time /t",
#else
    "whoami",
    "pwd",
#endif
  };

  for (int i = 0; i < 3; ++i) {
    processes[i] = subprocs_.Add(kCommands[i]);
    ASSERT_NE((Subprocess *) 0, processes[i]);
  }

  ASSERT_EQ(3u, subprocs_.running_.size());
  for (int i = 0; i < 3; ++i) {
    ASSERT_FALSE(processes[i]->Done());
    ASSERT_EQ("", processes[i]->GetOutput());
  }

  while (!processes[0]->Done() || !processes[1]->Done() ||
         !processes[2]->Done()) {
    ASSERT_GT(subprocs_.running_.size(), 0u);
    subprocs_.DoWork();
  }

  ASSERT_EQ(0u, subprocs_.running_.size());
  ASSERT_EQ(3u, subprocs_.finished_.size());

  for (int i = 0; i < 3; ++i) {
    ASSERT_EQ(ExitSuccess, processes[i]->Finish());
    ASSERT_NE("", processes[i]->GetOutput());
    delete processes[i];
  }
}

#if defined(USE_PPOLL)
TEST_F(SubprocessTest, SetWithLots) {
  // Arbitrary big number; needs to be over 1024 to confirm we're no longer
  // hostage to pselect.
  const unsigned kNumProcs = 1025;

  // Make sure [ulimit -n] isn't going to stop us from working.
  rlimit rlim;
  ASSERT_EQ(0, getrlimit(RLIMIT_NOFILE, &rlim));
  if (rlim.rlim_cur < kNumProcs) {
    printf("Raise [ulimit -n] above %u (currently %lu) to make this test go\n",
           kNumProcs, rlim.rlim_cur);
    return;
  }

  vector<Subprocess*> procs;
  for (size_t i = 0; i < kNumProcs; ++i) {
    Subprocess* subproc = subprocs_.Add("/bin/echo");
    ASSERT_NE((Subprocess *) 0, subproc);
    procs.push_back(subproc);
  }
  while (!subprocs_.running_.empty())
    subprocs_.DoWork();
  for (size_t i = 0; i < procs.size(); ++i) {
    ASSERT_EQ(ExitSuccess, procs[i]->Finish());
    ASSERT_NE("", procs[i]->GetOutput());
  }
  ASSERT_EQ(kNumProcs, subprocs_.finished_.size());
}
#endif  // !__APPLE__ && !_WIN32

// TODO: this test could work on Windows, just not sure how to simply
// read stdin.
#ifndef _WIN32
// Verify that a command that attempts to read stdin correctly thinks
// that stdin is closed.
TEST_F(SubprocessTest, ReadStdin) {
  Subprocess* subproc = subprocs_.Add("cat -");
  while (!subproc->Done()) {
    subprocs_.DoWork();
  }
  ASSERT_EQ(ExitSuccess, subproc->Finish());
  ASSERT_EQ(1u, subprocs_.finished_.size());
}
#endif  // _WIN32

*/