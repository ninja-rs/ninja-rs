// Copyright 2013 Google Inc. All Rights Reserved.
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

use std::cell::{Cell, RefCell};

#[derive(Clone, Copy, PartialEq)]
pub enum LinePrinterLineType {
    Full,
    Elide,
}

#[cfg(not(windows))]
struct LinePrinterOs {}

#[cfg(not(windows))]
impl LinePrinterOs {
    fn new() -> Self {
        LinePrinterOs {}
    }

    fn should_be_smart(&self) -> bool {
        use libc;
        use std::env;
        use std::ffi;

        if unsafe { libc::isatty(1usize as _) } != 0 {
            return false;
        }

        if let Some(term) = env::var_os("TERM") {
            if term != ffi::OsString::from("dumb") {
                return true;
            }
        }
        return false;
    }
}

#[cfg(windows)]
struct LinePrinterOs {
    console: ::winapi::HANDLE,
}

#[cfg(windows)]
impl LinePrinterOs {
    fn new() -> Self {
        use kernel32;
        use winapi;
        LinePrinterOs { console: unsafe { kernel32::GetStdHandle(winapi::STD_OUTPUT_HANDLE) } }
    }

    fn should_be_smart(&self) -> bool {
        use kernel32;
        use winapi;
        use std::mem;

        let mut csbi = unsafe { mem::zeroed::<winapi::CONSOLE_SCREEN_BUFFER_INFO>() };
        unsafe {
            kernel32::GetConsoleScreenBufferInfo(self.console, &mut csbi as *mut _) != winapi::FALSE
        }
    }
}



/// Prints lines of text, possibly overprinting previously printed lines
/// if the terminal supports it.
pub struct LinePrinter {
    /// Whether we can do fancy terminal control codes.
    smart_terminal: bool,

    /// Whether the caret is at the beginning of a blank line.
    have_blank_line: Cell<bool>,

    /// Whether console is locked.
    console_locked: bool,

    /// Buffered current line while console is locked.
    line_buffer: RefCell<Vec<u8>>,

    /// Buffered line type while console is locked.
    line_type: Cell<LinePrinterLineType>,

    /// Buffered console output while console is locked.
    output_buffer: RefCell<Vec<u8>>,

    extra: LinePrinterOs,
}

impl LinePrinter {
    pub fn new() -> Self {
        let lp_os = LinePrinterOs::new();
        let smart = lp_os.should_be_smart();

        LinePrinter {
            smart_terminal: smart,
            have_blank_line: Cell::new(true),
            console_locked: false,
            line_buffer: RefCell::new(Vec::new()),
            line_type: Cell::new(LinePrinterLineType::Full),
            output_buffer: RefCell::new(Vec::new()),
            extra: lp_os,
        }
    }

    pub fn is_smart_terminal(&self) -> bool {
        self.smart_terminal
    }
    pub fn set_smart_terminal(&mut self, smart: bool) {
        self.smart_terminal = smart;
    }

    /// Overprints the current line. If type is ELIDE, elides to_print to fit on
    /// one line.
    pub fn print(&self, to_print: &[u8], line_type: LinePrinterLineType) {
        if self.console_locked {
            *self.line_buffer.borrow_mut() = to_print.to_owned();
            self.line_type.set(line_type);
            return;
        }

        if self.smart_terminal {
            print!("\r"); // Print over previous line, if any.
            // On Windows, calling a C library function writing to stdout also handles
            // pausing the executable when the "Pause" key or Ctrl-S is pressed.
        }

        if self.smart_terminal && line_type == LinePrinterLineType::Elide {
            /*
#ifdef _WIN32
    CONSOLE_SCREEN_BUFFER_INFO csbi;
    GetConsoleScreenBufferInfo(console_, &csbi);

    to_print = ElideMiddle(to_print, static_cast<size_t>(csbi.dwSize.X));
    // We don't want to have the cursor spamming back and forth, so instead of
    // printf use WriteConsoleOutput which updates the contents of the buffer,
    // but doesn't move the cursor position.
    COORD buf_size = { csbi.dwSize.X, 1 };
    COORD zero_zero = { 0, 0 };
    SMALL_RECT target = {
      csbi.dwCursorPosition.X, csbi.dwCursorPosition.Y,
      static_cast<SHORT>(csbi.dwCursorPosition.X + csbi.dwSize.X - 1),
      csbi.dwCursorPosition.Y
    };
    vector<CHAR_INFO> char_data(csbi.dwSize.X);
    for (size_t i = 0; i < static_cast<size_t>(csbi.dwSize.X); ++i) {
      char_data[i].Char.AsciiChar = i < to_print.size() ? to_print[i] : ' ';
      char_data[i].Attributes = csbi.wAttributes;
    }
    WriteConsoleOutput(console_, &char_data[0], buf_size, zero_zero, &target);
#else
    // Limit output to width of the terminal if provided so we don't cause
    // line-wrapping.
    winsize size;
    if ((ioctl(0, TIOCGWINSZ, &size) == 0) && size.ws_col) {
      to_print = ElideMiddle(to_print, size.ws_col);
    }
    printf("%s", to_print.c_str());
    printf("\x1B[K");  // Clear to end of line.
    fflush(stdout);
#endif

    have_blank_line_ = false;
*/
            self.have_blank_line.set(false);

            return;
            unimplemented!();
        } else {
            use std::io::{self, Write};

            let stdout = io::stdout();
            let mut handle = stdout.lock();

            let _ = handle.write(to_print);
            let _ = handle.write(b"\n");
        }
    }

    /// Print the given data to the console, or buffer it if it is locked.
    fn print_or_buffer(&self, to_print: &[u8]) {
        if self.console_locked {
            self.output_buffer.borrow_mut().extend_from_slice(to_print);
        } else {
            use std::io::{self, Write};

            let stdout = io::stdout();
            let mut handle = stdout.lock();

            let _ = handle.write(to_print);
        }
    }

    /// Prints a string on a new line, not overprinting previous output.
    pub fn print_on_new_line(&self, to_print: &[u8]) {
        if self.console_locked && !self.line_buffer.borrow().is_empty() {
            let mut line_buffer = self.line_buffer.borrow_mut();
            let mut output_buffer = self.output_buffer.borrow_mut();
            output_buffer.extend(line_buffer.drain(..));
            output_buffer.push(b'\n');
        }

        if !self.have_blank_line.get() {
            self.print_or_buffer(b"\n");
        }
        if !to_print.is_empty() {
            self.print_or_buffer(to_print);
        }
        self.have_blank_line.set(match to_print.last() {
            None | Some(&b'\n') => true,
            _ => false,
        });
    }

    /// Lock or unlock the console.  Any output sent to the LinePrinter while the
    /// console is locked will not be printed until it is unlocked.
    pub fn set_console_locked(&mut self, locked: bool) {
        use std::mem;

        if self.console_locked == locked {
            return;
        }

        if locked {
            self.print_on_new_line(b"");
        }

        self.console_locked = locked;

        if !locked {
            let mut output_buffer = Vec::new();
            let mut line_buffer = Vec::new();
            mem::swap(&mut output_buffer, &mut *self.output_buffer.borrow_mut());
            mem::swap(&mut line_buffer, &mut *self.line_buffer.borrow_mut());
            self.print_on_new_line(&output_buffer);
            if !line_buffer.is_empty() {
                self.print(&line_buffer, self.line_type.get());
            }
        }
        return;
    }
}

/*

struct LinePrinter {
  LinePrinter();

  bool is_smart_terminal() const { return smart_terminal_; }
  void set_smart_terminal(bool smart) { smart_terminal_ = smart; }


  /// Overprints the current line. If type is ELIDE, elides to_print to fit on
  /// one line.
  void Print(string to_print, LineType type);

  /// Prints a string on a new line, not overprinting previous output.
  void PrintOnNewLine(const string& to_print);

  /// Lock or unlock the console.  Any output sent to the LinePrinter while the
  /// console is locked will not be printed until it is unlocked.
  void SetConsoleLocked(bool locked);

 private:
  /// Whether we can do fancy terminal control codes.
  bool smart_terminal_;

  /// Whether the caret is at the beginning of a blank line.
  bool have_blank_line_;

  /// Whether console is locked.
  bool console_locked_;

  /// Buffered current line while console is locked.
  string line_buffer_;

  /// Buffered line type while console is locked.
  LineType line_type_;

  /// Buffered console output while console is locked.
  string output_buffer_;

#ifdef _WIN32
  void* console_;
#endif

  /// Print the given data to the console, or buffer it if it is locked.
  void PrintOrBuffer(const char *data, size_t size);
};

#endif  // NINJA_LINE_PRINTER_H_

*/
