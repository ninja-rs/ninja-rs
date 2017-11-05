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

use std::path::{Path, PathBuf};
use std::collections::{HashMap, HashSet};
use std::cell::RefCell;
use std::io;

use super::disk_interface::{FileReader, FileReaderError, DiskInterface};
use super::manifest_parser::{ManifestParserOptions, ManifestParser};
use super::state::State;
use super::graph::{Node, NodeIndex};
use super::timestamp::TimeStamp;

// Support utilites for tests.

pub struct TestWithStateAndVFS<OtherData: Default> {
    pub state: RefCell<State>,
    pub fs: VirtualFileSystem,
    pub other: OtherData,
}

impl<OtherData: Default> TestWithStateAndVFS<OtherData> {
    pub fn new_minimal() -> Self {
        TestWithStateAndVFS {
            state: RefCell::new(State::new()),
            fs: VirtualFileSystem::new(),
            other: Default::default(),
        }
    }

    pub fn new_with_builtin_rule() -> Self {
        let mut test = Self::new_minimal();
        test.assert_parse(
            concat!("rule cat\n", "  command = cat $in > $out\n").as_bytes(),
        );
        test
    }

    pub fn assert_parse_with_options(
        &mut self,
        input: &[u8],
        options: ManifestParserOptions,
    ) -> () {
        let mut state = self.state.borrow_mut();
        {
            let mut parser = ManifestParser::new(&mut state, &self.fs, options);
            assert_eq!(Ok(()), parser.parse_test(input));
        }

        assert_eq!((), state.verify_graph());
    }

    pub fn assert_parse_with_options_error(
        &mut self,
        input: &[u8],
        options: ManifestParserOptions,
        err: &str,
    ) -> () {
        let mut state = self.state.borrow_mut();
        let mut parser = ManifestParser::new(&mut state, &self.fs, options);
        assert_eq!(Err(err.to_owned()), parser.parse_test(input));
    }


    pub fn assert_parse(&mut self, input: &[u8]) -> () {
        self.assert_parse_with_options(input, Default::default());
    }

    pub fn assert_parse_error(&mut self, input: &[u8], err: &str) -> () {
        self.assert_parse_with_options_error(input, Default::default(), err);
    }

    pub fn assert_node_idx(&self, path: &[u8]) -> NodeIndex {
        let state = self.state.borrow();
        state.node_state.lookup_node(path).unwrap()
    }

    pub fn assert_with_node_mut<F: FnMut(&mut Node)>(&mut self, path: &[u8], mut f: F) {
        let mut state = self.state.borrow_mut();
        let node_idx = state.node_state.lookup_node(path).unwrap();
        f(state.node_state.get_node_mut(node_idx));
    }
}

/*


struct Node;

/// A base test fixture that includes a State object with a
/// builtin "cat" rule.
struct StateTestWithBuiltinRules : public testing::Test {
  StateTestWithBuiltinRules();

  /// Add a "cat" rule to \a state.  Used by some tests; it's
  /// otherwise done by the ctor to state_.
  void AddCatRule(State* state);

  /// Short way to get a Node by its path from state_.
  Node* GetNode(const string& path);

  State state_;
};

void AssertParse(State* state, const char* input,
                 ManifestParserOptions = ManifestParserOptions());
void AssertHash(const char* expected, uint64_t actual);
void VerifyGraph(const State& state);
*/


/// An implementation of DiskInterface that uses an in-memory representation
/// of disk state.  It also logs file accesses and directory creations
/// so it can be used by tests to verify disk access patterns.
#[derive(Default)]
pub struct VirtualFileSystem {
    directories_made: Vec<PathBuf>,
    pub files_read: RefCell<Vec<PathBuf>>,
    files: HashMap<PathBuf, VirtualFileSystemEntry>,
    files_removed: HashSet<PathBuf>,
    files_created: HashSet<PathBuf>,
    /// A simple fake timestamp for file operations.
    now: isize,
}

/// An entry for a single in-memory file.
struct VirtualFileSystemEntry {
    mtime: isize,
    stat_error: String, // If mtime is -1.
    pub contents: Vec<u8>,
}

impl VirtualFileSystem {
    pub fn new() -> Self {
        let mut vfs: Self = Default::default();
        vfs.now = 1isize;
        vfs
    }

    /// Tick "time" forwards; subsequent file operations will be newer than
    /// previous ones.
    pub fn tick(&mut self) -> isize {
        self.now += 1;
        return self.now;
    }

    /// "Create" a file with contents.
    pub fn create(&mut self, path: &Path, contents: &[u8]) {
        self.files.insert(
            path.to_owned(),
            VirtualFileSystemEntry {
                mtime: self.now,
                stat_error: String::new(),
                contents: contents.to_owned(),
            },
        );

        self.files_created.insert(path.to_owned());
    }
}

impl FileReader for VirtualFileSystem {
    fn read_file(&self, path: &Path, contents: &mut Vec<u8>) -> Result<(), FileReaderError> {
        self.files_read.borrow_mut().push(path.to_owned());
        if let Some(file_contents) = self.files.get(path) {
            *contents = file_contents.contents.clone();
            Ok(())
        } else {
            Err(FileReaderError::NotFound(
                "No such file or directory".to_owned(),
            ))
        }
    }
}

impl DiskInterface for VirtualFileSystem {
    fn make_dir(&self, path: &Path) -> Result<(), io::Error> {
        unimplemented!{}
    }
    fn make_dirs(&self, path: &Path) -> Result<(), io::Error> {
        unimplemented!{}
    }
    fn stat(&self, path: &Path) -> Result<TimeStamp, String> {
        unimplemented!()
    }
    fn write_file(&self, path: &Path, contents: &[u8]) -> Result<(), ()> {
        unimplemented!()
    }
    fn remove_file(&self, path: &Path) -> Result<bool, io::Error> {
        unimplemented!()
    }
}


/*

struct VirtualFileSystem : public DiskInterface {


  // DiskInterface
  virtual TimeStamp Stat(const string& path, string* err) const;
  virtual bool WriteFile(const string& path, const string& contents);
  virtual bool MakeDir(const string& path);
  virtual Status ReadFile(const string& path, string* contents, string* err);
  virtual int RemoveFile(const string& path);

  /// An entry for a single in-memory file.
  struct Entry {
    int mtime;
    string stat_error;  // If mtime is -1.
    string contents;
  };

  vector<string> directories_made_;
  vector<string> files_read_;
  typedef map<string, Entry> FileMap;
  FileMap files_;
  set<string> files_removed_;
  set<string> files_created_;

};

struct ScopedTempDir {
  /// Create a temporary directory and chdir into it.
  void CreateAndEnter(const string& name);

  /// Clean up the temporary directory.
  void Cleanup();

  /// The temp directory containing our dir.
  string start_dir_;
  /// The subdirectory name for our dir, or empty if it hasn't been set up.
  string temp_dir_name_;
};

#endif // NINJA_TEST_H_

*/

/*

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

#ifdef _WIN32
#include <direct.h>  // Has to be before util.h is included.
#endif

#include "test.h"

#include <algorithm>

#include <errno.h>
#include <stdlib.h>
#ifdef _WIN32
#include <windows.h>
#else
#include <unistd.h>
#endif

#include "build_log.h"
#include "graph.h"
#include "manifest_parser.h"
#include "util.h"

namespace {

#ifdef _WIN32
#ifndef _mktemp_s
/// mingw has no mktemp.  Implement one with the same type as the one
/// found in the Windows API.
int _mktemp_s(char* templ) {
  char* ofs = strchr(templ, 'X');
  sprintf(ofs, "%d", rand() % 1000000);
  return 0;
}
#endif

/// Windows has no mkdtemp.  Implement it in terms of _mktemp_s.
char* mkdtemp(char* name_template) {
  int err = _mktemp_s(name_template);
  if (err < 0) {
    perror("_mktemp_s");
    return NULL;
  }

  err = _mkdir(name_template);
  if (err < 0) {
    perror("mkdir");
    return NULL;
  }

  return name_template;
}
#endif  // _WIN32

string GetSystemTempDir() {
#ifdef _WIN32
  char buf[1024];
  if (!GetTempPath(sizeof(buf), buf))
    return "";
  return buf;
#else
  const char* tempdir = getenv("TMPDIR");
  if (tempdir)
    return tempdir;
  return "/tmp";
#endif
}

}  // anonymous namespace

StateTestWithBuiltinRules::StateTestWithBuiltinRules() {
  AddCatRule(&state_);
}

void StateTestWithBuiltinRules::AddCatRule(State* state) {
  AssertParse(state,
"rule cat\n"
"  command = cat $in > $out\n");
}

Node* StateTestWithBuiltinRules::GetNode(const string& path) {
  EXPECT_FALSE(strpbrk(path.c_str(), "/\\"));
  return state_.GetNode(path, 0);
}

void AssertParse(State* state, const char* input,
                 ManifestParserOptions opts) {
  ManifestParser parser(state, NULL, opts);
  string err;
  EXPECT_TRUE(parser.ParseTest(input, &err));
  ASSERT_EQ("", err);
  VerifyGraph(*state);
}

void AssertHash(const char* expected, uint64_t actual) {
  ASSERT_EQ(BuildLog::LogEntry::HashCommand(expected), actual);
}

void VirtualFileSystem::Create(const string& path,
                               const string& contents) {
  files_[path].mtime = now_;
  files_[path].contents = contents;
  files_created_.insert(path);
}

TimeStamp VirtualFileSystem::Stat(const string& path, string* err) const {
  FileMap::const_iterator i = files_.find(path);
  if (i != files_.end()) {
    *err = i->second.stat_error;
    return i->second.mtime;
  }
  return 0;
}

bool VirtualFileSystem::WriteFile(const string& path, const string& contents) {
  Create(path, contents);
  return true;
}

bool VirtualFileSystem::MakeDir(const string& path) {
  directories_made_.push_back(path);
  return true;  // success
}

int VirtualFileSystem::RemoveFile(const string& path) {
  if (find(directories_made_.begin(), directories_made_.end(), path)
      != directories_made_.end())
    return -1;
  FileMap::iterator i = files_.find(path);
  if (i != files_.end()) {
    files_.erase(i);
    files_removed_.insert(path);
    return 0;
  } else {
    return 1;
  }
}

void ScopedTempDir::CreateAndEnter(const string& name) {
  // First change into the system temp dir and save it for cleanup.
  start_dir_ = GetSystemTempDir();
  if (start_dir_.empty())
    Fatal("couldn't get system temp dir");
  if (chdir(start_dir_.c_str()) < 0)
    Fatal("chdir: %s", strerror(errno));

  // Create a temporary subdirectory of that.
  char name_template[1024];
  strcpy(name_template, name.c_str());
  strcat(name_template, "-XXXXXX");
  char* tempname = mkdtemp(name_template);
  if (!tempname)
    Fatal("mkdtemp: %s", strerror(errno));
  temp_dir_name_ = tempname;

  // chdir into the new temporary directory.
  if (chdir(temp_dir_name_.c_str()) < 0)
    Fatal("chdir: %s", strerror(errno));
}

void ScopedTempDir::Cleanup() {
  if (temp_dir_name_.empty())
    return;  // Something went wrong earlier.

  // Move out of the directory we're about to clobber.
  if (chdir(start_dir_.c_str()) < 0)
    Fatal("chdir: %s", strerror(errno));

#ifdef _WIN32
  string command = "rmdir /s /q " + temp_dir_name_;
#else
  string command = "rm -rf " + temp_dir_name_;
#endif
  if (system(command.c_str()) < 0)
    Fatal("system: %s", strerror(errno));

  temp_dir_name_.clear();
}

*/
