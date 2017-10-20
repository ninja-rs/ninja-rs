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

use std::path::Path;

use super::disk_interface::{FileReader, FileReaderError, DiskInterface};

// Support utilites for tests.









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
pub struct VirtualFileSystem {
    /// A simple fake timestamp for file operations.
    now: isize,
}

impl VirtualFileSystem {
    pub fn new() -> Self {
        VirtualFileSystem {
            now: 1
        }
    }

    /// Tick "time" forwards; subsequent file operations will be newer than
    /// previous ones.
    pub fn tick(&mut self) -> isize {
        self.now += 1;
        return self.now;
    }
}

impl FileReader for VirtualFileSystem {
    fn read_file(&self, path: &Path, contents: &mut [u8]) -> Result<(), FileReaderError> {
        unimplemented!()
    }
}

impl DiskInterface for VirtualFileSystem {

}


/*

struct VirtualFileSystem : public DiskInterface {

  /// "Create" a file with contents.
  void Create(const string& path, const string& contents);

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

FileReader::Status VirtualFileSystem::ReadFile(const string& path,
                                               string* contents,
                                               string* err) {
  files_read_.push_back(path);
  FileMap::iterator i = files_.find(path);
  if (i != files_.end()) {
    *contents = i->second.contents;
    return Okay;
  }
  *err = strerror(ENOENT);
  return NotFound;
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