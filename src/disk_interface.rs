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
use std::fs::{self};
use std::io::{self, Read, ErrorKind};

use super::timestamp::TimeStamp;

/// Result of ReadFile.
pub enum FileReaderError {
    NotFound(String),
    OtherError(String),
}

/// Interface for reading files from disk.  See DiskInterface for details.
/// This base offers the minimum interface needed just to read files.
pub trait FileReader {
    /// Read and store in given string.  On success, return Okay.
    /// On error, return another Status and fill |err|.
    fn read_file(&self, path: &Path, contents: &mut Vec<u8>) -> Result<(), FileReaderError>;
}

/// Interface for accessing the disk.
///
/// Abstract so it can be mocked out for tests.  The real implementation
/// is RealDiskInterface.
pub trait DiskInterface: FileReader {
    /// Create a directory, returning false on failure.
    fn make_dir(&self, path: &Path) -> Result<(), io::Error>;

    /// Create all the parent directories for path; like mkdir -p
    /// `basename path`.
    fn make_dirs(&self, path: &Path) -> Result<(), io::Error>;

    /// stat() a file, returning the mtime, or 0 if missing and -1 on
    /// other errors.
    fn stat(&self, path: &Path) -> Result<TimeStamp, String>;
}

/*

struct DiskInterface: public FileReader {



  /// Create a file, with the specified name and contents
  /// Returns true on success, false on failure
  virtual bool WriteFile(const string& path, const string& contents) = 0;

  /// Remove the file named @a path. It behaves like 'rm -f path' so no errors
  /// are reported if it does not exists.
  /// @returns 0 if the file has been removed,
  ///          1 if the file does not exist, and
  ///          -1 if an error occurs.
  virtual int RemoveFile(const string& path) = 0;


};

*/

pub struct RealDiskInterface {}


/*


/// Implementation of DiskInterface that actually hits the disk.
struct RealDiskInterface : public DiskInterface {
  RealDiskInterface()
#ifdef _WIN32
                      : use_cache_(false)
#endif
                      {}
  virtual ~RealDiskInterface() {}
  virtual TimeStamp Stat(const string& path, string* err) const;
  virtual bool MakeDir(const string& path);
  virtual bool WriteFile(const string& path, const string& contents);
  virtual Status ReadFile(const string& path, string* contents, string* err);
  virtual int RemoveFile(const string& path);



 private:
#ifdef _WIN32
  /// Whether stat information can be cached.
  bool use_cache_;

  typedef map<string, TimeStamp> DirCache;
  // TODO: Neither a map nor a hashmap seems ideal here.  If the statcache
  // works out, come up with a better data structure.
  typedef map<string, DirCache> Cache;
  mutable Cache cache_;
#endif
};

#endif  // NINJA_DISK_INTERFACE_H_
*/

impl FileReader for RealDiskInterface {
    fn read_file(&self, path: &Path, contents: &mut Vec<u8>) -> Result<(), FileReaderError> {
        let mut file = fs::File::open(path).map_err(|err| {
            let c = if err.kind() == ErrorKind::NotFound {
                FileReaderError::NotFound
            } else {
                FileReaderError::OtherError
            };
            c(format!("{}", err))
        })?;

        file.read_to_end(contents).map_err(|err| {
            FileReaderError::OtherError(format!("{}", err))
        })?;

        Ok(())
    }
}

impl DiskInterface for RealDiskInterface {
    fn make_dir(&self, path: &Path) -> Result<(), io::Error> {
        fs::DirBuilder::new()
            .recursive(false)
            .create(path)?;
        Ok(())
    }

    fn make_dirs(&self, path: &Path) -> Result<(), io::Error> {
        fs::DirBuilder::new()
            .recursive(true)
            .create(path)?;
        Ok(())
    }

    fn stat(&self, path: &Path) -> Result<TimeStamp, String> {
        unimplemented!()
    }
}

impl RealDiskInterface {
    /// Whether stat information can be cached.  Only has an effect on Windows.
    pub fn allow_stat_cache(&self, allow: bool) {
        return;
        unimplemented!()
    }
}
