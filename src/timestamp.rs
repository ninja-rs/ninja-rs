// Copyright 2011 Google Inc. All Rights Reserved.
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

use std::fmt::{Display, Formatter, Error};

#[derive(Clone, Copy, PartialEq, PartialOrd, Default)]
pub struct TimeStamp(pub isize);

impl TimeStamp {
    fn none() -> Self {
        TimeStamp(0)
    }

    fn invalid() -> Self {
        TimeStamp(-1)
    }
}

impl Display for TimeStamp {
    fn fmt(&self, formatter: &mut Formatter) -> Result<(), Error> {
        <isize as Display>::fmt(&self.0, formatter)
    }
}
