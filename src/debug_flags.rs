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

use std::sync::Mutex;
use super::metrics::Metrics;

pub static EXPLAINING: bool = false;

pub static KEEP_DEPFILE: bool = false;

pub static KEEP_RSP: bool = false;

pub static EXPERIMENTAL_STATCACHE: bool = true;

pub static METRICS: Option<Mutex<Metrics>> = None;

// explain!{} moved to utils.rs
