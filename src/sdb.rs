//! Thread safe database. [`Sdb`] objects are safe to share between threads.
//! 
//! [`Sdb`]: struct.Sdb.html

// Copyright 2020 Magnus Aa. Hirth
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

use crate::{
    Source,
};

/// Safe db. Thread safe implementation of db.
pub struct Sdb {
    pagf: Box<dyn Source>,

    // .dir file is accessed by single bits. A bit value of 1 indicates that
    // a specific block is already used.
    dirf: Box<dyn Source>,

}

impl Sdb {
    pub fn open(name: &str) -> Result<Self> {
        let path: &Path = name.as_ref();
        let pagsrc = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .read(true)
            .open(path.with_extension(".pag"))?;
        let dirsrc = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .read(true)
            .open(path.with_extension(".dir"))?;
        Sdb::with_sources(Box::new(pagsrc), Box::new(dirsrc))
    }

    pub fn with_sources(pagsrc: Box<dyn Source>, dirsrc: Box<dyn Source>) -> Result<Self> {
        use io::SeekFrom::End;
        let mut db = Sdb {
            pagf: pagsrc,
            dirf: dirsrc,
            maxbno: 0,
        };
        db.maxbno = db.dirf.seek(End(0))?;
        Ok(db)
    }

}