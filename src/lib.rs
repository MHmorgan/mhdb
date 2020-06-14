//! [MHdb](https://mhmorgan.github.io/mhdb/) is a pure Rust key-value store
//! database, based on [dbm](https://en.wikipedia.org/wiki/DBM_(computing)).
//! 
//! # Simple use
//! 
//! ```no_run
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use mhdb::{Db, prelude::*};
//! 
//! let mut db = Db::open("mydb")?;
//! db.store(42u8, "Hello world")?;
//! let txt: Option<String> = db.fetch(42u8)?;
//! assert!(txt.is_some());
//! println!("{}", txt.unwrap());
//! # Ok(())
//! # }
//! ```
//! 
//! Any type which implement [`Datum`] can be stored in the
//! database. Most primitive types implement [`Datum`].
//! 
//! # In-memory database
//! 
//! Any type which implements the [`Source`] trait can be used
//! as database sources. This trait is in turn automatically
//! implemented for any type which implements the [`Read`],
//! [`Write`], and [`Seek`] standard library traits.
//! 
//! ```
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use mhdb::{Db, prelude::*};
//! use std::io::Cursor;
//!
//! let dirf = Cursor::new(Vec::<u8>::new());
//! let pagf = Cursor::new(Vec::<u8>::new());
//! let mut db: Db = Db::with_sources(Box::new(pagf), Box::new(dirf))?;
//! 
//! db.store(42u8, "Hello world")?;
//! let txt: Option<String> = db.fetch(42u8)?;
//! assert!(txt.is_some());
//! println!("{}", txt.unwrap());
//! # Ok(())
//! # }
//! ```
//! 
//! # Serde with custom types
//! 
//! [Serde] makes it easier to serialize and deserialize custom
//! data types.
//! 
//! ```
//! extern crate serde;
//! extern crate bincode;
//! 
//! use mhdb::{Db, prelude::*};
//! use serde::{Serialize,Deserialize};
//! use std::io::Cursor;
//! 
//! #[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
//! struct Point(i32, i32);
//! 
//! fn main() -> Result<(), Box<dyn std::error::Error>> {
//!     let dirf = Cursor::new(Vec::<u8>::new());
//!     let pagf = Cursor::new(Vec::<u8>::new());
//!     let mut db: Db = Db::with_sources(Box::new(pagf), Box::new(dirf))?;
//! 
//!     let p = Point(-4, 8);
//!     let val: Vec<u8> = bincode::serialize(&p)?;
//!     db.store("point", val)?;
//! 
//!     let val: Vec<u8> = db.fetch("point")?.unwrap();
//!     let p0: Point = bincode::deserialize(&val)?;
//!     assert_eq!(p, p0);
//!     Ok(())
//! }
//! ```
//! 
//! # Limitations
//! 
//! * Key-value pairs can not be larger than 506MB
//! * Not thread safe
//! 
//! [`Db`]: struct.Db.html
//! [`Source`]: traits.Source.html
//! [`Datum`]: traits.Datum.html
//! [`Read`]: https://doc.rust-lang.org/std/io/trait.Read.html
//! [`Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
//! [`Seek`]: https://doc.rust-lang.org/std/io/trait.Seek.html
//! [Serde]: https://serde.rs/

// pag file contains blocks of PBLKSIZ size
//
//  0   2   4   6                         480     500     512
//  +---+---+---+--------------------------+-------+-------+
//  | 2 |500|480|           ...            | item2 | item1 |
//  +---+---+---+--------------------------+-------+-------+
//    |
// index of index
// of last item

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

use std::cmp;
use std::error::Error as StdError;
use std::fmt;
use std::ffi::{CStr, CString};
use std::fs;
use std::io::{self, prelude::*};
use std::path::Path;

type Result<T> = std::result::Result<T, Box<dyn StdError + 'static>>;

const PBLKSIZ: usize = 512;  /* bytes */
const DBLKSIZ: usize = 8192; /* bits  */
const BYTESIZ: u64 = 8;

macro_rules! ppos {
    ($blk:expr) => {
        std::io::SeekFrom::Start($blk * (PBLKSIZ as u64))
    };
}

macro_rules! bail {
    ($err:expr) => {
        return Err(Box::new($err(None)))
    };
    ($err:expr, $($arg:tt)+) => {
        return Err(Box::new($err(Some(format!($($arg)+)))))
    };
}

/// The Db prelude.
/// 
/// This prelude exports the traits necessary to interract with [`Db`] objects.
/// 
/// ```
/// # #![allow(unused_imports)]
/// use mhdb::prelude::*;
/// ```
/// 
/// [`Db`]: struct.Db.html
pub mod prelude {
    pub use super::{Datum, Fetcher, Source};
}

/// Database object.
/// 
/// # Simple use
/// 
/// ```no_run
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use mhdb::{Db, prelude::*};
/// 
/// let mut db = Db::open("mydb")?;
/// db.store(42u8, "Hello world")?;
/// let txt: Option<String> = db.fetch(42u8)?;
/// assert!(txt.is_some());
/// println!("{}", txt.unwrap());
/// # Ok(())
/// # }
/// ```
/// 
/// This opens _mydb_ database, which is stored in the files:
/// *mydb.pag* and *mydb.dir*.
/// 
/// # In-memory
/// 
/// Any type which implements the [`Source`] trait can be used
/// as database sources. This trait is in turn automatically
/// implemented for any type which implements the [`Read`],
/// [`Write`], and [`Seek`] standard library traits.
/// 
/// ```
/// # fn main() -> Result<(), Box<dyn std::error::Error>> {
/// use mhdb::{Db, prelude::*};
/// use std::io::Cursor;
///
/// let dirf = Cursor::new(Vec::<u8>::new());
/// let pagf = Cursor::new(Vec::<u8>::new());
/// let mut db: Db = Db::with_sources(Box::new(pagf), Box::new(dirf))?;
/// 
/// db.store(42u8, "Hello world")?;
/// let txt: Option<String> = db.fetch(42u8)?;
/// assert!(txt.is_some());
/// println!("{}", txt.unwrap());
/// # Ok(())
/// # }
/// ```
/// 
/// [`Source`]: traits.Source.html
/// [`Read`]: https://doc.rust-lang.org/std/io/trait.Read.html
/// [`Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
/// [`Seek`]: https://doc.rust-lang.org/std/io/trait.Seek.html
// TODO: implement Debug for Db (and other common traits)
pub struct Db {
    // Keys and data are stored in the .pag file, in pairs.
    pagf: Box<dyn Source>,

    // .dir file is accessed by single bits. A bit value of 1 indicates that
    // a specific block is already used.
    dirf: Box<dyn Source>,

    pagbuf: [u8; PBLKSIZ],
    dirbuf: [u8; DBLKSIZ],

    blkno: u64,
    bitno: u64,
    hmask: u64,
    maxbno: u64,

    olddirb: Option<u64>,
}

impl Db {
    /// Open a database, creating the files _<name>.dir_ and _<name>.pag_
    /// unless they already exist.
    pub fn open(name: &str) -> Result<Db> {
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
        Db::with_sources(Box::new(pagsrc), Box::new(dirsrc))
    }

    /// Return a database using the provided sources for storing database content.
    /// 
    /// Any type implementing [`Source`] can be provided as source.
    /// 
    /// [`Source`]: trait.Source.html
    pub fn with_sources(pagsrc: Box<dyn Source>, dirsrc: Box<dyn Source>) -> Result<Db> {
        use io::SeekFrom::End;
        let mut db = Db {
            pagf: pagsrc,
            dirf: dirsrc,
            pagbuf: [0; PBLKSIZ],
            dirbuf: [0; DBLKSIZ],
            blkno: !0,
            bitno: 0,
            hmask: 0,
            maxbno: 0,
            olddirb: None,
        };
        db.maxbno = db.dirf.seek(End(0))?;
        Ok(db)
    }

    /// Store a key in the database.
    /// 
    /// Any type implementing [`Datum`] may be provided as `key` and `val`.
    /// [`Datum`] is implemented on most of the primitive types.
    /// 
    /// [`Datum`]: trait.Datum.html
    pub fn store(&mut self, key: impl Datum, val: impl Datum) -> Result<()> {
        let key = key.datum()?;
        let val = val.datum()?;
        self._store(&key, &val)
    }

    fn _store(&mut self, key: &[u8], val: &[u8]) -> Result<()> {
        use cmp::Ordering::Equal;
        use io::SeekFrom::Start;
        const MAX: usize = 64;

        let hash = calchash(key);

        'store: for _ in 0..=MAX {
            let (blkno, bitno, hmask) = self.calcblk(hash)?;
            let mut buf = self.readpak(blkno)?;

            // Remove old key and value
            let mut i = 0;
            while i < MAX {
                let (item, ok) = makdatum(&buf, i);
                if !ok {
                    break;
                }
                if key.cmp(item) == Equal {
                    delitem(&mut buf, i)?;
                    delitem(&mut buf, i)?;
                    break;
                }
                i += 2;
            }

            // Try to add key and value to block
            if let Ok(i) = additem(&mut buf, key) {
                match additem(&mut buf, val) {
                    Ok(_) => {
                        self.pagf.seek(Start(blkno * (PBLKSIZ as u64)))?;
                        self.pagf.write_all(&buf)?;
                        self.blkno = blkno;
                        self.bitno = bitno;
                        self.hmask = hmask;
                        self.pagbuf = buf;
                        break 'store;
                    },
                    Err(_) => delitem(&mut buf, i)?,
                }
            }

            if (key.len() + val.len() + 2*3) >= PBLKSIZ {
                bail!(Error::TooBig);
            }
            let mut ovfbuf = [0u8; PBLKSIZ];

            // Split the block
            let mut i = 0;
            while i < MAX {
                let (item, ok) = makdatum(&buf, i);
                if !ok {
                    break;
                }
                if (calchash(&item) & (hmask+1)) != 0 {
                    additem(&mut ovfbuf, &item)?;
                    delitem(&mut buf, i)?;
                    let (item, ok) = makdatum(&buf, i);
                    if !ok {
                        bail!(Error::Unpaired);
                    }
                    additem(&mut ovfbuf, item)?;
                    delitem(&mut buf, i)?;
                    continue;
                }
                i += 2;
            }

            self.pagf.seek(ppos!(blkno))?;
            self.pagf.write_all(&buf)?;
            self.pagf.seek(ppos!(blkno+hmask+1))?;
            self.pagf.write_all(&ovfbuf)?;
            self.setbit(bitno)?;
        }

        Ok(())
    }

    fn _fetch(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        use cmp::Ordering::Equal;
        const MAX: usize = PBLKSIZ;

        let hash = calchash(&key);
        let (blkno, bitno, hmask) = self.calcblk(hash)?;
        let buf = self.readpak(blkno)?;
        let mut ret = None;

        // Find key in block
        let mut i: usize = 0;
        while i < MAX {
            let (item, ok) = makdatum(&buf, i);
            if !ok {
                break;
            }
            if key.cmp(item) == Equal {
                let (item, ok) = makdatum(&buf, i+1);
                if !ok {
                    bail!(Error::Unpaired);
                }
                ret = Some(item.into());
                break;
            }
            i += 2;
        }

        self.blkno = blkno;
        self.bitno = bitno;
        self.hmask = hmask;
        self.pagbuf = buf;
        Ok(ret)
    }

    /// Delete a key from the database.
    /// 
    /// If the key doesn't exist in the database false is returned.
    /// 
    pub fn delete(&mut self, key: impl Datum) -> Result<bool> {
        let key = key.datum()?;
        self._delete(&key)
    }

    fn _delete(&mut self, key: &[u8]) -> Result<bool> {
        use cmp::Ordering::Equal;
        const MAX: usize = PBLKSIZ;

        let hash = calchash(key);
        let (blkno, bitno, hmask) = self.calcblk(hash)?;
        let mut buf = self.readpak(blkno)?;
        let mut found = false;

        // Find key in block
        let mut i: usize = 0;
        while i < MAX {
            let (item, ok) = makdatum(&buf, i);
            if !ok {
                break;
            }
            if key.cmp(item) == Equal {
                delitem(&mut buf, i)?;
                let (_, ok) = makdatum(&buf, i);
                if !ok {
                    bail!(Error::Unpaired);
                }
                delitem(&mut buf, i)?;
                found = true;
                break;
            }
            i += 2;
        }

        self.pagf.seek(ppos!(blkno))?;
        self.pagf.write_all(&buf)?;
        self.blkno = blkno;
        self.bitno = bitno;
        self.hmask = hmask;
        self.pagbuf = buf;
        Ok(found)
    }

    // NOTE: Not public until firsthash and nextkey are fixed 
    // pub fn firstkey(&mut self) -> Result<Option<Vec<u8>>> {
    //     self.firsthash(0)
    // }

    // XXX: Unpredictable behavior
    #[allow(unused)]
    fn firsthash(&mut self, hash: u64) -> Result<Option<Vec<u8>>> {
        use cmp::Ordering::Less;
        const MAX: usize = 64;
        const IMAX: usize = PBLKSIZ;
        let mut hash = hash;
        let mut res = None;

        for _ in 0..=MAX {
            let (blkno, bitno, hmask) = self.calcblk(hash)?;
            let buf = self.readpak(blkno)?;

            let (mut bitem, ok) = makdatum(&buf, 0);

            let mut i = 2;
            while i < IMAX {
                let (item, ok) = makdatum(&buf, i);
                if !ok {
                    break;
                }
                if bitem.cmp(item) == Less {
                    bitem = item;
                }
                i += 2;
            }

            if ok {
                res = Some(bitem.into());
                self.blkno = blkno;
                self.bitno = bitno;
                self.hmask = hmask;
                self.pagbuf = buf;
                break;
            }

            hash = hashinc(hash, hmask);
            if hash == 0 {
                break;
            }
        }

        Ok(res)
    }

    // NOTE: Not included until _nextkey is fixed
    // pub fn nextkey(&mut self, key: impl Datum) -> Result<Option<Vec<u8>>> {
    //     let key = key.datum()?;
    //     self._nextkey(&key)
    // }

    // XXX: Takes a huge amount of time
    #[allow(unused)]
    fn _nextkey(&mut self, key: &[u8]) -> Result<Option<Vec<u8>>> {
        use cmp::Ordering::{Greater,Less};
        const IMAX: usize = PBLKSIZ;

        let hash = calchash(key);
        let (blkno, bitno, hmask) = self.calcblk(hash)?;
        let buf = self.readpak(blkno)?;
        let mut bitem: &[u8] = &[];

        let mut f = true;
        let mut i = 0;
        while i < IMAX {
            let (item, ok) = makdatum(&buf, i);
            if !ok {
                break;
            }
            if key.cmp(item) != Greater {
                continue;
            }
            if f || bitem.cmp(item) == Less {
                bitem = item;
                f = false;
            }
            i += 2;
        }

        if !f {
            self.blkno = blkno;
            self.bitno = bitno;
            self.hmask = hmask;
            self.pagbuf = buf;
            return Ok(Some(bitem.into()));
        }

        let hash = hashinc(hash, hmask);
        if hash == 0 {
            return Ok(None);
        }

        self.firsthash(hash)
    }

    fn calcblk(&mut self, hash: u64) -> Result<(u64, u64, u64)> {
        let mut blkno: u64 = 0;
        let mut bitno: u64 = 0;
        let mut hmask: u64 = 0;

        for _ in 0..=64 {
            blkno = hash & hmask;
            bitno = blkno + hmask;
            if self.getbit(bitno)? == 0 {
                break;
            }
            hmask = (hmask<<1) + 1;
        }

        Ok((blkno, bitno, hmask))
    }

    fn readpak(&mut self, blkno: u64) -> Result<[u8; PBLKSIZ]> {
        let mut buf = [0; PBLKSIZ];

        if self.blkno != blkno {
            self.pagf.seek(ppos!(blkno))?;
            self.pagf.read(&mut buf[..])?;
            chkblk(&self.pagbuf)?;
        } else {
            buf = self.pagbuf;
        }

        Ok(buf)
    }

    fn getbit(&mut self, bitno: u64) -> Result<u8> {
        use io::SeekFrom::Start;
        let blksiz = DBLKSIZ as u64;

        if bitno > self.maxbno {
            return Ok(0);
        }

        let n = bitno % BYTESIZ;
        let bn = bitno / BYTESIZ;
        let i = (bn % blksiz) as usize;
        let b = bn / blksiz;
        if !matches!(self.olddirb, Some(oldb) if oldb == b) {
            for i in 0..DBLKSIZ {
                self.dirbuf[i] = 0;
            }
            self.dirf.seek(Start(b*blksiz))?;
            self.dirf.read(&mut self.dirbuf[..])?;
            self.olddirb = Some(b);
        }

        if (self.dirbuf[i] & (1<<n)) != 0 {
            Ok(1)
        } else {
            Ok(0)
        }
    }

    fn setbit(&mut self, bitno: u64) -> Result<()> {
        use io::SeekFrom::Start;
        let blksiz = DBLKSIZ as u64;

        if bitno > self.maxbno {
            self.maxbno = bitno;
            self.getbit(bitno)?;
        }

        let n = bitno % BYTESIZ;
        let bn = bitno / BYTESIZ;
        let i = (bn % blksiz) as usize;
        let b = bn / blksiz;

        self.dirbuf[i] |= 1<<n;
        self.dirf.seek(Start(b*blksiz))?;
        self.dirf.write_all(&self.dirbuf)?;
        Ok(())
    }

    /// Check if a key exists in the database.
    pub fn contains(&mut self, key: impl Datum) -> Result<bool> {
        let key = key.datum()?;
        let res = self._fetch(&key)?;
        Ok(res.is_some())
    }

    // NOTE: Not included until firstkey fixed
    // pub fn is_empty(&mut self) -> Result<bool> {
    //     let first = self.firstkey()?;
    //     Ok(first.is_none())
    // }
}

fn makdatum(buf: &[u8; PBLKSIZ], n: usize) -> (&[u8], bool) {
    let li = get16(buf, 0) as usize;

    if n >= li {
        return (&[0], false);
    }

    let end = if n > 0 {
        get16(buf, n+1-1) as usize
    } else {
        PBLKSIZ
    };
    let start = get16(buf, n+1) as usize;
    assert!(end <= PBLKSIZ);
    assert!(start <= end);
    (&buf[start..end], true)
}

fn additem(buf: &mut [u8; PBLKSIZ], item: &[u8]) -> Result<usize> {
    let li = get16(buf, 0) as usize;

    let start = if li > 0 {
        get16(buf, li) as usize
    } else {
        PBLKSIZ
    };
    assert!(start <= PBLKSIZ);

    if start < item.len() {
        bail!(Error::DataOverflow);
    }
    let start = start - item.len();

    let iend = (li+2)*2;
    if start <= iend {
        bail!(Error::DataOverflow);
    }

    set16(buf, li+1, start);
    buf[start..(item.len() + start)].clone_from_slice(&item[..]);
    set16(buf, 0, li+1);
    Ok(li)
}

fn delitem(buf: &mut [u8; PBLKSIZ], n: usize) -> Result<()> {
    let li = get16(buf, 0) as usize;

    if n >= li {
        bail!(Error::NoExist);
    }

    let end = if n > 0 {
        get16(buf, n+1-1) as usize
    } else {
        PBLKSIZ
    };
    assert!(end <= PBLKSIZ);
    let start = get16(buf, n+1) as usize;
    assert!(start <= end);
    let newest = get16(buf, li) as usize;
    assert!(newest <= start);

    // Copy data
    if end > start && start > newest {
        let diff = start - newest;
        for i in 1..=diff {
            buf[end-i] = buf[start-i];
            buf[start-i] = 0;
        }
    }

    // Update indices
    let len = end - start;
    for i in (n+1)..li {
        let tmp = get16(buf, i+1) as usize;
        assert!((tmp + len) <= PBLKSIZ);
        set16(buf, i, tmp + len);
    }
    set16(buf, 0, li-1);
    set16(buf, li, 0);
    Ok(())
}

#[allow(non_upper_case_globals)]
static hitab: [u8; 16] = [
    61, 57, 53, 49, 45, 41, 37, 33,
    29, 25, 21, 17, 13,  9,  5,  1,
];

#[allow(non_upper_case_globals)]
static hltab: [u64; 64] = [
    0x3100d2bf, 0x3118e3de, 0x34ab1372, 0x2807a847,
    0x1633f566, 0x2143b359, 0x26d56488, 0x3b9e6f59,
    0x37755656, 0x3089ca7b, 0x18e92d85, 0x0cd0e9d8,
    0x1a9e3b54, 0x3eaa902f, 0x0d9bfaae, 0x2f32b45b,
    0x31ed6102, 0x3d3c8398, 0x146660e3, 0x0f8d4b76,
    0x02c77a5f, 0x146c8799, 0x1c47f51f, 0x249f8f36,
    0x24772043, 0x1fbc1e4d, 0x1e86b3fa, 0x37df36a6,
    0x16ed30e4, 0x02c3148e, 0x216e5929, 0x0636b34e,
    0x317f9f56, 0x15f09d70, 0x131026fb, 0x38c784b1,
    0x29ac3305, 0x2b485dc5, 0x3c049ddc, 0x35a9fbcd,
    0x31d5373b, 0x2b246799, 0x0a2923d3, 0x08a96e9d,
    0x30031a9f, 0x08f525b5, 0x33611c06, 0x2409db98,
    0x0ca4feb2, 0x1000b71e, 0x30566e32, 0x39447d31,
    0x194e3752, 0x08233a95, 0x0f38fe36, 0x29c7cd57,
    0xf7b3a39,  0x328e8a16, 0x1e7d1388, 0x0fba78f5,
    0x274c7e7c, 0x1e8be65c, 0x2fa0b0bb, 0x1eb6c371,
];

fn calchash(bytes: impl AsRef<[u8]>) -> u64 {
    use std::num::Wrapping;

    let mut hashl = Wrapping(0u64);
    let mut hashi = Wrapping(0u8);
    let bytes = bytes.as_ref();

    for b in bytes {
        let mut f: u8 = *b;
        for _ in 0..2 {
            hashi += Wrapping(hitab[(f & 0xf) as usize]);
            hashl += Wrapping(hltab[(hashi.0 & 0x3f) as usize]);
            f >>= 4;
        }
    }
    hashl.0
}

fn hashinc(hash: u64, hmask: u64) -> u64 {
    const MAX: usize = 64;
    let mut hash = hash;
    let mut bit = hmask + 1;
    for _ in 0..=MAX {
        bit >>= 1;
        if bit == 0 {
            return 0;
        }
        if (hash&bit) == 0 {
            return hash | bit;
        }
        hash &= !bit;
    }
    0
}

fn chkblk(buf: &[u8; PBLKSIZ]) -> Result<()> {
    let mut t = PBLKSIZ;
    let lastidx = get16(buf, 0) as usize;

    // Check index values
    for i in 1..=lastidx {
        let idx = get16(buf, i) as usize;
        if idx > t {
            bail!(Error::BadBlock)
        }
        t = idx;
    }

    // Check overlap of index area and item area
    if t < (lastidx + 1)*2 {
        bail!(Error::BadBlock)
    } else {
        Ok(())
    }
}

fn get16(buf: &[u8; PBLKSIZ], n: usize) -> u16 {
    ((buf[n*2] as u16) << 8) | (buf[n*2 + 1] as u16)
}

fn set16(buf: &mut [u8; PBLKSIZ], n: usize, val: usize) {
    assert!(val <= std::u16::MAX as usize);
    assert!(val <= PBLKSIZ);
    let idx1 = n*2;
    let idx2 = n*2 + 1;
    buf[idx1] = ((val >> 8) & 0xff) as u8;
    buf[idx2] = (val & 0xff) as u8;
}

/// Trait required by database sources. Automatically implemented for standard 
/// library types such as [`File`] and [`Cursor`].
/// 
/// Allows in-memory databases using `Cursor<Vec<u8>>`.
/// 
/// [`File`]: https://doc.rust-lang.org/std/fs/struct.File.html
/// [`Cursor`]: https://doc.rust-lang.org/std/io/struct.Cursor.html
pub trait Source : Write + Read + Seek {}

impl<S: Write + Read + Seek> Source for S {}

/// Errors returned by database operations.
#[derive(Debug)]
pub enum Error {
    BadBlock(Option<String>),
    BadValue(Option<String>),
    DataOverflow(Option<String>),
    NoExist(Option<String>),
    TooBig(Option<String>),
    Unpaired(Option<String>),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Error::*;
        match self {
            BadBlock(None)          => write!(f, "bad block"),
            BadBlock(Some(msg))     => write!(f, "bad block: {}", msg),
            BadValue(None)          => write!(f, "bad value"),
            BadValue(Some(msg))     => write!(f, "bad value: {}", msg),
            DataOverflow(None)      => write!(f, "block data overflow"),
            DataOverflow(Some(msg)) => write!(f, "block data overflow: {}", msg),
            NoExist(None)           => write!(f, "item doesn't exist"),
            NoExist(Some(msg))      => write!(f, "item doesn't exist: {}", msg),
            TooBig(None)            => write!(f, "key-val pair too big"),
            TooBig(Some(msg))       => write!(f, "key-val pair too big: {}", msg),
            Unpaired(None)          => write!(f, "unpaired key-val in block"),
            Unpaired(Some(msg))     => write!(f, "unpaired key-val in block: {}", msg),
        }
    }
}

impl StdError for Error {}

/*******************************************************************************
 *                                                                             *
 * Datum implementation
 *                                                                             *
 *******************************************************************************/

/// Storable types must implement `Datum`.
/// 
/// `Datum` is implemented on most primitive types. 
/// 
/// ```
/// use mhdb::{Db, prelude::*};
/// use std::io::Cursor;
/// 
/// struct Point(i32, i32);
/// 
/// impl Datum for Point {
///     fn datum(&self) -> Result<Vec<u8>, Box<dyn std::error::Error>> {
///         let mut v = self.0.datum()?;
///         v.extend_from_slice(&self.1.datum()?);
///         Ok(v)
///     }
/// }
/// 
/// fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let dirf = Cursor::new(Vec::<u8>::new());
///     let pagf = Cursor::new(Vec::<u8>::new());
///     let mut db: Db = Db::with_sources(Box::new(pagf), Box::new(dirf))?;
/// 
///     let p = Point(-4, 8);
///     db.store("point", p)?;
///     Ok(())
/// }
/// ```
/// 
/// There is no similar way for retrieving user defined data types.
/// 
/// *Tip:* [Serde] makes it easier to serialize and deserialize
/// structs and enums.
/// 
/// ```
/// extern crate serde;
/// extern crate bincode;
/// 
/// use mhdb::{Db, prelude::*};
/// use serde::{Serialize,Deserialize};
/// use std::io::Cursor;
/// 
/// #[derive(Serialize, Deserialize, Debug, PartialEq, Eq)]
/// struct Point(i32, i32);
/// 
/// fn main() -> Result<(), Box<dyn std::error::Error>> {
///     let dirf = Cursor::new(Vec::<u8>::new());
///     let pagf = Cursor::new(Vec::<u8>::new());
///     let mut db: Db = Db::with_sources(Box::new(pagf), Box::new(dirf))?;
/// 
///     let p = Point(-4, 8);
///     let val: Vec<u8> = bincode::serialize(&p)?;
///     db.store("point", val)?;
/// 
///     let val: Vec<u8> = db.fetch("point")?.unwrap();
///     let p0: Point = bincode::deserialize(&val)?;
///     assert_eq!(p, p0);
///     Ok(())
/// }
/// ```
/// 
/// [Serde]: https://serde.rs/
pub trait Datum {
    fn datum(&self) -> Result<Vec<u8>>;
}

impl<T: Datum> Datum for &T {
    fn datum(&self) -> Result<Vec<u8>> {
        (*self).datum()
    }
}

impl<T: Datum> Datum for Vec<T> {
    fn datum(&self) -> Result<Vec<u8>> {
        let mut v = Vec::new();
        for d in self.iter() {
            let b = d.datum()?;
            v.extend_from_slice(&b);
        }
        Ok(v)
    }
}

impl<T: Datum> Datum for [T] {
    fn datum(&self) -> Result<Vec<u8>> {
        let mut v = Vec::new();
        for d in self.iter() {
            let b = d.datum()?;
            v.extend_from_slice(&b);
        }
        Ok(v)
    }
}

impl Datum for &str {
    fn datum(&self) -> Result<Vec<u8>> {
        Ok((*self).into())
    }
}

impl Datum for String {
    fn datum(&self) -> Result<Vec<u8>> {
        Ok(self.as_bytes().into())
    }
}

impl Datum for CStr {
    fn datum(&self) -> Result<Vec<u8>> {
        Ok(self.to_bytes().into())
    }
}

impl Datum for CString {
    fn datum(&self) -> Result<Vec<u8>> {
        Ok(self.to_bytes().into())
    }
}

impl Datum for u8 {
    fn datum(&self) -> Result<Vec<u8>> {
        Ok(vec![*self])
    }
}

impl Datum for i8 {
    fn datum(&self) -> Result<Vec<u8>> {
        Ok(vec![*self as u8])
    }
}

macro_rules! num_datum {
    ($type:ty, $n:expr) => {
        impl Datum for $type {
            fn datum(&self) -> Result<Vec<u8>> {
                let mut v = Vec::new();
                let mut n = *self;
                for _ in 0..$n {
                    v.push((n & 0xff) as u8);
                    n >>= 8;
                }
                Ok(v)
            }
        }
    };
}

num_datum!(u16, 2);
num_datum!(u32, 4);
num_datum!(u64, 8);
num_datum!(u128, 16);
num_datum!(i16, 2);
num_datum!(i32, 4);
num_datum!(i64, 8);
num_datum!(i128, 16);

impl Datum for bool {
    fn datum(&self) -> Result<Vec<u8>> {
        Ok(vec![*self as u8])
    }
}

impl Datum for f32 {
    fn datum(&self) -> Result<Vec<u8>> {
        let b = self.to_be_bytes();
        Ok(b.into())
    }
}

impl Datum for f64 {
    fn datum(&self) -> Result<Vec<u8>> {
        let b = self.to_be_bytes();
        Ok(b.into())
    }
}

/*******************************************************************************
 *                                                                             *
 * Fetcher implementation
 *                                                                             *
 *******************************************************************************/

/// Internal trait to allow fetching of most primitive types.
pub trait Fetcher<T> {
    fn fetch(&mut self, key: impl Datum) -> Result<Option<T>>;
}

impl Fetcher<Vec<u8>> for Db {
    fn fetch(&mut self, key: impl Datum) -> Result<Option<Vec<u8>>> {
        let key = key.datum()?;
        self._fetch(key.as_ref())
    }
}

impl Fetcher<String> for Db {
    fn fetch(&mut self, key: impl Datum) -> Result<Option<String>> {
        let key = key.datum()?;
        let v = self._fetch(key.as_ref())?;
        match v {
            Some(v) => Ok(Some(String::from_utf8(v)?)),
            None    => Ok(None),
        }
    }
}

impl Fetcher<CString> for Db {
    fn fetch(&mut self, key: impl Datum) -> Result<Option<CString>> {
        let key = key.datum()?;
        let v = self._fetch(key.as_ref())?;
        match v {
            Some(v) => Ok(Some(CString::new(v)?)),
            None    => Ok(None),
        }
    }
}

impl Fetcher<u8> for Db {
    fn fetch(&mut self, key: impl Datum) -> Result<Option<u8>> {
        let key = key.datum()?;
        let v = self._fetch(key.as_ref())?;
        match v {
            Some(v) if v.len() != 1 => bail!(Error::BadValue),
            Some(v) => Ok(Some(v[0])),
            None => Ok(None),
        }
    }
}

impl Fetcher<i8> for Db {
    fn fetch(&mut self, key: impl Datum) -> Result<Option<i8>> {
        let key = key.datum()?;
        let v = self._fetch(key.as_ref())?;
        match v {
            Some(v) if v.len() != 1 => bail!(Error::BadValue),
            Some(v) => Ok(Some(v[0] as i8)),
            None => Ok(None),
        }
    }
}

macro_rules! num_fetcher {
    ($type:ty, $n:expr) => {
        impl Fetcher<$type> for Db {
            fn fetch(&mut self, key: impl Datum) -> Result<Option<$type>> {
                let key = key.datum()?;
                let v = self._fetch(key.as_ref())?;
                match v {
                    Some(v) if v.len() != $n => bail!(Error::BadValue),
                    Some(v) => {
                        let mut num: $type = 0;
                        for i in 1..=$n {
                            num <<= 8;
                            num |= v[$n-i] as $type;
                        }
                        Ok(Some(num))
                    },
                    None => Ok(None),
                }
            }
        }
    }
}

num_fetcher!(u16, 2);
num_fetcher!(u32, 4);
num_fetcher!(u64, 8);
num_fetcher!(u128, 16);
num_fetcher!(i16, 2);
num_fetcher!(i32, 4);
num_fetcher!(i64, 8);
num_fetcher!(i128, 16);

impl Fetcher<bool> for Db {
    fn fetch(&mut self, key: impl Datum) -> Result<Option<bool>> {
        let key = key.datum()?;
        let v = self._fetch(key.as_ref())?;
        match v {
            Some(v) if v.len() != 1 => bail!(Error::BadValue),
            Some(v) => Ok(Some(v[0] != 0)),
            None => Ok(None),
        }
    }
}

impl Fetcher<f32> for Db {
    fn fetch(&mut self, key: impl Datum) -> Result<Option<f32>> {
        let key = key.datum()?;
        let v = self._fetch(key.as_ref())?;
        match v {
            Some(v) if v.len() != 4 => bail!(Error::BadValue),
            Some(v) => {
                let mut arr = [0u8; 4];
                arr.copy_from_slice(&v);
                Ok(Some(f32::from_be_bytes(arr)))
            },
            None => Ok(None),
        }
    }
}

impl Fetcher<f64> for Db {
    fn fetch(&mut self, key: impl Datum) -> Result<Option<f64>> {
        let key = key.datum()?;
        let v = self._fetch(key.as_ref())?;
        match v {
            Some(v) if v.len() != 8 => bail!(Error::BadValue),
            Some(v) => {
                let mut arr = [0u8; 8];
                arr.copy_from_slice(&v);
                Ok(Some(f64::from_be_bytes(arr)))
            },
            None => Ok(None),
        }
    }
}

/*******************************************************************************
 *                                                                             *
 * Tests
 *                                                                             *
 *******************************************************************************/

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Cursor;

    #[test]
    fn db() {
        use std::collections::{HashMap};
        use std::num::Wrapping;

        let dirf = Cursor::new(Vec::<u8>::new());
        let pagf = Cursor::new(Vec::<u8>::new());
        let mut db: Db = Db::with_sources(Box::new(pagf), Box::new(dirf))
            .expect("opening database");

        const N: usize = 42000;

        // Setup test values
        let mut tmp = 42u8;
        let mut key = Wrapping(42u64);
        let mut map: HashMap<u64, Vec<u8>> = HashMap::new();
        for i in 0..N {
            tmp ^= i as u8;
            key = Wrapping((key<<1).0 ^ i as u64);
            let mut val = Vec::new();
            // Don't make too big values or the process consumes too 
            // much memory when testing with in-memory database
            for _ in 0..=(tmp as usize) {
                val.push(tmp);
            }
            map.insert(key.0, val);
        }

        // Check overflow
        let mut val = Vec::new();
        for i in 0..=PBLKSIZ {
            val.push((i & 0xff) as u8);
        }
        match db.store(l2b(key.0), val) {
            Err(_) => (),
            _ => panic!("no error when storing too big item"),
        }

        // Fill database
        for (key, val) in &map {
            let key = l2b(*key);
            // println!("{} - {}", key.len(), val.len());
            db.store(key, val).expect("error on store");
        }

        // Check content
        for (key, val) in &map {
            let key = l2b(*key);
            let v: Vec<u8> = db.fetch(key)
                .expect("error fetching value")
                .expect("known key returned none");
            assert_eq!(&v, val);
        }

        // let key = db.firstkey()
        //     .expect("firstkey error")
        //     .expect("firstkey none");
        // let _: Vec<u8> = db.fetch(&key)
        //     .expect("error firstkey fetch")
        //     .expect("none firstkey fetch");
        // let key = db.nextkey(key)
        //     .expect("nextkey error")
        //     .expect("nextkey none");
        // let _: Vec<u8> = db.fetch(key)
        //     .expect("error nextkey fetch")
        //     .expect("none nextkey fetch");

        // Delete content
        // assert!(!db.is_empty().expect("error is_empty"));
        for (key, _) in &map {
            let key = l2b(*key);
            let v = db.delete(key)
                .expect("error deleting value");
            assert_eq!(v, true);
        }
        // assert!(db.is_empty().expect("error is_empty"));

        // Fetcher and Datum
        let key = "testkey";

        let val: Vec<u8> = vec![0, 1, 2, 3];
        db.store(key, &val).expect("storing Vec<u8>");
        let res: Vec<u8> = db.fetch(key)
            .expect("error fetching Vec<u8>")
            .expect("none fetching Vec<u8>");
        assert_eq!(val, res);

        let val: u8 = 42;
        db.store(key, val).expect("storing u8");
        let res: u8 = db.fetch(key)
            .expect("error fetching u8")
            .expect("none fetching u8");
        assert_eq!(val, res);

        let val: u16 = 42;
        db.store(key, val).expect("storing u16");
        let res: u16 = db.fetch(key)
            .expect("error fetching u16")
            .expect("none fetching u16");
        assert_eq!(val, res);

        let val: u32 = 42;
        db.store(key, val).expect("storing u32");
        let res: u32 = db.fetch(key)
            .expect("error fetching u32")
            .expect("none fetching u32");
        assert_eq!(val, res);

        let val: u64 = 42;
        db.store(key, val).expect("storing u64");
        let res: u64 = db.fetch(key)
            .expect("error fetching u64")
            .expect("none fetching u64");
        assert_eq!(val, res);

        let val: u128 = 42;
        db.store(key, val).expect("storing u128");
        let res: u128 = db.fetch(key)
            .expect("error fetching u128")
            .expect("none fetching u128");
        assert_eq!(val, res);

        let val: i8 = -42;
        db.store(key, val).expect("storing i8");
        let res: i8 = db.fetch(key)
            .expect("error fetching i8")
            .expect("none fetching i8");
        assert_eq!(val, res);

        let val: i16 = -42;
        db.store(key, val).expect("storing i16");
        let res: i16 = db.fetch(key)
            .expect("error fetching i16")
            .expect("none fetching i16");
        assert_eq!(val, res);

        let val: i32 = -42;
        db.store(key, val).expect("storing i32");
        let res: i32 = db.fetch(key)
            .expect("error fetching i32")
            .expect("none fetching i32");
        assert_eq!(val, res);

        let val: i64 = -42;
        db.store(key, val).expect("storing i64");
        let res: i64 = db.fetch(key)
            .expect("error fetching i64")
            .expect("none fetching i64");
        assert_eq!(val, res);

        let val: i128 = -42;
        db.store(key, val).expect("storing i128");
        let res: i128 = db.fetch(key)
            .expect("error fetching i128")
            .expect("none fetching i128");
        assert_eq!(val, res);

        let val: &str = "Hello World";
        db.store(key, &val).expect("storing String");
        let res: String = db.fetch(key)
            .expect("error fetching String")
            .expect("none fetching String");
        assert_eq!(val, res);

        let val: bool = true;
        db.store(key, val).expect("storing bool");
        let res: bool = db.fetch(key)
            .expect("error fetching bool")
            .expect("none fetching bool");
        assert_eq!(val, res);

        let val: f32 = 42.31415;
        db.store(key, val).expect("storing f32");
        let res: f32 = db.fetch(key)
            .expect("error fetching f32")
            .expect("none fetching f32");
        assert_eq!(val, res);

        let val: f64 = -42.16180;
        db.store(key, val).expect("storing f64");
        let res: f64 = db.fetch(key)
            .expect("error fetching f64")
            .expect("none fetching f64");
        assert_eq!(val, res);
    }

    #[test]
    fn getsetbit() {
        let dirf = Cursor::new(Vec::<u8>::new());
        let pagf = Cursor::new(Vec::<u8>::new());
        let mut db = Db::with_sources(Box::new(pagf), Box::new(dirf))
            .expect("opening database");

        assert!(matches!(db.getbit(db.bitno), Ok(0)));
        db.setbit(db.bitno).expect("setbit");
        assert!(matches!(db.getbit(db.bitno), Ok(1)));
    }

    // Test values from original c implementation
    #[test]
    fn calchash() {
        let bytes: &[u8] = &[110, 97, 109, 101];
        let want: u64 = 0x10489dcb5;
        let hash = super::calchash(bytes);
        assert_eq!(hash, want);

        let bytes: &[u8] = &[74, 111, 104, 110, 32, 83, 109, 105, 116, 104];
        let want: u64 = 0x2cf5ed230;
        let hash = super::calchash(bytes);
        assert_eq!(hash, want);

        let bytes: &[u8] = &[102, 111, 111];
        let want: u64 = 0x89f02011;
        let hash = super::calchash(bytes);
        assert_eq!(hash, want);

        let bytes: &[u8] = &[70,  117, 116, 117, 114, 97,  109, 97,  58,  32,
                             87,  104, 101, 110, 32,  65,  108, 105, 101, 110,
                             115, 32,  65,  116, 116, 97,  99,  107];
        let want: u64 = 0x64ac886d3;
        let hash = super::calchash(bytes);
        assert_eq!(hash, want);
    }

    #[test]
    fn chkblk() {
        let mut buf = [0u8; PBLKSIZ];
        set16(&mut buf, 0, 2);

        set16(&mut buf, 1, PBLKSIZ-2);
        set16(&mut buf, 2, PBLKSIZ-10);
        assert!(super::chkblk(&buf).is_ok());

        set16(&mut buf, 2, PBLKSIZ-1);
        assert!(super::chkblk(&buf).is_err());
    }

    #[test]
    fn buffer_manipulation() {
        let mut buf  = [0u8; PBLKSIZ];
        let mut want = [0u8; PBLKSIZ];

        // Adding

        set16(&mut want, 0, 1);
        set16(&mut want, 1, PBLKSIZ-4);
        want[PBLKSIZ-4] = 0x02;
        want[PBLKSIZ-3] = 0x03;
        want[PBLKSIZ-2] = 0x70;
        want[PBLKSIZ-1] = 0xff;
        additem(&mut buf, &[0x02, 0x03, 0x70, 0xff]).expect("adding item");
        for i in 0..buf.len() {
            assert_eq!(buf[i], want[i], "i = {}", i);
        }

        set16(&mut want, 0, 3);
        set16(&mut want, 2, PBLKSIZ-6);
        set16(&mut want, 3, PBLKSIZ-12);
        want[PBLKSIZ-6] = 0x02;
        want[PBLKSIZ-5] = 0x03;
        want[PBLKSIZ-12] = 0x75;
        want[PBLKSIZ-11] = 0x74;
        want[PBLKSIZ-10] = 0x73;
        want[PBLKSIZ-9] = 0x72;
        want[PBLKSIZ-8] = 0x71;
        want[PBLKSIZ-7] = 0x70;
        additem(&mut buf, &[0x02, 0x03]).expect("adding item");
        additem(&mut buf, &[0x75, 0x74, 0x73, 0x72, 0x71, 0x70]).expect("adding item");
        for i in 0..buf.len() {
            assert_eq!(buf[i], want[i], "i = {}", i);
        }

        // Deleting

        set16(&mut want, 0, 2);
        set16(&mut want, 2, PBLKSIZ-10);
        set16(&mut want, 3, 0);
        want[PBLKSIZ-12] = 0;
        want[PBLKSIZ-11] = 0;
        want[PBLKSIZ-10] = 0x75;
        want[PBLKSIZ-9] = 0x74;
        want[PBLKSIZ-8] = 0x73;
        want[PBLKSIZ-7] = 0x72;
        want[PBLKSIZ-6] = 0x71;
        want[PBLKSIZ-5] = 0x70;
        delitem(&mut buf, 1).expect("deleting item");
        for i in 0..buf.len() {
            assert_eq!(buf[i], want[i], "i = {}", i);
        }
    }

    #[allow(unused)]
    fn pbuf(buf: &[u8; PBLKSIZ]) {
        let tmp: Vec<_> = buf.iter().map(|e| *e).collect();
        println!("{:?}", &tmp);
    }

    fn l2b(n: u64) -> Vec<u8> {
        vec![
            (n & 0xff) as u8,
            ((n>>8) & 0xff) as u8,
            ((n>>16) & 0xff) as u8,
            ((n>>24) & 0xff) as u8,
            ((n>>32) & 0xff) as u8,
            ((n>>40) & 0xff) as u8,
            ((n>>48) & 0xff) as u8,
            ((n>>56) & 0xff) as u8,
        ]
    }

    #[allow(unused)]
    fn b2l(n: Vec<u8>) -> u64 {
        assert_eq!(n.len(), 8);
        ((n[7] as u64) << 56) |
        ((n[6] as u64) << 48) |
        ((n[5] as u64) << 40) |
        ((n[4] as u64) << 32) |
        ((n[3] as u64) << 24) |
        ((n[2] as u64) << 16) |
        ((n[1] as u64) << 8)  |
        (n[0] as u64)
    }
}
