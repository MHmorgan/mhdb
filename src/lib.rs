//! [MHdb](https://mhmorgan.github.io/mhdb/) is a pure Rust embedded key-value
//! store database, based on [dbm](https://en.wikipedia.org/wiki/DBM_(computing)).
//! 
//! # Simple use
//! 
//! ```no_run
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! use mhdb::{Db, prelude::*};
//! 
//! let mut db = Db::open("mydb")?;
//! let key = "Number".to_owned();
//! let val = 42i32;
//! 
//! db.store(key.clone(), val)?;
//! 
//! let num: Option<i32> = db.fetch(42u8)?;
//! assert_eq!(num, Some(val));
//! println!("{}", num.unwrap());
//! # Ok(())
//! # }
//! ```
//! 
//! Any type implementing [`Datum`] can be stored in the database.
//! 
//! # Datum
//! 
//! A datum represents a single item in the database. Types
//! used as keys and/or values must therefore implement the
//! [`Datum`] trait.
//! 
//! [`Datum`] is automatically implemented on any type implementing
//! the [Serde] traits [`Serialize`] and [`Deserialize`].
//! 
//! # In-memory database
//! 
//! Any type which implements the [`Source`] trait can be used
//! as database sources. This trait is in turn automatically
//! implemented for any type which implements the [`Read`],
//! [`Write`], [`Seek`], [`Sync`], and [`Send`]
//! standard library traits.
//! A vector may therefore be used as an in-memory database.
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
//! db.store(42u8, "Hello world".to_owned())?;
//! let txt: Option<String> = db.fetch(42u8)?;
//! assert!(txt.is_some());
//! println!("{}", txt.unwrap());
//! # Ok(())
//! # }
//! ```
//! 
//! # Limitations
//! 
//! * Key-value pairs can not be larger than 506B
//! * [`Db`] objects are not thread safe
//! 
//! [`Db`]: struct.Db.html
//! [`Source`]: traits.Source.html
//! [`Datum`]: traits.Datum.html
//! [`Read`]: https://doc.rust-lang.org/std/io/trait.Read.html
//! [`Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
//! [`Seek`]: https://doc.rust-lang.org/std/io/trait.Seek.html
//! [`Debug`]: https://doc.rust-lang.org/std/fmt/trait.Debug.html
//! [`Sync`]: https://doc.rust-lang.org/std/marker/trait.Sync.html
//! [`Send`]: https://doc.rust-lang.org/std/marker/trait.Send.html
//! [Serde]: https://serde.rs/
//! [`Serialize`]: https://docs.serde.rs/serde/trait.Serialize.html
//! [`Deserialize`]: https://docs.serde.rs/serde/trait.Deserialize.html

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
use std::fmt::{self, Debug};
use std::fs;
use std::io::{self, prelude::*};
use std::path::Path;

#[cfg(feature = "std")]
use serde::{Serialize, de::DeserializeOwned};

type DbResult<T> = Result<T, Error>;

const PBLKSIZ: usize = 512;
const DBLKSIZ: usize = 8192;
const BYTESIZ: u64 = 8;

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
    pub use super::{Datum, Source};
}

struct PagCache {
    src: Box<dyn Source>,
    buf: [u8; PBLKSIZ],
    blkno: u64,
}

impl PagCache {
    fn new(src: Box<dyn Source>) -> Self {
        PagCache {
            src,
            buf: [0; PBLKSIZ],
            blkno: !0,
        }
    }

    fn read(&mut self, blkno: u64) -> io::Result<[u8; PBLKSIZ]> {
        use io::SeekFrom::Start;
        if self.blkno != blkno || self.blkno == !0 {
            self.src.seek(Start(blkno * (PBLKSIZ as u64)))?;
            let _ = self.src.read(&mut self.buf[..])?;
            self.blkno = blkno;
        }
        let mut buf = [0; PBLKSIZ];
        buf[..PBLKSIZ].clone_from_slice(&self.buf[..PBLKSIZ]);
        Ok(buf)
    }

    fn write(&mut self, blkno: u64, buf: &[u8; PBLKSIZ]) -> io::Result<()> {
        use io::SeekFrom::Start;
        self.src.seek(Start(blkno * (PBLKSIZ as u64)))?;
        self.src.write_all(buf)?;
        self.blkno = blkno;
        self.buf[..PBLKSIZ].clone_from_slice(&buf[..PBLKSIZ]);
        Ok(())
    }
}

struct DirCache {
    src: Box<dyn Source>,
    buf: [u8; DBLKSIZ],
    blkno: u64,
    maxbno: u64,
}

impl DirCache {
    fn new(src: Box<dyn Source>) -> io::Result<Self> {
        use io::SeekFrom::End;
        let mut dir = DirCache {
            src,
            buf: [0; DBLKSIZ],
            blkno: !0,
            maxbno: 0,
        };
        dir.maxbno = match dir.src.seek(End(0))?*BYTESIZ {
            max @ 0 => max,
            max @ _ => max - 1,
        };
        Ok(dir)
    }

    fn read(&mut self, blkno: u64) -> io::Result<()> {
        use io::SeekFrom::Start;
        if self.blkno != blkno || self.blkno == !0 {
            self.buf[..DBLKSIZ].clone_from_slice(&[0; DBLKSIZ]);
            self.src.seek(Start(blkno * (DBLKSIZ as u64)))?;
            let _ = self.src.read(&mut self.buf[..])?;
            self.blkno = blkno;
        }
        Ok(())
    }

    fn write(&mut self, blkno: u64) -> io::Result<()> {
        use io::SeekFrom::Start;
        self.src.seek(Start(blkno * (DBLKSIZ as u64)))?;
        self.src.write_all(&self.buf)?;
        self.blkno = blkno;
        Ok(())
    }

    fn getbit(&mut self, bitno: u64) -> io::Result<u8> {
        const BLKSIZ: u64 = DBLKSIZ as u64;

        if bitno > self.maxbno {
            return Ok(0);
        }

        let n = bitno % BYTESIZ;
        let bn = bitno / BYTESIZ;
        let i = (bn % BLKSIZ) as usize;
        let blkno = bn / BLKSIZ;
        self.read(blkno)?;

        if (self.buf[i] & (1<<n)) != 0 {
            Ok(1)
        } else {
            Ok(0)
        }
    }

    fn setbit(&mut self, bitno: u64) -> DbResult<()> {
        const BLKSIZ: u64 = DBLKSIZ as u64;

        let n = bitno % BYTESIZ;
        let bn = bitno / BYTESIZ;
        let i = (bn % BLKSIZ) as usize;
        let blkno = bn / BLKSIZ;

        if bitno > self.maxbno {
            self.maxbno = bitno;
        }
        self.read(blkno)?;

        self.buf[i] |= 1<<n;
        self.write(blkno)?;
        Ok(())
    }
}

/// The database object. All interraction with mhdb databases is
/// done through this object.
/// 
/// See [crate documentation](index.html) for examples.
/// 
/// [`Source`]: traits.Source.html
/// [`Read`]: https://doc.rust-lang.org/std/io/trait.Read.html
/// [`Write`]: https://doc.rust-lang.org/std/io/trait.Write.html
/// [`Seek`]: https://doc.rust-lang.org/std/io/trait.Seek.html
pub struct Db {
    pag: PagCache,
    dir: DirCache,
}

impl Db {
    /// Open a database, creating the files _\<name\>.dir_ and _\<name\>.pag_
    /// unless they already exist.
    /// 
    /// # Errors
    /// 
    /// `open` may return an error if an I/O error is encountered.
    /// 
    pub fn open(name: &str) -> Result<Db, io::Error> {
        let path: &Path = name.as_ref();
        let pagsrc = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .read(true)
            .open(path.with_extension("pag"))?;
        let dirsrc = fs::OpenOptions::new()
            .create(true)
            .write(true)
            .read(true)
            .open(path.with_extension("dir"))?;
        Db::with_sources(Box::new(pagsrc), Box::new(dirsrc))
    }

    /// Return a database using the provided sources for storing database content.
    /// 
    /// Any type implementing [`Source`] can be provided as source.
    /// 
    /// [`Source`]: trait.Source.html
    pub fn with_sources(
        pagsrc: Box<dyn Source>,
        dirsrc: Box<dyn Source>
    ) -> Result<Db, io::Error> {
        Ok(Db {
            pag: PagCache::new(pagsrc),
            dir: DirCache::new(dirsrc)?,
        })
    }

    /// Store a key in the database.
    /// 
    /// Any type implementing [`Datum`] may be provided as `key` and `val`.
    /// [`Datum`] is implemented on any type implementing [`Serialize`] and
    /// [`Deserialize`].
    /// 
    /// # Errors
    /// 
    /// If converting the key or value to bytes fails, or if the key-value pair
    /// is larger than 506B, an error variant will be returned.
    /// 
    /// [`Datum`]: trait.Datum.html
    /// [`Serialize`]: https://docs.serde.rs/serde/trait.Serialize.html
    /// [`Deserialize`]: https://docs.serde.rs/serde/trait.Deserialize.html
    pub fn store(&mut self, key: impl Datum, val: impl Datum) -> DbResult<()> {
        let key = key.to_datum().map_err(|e| Error::DatumError(e))?;
        let val = val.to_datum().map_err(|e| Error::DatumError(e))?;
        self._store(&key, &val)
    }

    fn _store(&mut self, key: &[u8], val: &[u8]) -> DbResult<()> {
        use cmp::Ordering::Equal;
        const MAX: usize = 64;

        let hash = calchash(key);

        'store: for _ in 0..=MAX {
            let (blkno, bitno, hmask) = self.calcblk(hash)?;
            let mut buf = self.pag.read(blkno)?;
            chkblk(&buf)?;

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
                        self.pag.write(blkno, &buf)?;
                        break 'store;
                    },
                    Err(_) => delitem(&mut buf, i)?,
                }
            }

            if (key.len() + val.len() + 2*3) >= PBLKSIZ {
                return Err(Error::PairTooBig);
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
                        return Err(Error::Unpaired);
                    }
                    additem(&mut ovfbuf, item)?;
                    delitem(&mut buf, i)?;
                    continue;
                }
                i += 2;
            }

            self.pag.write(blkno, &buf)?;
            self.pag.write(blkno+hmask+1, &ovfbuf)?;
            self.dir.setbit(bitno)?;
        }

        Ok(())
    }

    /// Fetch a key from the database. If the key doesn't exist
    /// None is returned instead.
    /// 
    /// The value is deserialized before it is returned.
    /// The database doesn't remember types, and apart from
    /// checking that deserialization doesn't fail, no type
    /// checking is performed.
    /// 
    /// The following two examples may therefore return a value,
    /// without errors, but only one would be correct:
    /// 
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # use mhdb::{Db, prelude::*};
    /// # use std::io::Cursor;
    /// # let dirf = Cursor::new(Vec::<u8>::new());
    /// # let pagf = Cursor::new(Vec::<u8>::new());
    /// # let mut db: Db = Db::with_sources(Box::new(pagf), Box::new(dirf))?;
    /// let key = "myint".to_owned();
    /// # db.store(key.clone(), 42u64)?;
    /// let num: Option<u64> = db.fetch(key)?;
    /// # assert!(num.is_some() && num.unwrap() == 42);
    /// # Ok(())
    /// # }
    /// ```
    /// 
    /// ```
    /// # fn main() -> Result<(), Box<dyn std::error::Error>> {
    /// # use mhdb::{Db, prelude::*};
    /// # use std::io::Cursor;
    /// # let dirf = Cursor::new(Vec::<u8>::new());
    /// # let pagf = Cursor::new(Vec::<u8>::new());
    /// # let mut db: Db = Db::with_sources(Box::new(pagf), Box::new(dirf))?;
    /// let key = "myint".to_owned();
    /// # db.store(key.clone(), 42u64)?;
    /// let num: Option<f64> = db.fetch(key)?;
    /// # assert!(num.is_some());
    /// # Ok(())
    /// # }
    /// ```
    /// 
    /// # Errors
    /// 
    /// If converting the key to bytes fails, an error variant will be returned.
    /// 
    pub fn fetch<T: Datum>(&mut self, key: impl Datum) -> DbResult<Option<T>> {
        let key = key.to_datum().map_err(|e| Error::DatumError(e))?;
        let val = self._fetch(&key)?;
        match val {
            None => Ok(None),
            Some(b) => {
                let val = T::from_datum(b).map_err(|e| Error::DatumError(e))?;
                Ok(Some(val))
            }
        }
    }

    fn _fetch(&mut self, key: &[u8]) -> DbResult<Option<Vec<u8>>> {
        use cmp::Ordering::Equal;
        const MAX: usize = PBLKSIZ;

        let hash = calchash(&key);
        let (blkno, _, _) = self.calcblk(hash)?;
        let buf = self.pag.read(blkno)?;
        chkblk(&buf)?;
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
                    return Err(Error::Unpaired);
                }
                ret = Some(item.into());
                break;
            }
            i += 2;
        }
        Ok(ret)
    }

    /// Delete a key from the database.
    /// 
    /// If the key doesn't exist false is returned.
    /// 
    /// # Errors
    /// 
    /// If converting the key to bytes fails, an error variant will be returned.
    /// 
    pub fn delete(&mut self, key: impl Datum) -> DbResult<bool> {
        let key = key.to_datum().map_err(|e| Error::DatumError(e))?;
        self._delete(&key)
    }

    fn _delete(&mut self, key: &[u8]) -> DbResult<bool> {
        use cmp::Ordering::Equal;
        const MAX: usize = PBLKSIZ;

        let hash = calchash(key);
        let (blkno, _, _) = self.calcblk(hash)?;
        let mut buf = self.pag.read(blkno)?;
        chkblk(&buf)?;
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
                    return Err(Error::Unpaired);
                }
                delitem(&mut buf, i)?;
                found = true;
                break;
            }
            i += 2;
        }

        self.pag.write(blkno, &buf)?;
        Ok(found)
    }

    fn calcblk(&mut self, hash: u64) -> DbResult<(u64, u64, u64)> {
        let mut blkno: u64 = 0;
        let mut bitno: u64 = 0;
        let mut hmask: u64 = 0;

        for _ in 0..=64 {
            blkno = hash & hmask;
            bitno = blkno + hmask;
            if self.dir.getbit(bitno)? == 0 {
                break;
            }
            hmask = (hmask<<1) + 1;
        }

        Ok((blkno, bitno, hmask))
    }

    /// Check if a key exists in the database.
    pub fn contains(&mut self, key: impl Datum) -> DbResult<bool> {
        let key = key.to_datum().map_err(|e| Error::DatumError(e))?;
        let res = self._fetch(&key)?;
        Ok(res.is_some())
    }
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

fn additem(buf: &mut [u8; PBLKSIZ], item: &[u8]) -> DbResult<usize> {
    let li = get16(buf, 0) as usize;

    let start = if li > 0 {
        get16(buf, li) as usize
    } else {
        PBLKSIZ
    };
    assert!(start <= PBLKSIZ);

    if start < item.len() {
        return Err(Error::BlockOverflow);
    }
    let start = start - item.len();

    let iend = (li+2)*2;
    if start <= iend {
        return Err(Error::BlockOverflow);
    }

    set16(buf, li+1, start);
    buf[start..(item.len() + start)].clone_from_slice(&item[..]);
    set16(buf, 0, li+1);
    Ok(li)
}

fn delitem(buf: &mut [u8; PBLKSIZ], n: usize) -> DbResult<()> {
    let li = get16(buf, 0) as usize;

    if n >= li {
        return Err(Error::NoExist);
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

// fn hashinc(hash: u64, hmask: u64) -> u64 {
//     const MAX: usize = 64;
//     let mut hash = hash;
//     let mut bit = hmask + 1;
//     for _ in 0..=MAX {
//         bit >>= 1;
//         if bit == 0 {
//             return 0;
//         }
//         if (hash&bit) == 0 {
//             return hash | bit;
//         }
//         hash &= !bit;
//     }
//     0
// }

fn chkblk(buf: &[u8; PBLKSIZ]) -> DbResult<()> {
    let mut t = PBLKSIZ;
    let lastidx = get16(buf, 0) as usize;

    // Check index values
    for i in 1..=lastidx {
        let idx = get16(buf, i) as usize;
        if idx > t {
            return Err(Error::BadBlock)
        }
        t = idx;
    }

    // Check overlap of index area and item area
    if t < (lastidx + 1)*2 {
        Err(Error::BadBlock)
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
pub trait Source : Write + Read + Seek + Sync + Send {}

impl<S: Write + Read + Seek + Sync + Send> Source for S {}

type BoxError = Box<dyn StdError + Sync + Send>;

/// Errors returned by database operations.
#[derive(Debug)]
pub enum Error {
    BadBlock,
    BadValue,
    BlockOverflow,
    NoExist,
    PairTooBig,
    Unpaired,
    DatumError(BoxError),
    IoError(io::Error),
    /// A propagated error
    Unknown(BoxError)
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl StdError for Error {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Error::Unknown(src) => Some(src.as_ref()),
            _ => None,
        }
    }
}

impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error::IoError(err)
    }
}

/*******************************************************************************
 *                                                                             *
 * Datum implementation
 *                                                                             *
 *******************************************************************************/

/// A datum represents a single item in the database. Any type used as
/// key or value needs to implement `Datum`.
/// 
/// Any type implementing [`Serialize`] and [`Deserialize`] also
/// implements `Datum`.
/// 
/// [`Serialize`]: https://docs.serde.rs/serde/trait.Serialize.html
/// [`Deserialize`]: https://docs.serde.rs/serde/trait.Deserialize.html
pub trait Datum: Sized {
    fn to_datum(&self) -> Result<Vec<u8>, BoxError>;
    fn from_datum(b: Vec<u8>) -> Result<Self, BoxError>;
}

#[cfg(feature = "std")]
impl<T: Serialize + DeserializeOwned> Datum for T {
    fn to_datum(&self) -> Result<Vec<u8>, BoxError> {
        let val = bincode::serialize(self)?;
        Ok(val)
    }

    fn from_datum(b: Vec<u8>) -> Result<Self, BoxError> {
        let val = bincode::deserialize(&b)?;
        Ok(val)
    }
}

#[cfg(not(feature = "std"))]
impl Datum for Vec<u8> {
    fn to_datum(&self) -> Result<Vec<u8>, Box<dyn StdError + Sync + Send>> {
        Ok(self.clone())
    }

    fn from_datum(b: Vec<u8>) -> Result<Self, Box<dyn StdError + Sync + Send>> {
        Ok(b)
    }
}

#[cfg(not(feature = "std"))]
impl Datum for String {
    fn to_datum(&self) -> Result<Vec<u8>, Box<dyn StdError + Sync + Send>> {
        Ok(self.as_bytes().into())
    }

    fn from_datum(b: Vec<u8>) -> Result<Self, Box<dyn StdError + Sync + Send>> {
        let s = String::from_utf8(b)?;
        Ok(s)
    }
}

#[cfg(not(feature = "std"))]
impl Datum for CString {
    fn to_datum(&self) -> Result<Vec<u8>, Box<dyn StdError + Sync + Send>> {
        let v: Vec<u8> = self.to_bytes().into();
        Ok(v)
    }

    fn from_datum(b: Vec<u8>) -> Result<Self, Box<dyn StdError + Sync + Send>> {
        let s = CString::new(b)?;
        Ok(s)
    }
}

#[cfg(not(feature = "std"))]
impl Datum for u8 {
    fn to_datum(&self) -> Result<Vec<u8>, Box<dyn StdError + Sync + Send>> {
        Ok(vec![*self])
    }

    fn from_datum(b: Vec<u8>) -> Result<Self, Box<dyn StdError + Sync + Send>> {
        if b.len() != 1 {
            return Err(Error::BadValue);
        }
        Ok(b[0])
    }
}

#[cfg(not(feature = "std"))]
impl Datum for i8 {
    fn to_datum(&self) -> Result<Vec<u8>, Box<dyn StdError + Sync + Send>> {
        Ok(vec![*self as u8])
    }

    fn from_datum(b: Vec<u8>) -> Result<Self, Box<dyn StdError + Sync + Send>> {
        if b.len() != 1 {
            return Err(Error::BadValue);
        }
        Ok(b[0] as i8)
    }
}

#[cfg(not(feature = "std"))]
macro_rules! num_datum {
    ($type:ty, $n:expr) => {
        impl Datum for $type {
            fn to_datum(&self) -> Result<Vec<u8>, Box<dyn StdError + Sync + Send>> {
                let mut v = Vec::new();
                let mut n = *self;
                for _ in 0..$n {
                    v.push((n & 0xff) as u8);
                    n >>= 8;
                }
                Ok(v)
            }

            fn from_datum(b: Vec<u8>) -> Result<Self, Box<dyn StdError + Sync + Send>> {
                if b.len() != $n {
                    return Err(Error::BadValue);
                }
                let mut num: $type = 0;
                for i in 1..=$n {
                    num <<= 8;
                    num |= b[$n-i] as $type;
                }
                Ok(num)
            }
        }
    };
}

#[cfg(not(feature = "std"))] num_datum!(u16, 2);
#[cfg(not(feature = "std"))] num_datum!(u32, 4);
#[cfg(not(feature = "std"))] num_datum!(u64, 8);
#[cfg(not(feature = "std"))] num_datum!(u128, 16);
#[cfg(not(feature = "std"))] num_datum!(i16, 2);
#[cfg(not(feature = "std"))] num_datum!(i32, 4);
#[cfg(not(feature = "std"))] num_datum!(i64, 8);
#[cfg(not(feature = "std"))] num_datum!(i128, 16);

#[cfg(not(feature = "std"))]
impl Datum for bool {
    fn to_datum(&self) -> Result<Vec<u8>, Box<dyn StdError + Sync + Send>> {
        Ok(vec![*self as u8])
    }

    fn from_datum(b: Vec<u8>) -> Result<Self, Box<dyn StdError + Sync + Send>> {
        if b.len() != 1 {
            return Err(Error::BadValue);
        }
        Ok(b[0] != 0)
    }
}

#[cfg(not(feature = "std"))]
impl Datum for f32 {
    fn to_datum(&self) -> Result<Vec<u8>, Box<dyn StdError + Sync + Send>> {
        let b = self.to_be_bytes();
        Ok(b.into())
    }

    fn from_datum(b: Vec<u8>) -> Result<Self, Box<dyn StdError + Sync + Send>> {
            if b.len() != 4 {
                return Err(Error::BadValue);
            }
            let mut arr = [0u8; 4];
            arr.copy_from_slice(&b);
            Ok(f32::from_be_bytes(arr))
    }
}

#[cfg(not(feature = "std"))]
impl Datum for f64 {
    fn to_datum(&self) -> Result<Vec<u8>, Box<dyn StdError + Sync + Send>> {
        let b = self.to_be_bytes();
        Ok(b.into())
    }

    fn from_datum(b: Vec<u8>) -> Result<Self, Box<dyn StdError + Sync + Send>> {
            if b.len() != 8 {
                return Err(Error::BadValue);
            }
            let mut arr = [0u8; 8];
            arr.copy_from_slice(&b);
            Ok(f64::from_be_bytes(arr))
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
            db.store(key, val.clone()).expect("error on store");
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
        let key = "testkey".to_owned();

        let val: Vec<u8> = vec![0, 1, 2, 3];
        db.store(key.clone(), val.clone()).expect("storing Vec<u8>");
        let res: Vec<u8> = db.fetch(key.clone())
            .expect("error fetching Vec<u8>")
            .expect("none fetching Vec<u8>");
        assert_eq!(val, res);

        let val: u8 = 42;
        db.store(key.clone(), val.clone()).expect("storing u8");
        let res: u8 = db.fetch(key.clone())
            .expect("error fetching u8")
            .expect("none fetching u8");
        assert_eq!(val, res);

        let val: u16 = 42;
        db.store(key.clone(), val.clone()).expect("storing u16");
        let res: u16 = db.fetch(key.clone())
            .expect("error fetching u16")
            .expect("none fetching u16");
        assert_eq!(val, res);

        let val: u32 = 42;
        db.store(key.clone(), val.clone()).expect("storing u32");
        let res: u32 = db.fetch(key.clone())
            .expect("error fetching u32")
            .expect("none fetching u32");
        assert_eq!(val, res);

        let val: u64 = 42;
        db.store(key.clone(), val.clone()).expect("storing u64");
        let res: u64 = db.fetch(key.clone())
            .expect("error fetching u64")
            .expect("none fetching u64");
        assert_eq!(val, res);

        let val: u128 = 42;
        db.store(key.clone(), val.clone()).expect("storing u128");
        let res: u128 = db.fetch(key.clone())
            .expect("error fetching u128")
            .expect("none fetching u128");
        assert_eq!(val, res);

        let val: i8 = -42;
        db.store(key.clone(), val.clone()).expect("storing i8");
        let res: i8 = db.fetch(key.clone())
            .expect("error fetching i8")
            .expect("none fetching i8");
        assert_eq!(val, res);

        let val: i16 = -42;
        db.store(key.clone(), val.clone()).expect("storing i16");
        let res: i16 = db.fetch(key.clone())
            .expect("error fetching i16")
            .expect("none fetching i16");
        assert_eq!(val, res);

        let val: i32 = -42;
        db.store(key.clone(), val.clone()).expect("storing i32");
        let res: i32 = db.fetch(key.clone())
            .expect("error fetching i32")
            .expect("none fetching i32");
        assert_eq!(val, res);

        let val: i64 = -42;
        db.store(key.clone(), val.clone()).expect("storing i64");
        let res: i64 = db.fetch(key.clone())
            .expect("error fetching i64")
            .expect("none fetching i64");
        assert_eq!(val, res);

        let val: i128 = -42;
        db.store(key.clone(), val.clone()).expect("storing i128");
        let res: i128 = db.fetch(key.clone())
            .expect("error fetching i128")
            .expect("none fetching i128");
        assert_eq!(val, res);

        let val: String = "Hello World".to_owned();
        db.store(key.clone(), val.clone()).expect("storing String");
        let res: String = db.fetch(key.clone())
            .expect("error fetching String")
            .expect("none fetching String");
        assert_eq!(val, res);

        let val: bool = true;
        db.store(key.clone(), val.clone()).expect("storing bool");
        let res: bool = db.fetch(key.clone())
            .expect("error fetching bool")
            .expect("none fetching bool");
        assert_eq!(val, res);

        let val: f32 = 42.31415;
        db.store(key.clone(), val.clone()).expect("storing f32");
        let res: f32 = db.fetch(key.clone())
            .expect("error fetching f32")
            .expect("none fetching f32");
        assert_eq!(val, res);

        let val: f64 = -42.16180;
        db.store(key.clone(), val.clone()).expect("storing f64");
        let res: f64 = db.fetch(key.clone())
            .expect("error fetching f64")
            .expect("none fetching f64");
        assert_eq!(val, res);
    }

    // #[test]
    // fn getsetbit() {
    //     let dirf = Cursor::new(Vec::<u8>::new());
    //     let pagf = Cursor::new(Vec::<u8>::new());
    //     let mut db = Db::with_sources(Box::new(pagf), Box::new(dirf))
    //         .expect("opening database");

    //     assert!(matches!(db.getbit(db.bitno), Ok(0)));
    //     db.setbit(db.bitno).expect("setbit");
    //     assert!(matches!(db.getbit(db.bitno), Ok(1)));
    // }

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
