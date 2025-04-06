//
// Copyright 2024 Christopher Atherton <the8lack8ox@pm.me>
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the “Software”), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED “AS IS”, WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
// FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS
// IN THE SOFTWARE.
//

use std::env;
use std::fs::File;
use std::io::{Read, Result};
use std::process::ExitCode;

struct Sha1 {
    hash: [u32; 5],
    buffer: Vec<u8>,
    length: usize,
    finished: bool,
}

impl Sha1 {
    pub fn new() -> Self {
        Self {
            hash: [0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0],
            buffer: Vec::new(),
            length: 0,
            finished: false,
        }
    }

    fn slow_update(&mut self, buf: &[u8]) {
        self.length += buf.len();
        self.buffer.extend_from_slice(buf);

        let chunks = self.buffer.chunks_exact(64);
        let remainder_tmp = chunks.remainder();
        for chunk in chunks {
            let mut w = Vec::with_capacity(80);
            for i in 0..16 {
                w.push(u32::from_be_bytes(
                    chunk[i * 4..i * 4 + 4].try_into().unwrap(),
                ));
            }
            for i in 16..80 {
                w.push((w[i - 3] ^ w[i - 8] ^ w[i - 14] ^ w[i - 16]).rotate_left(1));
            }

            let mut a = self.hash[0];
            let mut b = self.hash[1];
            let mut c = self.hash[2];
            let mut d = self.hash[3];
            let mut e = self.hash[4];

            for v in &w[0..20] {
                let temp = a
                    .rotate_left(5)
                    .wrapping_add((b & c) | ((!b) & d))
                    .wrapping_add(e)
                    .wrapping_add(0x5A827999)
                    .wrapping_add(*v);
                e = d;
                d = c;
                c = b.rotate_left(30);
                b = a;
                a = temp;
            }

            for v in &w[20..40] {
                let temp = a
                    .rotate_left(5)
                    .wrapping_add(b ^ c ^ d)
                    .wrapping_add(e)
                    .wrapping_add(0x6ED9EBA1)
                    .wrapping_add(*v);
                e = d;
                d = c;
                c = b.rotate_left(30);
                b = a;
                a = temp;
            }

            for v in &w[40..60] {
                let temp = a
                    .rotate_left(5)
                    .wrapping_add((b & c) | (b & d) | (c & d))
                    .wrapping_add(e)
                    .wrapping_add(0x8F1BBCDC)
                    .wrapping_add(*v);
                e = d;
                d = c;
                c = b.rotate_left(30);
                b = a;
                a = temp;
            }

            for v in &w[60..80] {
                let temp = a
                    .rotate_left(5)
                    .wrapping_add(b ^ c ^ d)
                    .wrapping_add(e)
                    .wrapping_add(0xCA62C1D6)
                    .wrapping_add(*v);
                e = d;
                d = c;
                c = b.rotate_left(30);
                b = a;
                a = temp;
            }

            self.hash[0] = self.hash[0].wrapping_add(a);
            self.hash[1] = self.hash[1].wrapping_add(b);
            self.hash[2] = self.hash[2].wrapping_add(c);
            self.hash[3] = self.hash[3].wrapping_add(d);
            self.hash[4] = self.hash[4].wrapping_add(e);
        }

        self.buffer = Vec::from(remainder_tmp);
    }

    #[cfg(target_arch = "x86_64")]
    #[target_feature(enable = "sha")]
    unsafe fn intrinsic_update(&mut self, buf: &[u8]) {
        use std::arch::x86_64::*;

        self.length += buf.len();
        self.buffer.extend_from_slice(buf);

        let mask = unsafe { _mm_set_epi64x(0x0001020304050607, 0x08090A0B0C0D0E0F) };
        let mut abcd = unsafe { _mm_loadu_si128(self.hash.as_ptr() as *const _) };
        let mut e0 = unsafe { _mm_set_epi32(self.hash[4] as i32, 0, 0, 0) };
        abcd = unsafe { _mm_shuffle_epi32(abcd, 0x1B) };

        let chunks = self.buffer.chunks_exact(64);
        let remainder_tmp = chunks.remainder();
        for chunk in chunks {
            // Save current state
            let abcd_save = abcd;
            let e0_save = e0;

            // Declare variables
            let mut e1;
            let mut msg0;
            let mut msg1;
            let mut msg2;
            let mut msg3;

            // Rounds 0 ~ 3
            unsafe {
                msg0 = _mm_loadu_si128(chunk[0..16].as_ptr() as *const _);
                msg0 = _mm_shuffle_epi8(msg0, mask);
                e0 = _mm_add_epi32(e0, msg0);
                e1 = abcd;
                abcd = _mm_sha1rnds4_epu32(abcd, e0, 0);
            }

            // Rounds 4 ~ 7
            unsafe {
                msg1 = _mm_loadu_si128(chunk[16..32].as_ptr() as *const _);
                msg1 = _mm_shuffle_epi8(msg1, mask);
                e1 = _mm_sha1nexte_epu32(e1, msg1);
                e0 = abcd;
                abcd = _mm_sha1rnds4_epu32(abcd, e1, 0);
                msg0 = _mm_sha1msg1_epu32(msg0, msg1);
            }

            // Rounds 8 ~ 11
            unsafe {
                msg2 = _mm_loadu_si128(chunk[32..48].as_ptr() as *const _);
                msg2 = _mm_shuffle_epi8(msg2, mask);
                e0 = _mm_sha1nexte_epu32(e0, msg2);
                e1 = abcd;
                abcd = _mm_sha1rnds4_epu32(abcd, e0, 0);
                msg1 = _mm_sha1msg1_epu32(msg1, msg2);
                msg0 = _mm_xor_si128(msg0, msg2);
            }

            // Rounds 12 ~ 15
            unsafe {
                msg3 = _mm_loadu_si128(chunk[48..64].as_ptr() as *const _);
                msg3 = _mm_shuffle_epi8(msg3, mask);
                e1 = _mm_sha1nexte_epu32(e1, msg3);
                e0 = abcd;
                msg0 = _mm_sha1msg2_epu32(msg0, msg3);
                abcd = _mm_sha1rnds4_epu32(abcd, e1, 0);
                msg2 = _mm_sha1msg1_epu32(msg2, msg3);
                msg1 = _mm_xor_si128(msg1, msg3);
            }

            // Rounds 16 ~ 19
            unsafe {
                e0 = _mm_sha1nexte_epu32(e0, msg0);
                e1 = abcd;
                msg1 = _mm_sha1msg2_epu32(msg1, msg0);
                abcd = _mm_sha1rnds4_epu32(abcd, e0, 0);
                msg3 = _mm_sha1msg1_epu32(msg3, msg0);
                msg2 = _mm_xor_si128(msg2, msg0);
            }

            // Rounds 20 ~ 23
            unsafe {
                e1 = _mm_sha1nexte_epu32(e1, msg1);
                e0 = abcd;
                msg2 = _mm_sha1msg2_epu32(msg2, msg1);
                abcd = _mm_sha1rnds4_epu32(abcd, e1, 1);
                msg0 = _mm_sha1msg1_epu32(msg0, msg1);
                msg3 = _mm_xor_si128(msg3, msg1);
            }

            // Rounds 24 ~ 27
            unsafe {
                e0 = _mm_sha1nexte_epu32(e0, msg2);
                e1 = abcd;
                msg3 = _mm_sha1msg2_epu32(msg3, msg2);
                abcd = _mm_sha1rnds4_epu32(abcd, e0, 1);
                msg1 = _mm_sha1msg1_epu32(msg1, msg2);
                msg0 = _mm_xor_si128(msg0, msg2);
            }

            // Rounds 28 ~ 31
            unsafe {
                e1 = _mm_sha1nexte_epu32(e1, msg3);
                e0 = abcd;
                msg0 = _mm_sha1msg2_epu32(msg0, msg3);
                abcd = _mm_sha1rnds4_epu32(abcd, e1, 1);
                msg2 = _mm_sha1msg1_epu32(msg2, msg3);
                msg1 = _mm_xor_si128(msg1, msg3);
            }

            // Rounds 32 ~ 35
            unsafe {
                e0 = _mm_sha1nexte_epu32(e0, msg0);
                e1 = abcd;
                msg1 = _mm_sha1msg2_epu32(msg1, msg0);
                abcd = _mm_sha1rnds4_epu32(abcd, e0, 1);
                msg3 = _mm_sha1msg1_epu32(msg3, msg0);
                msg2 = _mm_xor_si128(msg2, msg0);
            }

            // Rounds 36 ~ 39
            unsafe {
                e1 = _mm_sha1nexte_epu32(e1, msg1);
                e0 = abcd;
                msg2 = _mm_sha1msg2_epu32(msg2, msg1);
                abcd = _mm_sha1rnds4_epu32(abcd, e1, 1);
                msg0 = _mm_sha1msg1_epu32(msg0, msg1);
                msg3 = _mm_xor_si128(msg3, msg1);
            }

            // Rounds 40 ~ 43
            unsafe {
                e0 = _mm_sha1nexte_epu32(e0, msg2);
                e1 = abcd;
                msg3 = _mm_sha1msg2_epu32(msg3, msg2);
                abcd = _mm_sha1rnds4_epu32(abcd, e0, 2);
                msg1 = _mm_sha1msg1_epu32(msg1, msg2);
                msg0 = _mm_xor_si128(msg0, msg2);
            }

            // Rounds 44 ~ 47
            unsafe {
                e1 = _mm_sha1nexte_epu32(e1, msg3);
                e0 = abcd;
                msg0 = _mm_sha1msg2_epu32(msg0, msg3);
                abcd = _mm_sha1rnds4_epu32(abcd, e1, 2);
                msg2 = _mm_sha1msg1_epu32(msg2, msg3);
                msg1 = _mm_xor_si128(msg1, msg3);
            }

            // Rounds 48 ~ 51
            unsafe {
                e0 = _mm_sha1nexte_epu32(e0, msg0);
                e1 = abcd;
                msg1 = _mm_sha1msg2_epu32(msg1, msg0);
                abcd = _mm_sha1rnds4_epu32(abcd, e0, 2);
                msg3 = _mm_sha1msg1_epu32(msg3, msg0);
                msg2 = _mm_xor_si128(msg2, msg0);
            }

            // Rounds 52 ~ 55
            unsafe {
                e1 = _mm_sha1nexte_epu32(e1, msg1);
                e0 = abcd;
                msg2 = _mm_sha1msg2_epu32(msg2, msg1);
                abcd = _mm_sha1rnds4_epu32(abcd, e1, 2);
                msg0 = _mm_sha1msg1_epu32(msg0, msg1);
                msg3 = _mm_xor_si128(msg3, msg1);
            }

            // Rounds 56 ~ 59
            unsafe {
                e0 = _mm_sha1nexte_epu32(e0, msg2);
                e1 = abcd;
                msg3 = _mm_sha1msg2_epu32(msg3, msg2);
                abcd = _mm_sha1rnds4_epu32(abcd, e0, 2);
                msg1 = _mm_sha1msg1_epu32(msg1, msg2);
                msg0 = _mm_xor_si128(msg0, msg2);
            }

            // Rounds 60 ~ 63
            unsafe {
                e1 = _mm_sha1nexte_epu32(e1, msg3);
                e0 = abcd;
                msg0 = _mm_sha1msg2_epu32(msg0, msg3);
                abcd = _mm_sha1rnds4_epu32(abcd, e1, 3);
                msg2 = _mm_sha1msg1_epu32(msg2, msg3);
                msg1 = _mm_xor_si128(msg1, msg3);
            }

            // Rounds 64 ~ 67
            unsafe {
                e0 = _mm_sha1nexte_epu32(e0, msg0);
                e1 = abcd;
                msg1 = _mm_sha1msg2_epu32(msg1, msg0);
                abcd = _mm_sha1rnds4_epu32(abcd, e0, 3);
                msg3 = _mm_sha1msg1_epu32(msg3, msg0);
                msg2 = _mm_xor_si128(msg2, msg0);
            }

            // Rounds 68 ~ 71
            unsafe {
                e1 = _mm_sha1nexte_epu32(e1, msg1);
                e0 = abcd;
                msg2 = _mm_sha1msg2_epu32(msg2, msg1);
                abcd = _mm_sha1rnds4_epu32(abcd, e1, 3);
                msg3 = _mm_xor_si128(msg3, msg1);
            }

            // Rounds 72 ~ 75
            unsafe {
                e0 = _mm_sha1nexte_epu32(e0, msg2);
                e1 = abcd;
                msg3 = _mm_sha1msg2_epu32(msg3, msg2);
                abcd = _mm_sha1rnds4_epu32(abcd, e0, 3);
            }

            // Rounds 76 ~ 79
            unsafe {
                e1 = _mm_sha1nexte_epu32(e1, msg3);
                e0 = abcd;
                abcd = _mm_sha1rnds4_epu32(abcd, e1, 3);
            }

            // Combine state
            unsafe {
                e0 = _mm_sha1nexte_epu32(e0, e0_save);
                abcd = _mm_add_epi32(abcd, abcd_save);
            }
        }

        unsafe {
            abcd = _mm_shuffle_epi32(abcd, 0x1B);
            _mm_storeu_si128(self.hash.as_ptr() as *mut _, abcd);
            self.hash[4] = _mm_extract_epi32(e0, 3) as u32;
        }

        self.buffer = Vec::from(remainder_tmp);
    }

    pub fn update(&mut self, buf: &[u8]) {
        assert!(!self.finished);

        #[cfg(target_arch = "x86_64")]
        {
            if is_x86_feature_detected!("sha") {
                unsafe {
                    self.intrinsic_update(buf);
                }
                return;
            }
        }

        self.slow_update(buf);
    }

    pub fn finish(&mut self) {
        assert!(!self.finished);

        const ZEROS: [u8; 64] = [0; 64];
        let mut end = Vec::with_capacity(64);
        end.push(0x80);
        end.extend_from_slice(&ZEROS[..(120 - ((self.length + 1) % 64)) % 64]);
        end.extend_from_slice(&(self.length as u64 * 8).to_be_bytes());

        self.update(&end);
        self.finished = true;
    }

    // pub fn hash(&self) -> [u32; 5] {
    //     assert!(self.finished);
    //     self.hash
    // }

    pub fn hash_as_string(&self) -> String {
        assert!(self.finished);
        format!(
            "{:08x}{:08x}{:08x}{:08x}{:08x}",
            self.hash[0], self.hash[1], self.hash[2], self.hash[3], self.hash[4]
        )
    }
}

fn run() -> Result<()> {
    let inputs: Vec<_> = env::args().skip(1).collect();

    if inputs.is_empty() {
        let mut sha = Sha1::new();
        let mut buffer = [0; 8192];
        let mut count = std::io::stdin().read(&mut buffer)?;
        while count > 0 {
            sha.update(&buffer[..count]);
            count = std::io::stdin().read(&mut buffer)?;
        }
        sha.finish();
        println!("{} -", sha.hash_as_string());
    } else {
        for input in inputs {
            let mut sha = Sha1::new();
            let mut buffer = [0; 8192];
            let mut file = File::open(&input)?;
            let mut count = file.read(&mut buffer)?;
            while count > 0 {
                sha.update(&buffer[..count]);
                count = file.read(&mut buffer)?;
            }
            sha.finish();
            println!("{} {input}", sha.hash_as_string());
        }
    }

    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("ERROR: {err}");
            ExitCode::FAILURE
        }
    }
}
