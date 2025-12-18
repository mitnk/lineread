//! Provides miscellaneous utilities for string manipulation and grapheme handling.
//!
//! This module includes functions for working with Unicode grapheme clusters,
//! which are essential for proper handling of complex characters like emoji sequences.

#![allow(missing_docs)]

use std::borrow::Cow;
use std::io;
use std::ops::{Range, RangeFrom, RangeFull, RangeTo};
use std::str::{from_utf8, from_utf8_unchecked};

use unicode_segmentation::UnicodeSegmentation;
use unicode_width::UnicodeWidthStr;

pub fn filter_visible(s: &str) -> Cow<str> {
    use crate::reader::{START_INVISIBLE, END_INVISIBLE};

    if !s.contains(START_INVISIBLE) {
        return Cow::Borrowed(s);
    }

    let mut virt = String::new();
    let mut ignore = false;

    for ch in s.chars() {
        if ch == START_INVISIBLE {
            ignore = true;
        } else if ch == END_INVISIBLE {
            ignore = false;
        } else if !ignore {
            virt.push(ch);
        }
    }

    Cow::Owned(virt)
}

/// Returns the longest common prefix of a set of strings.
///
/// If no common prefix exists, `None` is returned.
pub fn longest_common_prefix<'a, I, S>(iter: I) -> Option<&'a str> where
        I: IntoIterator<Item=&'a S>,
        S: 'a + ?Sized + AsRef<str>,
        {
    let mut iter = iter.into_iter();

    let mut pfx = iter.next()?.as_ref();

    for s in iter {
        let s = s.as_ref();

        let n = pfx.chars().zip(s.chars())
            .take_while(|&(a, b)| a == b)
            .map(|(ch, _)| ch.len_utf8()).sum();

        if n == 0 {
            return None;
        } else {
            pfx = &pfx[..n];
        }
    }

    Some(pfx)
}

/// Returns a string consisting of a `char`, repeated `n` times.
pub fn repeat_char(ch: char, n: usize) -> String {
    let mut buf = [0; 4];
    let s = ch.encode_utf8(&mut buf);

    s.repeat(n)
}

/// Implemented for built-in range types
// Waiting for stabilization of `std` trait of the same name
pub trait RangeArgument<T> {
    /// Returns the start of range, if present.
    fn start(&self) -> Option<&T> { None }

    /// Returns the end of range, if present.
    fn end(&self) -> Option<&T> { None }
}

impl<T> RangeArgument<T> for Range<T> {
    fn start(&self) -> Option<&T> { Some(&self.start) }

    fn end(&self) -> Option<&T> { Some(&self.end) }
}

impl<T> RangeArgument<T> for RangeFrom<T> {
    fn start(&self) -> Option<&T> { Some(&self.start) }
}

impl<T> RangeArgument<T> for RangeTo<T> {
    fn end(&self) -> Option<&T> { Some(&self.end) }
}

impl<T> RangeArgument<T> for RangeFull {}

/// Move backward by `n` graphemes from position `cur` in string `s`.
/// Returns the new byte position.
pub fn backward_char(n: usize, s: &str, cur: usize) -> usize {
    let mut graphemes: Vec<(usize, &str)> = s[..cur]
        .grapheme_indices(true)
        .collect();

    let mut res = cur;
    for _ in 0..n {
        match graphemes.pop() {
            Some((idx, _)) => res = idx,
            None => return 0
        }
    }

    res
}

/// Move forward by `n` graphemes from position `cur` in string `s`.
/// Returns the new byte position.
pub fn forward_char(n: usize, s: &str, cur: usize) -> usize {
    let mut graphemes = s[cur..].grapheme_indices(true);

    for _ in 0..n {
        match graphemes.next() {
            Some(_) => (),
            None => return s.len()
        }
    }

    match graphemes.next() {
        Some((idx, _)) => cur + idx,
        None => s.len()
    }
}

pub fn backward_search_char(n: usize, buf: &str, mut cur: usize, ch: char) -> Option<usize> {
    let mut pos = None;

    for _ in 0..n {
        match buf[..cur].rfind(ch) {
            Some(p) => {
                cur = p;
                pos = Some(cur);
            }
            None => break
        }
    }

    pos
}

pub fn forward_search_char(n: usize, buf: &str, mut cur: usize, ch: char) -> Option<usize> {
    let mut pos = None;

    for _ in 0..n {
        // Skip past the character under the cursor
        let off = match buf[cur..].chars().next() {
            Some(ch) => ch.len_utf8(),
            None => break
        };

        match buf[cur + off..].find(ch) {
            Some(p) => {
                cur += off + p;
                pos = Some(cur);
            }
            None => break
        }
    }

    pos
}

pub fn backward_word(n: usize, buf: &str, cur: usize, word_break: &str) -> usize {
    let mut chars = buf[..cur].char_indices().rev();

    for _ in 0..n {
        drop_while(&mut chars, |(_, ch)| word_break.contains(ch));
        if chars.clone().next().is_none() { break; }
        drop_while(&mut chars, |(_, ch)| !word_break.contains(ch));
        if chars.clone().next().is_none() { break; }
    }

    match chars.next() {
        Some((ind, ch)) => ind + ch.len_utf8(),
        None => 0
    }
}

pub fn forward_word(n: usize, buf: &str, cur: usize, word_break: &str) -> usize {
    let mut chars = buf[cur..].char_indices();

    for _ in 0..n {
        drop_while(&mut chars, |(_, ch)| word_break.contains(ch));
        if chars.clone().next().is_none() { break; }
        drop_while(&mut chars, |(_, ch)| !word_break.contains(ch));
        if chars.clone().next().is_none() { break; }
    }

    match chars.next() {
        Some((ind, _)) => cur + ind,
        None => buf.len()
    }
}

pub fn back_n_words(n: usize, buf: &str, cur: usize, word_break: &str) -> Range<usize> {
    let prev = backward_word(1, buf, cur, word_break);
    let end = word_end(&buf, prev, word_break);

    if n > 1 {
        let start = backward_word(n - 1, buf, prev, word_break);
        start..end
    } else {
        prev..end
    }
}

pub fn forward_n_words(n: usize, buf: &str, cur: usize, word_break: &str) -> Range<usize> {
    let start = next_word(1, buf, cur, word_break);

    if n > 1 {
        let last = next_word(n - 1, buf, start, word_break);
        let end = word_end(buf, last, word_break);
        start..end
    } else {
        let end = word_end(buf, start, word_break);
        start..end
    }
}

/// Returns the first character in the buffer, if it contains any valid characters.
pub fn first_char(buf: &[u8]) -> io::Result<Option<char>> {
    match from_utf8(buf) {
        Ok(s) => Ok(s.chars().next()),
        Err(e) => {
            if e.error_len().is_some() {
                return Err(io::Error::new(io::ErrorKind::InvalidData,
                    "invalid utf-8 input received"));
            }

            let valid = e.valid_up_to();

            let s = unsafe { from_utf8_unchecked(&buf[..valid]) };
            Ok(s.chars().next())
        }
    }
}

pub fn first_word(buf: &str, word_break: &str) -> Option<usize> {
    let mut chars = buf.char_indices();

    drop_while(&mut chars, |(_, ch)| word_break.contains(ch));

    chars.next().map(|(idx, _)| idx)
}

pub fn word_start(buf: &str, cur: usize, word_break: &str) -> usize {
    let fwd = match buf[cur..].chars().next() {
        Some(ch) => word_break.contains(ch),
        None => return buf.len()
    };

    if fwd {
        next_word(1, buf, cur, word_break)
    } else {
        let mut chars = buf[..cur].char_indices().rev();

        drop_while(&mut chars, |(_, ch)| !word_break.contains(ch));

        match chars.next() {
            Some((idx, ch)) => idx + ch.len_utf8(),
            None => 0
        }
    }
}

pub fn next_word(n: usize, buf: &str, cur: usize, word_break: &str) -> usize {
    let mut chars = buf[cur..].char_indices();

    for _ in 0..n {
        drop_while(&mut chars, |(_, ch)| !word_break.contains(ch));
        if chars.clone().next().is_none() { break; }
        drop_while(&mut chars, |(_, ch)| word_break.contains(ch));
        if chars.clone().next().is_none() { break; }
    }

    match chars.next() {
        Some((idx, _)) => cur + idx,
        None => buf.len()
    }
}

pub fn word_end(buf: &str, cur: usize, word_break: &str) -> usize {
    let mut chars = buf[cur..].char_indices();

    drop_while(&mut chars, |(_, ch)| !word_break.contains(ch));

    match chars.next() {
        Some((idx, _)) => cur + idx,
        None => buf.len()
    }
}

pub fn drop_while<I, T, F>(iter: &mut I, mut f: F)
        where I: Iterator<Item=T> + Clone, F: FnMut(T) -> bool {
    loop {
        let mut clone = iter.clone();

        match clone.next() {
            None => break,
            Some(t) => {
                if f(t) {
                    *iter = clone;
                } else {
                    break;
                }
            }
        }
    }
}

pub fn get_open_paren(ch: char) -> Option<char> {
    match ch {
        ')' => Some('('),
        ']' => Some('['),
        '}' => Some('{'),
        _ => None
    }
}

pub fn find_matching_paren(s: &str, quotes: &str, open: char, close: char) -> Option<usize> {
    let mut chars = s.char_indices().rev();
    let mut level = 0;
    let mut string_delim = None;

    while let Some((ind, ch)) = chars.next() {
        if string_delim == Some(ch) {
            string_delim = None;
        } else if quotes.contains(ch) {
            string_delim = Some(ch);
        } else if string_delim.is_none() && ch == close {
            level += 1;
        } else if string_delim.is_none() && ch == open {
            level -= 1;

            if level == 0 {
                return Some(ind);
            }
        }
    }

    None
}

pub fn match_name(name: &str, value: &str) -> bool {
    // A value of "foo" matches both "foo" and "foo-bar"
    name == value ||
        (name.starts_with(value) && name.as_bytes()[value.len()] == b'-')
}

/// Returns the display width of a grapheme cluster.
/// This correctly handles complex emoji sequences like "👩‍🚒" as a single unit.
pub fn grapheme_width(grapheme: &str) -> usize {
    // For emoji sequences joined by ZWJ (zero-width joiner), the visual width
    // is typically 2 (one emoji cell), not the sum of all component widths.
    // We use unicode-width which handles most cases correctly.
    let width = UnicodeWidthStr::width(grapheme);

    // Ensure minimum width of 1 for non-empty graphemes that report 0 width
    // (e.g., some control characters or unusual Unicode)
    if width == 0 && !grapheme.is_empty() {
        // Check if it's entirely composed of zero-width characters
        let has_visible = grapheme.chars().any(|ch| {
            use unicode_width::UnicodeWidthChar;
            ch.width().unwrap_or(0) > 0
        });
        if has_visible {
            // Has visible characters but width reported as 0, use 1 as minimum
            1
        } else {
            0
        }
    } else {
        width
    }
}

#[cfg(test)]
mod test {
    use super::{
        longest_common_prefix,
        match_name,
        grapheme_width,
        backward_char,
        forward_char,
    };

    #[test]
    fn test_longest_common_prefix() {
        let empty: &[&str] = &[];

        assert_eq!(longest_common_prefix(empty.iter()),
            None);
        assert_eq!(longest_common_prefix(["foo", "bar"].iter()),
            None);
        assert_eq!(longest_common_prefix(["foo"].iter()),
            Some("foo"));
        assert_eq!(longest_common_prefix(["foo", "foobar"].iter()),
            Some("foo"));
        assert_eq!(longest_common_prefix(["foobar", "foo"].iter()),
            Some("foo"));
        assert_eq!(longest_common_prefix(["alpha", "alpaca", "alto"].iter()),
            Some("al"));

        assert_eq!(longest_common_prefix(["äöüx", "äöüy"].iter()),
            Some("äöü"));
    }

    #[test]
    fn test_match_name() {
        assert!(match_name("foo", "foo"));
        assert!(match_name("foo-", "foo"));
        assert!(match_name("foo-bar", "foo"));
        assert!(match_name("foo-bar-baz", "foo-bar"));

        assert!(!match_name("foo", "bar"));
        assert!(!match_name("foo", "foo-"));
        assert!(!match_name("foo", "foo-bar"));
    }

    #[test]
    fn test_grapheme_width() {
        // Test 1: "é" as e + combining acute accent (2 bytes: 'e' + '\u{301}')
        // This is a combining character sequence - visually displays as 1 character width
        let e_acute = "e\u{301}";
        assert_eq!(grapheme_width(e_acute), 1);

        // Test 2: "🚒" (fire engine emoji) - single emoji, width 2
        let fire_engine = "🚒";
        assert_eq!(grapheme_width(fire_engine), 2);

        // Test 3: "👩‍🚒" (woman firefighter - ZWJ sequence: 👩 + ZWJ + 🚒)
        // This is a ZWJ emoji sequence that displays as a single emoji
        let woman_firefighter = "👩\u{200d}🚒";
        // ZWJ sequences should display as a single emoji with width 2
        assert_eq!(grapheme_width(woman_firefighter), 2);
    }

    #[test]
    fn test_char_navigation_ascii() {
        // Verify ASCII strings work correctly (each char = 1 grapheme)
        let ascii = "hello";

        // Forward navigation
        assert_eq!(forward_char(1, ascii, 0), 1);  // h -> e
        assert_eq!(forward_char(2, ascii, 0), 2);  // h -> l
        assert_eq!(forward_char(5, ascii, 0), 5);  // to end
        assert_eq!(forward_char(10, ascii, 0), 5); // past end -> clamp to end

        // Backward navigation
        assert_eq!(backward_char(1, ascii, 5), 4); // end -> o
        assert_eq!(backward_char(2, ascii, 5), 3); // end -> l
        assert_eq!(backward_char(5, ascii, 5), 0); // to start
        assert_eq!(backward_char(10, ascii, 5), 0); // past start -> clamp to 0
    }

    #[test]
    fn test_char_navigation_with_graphemes() {
        // Test string with all three grapheme types: "é🚒👩‍🚒"
        let test_str = "e\u{301}🚒👩\u{200d}🚒";

        // Verify byte positions:
        // - "e\u{301}" = 3 bytes (e=1 + combining=2)
        // - "🚒" = 4 bytes
        // - "👩\u{200d}🚒" = 11 bytes (👩=4 + ZWJ=3 + 🚒=4)
        // Total = 18 bytes
        assert_eq!(test_str.len(), 18);

        // Test forward_char: move forward by 1 grapheme at a time
        let pos0 = 0;
        let pos1 = forward_char(1, test_str, pos0); // After "é"
        assert_eq!(pos1, 3);

        let pos2 = forward_char(1, test_str, pos1); // After "🚒"
        assert_eq!(pos2, 7);

        let pos3 = forward_char(1, test_str, pos2); // After "👩‍🚒"
        assert_eq!(pos3, 18); // End of string

        // Test backward_char: move backward by 1 grapheme at a time
        let back1 = backward_char(1, test_str, 18); // Before "👩‍🚒"
        assert_eq!(back1, 7);

        let back2 = backward_char(1, test_str, back1); // Before "🚒"
        assert_eq!(back2, 3);

        let back3 = backward_char(1, test_str, back2); // Before "é"
        assert_eq!(back3, 0);

        // Test moving multiple graphemes at once
        assert_eq!(forward_char(2, test_str, 0), 7);
        assert_eq!(forward_char(3, test_str, 0), 18);
        assert_eq!(backward_char(2, test_str, 18), 3);
        assert_eq!(backward_char(3, test_str, 18), 0);
    }
}
