//! Read only explicit settings and fixed backend pins.
use std::collections::BTreeMap;
use std::sync::{Mutex, OnceLock};

fn settings() -> &'static Mutex<BTreeMap<String, String>> {
    static SETTINGS: OnceLock<Mutex<BTreeMap<String, String>>> = OnceLock::new();
    SETTINGS.get_or_init(|| Mutex::new(BTreeMap::new()))
}

pub fn var(name: &str) -> Result<String, std::env::VarError> {
    settings().lock().unwrap().get(name).cloned().ok_or(std::env::VarError::NotPresent)
}

pub fn set_default(name: &str, value: &str) {
    settings().lock().unwrap().entry(name.into()).or_insert_with(|| value.into());
}

pub fn insert(name: &str, value: &str) {
    settings().lock().unwrap().insert(name.into(), value.into());
}

pub fn enabled(name: &str) -> bool {
    var(name).map_or(true, |value| value == "1")
}

use std::sync::atomic::{AtomicUsize, Ordering};
static FOLD_SITE: AtomicUsize = AtomicUsize::new(0);

pub fn next_fold_site() -> usize {
    FOLD_SITE.fetch_add(1, Ordering::Relaxed)
}

pub fn fold_mode(site: usize) -> u8 {
    if let Ok(text) = var("CP_FOLD_SITES") {
        for item in text.split(',').filter(|s| !s.is_empty()) {
            let (index, mode) = item.split_once(':').expect("validated fold site");
            if index.parse::<usize>().unwrap() == site {
                return mode.parse::<u8>().unwrap();
            }
        }
    }
    if var("CP_FOLD_SPLIT").as_deref() != Ok("1") { return 0; }
    if var("CP_FOLD_STREAMED").as_deref() == Ok("1") { 2 } else { 1 }
}

pub fn profile_fold(site: usize, width: usize, active: u32, mode: u8, split: Option<usize>) {
    if var("CP_PROFILE").as_deref() == Ok("1") {
        eprintln!("SWARM_SITE\t{}\t{}\t{}\t{}\t{}", site, width, active, mode,
                  split.map(|n| n.to_string()).unwrap_or_else(|| "none".into()));
    }
}

pub fn validate_fold_sites() -> Result<(), String> {
    let count = FOLD_SITE.load(Ordering::Relaxed);
    if let Ok(text) = var("CP_FOLD_SITES") {
        for item in text.split(',').filter(|s| !s.is_empty()) {
            let (index, _) = item.split_once(':').expect("validated fold site");
            if index.parse::<usize>().unwrap() >= count {
                return Err(format!("fold site {index} does not exist; circuit has {count} sites"));
            }
        }
    }
    for name in ["CP_INLET_SITES", "CP_INLINE_SITES"] {
        if let Ok(text) = var(name) {
            for item in text.split(',').filter(|s| !s.is_empty()) {
                if item.parse::<usize>().unwrap() >= count {
                    return Err(format!("site {item} in {name} does not exist; circuit has {count} sites"));
                }
            }
        }
    }
    Ok(())
}

pub fn retire_inlet(site: usize) -> bool {
    var("CP_INLET_EARLY").as_deref() == Ok("1") || var("CP_INLET_SITES").map_or(false, |text|
        text.split(',').filter(|s| !s.is_empty()).any(|s| s.parse::<usize>().unwrap() == site))
}

pub fn peek_fold_site() -> usize { FOLD_SITE.load(Ordering::Relaxed) }

pub fn inline_plus2(site: usize) -> bool {
    var("CP_INLINE_PLUS2").as_deref() == Ok("1") || var("CP_INLINE_SITES").map_or(false, |text|
        text.split(',').filter(|s| !s.is_empty()).any(|s| s.parse::<usize>().unwrap() == site))
}
