//! Process-local research settings. This module is absent from scored builds.

use std::collections::BTreeMap;
use std::sync::OnceLock;

#[derive(Debug)]
struct Config {
    values: BTreeMap<&'static str, usize>,
}

impl Config {
    fn parse(text: &str) -> Result<Self, &'static str> {
        let mut values = BTreeMap::new();
        for setting in text.split(';') {
            let (name, value) = setting
                .split_once('=')
                .ok_or("expected name=value settings")?;
            let value: usize = value
                .trim()
                .parse()
                .map_err(|_| "settings must be integers")?;
            let (name, min, max) = match name.trim() {
                "qubits" => ("PP_WALK_MAX_QUBITS", 1024, 1250),
                "tail_cap" => ("PP_WALK_TAIL_CAP", 0, 1250),
                "rounds" => ("PP_ROUNDS_MUL", 650, 760),
                "head_div" => ("PP_HEAD_DIV", 3, 649),
                "head_mul" => ("PP_HEAD_MUL", 3, 649),
                "retain_extra_div" => ("PP_RETAIN_EXACT_EXTRA_DIV", 0, 64),
                "retain_extra_mul" => ("PP_RETAIN_EXACT_EXTRA_MUL", 0, 64),
                "guard" => ("PP_WALK_GUARD_BITS", 0, 16),
                "tail_from" => ("tail_from", 640, 759),
                "tail_bits" => ("tail_bits", 5, 32),
                "fold_guard" => ("FOLD_GUARD", 8, 64),
                "outer_compare" => ("ERASE_COMPARE", 2, 64),
                "replay_compare" => ("PP_REPLAY_CHUNK_COMPARE", 2, 64),
                "flag_compare" => ("PP_REPLAY_FLAG_COMPARE", 2, 64),
                "replay_fold" => ("PP_REPLAY_FOLD_WINDOW", 34, 128),
                "source_sign_loan" => ("PP_SOURCE_SIGN_LOAN", 0, 1),
                "small_tail" => ("PP_SMALL_TAIL", 0, 1),
                "early_sign" => ("PP_RECOMPUTE_SIGN2", 0, 1),
                _ => return Err("unknown research setting"),
            };
            if !(min..=max).contains(&value) {
                return Err("research setting outside its supported range");
            }
            if name == "PP_WALK_TAIL_CAP" && value != 0 && value < 1024 {
                return Err("walk precision footprint must be zero or at least 1024");
            }
            if values.insert(name, value).is_some() {
                return Err("duplicate research setting");
            }
        }
        if values.contains_key("tail_from") != values.contains_key("tail_bits") {
            return Err("tail_from and tail_bits must be provided together");
        }
        Ok(Self { values })
    }

    fn schedule(&self, original: &str, guard: usize) -> String {
        let mut widths = super::super::pingpong::parse_width_schedule(original);
        if self.values.contains_key("tail_from") {
            // Restore the inherited eight-bit envelope before applying the
            // explicitly requested taper; moving it later must undo the old one.
            widths.iter_mut().for_each(|width| *width = (*width).max(8));
        }
        if let Some(&rounds) = self.values.get("PP_ROUNDS_MUL") {
            widths.resize(rounds, *widths.last().unwrap());
        }
        if let Some(&start) = self.values.get("tail_from") {
            assert!(
                start < widths.len(),
                "research tail starts after the walk ends"
            );
            let physical = self.values["tail_bits"];
            let base = physical
                .checked_sub(guard)
                .expect("tail narrower than its guard");
            assert!(base >= 5, "tail must retain a five-bit baseline envelope");
            widths[start..].fill(base);
        }
        let mut runs = Vec::new();
        let mut start = 0;
        while start < widths.len() {
            let value = widths[start];
            let count = widths[start..]
                .iter()
                .take_while(|&&width| width == value)
                .count();
            runs.push(format!("{value}x{count}"));
            start += count;
        }
        let encoded = runs.join(",");
        assert_eq!(
            super::super::pingpong::parse_width_schedule(&encoded),
            widths
        );
        encoded
    }
}

fn config() -> Option<&'static Config> {
    static CONFIG: OnceLock<Option<Config>> = OnceLock::new();
    CONFIG
        .get_or_init(|| match std::env::var("MEASURE_CONFIG") {
            Ok(text) if text.is_empty() => None,
            Ok(text) => Some(
                Config::parse(&text)
                    .unwrap_or_else(|error| panic!("invalid MEASURE_CONFIG: {error}")),
            ),
            Err(std::env::VarError::NotPresent) => None,
            Err(std::env::VarError::NotUnicode(_)) => panic!("MEASURE_CONFIG is not Unicode"),
        })
        .as_ref()
}

pub(in super::super) fn override_setting(name: &str, original: &str) -> Option<String> {
    let config = config()?;
    if name == "PP_WIDTH_SCHEDULE"
        && (config.values.contains_key("PP_ROUNDS_MUL") || config.values.contains_key("tail_from"))
    {
        let guard = super::super::required_env("PP_WALK_GUARD_BITS");
        return Some(config.schedule(original, guard));
    }
    let key = if name == "PP_REPLAY_FOLD_WINDOW_MUL" {
        "PP_REPLAY_FOLD_WINDOW"
    } else {
        name
    };
    config.values.get(key).map(usize::to_string)
}

pub(super) fn describe() {
    if let Some(config) = config() {
        println!(
            "EXPERIMENT_SETTINGS {}",
            config
                .values
                .iter()
                .map(|(name, value)| format!("{name}={value}"))
                .collect::<Vec<_>>()
                .join(";")
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn settings_reject_unknown_duplicate_partial_and_out_of_range_values() {
        for text in [
            "nonce=1",
            "qubits=1251",
            "tail_cap=1251",
            "tail_cap=17",
            "head_div=2",
            "head_mul=650",
            "retain_extra_div=65",
            "guard=17",
            "qubits=1249;qubits=1248",
            "tail_from=700",
            "tail_bits=13",
            "rounds=not-a-number",
            "qubits=1249;",
        ] {
            assert!(Config::parse(text).is_err(), "{text}");
        }
    }

    #[test]
    fn schedule_keeps_prefix_and_applies_explicit_physical_tail_width() {
        let config =
            Config::parse("qubits=1249;rounds=712;guard=8;tail_from=700;tail_bits=13").unwrap();
        let original = "259,20x698,8x16";
        let schedule = config.schedule(original, 8);
        let widths = super::super::super::pingpong::parse_width_schedule(&schedule);
        assert_eq!(widths.len(), 712);
        assert_eq!(widths[0], 259);
        assert!(widths[1..699].iter().all(|&width| width == 20));
        assert_eq!(widths[699], 8);
        assert!(widths[700..].iter().all(|&width| width + 8 == 13));
    }

    #[test]
    fn moving_a_taper_later_restores_the_intervening_envelope() {
        let config = Config::parse("tail_from=704;tail_bits=13").unwrap();
        let schedule = config.schedule("259,20x698,8,5x15", 8);
        let widths = super::super::super::pingpong::parse_width_schedule(&schedule);
        assert!(widths[699..704].iter().all(|&width| width == 8));
        assert!(widths[704..].iter().all(|&width| width == 5));
    }
}
