//! Fixed source adapter for the qualified Leapfrog operation stream.
//! Source: optimizer commit 18996572e; upstream credit is in leapfrog/NOTICE.
#[allow(dead_code)]
mod configuration;
#[allow(dead_code)]
mod arithmetic_blocks;
#[cfg(test)]
mod path_test_support;
#[allow(dead_code)]
#[path = "leapfrog/mod.rs"]
mod leapfrog;

// Replace only this section when freezing another fully checked recipe.
// These values come from the committed exploitation winner.
const WINNER_SETTINGS: &[(&str, &str)] = &[
    ("AB_FUSION", "0"),
    ("HEO_PIN_ERASE_COMPARE", "20"),
    ("HEO_PIN_FOLD_GUARD", "32"),
    ("HEO_PIN_PP_FOLD_PROFILE", "0:0"),
    ("HEO_PIN_PP_REPLAY_CHUNK_COMPARE", "21"),
    ("HEO_PIN_PP_REPLAY_FLAG_COMPARE", "20"),
    ("HEO_PIN_PP_REPLAY_FOLD_WINDOW", "64"),
    ("HEO_PIN_PP_REPLAY_FOLD_WINDOW_MUL", "64"),
    ("HEO_PIN_PP_WALK_MAX_QUBITS", "1270"),
    ("HEO_PIN_SQ_ASM_TAIL", "32"),
    ("LFX_FUSED_FWD_TO", "134"),
    ("LFX_FUSED_REV_TO", "124"),
    ("LFX_WPAD", "4"),
    ("LFX_XTICKS", "4"),
    ("LFX_Y15_CMP_EXTRA", "2"),
    ("LFX_Y15_GUARD", "0"),
    ("LFX_Y15_WIN", "61"),
    ("LF_CELL_FOLD_MIN", "60"),
    ("LF_CMP_FROM", "0"),
    ("LF_CMP_SHIFT", "4,4"),
    ("LF_MERGED_LATE_WIN", "62"),
    ("LF_MERGED_WIN", "60"),
    ("LF_REORDER_DIV", "76"),
    ("LF_REORDER_MUL", "76"),
];

pub fn build() -> Vec<crate::circuit::Op> {
    static INIT: std::sync::Once = std::sync::Once::new();
    INIT.call_once(|| {
        for &(name, value) in WINNER_SETTINGS {
            configuration::insert(name, value);
        }
    });
    let ops = leapfrog::build();
    configuration::validate_fold_sites().expect("fixed recipe has valid fold sites");
    ops
}
