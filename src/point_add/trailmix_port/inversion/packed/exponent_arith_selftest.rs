//! Exhaustive Simulator harness for `exponent_arith` (the pattern of
//! `retained_division.rs::tests` / `midq_gate_compare_selftest`): build a small
//! circuit, load basis inputs 64 shots at a time, apply every emitted op through
//! `predicate_clear_selftest::checked_apply`, assert value / phase 0 / every
//! freed ancilla 0, forward AND inverse on the same data, and print the emitted
//! Toffoli count (CCX + CCZ) of each circuit.

use super::*;
use crate::circuit::{analyze_ops, Op, OperationType, QubitId};
use crate::sim::Simulator;
use sha3::{
    digest::{ExtendableOutput, Update},
    Shake256,
};

/// Real rows from the exact PZ recurrence (tools/packed_prefix_model.py::pz_prefix,
/// generated for this test; seed 7, 400 inputs x 530 steps).
mod rows {
    /// Division rows: (e_a, e_b, off, d, s_raw, a_low28, term).
    pub(super) const DIV_ROWS: &[(u16, u16, u8, u8, u8, u32, u8)] = &[
        (109, 105, 1, 2, 4, 0x04038f0a, 0),
        (25, 21, 0, 2, 4, 0x01919ec2, 0),
        (210, 210, 0, 2, 0, 0x0d94f35b, 0),
        (247, 247, 0, 5, 0, 0x05cbfff7, 0),
        (16, 15, 0, 4, 1, 0x0000d19f, 0),
        (122, 120, 1, 2, 2, 0x00de7ea7, 0),
        (51, 51, 0, 3, 0, 0x07cf3c4f, 0),
        (183, 183, 0, 2, 0, 0x0df5fd1d, 0),
        (241, 239, 1, 1, 2, 0x05f7e604, 0),
        (127, 126, 1, 1, 1, 0x03548f52, 0),
        (63, 62, 1, 2, 1, 0x053920c4, 0),
        (46, 45, 1, 1, 1, 0x02410e16, 0),
        (194, 194, 0, 2, 0, 0x0ae6d6a7, 0),
        (76, 73, 1, 2, 3, 0x07f0d91b, 0),
        (143, 142, 0, 3, 1, 0x04aade20, 0),
        (10, 9, 0, 4, 1, 0x00000249, 0),
        (26, 25, 0, 1, 1, 0x03d2e9d5, 0),
        (225, 225, 0, 4, 0, 0x092a9a4d, 0),
        (240, 237, 0, 6, 3, 0x06d33d9d, 0),
        (84, 77, 0, 2, 7, 0x08871b95, 0),
        (125, 125, 0, 5, 0, 0x007c4736, 0),
        (148, 145, 0, 4, 3, 0x063380bc, 0),
        (65, 65, 0, 2, 0, 0x06a8bdb5, 0),
        (142, 140, 1, 1, 2, 0x0ebb2aa1, 0),
        (2, 1, 0, 1, 1, 0x00000003, 0),
        (101, 99, 1, 3, 2, 0x08404968, 0),
        (115, 114, 1, 5, 1, 0x0cf0d94f, 0),
        (252, 249, 0, 3, 3, 0x0ef9c3cb, 0),
        (253, 252, 1, 1, 1, 0x0c365370, 0),
        (251, 251, 0, 1, 0, 0x0bfd49a6, 0),
        (180, 178, 1, 4, 2, 0x05ff1c1d, 0),
        (254, 254, 0, 6, 0, 0x0c0c4741, 0),
        (250, 247, 1, 2, 3, 0x06da95bb, 0),
        (254, 253, 0, 4, 1, 0x0421536b, 0),
        (251, 251, 0, 2, 0, 0x07f685db, 0),
        (244, 240, 1, 6, 4, 0x01beca5b, 0),
        (252, 252, 0, 5, 0, 0x0b5163ad, 0),
        (250, 248, 1, 3, 2, 0x05240ba7, 0),
        (255, 254, 1, 5, 1, 0x0789d05a, 0),
        (4, 1, 0, 2, 3, 0x0000000a, 0),
    ];
    /// Terminal divisions (A = 2^s, B = 1): same layout, term = 1.
    pub(super) const TERM_ROWS: &[(u16, u16, u8, u8, u8, u32, u8)] = &[
        (1, 1, 0, 1, 0, 0x00000001, 1),
        (2, 1, 0, 2, 1, 0x00000002, 1),
        (3, 1, 0, 3, 2, 0x00000004, 1),
        (1, 1, 0, 1, 0, 0x00000001, 1),
        (2, 1, 0, 2, 1, 0x00000002, 1),
        (3, 1, 0, 3, 2, 0x00000004, 1),
    ];
    /// Multiply rows: (e_cb, s2, carry, e_ca_new, e_ca_old).
    pub(super) const MUL_ROWS: &[(u16, u8, u8, u16, u16)] = &[
        (253, 1, 0, 254, 253),
        (137, 1, 0, 138, 135),
        (117, 3, 0, 120, 117),
        (97, 0, 1, 98, 95),
        (195, 1, 0, 196, 193),
        (151, 0, 1, 152, 151),
        (243, 3, 1, 247, 246),
        (105, 0, 1, 106, 104),
        (88, 0, 1, 89, 86),
        (195, 0, 1, 196, 194),
        (127, 0, 0, 127, 125),
        (135, 5, 1, 141, 140),
        (179, 1, 1, 181, 179),
        (196, 4, 1, 201, 200),
        (22, 2, 0, 24, 20),
        (221, 2, 0, 223, 219),
        (4, 1, 0, 5, 2),
        (108, 0, 1, 109, 108),
        (212, 0, 1, 213, 211),
        (201, 0, 0, 201, 197),
        (105, 1, 1, 107, 106),
        (20, 4, 1, 25, 23),
        (232, 1, 0, 233, 231),
        (214, 2, 0, 216, 213),
        (119, 2, 1, 122, 121),
        (199, 5, 0, 204, 199),
        (1, 0, 0, 1, 0),
        (1, 3, 0, 4, 0),
        (1, 1, 0, 2, 0),
        (1, 2, 0, 3, 0),
        (1, 5, 0, 6, 0),
    ];
    /// Step-start exponents: (e_ca, e_cb, e_a, e_b).
    pub(super) const ROLE_ROWS: &[(u16, u16, u16, u16)] = &[
        (173, 170, 170, 170),
        (149, 146, 144, 145),
        (33, 32, 31, 29),
        (50, 44, 44, 43),
        (11, 8, 8, 7),
        (0, 256, 250, 249),
        (54, 54, 52, 52),
        (110, 110, 107, 108),
        (43, 40, 38, 39),
        (39, 37, 34, 35),
        (27, 26, 19, 20),
        (140, 139, 139, 137),
        (213, 213, 212, 212),
        (16, 14, 12, 10),
        (141, 139, 136, 137),
        (46, 45, 44, 41),
        (21, 21, 21, 18),
        (205, 200, 200, 199),
        (169, 169, 166, 168),
        (235, 233, 227, 231),
        (63, 62, 53, 58),
        (146, 146, 143, 142),
        (44, 43, 42, 42),
        (239, 239, 239, 238),
        (122, 121, 121, 120),
        (62, 61, 60, 58),
        (92, 91, 91, 87),
        (136, 134, 134, 132),
        (146, 146, 145, 145),
        (56, 60, 51, 55),
        (62, 63, 57, 59),
        (211, 215, 208, 209),
        (163, 162, 161, 160),
        (14, 12, 12, 11),
        (59, 61, 55, 57),
        (22, 21, 21, 20),
        (164, 164, 161, 160),
        (148, 149, 143, 147),
        (224, 223, 221, 222),
        (166, 163, 162, 162),
    ];
    /// Non-division rows with e_B = 1 (gate_div = 0): (kind, a_low28, e_a, e_b, shift).
    pub(super) const NONDIV_ROWS: &[(&str, u32, u16, u16, u8)] = &[
        ("drain", 0x00000000, 0, 1, 0),
        ("drain", 0x00000000, 0, 1, 3),
        ("frozen", 0x00000000, 0, 1, 0),
        ("drain", 0x00000000, 0, 1, 1),
        ("drain", 0x00000000, 0, 1, 2),
        ("mul_b1", 0x00000000, 0, 1, 4),
    ];
}

/// Adversarial real rows (review, 2026-09-13): the exact PZ recurrence of
/// tools/packed_prefix_model.py::pz_prefix, seed 11, 600 inputs x 530 steps
/// (134,165 divisions / 134,165 multiplies / 318,000 step starts; max d 16,
/// max s_raw 16, max R2 gap 20, first termination at step 394, 0 violations of
/// the role fact `max(e_ca, e_cb) <= 257 - max(e_A, e_B)`), selected by class:
/// max drop, off = 1 with d = 1 (k = 31, the window top), step-0 rows
/// (e_A = 256), s_raw = 0, max s_raw, B = 1 rows with A not a power of two,
/// every terminal s seen, off = 1 near e_B = 256; first multiplies with
/// ca_old = 0 and e_B in [226, 256] (B's wrapped bits give pos in 2..14, nz = 0),
/// R2 gap 0 and max gap, draining rows (A = 0, B = 1, q != 0, e_ca_new up to
/// 256), tight multiplies (e_B + s2 + e_cb = 257, carry = 0), carry = 1, max s2.
mod rows2 {
    /// (e_a, e_b, off, d, s_raw, a_low28 at D0, a_new_low28 at D0-clear, term, step)
    pub(super) const DIV2_ROWS: &[(u16, u16, u8, u8, u8, u32, u32, u8, u16)] = &[
        (53, 49, 0, 16, 4, 0x0bbb592a, 0x07a2b73a, 0, 352),
        (214, 214, 0, 16, 0, 0x041e8399, 0x0f9fc2fa, 0, 69),
        (70, 68, 0, 15, 2, 0x01552abc, 0x01b2f5f0, 0, 306),
        (193, 193, 0, 15, 0, 0x04d10332, 0x0d218599, 0, 110),
        (84, 83, 0, 15, 1, 0x09788553, 0x0ba47edf, 0, 300),
        (216, 216, 0, 14, 0, 0x0b4a2a95, 0x0e9dc76a, 0, 76),
        (253, 253, 0, 14, 0, 0x0bcfb6a1, 0x08f66e5e, 0, 4),
        (217, 217, 0, 14, 0, 0x0f04e4c3, 0x0730e7b4, 0, 72),
        (153, 152, 0, 14, 1, 0x01ace236, 0x09f86344, 0, 196),
        (48, 47, 0, 14, 1, 0x0d4cef38, 0x05dcd202, 0, 365),
        (125, 121, 0, 14, 4, 0x06b4cdc5, 0x05245685, 0, 240),
        (176, 176, 0, 14, 0, 0x09aedbf4, 0x02a348f1, 0, 138),
        (53, 52, 0, 14, 1, 0x050ef835, 0x08739989, 0, 350),
        (246, 245, 0, 14, 1, 0x0742514b, 0x06acf455, 0, 22),
        (65, 65, 0, 14, 0, 0x081a5885, 0x045f7488, 0, 340),
        (245, 242, 0, 14, 3, 0x09541a3a, 0x08ab05e2, 0, 13),
        (248, 247, 1, 1, 1, 0x0dc25a31, 0x033150d3, 0, 12),
        (242, 240, 1, 1, 2, 0x0169d1df, 0x04090b7d, 0, 26),
        (241, 240, 1, 1, 1, 0x04090b7d, 0x0558a84c, 0, 27),
        (240, 237, 1, 1, 3, 0x0558a84c, 0x0ff9bcb8, 0, 32),
        (233, 231, 1, 1, 2, 0x09c35a9d, 0x08ebacff, 0, 42),
        (231, 229, 1, 1, 2, 0x006bd6cf, 0x0f6c2a6f, 0, 46),
        (245, 245, 0, 1, 0, 0x075fb88b, 0x02edd8ce, 0, 18),
        (228, 225, 0, 1, 3, 0x06ec543f, 0x01b2e6af, 0, 52),
        (223, 222, 0, 1, 1, 0x0390fdcb, 0x0c869993, 0, 60),
        (207, 207, 0, 1, 0, 0x034f15a1, 0x06fea808, 0, 90),
        (256, 255, 0, 3, 1, 0x0ffffc2f, 0x0861b153, 0, 0),
        (256, 255, 0, 4, 1, 0x0ffffc2f, 0x0bfc36b3, 0, 0),
        (256, 254, 0, 1, 2, 0x0ffffc2f, 0x0b000247, 0, 0),
        (256, 255, 0, 2, 1, 0x0ffffc2f, 0x0e6c621d, 0, 0),
        (256, 255, 0, 1, 1, 0x0ffffc2f, 0x06e2123b, 0, 0),
        (256, 252, 0, 1, 4, 0x0ffffc2f, 0x0ae775af, 0, 0),
        (253, 253, 0, 2, 0, 0x0861b153, 0x06195131, 0, 4),
        (247, 247, 0, 2, 0, 0x0a91095e, 0x075fb88b, 0, 14),
        (240, 240, 0, 3, 0, 0x0eb06331, 0x0957bae5, 0, 30),
        (214, 198, 0, 4, 16, 0x047ec09f, 0x0184c09f, 0, 72),
        (193, 178, 0, 1, 15, 0x07af7d99, 0x04e2fd99, 0, 114),
        (216, 202, 1, 3, 14, 0x0cac632b, 0x03bf232b, 0, 78),
        (253, 239, 1, 1, 14, 0x02d94843, 0x050d8843, 0, 6),
        (217, 203, 0, 3, 14, 0x07d3fd0f, 0x0de6fd0f, 0, 74),
        (176, 162, 1, 2, 14, 0x070b9303, 0x0ded7303, 0, 140),
        (10, 1, 0, 2, 9, 0x0000029f, 0x0000009f, 0, 432),
        (10, 1, 0, 4, 9, 0x0000023d, 0x0000003d, 0, 448),
        (10, 1, 0, 3, 9, 0x00000257, 0x00000057, 0, 406),
        (9, 1, 0, 1, 8, 0x00000198, 0x00000098, 0, 448),
        (9, 1, 0, 6, 8, 0x00000104, 0x00000004, 0, 428),
        (8, 1, 0, 3, 7, 0x00000098, 0x00000018, 0, 449),
        (8, 1, 0, 3, 7, 0x0000009f, 0x0000001f, 0, 433),
        (8, 1, 0, 6, 7, 0x00000082, 0x00000002, 0, 432),
        (8, 1, 0, 2, 7, 0x000000b5, 0x00000035, 0, 448),
        (8, 1, 0, 7, 7, 0x00000081, 0x00000001, 0, 462),
        (8, 1, 0, 2, 7, 0x000000ac, 0x0000002c, 0, 448),
        (7, 1, 0, 1, 6, 0x0000006c, 0x0000002c, 0, 430),
        (7, 1, 0, 6, 6, 0x00000041, 0x00000001, 0, 428),
        (6, 1, 0, 5, 5, 0x00000021, 0x00000001, 0, 444),
        (7, 1, 0, 5, 6, 0x00000042, 0x00000002, 0, 438),
        (5, 1, 0, 4, 4, 0x00000011, 0x00000001, 0, 434),
        (6, 1, 0, 6, 5, 0x00000020, 0x00000000, 1, 460),
        (5, 1, 0, 5, 4, 0x00000010, 0x00000000, 1, 450),
        (4, 1, 0, 4, 3, 0x00000008, 0x00000000, 1, 451),
        (3, 1, 0, 3, 2, 0x00000004, 0x00000000, 1, 450),
        (2, 1, 0, 2, 1, 0x00000002, 0x00000000, 1, 454),
        (1, 1, 0, 1, 0, 0x00000001, 0x00000000, 1, 461),
        (153, 151, 1, 10, 2, 0x0725af21, 0x0c2336b9, 0, 195),
        (141, 134, 1, 10, 7, 0x0c9479dd, 0x0bd7e81d, 0, 208),
        (141, 140, 1, 9, 1, 0x04f95fc5, 0x08f8a20f, 0, 203),
        (84, 83, 1, 8, 1, 0x0bd8b18c, 0x0dff1d81, 0, 310),
        (59, 57, 1, 8, 2, 0x06369b7f, 0x05a63155, 0, 350),
        (224, 222, 1, 8, 2, 0x097b1e95, 0x0ae62fd1, 0, 54),
        (253, 251, 1, 4, 2, 0x02486022, 0x0615bdc0, 0, 6),
        (253, 252, 1, 1, 1, 0x02202d26, 0x0623f673, 0, 3),
        (255, 252, 1, 2, 3, 0x06e2123b, 0x002e873f, 0, 4),
        (255, 251, 1, 1, 4, 0x00b17d0c, 0x015554b4, 0, 4),
    ];
    /// (e_b, e_ca_old, nz, pos, e_cb, s2, carry, e_ca_new, kind: 0 normal 1 first 2 drain, step)
    pub(super) const MUL2_ROWS: &[(u16, u16, u8, u8, u16, u8, u8, u16, u8, u16)] = &[
        (255, 0, 0, 3, 1, 1, 0, 2, 1, 1),
        (255, 0, 0, 2, 1, 1, 0, 2, 1, 1),
        (255, 0, 0, 4, 1, 0, 0, 1, 1, 2),
        (255, 0, 0, 2, 1, 0, 0, 1, 1, 2),
        (255, 0, 0, 3, 1, 0, 0, 1, 1, 2),
        (255, 0, 0, 7, 1, 1, 0, 2, 1, 1),
        (244, 0, 0, 14, 1, 1, 0, 2, 1, 7),
        (246, 0, 0, 11, 1, 1, 0, 2, 1, 6),
        (247, 0, 0, 12, 1, 0, 0, 1, 1, 4),
        (247, 0, 0, 11, 1, 0, 0, 1, 1, 6),
        (248, 0, 0, 12, 1, 1, 0, 2, 1, 6),
        (248, 0, 0, 10, 1, 0, 0, 1, 1, 4),
        (194, 43, 1, 20, 59, 2, 0, 61, 0, 90),
        (178, 61, 1, 18, 64, 0, 0, 64, 0, 124),
        (102, 137, 1, 18, 149, 0, 0, 149, 0, 251),
        (198, 41, 1, 18, 43, 1, 0, 44, 0, 80),
        (130, 110, 1, 17, 118, 0, 0, 118, 0, 233),
        (47, 193, 1, 17, 203, 0, 0, 203, 0, 374),
        (46, 194, 1, 17, 199, 1, 0, 200, 0, 343),
        (176, 64, 1, 17, 79, 1, 0, 80, 0, 135),
        (230, 10, 1, 17, 22, 0, 0, 22, 0, 26),
        (231, 9, 1, 17, 15, 0, 0, 15, 0, 19),
        (1, 242, 1, 14, 253, 1, 0, 254, 2, 435),
        (1, 244, 1, 12, 247, 0, 0, 247, 2, 439),
        (1, 245, 1, 11, 254, 1, 0, 255, 2, 450),
        (1, 246, 1, 10, 254, 0, 0, 254, 2, 464),
        (1, 246, 1, 10, 250, 0, 0, 250, 2, 438),
        (1, 246, 1, 10, 247, 0, 1, 248, 2, 454),
        (1, 247, 1, 9, 247, 1, 1, 249, 2, 440),
        (1, 247, 1, 9, 252, 0, 0, 252, 2, 459),
        (1, 247, 1, 9, 255, 0, 0, 255, 2, 450),
        (1, 247, 1, 9, 251, 1, 0, 252, 2, 459),
        (198, 56, 1, 3, 43, 16, 0, 59, 0, 87),
        (178, 78, 1, 1, 64, 15, 0, 79, 0, 133),
        (203, 51, 1, 3, 40, 14, 0, 54, 0, 91),
        (51, 203, 1, 3, 192, 14, 0, 206, 0, 353),
        (122, 131, 1, 4, 122, 13, 0, 135, 0, 227),
        (34, 220, 1, 3, 210, 13, 0, 223, 0, 387),
        (55, 199, 1, 3, 189, 13, 0, 202, 0, 319),
        (39, 216, 1, 2, 205, 13, 0, 218, 0, 367),
        (202, 52, 1, 3, 41, 13, 1, 55, 0, 85),
        (239, 17, 1, 1, 4, 13, 1, 18, 0, 21),
        (162, 93, 1, 2, 81, 13, 1, 95, 0, 153),
        (69, 185, 1, 3, 174, 13, 1, 188, 0, 317),
        (239, 15, 1, 3, 4, 12, 1, 17, 0, 20),
        (26, 229, 1, 2, 218, 12, 1, 231, 0, 403),
        (139, 117, 1, 1, 105, 12, 1, 118, 0, 213),
        (232, 24, 1, 1, 12, 12, 1, 25, 0, 39),
        (178, 77, 1, 2, 64, 14, 0, 78, 0, 132),
        (1, 254, 1, 2, 254, 2, 0, 256, 2, 463),
        (1, 255, 1, 1, 248, 8, 0, 256, 2, 455),
        (1, 253, 1, 3, 255, 1, 0, 256, 2, 455),
        (1, 254, 1, 2, 255, 1, 0, 256, 2, 455),
        (1, 252, 1, 4, 253, 3, 0, 256, 2, 437),
        (1, 254, 1, 2, 252, 4, 0, 256, 2, 459),
    ];
    /// (e_ca, e_cb, e_a, e_b, kind: 0 active 1 drain 2 frozen)
    pub(super) const ROLE2_ROWS: &[(u16, u16, u16, u16, u8)] = &[
        (4, 4, 253, 251, 0),
        (4, 4, 249, 251, 0),
        (9, 9, 247, 247, 0),
        (9, 9, 245, 247, 0),
        (13, 13, 243, 242, 0),
        (13, 13, 240, 242, 0),
        (0, 1, 256, 255, 0),
        (0, 1, 253, 255, 0),
        (1, 2, 255, 253, 0),
        (1, 2, 253, 253, 0),
        (2, 4, 253, 253, 0),
        (2, 4, 251, 253, 0),
        (255, 248, 0, 1, 1),
        (255, 254, 0, 1, 1),
        (255, 253, 0, 1, 1),
        (255, 252, 0, 1, 1),
        (248, 254, 0, 1, 1),
        (254, 254, 0, 1, 1),
        (248, 248, 0, 1, 1),
        (251, 248, 0, 1, 1),
        (256, 254, 0, 1, 2),
    ];
}

// ------------------------------------------------------------- harness

struct Fields {
    names: Vec<&'static str>,
    widths: Vec<usize>,
}

impl Fields {
    fn new(spec: &[(&'static str, usize)]) -> Self {
        let total: usize = spec.iter().map(|s| s.1).sum();
        assert!(total <= 64, "Fields: {total} bits do not fit the 64-bit harness word");
        Self { names: spec.iter().map(|s| s.0).collect(), widths: spec.iter().map(|s| s.1).collect() }
    }
    fn total(&self) -> usize {
        self.widths.iter().sum()
    }
    fn index(&self, name: &str) -> usize {
        self.names.iter().position(|n| *n == name).unwrap_or_else(|| panic!("no field {name}"))
    }
    fn off(&self, name: &str) -> usize {
        self.widths[..self.index(name)].iter().sum()
    }
    fn get(&self, word: u64, name: &str) -> u64 {
        let w = self.widths[self.index(name)];
        (word >> self.off(name)) & ((1u64 << w) - 1)
    }
    fn set(&self, word: u64, name: &str, v: u64) -> u64 {
        let w = self.widths[self.index(name)];
        let mask = ((1u64 << w) - 1) << self.off(name);
        (word & !mask) | ((v << self.off(name)) & mask)
    }
    fn pack(&self, vals: &[(&str, u64)]) -> u64 {
        vals.iter().fold(0u64, |acc, (n, v)| self.set(acc, n, *v))
    }
    fn alloc(&self, c: &mut Circuit) -> (Vec<Vec<QReg>>, Vec<QubitId>) {
        let mut regs = Vec::new();
        let mut ids = Vec::new();
        for (name, &w) in self.names.iter().zip(&self.widths) {
            let r = c.alloc_qreg_bits(&format!("t.{name}"), w);
            ids.extend(r.iter().map(|q| QubitId(q.id().into())));
            regs.push(r);
        }
        (regs, ids)
    }
}

struct Built {
    ops: Vec<Op>,
    ids: Vec<QubitId>,
    t: usize,
    /// Peak live qubits above the data registers (the op's scratch high-water mark).
    scratch_peak: usize,
}

fn build(fields: &Fields, body: impl FnOnce(&mut Circuit, &[Vec<QReg>])) -> Built {
    let mut c = Circuit::new();
    let (regs, ids) = fields.alloc(&mut c);
    body(&mut c, &regs);
    c.flush_pending_frees();
    let ops = c.b.ops.clone();
    let t = ops.iter().filter(|op| matches!(op.kind, OperationType::CCX | OperationType::CCZ)).count();
    let scratch_peak = (c.b.peak_qubits as usize).saturating_sub(ids.len());
    Built { ops, ids, t, scratch_peak }
}

fn apply(built: &Built, inputs: &[u64]) -> Vec<u64> {
    assert!(!inputs.is_empty() && inputs.len() <= 64);
    let (nq, nb, _, _) = analyze_ops(built.ops.iter());
    let nq = (nq as usize).max(built.ids.iter().map(|q| q.0 as usize + 1).max().unwrap_or(0));
    let mut seed = Shake256::default();
    seed.update(b"packed-exponent-arith-selftest-v1");
    seed.update(&inputs[0].to_le_bytes());
    seed.update(&(inputs.len() as u64).to_le_bytes());
    let mut rng = seed.finalize_xof();
    let mut sim = Simulator::new(nq, nb as usize + 1, &mut rng);
    for (bit, &id) in built.ids.iter().enumerate() {
        for (shot, &v) in inputs.iter().enumerate() {
            *sim.qubit_mut(id) |= ((v >> bit) & 1) << shot;
        }
    }
    let mask = u64::MAX >> (64 - inputs.len());
    super::super::super::predicate_clear_selftest::checked_apply(&mut sim, &built.ops, mask);
    assert_eq!(sim.phase & mask, 0, "phase mismatch");
    let out: Vec<u64> = (0..inputs.len())
        .map(|shot| {
            built.ids.iter().enumerate().fold(0u64, |acc, (bit, &id)| acc | (((sim.qubit(id) >> shot) & 1) << bit))
        })
        .collect();
    for &id in &built.ids {
        *sim.qubit_mut(id) = 0;
    }
    assert!(sim.qubits.iter().all(|v| v & mask == 0), "dirty scratch");
    out
}

/// Forward on `inputs`, check each output against `expect(input)`, then the
/// inverse circuit on the outputs must give the inputs back. Returns cases.
fn check_pair(name: &str, fwd: &Built, inv: &Built, inputs: &[u64], expect: &dyn Fn(u64) -> u64) -> usize {
    let mut cases = 0;
    for batch in inputs.chunks(64) {
        let out = apply(fwd, batch);
        for (&x, &y) in batch.iter().zip(&out) {
            assert_eq!(y, expect(x), "{name}: forward value mismatch on input {x:#x}");
        }
        let back = apply(inv, &out);
        assert_eq!(back, batch, "{name}: inverse does not restore");
        cases += batch.len();
    }
    cases
}

fn all_inputs(bits: usize) -> Vec<u64> {
    (0..1u64 << bits).collect()
}

fn lcg(seed: &mut u64) -> u64 {
    *seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
    *seed >> 11
}

fn report(name: &str, t: usize, cases: usize) {
    if t == 0 && name.contains("per k") {
        eprintln!("PACKED_EXPONENT_ARITH PASS: {name} cases={cases}");
    } else {
        eprintln!("PACKED_EXPONENT_ARITH PASS: {name:<44} T={t:<5} cases={cases}");
    }
}

// ---------------------------------------------------------------- tests

fn test_add_sub(n: usize) -> usize {
    let f = Fields::new(&[("a", n), ("b", n)]);
    let add = build(&f, |c, r| add_reg(c, &r[0], &r[1]));
    let sub = build(&f, |c, r| sub_reg(c, &r[0], &r[1]));
    let m = (1u64 << n) - 1;
    let inputs = all_inputs(f.total());
    let cases = check_pair("add_reg", &add, &sub, &inputs, &|x| {
        f.set(x, "a", (f.get(x, "a") + f.get(x, "b")) & m)
    });
    check_pair("sub_reg", &sub, &add, &inputs, &|x| {
        f.set(x, "a", (f.get(x, "a").wrapping_sub(f.get(x, "b"))) & m)
    });
    report(&format!("add_reg/sub_reg {n}-bit"), add.t, cases);
    assert_eq!(add.t, sub.t);
    cases
}

fn test_ctrl_add(n: usize, m: usize) -> usize {
    let f = Fields::new(&[("g", 1), ("a", n), ("b", m)]);
    let add = build(&f, |c, r| ctrl_add_reg(c, &r[0][0], &r[1], &r[2]));
    let sub = build(&f, |c, r| ctrl_sub_reg(c, &r[0][0], &r[1], &r[2]));
    let mask = (1u64 << n) - 1;
    let inputs = all_inputs(f.total());
    let cases = check_pair("ctrl_add_reg", &add, &sub, &inputs, &|x| {
        f.set(x, "a", (f.get(x, "a") + f.get(x, "g") * f.get(x, "b")) & mask)
    });
    check_pair("ctrl_sub_reg", &sub, &add, &inputs, &|x| {
        f.set(x, "a", (f.get(x, "a").wrapping_sub(f.get(x, "g") * f.get(x, "b"))) & mask)
    });
    report(&format!("ctrl_add_reg/ctrl_sub_reg {n}+={m}-bit"), add.t, cases);
    cases
}

fn test_add_const(n: usize, ks: &[i64]) -> usize {
    let f = Fields::new(&[("a", n)]);
    let mask = (1u64 << n) - 1;
    let inputs = all_inputs(n);
    let mut total = 0;
    let mut ts = Vec::new();
    for &k in ks {
        let fwd = build(&f, |c, r| add_const(c, &r[0], k));
        let inv = build(&f, |c, r| add_const(c, &r[0], -k));
        total += check_pair("add_const", &fwd, &inv, &inputs, &|x| {
            (x as i64).wrapping_add(k).rem_euclid(1i64 << n) as u64 & mask
        });
        ts.push(format!("{k}:{}", fwd.t));
    }
    report(&format!("add_const {n}-bit (rebase) T per k [{}]", ts.join(" ")), 0, total);
    total
}

fn test_ctrl_add_const(n: usize, ks: &[i64]) -> usize {
    let f = Fields::new(&[("g", 1), ("a", n)]);
    let inputs = all_inputs(f.total());
    let mut total = 0;
    let mut ts = Vec::new();
    for &k in ks {
        let fwd = build(&f, |c, r| ctrl_add_const(c, &r[0][0], &r[1], k));
        let inv = build(&f, |c, r| ctrl_add_const(c, &r[0][0], &r[1], -k));
        let vandaele = build(&f, |c, r| ctrl_add_const_vandaele(c, &r[0][0], &r[1], k));
        let expect = |x: u64| {
            let a = f.get(x, "a") as i64;
            let g = f.get(x, "g") as i64;
            f.set(x, "a", (a + g * k).rem_euclid(1i64 << n) as u64)
        };
        total += check_pair("ctrl_add_const", &fwd, &inv, &inputs, &expect);
        total += check_pair("ctrl_add_const_vandaele", &vandaele, &inv, &inputs, &expect);
        ts.push(format!("{k}:{}/{}", fwd.t, vandaele.t));
    }
    report(&format!("ctrl_add_const {n}-bit T per k naf/vandaele [{}]", ts.join(" ")), 0, total);
    total
}

fn test_ctrl_inc_dec(n: usize) -> usize {
    let f = Fields::new(&[("g", 1), ("a", n)]);
    let inc = build(&f, |c, r| ctrl_inc(c, &r[0][0], &r[1]));
    let dec = build(&f, |c, r| ctrl_dec(c, &r[0][0], &r[1]));
    let mask = (1u64 << n) - 1;
    let inputs = all_inputs(f.total());
    let cases = check_pair("ctrl_inc", &inc, &dec, &inputs, &|x| f.set(x, "a", (f.get(x, "a") + f.get(x, "g")) & mask));
    check_pair("ctrl_dec", &dec, &inc, &inputs, &|x| f.set(x, "a", f.get(x, "a").wrapping_sub(f.get(x, "g")) & mask));
    report(&format!("ctrl_inc/ctrl_dec {n}-bit"), inc.t, cases);
    cases
}

fn test_xor_diff_low(n: usize, w: usize) -> usize {
    let f = Fields::new(&[("gate", 1), ("ea", n), ("eb", n), ("shift", w)]);
    let b = build(&f, |c, r| xor_diff_low(c, &r[0][0], &r[1], &r[2], &r[3]));
    let inputs = all_inputs(f.total());
    let cases = check_pair("xor_diff_low", &b, &b, &inputs, &|x| {
        let diff = f.get(x, "ea").wrapping_sub(f.get(x, "eb")) & ((1u64 << n) - 1);
        let low = diff & ((1u64 << w) - 1);
        f.set(x, "shift", f.get(x, "shift") ^ (f.get(x, "gate") * low))
    });
    report(&format!("xor_diff_low (D1/M12) {n}-bit -> {w}-bit"), b.t, cases);
    cases
}

fn test_deposit(n: usize, w: usize) -> usize {
    let f = Fields::new(&[("gate", 1), ("eca", n), ("ecb", n), ("shift", w), ("carry", 1)]);
    let dep = build(&f, |c, r| deposit_sum(c, &r[0][0], &r[1], &r[2], &r[3], &r[4][0]));
    let undep = build(&f, |c, r| undeposit_sum(c, &r[0][0], &r[1], &r[2], &r[3], &r[4][0]));
    let mask = (1u64 << n) - 1;
    let inputs = all_inputs(f.total());
    let cases = check_pair("deposit_sum", &dep, &undep, &inputs, &|x| {
        let g = f.get(x, "gate");
        if g == 0 {
            return x;
        }
        let v = ((f.get(x, "eca") ^ f.get(x, "ecb")) + f.get(x, "shift") + f.get(x, "carry")) & mask;
        f.set(x, "eca", v)
    });
    report(&format!("deposit_sum/undeposit_sum (M6') {n}-bit, shift {w}"), dep.t, cases);
    cases
}

fn test_max(n: usize) -> usize {
    let f = Fields::new(&[("ex", n), ("ey", n), ("flag", 1)]);
    let fwd = build(&f, |c, r| max_into_second(c, &r[0], &r[1], &r[2][0]));
    let inv = build(&f, |c, r| unmax_into_second(c, &r[0], &r[1], &r[2][0]));
    let inputs = all_inputs(f.total());
    let cases = check_pair("max_into_second", &fwd, &inv, &inputs, &|x| {
        let (ex, ey, fl) = (f.get(x, "ex"), f.get(x, "ey"), f.get(x, "flag"));
        let fl2 = fl ^ u64::from(ex >= ey);
        let (nx, ny) = if fl2 == 1 { (ey, ex) } else { (ex, ey) };
        f.pack(&[("ex", nx), ("ey", ny), ("flag", fl2)])
    });
    report(&format!("max_into_second/unmax (role max-by-cswap) {n}-bit"), fwd.t, cases);
    cases
}

fn test_off_update(n: usize) -> usize {
    let f = Fields::new(&[("gate", 1), ("off", 1), ("ea", n)]);
    let fwd = build(&f, |c, r| off_update(c, &r[0][0], &r[1][0], &r[2]));
    let inv = build(&f, |c, r| off_update_inverse(c, &r[0][0], &r[1][0], &r[2]));
    let mask = (1u64 << n) - 1;
    let inputs = all_inputs(f.total());
    let cases = check_pair("off_update", &fwd, &inv, &inputs, &|x| {
        f.set(x, "ea", f.get(x, "ea").wrapping_sub(f.get(x, "gate") & f.get(x, "off")) & mask)
    });
    report(&format!("off_update (D7b) {n}-bit"), fwd.t, cases);
    cases
}

fn test_drop_update(n: usize, p: usize) -> usize {
    let f = Fields::new(&[("gate", 1), ("ea", n), ("pos", p)]);
    let fwd = build(&f, |c, r| drop_update(c, &r[0][0], &r[1], &r[2]));
    let inv = build(&f, |c, r| drop_update_inverse(c, &r[0][0], &r[1], &r[2]));
    let inputs = all_inputs(f.total());
    let cases = check_pair("drop_update", &fwd, &inv, &inputs, &|x| {
        let g = f.get(x, "gate") as i64;
        let v = (f.get(x, "ea") as i64 + g * (f.get(x, "pos") as i64 - 31)).rem_euclid(1i64 << n);
        f.set(x, "ea", v as u64)
    });
    report(&format!("drop_update (D11 e_A += g*(pos-31)) {n}-bit, pos {p}"), fwd.t, cases);
    cases
}

fn test_terminal_override(n: usize, p: usize, w: usize) -> usize {
    let f = Fields::new(&[("term", 1), ("ea", n), ("pos", p), ("shift", w)]);
    let fwd = build(&f, |c, r| terminal_override(c, &r[0][0], &r[1], &r[2], &r[3]));
    let inv = build(&f, |c, r| terminal_override_inverse(c, &r[0][0], &r[1], &r[2], &r[3]));
    let inputs = all_inputs(f.total());
    let cases = check_pair("terminal_override", &fwd, &inv, &inputs, &|x| {
        let t = f.get(x, "term") as i64;
        let v = (f.get(x, "ea") as i64 + t * (30 - f.get(x, "pos") as i64 - f.get(x, "shift") as i64)).rem_euclid(1i64 << n);
        f.set(x, "ea", v as u64)
    });
    report(&format!("terminal_override (D11t) {n}-bit, pos {p}, shift {w}"), fwd.t, cases);
    cases
}

fn test_load_affine(n: usize, tw: usize, k: i64, negate: bool) -> usize {
    let f = Fields::new(&[("e", n), ("t", tw)]);
    let fwd = build(&f, |c, r| load_affine(c, &r[0], &r[1], k, negate));
    let inv = build(&f, |c, r| unload_affine(c, &r[0], &r[1], k, negate));
    let inputs = all_inputs(f.total());
    let m = 1i64 << tw;
    let cases = check_pair("load_affine", &fwd, &inv, &inputs, &|x| {
        let e = (f.get(x, "e") as i64) & (m - 1);
        let t = f.get(x, "t") as i64;
        // t = 0 gives the amount; any t is the XOR-copy then the add.
        let copied = t ^ e;
        let v = if negate { (k - copied).rem_euclid(m) } else { (copied + k).rem_euclid(m) };
        f.set(x, "t", v as u64)
    });
    report(&format!("load_affine/unload_affine t{tw} := {}{} (e{n})", if negate { format!("{k} - e") } else { format!("e + {k}") }, ""), fwd.t, cases);
    cases
}

fn test_predicates(n: usize) -> usize {
    let f = Fields::new(&[("e", n), ("out", 1)]);
    let inputs = all_inputs(f.total());
    let mut total = 0;
    for k in [0usize, 1, 5, 256, 511] {
        let b = build(&f, |c, r| xor_eq_const(c, &r[0], k, &r[1][0]));
        total += check_pair("xor_eq_const", &b, &b, &inputs, &|x| {
            f.set(x, "out", f.get(x, "out") ^ u64::from(f.get(x, "e") as usize == k))
        });
        if k == 1 {
            report(&format!("xor_eq_const [e == 1] (eq1 root) {n}-bit"), b.t, inputs.len());
        }
    }
    let nz = build(&f, |c, r| xor_nonzero(c, &r[0], &r[1][0]));
    total += check_pair("xor_nonzero", &nz, &nz, &inputs, &|x| f.set(x, "out", f.get(x, "out") ^ u64::from(f.get(x, "e") != 0)));
    let z = build(&f, |c, r| xor_is_zero(c, &r[0], &r[1][0]));
    total += check_pair("xor_is_zero", &z, &z, &inputs, &|x| f.set(x, "out", f.get(x, "out") ^ u64::from(f.get(x, "e") == 0)));
    report(&format!("xor_nonzero (a_nonzero = OR(e_A)) / xor_is_zero {n}-bit"), nz.t, total);
    total
}

/// Classical `term` predicate with the pruning rule of `term_toggle`.
fn term_expected(gate: u64, e_b: u64, shift: u64, a_win: u64, n: usize) -> u64 {
    if gate == 0 || e_b != 1 || shift as usize > n {
        return 0;
    }
    u64::from(a_win & ((1u64 << shift) - 1) == 0)
}

fn test_term(n: usize, eb: usize, w: usize, exhaustive: bool) -> usize {
    let f = Fields::new(&[("gate", 1), ("eb", eb), ("shift", w), ("awin", n), ("term", 1)]);
    let b = build(&f, |c, r| term_toggle(c, &r[0][0], &r[1], &r[2], &r[3], &r[4][0]));
    let inputs: Vec<u64> = if exhaustive {
        all_inputs(f.total())
    } else {
        let mut seed = 0x9e3779b97f4a7c15u64 ^ (n as u64);
        let mut v = Vec::new();
        for _ in 0..4096 {
            v.push(lcg(&mut seed) & ((1u64 << f.total()) - 1));
        }
        // structured: e_b = 1, gate = 1, A = 2^s and 2^s + low garbage, every shift
        for s in 0..(1u64 << w) {
            for low in [0u64, 1, 3, (1u64 << s.min(n as u64)) - 1] {
                let a = if (s as usize) < n { (1u64 << s) | (low & ((1u64 << s) - 1)) } else { low };
                for term in 0..2u64 {
                    v.push(f.pack(&[("gate", 1), ("eb", 1), ("shift", s), ("awin", a & ((1u64 << n) - 1)), ("term", term)]));
                    v.push(f.pack(&[("gate", 0), ("eb", 1), ("shift", s), ("awin", a & ((1u64 << n) - 1)), ("term", term)]));
                    v.push(f.pack(&[("gate", 1), ("eb", 2), ("shift", s), ("awin", a & ((1u64 << n) - 1)), ("term", term)]));
                }
            }
        }
        v
    };
    let cases = check_pair("term_toggle", &b, &b, &inputs, &|x| {
        let t = term_expected(f.get(x, "gate"), f.get(x, "eb"), f.get(x, "shift"), f.get(x, "awin"), n);
        f.set(x, "term", f.get(x, "term") ^ t)
    });
    report(&format!("term_toggle (D0) window {n}, e_B {eb}-bit, shift {w}-bit{} scratch_peak={}", if exhaustive { " exhaustive" } else { "" }, b.scratch_peak), b.t, cases);
    // eq1 + root + one cursor level per shift bit + KG ancillae + one capture flag.
    if n > 0 {
        let kg = kg_prefix_compact_ancilla_count(n);
        assert!(b.scratch_peak <= 2 + w + kg + 1, "term_toggle scratch {} exceeds 2 + {w} + {kg} + 1", b.scratch_peak);
    }
    cases
}

fn test_offset(n: usize, w: usize) -> usize {
    let f = Fields::new(&[("off", 1), ("shift", w), ("eb", n)]);
    let fwd = build(&f, |c, r| offset_apply(c, &r[0][0], &r[1], &r[2]));
    let inv = build(&f, |c, r| offset_apply_inverse(c, &r[0][0], &r[1], &r[2]));
    let inputs = all_inputs(f.total());
    let cases = check_pair("offset_apply", &fwd, &inv, &inputs, &|x| {
        let off = f.get(x, "off");
        let x = f.set(x, "shift", f.get(x, "shift").wrapping_sub(off) & ((1u64 << w) - 1));
        f.set(x, "eb", (f.get(x, "eb") + off) & ((1u64 << n) - 1))
    });
    let rel = build(&f, |c, r| offset_release(c, &r[0][0], &r[2]));
    let rel_inv = build(&f, |c, r| offset_release_inverse(c, &r[0][0], &r[2]));
    check_pair("offset_release", &rel, &rel_inv, &inputs, &|x| {
        f.set(x, "eb", f.get(x, "eb").wrapping_sub(f.get(x, "off")) & ((1u64 << n) - 1))
    });
    report(&format!("offset_apply (D6) {w}/{n}-bit; offset_release (D6') T={}", rel.t), fwd.t, cases);
    cases
}

fn test_gap(n: usize, p: usize) -> usize {
    let f = Fields::new(&[("g", 1), ("eca", n), ("eb", n), ("pos", p)]);
    let fwd = build(&f, |c, r| gap_erase(c, &r[0][0], &r[1], &r[2], &r[3]));
    let inv = build(&f, |c, r| gap_deposit(c, &r[0][0], &r[1], &r[2], &r[3]));
    let inputs = all_inputs(f.total());
    let cases = check_pair("gap_erase", &fwd, &inv, &inputs, &|x| {
        let g = f.get(x, "g") as i64;
        let v = (f.get(x, "eca") as i64 - g * (257 - f.get(x, "eb") as i64 - f.get(x, "pos") as i64)).rem_euclid(1i64 << n);
        f.set(x, "eca", v as u64)
    });
    report(&format!("gap_erase/gap_deposit (M1 e_ca -= g*(257-e_B-pos)) {n}-bit, pos {p}"), fwd.t, cases);
    cases
}

/// The exponent bookkeeping of one division row on real model states:
/// D1, D0, D6, D7b, D6', D11 (deposit modelled as the `pos` input), D11t,
/// D0-clear, and the mirrored inverse. Checks `e_A_new = e_A - d`, `shift = s`,
/// `term = 0` at the end, and that the inverse restores every input.
fn test_division_rows() -> usize {
    let f = Fields::new(&[("gate", 1), ("ea", 9), ("eb", 9), ("shift", 5), ("off", 1), ("pos", 6), ("term", 1), ("awin", 28)]);
    let fwd = build(&f, |c, r| {
        let (gate, ea, eb, shift, off, pos, term, awin) = (&r[0][0], &r[1], &r[2], &r[3], &r[4][0], &r[5], &r[6][0], &r[7]);
        xor_diff_low(c, gate, ea, eb, shift); // D1: shift = s_raw
        term_toggle(c, gate, eb, shift, awin, term); // D0 (after D1, LSB frame)
        offset_apply(c, off, shift, eb); // D6: s, E
        off_update(c, gate, off, ea); // D7b
        offset_release(c, off, eb); // D6': e_B (before D9 clears off)
        drop_update(c, gate, ea, pos); // D11: e_A += pos - 31
        terminal_override(c, term, ea, pos, shift); // D11t
        term_toggle(c, gate, eb, shift, awin, term); // D0-clear (after D10, before D12)
    });
    let inv = build(&f, |c, r| {
        let (gate, ea, eb, shift, off, pos, term, awin) = (&r[0][0], &r[1], &r[2], &r[3], &r[4][0], &r[5], &r[6][0], &r[7]);
        term_toggle(c, gate, eb, shift, awin, term);
        terminal_override_inverse(c, term, ea, pos, shift);
        drop_update_inverse(c, gate, ea, pos);
        offset_release_inverse(c, off, eb);
        off_update_inverse(c, gate, off, ea);
        offset_apply_inverse(c, off, shift, eb);
        term_toggle(c, gate, eb, shift, awin, term);
        xor_diff_low(c, gate, ea, eb, shift);
    });
    let mut inputs = Vec::new();
    let mut want = Vec::new();
    for &(ea, eb, off, d, s_raw, a_low, term) in rows::DIV_ROWS.iter().chain(rows::TERM_ROWS) {
        let (ea, eb, off, d, s_raw) = (u64::from(ea), u64::from(eb), u64::from(off), u64::from(d), u64::from(s_raw));
        let s = s_raw - off;
        // pos = k = 31 + off - d on normal rows; garbage on the terminal row.
        let pos = if term == 1 { 17 } else { 31 + off - d };
        assert!(d <= 31 + off, "row outside drop_bound");
        inputs.push(f.pack(&[("gate", 1), ("ea", ea), ("eb", eb), ("shift", 0), ("off", off), ("pos", pos), ("term", 0), ("awin", u64::from(a_low))]));
        let ea_new = if term == 1 { 0 } else { ea - d };
        want.push(f.pack(&[("gate", 1), ("ea", ea_new), ("eb", eb), ("shift", s), ("off", off), ("pos", pos), ("term", 0), ("awin", u64::from(a_low))]));
        // the same row with gate = 0 must be a no-op (off = 0 there: D4's capture is
        // rooted at the gate, so an inactive row never carries off = 1 into D6).
        inputs.push(f.pack(&[("gate", 0), ("ea", ea), ("eb", eb), ("shift", 0), ("off", 0), ("pos", pos), ("term", 0), ("awin", u64::from(a_low))]));
        want.push(*inputs.last().unwrap());
    }
    let mut cases = 0;
    for (batch, w) in inputs.chunks(64).zip(want.chunks(64)) {
        let out = apply(&fwd, batch);
        for ((&x, &y), &z) in batch.iter().zip(&out).zip(w) {
            assert_eq!(y, z, "division row mismatch: in {x:#x} got {y:#x} want {z:#x} (e_A {} -> {}, want {})", f.get(x, "ea"), f.get(y, "ea"), f.get(z, "ea"));
        }
        assert_eq!(apply(&inv, &out), batch, "division row inverse");
        cases += batch.len();
    }
    // Term must stay 0 on non-division rows with e_B = 1 (draining / frozen / multiply).
    let tt = Fields::new(&[("gate", 1), ("eb", 9), ("shift", 5), ("awin", 28), ("term", 1)]);
    let tb = build(&tt, |c, r| term_toggle(c, &r[0][0], &r[1], &r[2], &r[3], &r[4][0]));
    let nd: Vec<u64> = rows::NONDIV_ROWS.iter().map(|&(_, a, _, eb, sh)| tt.pack(&[("gate", 0), ("eb", u64::from(eb)), ("shift", u64::from(sh)), ("awin", u64::from(a)), ("term", 0)])).collect();
    let out = apply(&tb, &nd);
    assert_eq!(out, nd, "term toggled on a non-division row");
    cases += nd.len();
    report(&format!("division rows D1..D0-clear on {} real model rows (+{} non-division)", inputs.len(), nd.len()), fwd.t, cases);
    cases
}

/// Multiply exponent bookkeeping on real rows: M6' deposit, M8, M12 (shift -> 0).
fn test_multiply_rows() -> usize {
    let f = Fields::new(&[("gate", 1), ("eca", 9), ("ecb", 9), ("shift", 5), ("carry", 1)]);
    let fwd = build(&f, |c, r| {
        let (gate, eca, ecb, shift, carry) = (&r[0][0], &r[1], &r[2], &r[3], &r[4][0]);
        deposit_sum(c, gate, eca, ecb, shift, carry); // M6'
        ctrl_inc(c, carry, shift); // M8: D = s2 + carry
        xor_diff_low(c, gate, eca, ecb, shift); // M12: shift ^= e_ca - e_cb = D -> 0
    });
    let inv = build(&f, |c, r| {
        let (gate, eca, ecb, shift, carry) = (&r[0][0], &r[1], &r[2], &r[3], &r[4][0]);
        xor_diff_low(c, gate, eca, ecb, shift);
        ctrl_dec(c, carry, shift);
        undeposit_sum(c, gate, eca, ecb, shift, carry);
    });
    let mut inputs = Vec::new();
    let mut want = Vec::new();
    for &(ecb, s2, carry, eca_new, _eca_old) in rows::MUL_ROWS {
        inputs.push(f.pack(&[("gate", 1), ("eca", 0), ("ecb", u64::from(ecb)), ("shift", u64::from(s2)), ("carry", u64::from(carry))]));
        want.push(f.pack(&[("gate", 1), ("eca", u64::from(eca_new)), ("ecb", u64::from(ecb)), ("shift", 0), ("carry", u64::from(carry))]));
    }
    let out = apply(&fwd, &inputs);
    assert_eq!(out, want, "multiply rows");
    assert_eq!(apply(&inv, &out), inputs, "multiply rows inverse");
    // Role max on real step-start exponents.
    let g = Fields::new(&[("eca", 9), ("ecb", 9), ("flag", 1)]);
    let mx = build(&g, |c, r| max_into_second(c, &r[0], &r[1], &r[2][0]));
    let un = build(&g, |c, r| unmax_into_second(c, &r[0], &r[1], &r[2][0]));
    let rin: Vec<u64> = rows::ROLE_ROWS.iter().map(|&(eca, ecb, _, _)| g.pack(&[("eca", u64::from(eca)), ("ecb", u64::from(ecb)), ("flag", 0)])).collect();
    let rout = apply(&mx, &rin);
    for (&x, &y) in rin.iter().zip(&rout) {
        let (a, b) = (g.get(x, "eca"), g.get(x, "ecb"));
        assert_eq!(g.get(y, "ecb"), a.max(b), "role max");
        assert_eq!(g.get(y, "eca"), a.min(b), "role min");
    }
    assert_eq!(apply(&un, &rout), rin, "role unmax");
    report(&format!("multiply rows M6'/M8/M12 on {} real rows + role max on {}", inputs.len(), rin.len()), fwd.t, inputs.len() + rin.len());
    inputs.len() + rin.len()
}

// ------------------------------------------------ adversarial review cases

/// The ladder identity behind `term_toggle`, layer by layer, on the design's
/// 28-window: for every shift s in 0..=28 the capture must read exactly
/// `AND(~A[0..s))` -- a single set bit at any position j < s must give 0, bits
/// at or above s must be ignored (0, all ones, random), and s in 29..31 is
/// pruned. `term` starts at 0 and at 1 (toggle).
fn test_term_ladder_identity(n: usize, w: usize) -> usize {
    let f = Fields::new(&[("gate", 1), ("eb", 9), ("shift", w), ("awin", n), ("term", 1)]);
    let b = build(&f, |c, r| term_toggle(c, &r[0][0], &r[1], &r[2], &r[3], &r[4][0]));
    let wm = (1u64 << n) - 1;
    let mut seed = 0xda3e_1234_5678_9abcu64 ^ (n as u64);
    let mut inputs = Vec::new();
    for s in 0..(1u64 << w) {
        let above = if (s as usize) < n { wm & !((1u64 << s) - 1) } else { 0 };
        let highs = [0u64, above, lcg(&mut seed) & above, lcg(&mut seed) & above];
        for &high in &highs {
            let mut lows = vec![0u64];
            if (s as usize) <= n {
                for j in 0..s.min(n as u64) {
                    lows.push(1u64 << j);
                }
                if s >= 1 {
                    lows.push((1u64 << s.min(n as u64)) - 1);
                }
            }
            for low in lows {
                for term in 0..2u64 {
                    for (gate, eb) in [(1u64, 1u64), (1, 0), (1, 3), (0, 1)] {
                        inputs.push(f.pack(&[("gate", gate), ("eb", eb), ("shift", s), ("awin", (high | low) & wm), ("term", term)]));
                    }
                }
            }
        }
    }
    let cases = check_pair("term_ladder_identity", &b, &b, &inputs, &|x| {
        let t = term_expected(f.get(x, "gate"), f.get(x, "eb"), f.get(x, "shift"), f.get(x, "awin"), n);
        f.set(x, "term", f.get(x, "term") ^ t)
    });
    report(&format!("term_toggle ladder identity per layer, window {n}, shift {w}-bit"), b.t, cases);
    cases
}

/// Mixed-width controlled adds at every (n, m) with m <= n for small n, and the
/// two 9-bit forms the author did not run (9 += 8: the carry fold is a 1-bit
/// cinc = CX; 9 += 7). Exhaustive.
fn test_ctrl_add_mixed_sweep() -> usize {
    let mut cases = 0;
    let mut ts = Vec::new();
    for n in 2..=6usize {
        for m in 1..=n {
            let f = Fields::new(&[("g", 1), ("a", n), ("b", m)]);
            let add = build(&f, |c, r| ctrl_add_reg(c, &r[0][0], &r[1], &r[2]));
            let sub = build(&f, |c, r| ctrl_sub_reg(c, &r[0][0], &r[1], &r[2]));
            let mask = (1u64 << n) - 1;
            let inputs = all_inputs(f.total());
            cases += check_pair("ctrl_add_reg sweep", &add, &sub, &inputs, &|x| {
                f.set(x, "a", (f.get(x, "a") + f.get(x, "g") * f.get(x, "b")) & mask)
            });
            cases += check_pair("ctrl_sub_reg sweep", &sub, &add, &inputs, &|x| {
                f.set(x, "a", (f.get(x, "a").wrapping_sub(f.get(x, "g") * f.get(x, "b"))) & mask)
            });
            ts.push(format!("{n}+={m}:{}", add.t));
        }
    }
    report(&format!("ctrl_add_reg/ctrl_sub_reg sweep n=2..6, m<=n T [{}]", ts.join(" ")), 0, cases);
    cases += test_ctrl_add(9, 8);
    cases += test_ctrl_add(9, 7);
    cases
}

/// The division exponent sequence on the review rows, with the VALUE WINDOW
/// CHANGING between D0 and D0-clear exactly as D7 changes it (`awin ^= delta`
/// by CX between D11t and the clear; on root rows delta = A ^ A_new differs
/// from 0 only at or above s, on every other row delta is arbitrary), plus
/// synthetic rows at the drop bound (d = 20, 24, 31 with off = 0; 24, 32 with
/// off = 1: k = 0 at the window bottom), the e_A = 256 step-0 rows, every
/// terminal s seen in the model, and the inactive twins (gate = 0, off = 0)
/// with a leftover `shift` on draining rows.
fn test_division_rows2() -> usize {
    // The window change `delta` is baked into each row's circuit as X gates (0 T):
    // the harness word is 64 bits and a second 28-bit register does not fit.
    let f = Fields::new(&[("gate", 1), ("ea", 9), ("eb", 9), ("shift", 5), ("off", 1), ("pos", 6), ("term", 1), ("awin", 28)]);
    let fwd = |delta: u64| {
        build(&f, |c, r| {
            let (gate, ea, eb, shift, off, pos, term, awin) = (&r[0][0], &r[1], &r[2], &r[3], &r[4][0], &r[5], &r[6][0], &r[7]);
            xor_diff_low(c, gate, ea, eb, shift); // D1
            term_toggle(c, gate, eb, shift, awin, term); // D0
            offset_apply(c, off, shift, eb); // D6
            off_update(c, gate, off, ea); // D7b
            offset_release(c, off, eb); // D6'
            drop_update(c, gate, ea, pos); // D11
            terminal_override(c, term, ea, pos, shift); // D11t
            for (j, a) in awin.iter().enumerate() {
                if (delta >> j) & 1 == 1 {
                    c.x(a); // D7's effect on the LSB-frame window
                }
            }
            term_toggle(c, gate, eb, shift, awin, term); // D0-clear
        })
    };
    let inv = |delta: u64| {
        build(&f, |c, r| {
            let (gate, ea, eb, shift, off, pos, term, awin) = (&r[0][0], &r[1], &r[2], &r[3], &r[4][0], &r[5], &r[6][0], &r[7]);
            term_toggle(c, gate, eb, shift, awin, term);
            for (j, a) in awin.iter().enumerate().rev() {
                if (delta >> j) & 1 == 1 {
                    c.x(a);
                }
            }
            terminal_override_inverse(c, term, ea, pos, shift);
            drop_update_inverse(c, gate, ea, pos);
            offset_release_inverse(c, off, eb);
            off_update_inverse(c, gate, off, ea);
            offset_apply_inverse(c, off, shift, eb);
            term_toggle(c, gate, eb, shift, awin, term);
            xor_diff_low(c, gate, ea, eb, shift);
        })
    };
    let m28 = (1u64 << 28) - 1;
    let mut seed = 0x5eed_0866_0000_0001u64;
    let mut rows: Vec<(u64, u64, u64, u64, u64, u64, u64, u64)> = Vec::new(); // (ea, eb, off, d, s_raw, a, a_new, term)
    for &(ea, eb, off, d, s_raw, a, a_new, term, _step) in rows2::DIV2_ROWS {
        rows.push((u64::from(ea), u64::from(eb), u64::from(off), u64::from(d), u64::from(s_raw), u64::from(a), u64::from(a_new), u64::from(term)));
    }
    // synthetic rows at the drop bound (a arbitrary: e_B != 1 so root = 0)
    for &(ea, eb, off, d) in &[(200u64, 180u64, 0u64, 20u64), (120, 100, 0, 24), (60, 40, 0, 31), (150, 130, 1, 24), (90, 70, 1, 32), (256, 228, 0, 28), (256, 227, 1, 28)] {
        let a = lcg(&mut seed) & m28;
        rows.push((ea, eb, off, d, ea - eb, a, lcg(&mut seed) & m28, 0));
    }
    // (delta, input, want)
    let mut cases_in: Vec<(u64, u64, u64)> = Vec::new();
    for &(ea, eb, off, d, s_raw, a, a_new, term) in &rows {
        assert!(d <= 31 + off && d >= 1, "row outside drop_bound");
        let s = s_raw - off;
        if eb == 1 {
            assert_eq!(off, 0, "B = 1 rows have off = 0");
            assert_eq!(a & ((1u64 << s) - 1), a_new & ((1u64 << s) - 1), "D7 must not touch the bits below s");
            assert_eq!(term, u64::from(a & ((1u64 << s) - 1) == 0 && (a >> s) == 1 && ea == s + 1), "term row consistency");
        }
        let pos = if term == 1 { 5 + (lcg(&mut seed) & 31) } else { 31 + off - d };
        let delta = a ^ a_new;
        let ea_new = if term == 1 { 0 } else { ea - d };
        cases_in.push((
            delta,
            f.pack(&[("gate", 1), ("ea", ea), ("eb", eb), ("shift", 0), ("off", off), ("pos", pos), ("term", 0), ("awin", a)]),
            f.pack(&[("gate", 1), ("ea", ea_new), ("eb", eb), ("shift", s), ("off", off), ("pos", pos), ("term", 0), ("awin", a_new)]),
        ));
        // inactive twin: gate = 0, off = 0 (D4 is rooted at the gate), any leftover shift
        // (draining rows see the multiply's cleared shift = 0; use a nonzero one too),
        // arbitrary delta (also below s: root = 0 must make it harmless).
        for sh in [0u64, (lcg(&mut seed) & 31)] {
            let dl = lcg(&mut seed) & m28;
            let x = f.pack(&[("gate", 0), ("ea", ea), ("eb", eb), ("shift", sh), ("off", 0), ("pos", pos), ("term", 0), ("awin", a)]);
            cases_in.push((dl, x, f.set(x, "awin", a ^ dl)));
        }
    }
    // draining / frozen rows: e_A = 0, e_B = 1, gate = 0, window all zero or garbage
    for &(_kind, a, ea, eb, sh) in rows::NONDIV_ROWS {
        for awin in [u64::from(a), lcg(&mut seed) & m28] {
            let dl = lcg(&mut seed) & m28;
            let x = f.pack(&[("gate", 0), ("ea", u64::from(ea)), ("eb", u64::from(eb)), ("shift", u64::from(sh)), ("off", 0), ("pos", 63), ("term", 0), ("awin", awin)]);
            cases_in.push((dl, x, f.set(x, "awin", awin ^ dl)));
        }
    }
    let mut cases = 0;
    let mut t = 0;
    let mut peak = 0;
    for &(delta, x, z) in &cases_in {
        let fb = fwd(delta);
        let ib = inv(delta);
        t = fb.t;
        peak = peak.max(fb.scratch_peak);
        let y = apply(&fb, &[x])[0];
        assert_eq!(y, z, "division row2 mismatch: in {x:#x} got {y:#x} want {z:#x} (e_A {} -> {}, want {}; term {})", f.get(x, "ea"), f.get(y, "ea"), f.get(z, "ea"), f.get(y, "term"));
        assert_eq!(apply(&ib, &[y]), vec![x], "division row2 inverse");
        cases += 1;
    }
    report(&format!("division rows2 D1..D0-clear with D7's window change, {} rows ({} real) scratch_peak={peak}", cases_in.len(), rows2::DIV2_ROWS.len()), t, cases);
    cases
}

/// The multiply exponent sequence on the review rows: M1's erase under
/// `g' = gate AND nz` (materialised and released here as the design does),
/// then M6', M8, M12; `e_ca` must end at `e_ca_new`, `shift` at 0, and on the
/// first multiply (ca_old = 0, nz = 0, pos = one of B's wrapped bits) `e_ca`
/// must pass through M1 untouched. Inactive twins (gate = 0: carry = 0 and
/// shift = 0 by the gated captures) must be no-ops for both nz values.
fn test_multiply_rows2() -> usize {
    let f = Fields::new(&[("gate", 1), ("nz", 1), ("eca", 9), ("eb", 9), ("pos", 6), ("ecb", 9), ("shift", 5), ("carry", 1)]);
    let fwd = build(&f, |c, r| {
        let (gate, nz, eca, eb, pos, ecb, shift, carry) = (&r[0][0], &r[1][0], &r[2], &r[3], &r[4], &r[5], &r[6], &r[7][0]);
        let g = c.alloc_qreg("t.gnz");
        c.ccx(gate, nz, &g);
        gap_erase(c, &g, eca, eb, pos); // M1 erase
        c.clear_and(&g, gate, nz);
        c.zero_and_free(g);
        deposit_sum(c, gate, eca, ecb, shift, carry); // M6'
        ctrl_inc(c, carry, shift); // M8
        xor_diff_low(c, gate, eca, ecb, shift); // M12
    });
    let inv = build(&f, |c, r| {
        let (gate, nz, eca, eb, pos, ecb, shift, carry) = (&r[0][0], &r[1][0], &r[2], &r[3], &r[4], &r[5], &r[6], &r[7][0]);
        xor_diff_low(c, gate, eca, ecb, shift);
        ctrl_dec(c, carry, shift);
        undeposit_sum(c, gate, eca, ecb, shift, carry);
        let g = c.alloc_qreg("t.gnz");
        c.ccx(gate, nz, &g);
        gap_deposit(c, &g, eca, eb, pos);
        c.clear_and(&g, gate, nz);
        c.zero_and_free(g);
    });
    let mut inputs = Vec::new();
    let mut want = Vec::new();
    for &(eb, eca_old, nz, pos, ecb, s2, carry, eca_new, kind, _step) in rows2::MUL2_ROWS {
        let (eb, eca_old, nz, pos, ecb, s2, carry, eca_new) = (u64::from(eb), u64::from(eca_old), u64::from(nz), u64::from(pos), u64::from(ecb), u64::from(s2), u64::from(carry), u64::from(eca_new));
        if nz == 1 {
            assert_eq!(eca_old, 257 - eb - pos, "gap row consistency");
        } else {
            assert_eq!(eca_old, 0, "first multiply has ca_old = 0");
            assert_eq!(kind, 1);
            assert!(pos == 63 || pos >= 257 - eb, "pos must be the sentinel or one of B's wrapped bits");
        }
        assert_eq!(eca_new, ecb + s2 + carry, "M6' theorem");
        inputs.push(f.pack(&[("gate", 1), ("nz", nz), ("eca", eca_old), ("eb", eb), ("pos", pos), ("ecb", ecb), ("shift", s2), ("carry", carry)]));
        want.push(f.pack(&[("gate", 1), ("nz", nz), ("eca", eca_new), ("eb", eb), ("pos", pos), ("ecb", ecb), ("shift", 0), ("carry", carry)]));
        for nz0 in 0..2u64 {
            let x = f.pack(&[("gate", 0), ("nz", nz0), ("eca", eca_old), ("eb", eb), ("pos", pos), ("ecb", ecb), ("shift", 0), ("carry", 0)]);
            inputs.push(x);
            want.push(x);
        }
    }
    let mut cases = 0;
    for (batch, w) in inputs.chunks(64).zip(want.chunks(64)) {
        let out = apply(&fwd, batch);
        for ((&x, &y), &z) in batch.iter().zip(&out).zip(w) {
            assert_eq!(y, z, "multiply row2 mismatch: in {x:#x} got {y:#x} want {z:#x} (e_ca {} -> {}, want {})", f.get(x, "eca"), f.get(y, "eca"), f.get(z, "eca"));
        }
        assert_eq!(apply(&inv, &out), batch, "multiply row2 inverse");
        cases += batch.len();
    }
    // Role max on the review step starts, incl. equal exponents, draining and frozen rows;
    // the rows also witness the role fact the capture leaf relies on.
    let g = Fields::new(&[("eca", 9), ("ecb", 9), ("flag", 1)]);
    let mx = build(&g, |c, r| max_into_second(c, &r[0], &r[1], &r[2][0]));
    let un = build(&g, |c, r| unmax_into_second(c, &r[0], &r[1], &r[2][0]));
    let mut rin = Vec::new();
    for &(eca, ecb, ea, eb, _kind) in rows2::ROLE2_ROWS {
        assert!(eca.max(ecb) <= 257 - ea.max(eb), "role fact");
        rin.push(g.pack(&[("eca", u64::from(eca)), ("ecb", u64::from(ecb)), ("flag", 0)]));
    }
    let rout = apply(&mx, &rin);
    for (&x, &y) in rin.iter().zip(&rout) {
        let (a, b) = (g.get(x, "eca"), g.get(x, "ecb"));
        assert_eq!(g.get(y, "ecb"), a.max(b), "role max");
        assert_eq!(g.get(y, "eca"), a.min(b), "role min");
        assert_eq!(g.get(y, "flag"), u64::from(a >= b), "role flag");
    }
    assert_eq!(apply(&un, &rout), rin, "role unmax");
    cases += rin.len();
    report(&format!("multiply rows2 M1-erase/M6'/M8/M12, {} rows ({} real) + role max on {}", inputs.len(), rows2::MUL2_ROWS.len(), rin.len()), fwd.t, cases);
    cases
}

/// Every constant of the NAF adders, not only the design's: `add_const` and
/// `ctrl_add_const` for all k mod 2^n at n = 5 and n = 7 (the rebase lever's
/// width), each exhaustive over the register (and the gate).
fn test_const_sweep(n: usize) -> usize {
    let mut cases = 0;
    let mut tmax = 0;
    let mut ctmax = 0;
    let f = Fields::new(&[("a", n)]);
    let g = Fields::new(&[("g", 1), ("a", n)]);
    let inputs = all_inputs(n);
    let ginputs = all_inputs(n + 1);
    let m = 1i64 << n;
    for k in -(m / 2)..m {
        let fwd = build(&f, |c, r| add_const(c, &r[0], k));
        let inv = build(&f, |c, r| add_const(c, &r[0], -k));
        cases += check_pair("add_const sweep", &fwd, &inv, &inputs, &|x| ((x as i64) + k).rem_euclid(m) as u64);
        tmax = tmax.max(fwd.t);
        let cf = build(&g, |c, r| ctrl_add_const(c, &r[0][0], &r[1], k));
        let ci = build(&g, |c, r| ctrl_add_const(c, &r[0][0], &r[1], -k));
        cases += check_pair("ctrl_add_const sweep", &cf, &ci, &ginputs, &|x| {
            g.set(x, "a", ((g.get(x, "a") as i64) + (g.get(x, "g") as i64) * k).rem_euclid(m) as u64)
        });
        ctmax = ctmax.max(cf.t);
    }
    report(&format!("add_const / ctrl_add_const every k, {n}-bit (max T {tmax} / {ctmax})"), 0, cases);
    cases
}

/// NEGATIVE: the harness must SEE the refuter's ordering bug. Run D0 before
/// D1 (shift = 0) on a real B = 1 row whose A is not a power of two: `term`
/// fires, D11t zeroes e_A, and the clear (now at shift = s) cannot undo it.
/// The mis-ordered circuit must disagree with the contract's result.
fn test_term_ordering_negative() -> usize {
    let f = Fields::new(&[("gate", 1), ("ea", 9), ("eb", 9), ("shift", 5), ("off", 1), ("pos", 6), ("term", 1), ("awin", 28)]);
    let bad = build(&f, |c, r| {
        let (gate, ea, eb, shift, off, pos, term, awin) = (&r[0][0], &r[1], &r[2], &r[3], &r[4][0], &r[5], &r[6][0], &r[7]);
        term_toggle(c, gate, eb, shift, awin, term); // D0 BEFORE D1: the bug
        xor_diff_low(c, gate, ea, eb, shift);
        offset_apply(c, off, shift, eb);
        off_update(c, gate, off, ea);
        offset_release(c, off, eb);
        drop_update(c, gate, ea, pos);
        terminal_override(c, term, ea, pos, shift);
        term_toggle(c, gate, eb, shift, awin, term);
    });
    // (10, 1, 0, 2, 9, 0x29f, ...) from rows2: A = 0x29f, B = 1, s = 9, d = 2, not terminal.
    let x = f.pack(&[("gate", 1), ("ea", 10), ("eb", 1), ("shift", 0), ("off", 0), ("pos", 29), ("term", 0), ("awin", 0x29f)]);
    let y = apply(&bad, &[x])[0];
    let good = f.pack(&[("gate", 1), ("ea", 8), ("eb", 1), ("shift", 9), ("off", 0), ("pos", 29), ("term", 0), ("awin", 0x29f)]);
    assert_ne!(y, good, "the mis-ordered D0 was not detected");
    assert_eq!(f.get(y, "term"), 1, "mis-ordered D0 leaves term dirty");
    assert_eq!(f.get(y, "ea"), 0, "mis-ordered D0 lets D11t zero e_A on a non-terminal row");
    report("NEGATIVE: D0 before D1 (shift = 0) is detected on a real B = 1 row", bad.t, 1);
    1
}

/// The 7-bit rebased lever: every composite op is width-generic; run the
/// division/multiply composites exhaustively at 7 bits (the constants 30, 31
/// and 257 are taken mod 128 here -- the lever's own constants are rebased by
/// the schedule, this checks the arithmetic identities only).
fn test_lever7() -> usize {
    let mut cases = 0;
    cases += test_off_update(7);
    cases += test_drop_update(7, 6);
    cases += test_terminal_override(7, 6, 5);
    cases += test_deposit(7, 5);
    cases += test_offset(7, 5);
    cases += test_gap(7, 6);
    cases += test_max(7);
    cases += test_ctrl_inc_dec(7);
    cases += test_predicates(7);
    cases
}

pub(super) fn run() {
    let mut cases = 0;
    {
        // Unit costs of the KG increment / controlled increment per width.
        let mut line = Vec::new();
        for m in 1..=10usize {
            let f = Fields::new(&[("a", m)]);
            let inc = build(&f, |c, r| add_const(c, &r[0], 1));
            let g = Fields::new(&[("g", 1), ("a", m)]);
            let cinc = build(&g, |c, r| ctrl_inc(c, &r[0][0], &r[1]));
            line.push(format!("{m}:{}/{}", inc.t, cinc.t));
        }
        eprintln!("PACKED_EXPONENT_ARITH unit T inc/cinc per width [{}]", line.join(" "));
    }
    cases += test_add_sub(9);
    cases += test_add_sub(7);
    cases += test_ctrl_add(9, 9);
    cases += test_ctrl_add(9, 6);
    cases += test_ctrl_add(9, 5);
    cases += test_ctrl_add(9, 1);
    cases += test_ctrl_add(7, 5);
    cases += test_add_const(9, &[1, -1, 30, -31, 31, 257, -257, 100, 127, 255, 256, 511]);
    cases += test_add_const(7, &[-3, 5, 64, -64, 127]);
    cases += test_ctrl_add_const(9, &[1, -1, 30, -30, -31, 31, 257, -257, 100, 255, 256]);
    cases += test_ctrl_add_const(7, &[-3, 5, 64]);
    cases += test_ctrl_inc_dec(9);
    cases += test_ctrl_inc_dec(5);
    cases += test_xor_diff_low(9, 5);
    cases += test_xor_diff_low(7, 5);
    cases += test_deposit(9, 5);
    cases += test_max(9);
    cases += test_offset(9, 5);
    cases += test_gap(9, 6);
    cases += test_off_update(9);
    cases += test_drop_update(9, 6);
    cases += test_terminal_override(9, 6, 5);
    cases += test_load_affine(9, 7, 76, true); // D11: t7 = W_A - e_B (W_A = 76 at step 378)
    cases += test_load_affine(9, 7, 256, true); // D11 at step 0
    cases += test_load_affine(9, 7, 0, false); // M1 with lo_B = 0
    cases += test_load_affine(9, 7, -40, false); // M1: t7 = e_B - lo_B, lo_B = 40
    cases += test_predicates(9);
    for n in [0usize, 1, 2, 3, 6] {
        cases += test_term(n, 3, 3, true);
    }
    cases += test_term(6, 9, 5, true);
    cases += test_term(28, 9, 5, false);
    cases += test_term(31, 9, 5, false);
    cases += test_term(33, 9, 5, false);
    if std::env::var_os("MIDQ_ONEHOT_COHERENT").is_none() {
        std::env::set_var("MIDQ_ONEHOT_COHERENT", "1");
        cases += test_term(6, 9, 5, true);
        cases += test_term(28, 9, 5, false);
        std::env::remove_var("MIDQ_ONEHOT_COHERENT");
    }
    cases += test_division_rows();
    cases += test_multiply_rows();
    // adversarial review cases (2026-09-13)
    cases += test_term_ladder_identity(28, 5);
    cases += test_ctrl_add_mixed_sweep();
    cases += test_division_rows2();
    cases += test_multiply_rows2();
    cases += test_lever7();
    cases += test_const_sweep(5);
    cases += test_const_sweep(7);
    cases += test_const_sweep(9);
    cases += test_term_ordering_negative();
    if std::env::var_os("MIDQ_ONEHOT_COHERENT").is_none() {
        std::env::set_var("MIDQ_ONEHOT_COHERENT", "1");
        cases += test_division_rows2();
        std::env::remove_var("MIDQ_ONEHOT_COHERENT");
    }
    eprintln!("PACKED_EXPONENT_ARITH PASS: {cases} value/phase/ancilla cases, forward and inverse");
}
