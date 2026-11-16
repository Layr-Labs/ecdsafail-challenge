//! lane maps and operand remapping of the expander kits
pub fn lane_map(raw: &[u8]) -> Vec<u16> { raw.chunks_exact(2).map(|p| u16::from_le_bytes([p[0], p[1]])).collect() }
pub fn remap(mut row: [u16; 4], lanes: &[u16]) -> [u16; 4] {
    let columns: &[usize] = match row[0] { 2 => &[2], 6 | 7 | 12 => &[1], 8 | 9 => &[1, 2], 13 => &[1, 2, 3], 1 | 3 | 4 | 5 | 15 | 16 | 18 => &[], _ => panic!("unknown opcode {}", row[0]) };
    for &column in columns { row[column] = lanes[row[column] as usize]; assert!(row[column] < 633); }
    row
}
pub fn rows_of(bytes: &[u8]) -> Vec<[u16; 4]> { bytes.chunks_exact(8).map(|c| [u16::from_le_bytes([c[0], c[1]]), u16::from_le_bytes([c[2], c[3]]), u16::from_le_bytes([c[4], c[5]]), u16::from_le_bytes([c[6], c[7]])]).collect() }
