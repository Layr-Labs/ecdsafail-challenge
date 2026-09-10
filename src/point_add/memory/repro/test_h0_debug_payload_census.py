from __future__ import annotations

import unittest

import h0_debug_payload_census as debug_payload
from h0_fixed_point_census import Scope


class DebugPrintPayloadCensusTests(unittest.TestCase):
    def test_reduced_payload_domain_is_complete_and_unique(self) -> None:
        records = tuple(debug_payload._payload_records(1))
        self.assertEqual(len(records), debug_payload.payload_state_count(1))
        self.assertEqual(len(records), 1_215)
        self.assertEqual(len(set(records)), len(records))
        self.assertTrue(all(len(record) == 49 for record in records))

    def test_small_exact_census_is_stable(self) -> None:
        report = debug_payload.census(Scope(1, 1))
        self.assertEqual(report["checked_pairs"], 19_440)
        self.assertEqual(report["successful_pairs"], 1_189)
        self.assertEqual(report["successful_tables"], 16)
        self.assertTrue(report["complete"])


if __name__ == "__main__":
    unittest.main()
