"""Profile protocol boundaries; a interrupted trace never supplies a decision."""
import sys
from pathlib import Path
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from profile_entailment import parse_trace


class ProfileTraceTests(unittest.TestCase):
    def test_completed_false_answer_and_phase(self):
        trace = "\n".join([
            "SUBTAIL_PROFILE:begin:positive", "SUBTAIL_PROFILE:value:positive:false",
            "SUBTAIL_PROFILE:end:positive:12", "SUBTAIL_PROFILE:result:false",
        ])
        result = parse_trace(trace, True, False)
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["phases"][0]["milliseconds"], 12)
        self.assertIs(result["actual"], False)

    def test_interruption_keeps_unfinished_phase(self):
        result = parse_trace("SUBTAIL_PROFILE:begin:forward\n", False, False)
        self.assertEqual(result["status"], "UNKNOWN")
        self.assertEqual(result["unfinished_phase"], "forward")
        self.assertNotIn("actual", result)

    def test_interruption_overrides_apparent_answer_or_partial_marker(self):
        for trace in ["SUBTAIL_PROFILE:result:false\n", "SUBTAIL_PROFILE:en"]:
            result = parse_trace(trace, False, False)
            self.assertEqual(result["status"], "UNKNOWN")
            self.assertNotIn("actual", result)

    def test_missing_duplicate_and_wrong_answers_fail(self):
        for trace in ["", "SUBTAIL_PROFILE:result:false\nSUBTAIL_PROFILE:result:false\n",
                      "SUBTAIL_PROFILE:result:true\n"]:
            self.assertEqual(parse_trace(trace, True, False)["status"], "FAIL")

    def test_phase_protocol_error_fails_on_completed_process(self):
        trace = "SUBTAIL_PROFILE:begin:forward\nSUBTAIL_PROFILE:end:backward:3\nSUBTAIL_PROFILE:result:false\n"
        self.assertEqual(parse_trace(trace, True, False)["status"], "FAIL")


if __name__ == "__main__":
    unittest.main()
