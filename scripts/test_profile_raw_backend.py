"""Profile protocol boundaries; an interrupted trace never supplies a decision."""
import sys
from pathlib import Path
import unittest
import tempfile
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "experiments"))
from profile_raw_backend import parse_trace, run


class ProfileTraceTests(unittest.TestCase):
    def test_completed_false_answer_and_phase(self):
        trace = "\n".join([
            "SUBTAIL_RAW_PROFILE:input:controls:2",
            "SUBTAIL_RAW_PROFILE:begin:summary", "SUBTAIL_RAW_PROFILE:value:summary:false",
            "SUBTAIL_RAW_PROFILE:end:summary:12", "SUBTAIL_RAW_PROFILE:result:false",
        ])
        result = parse_trace(trace, True, False)
        self.assertEqual(result["status"], "PASS")
        self.assertEqual(result["phases"][0]["milliseconds"], 12)
        self.assertIs(result["actual"], False)

    def test_interruption_keeps_unfinished_phase(self):
        result = parse_trace("SUBTAIL_RAW_PROFILE:begin:cycle_candidates\n", False, False)
        self.assertEqual(result["status"], "UNKNOWN")
        self.assertEqual(result["unfinished_phase"], "cycle_candidates")
        self.assertNotIn("actual", result)

    def test_interruption_overrides_apparent_answer_or_partial_marker(self):
        for trace in ["SUBTAIL_RAW_PROFILE:result:false\n", "SUBTAIL_RAW_PROFILE:en"]:
            result = parse_trace(trace, False, False)
            self.assertEqual(result["status"], "UNKNOWN")
            self.assertNotIn("actual", result)

    def test_missing_duplicate_and_wrong_answers_fail(self):
        for trace in ["", "SUBTAIL_RAW_PROFILE:result:false\nSUBTAIL_RAW_PROFILE:result:false\n",
                      "SUBTAIL_RAW_PROFILE:result:true\n"]:
            self.assertEqual(parse_trace(trace, True, False)["status"], "FAIL")

    def test_phase_protocol_error_fails_on_completed_process(self):
        trace = "SUBTAIL_RAW_PROFILE:begin:cycle_candidates\nSUBTAIL_RAW_PROFILE:end:infinite_prefix_search:3\nSUBTAIL_RAW_PROFILE:result:false\n"
        self.assertEqual(parse_trace(trace, True, False)["status"], "FAIL")

    def test_bare_result_and_markers_after_result_fail(self):
        phase = ("SUBTAIL_RAW_PROFILE:input:controls:2\nSUBTAIL_RAW_PROFILE:begin:summary\n"
                 "SUBTAIL_RAW_PROFILE:value:summary:false\nSUBTAIL_RAW_PROFILE:end:summary:1\n")
        result = "SUBTAIL_RAW_PROFILE:result:false\n"
        for trace in [result, result + phase, phase + result + "SUBTAIL_RAW_PROFILE:input:controls:2\n",
                      phase + result + phase]:
            self.assertEqual(parse_trace(trace, True, False)["status"], "FAIL")

    def test_unknown_phase_and_duplicate_input_fail(self):
        trace = ("SUBTAIL_RAW_PROFILE:input:controls:2\nSUBTAIL_RAW_PROFILE:begin:summary\n"
                 "SUBTAIL_RAW_PROFILE:value:summary:false\nSUBTAIL_RAW_PROFILE:end:summary:1\n"
                 "SUBTAIL_RAW_PROFILE:result:false\n")
        for bad in [trace.replace("summary", "bogus"), "SUBTAIL_RAW_PROFILE:input:controls:2\n" + trace]:
            self.assertEqual(parse_trace(bad, True, False)["status"], "FAIL")

    def test_launch_error_is_unknown(self):
        with tempfile.TemporaryDirectory() as directory, \
             patch("profile_raw_backend.subprocess.Popen", side_effect=FileNotFoundError("missing tool")):
            result = run(Path(directory) / "test.lean", 1, False)
        self.assertEqual(result["status"], "UNKNOWN")
        self.assertEqual(result["reason"], "launch_error")
        self.assertNotIn("actual", result)

    def test_truncated_completed_output_is_rejected_and_tail_is_real(self):
        trace = ("SUBTAIL_RAW_PROFILE:input:controls:2\nSUBTAIL_RAW_PROFILE:begin:summary\n"
                 "SUBTAIL_RAW_PROFILE:value:summary:false\nSUBTAIL_RAW_PROFILE:end:summary:1\n"
                 "SUBTAIL_RAW_PROFILE:result:false\n" + "x" * 70000 + "REAL_TAIL")

        def launch(command, **kwargs):
            kwargs["stdout"].write(trace.encode())
            return SimpleNamespace(returncode=0, wait=lambda **kwargs: 0)

        with tempfile.TemporaryDirectory() as directory, patch("profile_raw_backend.subprocess.Popen", launch):
            result = run(Path(directory) / "test.lean", 1, False)
        self.assertEqual(result["status"], "FAIL")
        self.assertEqual(result["reason"], "trace_output_truncated")
        self.assertNotIn("actual", result)
        self.assertTrue(result["output_tail"].endswith("REAL_TAIL"))


if __name__ == "__main__":
    unittest.main()
