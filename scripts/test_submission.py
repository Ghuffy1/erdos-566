"""Regression checks for publication-path screening."""

from pathlib import Path
import unittest

from check_submission import PRIVATE_PATH


class PublicationPathTests(unittest.TestCase):
    def test_local_paths_are_detected(self):
        windows_upper = "C" + ":" + "\\".join(["", "Users", "example", "work"])
        windows_lower = "c" + ":" + "\\".join(["", "work", "file"])
        macos = "/".join(["", "Users", "example", "work"])
        linux = "/".join(["", "home", "example", "work"])
        for path in [windows_upper, windows_lower, macos, linux]:
            with self.subTest(path=path):
                self.assertIsNotNone(PRIVATE_PATH.search(path))

    def test_pattern_source_does_not_match_itself(self):
        for name in ["check_submission.py", "test_submission.py"]:
            source = Path(__file__).with_name(name).read_text(encoding="utf-8")
            self.assertIsNone(PRIVATE_PATH.search(source))


if __name__ == "__main__":
    unittest.main()
