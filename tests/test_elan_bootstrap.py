"""A cached elan must match the selected installer before setup succeeds."""

import os
import subprocess
import tempfile
import unittest
from pathlib import Path


class ElanBootstrapTests(unittest.TestCase):
    def run_bootstrap(self, version: str, *, fail: bool = False):
        source = (Path(__file__).resolve().parents[1] / "setup.sh").read_text()
        function = source[source.index("ensure_elan() {") : source.index("\nRESOLVED_TEX_CMD=()")]
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            state = root / "version"
            calls = root / "calls"
            state.write_text(version)
            installed = root / "elan"
            installed.write_text('#!/bin/sh\nprintf "elan %s\\n" "$(cat "$ELAN_TEST_STATE")"\n')
            installer = root / "elan-init"
            installer.write_text(
                '#!/bin/sh\nif [ "$1" = --version ]; then printf "elan-init 4.2.4\\n"; exit; fi\n'
                'printf x >> "$ELAN_TEST_CALLS"\n'
                'if [ "$ELAN_TEST_FAIL" = 1 ]; then exit 1; fi\n'
                'printf 4.2.4 > "$ELAN_TEST_STATE"\n'
            )
            installed.chmod(0o755)
            installer.chmod(0o755)
            script = (
                'elan_bin() { printf "%s\\n" "$ELAN_TEST_INSTALLED"; }\n'
                'elan_init_bin() { printf "%s\\n" "$ELAN_TEST_INIT"; }\n'
                'run_cmd() { "$@"; }\nDRY_RUN=0\n' + function + "\nensure_elan\n"
            )
            env = dict(
                os.environ,
                ELAN_TEST_STATE=str(state),
                ELAN_TEST_CALLS=str(calls),
                ELAN_TEST_INSTALLED=str(installed),
                ELAN_TEST_INIT=str(installer),
                ELAN_TEST_FAIL="1" if fail else "0",
            )
            result = subprocess.run(["bash", "-c", script], env=env, capture_output=True, text=True, check=False)
            return result.returncode, state.read_text(), calls.read_text() if calls.exists() else ""

    def test_cached_old_manager_is_upgraded(self):
        self.assertEqual(self.run_bootstrap("4.2.1"), (0, "4.2.4", "x"))

    def test_current_manager_is_not_reinstalled(self):
        self.assertEqual(self.run_bootstrap("4.2.4"), (0, "4.2.4", ""))

    def test_failed_upgrade_does_not_accept_old_manager(self):
        self.assertEqual(self.run_bootstrap("4.2.1", fail=True), (1, "4.2.1", "x"))


if __name__ == "__main__":
    unittest.main()
