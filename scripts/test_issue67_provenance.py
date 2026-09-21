"""The native integration guard permits additions, never changes to pinned files."""
import importlib.util
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('issue67_native_probe', ROOT / 'experiments/issue67_native_probe.py')
PROBE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PROBE)


class ProvenanceTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.git('init', '-q')
        self.git('config', 'user.name', 'Fixture')
        self.git('config', 'user.email', 'fixture@example.invalid')
        (self.root / 'lean/Subtail').mkdir(parents=True)
        self.original = self.root / 'lean/Subtail/Original.lean'
        self.original.write_text('original dependency\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'fixture')
        self.base = self.git('rev-parse', 'HEAD').strip()

    def git(self, *args):
        return subprocess.check_output(['git', *args], cwd=self.root, text=True)

    def changes(self):
        return PROBE.protected_source_changes(self.root, self.base, ['lean/Subtail'])

    def test_committed_addition_is_allowed(self):
        (self.root / 'lean/Subtail/Additional.lean').write_text('new optional module\n')
        self.git('add', '.')
        self.git('commit', '-qm', 'add module')
        self.assertEqual(self.changes(), [])

    def test_changed_or_deleted_base_source_is_rejected(self):
        self.original.write_text('changed semantic dependency\n')
        self.assertEqual(self.changes(), ['lean/Subtail/Original.lean'])
        self.original.unlink()
        self.assertEqual(self.changes(), ['lean/Subtail/Original.lean'])

    def test_empty_protected_scope_is_rejected(self):
        with self.assertRaises(ValueError):
            PROBE.protected_source_changes(self.root, self.base, ['missing'])


if __name__ == '__main__':
    unittest.main()
