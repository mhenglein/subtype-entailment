"""Behavior checks for bounded scholarship retrieval; no mathematical proofs."""
import contextlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import search


class RetrievalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.corpus = search.records()
        cls.topics = search.topics()

    def test_sources_keep_publication_and_inspection_separate(self):
        withdrawn = self.corpus['PW-SCH21']
        self.assertEqual(withdrawn['status'], 'withdrawn')
        self.assertEqual(withdrawn['inspection'], 'selected-primary-text')
        self.assertIn('F27', search.related('PW-SCH21', self.topics))

    def test_canonical_claim_is_read_directly(self):
        record = self.corpus['C029']
        self.assertTrue(record['content'].startswith('### C029 '))
        self.assertIn('**Status / scope.**', record['content'])
        self.assertIn(record['content'], (search.ROOT / record['source']).read_text())

    def test_topic_returns_sources_and_known_obstructions(self):
        result = search.search(self.corpus, self.topics, 'finite quotient', 50)
        keys = {row['id'] for row in result['results']}
        self.assertTrue({'PW-KUF07', 'F13', 'A017'} <= keys)
        self.assertEqual(result['returned'], len(result['results']))

    def test_search_is_bounded_and_reports_truncation(self):
        result = search.search(self.corpus, self.topics, 'shared', 2)
        self.assertGreater(result['total'], 2)
        self.assertTrue(result['truncated'])
        self.assertEqual(result['returned'], 2)
        self.assertTrue(all(len(row['excerpt']) <= 360 for row in result['results']))

    def test_unknown_query_is_empty_not_error(self):
        result = search.search(self.corpus, self.topics, 'zzzz-no-such-concept', 12)
        self.assertEqual(result['results'], [])
        self.assertFalse(result['truncated'])

    def test_duplicates_and_escaped_table_delimiters(self):
        with tempfile.TemporaryDirectory(dir=search.HERE) as folder:
            path = Path(folder) / 'fixture.md'
            path.write_text('| F99 HAZARD | a \\| b | evidence | limit |\n')
            records = search.table_records(path, 'F')
            self.assertEqual(records['F99']['title'], 'a \\| b')
            path.write_text(path.read_text() * 2)
            with self.assertRaisesRegex(ValueError, 'Duplicate'):
                search.table_records(path, 'F')

    def test_missing_topic_reference_fails(self):
        with self.assertRaisesRegex(ValueError, 'Unknown topic reference'):
            search.validate_links(self.corpus, [{'key': 'bad', 'records': ['PW-MISSING99']}])

    def test_unknown_lookup_and_bad_limit_exit_nonzero(self):
        for arguments in (['--lookup', 'PW-MISSING99'], ['--search', 'border', '--limit', '0']):
            with patch('sys.argv', ['search.py', *arguments]), contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(search.main(), 1)

    def test_lookup_contains_related_records(self):
        output = io.StringIO()
        with patch('sys.argv', ['search.py', '--lookup', 'F13']), contextlib.redirect_stdout(output):
            self.assertEqual(search.main(), 0)
        record = json.loads(output.getvalue())
        self.assertIn('PW-KUF07', record['related_records'])
        self.assertIn('agreement profile', record['content'])


if __name__ == '__main__':
    unittest.main()
