"""Paired timestamp-fast benchmarks; binaries must use identical compiler flags."""
import argparse
import hashlib
import json
from pathlib import Path
import platform
import random
import statistics
import shlex
import sys
import subprocess
import tempfile
from datasets import cases, generate, file_hash
from verify import command


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--before', type=Path, required=True)
    parser.add_argument('--after', type=Path, required=True)
    parser.add_argument('--profile', choices=['standard', 'scaling', 'stress'], default='standard')
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--before-label', default='unspecified')
    parser.add_argument('--after-label', default='working-tree')
    parser.add_argument('--build-flags', required=True, help='identical flags used to build both binaries')
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error('repeats must be positive')
    if args.output.exists():
        parser.error('output already exists')
    binaries = {name: path.resolve() for name, path in [('before', args.before), ('after', args.after)]}
    report = {'command': shlex.join([sys.executable, *sys.argv]),
              'before_label': args.before_label, 'after_label': args.after_label,
              'build_flags': args.build_flags, 'platform': platform.platform(), 'profile': args.profile, 'repeats': args.repeats,
              'binary_sha256': {name: file_hash(path) for name, path in binaries.items()},
              'source_sha256': {name: file_hash(Path(__file__).parent / name) for name in
                                ['algorithms.hpp', 'datasets.py', 'compare_versions.py']}, 'cases': []}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    rng = random.Random(20260918)
    with tempfile.TemporaryDirectory() as tmp:
        for case in cases(args.profile):
            path = Path(tmp) / 'input.txt'
            manifest = generate(case, path)
            runs = {name: [] for name in binaries}
            expected_hash = None
            expected_counters = None
            for round_id in range(args.repeats + 1):
                order = list(binaries)
                rng.shuffle(order)
                for name in order:
                    with path.open('rb') as stream:
                        result = subprocess.run(command(binaries[name], 'timestamp-fast', case.factors),
                                                stdin=stream, capture_output=True, timeout=120, check=True)
                    digest = hashlib.sha256(result.stdout).hexdigest()
                    metrics = json.loads(result.stderr)
                    counters = {key: metrics[key] for key in ['visits', 'reductions', 'writes', 'pops', 'max_pending']}
                    if expected_hash is not None and (digest != expected_hash or counters != expected_counters):
                        raise AssertionError(f'answer or task-trace mismatch: {case.name}/{name}')
                    expected_hash, expected_counters = digest, counters
                    answers = result.stdout.splitlines()
                    for probe in manifest['oracle_probes']:
                        assert (answers[probe['query_index']] == b'YES') == probe['expected']
                    if round_id:
                        runs[name].append(metrics)
            medians = {name: statistics.median(x['solve_seconds'] for x in values) for name, values in runs.items()}
            item = {'manifest': manifest, 'answer_sha256': expected_hash, 'runs': runs,
                    'median_seconds': medians, 'speedup': medians['before'] / medians['after']}
            report['cases'].append(item)
            args.output.write_text(json.dumps(report, indent=2) + '\n')
            print(f"{case.name}: {medians['before']*1000:.2f} -> {medians['after']*1000:.2f} ms; {item['speedup']:.2f}x", flush=True)
    report['status'] = 'complete'
    args.output.write_text(json.dumps(report, indent=2) + '\n')


if __name__ == '__main__':
    main()
