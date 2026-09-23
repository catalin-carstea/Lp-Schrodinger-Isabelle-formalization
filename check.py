"""Standalone reviewer checker using Python's standard library."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PureWindowsPath
import re
import shlex
import subprocess
import sys


def require(condition, message):
    if not condition:
        raise ValueError(message)


def package_path(root, relative):
    require(relative and '\\' not in relative and ':' not in relative
            and not relative.startswith('/')
            and all(part not in ('', '.', '..') for part in relative.split('/'))
            and relative.split('/')[0] != '.git', 'Unsafe package path: ' + relative)
    path = root
    for part in relative.split('/'):
        path = path / part
        require(not path.is_symlink(), 'Package symlink is not allowed: ' + relative)
    return path


def inventory(root):
    result = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        base = Path(directory)
        # Git metadata is not release content. No other hidden file is exempt.
        if base == root and '.git' in dirs:
            dirs.remove('.git')
        for name in dirs + files:
            if base == root and name == '.git':
                continue
            path = base / name
            require(not path.is_symlink(), 'Package symlink is not allowed: ' + str(path))
        for name in files:
            relative = (base / name).relative_to(root).as_posix()
            if relative not in ('SHA256SUMS', '.git'):
                result.add(relative)
    return result


def cygwin_path(path):
    """Paths for the Cygwin bundled with the Windows Isabelle distribution."""
    value = PureWindowsPath(path)
    require(value.is_absolute(), 'Expected absolute Windows path: ' + str(path))
    if value.drive.startswith('\\\\'):
        return value.as_posix()
    return '/cygdrive/' + value.drive[0].lower() + '/' + '/'.join(value.parts[1:])


def isabelle_command(executable, arguments, windows=False, home=None, user=None):
    if not windows:
        return [str(executable), *arguments]
    require(home is not None, 'On Windows supply --isabelle-home (the Isabelle2025-2 installation folder).')
    bash = str(PureWindowsPath(home) / 'contrib/cygwin/bin/bash.exe')
    command = 'exec ' + shlex.join([cygwin_path(executable), *arguments])
    if user:
        command = 'export USER_HOME=' + shlex.quote(cygwin_path(user)) + '; ' + command
    return [bash, '--login', '-c', command]


def main():
    require(sys.version_info >= (3, 10), 'Python 3.10 or newer is required.')
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--skip-build', '-SkipBuild', action='store_true')
    parser.add_argument('--isabelle-home', '-IsabelleHome')
    parser.add_argument('--afp-thys', '-AfpThys')
    parser.add_argument('--isabelle-user', '-IsabelleUser')
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    expected = {}
    for line in (root / 'SHA256SUMS').read_text(encoding='utf-8').splitlines():
        if not line.strip():
            continue
        match = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        require(match, 'Malformed SHA256SUMS line.')
        digest, relative = match.groups()
        require(relative not in expected, 'Duplicate checksum path: ' + relative)
        require(relative != 'SHA256SUMS', 'SHA256SUMS cannot list itself.')
        path = package_path(root, relative)
        require(path.is_file(), 'Missing package file: ' + relative)
        require(hashlib.sha256(path.read_bytes()).hexdigest() == digest, 'Checksum mismatch: ' + relative)
        expected[relative] = digest
    require(expected, 'Empty checksum inventory.')
    require(len({p.casefold() for p in expected}) == len(expected), 'Case-colliding package paths are not portable to Windows.')
    actual = inventory(root)
    require(actual == set(expected), 'Unlisted files or incomplete checksum inventory: ' + ', '.join(sorted(actual ^ set(expected))))
    manifest = json.loads((root / 'MANIFEST.json').read_text(encoding='utf-8-sig'))
    source_files = manifest['source_files']
    require(len({entry['path'] for entry in source_files}) == len(source_files), 'Duplicate manifest source path.')
    require({entry['path'] for entry in source_files} == set(expected) - {'MANIFEST.json'}, 'Manifest source inventory disagrees with SHA256SUMS.')
    for entry in source_files:
        require(entry['sha256'].lower() == expected[entry['path']], 'Manifest source hash mismatch: ' + entry['path'])
    binding = manifest['manuscript_binding']
    require(not binding['hard_gate'] and binding['mode'] == 'external_semantic_review', 'Invalid manuscript-binding policy.')
    theories = list((root / 'isabelle').rglob('*.thy'))
    require(theories and manifest['build']['terminal_sessions'] and manifest['build']['checked_theorems'], 'Empty theory/session/theorem boundary.')
    text = '\n'.join(p.read_text(encoding='utf-8-sig') for p in theories)
    pattern = r'(?<![A-Za-z0-9_])(sorry|oops|skip_proof|axiomatization)(?![A-Za-z0-9_])|Thm[.]add_oracle|(?<![A-Za-z0-9_])CF_Scratch_'
    require(not re.search(pattern, text), 'Admission/oracle/scratch scan failed.')
    for theorem in manifest['build']['checked_theorems']:
        name = theorem['formal_identifier']
        require(re.search(r'\b' + re.escape(name) + r'\b', text), 'Checked theorem identifier not found: ' + name)
    print(f'Integrity check passed for {len(expected)} static files; admission and theorem-name checks passed.')
    if args.skip_build:
        return 0
    windows = os.name == 'nt'
    home = Path(args.isabelle_home).resolve() if args.isabelle_home else None
    require(not windows or home is not None, 'On Windows supply --isabelle-home (the Isabelle2025-2 installation folder).')
    executable = str(home / 'bin/isabelle') if home else os.environ.get('ISABELLE', 'isabelle')
    if windows:
        require((home / 'contrib/cygwin/bin/bash.exe').is_file(), 'Bundled Isabelle Cygwin bash.exe not found.')
    if home:
        require(Path(executable).is_file(), 'Isabelle executable not found: ' + executable)
    env = os.environ.copy()
    user = args.isabelle_user or env.get('USER_HOME')
    if user:
        user = Path(user).resolve()
        require(user != root and not user.is_relative_to(root), 'Isabelle user directory must be outside the extracted package.')
        env['USER_HOME'] = str(user)
    def command(arguments):
        return isabelle_command(executable, arguments, windows, home, user)
    version = subprocess.run(command(['version']), env=env, text=True, capture_output=True)
    require(version.returncode == 0 and manifest['required_environment']['isabelle'] == version.stdout.strip(), 'Isabelle release check failed: ' + version.stdout + version.stderr)
    path_argument = cygwin_path if windows else str
    argv = ['build', '-v', '-j', '1', '-o', 'threads=1', '-o', 'parallel_proofs=0', '-D', path_argument(root / 'isabelle')]
    afp = args.afp_thys or env.get('AFP_THYS')
    if afp:
        afp = Path(afp).resolve()
        require((afp / 'ROOTS').is_file(), 'AFP theory directory must contain ROOTS: ' + str(afp))
        argv += ['-d', path_argument(afp)]
    require(subprocess.run(command(argv), env=env).returncode == 0, 'Isabelle build failed.')
    print('Proof package build passed.')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(error, file=sys.stderr)
        sys.exit(1)
