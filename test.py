#!/usr/bin/python3
import os
import subprocess
from sys import stdout

from requests import patch

run = ['cargo', 'run', '-q', '--', 'run']

GREEN = '\033[1;32m'
RED = '\033[1;31m'
CYAN = '\033[1;36m'
R = '\033[1;0m'

def main():
    errors = walk('eye')
    if errors > 0:
        s = 's' if errors > 1 else ''
        print(f'{errors} test{s} failed!')
        exit(1)
    else:
        print(f'{GREEN}All tests passed!{R}')

def walk(walkdir):
    errors = 0
    with os.scandir(walkdir) as it:
        for entry in it:
            if entry.name.endswith('.eye') and entry.is_file():
                if not test(entry.path): errors += 1
            elif entry.is_dir():
                if os.path.exists(entry.path + "/main.eye"):
                    if not test(entry.path): errors += 1
                else:
                    walk(entry.path)
    return errors
    


def test(eye_file) -> bool:
    print(eye_file, '...', end='')
    stdout.flush()
    no_ext = eye_file.rsplit('.', maxsplit=1)[0]
    
    if os.path.exists(no_ext + '.out'):
        expected = no_ext + '.out'
    elif os.path.exists(no_ext + '.err'):
        expected = no_ext + '.err'
    else:
        t = 'No .out or .err file'
        padding = ' ' * max(0, 50 - len(eye_file) - len(t))
        print(f'{t}{padding}{CYAN}[SKIP]{R}')
        return True

    with open(expected) as file:
        expected_output = file.read()

    input = None
    if os.path.exists(no_ext + '.in'):
        with open(no_ext + '.in') as file:
            input = memoryview(bytes(file.read(), 'utf-8'))

    res = subprocess.run(run + [eye_file], stdout = subprocess.PIPE, input=input)

    out = res.stdout.decode('utf-8')
    
    padding = ' ' * max(0, 50 - len(eye_file))
    
    if expected_output == out:
        print(f'{padding}{GREEN}[OK]{R}')
        return True
    else:
        print(f'{padding}{RED}[ERR]{R}\nFailed with status: {res.returncode}, output:')
        print(f'--------------------\n{out}\n--------------------')
        print('... but expected:')
        print(f'--------------------\n{expected_output}\n--------------------')
        return False





    
if __name__ == '__main__':
    main()