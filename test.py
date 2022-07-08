#!/usr/bin/python3
import os
import subprocess
from sys import stdout

from requests import patch

build = ['cargo', 'build']
run_cmd = ['./target/debug/eyelang', 'run']
tmp_file = 'tmp_test.eye'

GREEN = '\033[1;32m'
RED = '\033[1;31m'
CYAN = '\033[1;36m'
R = '\033[1;0m'

def main():
    total, errors = test_files()
    total2, errors2 = test_readme()
    total += total2
    errors += errors2

    if errors > 0:
        print(f'{RED}{errors}/{total} tests failed!{R}')
        exit(1)
    else:
        print(f'{GREEN}All {total} tests passed!{R}')

def test_files():
    print(f'{CYAN}Compiling...{R}')
    if subprocess.run(build).returncode != 0:
        print(f'{RED}An error occurred while compiling{R}')
        exit(1)
    print(f'{CYAN}Running tests ...{R}')
    return walk('eye')
    
    


def test_readme():
    print(f'{CYAN}Running README tests ...{R}')
    file = open('README.md')
    # contents = file.read()
    current_source = ''
    in_code_block = False
    block_count = 0
    errors = 0
    for line in file:
        if line.find('```') != -1:
            if in_code_block:
                temp_code_file = open(tmp_file, 'w')
                temp_code_file.write(current_source)
                temp_code_file.close()
                
                print(f'Testing README block #{block_count}', end = '')
                out, exit_code = run(tmp_file)
                padding = ' ' * max(0, 32 - len(f'{block_count}'))
                if exit_code != 0:
                    print(f'{padding}{RED}[ERR]{R}')
                    print(f'{RED}Output{R}:\n{out}')
                    errors += 1
                else:
                    print(f'{padding}{GREEN}[OK]{R}')
                current_source = ''
            else: block_count += 1
            in_code_block = not in_code_block
        elif in_code_block:
            current_source += line

    os.remove(tmp_file)
    return block_count, errors




def walk(walkdir):
    errors = 0
    total = 0
    with os.scandir(walkdir) as it:
        for entry in it:
            if entry.name.endswith('.eye') and entry.is_file():
                total += 1
                if not test(entry.path): errors += 1
            elif entry.is_dir():
                if os.path.exists(entry.path + "/main.eye"):
                    total += 1
                    if not test(entry.path): errors += 1
                else:
                    total2, errors2 = walk(entry.path)
                    total += total2
                    errors += errors2
    return total, errors
    


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

    out, exit_code = run(eye_file, input)
    
    padding = ' ' * max(0, 50 - len(eye_file))
    
    if expected_output == out:
        print(f'{padding}{GREEN}[OK]{R}')
        return True
    else:
        print(f'{padding}{RED}[ERR]{R}\nFailed with status: {exit_code}, output:')
        print(f'--------------------\n{out}\n--------------------')
        print('... but expected:')
        print(f'--------------------\n{expected_output}\n--------------------')
        return False


def run(eye_file, input = ''):
    res = subprocess.run(run_cmd + [eye_file], stdout = subprocess.PIPE, input=input)
    return res.stdout.decode('utf-8'), res.returncode


    
if __name__ == '__main__':
    main()