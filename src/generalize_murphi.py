import os
import subprocess


temp_dir = None


def murphi_check_init():
    global temp_dir
    temp_dir = create_directory('..', 'murphi_gen')
    if temp_dir is None:
        raise Exception('create directory failed')


def check_murphi(murphi_str: str):
    assert temp_dir is not None
    murphi_file = os.path.join(str(temp_dir), 'murphi_gen.m')
    with open(murphi_file, 'w') as f:
        f.write(murphi_str)
    cpp_file = process_with_mu('/home/loyce/MC/cmurphi5.5.0/src/mu', murphi_file)
    if cpp_file is None:
        raise Exception('process with mu failed')
    object_file = compile_cpp(cpp_file, '/home/loyce/MC/cmurphi5.5.0/include')
    if object_file is None:
        raise Exception('compile cpp failed')
    result = run_object_file(object_file)
    if result is None:
        raise Exception('run object file failed')
    # output_file = os.path.join(str(temp_dir), 'murphi_out.txt')
    # with open(output_file, 'w') as f:
    #     f.write(result)
    return result


def create_directory(parent_dir, new_dir_name):
    new_dir_path = os.path.join(parent_dir, new_dir_name)
    try:
        os.makedirs(new_dir_path, exist_ok=True)
        return new_dir_path
    except OSError:
        return None


def process_with_mu(mu_path, input_file):
    cpp_file = os.path.splitext(input_file)[0] + '.cpp'
    try:
        subprocess.run([mu_path, input_file], check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return cpp_file
    except subprocess.CalledProcessError:
        return None


def compile_cpp(cpp_file, include_path):
    object_file = os.path.splitext(cpp_file)[0] + '.o'
    try:
        command = ['g++', cpp_file, '-o', object_file, f'-I{include_path}', '-w']
        subprocess.run(command, check=True, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return object_file
    except subprocess.CalledProcessError:
        return None


def run_object_file(object_file):
    try:
        result = subprocess.run([object_file], stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        return result.returncode == 0
    except subprocess.CalledProcessError:
        return None
