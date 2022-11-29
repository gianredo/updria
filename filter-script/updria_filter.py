import readline
from string import Template
from unicodedata import name
import sys
import os

def do_filter(iterable):
    result = "?"
    tot_time = 0
    z3_time = 0
    gen_time = 0
    rec_block_time = 0
    propagation_time = 0 
    refinement_time = 0
    minimization_models_time = 0
    num_z3_calls = 0
    added_diagrams_frame = 0
    greatest_num_literals_frame = 0
    num_ref_steps = 0
    num_initial_preds = 0
    num_final_preds = 0
    max_concrete_size = 0
    num_used_preds = 0    
    memout = False
    for line in iterable:
        line = line.strip()
        if line.startswith('Proved!'):
            result = 'safe'
        elif line == 'true counterexample!':
            result = 'unsafe'
        elif line.startswith('verification time'):
            try:
                _, tot_time = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('z3 check time'):
            try:
                _, z3_time = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('generalization time'):
            try:
                _, gen_time = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('recursive block time'):
            try:
                _, rec_block_time = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('propagation time'):
            try:
                _, propagation_time = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('refinement time'):
            try:
                _, refinement_time = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('minimization models time'):
            try:
                _, minimization_models_time = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('num z3 calls'):
            try:
                _, num_z3_calls = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('number of added diagrams per frame'):
            try:
                _, added_diagrams_frame = line.split(':', 1)
                added_diagrams_frame = added_diagrams_frame.replace(',', ';')
            except ValueError: pass
        elif line.startswith('greatest number of literals in a diagram per frame'):
            try:
                _, greatest_num_literals_frame = line.split(':', 1)
                greatest_num_literals_frame = greatest_num_literals_frame.replace(',', ';')
            except ValueError: pass
        elif line.startswith('number of refinement steps'):
            try:
                _, num_ref_steps = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('number of initial predicates'):
            try:
                _, num_initial_preds = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('number of final predicates'):
            try:
                _, num_final_preds = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('max concrete size'):
            try:
                _, max_concrete_size = line.split(':', 1)
            except ValueError: pass
        elif line.startswith('number of predicates used in the inductive invariant'):
            try:
                _, num_used_preds = line.split(':', 1)
            except ValueError: pass

        elif 'std::bad_alloc' in line and not memout:
            result = 'memout'
            time = '?'

    t = Template('$result, $tot_time, $z3_time, $gen_time, $rec_block_time, $propagation_time, $refinement_time, $minimization_models_time, $num_z3_calls, $added_diagrams_frame, $greatest_num_literals_frame, $num_ref_steps, $num_initial_preds, $num_final_preds, $max_concrete_size, $num_used_preds \n')
    return t.substitute(locals())

if __name__ == '__main__':
    print('name, result, total time, z3 time, generalization time, recursive block time, propagation time, refinement time, minimization time, number of z3 calls, added diagrams per frame, greates number of literas per frame, # refinements, # initial preds, # final preds, max size, # used preds\n')
    directory = os.fsencode(sys.argv[1])    
    for file in os.listdir(directory):
        filename = os.fsdecode(file)
        if filename.endswith(".stdout"): 
            f = open(sys.argv[1] + '/' + filename)
            print(filename.replace('.stdout', '') + ', ' + do_filter(f.readlines()))
        else:
            continue
