from random import shuffle,getrandbits,uniform
from os.path import join
import argparse
from os import makedirs 
import os
from typing import List
from itertools import zip_longest
import sys

def isTrue(s:str):
    if s=='True':
        return True
    else:
        assert s=='False'
        return False


def analyse(out:str,ref:str,src:str,info:str):
    total = 0
    invalid_test = 0
    exact_match = 0
    exact_match_while_valid = 0
    alternative_deri = 0
    auto_increase = 0
    if_concl = 0
    concl_via_target = 0
    output_not_dummy = 0
    output_not_dummy_while_exact_match = 0
    noted_metas = []

    if_target_derivable = 0
    if_concl_via_target = 0
    concl_via_output = 0

    exact_small_step = 0
    exact_too_big = 0

    with open(out,'r') as out_f, open(ref,'r') as ref_f, open(info,'r') as info_f,open(src,'r') as src_f:
        for idx,(out_line,ref_line,src_line,info_line) in enumerate(zip_longest(out_f,ref_f,src_f,info_f)):
            out_line = out_line.rstrip()
            ref_line = ref_line.rstrip()
            src_line = src_line.rstrip()
            info_line = info_line.rstrip()
            if out_line == '':
                continue
            total+=1
            if out_line == ref_line:
                exact_match +=1
            if info_line:
                rs = info_line[:info_line.index('@@@@')].split()
                meta = info_line[info_line.index('@@@@'):]

                if len(rs) == 9: # for backward compatibility
                    rs.insert(6,'False')
                    rs.append('False')

                assert len(rs) == 11
                if isTrue(rs[0]) and isTrue(rs[7]) and (out_line == ref_line):
                    exact_match_while_valid += 1
                    if isTrue(rs[9]):
                        exact_small_step += 1
                    elif not isTrue(rs[5]) or not isTrue(rs[8]):
                        exact_too_big += 1
                    else:
                        # noted_metas.append(str(idx)+'@@'+(info_line))
                        pass

                if isTrue(rs[2]):
                    output_not_dummy+=1
                if isTrue(rs[2]) and out_line == ref_line:
                    output_not_dummy_while_exact_match+=1

                if isTrue(rs[5]) and isTrue(rs[8]) and not out_line == ref_line and not out_line in src_line:
                    alternative_deri+=1
                   
                if not (isTrue(rs[6]) and isTrue(rs[10])) and isTrue(rs[9]) and len(src_line.split()) < 100:
                    # noted_metas.append(str(idx)+'@@'+info_line)
                    pass

                if not isTrue(rs[0]) or not isTrue(rs[7]):
                    invalid_test += 1
                if isTrue(rs[0]) and isTrue(rs[7]) and isTrue(rs[9]):
                    if_concl += 1
                if isTrue(rs[5]) and isTrue(rs[8]) and not isTrue(rs[9]):
                    auto_increase += 1
                    # noted_metas.append(str(idx)+'@@'+info_line)
                if (isTrue(rs[6]) and isTrue(rs[10])) or isTrue(rs[9]):
                    concl_via_target+=1
                
                # if not isTrue(rs[9]) and (isTrue(rs[6]) and isTrue(rs[10])):
                #     noted_metas.append(str(idx))

                if isTrue(rs[6]):
                    if_target_derivable += 1
                if isTrue(rs[10]):
                    if_concl_via_target += 1
                if isTrue(rs[5]) and isTrue(rs[8]):
                    concl_via_output += 1
            else:
                invalid_test += 1

    print('Total test: {}'.format(total))
    print('invalid test: {}'.format(invalid_test))
    print('accuracy (matching ground truth): {:.3f}'.format(exact_match/total))
    print('alternative steps: {:.3f}'.format(alternative_deri/total))
    print('exact match + alternative: {:.3f}'.format((exact_match+alternative_deri)/total))
    print('potential automation increase: {} / {}'.format(auto_increase,if_concl))
    print('output type checks: {}/{} = {:.3f} '.format(output_not_dummy,total-invalid_test, output_not_dummy/(total-invalid_test) ))
    print('ground truth type checks: {:.3f}'.format( output_not_dummy_while_exact_match/exact_match))
    print('ground truth derivation via sledgehammer: {} <- target derivable: {} and goal via target: {}'.format(concl_via_target,if_target_derivable,if_concl_via_target))
    print('Among the {} exact matches (in valid tests), {} of them have too small gaps; {} of the gaps are potentially "just right"; the remaining cases are {}.'\
        .format(exact_match_while_valid,exact_small_step,exact_match_while_valid-exact_small_step-exact_too_big,exact_too_big))
                
    # for m in noted_metas:
    #     print(m)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Further analysis on the output file of the test suite')
    parser.add_argument('--out', type=str, default=None,
                        help='path to the output file from seq2seq model')
    parser.add_argument('--ref', type=str, default=None,
                        help='path to the ground truth file (e.g., test.tgt)')
    parser.add_argument('--src', type=str, default=None,
                        help='path to the source file (e.g., test.src)')
    parser.add_argument('--info', type=str, default=None,
                        help='path to the output file of the test suite')

    args = parser.parse_args()

    analyse(args.out,args.ref,args.src,args.info)