#!/usr/bin/env python
# -*- coding: utf-8 -*-
import sys, getopt, collections
import string
import io, os
import argparse
from random import shuffle
import xml.etree.ElementTree as ET

META_NUMBERS = 5000

def isTrue(s:str):
    if s=='True':
        return True
    else:
        assert s=='False'
        return False

def extract_derivation_results_from_isar_dataset(dir_in:str,file_out:str,processed_id:int):
    deri_results = {}
    meta_info = {}
    for root, subdirs, files in os.walk(dir_in):
        print('Checking directory: ',root)
        if root.endswith('CheckingDerivation'):
            for file in files:
                if file.endswith('.xml'):
                    file_path = os.path.join(root, file)
                    print('Start processing {}'.format(file_path))
                    try:
                        tree = ET.parse(file_path)
                    except ET.ParseError:
                        # print('Fail to parse {}'.format(file_path))
                        continue
                    tree_root = tree.getroot()
                    assert tree_root.tag == 'database'
                    if str(processed_id) != tree_root.attrib['processed_id']:
                        print('{} has been skipped due to mismatched processed_id: {}!={}'.format(root,str(processed_id),tree_root.attrib['processed_id']))
                        continue
                    for entry in tree_root:
                        assert entry.tag == 'derivation' 
                        key = (entry.attrib['meta_id'],entry.attrib['meta_tag'])
                        deri_results[key] = entry.text
                        meta_info[entry.attrib['meta_id']] = root + ';' + entry.attrib['theory_name'] + ';' +entry.attrib['theorem_id'] + ';' + entry.attrib['meta_id']

    restab = {
        'target_not_dummy' : 0,
        'output_syntactically_correct': 0,
        'output_not_dummy' : 0,
        'output_aconv_target' : 0, 
        'output_unify_target' : 0,
        'aconv_or_unify' : 0,
        'if_output_derivable' : 0,
        'if_target_derivable' : 0,
        'concl_not_dummy' : 0,
        'if_concl_via_output' : 0,
        'if_concl_via_target' : 0,
        'if_concl' : 0,

        'A_output_B_derivable' : 0,
        'A_output_B_alternative' : 0,
        'A_output_B_complement' : 0,
        'A_output_B_complement_alternative' : 0,
    }
    noted_ids = set()
    for (m_id,tag) in deri_results.keys():
        rs = deri_results[(m_id,tag)].split()
        if tag == 'AB':
            assert len(rs) == 7
            if isTrue(rs[5]) and isTrue(deri_results[(m_id,'BC')].split()[1]):
                restab['A_output_B_derivable'] += 1
                restab['A_output_B_alternative'] += 1 if not isTrue(rs[4]) else 0
                if not isTrue(deri_results[(m_id,'BC')].split()[2]):
                    noted_ids.add(m_id)

                restab['A_output_B_complement'] += 1 if not isTrue(deri_results[(m_id,'BC')].split()[2]) else 0
                restab['A_output_B_complement_alternative'] += 1 if not isTrue(deri_results[(m_id,'BC')].split()[2]) and not isTrue(rs[4]) else 0

            restab['target_not_dummy'] += 1 if isTrue(rs[0]) else 0
            restab['output_syntactically_correct'] += 1 if isTrue(rs[1]) else 0
            restab['output_not_dummy'] += 1 if isTrue(rs[2]) else 0
            restab['output_aconv_target'] += 1 if isTrue(rs[3]) else 0
            restab['output_unify_target'] += 1 if isTrue(rs[4]) else 0
            restab['aconv_or_unify'] += 1 if isTrue(rs[3]) or isTrue(rs[4]) else 0
            restab['if_output_derivable'] += 1 if isTrue(rs[5]) else 0
            restab['if_target_derivable'] += 1 if isTrue(rs[6]) else 0
        else:
            assert tag == 'BC'
            assert len(rs) == 4
            restab['concl_not_dummy'] += 1 if isTrue(rs[0]) else 0
            restab['if_concl_via_output'] += 1 if isTrue(rs[1]) else 0
            restab['if_concl'] += 1 if isTrue(rs[2]) else 0
            restab['if_concl_via_target'] += 1 if isTrue(rs[3]) else 0
            
    
    print('Number of metas are {}/2={}.'.format(len(deri_results), len(deri_results)//2 ))
    for key in restab.keys():
        print('{}: {}'.format(key,restab[key]))
    
    if file_out is not None:
        with open(file_out, 'w') as file:
            for idx in range(META_NUMBERS):
                key1 = (str(idx),'AB')
                key2 = (str(idx),'BC')
                if key1 in deri_results:
                    assert key2 in deri_results
                    line = '{} {} @@@@ {}'.format(deri_results[key1],deri_results[key2],meta_info[str(idx)])
                    assert '\n' not in line
                    file.write(line+'\n')
                else:
                    file.write('\n')
            
if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Extract data from xmls in Isar corpus')
    parser.add_argument('--dir_in', type=str, default='./isar_dataset',
                        help='The path of the input corpus')
    parser.add_argument('--file_out', type=str, default=None,
                        help='The path of the output file. No output file will be produced in left empty.')
    parser.add_argument('--processed_id', type=int, default=-1,
                        help='An integer used for resuming processing a dataset')
    args = parser.parse_args()
    extract_derivation_results_from_isar_dataset(args.dir_in,args.file_out,args.processed_id)
