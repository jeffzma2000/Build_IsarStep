#!/usr/bin/env python
# -*- coding: utf-8 -*-
import sys, getopt, collections
import string
import io, os
import re
import numpy as np
import argparse
from random import shuffle
# from bs4 import BeautifulSoup

import xml.etree.ElementTree as ET

IGNORED_ENTRIES = {
    'Launchbury',
    'Call_Arity',
    'Incompleteness',
    'LambdaAuth',
    'Modal_Logics_for_NTS',
    'Rewriting_Z',
    'Surprise_Paradox',
    'Isabelle_C',
    'Clean'
}

META_SEP = '<!;!>'

FOCUSED_ENTRIES = {
        # 'Sturm_Tarski'
        'HOL'
}

def adjust_SEP(s:str):
    if s:
        return s.replace('\n',' ')
    else:
        return ''
    
    # if s:
    #     return ' <SEP> ' + ' <SEP> '.join(filter(lambda x: x!='', s.split('<SEP>') ))         
    # else:
    #     return ''

def extract_CausalSteps_from_isar_dataset(dir_in:str,dir_out:str,processed_id:int,mode:str):
    def get_entry_name(path:str):
        assert path.startswith(dir_in)
        dlen = len(os.path.normpath(dir_in).split(os.sep))
        path_s= os.path.normpath(path).split(os.sep)
        if len(path_s)>dlen:
            return path_s[dlen]
        else:
            return ''


    os.makedirs(dir_out, exist_ok=True)
    
    causal_dir =  os.path.join(dir_out, 'CausalSteps')
    os.makedirs(causal_dir, exist_ok=True)

    filenames = ("target.txt","source.txt",'source_g.txt','meta.txt'\
                ,"target_ascii.txt","source_ascii.txt",'source_g_ascii.txt'\
                ,"target_latex.txt","source_latex.txt",'source_g_latex.txt',)
    filepaths = [os.path.join(causal_dir,f) for f in filenames]

    # clear file contents if any
    for f in filepaths:
        open(f, 'w').close()

    with open(filepaths[0],'a') as f_target,\
         open(filepaths[1],'a') as f_source,\
         open(filepaths[2],'a') as f_source_g,\
         open(filepaths[3],'a') as f_meta,\
         open(filepaths[4],'a') as f_target_ascii,\
         open(filepaths[5],'a') as f_source_ascii,\
         open(filepaths[6],'a') as f_source_g_ascii,\
         open(filepaths[7],'a') as f_target_latex,\
         open(filepaths[8],'a') as f_source_latex,\
         open(filepaths[9],'a') as f_source_g_latex\
         :

        CausalSteps_entry_count = 0
        CausalSteps_has_consequence_count = 0
        for root, subdirs, files in os.walk(dir_in):
            print('Checking directory: ',root)
            if root in IGNORED_ENTRIES:
                continue
            if  mode == 'FOCUSED_ENTRIES' and get_entry_name(root) not in FOCUSED_ENTRIES:
                continue
        # print('--\nroot = ' + root)
            if root.endswith('CausalSteps') and not root.endswith('AlternativeCausalSteps')  :
                for file in files:
                    if file.endswith('.xml'):
                        file_path = os.path.join(root, file)
                        print('Start processing {}'.format(file_path))
                        tree = ET.parse(file_path)
                        tree_root = tree.getroot()
                        assert tree_root.tag == 'theory'
                        theory_name = tree_root.attrib['full_name']
                        if str(processed_id) != tree_root.attrib['processed_id']:
                            print('{} has been skipped due to mismatched processed_id: {}!={}'.format(theory_name,str(processed_id),tree_root.attrib['processed_id']))
                            continue
                        

                        for entry in tree_root:
                            assert entry.tag == 'entry'      
                            if not entry.find('used_local_facts').text and not entry.find('consequences').text:
                                continue

                            f_target.write(entry.find('target_fact').text+'\n')
                            f_target_ascii.write(entry.find('target_fact_ascii_original').text.replace('\n',' ')+'\n')
                            f_target_latex.write(entry.find('target_fact_latex').text.replace('\n',' ')+'\n')

                            meta_list=[theory_name, entry.attrib['theorem_id']\
                                ,entry.attrib['location_in_theorem']\
                                ,entry.attrib['refinement_step_location'],entry.attrib['compound_index']\
                                ,entry.find('target_fact_ascii').text.replace("\n","")\
                                ,entry.attrib['has_consequence']\
                                ,entry.attrib['location_in_theorem_consequence'],entry.attrib['refinement_step_location_consequence']\
                                ,entry.attrib['compound_index_consequence']\
                                ,entry.find('consequences_ascii').text.replace("\n","") if entry.find('consequences_ascii').text else ''\
                            ]
                            f_meta.write(META_SEP.join(meta_list) +'\n')

                            used_local_facts_text = '<used_local_facts>' + adjust_SEP(entry.find('used_local_facts').text)
                            used_global_facts_text= '<used_global_facts>'+ adjust_SEP(entry.find('used_global_facts').text)
                            consequences_text = '<consequences>'+(' '+entry.find('consequences').text if entry.find('consequences').text else '')
                            consequences_others_text = '<consequences_others>'+adjust_SEP(entry.find('consequences_others').text)

                            source_seq=[x for x in [used_local_facts_text\
                                    ,consequences_text,consequences_others_text] if x]
                            f_source.write(' '.join(source_seq)+'\n')
                            source_seq=[x for x in [used_local_facts_text\
                                ,consequences_text,consequences_others_text,used_global_facts_text] if x]
                            f_source_g.write(' '.join(source_seq)+'\n')  

                            used_local_facts_ascii_text = '<used_local_facts>' + adjust_SEP(entry.find('used_local_facts_ascii_original').text)
                            used_global_facts_ascii_text= '<used_global_facts>'+ adjust_SEP(entry.find('used_global_facts_ascii_original').text)
                            consequences_ascii_text = '<consequences>'+(' '+entry.find('consequences_ascii_original').text.replace('\n',' ') \
                                if entry.find('consequences_ascii_original').text else '')
                            consequences_others_ascii_text = '<consequences_others>'+adjust_SEP(entry.find('consequences_others_ascii_original').text)

                            source_seq=[x for x in [used_local_facts_ascii_text\
                                    ,consequences_ascii_text,consequences_others_ascii_text] if x]
                            f_source_ascii.write(' '.join(source_seq)+'\n')
                            source_seq=[x for x in [used_local_facts_ascii_text\
                                ,consequences_ascii_text,consequences_others_ascii_text,used_global_facts_ascii_text] if x]
                            f_source_g_ascii.write(' '.join(source_seq)+'\n')

                            used_local_facts_latex_text = '<used_local_facts>' + adjust_SEP(entry.find('used_local_facts_latex').text)
                            used_global_facts_latex_text= '<used_global_facts>'+ adjust_SEP(entry.find('used_global_facts_latex').text)
                            consequences_latex_text = '<consequences>'+(' '+entry.find('consequences_latex').text.replace('\n',' ') \
                                if entry.find('consequences_latex').text else '')
                            consequences_others_latex_text = '<consequences_others>'+adjust_SEP(entry.find('consequences_others_latex').text)

                            source_seq=[x for x in [used_local_facts_latex_text\
                                    ,consequences_latex_text,consequences_others_latex_text] if x]
                            f_source_latex.write(' '.join(source_seq)+'\n')
                            source_seq=[x for x in [used_local_facts_latex_text\
                                ,consequences_latex_text,consequences_others_latex_text,used_global_facts_latex_text] if x]
                            f_source_g_latex.write(' '.join(source_seq)+'\n')

                            if entry.attrib['has_consequence'] == 'True':
                                CausalSteps_has_consequence_count += 1
                            # if used_local_facts_text or used_global_facts_text or \
                            #     consequences_text or consequences_others_text:

                            #     source_seq=[x for x in [used_local_facts_text\
                            #         ,consequences_text,consequences_others_text] if x]
                            #     f_source.write(' '.join(source_seq)+'\n')
                            #     source_seq=[x for x in [used_local_facts_text\
                            #         ,consequences_text,consequences_others_text,used_global_facts_text] if x]
                            #     f_source_g.write(' '.join(source_seq)+'\n')  
                            # else:
                            #     CausalSteps_empty_source_count+=1

                            CausalSteps_entry_count+=1

    return 'CausalSteps:{} entries have been processed and {} of them have consequences.'.format(CausalSteps_entry_count,CausalSteps_has_consequence_count)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description='Extract data from xmls in Isar corpus')
    parser.add_argument('--dir_in', type=str, default='./isar_dataset',
                        help='The path of the input corpus')
    parser.add_argument('--dir_out', type=str, default='./extracted_isar_dataset',
                        help='The path of the output corpus')
    parser.add_argument('--processed_id', type=int, default=-1,
                        help='An integer used for resuming processing a dataset')
    parser.add_argument('--mode', type=str, default='DEFAULT',
                        help='Mainly for debugging. Current modes: DEFAULT, FOCUSED_ENTRIES.')
    args = parser.parse_args()

    r1 = extract_CausalSteps_from_isar_dataset(args.dir_in,args.dir_out,args.processed_id,args.mode)
    print(r1)