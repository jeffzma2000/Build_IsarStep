from evaluation_scripts.expand_thy_model import expand_model,KNOWN_FACT_COLLECTIONS,CollectedFacts,GlobalFact,LocalFact,FactDict,DependencyGraph,expand_model
from evaluation_scripts.annotate_with_database import annotate_wrt_derivations
from evaluation_scripts.print_theory import *

import argparse
from datetime import datetime
import os
from os.path import isfile, join,normpath
import subprocess
from time import sleep

import subprocess
from multiprocessing import Pool
import multiprocessing

class WrappedThyModel:
    def __init__(self,thy_model):
        self.thy_model = thy_model

class NameToModel:
    def __init__(self,parser,dir_path,purge_diagnostic,keep_diagnostic):
        self.parser = parser
        self.dir_path = dir_path
        self.purge_diagnostic = purge_diagnostic
        self.keep_diagnostic = keep_diagnostic

    def name_to_model(self,full_filename):
        thy_path=os.path.normpath(os.path.join(self.dir_path,full_filename))
        with open(thy_path,'r+') as file:
            thy_src = file.read()
            try:
                model = self.parser.parse(thy_src)
            except:
                print('Failed to parse:' + thy_path)
                return WrappedThyModel(None)
            model.annotate_Theorems()
            if not self.keep_diagnostic:
                model.purge_diagnostic()
            try:
                model.add_diagnostic()
            except:
                print('Error in ' + full_filename )
                raise
            model.filepath = thy_path
            model.full_filename = full_filename
            if self.purge_diagnostic:
                model.purge_diagnostic()
            return WrappedThyModel(model)

UNSUPPORTED_FILES = {
    'Ordinary_Differential_Equations/Ex/Lorenz/Lorenz_Approximation.thy'
    'HOL-M/Fun.thy',
    'HOL-M/Zorn.thy',
    'HOL-M/BNF_Cardinal_Order_Relation.thy',
    'HOL-M/Groups_Big.thy',
    'HOL-M/Int.thy',
    'HOL-M/Divides.thy',
    'HOL-M/Filter.thy'
    }

def get_seq_results(seq_file,meta_file,META_SEP='<!;!>'):
    '''
        return session_name -> (full_theory_name -> (meta,seq) list)
    '''
    with open(seq_file,'r+') as file:
        generated_seqs = file.read()
    with open(meta_file,'r+') as file:
        metas = file.read()
    generated_seqs = generated_seqs.splitlines()
    metas = metas.splitlines()
    assert len(generated_seqs) == len(metas)

    dict_of_metas = dict()
    for (m_id,(meta,seq)) in enumerate(zip(metas,generated_seqs)):
        meta = meta.split(META_SEP)
        assert len(meta) == 11 
        if meta[0] in UNSUPPORTED_FILES:
            print('Meta_id<{}> in unsupported files<{}>. IGNORED.'.format(m_id,meta[0]))
            continue

        key = meta[0].split(os.path.sep)[0] # session directory name is used as the key
        key1 = meta[0]
        if key in dict_of_metas.keys():
            key1 = meta[0]
            if key1 in dict_of_metas[key].keys():
                dict_of_metas[key][key1].append((m_id,meta,seq))
            else:
                dict_of_metas[key][key1] = dict()
                dict_of_metas[key][key1] = [(m_id,meta,seq)]

        else:
            dict_of_metas[key] = dict()
            dict_of_metas[key][key1] = dict()
            dict_of_metas[key][key1] = [(m_id,meta,seq)]
    
    return dict_of_metas

def get_models(dir_path,entry_name,dict_of_metas,purge_diagnostic=False\
        ,keep_diagnostic = True):
    full_thy_names = dict_of_metas[entry_name].keys()

    parser = ThyParser(semantics=ThyModelBuilderSemantics())
    n2m = NameToModel(parser,dir_path,purge_diagnostic,keep_diagnostic)
    with Pool(multiprocessing.cpu_count()-1) as p:
        thy_models = list(p.imap_unordered(n2m.name_to_model, full_thy_names))
    print('{} theories have been parsed'.format(len(thy_models)) )
    thy_models = list(filter(lambda x: x.thy_model is not None,thy_models))

    return thy_models

def build_isabelle_repository(dir_path,wrapped_thy_models,isa_bin,processed_id=-1,threads=6):
    thy_models = list(map(lambda x:x.thy_model,wrapped_thy_models))
    for (root , _ , _) in os.walk(dir_path): 
        if os.path.basename(root) in {'Database','InterSteps','AlternativeCausalSteps','CausalSteps'\
            ,'TransitiveSteps','document','CheckingDerivation'}: # ignore some special directories
            continue
        os.makedirs(join(root,'Database'), exist_ok=True)
        os.makedirs(join(root,'CausalSteps'), exist_ok=True)
        os.makedirs(join(root,'AlternativeCausalSteps'), exist_ok=True)
        os.makedirs(join(root,'TransitiveSteps'), exist_ok=True)
        os.makedirs(join(root,'CheckingDerivation'), exist_ok=True)
    for model in thy_models:
        database_path = join(os.path.dirname(model.filepath),'CheckingDerivation',model.thy_name+'.xml')
        with open(database_path,'w') as file:
            file.write('<database processed_id="{}">\n'.format(str(processed_id)) )
    bashCommand = '{} build -c -o timeout_scale=100 -o threads={} -D {}'.format(isa_bin,threads,dir_path)
    print(bashCommand)
    process = subprocess.run(bashCommand.split(), check=True)
    
    print('{} has been built.'.format(dir_path)) 
    sleep(1)

    for model in thy_models:
        database_path = join(os.path.dirname(model.filepath),'CheckingDerivation',model.thy_name+'.xml')
        with open(database_path,'a') as file:
            file.write('</database>\n')
    return process.returncode

FOCUSED_ENTRIES = {
    # 'Sturm_Tarski',
    # 'HOL',
    'Markov_Models'
}




def check_derivation(dir_path,isa_bin,output_seq,output_meta,processed_id,threads=6,is_test_mode=False):
    def check_meta(session_dir_path) -> bool:
        path = os.path.join(session_dir_path,'META.META')
        if os.path.isfile(path):
            with open(path,'r') as file:
                p_id = int(file.readline())
            if p_id == processed_id:
                return True
            else:
                return False
        else:
            return False

    def update_meta(session_dir_path):
        path = os.path.join(session_dir_path,'META.META')
        with open(path,'w') as file:
            file.write('{}\n'.format(processed_id))

    expand_model()
    dd_metas=get_seq_results(output_seq,output_meta)
    
    for entry_name in dd_metas.keys():
        print('Checking derivation in {}'.format(entry_name))
        if is_test_mode and entry_name not in FOCUSED_ENTRIES:
            print('Since {} is not in FOCUSED ENTRIES, skipped.'.format(entry_name))
            continue
        full_entry_path = os.path.join(dir_path,entry_name)
        if check_meta(full_entry_path):
            print('Entry {} has been skipped due to processed_id<{}> being matched.'.format(full_entry_path,processed_id) )
            continue

        wrapped_models = get_models(dir_path,entry_name,dd_metas)
        annotate_wrt_derivations(full_entry_path,wrapped_models,dd_metas[entry_name],parser=ThyParser(semantics=ThyModelBuilderSemantics()))
        
        try:
            build_isabelle_repository(full_entry_path,wrapped_models,isa_bin,processed_id,threads)
        except subprocess.CalledProcessError as e:
            print('Failed to build:' + full_entry_path)
            continue 
        
        print('Entry {} has been processed successfully with processed_id<{}>. And the present time is {}.'.format(full_entry_path,processed_id,datetime.now()))
        update_meta(full_entry_path)

if __name__ == '__main__':
    def default_processed_id():
        now = datetime.now()
        return int("{}{}{}{}{}{}".format(now.year,now.month,now.day,now.hour,now.minute,now.second))

    parser = argparse.ArgumentParser(description='Preprocess Isabelle corpus')
    parser.add_argument('--isar_data', type=str, default='./test_isar_dataset',
                        help='The path of an Isabelle corpus')
    parser.add_argument('--isa_bin', type=str, default=None,
                        help='The path of an Isabelle2019 executable')
    parser.add_argument('--output_seq', type=str, default=None,
                        help='The path of an Isabelle corpus')
    parser.add_argument('--output_meta', type=str, default=None,
                        help='The path to the meta file')
    parser.add_argument('--processed_id', type=int, default=default_processed_id(),
                        help='An integer used for resuming processing a dataset')
    parser.add_argument('--threads', type=int, default=6,
                        help='Number of threads for the building process')
    parser.add_argument('--test_mode', type=bool, default=False,
                        help='True for testing')

    args = parser.parse_args()

    check_derivation(args.isar_data,args.isa_bin,args.output_seq,args.output_meta,args.processed_id,args.threads,args.test_mode)