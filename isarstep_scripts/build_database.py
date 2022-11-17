from isarstep_scripts.expand_thy_model import expand_model,KNOWN_FACT_COLLECTIONS,CollectedFacts,GlobalFact,LocalFact,FactDict,DependencyGraph,expand_model
from isarstep_scripts.print_theory import *
from isarstep_scripts.annotate_with_database import annotate_with_database, LOGFILE_PATH, append_to_log

# if either generated_thy_model.py or generated_thy_parser.py is not available, run 'python -m tatsu -o generated_parser/generated_thy_parser.py -G generated_parser/generated_thy_model.py  thy_model.ebnf'

# from generated_thy_model import *
# from generated_thy_parser import ThyParser, KEYWORDS
from tatsu.exceptions import *


from os.path import isfile, join,normpath
from os import listdir
import os
import subprocess
from multiprocessing import Pool
import multiprocessing
import base64
import warnings
import xml.etree.ElementTree as ET
from time import sleep
from datetime import datetime
import argparse

IGNORED_THEORIES = {
    'HOL/ex/Reflection_Examples.thy',
    'HOL/ex/Refute_Examples.thy',
    'HOL/ex/Commands.thy',
    'HOL/ex/Code_Lazy_Demo.thy',
    'HOL/ex/Meson_Test.thy',
    'HOL/ex/Cartouche_Examples.thy',
    'HOL/ex/ML.thy',
    'HOL/ex/Iff_Oracle.thy',
    'HOL/ex/Executable_Relation.thy',
    'HOL/Datatype_Examples/Compat.thy',
    'BNF_Operations/N2M.thy',
    'CAVA_LTL_Modelchecker/SM/Refine/Decide_Locality.thy',
    'CakeML_Codegen/Test/Test_Datatypes.thy',
    'CakeML/CakeML_Quickcheck.thy',
    'CakeML/Tests/Compiler_Test.thy',
    'Circus/Denotational_Semantics.thy',
    'Constructor_Funs/Test_Constructor_Funs.thy',
    'ComponentDependencies/DataDependencies.thy',
    'Consensus_Refined/Consensus_Misc.thy',
    'Datatype_Order_Generator/Derive.thy',
    'Deriving/Derive.thy',
    'Deriving/Comparator_Generator/RBT_Compare_Order_Impl.thy',
    'Game_Based_Crypto/CryptHOL_Tutorial.thy',
    'GewirthPGCProof/GewirthArgument.thy',
    'GewirthPGCProof/CJDDLplus.thy',
    'GoedelGod/GoedelGod.thy',
    'IMP2/automation/IMP2_Program_Analysis.thy',
    # 'Kruskal/Kruskal_Refine.thy',
    'Planarity_Certificates/Verification/Check_Non_Planarity_Impl.thy',
    'Planarity_Certificates/Verification/Check_Non_Planarity_Verification.thy',
    'Propositional_Proof_Systems/Tseytin_Sema.thy',
    'Safe_OCL/OCL_Examples.thy',

    'Gromov_Hyperbolicity/Morse_Gromov_Theorem.thy' 
}

IGNORED_DIRECTORIES = {
    'HOL/Eisbach/',
    'HOL/TPTP/',
    'HOL/Nominal/',
    'HOL/Statespace/',
    'HOL/Mirabelle/',
    'HOL/SMT_Examples/',
    'HOL/SPARK/',
    'HOL/Mutabelle/',
    'HOL/Quickcheck_Examples/',
    'HOL/Quotient_Examples/',
    'HOL/Predicate_Compile_Examples/',
    'HOL/Types_To_Sets/',
    'HOL/HOLCF/',
    'HOL/Proofs/',
    'HOL/Codegenerator_Test/',
    'HOL/Nitpick_Examples/',
    'HOL/Metis_Examples/',
    'HOL/Import/',
    'HOL/Induct/'
}

IGNORED_ENTRIES = {
    'Auto2_HOL',
    'Auto2_Imperative_HOL',
    'AnselmGod',
    'AxiomaticCategoryTheory',
    'Featherweight_OCL',
    'Generic_Deriving',
    'HOLCF-Prelude',
    'Incredible_Proof_Machine',
    'Iptables_Semantics',
    'Isabelle_Meta_Model',
    'LOFT',
    'Lazy_Case',
    'Lowe_Ontological_Argument',
    'Native_Word',
    'UTP',
    'Optics',
    'Partial_Function_MR',
    'Proof_Strategy_Language',
    'Propositional_Proof_Systems',
    'SDS_Impossibility',
    'Routing',
    'Stream-Fusion',
    'TortoiseHare',
    'Types_Tableaus_and_Goedels_God',
    'Tail_Recursive_Functions',
    'WorkerWrapper',

    'Nominal2',
    'Pi_Calculus',
    'Isabelle_C',
    'IMAP-CRDT'
}

with open("train_names.txt", "r") as f:
    train_li = f.read().splitlines()
IGNORED_ENTRIES.update(train_li)

FOCUSED_THEORIES = {
    'HOL/Transcendental.thy',
}

FOCUSED_ENTRIES = {
    # 'Stone_Relation_Algebras',
    # 'Lambda_Free_KBOs',
    # 'UPF_Firewall',
    'HOL',
    # 'Ordinary_Differential_Equations',
    # 'Prpu_Maxflow',
    # 'Polynomials'

    # 'Sturm_Tarski'

    # 'Closest_Pair_Points',
    # 'Gauss_Sums',
    # 'ZFC_in_HOL',
    # 'Poincare_Bendixson',
    # 'Generalized_Counting_Sort',
    # 'Approximation_Algorithms',
    # 'Hybrid_Systems_VCs',
    # 'Isabelle_C',
    # 'Generic_Join',
    # 'Interval_Arithmetic_Word32',
    # 'Bicategory',
    # 'Hybrid_Logic',
    # 'Fourier',
    # 'Zeta_3_Irrational',
    # 'Clean',
    # 'Aristotles_Assertoric_Syllogistic',
    # 'Sigma_Commit_Crypto',
    # 'VerifyThis2019',
    # 'Skip_Lists',
}

FOCUSED_DIRECTORIES = [
    'HOL/Induct/'
]

# IGNORED_THEOREMS = {
#     # fs == [] problems
#     ('HOL/Nat.thy', 'diff_induct42'), # isar_idx:[4, 4]
#     ('HOL/Hilbert_Choice.thy', 'wf_iff_no_infinite_down_chain84'), #isar_idx:[1, 7]
#     ('HOL/Wellfounded.thy', 'wf_trancl27'), #isar_idx:[0, 0, 1]
#     ('HOL/Topological_Spaces.thy', 'approx_from_above_dense_linorder221'), #isar_idx:[3]
#     ('HOL/Topological_Spaces.thy', 'approx_from_below_dense_linorder222'), #isar_idx:[3]
#     ('HOL/Transcendental.thy', 'summable_Leibniz30'), #isar_idx:[0, 4], isar_idx:[0, 18]
#     ('HOL/Transcendental.thy', 'arctan_series710'), #isar_idx:[5, 9, 3]
#     ('HOL/Real_Vector_Spaces.thy', 'complete_def281'), #isar_idx:[17, 0, 3])
#     ('HOL/Product_Type.thy', 'split_paired_all91'), #isar_idx:[6])
#     ('HOL/Library/Extended_Real.thy', 'suminf_ereal_minus431'), #isar_idx:[6], isar_idx:[1]
#     ('HOL/Library/Extended_Real.thy', 'suminf_le_pos423'), #isar_idx:[3]

#     # matching error when adding a global fact
#     ('HOL/Algebra/Complete_Lattice.thy', 'Knaster_Tarski44'), #isar_idx: [2, 3, 8, 12, 2, 3]

#     # issue with pre_facts for the very first isar statement in a proof block
#     ('HOL/Analysis/Equivalence_Lebesgue_Henstock_Integration.thy','has_integral_integral_real13') ,#isar_idx: [0]
# }

def build_isabelle_repository(dir_path,wrapped_thy_models,isa_bin,processed_id=-1):
    
    # for (root , dirs , _) in os.walk(dir_path): 
    #     os.makedirs(join(root,'Database'), exist_ok=True)
    #     for dd in dirs:
    #         os.makedirs(join(root,dd,'Database'), exist_ok=True)
    #     break
    thy_models = list(map(lambda x:x.thy_model,wrapped_thy_models))
    for (root , _ , _) in os.walk(dir_path): 
        if os.path.basename(root) in {'Database','InterSteps','AlternativeCausalSteps','CausalSteps'\
            ,'TransitiveSteps','document','CheckingDerivation'}: # ignore some special directories
            continue
        os.makedirs(join(root,'Database'), exist_ok=True)
        os.makedirs(join(root,'CausalSteps'), exist_ok=True)
        os.makedirs(join(root,'AlternativeCausalSteps'), exist_ok=True)
        os.makedirs(join(root,'TransitiveSteps'), exist_ok=True)
    for model in thy_models:
        database_path = join(os.path.dirname(model.filepath),'Database',model.thy_name+'.xml')
        with open(database_path,'w') as file:
            file.write('<database processed_id="{}">\n'.format(str(processed_id)) )
    bashCommand = '{} build -c -D  {}'.format(isa_bin,dir_path)
    process = subprocess.run(bashCommand.split(), check=True)
    
    # deleting this part may increase the chance that '</database>\n' being inserted in the middle of Database.xml --- I know this quick and dirty...
    print('{} has been built.'.format(dir_path)) 
    sleep(1)

    for model in thy_models:
        database_path = join(os.path.dirname(model.filepath),'Database',model.thy_name+'.xml')
        with open(database_path,'a') as file:
            file.write('</database>\n')
    return process.returncode

    # output, error = process.communicate()
    # print('output is {}; error is {}'.format(output,error))

# def extract_thy_models(dir_path,purge_diagnostic=False):
#     full_thy_names = []
#     for (_ , _ , filenames) in os.walk(dir_path):
#         for f in filenames:
#             if f.endswith('.thy'):
#                 full_thy_names.append(f)
#         break

#     parser = ThyParser(semantics=ThyModelBuilderSemantics())
#     thy_models = []
#     for thy_name in full_thy_names:
#         thy_path=os.path.join(dir_path,thy_name)
#         with open(thy_path,'r+') as file:
#             thy_src = file.read()
#             try:
#                 model = parser.parse(thy_src)
#             except FailedParse as error:
#                 print('Failed to parse:' + thy_path)
#                 print(error)
#                 raise
#             model.annotate_Theorems()
#             model.add_diagnostic()
#             model.filepath = thy_path
#             if purge_diagnostic:
#                 model.purge_diagnostic()
#             thy_models.append(model)
#     return thy_models

class NameToModel:
    def __init__(self,parser,dir_path,purge_diagnostic,keep_diagnostic,processed_id):
        self.parser = parser
        self.dir_path = dir_path
        # self.dir_name = os.path.basename(os.path.normpath(dir_path))
        # self.subdir_name = subdir_name
        self.purge_diagnostic = purge_diagnostic
        self.keep_diagnostic = keep_diagnostic
        self.processed_id = processed_id

    def name_to_model(self,full_filename):
        # def get_full_thy_name():
        #     if self.subdir_name is None:
        #         return self.dir_name+'.'+full_filename
        #     else:
        #         return self.dir_name+'.'+self.subdir_name+'.'+full_filename
        thy_path=os.path.normpath(join(self.dir_path,'..',full_filename))
        # print( 'self.dir_path is {}, full_filename is {}, thy_path is {}'.format(self.dir_path,full_filename,thy_path))
        with open(thy_path,'r+') as file:
            thy_src = file.read()
            try:
                model = self.parser.parse(thy_src)
            except FailedParse as error:
                append_to_log('Failed to parse {}.\n{}\n'.format(thy_path,str(error)))
                print('Failed to parse:' + thy_path)
                return WrappedThyModel(None,self.processed_id)
                # print('Failed to parse:' + thy_path)
                # print(error)
                # raise
            model.annotate_Theorems()
            # with open(LOGFILE_PATH,'a') as file:
            #     file.write(json.dumps(model.get_Theorem_by_id('thm_filterlim_sequentially_iff_filterlim_real0').asjson(),indent=4))  
            if not self.keep_diagnostic:
                model.purge_diagnostic()
            try:
                model.add_diagnostic()
            except:
                print('Error in ' + full_filename )
                raise
            model.filepath = thy_path
            model.full_filename = full_filename
            # model.diag_thy_path = DIAG_THY_PATH
            if self.purge_diagnostic:
                model.purge_diagnostic()
            return WrappedThyModel(model,self.processed_id )

def remove_prefix(text, prefix):
    if text.startswith(prefix):
        return text[len(prefix):]
    assert False, '"{}" is not a prefix of "{}"'.format(prefix,text)

def extract_thy_models(dir_path,purge_diagnostic=False\
        ,keep_diagnostic = False,visible_opt='DEFAULT',processed_id=-1):
    print('Start extracting models from '+dir_path)
    full_thy_names = []
    dir_path_parent = normpath(join(normpath(dir_path),'..'))
    for root, _ , filenames in os.walk(dir_path):
        for filename in filenames:
            # print('root {}, filename {}, dir_path {}, dir_path_parent {}'.format(root,filename,dir_path,dir_path_parent) )
            f_name = join(remove_prefix(root,join(dir_path_parent,'')),filename)
            # f_name = os.path.normpath(join(root, filename))
            # if f_name != 'HOL/Analysis/ex/Approximations.thy': # TODO:remove
            #     continue

            if not filename.endswith('.thy') or f_name in IGNORED_THEORIES\
                    or any(map(f_name.startswith,IGNORED_DIRECTORIES)):
                continue
            if visible_opt == 'DEFAULT' :
                full_thy_names.append(f_name)
            else:
                assert visible_opt == 'FOCUSED_DIR'
                if any(map(f_name.startswith,FOCUSED_DIRECTORIES)):
                    full_thy_names.append(f_name)
    parser = ThyParser(semantics=ThyModelBuilderSemantics())
    n2m = NameToModel(parser,dir_path,purge_diagnostic,keep_diagnostic,processed_id)
    with Pool(multiprocessing.cpu_count()-1) as p:
        thy_models = list(p.imap_unordered(n2m.name_to_model, full_thy_names))
    print('{} theories have been parsed'.format(len(thy_models)) )
    thy_models = list(filter(lambda x: x.thy_model is not None,thy_models))
    return thy_models
    
def build_database(dir_path,thy_models,isa_bin,processed_id=-1):
    print('Start building the directory '+dir_path)
    for wrapped_model in thy_models:
        model=wrapped_model.thy_model
        assert model.filepath.startswith(os.path.normpath(dir_path))
        try:
            thy_str = StringOfTheory(incl_recording=True).str_Theory(model)
        except Exception as error:
            append_to_log('Fail to print the theory {}.\n{}\n'.format(model.full_filename,str(error)))
            print('fail to print theory:' + model.full_filename)
            return 
            # print('fail to print theory:' + model.full_filename)
            # raise
        with open(model.filepath,'w') as file:
            file.write(thy_str)    
    build_isabelle_repository(dir_path,thy_models,isa_bin,processed_id=processed_id)








    # print(full_thy_names)
    # print(StringOfTheory(True).str_Theory(thy_models[0]))
    # # print(thy_models[0])

    # thy_models[0].purge_diagnostic()
    # print('xxxxxxxxxxxxxxxxxxxxxxxxxxx')
    # print(StringOfTheory().str_Theory(thy_models[0]))

class WrappedThyModel:
    def __init__(self,thy_model,processed_id):
        self.thy_model = thy_model
        self.processed_id = processed_id


def create_dataset(dir_path,isa_bin ,visible_opt = 'DEFAULT',processed_id = 0, no_build=False):
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
         

    with open(LOGFILE_PATH,'w') as file:
        file.write('The log stats:\n\n')

    for (_ , dir_names , _) in os.walk(dir_path): 
        for dir_name in dir_names:
            if visible_opt == 'FOCUSED_ENTRIES' and dir_name not in FOCUSED_ENTRIES:
                continue
            if dir_name in IGNORED_ENTRIES:
                print('Dataset {} has been skipped due to being in IGNORED_ENTRIES'.format(dir_name))
                continue
            session_dir_path = os.path.normpath(join(dir_path, dir_name))
            if check_meta(session_dir_path):
                print('Dataset {} has been skipped due to processed_id<{}> being matched.'.format(session_dir_path,processed_id) )
                continue

            print('Start processing dataset {}.'.format(session_dir_path))
            wrapped_models = extract_thy_models(session_dir_path,purge_diagnostic=False,keep_diagnostic=False
                ,visible_opt='DEFAULT',processed_id=processed_id
                )
            # print( json.dumps(wrapped_models[0].thy_model.get_Theorem_by_name('foo1').proof.get_IsarStatement([1]).asjson(),indent=4) )
            if not no_build:
                try:
                    build_database(session_dir_path,wrapped_models,isa_bin,processed_id=processed_id)
                except subprocess.CalledProcessError as e:
                    append_to_log('Failed to build {}.\n{}\n'.format(session_dir_path,e.output))
                    print('Failed to build:' + session_dir_path)
                    continue 
            else:
                print('NOT trying to build {}. Start annotation directly.'.format(session_dir_path))
            
            annotate_with_database(session_dir_path,wrapped_models)
            
            # print(wrapped_models[0].thy_model.get_Theorem_by_id('thm_de_Morgan9')._fact_dict.local_dict_by_ascii )
            # print(w_models[0].thy_model.get_Theorem_by_id('thm_de_Morgan9')._fact_dict.local_dict_by_ascii ) 
            # print(wrapped_models[0].thy_model.get_Theorem_by_id('thm_de_Morgan9') ) 
            # except:
            #     append_to_log('Failed (critically) to annotate {}.\n'.format(session_dir_path))
            #     continue
            update_meta(session_dir_path)
            print('Dataset from {} has been created successfully with processed_id<{}>. And the present time is {}.'.format(session_dir_path,processed_id,datetime.now()))
        break

def build_models(dir_path,isa_bin,processed_id):
    expand_model()
    
    # thy_src = open('Test/Drinker.thy').read()
    # parse_and_walk_model(thy_src)

    # create_dataset('./dataset'\
    #     ,visible_opt='FOCUSED_ENTRIES'
    #     )

    # create_dataset('./test_isar_dataset')
    # create_dataset(dir_path,isa_bin,visible_opt='FOCUSED_ENTRIES',processed_id=processed_id, no_build=False)
    create_dataset(dir_path,isa_bin,processed_id=processed_id)

    # dir_path = './Test'
    # dir_path = './Sturm_Tarski'
    # dir_path = './HOL'
    # wrapped_models = extract_thy_models(dir_path,purge_diagnostic=False,keep_diagnostic=False
    #     # ,visible_opt='FOCUSED_DIR'
    #     ,visible_opt='DEFAULT'
    #     )
    # build_database(dir_path,wrapped_models)
    # annotate_with_database(dir_path,wrapped_models)
   
    # isar_stat = models[0].get_Theorem('foo').proof.get_IsarStatement([1])
    # print( models[0].get_Theorem_by_name('euclidean_size_eq_0_iff').proof.get_IsarStatement([4,1]) )
    # print( models[0].get_Theorem('sign_r_pos_mult').fact_dict.get_local_by_location([4,1]) )
    # print( models[0].get_Theorem('euclidean_size_eq_0_iff').fact_dict.local_dict_by_ascii)
    # print( models[0].get_Theorem_by_name('fact_in_Reals').proof)
    # print( models[0].get_Theorem_by_name('fact_in_Reals').proof.retrieve_used_global_facts())
    # print( models[0].get_Theorem_by_name('fact_in_Reals').thm_reprs)
    # print( models[0].get_Theorem_by_id('None0').str_neighbours_of_location([0,4]) )
    
    # print(isar_stat.proof.retrieve_facts(isar_stat)[1][0] )
    # print(isar_stat.proof.diag_stats_pre)

    # print(StringOfTheory(True).str_Theory(models[0]))
    # print(type(models[0].filepath))
    # print(models[0].filepath.startswith('./Test') ) 
    # return models

  

if __name__ == '__main__':
    def default_processed_id():
        
        now = datetime.now()
        return int("{}{}{}{}{}{}".format(now.year,now.month,now.day,now.hour,now.minute,now.second))

    parser = argparse.ArgumentParser(description='Preprocess Isabelle corpus')
    parser.add_argument('--isa_bin', type=str, default='/home/wenda/Programs/Isabelle2019/bin/isabelle',
                        help='The path of an Isabelle2019 executable')
    parser.add_argument('--isar_data', type=str, default='./isarstep_scripts/test_isar_dataset',
                        help='The path of an Isabelle corpus')
    parser.add_argument('--processed_id', type=int, default=default_processed_id(),
                        help='An integer used for resuming processing a dataset')
    args = parser.parse_args()

    build_models(args.isar_data,args.isa_bin,args.processed_id)
