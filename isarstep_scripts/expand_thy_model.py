from isarstep_scripts.print_theory import *
from isarstep_scripts.parse_isabelle_term.isabelle_term import *

import os

# import xml.etree.ElementTree as ET

KNOWN_FACT_COLLECTIONS = {
    'tendsto_intros','tendsto_eq_intros'
    ,'derivative_intros','derivative_eq_intros'
    ,'continuous_intros'
    ,'algebra_simps','field_simps','ac_simps','divide_simps'
    
    ,'com','inv','loc' # in ConcurrentIMP
    }

# DIAG_THY_PATH = '"'+ os.path.join(os.getcwd(),'Recording/ProofRecording')+'"'
# DIAG_THY_PATH = ['"'+ os.path.join(os.path.dirname(os.path.realpath(__file__)),'Recording/ProofRecording')+'"',\
#                 '"'+ os.path.join(os.path.dirname(os.path.realpath(__file__)),'Recording/Sequence_Evaluation')+'"']

DIAG_THY_PATH_RECORDING = '"'+ os.path.join(os.path.dirname(os.path.realpath(__file__)),'Recording/ProofRecording')+'"'
DIAG_THY_PATH_EVALUATION = '"'+ os.path.join(os.path.dirname(os.path.realpath(__file__)),'Recording/Sequence_Evaluation')+'"'

print(DIAG_THY_PATH_EVALUATION)

class Fact(object):
    pass

class CollectedFacts(Fact):
    def __init__(self,name):
        self.name = name

#referenced by the theorem name
class GlobalFact(Fact):
    def __init__(self,fact_name,fact_index,content_in_term : Term, content_in_ascii,content_in_latex,content_in_yxml):
        self.fact_name = fact_name
        self.fact_index = fact_index
        self.content_in_term = content_in_term
        self.content_in_ascii = content_in_ascii
        self.content_in_latex = content_in_latex
        self.content_in_yxml = content_in_yxml
        
    def __str__(self):
        return '{}({}):{}'.format(self.fact_name,self.fact_index,self.content_in_ascii)
    
class LocalFact(Fact):
    def __init__(self, location_in_theorem, refinement_step_location,content_in_term : Term, content_in_ascii,content_in_latex, content_in_yxml\
            ,compound_index=None,next_next_idx=None,content_in_ascii_original=None,text_infomation=None,has_forward=False):
        self.content_in_term = content_in_term
        self.content_in_yxml = content_in_yxml
        self.content_in_ascii = content_in_ascii
        self.content_in_ascii_original = content_in_ascii_original
        self.content_in_latex = content_in_latex
        self.location_in_theorem = location_in_theorem # Isar location e.g. [1,2,3]
        self.refinement_step_location = refinement_step_location
        self.compound_index = compound_index
        self.next_next_idx = next_next_idx
        self.text_infomation = text_infomation
        self.has_forward = has_forward

    def __str__(self):
        loc_str = '('+str(self.location_in_theorem)+','+ str(self.refinement_step_location)+')'
        if self.compound_index is None:
            result_str = self.content_in_ascii +' @ '+loc_str
        else:
            result_str = self.content_in_ascii +' @ '+loc_str + ' - ' + str(self.compound_index)
        if self.next_next_idx is not None:
            result_str += ' NNext@ ' +str(self.next_next_idx) 
        return result_str

    def visible_from_loc(self,isar_loc):
        if not isar_loc:
            return True
        if self.next_next_idx is None:
            check_next_next = True # check_next_next is True if there is no visibility issue caused by 'next'
        else:
            check_next_next = isar_loc < self.next_next_idx
        # not considering the Isar command 'next'
        if len(self.location_in_theorem) > len(isar_loc):
            if self.location_in_theorem and self.location_in_theorem[-1] == -1 \
                    and self.location_in_theorem[:-1] == isar_loc:
                return True
            return False
        elif len(self.location_in_theorem) == len(isar_loc):
            return self.location_in_theorem[:-1] == isar_loc[:-1] and self.location_in_theorem[-1] < isar_loc[-1] and check_next_next
        elif self.compound_index is None:
            return self.location_in_theorem < isar_loc and check_next_next
        else:
            return self.location_in_theorem == isar_loc

    def visible_from_rs_loc(self,rs_location):
        if not rs_location or not self.refinement_step_location:
            return True
        if len(self.refinement_step_location) > len(rs_location):
            return False
        elif len(self.refinement_step_location) == len(rs_location):
            return self.refinement_step_location[:-1] == rs_location[:-1] and self.refinement_step_location[-1] <= rs_location[-1]
        else:
            return self.refinement_step_location < rs_location
            

class FactDict:

    def __init__(self):
        self.local_dict_by_ascii = {} # key: content_in_ascii in LocalFact; value: a list of LocalFact
        self.local_dict_by_location = {} # key: str_of_list(location_in_theorem) in LocalFact; value: a list of LocalFact
        self.global_fact_dict = {} # key: a tuple (name,name_index) in GlobalFact; value: a GlobalFact

    def get_all_local_facts(self):
        facts = []
        for ff in self.local_dict_by_ascii.values():
            facts.extend(ff)
        return facts

    def get_all_global_facts(self):
        return list(self.global_fact_dict.values())

    def add_local_fact(self, local_fact):
        if local_fact.content_in_ascii in self.local_dict_by_ascii:
            self.local_dict_by_ascii[local_fact.content_in_ascii].append(local_fact)
        else:
            self.local_dict_by_ascii[local_fact.content_in_ascii] = [local_fact]
        loc_key_str = (str_of_list(local_fact.location_in_theorem)\
            ,str_of_tuple(local_fact.refinement_step_location)\
            ,str(local_fact.compound_index))    
        if loc_key_str in self.local_dict_by_location:
            self.local_dict_by_location[loc_key_str].append(local_fact)
        else:
            self.local_dict_by_location[loc_key_str] = [local_fact]

    def get_local_by_ascii(self,content_in_ascii,reveal_compound=False):
        if content_in_ascii in self.local_dict_by_ascii: 
            if reveal_compound:
                return self.local_dict_by_ascii[content_in_ascii]
            else:
                rr=self.local_dict_by_ascii[content_in_ascii]
                return list(filter(lambda x: x.compound_index is None,rr) )
        else:
            return []
    
    def get_local_by_location(self,isar_location, rs_location=None,compound_index=None,ascii_cont=None):
        '''
        ascii_cont can be used to further refine the results
        '''
        def remove_newline(s): #ascii_cont can sometimes contain mysterious newline charater when we may want to remove before making comparison
            return s.replace("\n","")

        key = (str_of_list(isar_location),str_of_tuple(rs_location),str(compound_index))
        if key in self.local_dict_by_location:
            res = self.local_dict_by_location[key]
            if ascii_cont is None:
                return res
            else:
                return list(filter(lambda x: remove_newline(x.content_in_ascii) == remove_newline(ascii_cont),res) )
        else:
            return []

    def get_global(self, fact_name, fact_index=1):
        if (fact_name,fact_index) in self.global_fact_dict:
            return self.global_fact_dict[(fact_name,fact_index)]
        else:
            return None

    def add_global_fact(self, global_fact):
        key = (global_fact.fact_name,global_fact.fact_index)
        assert key not in self.global_fact_dict
        self.global_fact_dict[key] = global_fact

class DependencyGraph:

    def __init__(self):
        self.dict_of_used_local = {} # key: a LocalFact; value: a list of LocalFact being used by the key
        self.dict_of_used_global = {} # key: a LocalFact; value: a list of GlobalFact being used by the key
        self.dict_of_consequences = {} # key: a LocalFact; value: a list of LocalFact making use of the key

    def get_used_locals(self,fact):
        return self.dict_of_used_local[fact]

    def get_used_globals(self,fact):
        return self.dict_of_used_global[fact]

    def get_consequences(self,fact):
        return self.dict_of_consequences[fact]

    def add_local_fact(self,fact):
        self.dict_of_consequences[fact] = []
        self.dict_of_used_local[fact] = []
        self.dict_of_used_global[fact] = []

    def add_local_local(self,fact1,fact2): # fact1 leads to fact2
        # print('fact1 is{};fact2 is{}'.format(str(fact1) ,str(fact2) ) )
        self.dict_of_consequences[fact1].append(fact2)
        self.dict_of_used_local[fact2].append(fact1)
    
    def add_used_global(self,local_fact,global_fact):
        assert isinstance(global_fact,GlobalFact) or isinstance(global_fact,CollectedFacts)
        self.dict_of_used_global[local_fact].append(global_fact)

    def str_neighbours_of_fact(self,local_fact):
        facts_str = 'target fact is\n\t'+str(local_fact)+'\n'
        facts_str+= 'utilised these local facts:\n'
        for fact in self.dict_of_used_local[local_fact]:
            facts_str += '\t'+str(fact)+'\n'
        facts_str+='utilised these global facts:\n'
        for fact in self.dict_of_used_global[local_fact]:
            facts_str += '\t'+str(fact)+'\n'
        facts_str+='leading to those local facts:\n'
        for fact in self.dict_of_consequences[local_fact]:
            facts_str += '\t'+str(fact)+'\n'
        return facts_str

class StepIndexError(Exception):
    pass

def expand_ForwardModifier():
    def retrieve_all_facts(self): # return a list of FactReference that occurs in this modifier
        facts = []
        for sf in self.cont:
            if sf != ',' and sf.key in ['OF','THEN','folded','unfolded','simplified','case_product','to_pred','to_set','FCOMP']:
                for ff in sf.facts:
                    if ff != '_':
                        facts.append(ff)
                        if isinstance(ff.for_mod,ForwardModifier):
                            facts.extend(retrieve_all_facts(ff.for_mod))
        return facts
    ForwardModifier.retrieve_all_facts = retrieve_all_facts

def expand_FactReference():

    def set_from_fact(self,fact):
        def enclose_open_close(s:str):
            return '\\<open>'+ s +'\\<close>'

        if isinstance(fact,LocalFact):
            self.cont = enclose_open_close(fact.content_in_ascii_original)
        elif isinstance(fact,GlobalFact):
            self.fact_name = fact.fact_name
            self.sel = Selection().set_index(fact.fact_index)
        else:
            assert isinstance(fact,CollectedFacts)
            self.fact_name = fact.name
        return self

    def set_fact_name(self,fact_name_str):
        assert isinstance(fact_name_str,str)
        self.fact_name = fact_name_str
        return self

    def without_forward_modifier(self):
        return FactReference(fact_name = self.fact_name, sel= self.sel, for_mod = None, cont = self.cont)

    def get_name_and_sel(self):
        if self.fact_name is not None:
            sel_str = '' if self.sel is None else str(self.sel)
            return self.fact_name.replace('\"','')+ sel_str 
        else:
            assert self.cont is not None 
            return '<unnamed>'
        
    def is_equal_to(self,fact):
        if isinstance(fact,str):
            if self.fact_name == fact \
                and self.sel is None and self.for_mod is None:
                return True
            else:
                return False
        else:
            return NotImplemented

    FactReference.set_from_fact = set_from_fact
    FactReference.set_fact_name = set_fact_name
    FactReference.is_equal_to = is_equal_to
    FactReference.without_forward_modifier=without_forward_modifier
    FactReference.get_name_and_sel = get_name_and_sel
    FactReference.__str__ = (lambda self: StringOfTheory().str_FactReference(self))

# def expand_IsPattern():
#     IsPattern.__str__ = (lambda self: StringOfTheory().str_IsPattern(self))

def expand_Selection():

    def set_index(self,idx:int):
        self.cont = [idx]
        return self

    def retrieve_indices(self,max_index = None):
        indices = []
        for tt in self.cont:
            if tt != ',':
                if isinstance(tt,list):
                    if len(tt) ==3:
                        indices.extend(list(range(tt[0],tt[2]+1)))
                    else:
                        assert len(tt) ==2 and max_index is not None
                        indices.extend(list(range(tt[0],max_index+1)))
                else:
                    assert isinstance(tt,int)
                    indices.append(tt)
        return indices

    def infer_max_index(self, num_of_avail_entries):
        num_ubd = 0 # counting the number of unbounded intervals
        rem_entries = num_of_avail_entries # recording the number of remaining entries
        for tt in self.cont:
            if tt != ',':
                if isinstance(tt,list):
                    if len(tt) ==3:
                        rem_entries -= (tt[2]+1 - tt[0])
                    else:
                        assert len(tt) ==2 
                        rem_entries+=tt[0]
                        num_ubd+=1
                else:
                    assert isinstance(tt,int)
                    rem_entries -= 1
        if num_ubd == 0:
            return None # not possible to infer the max index without unbounded intervals
        else:
            assert rem_entries % num_ubd == 0
            return (rem_entries // num_ubd) - 1

    Selection.infer_max_index = infer_max_index
    Selection.retrieve_indices = retrieve_indices
    Selection.__str__ = (lambda self: StringOfTheory().str_Selection(self))
    Selection.set_index = set_index

def expand_Tactic():
    def retrieve_relevant_facts(self):
        def retr_facts(model): #retrive facts from single_tactic
            if model.key in ['cases','relation','case_tac','injectivity_solver','transfer_hma','inst_existentials']:
                return [model.rule_fact[-1]] if isinstance(model.rule_fact,list) else [] 
            elif model.key == 'subst':
                assert model.fact is None
                return model.facts
            elif model.key == 'rewrite':
                return [model.fact]
            elif model.key in ['rule_tac','drule_tac','erule_tac','frule_tac','cut_tac','subst_tac','transfer'\
                ,"transfer'",'master_theorem','r_compose','hoare_rule','has_type_tac',"has_type_tac'",'has_type_no_if_tac','if_type_tac', 'seq_decl_inv_method'\
                ,'seq_stop_inv_method','sep_auto','PLM_solver','vcg']:
                assert model.fact is None
                return flatten(model.facts)
            elif model.key in ['rename_tac','tactic','subgoal_tac',
                'thin_tac','ind_cases','rotate_tac','frpar2','frpar','approximation','autoref','sos']:
                return []
            elif model.key == 'use':
                fact_tuples = []
                fact_tuples.extend(model.facts)
                if isinstance(model.more_tac,list):
                    for cc in model.more_tac[1]:
                        if cc not in [',',';','|']: # cc is a single tactic
                            fact_tuples.extend(retr_facts(cc))
                # if isinstance(model.more_tac,list):
                #     fact_tuples.extend(retr_facts(model.more_tac[1]))
                return fact_tuples
            elif model.key == 'all':
                fact_tuples = []
                if isinstance(model.more_tac,list):
                    for cc in model.more_tac[1]:
                        if cc not in [',',';','|']: # cc is a single tactic
                            fact_tuples.extend(retr_facts(cc))
                return fact_tuples
            elif model.key in ['induct','induction','induct_tac','coinduct','coinduction','nominal_induct']:
                if isinstance(model.induct_rule,list):
                    assert isinstance(model.induct_rule[-1][0], FactReference)
                    return model.induct_rule[-1]
                else:
                    return []
            elif isinstance(model.key,Tactic):
                return model.key.retrieve_relevant_facts()
            else:
                assert model.key is None, model.key 
                assert model.method_name is not None, model.method_name
                fact_tuples = []
                for fs in flatten(model.facts):
                    if isinstance(fs,FactReference):
                        fact_tuples.append(fs)

                    # if isinstance(fs,list):
                    #     for f in fs:
                    #         fact_tuples.append(f)
                    # else:
                    #     assert isinstance(fs,FactReference)
                    #     fact_tuples.append(fs)
                return fact_tuples

        if self.key == '(':
            facts = []
            facts.extend(retr_facts(self.main_tactic))
            for tt in self.more_tactics:
                assert tt[0] in [',',';','|']
                facts.extend(retr_facts(tt[1]))
            return facts
        else:
            #self.key is a name or '-'
            return []
        
    Tactic.retrieve_relevant_facts = retrieve_relevant_facts

def rs_location_from_str(s):
    from ast import literal_eval as make_tuple
    res = make_tuple(s)
    assert isinstance(res,tuple), s
    return res 

def isar_location_from_str(s):
    from ast import literal_eval as make_list
    res = make_list(s)
    assert isinstance(res,list), s
    return res 

def expand_ProofBlock():
    def get_RefinementStep(self,rs_location): 
        '''
            return an IsarStatement if rs_location ending with a list like ([1,2],3,[4])
            , otherwise return a RefinementStep when rs_location ending with an integer like ([1,2],3)
        '''
        hd,tail = rs_location[0],rs_location[1:]
        if len(tail) == 0:
            isar = get_IsarStatement(self,hd)
            return isar 
        if hd:
            isar = get_IsarStatement(self,hd)
            rstep = isar.proof.rsteps[tail[0]]
        else: # hd is []
            rstep = self.rsteps[tail[0]]
        if len(tail) == 1:
            return rstep
        else: # the step is within a subgoal_block
            assert len(tail) > 1 
            return get_RefinementStep(rstep.sblock.proof,tail[1:])

    def get_IsarStatement(self, stat_idx):
        def get_Isar_from_Isar(model,idx):
            if not idx:
                # print(idx,model.asjson())
                return model
            else:
                if model.key == '{':
                    hd,tail = idx[0],idx[1:]
                    assert hd >= 0
                    return get_Isar_from_Isar(model.isar_stats[hd],tail)
                else:
                    return model.proof.get_IsarStatement(idx)

        hd,tail = stat_idx[0],stat_idx[1:]
        assert hd >= 0
        try:
            if isinstance(self.key, ProofQed):
                isar = self.key.isar_stats[hd]
            else:
                raise IndexError
            res = get_Isar_from_Isar(isar,tail)
        except IndexError:
            raise StepIndexError('Trying to access an non-exist IsarStatement!')
        return res


    def retrieve_facts(self, attached_isar = None, include_special_fact = False):
        # attached_isar is used for extracting facts in the from/with part in an IsarStatement
        # returns (pre_facts,pre_facts_,facts,isar_facts), both of which are lists of FactReference, where xs is from the from/with part, isar_facts are from isar statements, and facts are facts from the rest.
        pre_facts = [] 
        if attached_isar is not None:
            if attached_isar.key in ['have','show','obtain','hence','thus','interpret','consider','guess']:
                if attached_isar.pre_facts is not None:
                    pf = attached_isar.pre_facts
                    if 'then' in pf or 'with' in pf:
                        pre_facts.append(FactReference().set_fact_name('this'))
                    # if 'finally' in pf and include_special_fact:
                    #     pre_facts.append(FactReference().set_fact_name('<finally>'))
                    pre_facts.extend(list(filter(lambda x:isinstance(x,FactReference),pf)))
                else:
                    if attached_isar.key in ['hence','thus'] :
                        pre_facts.append(FactReference().set_fact_name('this'))
            if attached_isar.key == 'note':
                assert self.key == '@phantom'
                facts = list(filter(lambda x:isinstance(x,FactReference),flatten(attached_isar.facts)))
                # pre_facts.extend( flatten(attached_isar.facts) ) 
                pre_facts.extend(facts)                      
        
        pre_facts2 = []
        if attached_isar is not None:
            if attached_isar.key in ['have','show','obtain','consider','guess' ]:
                if attached_isar.pre_facts == ['ultimately']:
                    pre_facts2.append(FactReference().set_fact_name('this'))
                elif attached_isar.pre_facts == ['finally'] and include_special_fact:
                    pre_facts2.append(FactReference().set_fact_name('<finally>'))

        facts = []
        if self.rsteps is not None:
            for rs in self.rsteps:
                facts.extend(rs.retrieve_relevant_facts())
        if isinstance(self.key,ProofQed):
            if self.key.main_tac is not None:
                facts.extend(self.key.main_tac.retrieve_relevant_facts())
            if self.key.closing_tac is not None:
                facts.extend(self.key.closing_tac.retrieve_relevant_facts())
        elif isinstance(self.key,ClosingStep):
            facts.extend(self.key.retrieve_relevant_facts())
        else:
            assert self.key == '@phantom'
            pass
        
        return (pre_facts,pre_facts2,facts,[])

    def retrieve_used_local_facts(self): # editable list
        if self._used_local_fact is None:
            self._used_local_fact = []
        return self._used_local_fact

    def retrieve_used_global_facts(self): # editable list
        if self._used_global_fact is None:
            self._used_global_fact = []
        return self._used_global_fact
    
    def str_used_facts(self):
        facts_str = ''
        facts_str+= 'local facts:\n'
        for fact in self.retrieve_used_local_facts():
            facts_str += '\t'+str(fact)+'\n'
        facts_str+='global facts:\n'
        for fact in self.retrieve_used_global_facts():
            facts_str += '\t'+str(fact)+'\n'
        return facts_str

    ProofBlock.get_RefinementStep = get_RefinementStep
    ProofBlock.get_IsarStatement = get_IsarStatement
    ProofBlock.retrieve_facts = retrieve_facts
    ProofBlock.retrieve_used_local_facts = retrieve_used_local_facts
    ProofBlock.retrieve_used_global_facts = retrieve_used_global_facts
    ProofBlock.str_used_facts = str_used_facts
    ProofBlock._used_local_fact = None # elements of this list are from FactDict associated with each theorem
    ProofBlock._used_global_fact = None # elements of this list are from FactDict associated with each theorem 

def expand_Propositions():
    def get_prop (self, index): # deprecated
        if index < len(self.main_conts):
            return self.main_conts[index]
        local_index= index - len(self.main_conts)
        for cc in self.more_conts: 
            if local_index < len(cc[-1]):
                return cc[-1][local_index]
            else:
                local_index -= len(cc[-1])
        raise Exception('Out-of-boundary index', index) 

    def set_prop (self, index, prop_in_str): # deprecated
        if index < len(self.main_conts):
            self.main_conts[index] = prop_in_str
            return None
        local_index= index - len(self.main_conts)
        for cc in self.more_conts: 
            if local_index < len(cc[-1]):
                cc[-1][local_index] = prop_in_str
                return None
            else:
                local_index -= len(cc[-1])
        raise Exception('Out-of-boundary index', index) 

    def length(self): # deprecated
        length = len(self.main_conts)
        for cc in self.more_conts:
            length += len(cc[-1])
        return length

    Propositions.get_prop = get_prop
    Propositions.set_prop = set_prop
    Propositions.length = length
    Propositions.__str__ = (lambda self: StringOfTheory().str_Propositions(self))

def expand_IsarStatement():
    IsarStatement._theorem = None
    IsarStatement._theory = None
    IsarStatement.location_in_theorem = None # encoded as a list of integers; work with ProofBlock.get_IsarStatement
    IsarStatement.rs_location = None # e.g. ([1],3,[4]), used when the statement is within a subgoal_block
    
    IsarStatement.__str__ = (lambda self: StringOfTheory(True).str_IsarStatement(self))

# def expand_LongName():
#     LongName.__str__ = (lambda self: StringOfTheory().str_LongName(self))

def expand_Theory():

    def get_all_Theorems(self):
        def get_from_LocaleClass(model):
            more_thms = []
            if not isinstance(model.ex_thy_stats,list):
                return more_thms
            for st in model.ex_thy_stats[1]:
                assert not isinstance(st,LocaleClass)
                if isinstance(st,Theorem):
                    more_thms.append(st)
                if isinstance(st,Context):
                    more_thms.extend(get_from_Context(st))
            return more_thms
        
        def get_from_Context(model):
            more_thms = []
            for st in model.thy_stats:
                assert not isinstance(st,LocaleClass)
                if isinstance(st,Theorem):
                    more_thms.append(st)
                if isinstance(st,Context):
                    more_thms.extend(get_from_Context(st))
            return more_thms

        thms = []
        for st in self.thy_stats:
            if isinstance(st,Theorem):
                thms.append(st)
            if isinstance(st,LocaleClass):
                thms.extend(get_from_LocaleClass(st))
            if isinstance(st,Context):
                thms.extend(get_from_Context(st))
        return thms

    def get_Theorem_by_name(self, thm_name):
        for st in self.get_all_Theorems():
            if st.thm_name == thm_name:
                return st
        return None
    
    def get_Theorem_by_id(self, thm_id):
        for st in self.get_all_Theorems():
            if st.thm_id == thm_id:
                return st
        return None

    # enrich the AST by semantic analysis; this should be done before interacting with Isabelle
    def annotate_Theorems(self):
        def annotate_ProofBlock(model,isar_idx,thm,rs_location=None):
            '''
                rs_location: when the proof_black belongs to a subgoal_block, of the format ([1,2],3) or ([1,2],3,[4])
            '''
            # print(model)
            if model.diag_stats_post or model.diag_stats_pre:
                self.have_diagnostic = True
            
            if model.rsteps is not None:
                model.rsteps = list(filter(lambda x:isinstance(x,RefinementStep),model.rsteps)) 
                for idx,rs in enumerate(model.rsteps):
                    if rs_location:
                        if isinstance(rs_location[-1],list):
                            rs.rs_location = rs_location+(idx,)
                        else:
                            assert isinstance(rs_location[-1],int)
                            rs.rs_location = rs_location+([],idx)
                    else:        
                        rs.rs_location = (isar_idx.copy(),idx)
                    if rs.sblock is not None:
                        # rs.sblock.rsteps = list(filter(lambda x:isinstance(x,RefinementStep),rs.sblock.rsteps))
                        if rs.sblock.bname in KEYWORDS:
                            rs.sblock.bname = None # to counter a TatSu bug
                        if rs.sblock.bname is None:
                            rs.sblock.bname = 'this_'
                        if rs.sblock.prems is not None and (rs.sblock.prem_name is None or rs.sblock.prem_name =='_'  or rs.sblock.prem_name in KEYWORDS):
                            # print(rs.sblock.prems, type(rs.sblock.prems),len(rs.sblock.prems),flatten(rs.sblock.prems)[0] )
                            assert rs.sblock.prems and flatten(rs.sblock.prems)[0] == 'premises','rs.sblock.prems is {}'.format(str(rs.sblock.prems))
                            assert len(flatten(rs.sblock.prems)) <= 2, str(flatten(rs.sblock.prems))
                            tail = flatten(rs.sblock.prems)[2:] if rs.sblock.prem_name =='_' \
                                else  flatten(rs.sblock.prems)[1:]
                            rs.sblock.prems = ['premises that'] + tail
                            rs.sblock.prem_name = 'that'
                            
                        annotate_ProofBlock(rs.sblock.proof,isar_idx,thm,rs.rs_location)

            if isinstance(model.key,ClosingStep):
                if rs_location:
                    if isinstance(rs_location[-1],list):
                        model.key.cs_location = rs_location
                    else:
                        assert isinstance(rs_location[-1],int)
                        model.key.cs_location = rs_location+([],)
                else:        
                    model.key.cs_location = (isar_idx.copy(),)
                if not isinstance(model.key.closing_tac,Tactic):
                    model.key.closing_tac = None # to counter a TatSu bug

            if isinstance(model.key,ProofQed):
                #to counter a possible bug when model.main_tac has been assigned a string rather than a Tactic object
                if not isinstance(model.key.main_tac,Tactic):
                    model.key.main_tac= None
                if not isinstance(model.key.closing_tac,Tactic):
                    model.key.closing_tac= None
                # print('model is {}'.format(model))
                # print('isar_idx is {}'.format(isar_idx))
                # remove 'thm' from isar_stats
                model.key.isar_stats = list(filter(lambda x:isinstance(x,IsarStatement),model.key.isar_stats)) 
                for idx, st in enumerate(model.key.isar_stats):
                    if rs_location:
                        if isinstance(rs_location[-1],list):
                            new_rs_location= rs_location[:-1]+(rs_location[-1]+[idx],)
                            annotate_IsarStatement(st,isar_idx.copy(),thm,new_rs_location)
                        else:
                            assert isinstance(rs_location[-1],int)
                            annotate_IsarStatement(st,isar_idx.copy(),thm,rs_location+([idx],))
                    else:
                        new_isar_idx = isar_idx.copy()
                        new_isar_idx.append(idx)
                        annotate_IsarStatement(st,new_isar_idx,thm)

        def annotate_IsarStatement(model,isar_idx,thm,rs_location=None):
            '''
                rs_location is used only when the Isar statement is within a subgoal_block, and it is of the format like ([1],2,[3])
            '''
            model._theorem = thm
            model._theory = self
            model.location_in_theorem = isar_idx
            model.rs_location = rs_location
            if model.key == 'note': # to counter a TatSu bug
                if not isinstance(model.name_eq,list):
                    model.name_eq = None
                if model.proof == '@phantom':
                    model.proof = ProofBlock(key = '@phantom', diag_stats_pre= [], diag_stats_post = [])
            if model.key == '{':
                model.isar_stats = list(filter(lambda x:isinstance(x,IsarStatement),model.isar_stats)) 
                for idx, st in enumerate(model.isar_stats):
                    if rs_location:
                        new_rs_location= rs_location[:-1]+(rs_location[-1]+[idx],)
                        annotate_IsarStatement(st,isar_idx.copy(),thm,new_rs_location)
                    else:
                        new_isar_idx = isar_idx.copy()
                        new_isar_idx.append(idx)
                        annotate_IsarStatement(st,new_isar_idx,thm)
            if model.proof is not None:
                annotate_ProofBlock(model.proof,isar_idx,thm,rs_location)
            if model.diag_stats_pre1 or model.diag_stats_pre2 or model.diag_stats_post:
                self.have_diagnostic = True

        def annotate_Theorem(model, int_id):
            if model.thm_name in KEYWORDS: # to count TatSu bug
                model.thm_name = None
            annotate_ProofBlock(model.proof,[],model)
            if model.thm_stat.diag_stats or model.diag_stats:
                self.have_diagnostic = True
            model._fact_dict = FactDict()
            model._depen_graph = DependencyGraph()
            if model.thm_name is None:
                thm_name_str = 'None'
            else:
                assert isinstance(model.thm_name,str)
                import re
                thm_name_str = re.sub('[ ",\(\)\.<>\\\^]','',model.thm_name)
                # thm_name_str = model.thm_name.replace('"','')
            model.thm_id = 'thm_'+thm_name_str+str(int_id)

        def annotate_LocaleClass(model,int_id):
            if isinstance(model.ex_thy_stats,list):
                for idx, st in enumerate(model.ex_thy_stats[1]):
                    if isinstance(st,Theorem):
                        annotate_Theorem(st,int_id*100+idx)
                    if isinstance(st,Context):
                        annotate_Context(st,int_id*100+idx)
        
        def annotate_Context(model,int_id):
            for idx, st in enumerate(model.thy_stats):
                if isinstance(st,Theorem):
                    annotate_Theorem(st,int_id*100+idx)
                if isinstance(st,Context):
                    annotate_Context(st,int_id*100+idx)
        
        if self.thy_name[0] == '"' and self.thy_name[-1] == '"':  # normalise theory name, "Equipollence" -> Equipollence
            self.thy_name = self.thy_name[1:-1]
        for idx,stat in enumerate(self.thy_stats):
            if isinstance(stat,Theorem):
                annotate_Theorem(stat,idx)
            if isinstance(stat,LocaleClass):
                annotate_LocaleClass(stat,idx)
            if isinstance(stat,Context):
                annotate_Context(stat,idx)
            if isinstance(stat,Function): # to counter a TatSu bug
                if not isinstance(stat.proof, ProofBlock):
                    stat.proof = None
            if isinstance(stat,Termination): # to counter a TatSu bug
                if stat.name in KEYWORDS:
                    stat.name = None

    def add_diagnostic(self):
        # fact_ref can be a String or FactReference
        def create_DiagStatement(thm_id,isar_idx,rs_location,fact_ref=None,more_info=None,comp_idx=None):
            def enclose_quote(some_str):
                assert isinstance(some_str,str)
                assert '\"' not in some_str
                return '\"'+some_str+ '\"'

            def enclose_cartouche(some_str):
                assert isinstance(some_str,str)
                return '\<open>'+some_str+'\<close>'
                
            if isinstance(fact_ref,str):
                fact_ref = FactReference(fact_name=fact_ref)
            txt_str = enclose_cartouche(StringOfTheory().str_FactReference(fact_ref) if fact_ref is not None else '<N.A.>' )
            isar_idx_str = '\"'+str_of_list(isar_idx)+ '\"'
            rs_location_str = '\"'+str_of_tuple(rs_location)+ '\"' \
                if rs_location is not None else '\"<N.A.>\"'
            comp_idx_str = '\"' + str(comp_idx) + '\"'
            name_str = '\"<unnamed>\"' if fact_ref is None else enclose_quote(fact_ref.get_name_and_sel())
            if more_info is None:
                assert comp_idx is None
                attrs=[self.thy_name,thm_id,isar_idx_str,rs_location_str,name_str]
            elif comp_idx is None:
                attrs=[self.thy_name,thm_id,isar_idx_str,rs_location_str,name_str,more_info]
            else:
                attrs=[self.thy_name,thm_id,isar_idx_str,rs_location_str,name_str,more_info,comp_idx_str] 
            
            if fact_ref is not None:
                return DiagStatement(key='record_facts',attrs=attrs, fact_ref=fact_ref,txt=txt_str)
            else:
                return DiagStatement(key='record_all_facts',attrs=attrs)

        ''' add default diagnostic statements if there is none '''
        # def annotate_ProofBlock(model,isar_idx=[],thm=None):
        #     # def get_previous_isar_index():
        #     #     idx = list(isar_idx)
        #     #     if idx[-1] == 0:
        #     #         return idx
        #     #     else:
        #     #         idx[-1] = idx[-1] -1
        #     #         return idx
        


        #     if isar_idx:
        #         current_isar_st = thm.proof.get_IsarStatement(isar_idx)
        #         pre_facts,pre_facts2,facts,_ = model.retrieve_facts(current_isar_st)
        #         if current_isar_st.key != 'interpret':
        #             # 'interpret' is special -- it has a proof but does not have a 'this' binding for produced facts
        #             model.diag_stats_post.append(create_DiagStatement(thm.thm_id,isar_idx,None,'this'))
        #         for idx,ff in enumerate(pre_facts): 
        #             pre_diag_stats = current_isar_st.diag_stats_pre1
        #             if isinstance(ff.for_mod,ForwardModifier):
        #                 pre_diag_stats.append(create_DiagStatement(thm.thm_id\
        #                     ,isar_idx,None,ff,'used_fact',idx))
        #                 pre_diag_stats.append(create_DiagStatement(thm.thm_id\
        #                     ,isar_idx,None,ff.without_forward_modifier(),'used_fact_in_modifier',idx))
        #                 for fm in ff.for_mod.retrieve_all_facts():
        #                     pre_diag_stats.append(create_DiagStatement(thm.thm_id\
        #                         ,isar_idx,None,fm.without_forward_modifier(),'used_fact_in_modifier',idx))
        #             else:
        #                 pre_diag_stats.append(create_DiagStatement(thm.thm_id\
        #                     ,isar_idx,None,ff,'used_fact'))

        #         for ff in pre_facts2: 
        #             if ff.is_equal_to('<finally>'):
        #                 continue
        #             else:
        #                 assert ff.is_equal_to('this')
        #                 current_isar_model = thm.proof.get_IsarStatement(isar_idx)
        #                 current_isar_model.diag_stats_pre2.append(create_DiagStatement(thm.thm_id\
        #                         ,isar_idx,None,ff,'used_fact'))

        #         for idx,ff in enumerate(facts):
        #             if str(ff) in KNOWN_FACT_COLLECTIONS:
        #                 continue
        #             if isinstance(ff.for_mod,ForwardModifier):
        #                 model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
        #                     ,isar_idx,None,ff,'used_fact',idx+len(pre_facts+pre_facts2)))
        #                 model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
        #                     ,isar_idx,None,ff.without_forward_modifier(),'used_fact_in_modifier',idx+len(pre_facts+pre_facts2)))
        #                 for fm in ff.for_mod.retrieve_all_facts():
        #                     model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
        #                         ,isar_idx,None,fm.without_forward_modifier(),'used_fact_in_modifier',idx+len(pre_facts +pre_facts2)))
        #             else:
        #                 model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
        #                     ,isar_idx,None,ff,'used_fact'))
                
        #     else:
        #         pre_facts,pre_facts2,facts,_ = model.retrieve_facts()
        #         assert pre_facts == [] and pre_facts2 == []
        #         for idx,ff in enumerate(facts):
        #             if str(ff) in KNOWN_FACT_COLLECTIONS:
        #                 continue
        #             if isinstance(ff.for_mod,ForwardModifier):
        #                 model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
        #                     ,isar_idx,None,ff,'used_fact',idx))
        #                 model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
        #                     ,isar_idx,None,ff.without_forward_modifier(),'used_fact_in_modifier',idx))
        #                 for fm in ff.for_mod.retrieve_all_facts():
        #                     model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
        #                         ,isar_idx,None,fm.without_forward_modifier(),'used_fact_in_modifier',idx))
        #             else:
        #                 model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
        #                     ,isar_idx,None,ff,'used_fact'))

        #     if model.rsteps:
        #         for step in model.rsteps:
        #             if step.sblock is not None:
        #                 assert isinstance(step.sblock.bname,str) and step.sblock.bname not in KEYWORDS
        #                 step.sblock.proof.diag_stats_post.append(create_DiagStatement(thm.thm_id\
        #                         ,isar_idx,step.rs_location,step.sblock.bname,'used_fact'))
        #                 annotate_ProofBlock(step.sblock.proof,isar_idx,thm)

        #     if isinstance(model.key, ProofQed):
        #         for st in model.key.isar_stats:
        #             annotate_IsarStatement(st)

        def annotate_ProofBlock(model,current_isar = None,thm=None,rs_location=None):
            isar_idx = [] if current_isar is None else current_isar.location_in_theorem
            # rs_location = None if current_isar is None else current_isar.rs_location
            pre_facts,pre_facts2,facts,_ = model.retrieve_facts(current_isar)
            if current_isar is not None and current_isar.key != 'interpret':
                # 'interpret' is special -- it has a proof but does not have a 'this' binding for produced facts
                model.diag_stats_post.append(create_DiagStatement(thm.thm_id,isar_idx,rs_location,'this'))
            if current_isar is not None:
                for idx,ff in enumerate(pre_facts): 
                    pre_diag_stats = current_isar.diag_stats_pre1
                    if isinstance(ff.for_mod,ForwardModifier):
                        pre_diag_stats.append(create_DiagStatement(thm.thm_id\
                            ,isar_idx,rs_location,ff,'used_fact',idx))
                        pre_diag_stats.append(create_DiagStatement(thm.thm_id\
                            ,isar_idx,rs_location,ff.without_forward_modifier(),'used_fact_in_modifier',idx))
                        for fm in ff.for_mod.retrieve_all_facts():
                            pre_diag_stats.append(create_DiagStatement(thm.thm_id\
                                ,isar_idx,rs_location,fm.without_forward_modifier(),'used_fact_in_modifier',idx))
                    else:
                        pre_diag_stats.append(create_DiagStatement(thm.thm_id\
                            ,isar_idx,rs_location,ff,'used_fact'))

                for ff in pre_facts2: 
                    if ff.is_equal_to('<finally>'):
                        continue
                    else:
                        assert ff.is_equal_to('this')
                        current_isar.diag_stats_pre2.append(create_DiagStatement(thm.thm_id\
                                ,isar_idx,rs_location,ff,'used_fact'))

            for idx,ff in enumerate(facts):
                if str(ff) in KNOWN_FACT_COLLECTIONS:
                    continue
                if isinstance(ff.for_mod,ForwardModifier):
                    model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
                        ,isar_idx,rs_location,ff,'used_fact',idx+len(pre_facts+pre_facts2)))
                    model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
                        ,isar_idx,rs_location,ff.without_forward_modifier(),'used_fact_in_modifier',idx+len(pre_facts+pre_facts2)))
                    for fm in ff.for_mod.retrieve_all_facts():
                        model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
                            ,isar_idx,rs_location,fm.without_forward_modifier(),'used_fact_in_modifier',idx+len(pre_facts +pre_facts2)))
                else:
                    model.diag_stats_pre.append(create_DiagStatement(thm.thm_id\
                        ,isar_idx,rs_location,ff,'used_fact'))

            if model.rsteps:
                for step in model.rsteps:
                    if step.sblock is not None:
                        assert isinstance(step.sblock.bname,str) and step.sblock.bname not in KEYWORDS
                        if step.sblock.prems is not None:
                            step.sblock.proof.diag_stats_pre.append(create_DiagStatement(\
                                thm.thm_id,isar_idx,step.rs_location+([-1],),step.sblock.prem_name)) 
                        step.sblock.proof.diag_stats_post.append(create_DiagStatement(thm.thm_id\
                                ,isar_idx,step.rs_location,step.sblock.bname,'used_fact'))
                        annotate_ProofBlock(step.sblock.proof,None,thm,step.rs_location)

            if isinstance(model.key, ProofQed):
                for st in model.key.isar_stats:
                    annotate_IsarStatement(st)

        def annotate_IsarStatement(model):
            if model.proof is not None:
                # assert model._theorem.thm_name is not None 
                annotate_ProofBlock(model.proof,model,model._theorem,model.rs_location)
            if model.key == '{':
                for st in model.isar_stats:
                    annotate_IsarStatement(st)
            if model.key in ['assume','presume','case','define','{']:
                model.diag_stats_post.append(create_DiagStatement(\
                    model._theorem.thm_id,model.location_in_theorem,model.rs_location,'this'))
            if model.when_if is not None or (model.props is not None and model.props.if_if is not None)\
                or model.key == 'obtain':
                if model.proof is not None:
                    new_loc = model.location_in_theorem+ [-1]
                    model.proof.diag_stats_pre.append(create_DiagStatement(\
                        model._theorem.thm_id,new_loc,model.rs_location,'that')) 

        if not self.have_diagnostic:
            for stat in self.get_all_Theorems():
                annotate_ProofBlock(stat.proof,None,thm=stat,rs_location=None)
                stat.thm_stat.diag_stats.append(create_DiagStatement(stat.thm_id,[-1],None))
                if stat.thm_name is not None:
                    stat.diag_stats.append(create_DiagStatement(stat.thm_id,[],None,stat.thm_name ))
                    

    def purge_diagnostic(self):
        def purge_ProofBlock(model):
            assert hasattr(model,'diag_stats_pre') and hasattr(model,'diag_stats_post')
            model.diag_stats_pre = []
            model.diag_stats_post = []
            if isinstance(model.key, ProofQed):
                for st in model.key.isar_stats:
                    purge_IsarStatement(st)
            if isinstance(model.key,ClosingStep) and model.key.diag_stats_pre:
                model.key.diag_stats_pre = []
            if model.rsteps:
                for step in model.rsteps:
                    step.diag_stats_pre = []
                    if step.sblock is not None:
                        purge_ProofBlock(step.sblock.proof)
             
        def purge_IsarStatement(model):
            if model.proof is not None:
                purge_ProofBlock(model.proof)
            if model.diag_stats_pre1 is not None:
                model.diag_stats_pre1 = []
            if model.diag_stats_pre2 is not None:
                model.diag_stats_pre2 = []
            if model.diag_stats_post is not None:
                model.diag_stats_post = []
            if model.isar_stats is not None:
                for st in model.isar_stats:
                    purge_IsarStatement(st)

        # self.imported_thy_names = filter(lambda x:x != '\"../Recording/ProofRecording\"', self.imported_thy_names)
        self.imported_thy_names = [x for x in self.imported_thy_names \
            if not x.endswith('Recording/ProofRecording\"') and not x.endswith('Recording/Sequence_Evaluation\"') ] 
        for stat in self.get_all_Theorems():
            if stat.thm_stat.diag_stats is not None:
                # purge diagnostics in theorem statements
                stat.thm_stat.diag_stats = []
            stat.diag_stats = []
            purge_ProofBlock(stat.proof)
        self.have_diagnostic = False

    

    Theory.full_filename = None # full file name inside a root directory e.g. HOL/Nat.thy, HOL/Analysis/L2_Norm.thy
    Theory.filepath = None # absolute or relative path to the theory e.g. ./HOL/Nat.thy
    Theory.have_diagnostic = False
    Theory.diag_thy_path_recording = DIAG_THY_PATH_RECORDING # ['\"../Recording/ProofRecording\"']
    Theory.diag_thy_path_evaluation = DIAG_THY_PATH_EVALUATION
    Theory.get_Theorem_by_name = get_Theorem_by_name
    Theory.get_Theorem_by_id = get_Theorem_by_id
    Theory.get_all_Theorems = get_all_Theorems
    Theory.annotate_Theorems = annotate_Theorems
    Theory.add_diagnostic = add_diagnostic
    Theory.purge_diagnostic = purge_diagnostic

def expand_ClosingStep():
    def retrieve_relevant_facts(self):
        facts = []
        if self.key == 'by':
            facts.extend(self.main_tac.retrieve_relevant_facts())
        if isinstance(self.closing_tac,Tactic):
            facts.extend(self.closing_tac.retrieve_relevant_facts())
        return facts
    
    ClosingStep.retrieve_relevant_facts =retrieve_relevant_facts
    ClosingStep.cs_location = None # e.g. ([3],) or ([1,2],2,[]) where the list is for the isar-location, and we use the following integer to identify the subgoal_block refinement step

def expand_RefinementStep():
    def retrieve_relevant_facts(self):
        facts = []
        if self.key == 'using' or self.key == 'unfolding':
            facts.extend(list(filter(lambda x:isinstance(x,FactReference),self.facts) ))
        elif self.key in ['apply','applyS','applyF','apply1']:
            facts.extend(self.tac.retrieve_relevant_facts())
        elif self.key in ['focus']:
            if self.tac is not None and self.tac not in KEYWORDS:
                facts.extend(self.tac.retrieve_relevant_facts())
        elif self.key == 'supply':
            facts.extend(list(filter(lambda x:isinstance(x,FactReference),self.facts) ))
        elif self.key in ['prefer','defer','back','solved']:
            pass
        elif self.key == 'including':
            pass
        else:
            assert self.sblock is not None
            pass
            # for rf in self.sblock.rsteps:
            #     facts.extend(rf.retrieve_relevant_facts())
            # if isinstance(self.sblock.cstep,ClosingStep):
            #     facts.extend(self.sblock.cstep.retrieve_relevant_facts())
            # else:
            #     assert isinstance(self.sblock.cstep,ProofQed)
                # we ignore this case for now
        return facts
    
    RefinementStep.retrieve_relevant_facts=retrieve_relevant_facts
    RefinementStep.rs_location = None # e.g. ([1,2],2,[],3) where the list is for the isar-location, and we use the following integer to identify the refinement step 

def expand_Theorem():
    
    def str_neighbours_of_location(self,isar_idx,rs_location=None):
        facts = self._fact_dict.get_local_by_location(isar_idx,rs_location)
        re_str = ''
        for ff in facts:
            re_str += self._depen_graph.str_neighbours_of_fact(ff)
        return re_str

    def get_causal_steps(self):
        entries = []
        for fact in self._fact_dict.get_all_local_facts():
            used_locals = self._depen_graph.get_used_locals(fact)
            used_globals = self._depen_graph.get_used_globals(fact)
            consequences = self._depen_graph.get_consequences(fact)
            if not used_locals and not used_globals and not consequences:
                # we only desire intermediate steps (not assumptions or conclusions)
                continue 
            # conq_tuples = []
            if consequences:
                for conq in consequences: 
                    other_used_locals = list(filter(lambda x:x is not fact,self._depen_graph.get_used_locals(conq)))
                    entries.append( (fact,used_locals,used_globals,(conq,other_used_locals,self._depen_graph.get_used_globals(conq)) ) ) 
            else:
                entries.append( (fact,used_locals,used_globals,None ) )

                # conq_tuples.append( (conq,other_used_locals,self._depen_graph.get_used_globals(conq)) )
            # entries.append( (fact,used_locals,used_globals,conq_tuples) )
        return entries
            
    Theorem.get_causal_steps = get_causal_steps
    Theorem.str_neighbours_of_location = str_neighbours_of_location
    Theorem._fact_dict = None # FactDict to store facts
    Theorem._depen_graph = None # DependencyGraph to store dependency
    Theorem.thm_id = None #this is helpful when the theorem has no name
    Theorem.thm_reprs = None #list of LocalFacts encoding the theorem itself

def expand_model():
    expand_Theorem()
    expand_ClosingStep()
    expand_RefinementStep()
    expand_FactReference()
    expand_ForwardModifier()
    expand_Tactic()
    expand_Selection()
    expand_Propositions()
    expand_IsarStatement()
    expand_Theory()
    expand_ProofBlock()


if __name__ == '__main__':
    expand_model()
    # grammar = open('grammars/thy_model.ebnf').read()    
    # parser = tatsu.compile(grammar, asmodel=True)

    # thy_src = open('./Test/Drinker.thy').read()
    # model = parser.parse(thy_src,comments_re="\(\*(.|\n)*?\*\)")

    # parser = ThyParser(semantics=ThyModelBuilderSemantics())

    # model = parser.parse("with \<open>a \<noteq> b\<close> show  \"card ?S = 0 \<or> card ?S = 2\" by auto", rule_name = 'isar_statement')
    # model = parser.parse("\<T>'", rule_name = 'long_name')
    # model = parser.parse("theory Groups imports Orderings begin\
    #     simproc_setup group_cancel_le (\"a \<le> (b::'a::ordered_ab_group_add)\") =\
    #     \<open>fn phi => fn ss => try Group_Cancel.cancel_le_conv\<close>\
    #     simproc_setup group_cancel_less (\"a < (b::'a::ordered_ab_group_add)\") =\
    #     \<open>fn phi => fn ss => try Group_Cancel.cancel_less_conv\<close> end", rule_name = 'theory')

    # print( model.proof.retrieve_facts(model)[0][1].get_name_and_sel())
    # print(model.get_Theorem_by_name('euclidean_size_eq_0_iff'))
    # print( json.dumps(model.asjson(),indent=4) )
    # model.annotate_Theorems()
    # model.add_diagnostic()
    # print(model.asjson())
    # model.filepath = thy_path
    # model.purge_diagnostic()
    # model.add_diagnostic()
    # print(StringOfTheory(True).str_Theory(model) )
    # print(StringOfTheory(True).str_RefinementStep(model) )
    # print(StringOfTheory(True).str_IsarStatement(model) )
    # print(thy_src)