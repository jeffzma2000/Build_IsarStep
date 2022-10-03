from os.path import isfile, join
from os import listdir
import os
import subprocess
from multiprocessing import Pool
import multiprocessing
import xml.etree.ElementTree as ET
from .expand_thy_model import expand_model,KNOWN_FACT_COLLECTIONS,Fact,CollectedFacts,GlobalFact\
    ,LocalFact,FactDict,DependencyGraph,expand_model,StepIndexError,rs_location_from_str\
    ,isar_location_from_str
from .generated_parser.generated_thy_model import *
from .print_theory import *
from .parse_isabelle_term.isabelle_term import *
from typing import Optional


SEP_TOKEN = '<SEP>'

LOGFILE_PATH = './log_build_models.txt'

def append_to_log(msg):
    with open(LOGFILE_PATH,'a') as file:
        file.write(msg)

def decode_term_from_base64(s:str) -> Term:
    import base64
    return decode_term_from_yxml(str(base64.b64decode(s),'ascii')) 

def annotate_thy(wrapped_thy):
    thy = wrapped_thy.thy_model
    database_path = join(os.path.dirname(thy.filepath),'Database',thy.thy_name+'.xml')
    try:
        tree = ET.parse(database_path,ET.XMLParser())
    except ET.ParseError:
        print('Invalid database:'+database_path)
        raise
    all_theorems = thy.get_all_Theorems()
    if len(tree.getroot()) == 0 and len(all_theorems) != 0:
        msg_str = 'Warning: trying to process theory:{}, but its database is empty and this is probably because it is not built with the current ROOT setting or none of the diagnostic command has been inserted.\n\n'.format(thy.full_filename)
        print(msg_str)
        return
    for stat in all_theorems:
        facts = lookup_facts(tree,thy.thy_name,stat.thm_id,'[-1]','<N.A.>','<unnamed>',thy=thy) 
        for fact in facts: # this should be one of the only three places we add local non-compound facts
                stat._fact_dict.add_local_fact(fact)
                stat._depen_graph.add_local_fact(fact)
        if stat.thm_name is not None:
            facts = lookup_facts(tree,thy.thy_name,stat.thm_id,'[]','<N.A.>',stat.thm_name,thy=thy)
            stat.thm_reprs = facts
        annotate_ProofBlock(stat.proof,tree,None,None,thm=stat,thy=thy)
    return

def lookup_facts(database_tree,theory_name,theorem_id,isar_location,rs_location\
        ,props_name,more_info='None',compound_index="None",next_next_idx = None,thy=None,has_forward=False):
    assert next_next_idx is None or isinstance(next_next_idx,list)
    if props_name[0] == '"' and props_name[-1] == '"':
        props_name = props_name[1:-1]  # drop quotation if any
    root = database_tree.getroot()
    for child in root:
        att= child.attrib
        if att['theory_name'] == theory_name and att['theorem_id'] == theorem_id\
            and att['isar_location'] == isar_location and att['refinement_location'] == rs_location\
            and att['props_name'] == props_name\
            and att['more_info'] == more_info and att['compound_index'] == compound_index:
            facts = []
            for prop in child:
                aa = prop.find('ascii').text
                aa_original = prop.find('ascii_original').text
                ll = prop.find('latex').text
                yy = prop.find('yxml').text
                trm = decode_term_from_base64( yy)
                com_idx = None if compound_index == 'None' else int(compound_index)
                rs_loc = None if rs_location == '<N.A.>' else to_int_tuple(rs_location)
                facts.append(LocalFact(to_int_list(isar_location),rs_loc,trm,aa,ll,yy,com_idx,next_next_idx,aa_original\
                    ,att['text_information'],has_forward=has_forward))
            return facts
    assert False, 'Failed to retrieve facts from the database!\n\
        theory:{} theorem:{} isar_loc:{} rs_loc:{} props_name:{} more_info:{} compound_index:{}'.format(\
            theory_name if thy is None else thy.full_filename ,theorem_id,isar_location,rs_location,props_name,more_info,compound_index)

def lookup_all_facts(database_tree,theory_name,theorem_id,isar_location,rs_location\
        ,props_name,more_info='None',compound_index="None",next_next_idx = None):
    assert next_next_idx is None or isinstance(next_next_idx,list)
    root = database_tree.getroot()
    facts = []
    for child in root:
        att= child.attrib
        if att['theory_name'] == theory_name and att['theorem_id'] == theorem_id\
            and att['isar_location'] == isar_location and att['refinement_location'] == rs_location\
            and att['props_name'] == props_name\
            and att['more_info'] == more_info and att['compound_index'] == compound_index:
            for prop in child:
                aa = prop.find('ascii').text
                aa_original = prop.find('ascii_original').text
                ll = prop.find('latex').text
                yy = prop.find('yxml').text
                trm = decode_term_from_base64(yy)
                com_idx = None if compound_index == 'None' else int(compound_index)
                rs_loc = None if rs_location == '<N.A.>' else to_int_tuple(rs_location)
                facts.append(LocalFact(to_int_list(isar_location),rs_loc,trm,aa,ll,yy,com_idx,next_next_idx,aa_original,att['text_information']))
    return facts

def get_next_next_idx(thm,isar_idx): #TODO: this can be more accurate with respect to rs_location
    if not isar_idx:
        return None
    if isar_idx[:-1]:
        current_isar = thm.proof.get_IsarStatement(isar_idx[:-1])
        if current_isar.proof is not None:
            isar_stats = current_isar.proof.key.isar_stats
        else:
            assert current_isar.isar_stats is not None
            isar_stats = current_isar.isar_stats
    else:
        isar_stats = thm.proof.key.isar_stats
    next_next_idx = None
    for idx,st in enumerate(isar_stats):
        if idx > isar_idx[-1] and st.key == 'next':
            next_next_idx = list(isar_idx[:-1])+ [idx]
    return next_next_idx

def annotate_ProofBlock(model,tree,attached_isar = None,rs_location=None ,thm=None,thy=None):
    def add_named_fact(fact_dict,isar_idx,rs_location,raw_fact,rich_facts,compound_index=None):
        assert raw_fact.fact_name is not None
        extended_local,extended_global = [], []
        for rich_idx,rich_fact in enumerate(rich_facts):
            if isinstance(rich_fact, CollectedFacts):
                model.retrieve_used_global_facts().append(rich_fact)
                extended_global.append(rich_fact)
                continue
            fs = list(filter(lambda x: x.visible_from_loc(isar_idx) and x.visible_from_rs_loc(rs_location)\
                , fact_dict.get_local_by_ascii(rich_fact.content_in_ascii)))    
            if len(fs) > 0: # rich_fact is a local fact
                model.retrieve_used_local_facts().append(fs[-1])
                extended_local.append(fs[-1])
            else: # rich_fact is a global fact
                assert len(fs) == 0
                if raw_fact.sel is not None:
                    max_i = raw_fact.sel.infer_max_index(len(rich_facts))
                    indices = raw_fact.sel.retrieve_indices(max_i)
                else:
                    indices = list(range(1,len(rich_facts)+1))
                re = fact_dict.get_global(raw_fact.fact_name,indices[rich_idx])
                if re is None:
                    yxml = rich_fact.content_in_yxml
                    gf = GlobalFact(raw_fact.fact_name,indices[rich_idx], decode_term_from_base64(yxml) \
                                ,rich_fact.content_in_ascii,rich_fact.content_in_latex, yxml)
                    fact_dict.add_global_fact(gf)
                    model.retrieve_used_global_facts().append(gf)
                    extended_global.append(gf)
                else:
                    if re.content_in_ascii != rich_fact.content_in_ascii:
                        pass
                    model.retrieve_used_global_facts().append(re)
                    extended_global.append(re)
        return extended_local,extended_global

    def add_anonymous_fact(fact_dict,isar_idx,rs_location,rich_facts,compound_index=None):
        extended_local = []
        for rich_fact in rich_facts:
            fs = list(filter(lambda x: x.visible_from_loc(isar_idx) and x.visible_from_rs_loc(rs_location)\
                        , fact_dict.get_local_by_ascii(rich_fact.content_in_ascii)))
            if fs == []: 
                return []
            model.retrieve_used_local_facts().append(fs[-1])
            extended_local.append(fs[-1])
        return extended_local

    def add_dependencies(depen_graph,isar_idx,rs_location,compound_idx,used_locals,used_globals):
        current_locals = thm._fact_dict.get_local_by_location(isar_idx,rs_location,compound_idx)
        for c_local in current_locals:
            for u_local in used_locals:
                depen_graph.add_local_local(u_local,c_local)
            for u_global in used_globals:
                depen_graph.add_used_global(c_local,u_global)

    # TODO: need a more accurate version
    def get_also_finally_rich_facts(database_tree,theory_name,theorem,isar_idx): 
        def get_previous_isar_index(current_idx):
            idx = list(current_idx)
            idx[-1] = idx[-1] -1
            return idx
        assert theorem.proof.get_IsarStatement(isar_idx).pre_facts==['finally']
        af_rich_facts = []
        current_idx = list(isar_idx)
        while True:
            prev_isar_model = theorem.proof.get_IsarStatement(get_previous_isar_index(current_idx))
            rich_facts = lookup_facts(database_tree,theory_name,theorem.thm_id\
                ,str_of_list(prev_isar_model.location_in_theorem),'<N.A.>','this',thy=thy)
            af_rich_facts.extend(rich_facts)
            if prev_isar_model.pre_facts is None or 'also' not in prev_isar_model.pre_facts:
                break
            else:
                current_idx = list(prev_isar_model.location_in_theorem)
        return af_rich_facts

    isar_idx = [] if attached_isar is None else attached_isar.location_in_theorem

    if model.rsteps:
        for step in model.rsteps:
            if step.sblock is not None:
                assert isinstance(step.sblock.bname,str) and step.sblock.bname not in KEYWORDS
                if step.sblock.prems is not None:
                    subgoal_prems_rich_facts = lookup_facts(tree,thy.thy_name,thm.thm_id,str_of_list(isar_idx)\
                            ,str_of_tuple(step.rs_location+([-1],)),step.sblock.prem_name,thy=thy)
                    for ff in subgoal_prems_rich_facts:
                        thm._fact_dict.add_local_fact(ff) # the only place to local facts from subgoal prems
                        thm._depen_graph.add_local_fact(ff)
                subgoal_rich_facts = lookup_facts(tree,thy.thy_name,thm.thm_id,str_of_list(isar_idx)\
                            ,str_of_tuple(step.rs_location),step.sblock.bname,'used_fact',thy=thy)
                for ff in subgoal_rich_facts:
                    thm._fact_dict.add_local_fact(ff) # the only place we add subgoal local facts
                    thm._depen_graph.add_local_fact(ff)
                
                annotate_ProofBlock(step.sblock.proof,tree,None,step.rs_location,thm=thm,thy=thy)
                visible_local_facts = list (filter(lambda x: x.visible_from_loc(isar_idx) and x.visible_from_rs_loc(rs_location)\
                    ,step.sblock.proof.retrieve_used_local_facts()) ) 
                model.retrieve_used_local_facts().extend(visible_local_facts)
                model.retrieve_used_global_facts().extend(step.sblock.proof.retrieve_used_global_facts())

    if isinstance(model.key, ProofQed):
        # isar_idx = [] if attached_isar is None else attached_isar.location_in_theorem
        for st in model.key.isar_stats:
            annotate_IsarStatement(st,tree)
            if st.proof is not None:
                visible_local_facts = list (filter(lambda x: x.visible_from_loc(isar_idx) and x.visible_from_rs_loc(rs_location)\
                    ,st.proof.retrieve_used_local_facts()) ) 
                model.retrieve_used_local_facts().extend(visible_local_facts)
                model.retrieve_used_global_facts().extend(st.proof.retrieve_used_global_facts())
    
    
   
    rs_location_str = '<N.A.>' if rs_location is None else str_of_tuple(rs_location)

    # deal with used anonymous facts in non-compound facts
    rich_facts = lookup_all_facts(tree,thy.thy_name,thm.thm_id,str_of_list(isar_idx)\
        ,rs_location_str,'<unnamed>','used_fact')
    ex_locals=add_anonymous_fact(thm._fact_dict,isar_idx,rs_location,rich_facts)
    add_dependencies(thm._depen_graph,isar_idx,rs_location,None,ex_locals,[])

    # dependency from ProofQed or sblock
    add_dependencies(thm._depen_graph,isar_idx,rs_location,None,model.retrieve_used_local_facts(),model.retrieve_used_global_facts()) 

    pre_facts,pre_facts2,facts,_ = model.retrieve_facts(attached_isar)
    for raw_idx, raw_fact in enumerate(pre_facts+pre_facts2+facts):
        if not isinstance(raw_fact.for_mod,ForwardModifier):
            if raw_fact.fact_name is not None: # anonymous facts have been dealt with earlier
                if raw_fact.is_equal_to('<finally>'):
                    rich_facts = get_also_finally_rich_facts(tree,thy.thy_name,thm\
                        ,isar_idx) if rs_location_str ==  '<N.A.>' else [] # TODO: need to be more accurate
                elif str(raw_fact) in KNOWN_FACT_COLLECTIONS:
                    rich_facts = [CollectedFacts(name = str(raw_fact))]
                else:
                    rich_facts = lookup_facts(tree,thy.thy_name,thm.thm_id,str_of_list(isar_idx)\
                    ,rs_location_str,raw_fact.get_name_and_sel(),'used_fact',thy=thy)
                ex_locals,ex_globals = add_named_fact(thm._fact_dict,isar_idx,rs_location,raw_fact,rich_facts)
                add_dependencies(thm._depen_graph,isar_idx,rs_location,None,ex_locals,ex_globals)
        else:
            f_name = raw_fact.get_name_and_sel() 
            compound_rich_facts = lookup_facts(tree,thy.thy_name,thm.thm_id\
                    ,str_of_list(isar_idx),rs_location_str,f_name,'used_fact',str(raw_idx),thy=thy,has_forward=True)
            for ff in compound_rich_facts:
                thm._fact_dict.add_local_fact(ff) # the only place we add compound local facts
                thm._depen_graph.add_local_fact(ff)
            add_dependencies(thm._depen_graph,isar_idx,rs_location,None,compound_rich_facts,[])     
                
            rich_facts = lookup_all_facts(tree,thy.thy_name,thm.thm_id\
                                ,str_of_list(isar_idx),rs_location_str,'<unnamed>','used_fact_in_modifier',str(raw_idx))
            ex_locals = add_anonymous_fact(thm._fact_dict,isar_idx,rs_location,rich_facts,raw_idx)
            add_dependencies(thm._depen_graph,isar_idx,rs_location,raw_idx,ex_locals,[])
                
            for raw_fact_in_mod in [raw_fact]+raw_fact.for_mod.retrieve_all_facts():
                if raw_fact_in_mod.fact_name is not None:
                    rich_facts = lookup_facts(tree,thy.thy_name,thm.thm_id,str_of_list(isar_idx)\
                            ,rs_location_str,raw_fact_in_mod.get_name_and_sel(),'used_fact_in_modifier',str(raw_idx),thy=thy)
                    ex_locals,ex_globals = add_named_fact(thm._fact_dict,isar_idx,rs_location,raw_fact_in_mod,rich_facts,raw_idx)
                    add_dependencies(thm._depen_graph,isar_idx,rs_location,raw_idx,ex_locals,ex_globals)
                    
def annotate_IsarStatement(model,tree):
    isar_idx = model.location_in_theorem
    rs_location = '<N.A.>' if model.rs_location is None else model.rs_location
    thm = model._theorem
    thy = model._theory
    
    if model.key in ['assume','presume','case','define','note','{','consider','guess','have','show','hence','thus','obtain']:
        next_next_idx = get_next_next_idx(thm,isar_idx)
        facts = lookup_facts(tree,thy.thy_name,thm.thm_id,str_of_list(isar_idx),str_of_tuple(rs_location),'this',next_next_idx=next_next_idx,thy=thy)
        for fact in facts: # this should be one of the only three places we add local non-compound facts
            thm._fact_dict.add_local_fact(fact)
            thm._depen_graph.add_local_fact(fact)

    if model.when_if is not None or (model.props is not None and model.props.if_if is not None)\
            or model.key == 'obtain':
        if model.proof is not None:
            new_isar_idx = isar_idx + [-1]
            facts = lookup_facts(tree,thy.thy_name,thm.thm_id,str_of_list(new_isar_idx),str_of_tuple(rs_location),'that',thy=thy)
            for fact in facts: # this should be one of the only three places we add local non-compound facts
                thm._fact_dict.add_local_fact(fact)
                thm._depen_graph.add_local_fact(fact)

    if model.proof is not None:
        annotate_ProofBlock(model.proof,tree,model,model.rs_location,thm=thm,thy=thy)
    
    if model.isar_stats is not None:
        for st in model.isar_stats:
            annotate_IsarStatement(st,tree)

def build_CausalSteps(wrapped_thy):
    def string_of_facts(facts,mode):
        '''
        facts is a list of GlobalFact/CollectedFacts/LocalFact
        '''
        facts_without_collected = filter(lambda x: isinstance(x,GlobalFact)\
            or isinstance(x,LocalFact),facts) 
        if mode is 'latex':
            list_of_strings = map(lambda x: x.content_in_latex, facts_without_collected)
            sorted_ll = sorted(list_of_strings,key=lambda x: -len(x))
        elif mode is 'ascii_original':
            list_of_strings = map(lambda x: x.content_in_ascii_original \
                if isinstance(x,LocalFact) else x.content_in_ascii, facts_without_collected)
            sorted_ll = sorted(list_of_strings,key=lambda x: -len(x))
        else:
            assert False, 'Unsupported CausalSteps mode'

        res = ''
        for ss in sorted_ll:
            res+=' ' + SEP_TOKEN+' '+ss 
        return res

    def concate_two_strings(s1,s2):
        if not s1 and not s2:
            return ''
        else:
            return s1+' '+s2

    thy = wrapped_thy.thy_model
    all_theorems = thy.get_all_Theorems()
    root = ET.Element("theory",full_name=thy.full_filename,processed_id=str(wrapped_thy.processed_id))
    for thm in all_theorems:
        for fact,used_locals,used_globals,conq_tuple in thm.get_causal_steps():
            has_consequence = True if conq_tuple else False
            entry = ET.SubElement(root, "entry",theorem_id=thm.thm_id\
                ,location_in_theorem=str_of_list(fact.location_in_theorem)\
                ,refinement_step_location=str_of_tuple(fact.refinement_step_location)\
                ,compound_index=str(fact.compound_index)\
                ,location_in_theorem_consequence=str_of_list(conq_tuple[0].location_in_theorem) if has_consequence else 'None'\
                ,refinement_step_location_consequence=str_of_tuple(conq_tuple[0].refinement_step_location) if has_consequence else 'None'\
                ,compound_index_consequence=str(conq_tuple[0].compound_index) if has_consequence else 'None'\
                ,has_consequence = str(has_consequence)
                )

            target_fact = ET.SubElement(entry,"target_fact")
            target_fact.text = ' '.join(token_of_term(fact.content_in_term))

            target_fact_ascii = ET.SubElement(entry,"target_fact_ascii")
            target_fact_ascii.text = fact.content_in_ascii

            target_fact_ascii_original = ET.SubElement(entry,"target_fact_ascii_original")
            target_fact_ascii_original.text = fact.content_in_ascii_original

            target_fact_latex = ET.SubElement(entry,"target_fact_latex")
            target_fact_latex.text = fact.content_in_latex

            used_local_facts = ET.SubElement(entry,"used_local_facts")
            used_local_facts.text = tokens_of_local_facts(used_locals)

            used_local_facts_ascii_original = ET.SubElement(entry,"used_local_facts_ascii_original")
            used_local_facts_ascii_original.text = string_of_facts(used_locals,mode='ascii_original')

            used_local_facts_latex = ET.SubElement(entry,"used_local_facts_latex")
            used_local_facts_latex.text = string_of_facts(used_locals,mode='latex')

            used_global_facts = ET.SubElement(entry,"used_global_facts")
            used_global_facts.text = tokens_of_global_facts(used_globals)

            used_global_facts_ascii_original = ET.SubElement(entry,"used_global_facts_ascii_original")
            used_global_facts_ascii_original.text = string_of_facts(used_globals,mode='ascii_original')

            used_global_facts_latex = ET.SubElement(entry,"used_global_facts_latex")
            used_global_facts_latex.text = string_of_facts(used_globals,mode='latex')

            consequences = ET.SubElement(entry,"consequences") #in fact only one consequence, be backward compatible
            consequences.text = ' '.join(token_of_term(conq_tuple[0].content_in_term)) if has_consequence else ''

            consequences_ascii = ET.SubElement(entry,"consequences_ascii")
            consequences_ascii.text = conq_tuple[0].content_in_ascii if has_consequence else ''

            consequences_ascii_original = ET.SubElement(entry,"consequences_ascii_original")
            consequences_ascii_original.text = conq_tuple[0].content_in_ascii_original if has_consequence else ''

            consequences_latex = ET.SubElement(entry,"consequences_latex")
            consequences_latex.text = conq_tuple[0].content_in_latex if has_consequence else ''

           
            consequences_others = ET.SubElement(entry,"consequences_others")
            consequences_others_ascii_original = ET.SubElement(entry,"consequences_others_ascii_original")
            consequences_others_latex = ET.SubElement(entry,"consequences_others_latex")
            consequences_others_str = ''
            consequences_others_ascii_original_str =''
            consequences_others_latex_str = ''
            if has_consequence: 
                for _,conq_locals,conq_globals in [conq_tuple]: 
                    consequences_others_str += concate_two_strings(tokens_of_local_facts(conq_locals)\
                        ,tokens_of_global_facts(conq_globals))
                    consequences_others_ascii_original_str += concate_two_strings(string_of_facts(conq_locals,mode='ascii_original')\
                        ,string_of_facts(conq_globals,mode='ascii_original'))
                    consequences_others_latex_str += concate_two_strings(string_of_facts(conq_locals,mode='latex')\
                        ,string_of_facts(conq_globals,mode='latex'))
            consequences_others.text = consequences_others_str
            consequences_others_ascii_original.text = consequences_others_ascii_original_str
            consequences_others_latex.text = consequences_others_latex_str
    
    root_path = join(os.path.dirname(thy.filepath),'CausalSteps',thy.thy_name+'.xml')
    with open(root_path, "w") as f:
        from xml.dom import minidom
        xmlstr = minidom.parseString(ET.tostring(root)).toprettyxml(indent="   ")
        f.write(xmlstr)
    return 


def tokens_of_global_facts(g_facts) -> str:
    '''
    g_facts is a list of GlobalFact/CollectedFacts
    '''
    facts_without_collected = filter(lambda x: isinstance(x,GlobalFact),g_facts) 
    list_of_list_of_tokens = map(lambda x: token_of_term(x.content_in_term), facts_without_collected)
    sorted_ll = sorted(list_of_list_of_tokens,key=lambda x: -len(x))
    res = ''
    for ss in sorted_ll:
        res+=' '+SEP_TOKEN+' '+' '.join(ss)
    return res

def tokens_of_local_facts(l_facts) -> str:
    '''
    l_facts is a list of LocalFact
    '''
    list_of_list_of_tokens = map(lambda x: token_of_term(x.content_in_term), l_facts)
    sorted_ll = sorted(list_of_list_of_tokens,key=lambda x: -len(x))
    res = ''
    for ss in sorted_ll:
        res+=' '+SEP_TOKEN+' '+' '.join(ss)
    return res

def anno_and_produce_examples(w_thy):
    
    try:
        annotate_thy(w_thy)
        # print('Finished annotating {}.'.format(w_thy.thy_model.full_filename) )
    except Exception as e:
        append_to_log('Error: failed to annotate {}.\n'.format(w_thy.thy_model.full_filename))
        if hasattr(e,'output'):
            append_to_log('{}\n'.format(e.output))
        print('Failed to annotate:' + w_thy.thy_model.full_filename)
        return
    # print('Start to build CausalSteps of {}'.format(w_thy.thy_model.full_filename))
    try:
        build_CausalSteps(w_thy)
    except Exception as e:
        append_to_log('Error: failed to build CausalSteps of {}.\n'.format(w_thy.thy_model.full_filename))
        if hasattr(e,'output'):
            append_to_log('{}\n'.format(e.output))
        print('Failed to build CausalSteps for ' + w_thy.thy_model.full_filename)
        return
    del w_thy.thy_model
    # print('!!!!', hasattr(w_thy,'thy_model'),hasattr(w_thy,'processed_id'))
    # build_AlternativeCausalSteps(w_thy)
    # build_TransitiveSteps(w_thy)
    return

def retrive_relevant_proofblock(thm_model,isar_loc:str,rs_loc:str,comp_str:str):

    def get_block_isar(model,isar_location,comp_idx): # if the block is None (e.g. when encountering IsarStatement 'assume') IsarStatement is returned instead
        def is_when_if(model):
            if model.key in {'have','show','thus','hence'}:
                if isinstance(model.when_if,list) or isinstance(model.for_vars,list):
                    return True
            if hasattr(model,'props') and isinstance(model.props,Propositions):
                if hasattr(model.props, 'if_if') and isinstance(model.props.if_if, list):
                    return True
                if hasattr(model.props, 'for_vars') and isinstance(model.props.for_vars,list):
                    return True
            return False

        def is_pre_isar(isar_model,comp_idx):
            if comp_idx is None:
                return False
            pre_facts,_,_,_ = isar_model.proof.retrieve_facts(isar_model)
            if comp_idx < len(pre_facts):
                return True
            else:
                return False

        if isar_location == []:
            return ('POST',model)
        if isar_location[-1] == -1:
            _,new_model = get_block_isar(model,isar_location[:-1],comp_idx)
            return ('PRE',new_model)
        isar = model.get_IsarStatement(isar_location)

        if isar.proof is None:
            return ('POST',isar)
        elif is_pre_isar(isar,comp_idx):
            return ('PRE1',isar)
        elif is_when_if(isar):
            return ('PRE',isar.proof)
        else:
            return ('POST',isar.proof)

    def get_block_rs(model,rs_location,comp_idx): 
        hd,tail = rs_location[0],rs_location[1:]
        if len(tail) == 0:
            return get_block_isar(model,hd,comp_idx)
        elif len(tail) == 1:
            _,new_model = get_block_isar(model,hd,comp_idx)
            rstep = new_model.rsteps[tail[0]] if isinstance(new_model,ProofBlock)\
                 else new_model.proof.rsteps[tail[0]] # new_model is of type IsarStatement
            if rstep.sblock is not None:
                return ('POST',rstep.sblock.proof)
            else:
                _,new_model = get_block_isar(model,hd,comp_idx)
                return ('PRE',new_model)
        else:
            _,new_model = get_block_isar(model,hd,comp_idx)
            rstep = new_model.rsteps[tail[0]] if isinstance(new_model,ProofBlock)\
                 else new_model.proof.rsteps[tail[0]] # new_model is of type IsarStatement
            return get_block_rs(rstep.sblock.proof,tail[1:],comp_idx)

    isar_location = isar_location_from_str(isar_loc)
    rs_location = rs_location_from_str(rs_loc) if rs_loc!='None' else None
    comp_idx = int(comp_str) if comp_str!='None' else None
    if rs_loc == 'None': 
        return get_block_isar(thm_model.proof,isar_location,comp_idx)
    else:
        return get_block_rs(thm_model.proof,rs_location,comp_idx)


def create_deriv_DiagStatement(m_id,thy_name,thm_id,raw_seq,fact,fact_asms,parser=None,fact_C=None):
    def enclose_quote(some_str):
        assert isinstance(some_str,str)
        assert '\"' not in some_str
        return '\"'+some_str+ '\"'

    def is_compound(fact:Fact):
        if isinstance(fact,LocalFact):
            return fact.has_forward
        else:
            return False 
        
    isar_idx_str = '\"'+str_of_list(fact.location_in_theorem)+ '\"'
    rs_location_str = '\"'+str_of_tuple(fact.refinement_step_location)+ '\"' \
        if fact.refinement_step_location is not None else '\"<N.A.>\"'
    comp_idx_str = '\"' + str(fact.compound_index) + '\"'
    assert isinstance(m_id,int)
    m_id_str = '\"'+str(m_id)+'\"'
    m_tag = 'AB' if fact_C is None else 'BC'
    attrs=[m_id_str,m_tag,thy_name,thm_id, isar_idx_str,rs_location_str,comp_idx_str] 

    fact_ref = parser.parse(fact.text_infomation,rule_name='fact_reference') if is_compound(fact) else FactReference().set_from_fact(fact) 
    assert fact_ref
    fact_asm_refs = []
    for ff in fact_asms:
        assert ff
        if isinstance(ff,CollectedFacts):
            continue
        ff_ref = parser.parse(ff.text_infomation,rule_name='fact_reference') if is_compound(ff) else FactReference().set_from_fact(ff) 
        fact_asm_refs.append(ff_ref)

    if fact_C is None:
        return DiagStatement(key='check_derivation',attrs=attrs, raw_seq=enclose_quote(raw_seq), fact_ref=fact_ref,fact_asms=fact_asm_refs)
    else:
        fact_ref2 = parser.parse(fact_C.text_infomation,rule_name='fact_reference') if is_compound(fact_C) else FactReference().set_from_fact(fact_C) 
        return DiagStatement(key='check_derivation_C',attrs=attrs, raw_seq=enclose_quote(raw_seq)\
            , fact_ref=fact_ref,fact_ref2=fact_ref2,fact_asms=fact_asm_refs)



class ProcessTheory:

    def __init__ (self, dict_of_metas,parser):
        self.dict_of_metas = dict_of_metas # the dictionary is of type full_theory_name (or thy.full_filename) -> (meta,seq) list
        self.parser = parser

    def annotate_thm(self,thy,m_id,meta,seq):
            
        def add_wrt_tag(pblock_or_isarSt,tag,diag_st):
            if tag == 'PRE':
                assert isinstance(pblock_or_isarSt,ProofBlock)
                pblock_or_isarSt.diag_stats_pre.append(diag_st)
            elif tag == 'POST':
                assert isinstance(pblock_or_isarSt,ProofBlock) or isinstance(pblock_or_isarSt,IsarStatement)
                pblock_or_isarSt.diag_stats_post.append(diag_st)
            else:
                assert tag == 'PRE1' and isinstance(pblock_or_isarSt,IsarStatement)
                pblock_or_isarSt.diag_stats_pre1.append(diag_st)

        thm = thy.get_Theorem_by_id(meta[1])

        fact = thm._fact_dict.get_local_by_location(meta[2],meta[3],meta[4],ascii_cont=meta[5])[0] #assume it is a singleton list
        used_locals = thm._depen_graph.get_used_locals(fact)
        used_globals = thm._depen_graph.get_used_globals(fact)
        diag_st = create_deriv_DiagStatement(m_id,thy.thy_name,thm.thm_id,seq,fact,used_locals+used_globals,parser=self.parser )
        loc_str,rs_str,comp_str = meta[2],meta[3],meta[4]
        (tag,pblock_or_isarSt) = retrive_relevant_proofblock(thm,loc_str,rs_str,comp_str)
        add_wrt_tag(pblock_or_isarSt,tag,diag_st)

        if meta[6]=='True':
            fact_C = thm._fact_dict.get_local_by_location(meta[7],meta[8],meta[9],ascii_cont=meta[10])[0] #assume it is a singleton list
            used_locals_C = [x for x in thm._depen_graph.get_used_locals(fact_C) if x is not fact_C]
            used_globals_C = thm._depen_graph.get_used_globals(fact_C)
            diag_st_C = create_deriv_DiagStatement(m_id,thy.thy_name,thm.thm_id,seq,fact,used_locals_C+used_globals_C,parser=self.parser,fact_C=fact_C )
            loc_str_C,rs_str_C,comp_str_C = meta[7],meta[8],meta[9]
            (tag_C,pblock_or_isarSt_C) = retrive_relevant_proofblock(thm,loc_str_C,rs_str_C,comp_str_C)
            add_wrt_tag(pblock_or_isarSt_C,tag_C,diag_st_C)
        else:
            assert False
            pass


    def process_theory(self,w_thy):
        thy = w_thy.thy_model
        try:
            annotate_thy(w_thy)
        except Exception as e:
            print('Failed to annotate:' + thy.full_filename)
            return
        
        thy.purge_diagnostic()
        
        for (m_id,meta,seq) in self.dict_of_metas[thy.full_filename]:
            self.annotate_thm(thy,m_id,meta,seq)

        thy_str = StringOfTheory(incl_recording= False,incl_evaluation=True).str_Theory(thy)
        with open(thy.filepath,'w') as file:
            file.write(thy_str)    
        print(thy.filepath)

def anno_wrt_derivations(w_thy):
    try:
        annotate_thy(w_thy)
    except Exception as e:
        thy = w_thy.thy_model
        print('Failed to annotate:' + thy.full_filename)
        return
    
    print( w_thy.thy_model.get_Theorem_by_id('thm_de_Morgan9')._fact_dict.local_dict_by_location) 
    return

def annotate_wrt_derivations(dir_path,wrapped_thy_models,dict_of_metas,parser=None):
    assert parser
    print('Start enriching models from the directory {} with info from databases.'.format(dir_path))

    p_thy = ProcessTheory(dict_of_metas, parser)

    with Pool(3) as p: # insufficient RAM when the number of threads is large
        list(p.imap_unordered(p_thy.process_theory, wrapped_thy_models))

    print('Finished successfully!')
    return wrapped_thy_models

def annotate_with_database(dir_path,wrapped_thy_models):
    print('Start enriching models from the directory {} with info from databases.'.format(dir_path))

    with Pool(3) as p: # insufficient RAM when the number of threads is large
        list(p.imap_unordered(anno_and_produce_examples, wrapped_thy_models))
    
    print('Finished successfully!')
    return wrapped_thy_models