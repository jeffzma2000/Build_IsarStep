#!/usr/bin/env python
# -*- coding: utf-8 -*-

# CAVEAT UTILITOR
#
# This file was automatically generated by TatSu.
#
#    https://pypi.python.org/pypi/tatsu/
#
# Any changes you make to it will be overwritten the next time
# the file is generated.

from __future__ import print_function, division, absolute_import, unicode_literals

from tatsu.objectmodel import Node
from tatsu.semantics import ModelBuilderSemantics


class ModelBase(Node):
    pass


class ThyModelBuilderSemantics(ModelBuilderSemantics):
    def __init__(self, context=None, types=None):
        types = [
            t for t in globals().values()
            if type(t) is type and issubclass(t, ModelBase)
        ] + (types or [])
        super(ThyModelBuilderSemantics, self).__init__(context=context, types=types)


class Theory(ModelBase):
    abbrevs = None
    imported_thy_names = None
    keywords = None
    text_blocks = None
    thy_name = None
    thy_stats = None


class ExtraContext(ModelBase):
    args = None
    cont = None
    key = None


class ExtraThyCommand(ModelBase):
    args = None
    key = None
    proof = None
    qualifier = None


class Sublocale(ModelBase):
    key = None
    proof = None
    sub_args = None


class Theorem(ModelBase):
    diag_stats = None
    key = None
    locale = None
    proof = None
    qualifier = None
    thm_name = None
    thm_name_args = None
    thm_stat = None


class LocaleClass(ModelBase):
    class_name = None
    eq = None
    ex_thy_stats = None
    inherited_names = None
    key = None
    prec_or_name = None


class Context(ModelBase):
    prec_or_name = None
    thy_stats = None


class NamedTheorems(ModelBase):
    cont = None
    qualifier = None


class Definition(ModelBase):
    key = None
    locale = None
    props = None
    qualifier = None
    vars = None


class Function(ModelBase):
    cont = None
    key = None
    locale = None
    proof = None
    qualifier = None
    vars = None


class Termination(ModelBase):
    key = None
    locale = None
    name = None
    proof = None
    qualifier = None


class TheoremStatement(ModelBase):
    diag_stats = None
    key = None
    ob_cont = None
    preconditions = None
    props = None


class ProofBlock(ModelBase):
    diag_stats_post = None
    diag_stats_pre = None
    key = None
    rsteps = None


class ProofQed(ModelBase):
    closing_tac = None
    isar_stats = None
    main_tac = None


class RefinementStep(ModelBase):
    diag_stats_pre = None
    facts = None
    incl_args = None
    key = None
    sblock = None
    supply_args = None
    tac = None
    tac_arg = None


class ClosingStep(ModelBase):
    closing_tac = None
    diag_stats_pre = None
    key = None
    main_tac = None


class SubgoalBlock(ModelBase):
    bname = None
    for_vars = None
    prem_name = None
    prems = None
    proof = None


class IsarStatement(ModelBase):
    case_arg = None
    case_name = None
    consider_args = None
    diag_stats_post = None
    diag_stats_pre1 = None
    diag_stats_pre2 = None
    facts = None
    for_vars = None
    incl_args = None
    inst = None
    inter_args = None
    isar_stats = None
    key = None
    name_eq = None
    pre_facts = None
    proof = None
    props = None
    vars = None
    when_if = None
    write_args = None


class Tactic(ModelBase):
    key = None
    main_tactic = None
    more_tactics = None
    tac_mod = None


class Instantiations(ModelBase):
    main_inst = None
    more_insts = None


class Propositions(ModelBase):
    for_vars = None
    if_if = None
    main_conts = None
    main_name = None
    more_conts = None


class Variables(ModelBase):
    main_type = None
    main_var = None
    mixfix = None
    more_vars = None


class TextBlock(ModelBase):
    cont = None
    key = None
    opt = None


class FactReference(ModelBase):
    cont = None
    fact_name = None
    for_mod = None
    sel = None


class ForwardModifier(ModelBase):
    cont = None


class Selection(ModelBase):
    cont = None


class DiagStatement(ModelBase):
    attrs = None
    fact_asms = None
    fact_ref = None
    fact_ref2 = None
    key = None
    raw_seq = None
    txt = None
