from adt import adt, Case
from typing import List,Tuple,  Any, Callable, Type, TypeVar, no_type_check,Generic 
from .parse_yxml import *
import json

'''
  A term in Isabelle is defined in $ISABELLE_HOME/src/Pure/term.ML:

  type indexname = string * int
  type class = string
  type sort = class list
  type arity = string * sort list * sort
  datatype typ =
    Type  of string * typ list |
    TFree of string * sort |
    TVar  of indexname * sort
  datatype term =
    Const of string * typ |
    Free of string * typ |
    Var of indexname * typ |
    Bound of int |
    Abs of string * typ * term |
    $ of term * term
'''

Indexname = Tuple[str,int]
Sort = List[str]

@adt
class Typ:
    TYPE: Case[str,'List[Typ]']
    TFREE: Case[str,Sort]
    TVAR: Case[Indexname,Sort]

@adt
class Term:
    CONST: Case[str,Typ]
    FREE: Case[str,Typ]
    VAR: Case[Indexname,Sort]
    BOUND: Case[int]
    ABS: Case[str,Typ,'Term']
    APP: Case['Term','Term'] # application operation (i.e., '$' in Isabelle)

def destructTerm(trm:Term) -> Tuple[str,Tuple[Any]]:
  return trm.match(const=lambda ss, typ: ('CONST',(ss,typ)) ,\
        free=lambda ss, typ: ('FREE',(ss,typ)),\
        var = lambda idx, srt: ('VAR',(idx,srt)) ,\
        bound=lambda i: ('BOUND',(i,)),\
        abs=lambda ss,typ,trm1: ('ABS',(ss,typ,trm1)) ,\
        app=lambda trm1,trm2: ('APP',(trm1,trm2))\
        )

def eq_ignoring_typ(trm1:Term,trm2:Term) -> bool:
  cons1,args1 = destructTerm(trm1)
  cons2,args2 = destructTerm(trm2)
  if cons1 == cons2:
    if cons1 in ['CONST','FREE', 'VAR','BOUND']:
      return args1[0] == args2[0]
    elif cons1 == 'ABS':
      return args1[0] == args2[0] and eq_ignoring_typ(args1[2],args2[2])
    elif cons1 == 'APP':
      return eq_ignoring_typ(args1[0],args2[0]) and eq_ignoring_typ(args1[1],args2[1])
    else:
      assert False,'Unsupported constructor for Term'
  else:
    return False

def replace_ignoring_typ(trm:Term,m_trm:Term,s_trm:Term) -> Term:
  if eq_ignoring_typ(trm,m_trm):
    return s_trm
  else:
    return trm.match(const=lambda ss, typ: trm ,\
        free=lambda ss, typ: trm,\
        var = lambda idx, srt: trm,\
        bound=lambda i: trm,\
        abs=lambda ss,typ,trm1: Term.ABS(ss,typ,replace_ignoring_typ(trm1,m_trm,s_trm)),\
        app=lambda trm1,trm2: Term.APP(replace_ignoring_typ(trm1,m_trm,s_trm),replace_ignoring_typ(trm2,m_trm,s_trm)) \
        )

def exists_ignoring_typ(trm:Term,m_trm:Term) -> bool:
  if eq_ignoring_typ(trm,m_trm):
    return True
  else:
    # print(token_of_term(trm))
    return trm.match(const=lambda ss, typ: False ,\
        free=lambda ss, typ: False,\
        var = lambda idx, srt: False,\
        bound=lambda i: False,\
        abs=lambda ss,typ,trm1: exists_ignoring_typ(trm1,m_trm),\
        app=lambda trm1,trm2: exists_ignoring_typ(trm1,m_trm) or exists_ignoring_typ(trm2,m_trm)\
        )

def de_sort(ts):
  '''
  val sort = list string;
  '''
  return xml_list(xml_string,ts)

def de_typ(ts):
  '''
  fun typ T = T |> variant
  [fn ([a], b) => Type (a, list typ b),
    fn ([a], b) => TFree (a, sort b),
    fn ([a, b], c) => TVar ((a, int_atom b), sort c)];
  '''
  def f1(strs,ts):
    [a]=strs 
    return Typ.TYPE(a,xml_list(de_typ,ts))
  def f2(strs,ts):
    [a]=strs
    return Typ.TFREE(a,de_sort(ts))
  def f3(strs,ts):
    [a,b] = strs
    return Typ.TVAR((a,int(b)),de_sort(ts))
  return variant([f1,f2,f3],ts)

def de_term(ts):
  '''
  fun term t = t |> variant
    [fn ([a], b) => Const (a, typ b),
      fn ([a], b) => Free (a, typ b),
      fn ([a, b], c) => Var ((a, int_atom b), typ c),
      fn ([a], []) => Bound (int_atom a),
      fn ([a], b) => let val (c, d) = pair typ term b in Abs (a, c, d) end,
      fn ([], a) => op $ (pair term term a)];
  '''
  def f1(strs,ts):
    [a]=strs 
    return Term.CONST(a, de_typ(ts))
  def f2(strs,ts):
    [a]=strs 
    return Term.FREE(a, de_typ(ts))
  def f3(strs,ts):
    [a,b] = strs
    return Term.VAR((a,int(b)),de_typ(ts))
  def f4(strs,ts):
    [a]=strs 
    assert ts == []
    return Term.BOUND(int(a))
  def f5(strs,ts):
    [a]=strs
    c, d = pair(de_typ,de_term,ts)
    return Term.ABS(a,c,d)
  def f6(strs,ts):
    assert strs == []
    t1,t2 = pair(de_term,de_term,ts)
    return Term.APP(t1,t2)
  return variant([f1,f2,f3,f4,f5,f6],ts)

def decode_term_from_yxml(s:str) -> Term:
  return de_term(parse_body(s))

# def token_of_term(trm:Term) -> List[str]:
#   # def m_const(ss:str,typ:Typ):
#   return ['('] + trm.match(\
#             const=lambda ss, _: ['CONST',ss],\
#             free=lambda ss, _: ['FREE',ss],\
#             var = lambda idx, _: ['VAR',idx[0],str(idx[1])],\
#             bound=lambda i: ['BOUND',str(i)],\
#             abs=lambda ss,_,trm: ['ABS',ss]+ token_of_term(trm),\
#             app=lambda trm1,trm2: ['APP']+token_of_term(trm1)+token_of_term(trm2)\
#             )+ [')']

def token_of_term(trm:Term) -> List[str]:
  def token_of_APP(trm1:Term,trm2:Term) -> List[str]:
    if is_APP(trm2):
      return token_of_term(trm1)+['$','(']+token_of_term(trm2)+ [')']
    else:
      return token_of_term(trm1)+['$']+token_of_term(trm2)

  # def m_const(ss:str,typ:Typ):
  return  trm.match(\
            const=lambda ss, _: ['CONST',ss],\
            free=lambda ss, _: ['FREE',ss],\
            var = lambda idx, _: ['VAR',idx[0],str(idx[1])],\
            bound=lambda i: ['BOUND',str(i)],\
            abs=lambda ss,_,trm: ['(','ABS']+ token_of_term(trm)+[')'],\
            app=lambda trm1,trm2: token_of_APP(trm1,trm2)\
            )

def get_const_name(trm:Term) -> str:
  return trm.match(\
      const=lambda ss, _: ss,\
      app=lambda trm1,trm2: None,\
      free=lambda ss, _: None,\
      var=lambda idx, _: None,\
      bound=lambda _: None,\
      abs=lambda ss,_,trm: None)

def is_APP(trm:Term) -> bool:
  return trm.match(\
      const=lambda ss, _: False,\
      app=lambda trm1,trm2: True,\
      free=lambda ss, _: False,\
      var=lambda idx, _: False,\
      bound=lambda _: False,\
      abs=lambda ss,_,trm: False)

def match_app_const(trm:Term,const_names:List[str]) -> Tuple[Term,List[Term]]:
  '''
  Returns:
    (t1,[a1,a2,...]) such that trm == Term.APP(Term.APP(t1,a1),a2)... when get_const_name(trm) in const_names.
    otherwise, None is returned.
  '''
  def f_app(trm1:Term,trm2:Term) -> Tuple[Term,List[Term]]:
    # tt,rr = match_app_const(trm1,const_names)
    res = match_app_const(trm1,const_names)
    if res is None:
      return None
    else:
      tt,rr = res
      rr.append(trm2)
      return tt,rr

  return trm.match(\
      const=lambda ss,tt: (Term.CONST(ss,tt),[]) if ss in const_names else None,\
      app=f_app,\
      free=lambda ss, _: None,\
      var=lambda idx, _: None,\
      bound=lambda _: None,\
      abs=lambda ss,_,trm: None)

trm_Trueprop = decode_term_from_yxml('00=HOL.Trueprop00=fun:00=HOL.bool:00=prop')

trm_dummy = decode_term_from_yxml('00=Pure.dummy_pattern00=dummy')

LEFT_RIGHT_CONSTS = ['Set.member','HOL.eq','Orderings.ord_class.less','Orderings.ord_class.less_eq'\
  ,'Power_Products.plus_class.adds']



def retrieve_transitive(trma:Term,trmb:Term) -> Tuple[Term,Term,Term]:
  _,ra1 = match_app_const(trma,['HOL.Trueprop'])
  ta2,ra2 = match_app_const(ra1[0], LEFT_RIGHT_CONSTS)
  trmb_r = match_app_const(trmb,['HOL.Trueprop']) if trmb else None
  trmb_rr = match_app_const(trmb_r[1][0], LEFT_RIGHT_CONSTS) if trmb_r else None
  if trmb_rr:
    # _,rb1 = trmb_r
    # tb2,rb2 = match_app_const(rb1[0], LEFT_RIGHT_CONSTS)
    tb2,rb2=trmb_rr
    if exists_ignoring_typ(rb2[0],ra2[1]):
      res1 = Term.APP(trm_Trueprop,Term.APP(Term.APP(ta2,ra2[0]),trm_dummy))
      res2 = ra2[1]
      res3 = Term.APP(trm_Trueprop, Term.APP(Term.APP(tb2,replace_ignoring_typ(rb2[0],res2,trm_dummy)),rb2[1]))
      return (res1,res2,res3)
    elif exists_ignoring_typ(ra2[1],rb2[0]):
      res2 = rb2[0]
      res1 = Term.APP(trm_Trueprop, Term.APP(Term.APP(ta2,ra2[0]),replace_ignoring_typ(ra2[1],res2,trm_dummy)))
      res3 = Term.APP(trm_Trueprop,Term.APP(Term.APP(tb2,trm_dummy), rb2[1]))
      return (res1,res2,res3)
    else:
      return None
  else:
    res1 = Term.APP(trm_Trueprop,Term.APP(Term.APP(ta2,ra2[0]),trm_dummy))
    return (res1,ra2[1],None)

def retrieve_right(trm:Term) -> Tuple[Term,Term]:
  '''
  Returns:
    (t1:Term,t2:Term), where t1 is the same as trm except for that the right part being replaced with a dummy term, and t2 is the right part
  '''
  _,r1 = match_app_const(trm,['HOL.Trueprop'])
  assert len(r1) == 1
  t2,r2 = match_app_const(r1[0], LEFT_RIGHT_CONSTS)
  assert len(r2) == 2
  trm1 = Term.APP(trm_Trueprop,Term.APP(Term.APP(t2,r2[0]),trm_dummy))
  return trm1,r2[1]

def replace_in_left(trm:Term,sub:Term) -> Term:
  '''
  Returns:
    a term, which is the same as trm except for the part (in the left) matching sub (igoring types) being replaced with a dummy term. None is returned if no match occurs
  '''
  _,r1 = match_app_const(trm,['HOL.Trueprop'])
  assert len(r1) == 1
  t2,r2 = match_app_const(r1[0], LEFT_RIGHT_CONSTS)
  assert len(r2) == 2
  res = Term.APP(trm_Trueprop, Term.APP(Term.APP(t2,replace_ignoring_typ(r2[0],sub,trm_dummy)),r2[1]))
  # print(token_of_term(res))
  if exists_ignoring_typ(res,trm_dummy):
    return res
  else:
    return None

def is_valid_left_right(trm:Term) -> bool:
  res = match_app_const(trm,['HOL.Trueprop'])
  if res is None:
    return False
  _, r1 = res
  res = match_app_const(r1[0], LEFT_RIGHT_CONSTS)
  if res is None:
    return False
  return True

def split_concl_prems(trm:Term) -> Tuple[Term,List[Term]]:
  res = match_app_const(trm,['HOL.Trueprop'])
  if res:
    return (trm,[])
  else:
    # _ ,r1 = match_app_const(trm,['Pure.imp'])
    res_i = match_app_const(trm,['Pure.imp']) # note 'Pure.all'
    if res_i:
      _ ,r1 = res_i
      c2,r2 = split_concl_prems(r1[1])
      return (c2,[r1[0]] + r2 )
    else:
      return (trm,[])


'''
CONST: Case[str,Typ]
    FREE: Case[str,Typ]
    VAR: Case[Indexname,Sort]
    BOUND: Case[int]
    ABS: Case[str,Typ,'Term']
    APP: Case['Term','Term'] # application operation (i.e., '$' in Isabelle)
'''

if __name__ == '__main__':
  # xx= Typ.TYPE('abc',[Typ.TFREE('abc',['bbc','cbc'])] )
  # print(xx)
  # test_typ_tree = parse(test_typ)[0]

  # print(parse(test_typ)[0].to_string())
  # print(json.dumps(test_typ_tree.__dict__ ) )

  print(parse_body(test_typ))
  print(de_term(parse_body(test_term)))
  trm = de_term(parse_body(test_term))
  print(token_of_term(trm))
  # print()