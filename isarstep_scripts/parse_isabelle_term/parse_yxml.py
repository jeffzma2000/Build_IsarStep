from typing import List,Tuple,  Any, Callable, Type, TypeVar, no_type_check,Generic 
from adt import adt, Case


def xml_escape(str):
    '''
        fun encode "<" = "&lt;"
        | encode ">" = "&gt;"
        | encode "&" = "&amp;"
        | encode "'" = "&apos;"
        | encode "\"" = "&quot;"
        | encode c = c;
    '''
    return str.replace('<',"&lt;").replace(">","&gt;").replace("&","&amp;")\
                .replace("'","&apos;").replace("\"","&quot;")

Attributes = List[Tuple[str,str]]

def xml_elem(name:str,attrs:Attributes) -> str:
    '''
    fun elem name atts =
        space_implode " " (name :: map (fn (a, x) => a ^ "=\"" ^ text x ^ "\"") atts);
    '''
    ats = [name]+list(map(lambda ax:ax[0]+"=\""+xml_escape(ax[1])+"\"", attrs))
    return ' '.join(ats)

# class attributes:
#     '''
#     type attributes = (string * string) list
#     '''
#     def __init__(self,attrs = None):
#         self.attrs = attrs # 

#     def elem(self,name):
#         '''
#             returns string

#             fun elem name atts =
#                 space_implode " " (name :: map (fn (a, x) => a ^ "=\"" ^ text x ^ "\"") atts);
#         '''
#         # print(self.attrs)
#         ats = [name]+list(map(lambda ax:ax[0]+"=\""+xml_escape(ax[1])+"\"", self.attrs))
#         return ' '.join(ats)

@adt
class Tree:
    ELEM: Case[Tuple[Tuple[str,Attributes],List['Tree']]]
    TEXT: Case[str]

    @property
    def to_string(self):
        def traverse(bound,tree):
            '''
            fun traverse _ (Elem ((name, atts), [])) =
                    Buffer.add "<" #> Buffer.add (elem name atts) #> Buffer.add "/>"
                | traverse d (Elem ((name, atts), ts)) =
                    Buffer.add "<" #> Buffer.add (elem name atts) #> Buffer.add ">" #>
                    traverse_body d ts #>
                    Buffer.add "</" #> Buffer.add name #> Buffer.add ">"
                | traverse _ (Text s) = Buffer.add (text s)
            and traverse_body 0 _ = Buffer.add "..."
                | traverse_body d ts = fold (traverse (d - 1)) ts;
            '''
            def elem_case(e):
                (name, atts),ts = e
                if ts == []:
                    return '<'+xml_elem(name,atts)+'/>'
                else:
                    return '<'+xml_elem(name,atts)+'>'+traverse_body(bound,ts)+'</'+name+'>'

            return tree.match(elem=elem_case, text=lambda s: s)
        
        def traverse_body(bound,trees):
            if bound==0:
                return '...'
            else:
                rr = ''
                for tt in trees:
                    rr+=traverse(bound-1,tt)
                return rr
        
        return traverse(-1,self) 


    

X_CHAR = chr(5)
Y_CHAR = chr(6)
XY = X_CHAR + Y_CHAR
XYX = XY + X_CHAR

test1 = "a=bc"+X_CHAR+Y_CHAR+"cc"+X_CHAR+"dd"+Y_CHAR
test2 = "5:5:00=Groups.plus_class.plus00=fun:10='a:Groups.one:Groups.plus:00=fun:10='a:Groups.one:Groups.plus:10='a:Groups.one:Groups.plus:00=Groups.one_class.one10='a:Groups.one:Groups.plus:00=Groups.one_class.one10='a:Groups.one:Groups.plus"

test_typ = "00=List.list:10='a:HOL.type"
test_term = "40=x:10='a:Groups.one:Groups.plus:5:5:00=Groups.plus_class.plus00=fun:10='a:Groups.one:Groups.plus:00=fun:10='a:Groups.one:Groups.plus:10='a:Groups.one:Groups.plus:30=0:00=Groups.one_class.one10='a:Groups.one:Groups.plus"

test3='<5><:><5><:><0 0="Groups.plus_class.plus"><0 0="fun"><:><1 0="&apos;a"><:>Groups.one</:><:>Groups.plus</:></1></:><:><0 0="fun"><:><1 0="&apos;a"><:>Groups.one</:><:>Groups.plus</:></1></:><:><1 0="&apos;a"><:>Groups.one</:><:>Groups.plus</:></1></:></0></:></0></0></:><:><0 0="Groups.one_class.one"><1 0="&apos;a"><:>Groups.one</:><:>Groups.plus</:></1></0></:></5></:><:><0 0="Groups.one_class.one"><1 0="&apos;a"><:>Groups.one</:><:>Groups.plus</:></1></0></:></5>'

test4='<5><:><5><:><0 0="Groups.plus_class.plus"><0 0="fun"><:><1 0="&apos;a"><:>Groups.one</:><:>Groups.plus</:></1></:><:><0 0="fun"><:><1 0="&apos;a"><:>Groups.one</:><:>Groups.plus</:></1></:><:><1 0="&apos;a"><:>Groups.one</:><:>Groups.plus</:></1></:></0></:></0></0></:><:><0 0="Groups.one_class.one"><1 0="&apos;a"><:>Groups.one</:><:>Groups.plus</:></1></0></:></5></:><:><0 0="Groups.one_class.one"><1 0="&apos;a"><:>Groups.one</:><:>Groups.plus</:></1></0></:></5>'

def split_string(str):
    '''
    returns string list list
    
    val split_string =
        Substring.full #>
        Substring.tokens (fn c => c = X_char) #>
        map (Substring.fields (fn c => c = Y_char) #> map Substring.string);
    '''
    xs = filter(None, str.split(X_CHAR))
    return map(lambda x:x.split(Y_CHAR),xs)

def parse_attrib(str):
    '''
    returns string * string

    fun parse_attrib s =
        (case first_field "=" s of
            NONE => err_attribute ()
        | SOME ("", _) => err_attribute ()
        | SOME att => att);
    '''
    return tuple(str.split('=',1))

def parse_chunk(strs,ks):
    '''
    ks is of type ((string * XML.attributes) * XML.tree list) list;
    returns ((string * XML.attributes) * XML.tree list) list  

    fun parse_chunk ["", ""] = pop
        | parse_chunk ("" :: name :: atts) = push name (map parse_attrib atts)
        | parse_chunk txts = fold (add o XML.Text) txts;
    '''
    if len(strs)==2 and strs[0]=='' and strs[1]=='':
        '''
        fun pop ((("", _), _) :: _) = err_unbalanced ""
            | pop ((markup, body) :: pending) = add (XML.Elem (markup, rev body)) pending;
        '''
        (markup,body) = ks[0]
        assert markup[0] != ''
        (markup2,body2) = ks[1]
        pending = ks[2:]
        e_args = markup,list(reversed(body))
        new_tree = Tree.ELEM(e_args)
        return [(markup2,[new_tree]+body2)]+pending
    elif len(strs)>=2 and strs[0]=='':
        name = strs[1]
        assert name != ''
        atts = strs[2:]
        new_atts = list(map(parse_attrib, atts))
        return [((name,new_atts),[])] + ks
    else:
        for ss in strs:
            new_tree = Tree.TEXT(ss)
            (markup,body) = ks[0]
            pending = ks[1:]
            ks = [(markup,[new_tree]+body)]+pending
        return ks

def parse_body(source:str) -> List[Tree]:
    '''
    returns XML.tree list

    fun parse_body source =
        (case fold parse_chunk (split_string source) [(("", []), [])] of
            [(("", _), result)] => rev result
            | ((name, _), _) :: _ => err_unbalanced name);
    '''
    st = [(("", []), [])]
    for ss in split_string(source):
        st = parse_chunk(ss,st)
    assert len(st)==1 and st[0][0][0] == '', 'unbalanced element ' + st[0][0][0]
    return st[0][1]

def parse(source:str) -> Tree:
    '''
    fun parse source =
        (case parse_body source of
            [result] => result
            | [] => XML.Text ""
            | _ => err "multiple results");
    '''
    rr = parse_body(source)
    if len(rr) == 1:
        return rr[0]
    elif rr == []:
        # return tree(text='')
        return Tree.TEXT('')
    else:
        assert False, 'multiple results'

def node(tree):
    '''
    returns tree list

    fun node (Elem ((":", []), ts)) = ts
      | node t = raise XML_BODY [t];
    '''
    def elem_case(e):
        (name, atts),ts = e
        assert name==':' and atts==[]
        return ts
    res= tree.match(elem=elem_case,text=lambda _:None)
    assert res is not None
    return res

def vector(attrs:Attributes) -> List[str]:
    '''
    atts is of type (string * 'a) list;
    returns 'a list

    fun vector atts =
        map_index (fn (i, (a, x)) => if int_atom a = i then x else raise XML_ATOM a) atts;
    '''
    rs = []
    for idx,att in enumerate(attrs):
        at1,at2 = att
        assert type(at1) is str and type(at2) is str
        assert idx==int(at1)
        rs.append(at2)
    return rs

def tagged(tree):
    '''
    returns int * (string list * tree list)

    fun tagged (Elem ((name, atts), ts)) = (int_atom name, (vector atts, ts))
      | tagged t = raise XML_BODY [t];
    '''
    def elem_case(e):
        (name, atts),ts = e
        return (int(name),(vector(atts),ts))
    res = tree.match(elem=elem_case,text=lambda _:None)
    assert res is not None
    return res

def variant(fs,tts:List[Tree]):
    '''
    variant is of type (string list * tree list -> 'a) list -> tree list -> 'a

    fun variant fs [t] =
            let
                val (tag, (xs, ts)) = tagged t;
                val f = nth fs tag handle General.Subscript => raise XML_BODY [t];
            in f (xs, ts) end
      | variant _ ts = raise XML_BODY ts;
    '''
    if len(tts) == 1:
        t = tts[0]
        (tag, (xs, ts)) = tagged(t)
        return fs[tag](xs,ts)
    assert False, len(tts)

def pair(f,g,ts):
    '''
    pair is of type (tree list -> 'a) -> (tree list -> 'b) -> tree list -> 'a * 'b

    fun pair f g [t1, t2] = (f (node t1), g (node t2))
        | pair _ _ ts = raise XML_BODY ts;
    '''
    if len(ts) == 2:
        return (f (node(ts[0])), g (node (ts[1])) )
    assert False


def xml_list(f,ts):
    '''
    xml_list is of type (tree list -> 'a) -> tree list -> 'a list

    fun list f ts = map (f o node) ts;
    '''
    return list(map(lambda x: f(node(x)),ts))

def xml_string(ts):
    '''
    returns string

    fun string [] = ""
    | string [Text s] = s
    | string ts = raise XML_BODY ts;
    '''
    if ts == []:
        return ''
    else:
        # assert len(ts) == 1 and ts[0].text is not None
        # return ts[0].text
        assert len(ts) == 1
        res= ts[0].match( text=lambda s: s, elem=lambda _:None)
        assert res is not None
        return res


def test():
    print(XYX)
    print(list(map(ord,XYX)))
    print(list(split_string(test1)))
    print(parse_attrib(test1))
    print(parse(test2))
    # print(parse(test2)[0].to_string())
    # print(test3==test4)
    return

if __name__ == '__main__':
    test()