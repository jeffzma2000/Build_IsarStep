theory ProofRecording imports Utils
  keywords
    "record_facts"  "@phantom" "record_all_facts" :: diag
begin

ML \<open>
fun atomise_thm ctxt thm =  
  let 
    val thm' = forall_intr_vars thm (*forall_intr_vars may throw exception sometimes*)
    val meta_eq = Object_Logic.atomize ctxt (Thm.cprop_of thm')
  in
    if Thm.is_reflexive meta_eq then
      thm
    else
      Raw_Simplifier.rewrite_rule ctxt [meta_eq] thm'
  end
\<close>

ML \<open>
local

fun is_special ss = (ss = "thesis__");

fun get_name_aux [] ss _ = ss
  | get_name_aux (name::fnames) ss k =
      if is_special ss then ss else
        if ss=name then "<X"^Int.toString k^">"  else 
          get_name_aux fnames ss (k+1)

fun normalise_free_aux fnames (Free (ss,typ)) = 
     (Free ((get_name_aux fnames ss 0),typ))
  | normalise_free_aux fnames (Abs (ss,typ,trm)) 
        = Abs (ss,typ,normalise_free_aux fnames trm) 
  | normalise_free_aux fnames (trm1 $ trm2) 
        = normalise_free_aux fnames trm1 $ normalise_free_aux fnames trm2
  | normalise_free_aux fnames trm = trm

structure Vars = Table(type key = indexname * typ val ord = Term_Ord.var_ord);

fun dest_var_indexnames trm =
  let
    val tt=fold_aterms (fn (Var x) => Vars.update (x,())| _ => I) trm Vars.empty 
  in
    tt |> Vars.keys |> map #1
  end;

fun get_idxn_aux (vn::vnames) ix k  =
        if Term.eq_ix(ix,vn) then ("<V"^Int.toString k^">", #2 ix):indexname  else 
          get_idxn_aux vnames ix (k+1);

fun normalise_var_aux vnames (Var (ix,typ)) = 
     (Var ((get_idxn_aux vnames ix 0),typ))
  | normalise_var_aux vnames (Abs (ss,typ,trm)) 
        = Abs (ss,typ,normalise_var_aux vnames trm) 
  | normalise_var_aux vnames (trm1 $ trm2) 
        = normalise_var_aux vnames trm1 $ normalise_var_aux vnames trm2
  | normalise_var_aux vnames trm = trm;

fun normalise_trm_aux vnames fnames (Var (ix,typ)) = 
     (Var ((get_idxn_aux vnames ix 0),typ))
  | normalise_trm_aux vnames fnames (Free (ss,typ)) = 
     (Free ((get_name_aux fnames ss 0),typ))  
  | normalise_trm_aux vnames fnames (Abs (ss,typ,trm)) 
        = Abs (ss,typ,normalise_trm_aux vnames fnames trm) 
  | normalise_trm_aux vnames fnames (trm1 $ trm2) 
        = normalise_trm_aux vnames fnames trm1 $ normalise_trm_aux vnames fnames trm2
  | normalise_trm_aux vnames fnames trm = trm;
in

fun normalise_term ctxt trm =
  let 
    val fnames = Variable.dest_fixes ctxt |> map #2
    val vnames = dest_var_indexnames trm
  in
    normalise_trm_aux vnames fnames trm
  end;
end;
\<close>

(*
SML_file "IOtest.sml"             
*)



(*
ML \<open>
Word.wordSize;
Word.<<(0w1,0w3);
Word.fromInt (Char.ord #"a");

fun hash_mod str mm =
  let
    val i =  Unsynchronized.ref ((String.size str) - 1);
    val hh =  Unsynchronized.ref 0w5381;
  in 
    while (!i >=0) do 
      (hh:= (Word.<<(!hh, 0w5) + !hh) + Word.fromInt (Char.ord (String.sub(str, !i))); 
        i:= !i-1); 
    Word.mod(!hh, Word.fromInt(mm)) |> Word.toInt 
  end;
\<close>

ML \<open>
  hash_mod "abcdedasc" 30;
  Int.toString ;
\<close>
*)

SML_file "Base64.sml"

SML_export \<open>
  val base64_encode = Base64.encode;
\<close>

ML_val\<open>
singleton
\<close>

ML \<open>
fun yxml_of_term trm =
  let
    val xml_body = trm |> Term_XML.Encode.term;
  in xml_body |> YXML.string_of_body end;

fun xml_of_term trm = 
      let 
        val xml_body = Term_XML.Encode.term trm;
        val _ = @{assert} (length xml_body = 1);
      in
        hd (xml_body) |> XML.string_of
      end;

fun term_of_xml str = 
      let 
        val trm = [str |> XML.parse] |> Term_XML.Decode.term;
      in
        trm
      end;

fun ascii_of_term ctxt trm = 
  let 
    val xml_body = Syntax.string_of_term ctxt trm |> YXML.parse_body;
  in XML.content_of xml_body end;

fun latex_of_term ctxt trm = 
  Print_Mode.with_modes ["latex"] (ascii_of_term ctxt) trm;

(*escape the body part, while XML.element doesn't*)
fun element' name atts body = XML.element name atts [XML.text body]

(*
fun print_prop_xml ctxt thy_name thm_name isar_loc prop_loc trm = 
  let
    val ascii = element' "ascii" [] (ascii_of_term ctxt trm);
    val yxml = element' "yxml" [] (base64_encode(yxml_of_term trm));
  in
    XML.element "proposition" [("theory_name",thy_name),("theorem_name",thm_name)
      ,("isar_location",isar_loc) ,("prop_location",prop_loc)] [ascii,yxml] 
  end;
*)

fun print_facts_xml ctxt thy_name thm_id isar_loc rs_loc props_name more_info comp_idx trms 
      (txt:string option) = 
  let
    val normalise_props = trms
              |> map (fn x => (normalise_term ctxt x, x))
              |> map (fn (x,y) => (singleton(Syntax.uncheck_terms ctxt) x
                                  ,singleton(Syntax.uncheck_terms ctxt) y)) ;

    val props_xml = map (fn (x,y) => XML.element "prop" [] 
          [element' "ascii" [] (ascii_of_term ctxt x)
           , element' "ascii_original" [] (ascii_of_term ctxt y)
           , element' "latex" [] (latex_of_term ctxt y)
           , element' "yxml" [] (base64_encode(yxml_of_term x))]) normalise_props 
    
    val txt_str = (case txt of SOME x => x | NONE => "<N.A.>");  

  in
    XML.element "propositions" [("theory_name",thy_name),("theorem_id",thm_id)
      ,("isar_location",isar_loc),("refinement_location",rs_loc),("props_name",props_name),("more_info",more_info)
      ,("compound_index",comp_idx),("text_information",txt_str)] props_xml
  end;
\<close>


(*
find_theorems "_ / 0 = 0"

thm (latex) division_ring_divide_zero

ML \<open>

val t1 = atomise_thm @{context} @{thm division_ring_divide_zero};
t1 |> Thm.prop_of |> latex_of_term @{context} 

\<close>
*)


ML \<open>
val opt_attrs = Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

(*
fun print_prop (attrs:string list, prop_str) = Toplevel.keep (fn state =>
    let val ctxt = Toplevel.context_of state;
        val [a1,a2,a3,a4] = attrs; (*assuming there exist exactly four attributes*)
        val prop = Syntax.read_prop ctxt prop_str;
        val ctxt' = Variable.auto_fixes prop ctxt;
        val xml_str = print_prop_xml ctxt a1 a2 a3 a4 prop;
        val path = Resources.master_directory (Proof_Context.theory_of ctxt') 
                            |> File.platform_path;
        val file_path  = path ^ "/Database.xml" : string;
        val cmd = ("echo '" ^ xml_str ^ "' >> " ^ file_path);
        val _ = Isabelle_System.bash cmd;
        val _ = writeln("bash command is:" ^ cmd)
    in () end);
*)

fun write_to_file thy_name dir_path xml_str =
  let
      val file_path  = dir_path ^ "/Database/" ^ thy_name ^".xml"  : string;
      (*
      val cmd = ("( flock -x 200; echo '" ^ xml_str ^ "' >> " ^ file_path 
                    ^ ") 200>/var/lock/mylockfile" ^ Int.toString(hash_mod thy_name 500));
      val _ = Isabelle_System.bash cmd;
      val _ = writeln("bash command is:" ^ cmd)
      *)
      (*
      val cmd = ("echo '" ^ xml_str ^ "' >> " ^ file_path);
      *)
      val _ = appendToFile file_path (xml_str^"\n")
  in () end;



fun print_facts ((attrs:string list, fr:Facts.ref * Token.src list),txt:string option) = Toplevel.keep 
    (fn state =>
      let 
        val ctxt = Toplevel.context_of state;
        val a1::a2::a3::a3'::ns::ats = attrs; 
        val a4 = (if ats=[] then "None" else hd ats);
        val a5 = (if length ats = 2 then hd (tl ats) else "None");   
        (*
        val prop_list_name = (case #1 fr of 
                                Facts.Named _ => Facts.name_of_ref (#1 fr)|
                                Facts.Fact _ => "<unnamed>");
        *)
        (*
        val props =Attrib.eval_thms ctxt [fr] |> map Thm.prop_of 
                      handle ERROR msg => (warning msg ;[]);
        *)
        
        val props =eval_thm_alt ctxt fr 
                      |> map forall_intr_vars_prop_of
                      (*|> map (atomise_thm ctxt)
                      |> map Thm.prop_of *)
                      handle ERROR msg => (warning msg ;[]);
        (*
        val normalise_props = props 
              |> map (normalise_term ctxt)
              |> Syntax.uncheck_terms ctxt ;
        *)        

        (*val _ = @{print} props; (*having this line may cause memory 
            issue when processing large repository*)*)
        val xml_str = print_facts_xml ctxt a1 a2 a3 a3'  
                        ns a4 a5 props txt;
        val path = Resources.master_directory (Proof_Context.theory_of ctxt) 
                            |> File.platform_path;
        (*val _ = writeln ("Recorded text is <"^xml_str^">");*)
        val _ = write_to_file a1 path xml_str
     (*
        val file_path  = path ^ "/Database.xml" : string;
        val cmd = ("( flock -x 200; echo '" ^ xml_str ^ "' >> " ^ file_path ^ ") 200>/var/lock/mylockfile");
        (*val cmd = ("echo '" ^ xml_str ^ "' >> " ^ file_path);*)
        val _ = Isabelle_System.bash cmd;
        val _ = writeln("bash command is:" ^ cmd)
     *)
    in () end handle ERROR msg => appendToFile "/home/wenda/Dropbox/isabelle_playaround/isa_dataset/Recording/log.txt" (msg^"\n"^hd attrs^"\n"))
    ;

fun print_all_facts (attrs:string list) = Toplevel.keep (fn state =>
    let val ctxt = Toplevel.context_of state;
        val a1::a2::a3::a3'::ns::ats = attrs; 
        val a4 = (if ats=[] then "None" else hd ats);
        val a5 = (if length ats = 2 then hd (tl ats) else "None");   
        val props = map #1 (Facts.props (Proof_Context.facts_of ctxt)) 
              |> map forall_intr_vars_prop_of
              (*|> map (atomise_thm ctxt)
              |> map Thm.prop_of*);
        (*
        val normalise_props = props 
                |> map (normalise_term ctxt)  
                |> Syntax.uncheck_terms ctxt;
        *)

        val xml_str = print_facts_xml ctxt a1 a2 a3 a3'  
                        ns a4 a5 props NONE;
        val path = Resources.master_directory (Proof_Context.theory_of ctxt) 
                            |> File.platform_path;
        val _ = write_to_file a1 path xml_str
(*
        val file_path  = path ^ "/Database.xml" : string;
        val cmd = ("( flock -x 200; echo '" ^ xml_str ^ "' >> " ^ file_path ^ ") 200>/var/lock/mylockfile");
        (*val cmd = ("echo '" ^ xml_str ^ "' >> " ^ file_path);*)
        val _ = Isabelle_System.bash cmd;
        val _ = writeln("bash command is:" ^ cmd)
*)
    in () end);

(*
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>record_prop\<close> "read and print proposition"
    (opt_attrs -- Parse.term >> (fn x => let val _ = writeln (#2 x);val _ = @{print} (#1 x) in print_prop x end));
*)

local

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>record_facts\<close> "record facts by name or content string"
    (opt_attrs -- Parse.thm -- (Scan.option Parse.text) >> (fn x => let (*val _ = @{print} x*) 
        in
           (*Toplevel.keep (fn state => ()) *)
          print_facts x
        end));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>record_all_facts\<close> "record all local facts"
    (opt_attrs >> (fn x => let (*val _ = @{print} x*)
        in print_all_facts x end));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>@phantom\<close> "dummy command as a place holder"
    (Scan.succeed (Toplevel.keep (fn _ => () )));
in end;
\<close>

end