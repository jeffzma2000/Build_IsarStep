theory Sequence_Evaluation imports Main (*"/home/wenda/Programs/Isabelle2019_fake/src/HOL/Sledgehammer"*)
  keywords
    "check_derivation" "test_derivation" "check_derivation_C" :: diag
    and 
    
    "@phantom" :: diag 
begin

ML \<open>
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>@phantom\<close> "dummy command as a place holder"
    (Scan.succeed (Toplevel.keep (fn _ => () )));
\<close>

ML \<open>
fun appendToFile filepath str = 
  let
    val os = TextIO.openAppend filepath;
    val _ = TextIO.output(os,str);
    (*val _ = TextIO.flushOut os;*)
    val _ = TextIO.closeOut os
  in
    ()
  end;
\<close>

ML \<open>
local

fun comp_hhf_tac ctxt th i st =
  PRIMSEQ (Thm.bicompose (SOME ctxt) {flatten = true, match = false, incremented = true}
    (false, Drule.lift_all ctxt (Thm.cprem_of st i) th, 0) i) st;

fun comp_incr_tac _ [] _ = no_tac
  | comp_incr_tac ctxt (th :: ths) i =
      (fn st => comp_hhf_tac ctxt (Drule.incr_indexes st th) i st) APPEND
      comp_incr_tac ctxt ths i;

val vacuous_facts = [Drule.termI];

in

fun potential_facts_alt ctxt prop =
  let
    val body = Term.strip_all_body prop;
    val vacuous =
      filter (fn th => Term.could_unify (body, Thm.concl_of th)) vacuous_facts
      |> map (rpair Position.none);
  in Facts.could_unify (Proof_Context.facts_of ctxt) body @ vacuous end;

(*
fun fact_tac ctxt facts = Goal.norm_hhf_tac ctxt THEN' comp_incr_tac ctxt facts;

fun some_fact_tac ctxt =
  SUBGOAL (fn (goal, i) => fact_tac ctxt (map #1 (potential_facts ctxt goal)) i);
*)
end;
\<close>

ML \<open>
fun eval_thm_alt ctxt (fr:Facts.ref * Token.src list) =
  case #1 fr of
    Facts.Named _ => (Attrib.eval_thms ctxt [fr] 
      handle _ => (warning "Has trouble evaluating a named fact.";[]))
    | Facts.Fact s => (case #2 fr of
        [] => (
          let val trm = SOME (Syntax.read_prop ctxt s)
                  handle _ => (warning "Invalid proposition found found.";NONE)
          in
            case trm of
              SOME tt => ([hd (map #1 (potential_facts_alt ctxt tt))]
                              handle Empty => (warning "No potential facts found.";[]))
            | NONE => []
          end)
        | _ => Attrib.eval_thms ctxt [fr])

fun forall_intr_vars_prop_of thm =
  let
    val pp = SOME (forall_intr_vars thm) handle _ => NONE
  in
    case pp of 
      SOME tt => Thm.prop_of tt 
    | NONE => Thm.prop_of thm
  end
\<close>



ML\<open>
val dummy_App = Term.dummy
val dummy_thm = dummy_App |> Thm.cterm_of @{context} |> Thm.reflexive;
val dummy_trm = Term.dummy;
\<close>

ML \<open>
fun check_derivation_with_sledgehammer ctxt trm dels asms =
  (
  let
    val thy = Proof_Context.theory_of ctxt
    val goal = Goal.init (Thm.cterm_of ctxt trm)
    val p_state = Proof.init_alt ctxt asms goal;
    (*val params = Sledgehammer_Commands.default_params thy
                    [("isar_proofs", "false"),("smt_proofs", "false")]*)
    val override = {add=[],del=dels,only=false}
    (*
    val run_sledgehammer = (if false (*set 'false' to shut off the hammer*) then 
                              Sledgehammer.run_sledgehammer params Sledgehammer_Prover.Auto_Try
                                NONE 1 override
                              : Proof.state -> bool * (string * string list)
                            else 
                              (fn _ => (false,("dummy",[])))
                            );*)
    val run_sledgehammer = (fn _ => (false,("dummy",[])))
  in
    if exists_subterm (fn t => Term.aconv_untyped(t, dummy_trm)) trm 
      then (false,("dummy",[])) 
      else run_sledgehammer p_state
  end
  )
\<close>

ML \<open>
local

fun is_special ss = (ss = "thesis__");

fun get_int ss = Substring.substring (ss,2,size ss - 3) |> Substring.string 
      |> Int.fromString |> Option.valOf;

fun get_name_aux_reverse [] ss = ss
  | get_name_aux_reverse fnames ss = if is_special ss then ss else nth fnames (get_int ss)

fun normalise_free_aux_reverse fnames (Free (ss,typ)) = 
     (Free ((get_name_aux_reverse fnames ss),typ))
  | normalise_free_aux_reverse fnames (Abs (ss,typ,trm)) 
        = Abs (ss,typ,normalise_free_aux_reverse fnames trm) 
  | normalise_free_aux_reverse fnames (trm1 $ trm2) 
        = normalise_free_aux_reverse fnames trm1 $ normalise_free_aux_reverse fnames trm2
  | normalise_free_aux_reverse fnames trm = trm

fun normalise_trm_aux_reverse fnames (Free (ss,typ)) = 
     (Free ((get_name_aux_reverse fnames ss),typ))  
  | normalise_trm_aux_reverse fnames (Abs (ss,typ,trm)) 
        = Abs (ss,typ,normalise_trm_aux_reverse  fnames trm) 
  | normalise_trm_aux_reverse  fnames (trm1 $ trm2) 
        = normalise_trm_aux_reverse  fnames trm1 $ normalise_trm_aux_reverse  fnames trm2
  | normalise_trm_aux_reverse  fnames trm = trm;
in

fun normalise_term_reverse ctxt trm =
  let 
    val fnames = Variable.dest_fixes ctxt |> map #2
  in
    normalise_trm_aux_reverse fnames trm handle _ => raise Fail "aa"
  end;
end;
\<close>



ML \<open>
local
exception RawTermParse of (string * (term list) )
exception TypeInference of string
exception TermParse of string


fun extract_bracket xs ("(" :: ys)  n  = extract_bracket ("(" :: xs) ys  (n+1)
   |extract_bracket xs (")" :: ys)  n  = 
      (if n=1 then (tl(rev xs),ys) else extract_bracket (")" :: xs) (ys)  (n-1))
   |extract_bracket xs (y :: ys)  n  = extract_bracket (y :: xs) (ys)  n
;

val _ = extract_bracket [] ["(","x","(","y",")",")"] 0
;


fun extract_bracket xs ("(" :: ys)  n  = extract_bracket ("(" :: xs) ys  (n+1)
   |extract_bracket xs (")" :: ys)  n  = 
      (if n=1 then (tl(rev xs),ys) else extract_bracket (")" :: xs) (ys)  (n-1))
   |extract_bracket xs (y :: ys)  n  = extract_bracket (y :: xs) (ys)  n
;

fun add_to_stack t1 (dummy_App::t2::ts) = (t2 $ t1)::ts
    | add_to_stack t1 ts = t1::ts
;

fun parse_raw_term [trm] [] = trm
  | parse_raw_term ts ("CONST"::s::xs) = 
      parse_raw_term (add_to_stack (Const (s,dummyT)) ts) xs 
  | parse_raw_term ts ("FREE"::s::xs) = 
      parse_raw_term (add_to_stack (Free (s, dummyT)) ts) xs
  | parse_raw_term ts ("VAR"::s::i::xs) 
      = parse_raw_term (add_to_stack (Var ((s,case Int.fromString i of SOME j=> j), dummyT)) ts) xs
  | parse_raw_term ts ("BOUND"::i::xs) 
      = parse_raw_term ( add_to_stack (Bound (case Int.fromString i of SOME j=> j)) ts) xs
  | parse_raw_term ts ("ABS"::xs) 
      =  let val tt = parse_raw_term [] xs in 
            parse_raw_term (add_to_stack (Abs ("_",dummyT,tt)) ts) []
         end (* Abs ("_",dummyT, parse_raw_term ts xs) *)
  | parse_raw_term ts ("$"::xs) = parse_raw_term (add_to_stack dummy_App ts) xs
  | parse_raw_term ts ("(" :: xs) = 
      let val (zs,ws) = extract_bracket [] ("(" :: xs) 0
      in parse_raw_term (add_to_stack (parse_raw_term [] zs) ts) ws end
  | parse_raw_term ts xs = raise RawTermParse ((String.concatWith " " xs) , ts) 
;
in
fun parse_term_from_tokens ctxt str =
      str 
      |> String.tokens (fn c => c = #" " )
      |> (parse_raw_term [] handle _ => raise TermParse "Fail to parse the term")
      |> normalise_term_reverse ctxt
      |> (Syntax.check_term ctxt handle _ => raise TypeInference "Fail to infer types")
      
end
\<close>




ML \<open>
fun get_target_prop (ctxt: Proof.context) (fr:Facts.ref * Token.src list) =
  let 
      val eval_r = eval_thm_alt ctxt fr
      val r = (case eval_r of
               [] => ((case #1 fr of Facts.Fact s => Syntax.read_prop ctxt s) handle _ => dummy_trm)
              | s => hd s |> forall_intr_vars_prop_of)
  in
    r (* |> Term.close_schematic_term *)
  end
\<close>



ML \<open>
fun bool_list_to_string [] = ""
  | bool_list_to_string (x::xs) = (if x then "True " else "False ")^bool_list_to_string xs

fun write_to_file_deri thy_name dir_path xml_str =
  let
      val file_path  = dir_path ^ "/CheckingDerivation/" ^ thy_name ^".xml"  : string;
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

fun print_derivation_xml meta_id meta_tag thy_name thm_id isar_loc rs_loc comp_idx 
      txt 
       = 
  let
  in
    XML.element "derivation" [("meta_id",meta_id),("meta_tag",meta_tag)
      ,("theory_name",thy_name),("theorem_id",thm_id)
      ,("isar_location",isar_loc),("refinement_location",rs_loc)
      ,("compound_index",comp_idx)] [txt]
  end;
\<close>


ML\<open>
fun check_derivation (((attrs:string list, raw_output:string), fr:Facts.ref * Token.src list)
                      ,frs:(Facts.ref * Token.src list) list) = Toplevel.keep 
    (fn state =>
      let 
        val ctxt = Toplevel.context_of state;
        val [meta_id,meta_tag,thy_name,thm_id,isar_loc,rs_loc,comp_idx] = attrs; 
       
        (*
        val prop_list_name = (case #1 fr of 
                                Facts.Named _ => Facts.name_of_ref (#1 fr)|
                                Facts.Fact _ => "<unnamed>");
        *)
        (*
        val props =Attrib.eval_thms ctxt [fr] |> map Thm.prop_of 
                      handle ERROR msg => (warning msg ;[]);
        *)
       
        (*
        val props =eval_thm ctxt fr 
                      (*|> map (atomise_thm ctxt)*)
                      |> map forall_intr_vars_prop_of
                      (*|> Syntax.uncheck_terms ctxt*)
                      |> map Term.close_schematic_term
                      handle ERROR msg => (warning msg ;[]);
        *)

        val assumptions = frs
                          |> map (eval_thm_alt ctxt) |> List.concat
                          (*|> Attrib.eval_thms ctxt*);
        
        (* val _ = @{print} assumptions;*)   

        val output_trm = (parse_term_from_tokens ctxt raw_output
                          |> singleton(Variable.polymorphic ctxt)
                          (*|> (Term.close_schematic_term)*)) handle _ => dummy_trm;
        (*val _ = @{print} output_trm;*)
        val target_pp = get_target_prop ctxt fr
        (*val _ = @{print} target_pp;*)
        
        val target_not_dummy = not (target_pp aconv dummy_trm)
        val output_not_dummy = not (output_trm aconv dummy_trm)
        val output_aconv_target = (output_trm aconv target_pp);
        val output_unify_target = Term.could_unify (output_trm, target_pp)
        val if_target_derivable = (check_derivation_with_sledgehammer ctxt target_pp [fr] assumptions
                        handle _ => (false,("dummy",[]))) |> fst;
        val if_output_derivable = (check_derivation_with_sledgehammer ctxt output_trm [fr] assumptions
                        handle _ => (false,("dummy",[]))) |> fst;
        
        val res = [target_not_dummy,output_not_dummy,output_aconv_target
                      ,output_unify_target,if_target_derivable,if_output_derivable]


        val _ = @{print} res
      
        val xml_str = bool_list_to_string res |> 
              print_derivation_xml  meta_id meta_tag thy_name thm_id isar_loc rs_loc comp_idx 
              ;
        val path = Resources.master_directory (Proof_Context.theory_of ctxt) 
                            |> File.platform_path;
        val _ = write_to_file_deri thy_name path xml_str
        
        (*val _ = @{print} props; (*having this line may cause memory 
            issue when processing large repository*)*)
        
        (*
        val xml_str = print_facts_xml ctxt a1 a2 a3 a3'  
                        ns a4 a5 normalise_props;
        val path = Resources.master_directory (Proof_Context.theory_of ctxt) 
                            |> File.platform_path;
        *)        

        (*val _ = writeln ("Recorded text is <"^xml_str^">");*)
          
        (*
        val _ = write_to_file a1 path xml_str
        *)
    in () end 
    (*
    handle ERROR msg => appendToFile "/home/wenda/Dropbox/isabelle_playaround/isa_dataset/Recording/log.txt" (msg^"\n"^hd attrs^"\n")
    *)
    ) 
    ;

fun check_derivation_C ((((attrs:string list, raw_output:string)
      , fr:Facts.ref * Token.src list)
      , fr1:Facts.ref * Token.src list)
      , frs:(Facts.ref * Token.src list) list) 
= Toplevel.keep 
    (fn state =>
      let 
        val ctxt = Toplevel.context_of state;
        val [meta_id,meta_tag,thy_name,thm_id,isar_loc,rs_loc,comp_idx] = attrs; 
       
        (*
        val prop_list_name = (case #1 fr of 
                                Facts.Named _ => Facts.name_of_ref (#1 fr)|
                                Facts.Fact _ => "<unnamed>");
        *)
        (*
        val props =Attrib.eval_thms ctxt [fr] |> map Thm.prop_of 
                      handle ERROR msg => (warning msg ;[]);
        *)
       
        (*
        val props =eval_thm ctxt fr 
                      (*|> map (atomise_thm ctxt)*)
                      |> map forall_intr_vars_prop_of
                      (*|> Syntax.uncheck_terms ctxt*)
                      |> map Term.close_schematic_term
                      handle ERROR msg => (warning msg ;[]);
        *)

        val assumptions = frs
                          |> map (eval_thm_alt ctxt) |> List.concat
                          (*|> Attrib.eval_thms ctxt*);
        
        (* val _ = @{print} assumptions;*)   

        val output_trm = (parse_term_from_tokens ctxt raw_output
                          |> singleton(Variable.polymorphic ctxt)
                          (*|> (Term.close_schematic_term)*)) handle _ => dummy_trm;
        (*val _ = @{print} output_trm;*)
        val target_pp = get_target_prop ctxt fr
        val concl_pp = get_target_prop ctxt fr1

        val concl_not_dummy = not (concl_pp aconv dummy_trm)
        val concl_via_output = Logic.mk_implies(output_trm,concl_pp)
        val if_concl_via_output = (check_derivation_with_sledgehammer ctxt 
              concl_via_output [fr] assumptions
                        handle _ => (false,("dummy",[]))) |> fst;
        val concl_via_target = Logic.mk_implies(target_pp,concl_pp)
        val if_concl_via_target = (check_derivation_with_sledgehammer ctxt 
             concl_via_target  [fr] assumptions
                        handle _ => (false,("dummy",[]))) |> fst;
        
        val res = [concl_not_dummy,if_concl_via_output,if_concl_via_target]

        val _ = @{print} res
        (*
        val _ = @{print} (Term.could_unify((Logic.mk_implies(output_trm,concl_pp)),
                                (Logic.mk_implies(target_pp,concl_pp))))
        *)
        val _ = writeln (Syntax.string_of_term ctxt concl_via_output)
        val _ = writeln (Syntax.string_of_term ctxt concl_via_target)
        val xml_str = bool_list_to_string res |> 
              print_derivation_xml  meta_id meta_tag thy_name thm_id isar_loc rs_loc comp_idx 
              ;
        val path = Resources.master_directory (Proof_Context.theory_of ctxt) 
                            |> File.platform_path;
        val _ = write_to_file_deri thy_name path xml_str
    in () end 
    (*
    handle ERROR msg => appendToFile "/home/wenda/Dropbox/isabelle_playaround/isa_dataset/Recording/log.txt" (msg^"\n"^hd attrs^"\n")
    *)
    ) 
    ;
\<close>


ML \<open>

val opt_attrs = Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

val opt_thms = Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat Parse.thm --| \<^keyword>\<open>)\<close>)) [];

(*
val foo1 = map Token.unparse;

val foo = Token.pretty_src @{context} #> Pretty.string_of;
*)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>check_derivation\<close> "record facts by name or content string"
    (opt_attrs -- Parse.name -- Parse.thm -- opt_thms >> (fn x => 
      let (*val _ = @{print} (x |> #1 |> #2)
          val tsl = x |> #1 |> #2 |> #2 |> map foo1 |> map (String.concatWith " ") |> (String.concatWith " ")
          val _ = writeln tsl
          *)
        in 
           

          check_derivation x
        
        end));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>check_derivation_C\<close> "record facts by name or content string"
    (opt_attrs -- Parse.name -- Parse.thm -- Parse.thm -- opt_thms >> (fn x => 
      let (*val _ = @{print} (x |> #1 |> #2)
          val tsl = x |> #1 |> #2 |> #2 |> map foo1 |> map (String.concatWith " ") |> (String.concatWith " ")
          val _ = writeln tsl
          *)
        in 
           

          check_derivation_C x
        
        end));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>test_derivation\<close> "record facts by name or content string"
    ( Parse.thm -- Parse.text >> (fn x => 
      let 
          val _ = @{print} x
          val _ = writeln ""
        in 
           
          Toplevel.keep (fn state => () )
        
        end));
\<close>



(*
CONST HOL.Trueprop $ ( CONST Set.member $ FREE <X3> $ FREE <X4> )
*)

(*
notepad
begin
  fix P::"'a \<Rightarrow> bool" and y x::'a and S::"'a set"
  assume pp:"P x" and pq:"x\<in>S" and xy:"x=y"

ML_val \<open>
  val qq = @{thms pq};
  val qq = @{thm pq} |> Thm.prop_of;
  (normalise_term @{context} qq |> normalise_term_reverse @{context}) aconv qq;
  (normalise_term @{context} qq) aconv qq;
  (normalise_term @{context} @{term "y\<in>S"});
  (normalise_term @{context} @{term "x=y"})
\<close>

ML_val\<open>
dummy_App |> Thm.cterm_of @{context} |> Thm.reflexive;
Thm.reflexive;

val tt = @{thms \<open>x\<in>S\<close> \<open>x=y\<close>};
 Simplifier.add_simp;
let
val ctxt = @{context};
val trm = @{term "Trueprop (y\<in>S)"};
in
Goal.prove ctxt [] [] trm (fn _ => 
    Timeout.apply (Time.fromSeconds 10) (HEADGOAL(Method.insert_tac ctxt tt) THEN (auto_tac ctxt))  
    ) 
end
\<close>

  have "y\<in>S" using pq \<open>x=y\<close> by auto

check_derivation (Drinker thm_x_sq1 "[2]" "<N.A.>" "this") "CONST HOL.Trueprop $ ( CONST Set.member $ FREE <X1> $ FREE <X3> )"
    TrueI (TrueI)


end
*)


(*
type fact_override =
    {add : (Facts.ref * Token.src list) list,
     del : (Facts.ref * Token.src list) list,
     only : bool}
*)



(*
ML_val \<open>
@{thm conjI} |> Thm.prop_of;
exists_subterm (fn t => Term.aconv_untyped(t, dummy_trm))
\<close>
*)


(*
ML_val \<open>
Sledgehammer_Fact.cartouche_thm @{context} @{thm conjI};

val trm = Logic.mk_implies (@{term "Trueprop False"},@{term "Trueprop (1=2)"}) ;

check_derivation_with_sledgehammer @{context} trm [] []
\<close>
*)
(*

notepad
begin
  fix P::"'a \<Rightarrow> bool"
  assume pp:"\<And>x. P x"

  ML_val \<open>
atomise_thm;
@{thm pp};
forall_intr_vars @{thm pp};
\<close>

  ML_val \<open>
  val t = @{thm pp} (*|> atomise_thm @{context}*) |> Thm.prop_of ;
  val tt = @{term "\<And>x. P x"};
  ascii_of_term @{context} t; 
  ascii_of_term @{context} tt; 
  
\<close>

  thm pp
  thm \<open>\<And>x. P x\<close>
  (*
  thm \<open>P ?x\<close>
  *)
end
*)

(*
CONST HOL.Trueprop $ ( CONST Set.member $ FREE <X5> $ FREE <X1> )
*)


(*
ML \<open>
extract_bracket [] ["(","x","(","y",")",")","aa"] 0
;
Syntax_Phases.term_check
\<close>

ML \<open>
@{term HOL.Trueprop};
parse_term_from_tokens @{context} "CONST HOL.Trueprop $ ( CONST Set.member $ FREE <X5> $ FREE <X1> )";
\<close>

ML \<open>
val yyy = @{term "(x \<in> y)"};

val yy=parse_raw_term [] (" ( CONST Set.member $ FREE <X5> ) $ FREE <X1> "|> String.tokens (fn c => c = #" " ));
\<close>

ML \<open>
nth [1,2,3] 0;
"1a23" |> size;
val ss = "1a233" ;
Substring.string;
Option.valOf
;
Substring.substring (ss,2,size ss - 3) |>Substring.string |>   Int.fromString |> Option.valOf

\<close>




notepad
begin
  fix x y :: bool and P::"'a \<Rightarrow> 'b \<Rightarrow> bool"
  assume qq:"x=y" and pp:"\<And>x z. P x z"  and pp':"\<And>y z. P y z"

ML_val
\<open>
  val x = @{thm pp} |> Thm.prop_of ;
  val y = @{thm pp'} |> Thm.prop_of ;
  aconv (x,y);
  Term.could_unify (x,y);
  Term.close_schematic_term x 
\<close>

ML_val
\<open>
  val qq = @{thm qq} |> Thm.prop_of;
  (normalise_term @{context} qq |> normalise_term_reverse @{context}) aconv qq;
  (normalise_term @{context} qq) aconv qq
\<close>








end




















ML \<open>
yy;
 [yy] |> Syntax.check_terms @{context};
Syntax_Phases.print_checks @{context}
\<close>


lemma "P \<Longrightarrow> P" by auto

  ML_val \<open>
Goal.prove;
val auto_method =
  Scan.lift (Scan.option (Parse.nat -- Parse.nat)) --|
    Method.sections clasimp_modifiers >>
  (fn NONE => SIMPLE_METHOD o CHANGED_PROP o auto_tac
    | SOME (m, n) => (fn ctxt => SIMPLE_METHOD (CHANGED_PROP (mk_auto_tac ctxt m n))));

\<close>

context
  fixes P Q R::bool
  assumes pq:"P=Q" 
begin

lemma "P \<Longrightarrow> Q"
  apply (insert pq)
  apply simp

  ML_val \<open>
Method.get_facts @{context}

\<close>

  using pq

 ML_val \<open>
Method.get_facts @{context}

\<close>
  oops


ML_val \<open>

Proof_Context.note_thms ""
       ((Binding.empty, [Context_Rules.rule_del]), [([allI], [])])
\<close>

ML\<open>  
Timeout.apply (Time.fromSeconds 10);
 HEADGOAL;
 val tt = @{thms pq};     
 Simplifier.add_simp;
 Proof_Context.note_thmss;
 Proof_Context.put_thms false ("x",SOME tt)
\<close>

ML_val\<open>
dummy_App |> Thm.cterm_of @{context} |> Thm.reflexive;
Thm.reflexive;

val tt = @{thms pq};
 Simplifier.add_simp;
let
val ctxt = @{context};
val trm = @{term "R \<Longrightarrow> Q::bool"};
in
Goal.prove ctxt [] [] trm (fn {context = ctxt, ...} => 
    Timeout.apply (Time.fromSeconds 10) (HEADGOAL(Method.insert_tac ctxt tt) THEN (auto_tac ctxt))  
    ) handle _ => @{thm pq}
end
\<close>

ML_val \<open>
Goal.prove_sorry
\<close>

ML \<open>

\<close>

end


context
  fixes x::"'a::idom" and xs::"'a set"
begin

ML_val \<open>
val x= (Const ("Set.member",dummyT) $ Free ("x", dummyT)) $ Free ("xs", dummyT);
val y=Type_Infer_Context.infer_types @{context} [x] |> hd ;
val z = @{term "x\<in>xs"};
Term.aconv (y, z);
Term.aconv (@{term "\<lambda>x. x"}, @{term "\<lambda>y. y"});
@{term "(\<lambda>x. x) 1 "}
\<close>
end
*)
(*
ML_val \<open>
fun SOLVE_TIMEOUT seconds name tac st =
  let
    val result =
      TimeLimit.timeLimit (Time.fromSeconds seconds)
        (fn () => SINGLE (SOLVE tac) st) ()
      handle TimeLimit.TimeOut => NONE
        | ERROR _ => NONE
  in
    (case result of
      NONE => (warning ("FAILURE: " ^ name); Seq.empty)
    | SOME st' => (warning ("SUCCESS: " ^ name); Seq.single st'))
  end
\<close>
*)
ML_val \<open>
(*
fun DETERM_TIMEOUT delay tac st =
  Seq.of_list (the_list (Timeout.apply delay (fn () => SINGLE tac st) ()))
*)
\<close>


ML_val \<open>


(*
fun check_deri ctxt trm timeout assumptions =
  Goal.prove ctxt [] [] trm (fn {context = ctxt, ...} => 
    Timeout.apply (Time.fromSeconds timeout) (HEADGOAL(Method.insert_tac ctxt assumptions) 
                        THEN (auto_tac ctxt))
     (*handle Timeout.TIMEOUT _ => []  *)
    ) handle  _ => dummy_thm
;
*)

(*
fun check_deri' ctxt trm timeout assumptions =
  Goal.prove ctxt [] [] trm (fn {context = ctxt, ...} => 
     (HEADGOAL(Method.insert_tac ctxt assumptions) 
                        THEN ( DETERM_TIMEOUT (Time.fromSeconds timeout) 
                            (HEADGOAL (full_simp_tac ctxt))) )
     (*handle Timeout.TIMEOUT _ => []  *)
    ) handle  _ => (writeln "Timeout/Fail!";dummy_thm)
;
*)

\<close>

(*
ML \<open>
fun loop x = loop x;
\<close>

ML_val\<open>
check_deri' @{context} @{term "Trueprop (a=b)"} 10 []
\<close>

lemma "a=b"
  apply (subst refl)
*)


end