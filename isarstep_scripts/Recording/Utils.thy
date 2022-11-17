theory Utils imports Pure
begin

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
    val pp = SOME (Thm.forall_intr_vars thm) handle _ => NONE
  in
    case pp of 
      SOME tt => Thm.prop_of tt 
    | NONE => Thm.prop_of thm
  end
\<close>



end
