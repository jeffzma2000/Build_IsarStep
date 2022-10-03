theory "Drinker" imports
  Complex_Main "/home/wenda/Dropbox/isabelle_playaround/Build_IsarStep/isarstep_scripts/Recording/ProofRecording"


begin

lemma x_sq :
 "(0::real) \<le> x^2+2*x+1"
  record_all_facts ( Drinker thm_x_sq0 "[-1]" "<N.A.>" "<unnamed>" )
proof -
  have  "0 \<le> (x+1)^2"
    by auto
  record_facts ( Drinker thm_x_sq0 "[0]" "<N.A.>" "this" ) this \<open>this\<close>
  also 
  have  "... = x^2+2*x+1"
  record_facts ( Drinker thm_x_sq0 "[1]" "<N.A.>" "power2_eq_square" used_fact ) power2_eq_square \<open>power2_eq_square\<close>
    by (auto simp : power2_eq_square algebra_simps)
  record_facts ( Drinker thm_x_sq0 "[1]" "<N.A.>" "this" ) this \<open>this\<close>
  finally 
  show  "0 \<le> x^2+2*x+1"
    .
  record_facts ( Drinker thm_x_sq0 "[2]" "<N.A.>" "this" ) this \<open>this\<close>
qed 
record_facts ( Drinker thm_x_sq0 "[]" "<N.A.>" "x_sq" ) x_sq \<open>x_sq\<close>


theorem sqt_2_irra :
 "sqrt 2 \<notin> \<rat>"
  record_all_facts ( Drinker thm_sqt_2_irra1 "[-1]" "<N.A.>" "<unnamed>" )
proof 
  assume  "sqrt 2 \<in> \<rat>"
  record_facts ( Drinker thm_sqt_2_irra1 "[0]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[1]" "<N.A.>" "this" used_fact "0" ) this[simplified ] \<open>this[simplified ]\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[1]" "<N.A.>" "this" used_fact_in_modifier "0" ) this \<open>this\<close>
  from this[simplified ] 
  obtain a b :: int where  "sqrt 2 = a/b" "coprime a b"
  record_facts ( Drinker thm_sqt_2_irra1 "[1]" "<N.A.>" "Rat_cases" used_fact ) Rat_cases \<open>Rat_cases\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[1]" "<N.A.>" "Rats_def" used_fact ) Rats_def \<open>Rats_def\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[1]" "<N.A.>" "imageE" used_fact ) imageE \<open>imageE\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[1]" "<N.A.>" "normalize_stable" used_fact ) normalize_stable \<open>normalize_stable\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[1]" "<N.A.>" "of_rat_divide" used_fact ) of_rat_divide \<open>of_rat_divide\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[1]" "<N.A.>" "of_rat_of_int_eq" used_fact ) of_rat_of_int_eq \<open>of_rat_of_int_eq\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[1]" "<N.A.>" "quotient_of_Fract" used_fact ) quotient_of_Fract \<open>quotient_of_Fract\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[1]" "<N.A.>" "quotient_of_div" used_fact ) quotient_of_div \<open>quotient_of_div\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[1,-1]" "<N.A.>" "that" ) that \<open>that\<close>
    by (metis Rat_cases Rats_def imageE normalize_stable of_rat_divide of_rat_of_int_eq quotient_of_Fract quotient_of_div)
  record_facts ( Drinker thm_sqt_2_irra1 "[1]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[2]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  then 
  have  "2 = a\<^sup>2 / b\<^sup>2"
  record_facts ( Drinker thm_sqt_2_irra1 "[2]" "<N.A.>" "of_int_power" used_fact ) of_int_power \<open>of_int_power\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[2]" "<N.A.>" "power_divide" used_fact ) power_divide \<open>power_divide\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[2]" "<N.A.>" "real_sqrt_pow2" used_fact ) real_sqrt_pow2 \<open>real_sqrt_pow2\<close>
    by (smt of_int_power power_divide real_sqrt_pow2)
  record_facts ( Drinker thm_sqt_2_irra1 "[2]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[3]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  then 
  have * : "2*b\<^sup>2 = a\<^sup>2"
  proof -
    assume  "2 = a\<^sup>2 / b\<^sup>2"
    record_facts ( Drinker thm_sqt_2_irra1 "[3,0]" "<N.A.>" "this" ) this \<open>this\<close>
    record_facts ( Drinker thm_sqt_2_irra1 "[3,1]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
    then 
    have  "b\<^sup>2 * (2::real) = a\<^sup>2"
    record_facts ( Drinker thm_sqt_2_irra1 "[3,1]" "<N.A.>" "division_ring_divide_zero" used_fact ) division_ring_divide_zero \<open>division_ring_divide_zero\<close>
    record_facts ( Drinker thm_sqt_2_irra1 "[3,1]" "<N.A.>" "nonzero_mult_div_cancel_left" used_fact ) nonzero_mult_div_cancel_left \<open>nonzero_mult_div_cancel_left\<close>
    record_facts ( Drinker thm_sqt_2_irra1 "[3,1]" "<N.A.>" "rel_simps(76)" used_fact ) rel_simps(76) \<open>rel_simps(76)\<close>
    record_facts ( Drinker thm_sqt_2_irra1 "[3,1]" "<N.A.>" "times_divide_eq_right" used_fact ) times_divide_eq_right \<open>times_divide_eq_right\<close>
      by (metis division_ring_divide_zero nonzero_mult_div_cancel_left rel_simps(76) times_divide_eq_right)
    record_facts ( Drinker thm_sqt_2_irra1 "[3,1]" "<N.A.>" "this" ) this \<open>this\<close>
    record_facts ( Drinker thm_sqt_2_irra1 "[3,2]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
    then 
    show  "2 * b\<^sup>2 = a\<^sup>2"
      by linarith
    record_facts ( Drinker thm_sqt_2_irra1 "[3,2]" "<N.A.>" "this" ) this \<open>this\<close>
  qed 
  record_facts ( Drinker thm_sqt_2_irra1 "[3]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[4]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  then 
  have  "even a"
  record_facts ( Drinker thm_sqt_2_irra1 "[4]" "<N.A.>" "dvd_triv_left" used_fact ) dvd_triv_left \<open>dvd_triv_left\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[4]" "<N.A.>" "even_mult_iff" used_fact ) even_mult_iff \<open>even_mult_iff\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[4]" "<N.A.>" "power2_eq_square" used_fact ) power2_eq_square \<open>power2_eq_square\<close>
    by (metis dvd_triv_left even_mult_iff power2_eq_square)
  record_facts ( Drinker thm_sqt_2_irra1 "[4]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[5]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  then 
  obtain c::int where  "a=2*c"
  record_facts ( Drinker thm_sqt_2_irra1 "[5,-1]" "<N.A.>" "that" ) that \<open>that\<close>
    by blast
  record_facts ( Drinker thm_sqt_2_irra1 "[5]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[6]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[6]" "<N.A.>" "*" used_fact ) * \<open>*\<close>
  with * 
  have  "b\<^sup>2 = 2*c\<^sup>2"
    by simp
  record_facts ( Drinker thm_sqt_2_irra1 "[6]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[7]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  then 
  have  "even b"
  record_facts ( Drinker thm_sqt_2_irra1 "[7]" "<N.A.>" "dvd_triv_left" used_fact ) dvd_triv_left \<open>dvd_triv_left\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[7]" "<N.A.>" "even_mult_iff" used_fact ) even_mult_iff \<open>even_mult_iff\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[7]" "<N.A.>" "power2_eq_square" used_fact ) power2_eq_square \<open>power2_eq_square\<close>
    by (metis dvd_triv_left even_mult_iff power2_eq_square)
  record_facts ( Drinker thm_sqt_2_irra1 "[7]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[8]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[8]" "<N.A.>" "<unnamed>" used_fact ) \<open>even a\<close> \<open>\<open>even a\<close>\<close>
  record_facts ( Drinker thm_sqt_2_irra1 "[8]" "<N.A.>" "<unnamed>" used_fact ) \<open>coprime a b\<close> \<open>\<open>coprime a b\<close>\<close>
  with \<open>even a\<close> \<open>coprime a b\<close> 
  show  False
    by auto
  record_facts ( Drinker thm_sqt_2_irra1 "[8]" "<N.A.>" "this" ) this \<open>this\<close>
qed 
record_facts ( Drinker thm_sqt_2_irra1 "[]" "<N.A.>" "sqt_2_irra" ) sqt_2_irra \<open>sqt_2_irra\<close>


lemma filterlim_sequentially_iff_filterlim_real :
 "filterlim f sequentially F \<longleftrightarrow> filterlim (\<lambda>x. real (f x)) at_top F"
  record_all_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[-1]" "<N.A.>" "<unnamed>" )
record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "<N.A.>" "iffI" used_fact ) iffI \<open>iffI\<close>
  apply (rule iffI)
  subgoal this_ 
  record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],1)" "filterlim_compose" used_fact ) filterlim_compose \<open>filterlim_compose\<close>
  record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],1)" "filterlim_real_sequentially" used_fact ) filterlim_real_sequentially \<open>filterlim_real_sequentially\<close>
    using filterlim_compose filterlim_real_sequentially
    by blast
  record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],1)" "this_" used_fact ) this_ \<open>this_\<close>
  subgoal aa premises that
  record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[-1])" "that" ) that \<open>that\<close>
  proof -
    have  "filterlim (\<lambda>x. nat (floor (real (f x)))) sequentially F"
      subgoal this_ 
      record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[0],0)" "conjI" used_fact ) conjI \<open>conjI\<close>
      record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[0],0)" "filterlim_compose" used_fact "1" ) filterlim_compose[OF filterlim_nat_sequentially] \<open>filterlim_compose[OF filterlim_nat_sequentially]\<close>
      record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[0],0)" "filterlim_compose" used_fact_in_modifier "1" ) filterlim_compose \<open>filterlim_compose\<close>
      record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[0],0)" "filterlim_nat_sequentially" used_fact_in_modifier "1" ) filterlim_nat_sequentially \<open>filterlim_nat_sequentially\<close>
      record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[0],0)" "filterlim_compose" used_fact "2" ) filterlim_compose[OF filterlim_floor_sequentially] \<open>filterlim_compose[OF filterlim_floor_sequentially]\<close>
      record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[0],0)" "filterlim_compose" used_fact_in_modifier "2" ) filterlim_compose \<open>filterlim_compose\<close>
      record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[0],0)" "filterlim_floor_sequentially" used_fact_in_modifier "2" ) filterlim_floor_sequentially \<open>filterlim_floor_sequentially\<close>
      record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[0],0)" "that" used_fact ) that \<open>that\<close>
        using conjI
        by (intro filterlim_compose[OF filterlim_nat_sequentially] filterlim_compose[OF filterlim_floor_sequentially] that)
      record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[0],0)" "this_" used_fact ) this_ \<open>this_\<close>
      done
    record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[0])" "this" ) this \<open>this\<close>
    record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[1])" "this" used_fact ) this \<open>this\<close>
    then 
    show  ?thesis
      by simp
    record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2,[1])" "this" ) this \<open>this\<close>
  qed 
  record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "([],2)" "aa" used_fact ) aa \<open>aa\<close>
  done
record_facts ( Drinker thm_filterlim_sequentially_iff_filterlim_real2 "[]" "<N.A.>" "filterlim_sequentially_iff_filterlim_real" ) filterlim_sequentially_iff_filterlim_real \<open>filterlim_sequentially_iff_filterlim_real\<close>


theorem sum_of_odds :
 "(\<Sum>i::nat=0..<n. 2 * i + 1) = n^Suc (Suc 0)" (is "?P n" is "?S n = _")
  record_all_facts ( Drinker thm_sum_of_odds3 "[-1]" "<N.A.>" "<unnamed>" )
proof (induct n )
  show  "?P 0"
    by simp
  record_facts ( Drinker thm_sum_of_odds3 "[0]" "<N.A.>" "this" ) this \<open>this\<close>
next
  fix n
  have  "?S (n + 1) = ?S n + 2 * n + 1"
    by simp
  record_facts ( Drinker thm_sum_of_odds3 "[3]" "<N.A.>" "this" ) this \<open>this\<close>
  also 
  assume  "?S n = n^Suc (Suc 0)"
  record_facts ( Drinker thm_sum_of_odds3 "[4]" "<N.A.>" "this" ) this \<open>this\<close>
  also 
  have  "\<dots> + 2 * n + 1 = (n + 1)^Suc (Suc 0)"
    by simp
  record_facts ( Drinker thm_sum_of_odds3 "[5]" "<N.A.>" "this" ) this \<open>this\<close>
  finally 
  show  "?P (Suc n)"
    by simp
  record_facts ( Drinker thm_sum_of_odds3 "[6]" "<N.A.>" "this" ) this \<open>this\<close>
qed 
record_facts ( Drinker thm_sum_of_odds3 "[]" "<N.A.>" "sum_of_odds" ) sum_of_odds \<open>sum_of_odds\<close>


lemma "1 2 3" :
 "2=3"
  record_all_facts ( Drinker thm_1234 "[-1]" "<N.A.>" "<unnamed>" )
  sorry
record_facts ( Drinker thm_1234 "[]" "<N.A.>" "1 2 3" ) "1 2 3" \<open>"1 2 3"\<close>


thm "1 2 3"


lemma foo1 :
  assumes  A
  shows  "True \<Longrightarrow> False"
  record_all_facts ( Drinker thm_foo16 "[-1]" "<N.A.>" "<unnamed>" )
proof -
  fix a::real
  note [[simproc add: finite_Collect]]
    @phantom
  record_facts ( Drinker thm_foo16 "[1]" "<N.A.>" "this" ) this \<open>this\<close>
  {
    have that : "a=1"
      subgoal this 
        sorry
      record_facts ( Drinker thm_foo16 "[2,0]" "([2,0],0)" "this" used_fact ) this \<open>this\<close>
      sorry
    record_facts ( Drinker thm_foo16 "[2,0]" "<N.A.>" "this" ) this \<open>this\<close>
  }
  record_facts ( Drinker thm_foo16 "[2]" "<N.A.>" "this" ) this \<open>this\<close>
  obtain b::real where  "b=2"
  record_facts ( Drinker thm_foo16 "[3]" "<N.A.>" "that" used_fact ) that \<open>that\<close>
  record_facts ( Drinker thm_foo16 "[3,-1]" "<N.A.>" "that" ) that \<open>that\<close>
    using that
    sorry
  record_facts ( Drinker thm_foo16 "[3]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_foo16 "[4]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  then 
  show  False
    sorry
  record_facts ( Drinker thm_foo16 "[4]" "<N.A.>" "this" ) this \<open>this\<close>
qed 
record_facts ( Drinker thm_foo16 "[]" "<N.A.>" "foo1" ) foo1 \<open>foo1\<close>


lemma fact_in_Reals :
  defines  "x\<equiv>3"
  shows  "fact n \<in> \<real>"
  record_all_facts ( Drinker thm_fact_in_Reals7 "[-1]" "<N.A.>" "<unnamed>" )
record_facts ( Drinker thm_fact_in_Reals7 "[]" "<N.A.>" "conjI" used_fact ) conjI \<open>conjI\<close>
record_facts ( Drinker thm_fact_in_Reals7 "[]" "<N.A.>" "cong" used_fact "1" ) cong[OF refl, of 1 2 plus] \<open>cong[OF refl, of 1 2 plus]\<close>
record_facts ( Drinker thm_fact_in_Reals7 "[]" "<N.A.>" "cong" used_fact_in_modifier "1" ) cong \<open>cong\<close>
record_facts ( Drinker thm_fact_in_Reals7 "[]" "<N.A.>" "refl" used_fact_in_modifier "1" ) refl \<open>refl\<close>
  by (induction n ) (auto simp : conjI cong[OF refl, of 1 2 plus])
record_facts ( Drinker thm_fact_in_Reals7 "[]" "<N.A.>" "fact_in_Reals" ) fact_in_Reals \<open>fact_in_Reals\<close>


lemma foo :
 "\<lbrakk>A=B;B=C;C=D\<rbrakk> \<Longrightarrow> A=D"
  record_all_facts ( Drinker thm_foo8 "[-1]" "<N.A.>" "<unnamed>" )
proof -
  assume  "A=B" "B=C" (is "?L = ?R") "C=D"
  record_facts ( Drinker thm_foo8 "[0]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_foo8 "[1]" "<N.A.>" "<unnamed>" used_fact "0" ) \<open>A=B\<close>[unfolded \<open>B=C\<close>] \<open>\<open>A=B\<close>[unfolded \<open>B=C\<close>]\<close>
  record_facts ( Drinker thm_foo8 "[1]" "<N.A.>" "<unnamed>" used_fact_in_modifier "0" ) \<open>A=B\<close> \<open>\<open>A=B\<close>\<close>
  record_facts ( Drinker thm_foo8 "[1]" "<N.A.>" "<unnamed>" used_fact_in_modifier "0" ) \<open>B=C\<close> \<open>\<open>B=C\<close>\<close>
  record_facts ( Drinker thm_foo8 "[1]" "<N.A.>" "<unnamed>" used_fact ) \<open>C=D\<close> \<open>\<open>C=D\<close>\<close>
  moreover 
  note xx = \<open>A=B\<close>[unfolded \<open>B=C\<close>] \<open>C=D\<close>
    @phantom
  record_facts ( Drinker thm_foo8 "[1]" "<N.A.>" "this" ) this \<open>this\<close>
  ultimately 
  record_facts ( Drinker thm_foo8 "[2]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  show  "A=D"
    by (simp add : tendsto_intros)
  record_facts ( Drinker thm_foo8 "[2]" "<N.A.>" "this" ) this \<open>this\<close>
qed 
record_facts ( Drinker thm_foo8 "[]" "<N.A.>" "foo" ) foo \<open>foo\<close>


lemma de_Morgan :
  assumes  "\<not> (\<forall>x. P x)"
  shows  "\<exists>x. \<not> P x"
  record_all_facts ( Drinker thm_de_Morgan9 "[-1]" "<N.A.>" "<unnamed>" )
record_facts ( Drinker thm_de_Morgan9 "[]" "<N.A.>" "classical" used_fact ) classical \<open>classical\<close>
proof (rule classical)
  assume  "\<nexists>x. \<not> P x"
  record_facts ( Drinker thm_de_Morgan9 "[0]" "<N.A.>" "this" ) this \<open>this\<close>
  have  "\<forall>x. P x"
  proof 
    fix x
    show  "P x"
    record_facts ( Drinker thm_de_Morgan9 "[1,1]" "<N.A.>" "classical" used_fact ) classical \<open>classical\<close>
    proof (rule classical)
      assume  "\<not> P x"
      record_facts ( Drinker thm_de_Morgan9 "[1,1,0]" "<N.A.>" "this" ) this \<open>this\<close>
      record_facts ( Drinker thm_de_Morgan9 "[1,1,1]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
      then 
      have  "\<exists>x. \<not> P x"
        ..
      record_facts ( Drinker thm_de_Morgan9 "[1,1,1]" "<N.A.>" "this" ) this \<open>this\<close>
      record_facts ( Drinker thm_de_Morgan9 "[1,1,2]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
      record_facts ( Drinker thm_de_Morgan9 "[1,1,2]" "<N.A.>" "<unnamed>" used_fact "1" ) \<open>\<nexists>x. \<not> P x\<close>[simplified ] \<open>\<open>\<nexists>x. \<not> P x\<close>[simplified ]\<close>
      record_facts ( Drinker thm_de_Morgan9 "[1,1,2]" "<N.A.>" "<unnamed>" used_fact_in_modifier "1" ) \<open>\<nexists>x. \<not> P x\<close> \<open>\<open>\<nexists>x. \<not> P x\<close>\<close>
      record_facts ( Drinker thm_de_Morgan9 "[1,1,2]" "<N.A.>" "HOL.conjI" used_fact "2" ) HOL.conjI[of True, simplified , OF \<open>\<not> P x\<close>[rule_format]] \<open>HOL.conjI[of True, simplified , OF \<open>\<not> P x\<close>[rule_format]]\<close>
      record_facts ( Drinker thm_de_Morgan9 "[1,1,2]" "<N.A.>" "HOL.conjI" used_fact_in_modifier "2" ) HOL.conjI \<open>HOL.conjI\<close>
      record_facts ( Drinker thm_de_Morgan9 "[1,1,2]" "<N.A.>" "<unnamed>" used_fact_in_modifier "2" ) \<open>\<not> P x\<close> \<open>\<open>\<not> P x\<close>\<close>
      record_facts ( Drinker thm_de_Morgan9 "[1,1,2]" "<N.A.>" "HOL.False_not_True(1,1,1-1)" used_fact ) HOL.False_not_True(1,1,1-1) \<open>HOL.False_not_True(1,1,1-1)\<close>
      with \<open>\<nexists>x. \<not> P x\<close>[simplified ] HOL.conjI[of True, simplified , OF \<open>\<not> P x\<close>[rule_format]] HOL.False_not_True(1,1,1-1) 
      show  ?thesis
      record_facts ( Drinker thm_de_Morgan9 "[1,1,2]" "<N.A.>" "TrueI" used_fact ) TrueI \<open>TrueI\<close>
        using TrueI
        subgoal this 
        record_facts ( Drinker thm_de_Morgan9 "[]" "([1,1,2],1)" "FalseE" used_fact ) FalseE \<open>FalseE\<close>
          by (auto simp : FalseE)
        record_facts ( Drinker thm_de_Morgan9 "[1,1,2]" "([1,1,2],1)" "this" used_fact ) this \<open>this\<close>
        done
      record_facts ( Drinker thm_de_Morgan9 "[1,1,2]" "<N.A.>" "this" ) this \<open>this\<close>
    qed 
    record_facts ( Drinker thm_de_Morgan9 "[1,1]" "<N.A.>" "this" ) this \<open>this\<close>
  qed 
  record_facts ( Drinker thm_de_Morgan9 "[1]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_de_Morgan9 "[2]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  record_facts ( Drinker thm_de_Morgan9 "[2]" "<N.A.>" "<unnamed>" used_fact ) \<open>\<not> (\<forall>x. P x)\<close> \<open>\<open>\<not> (\<forall>x. P x)\<close>\<close>
  with \<open>\<not> (\<forall>x. P x)\<close> 
  show  ?thesis
    by contradiction
  record_facts ( Drinker thm_de_Morgan9 "[2]" "<N.A.>" "this" ) this \<open>this\<close>
qed 
record_facts ( Drinker thm_de_Morgan9 "[]" "<N.A.>" "de_Morgan" ) de_Morgan \<open>de_Morgan\<close>


theorem Drinker's_Principle :
 "\<exists>x. drunk x \<longrightarrow> (\<forall>x. drunk x)"
  record_all_facts ( Drinker thm_Drinker's_Principle10 "[-1]" "<N.A.>" "<unnamed>" )
proof cases
  assume  "\<forall>x. drunk x"
  record_facts ( Drinker thm_Drinker's_Principle10 "[0]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_Drinker's_Principle10 "[1]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  then 
  have  "drunk a \<longrightarrow> (\<forall>x. drunk x)" for a
    ..
  record_facts ( Drinker thm_Drinker's_Principle10 "[1]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_Drinker's_Principle10 "[2]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  then 
  show  ?thesis
    ..
  record_facts ( Drinker thm_Drinker's_Principle10 "[2]" "<N.A.>" "this" ) this \<open>this\<close>
next
  assume  "\<not> (\<forall>x. drunk x)"
  record_facts ( Drinker thm_Drinker's_Principle10 "[4]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_Drinker's_Principle10 "[5]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  then 
  have  "\<exists>x. \<not> drunk x"
  record_facts ( Drinker thm_Drinker's_Principle10 "[5]" "<N.A.>" "de_Morgan" used_fact ) de_Morgan \<open>de_Morgan\<close>
    by (rule de_Morgan)
  record_facts ( Drinker thm_Drinker's_Principle10 "[5]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_Drinker's_Principle10 "[6]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  then 
  obtain a where  "\<not> drunk a"
  record_facts ( Drinker thm_Drinker's_Principle10 "[6,-1]" "<N.A.>" "that" ) that \<open>that\<close>
    ..
  record_facts ( Drinker thm_Drinker's_Principle10 "[6]" "<N.A.>" "this" ) this \<open>this\<close>
  have  "drunk a \<longrightarrow> (\<forall>x. drunk x)"
  proof 
    assume  "drunk a"
    record_facts ( Drinker thm_Drinker's_Principle10 "[7,0]" "<N.A.>" "this" ) this \<open>this\<close>
    record_facts ( Drinker thm_Drinker's_Principle10 "[7,1]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
    record_facts ( Drinker thm_Drinker's_Principle10 "[7,1]" "<N.A.>" "<unnamed>" used_fact ) \<open>\<not> drunk a\<close> \<open>\<open>\<not> drunk a\<close>\<close>
    with \<open>\<not> drunk a\<close> 
    show  "\<forall>x. drunk x"
      by contradiction
    record_facts ( Drinker thm_Drinker's_Principle10 "[7,1]" "<N.A.>" "this" ) this \<open>this\<close>
  qed 
  record_facts ( Drinker thm_Drinker's_Principle10 "[7]" "<N.A.>" "this" ) this \<open>this\<close>
  record_facts ( Drinker thm_Drinker's_Principle10 "[8]" "<N.A.>" "this" used_fact ) this \<open>this\<close>
  then 
  show  ?thesis
    ..
  record_facts ( Drinker thm_Drinker's_Principle10 "[8]" "<N.A.>" "this" ) this \<open>this\<close>
qed 
record_facts ( Drinker thm_Drinker's_Principle10 "[]" "<N.A.>" "Drinker's_Principle" ) Drinker's_Principle \<open>Drinker's_Principle\<close>


end
