theory Common
  imports Main (* "HOL-Eisbach.Eisbach" *)
begin

sledgehammer_params [provers=vampire cvc4 spass z3,timeout=60]

bundle trace = [[simp_trace, linarith_trace, metis_trace, smt_trace]]

lemma wf_compatP: 
  assumes "\<And>a b. R a b \<Longrightarrow> R' (f a) (f b)" "wfP R'"
  shows "wfP R"
proof -
  have A: "\<forall>a b. (a, b) \<in> {(x, y). r x y} \<longrightarrow> (f a, f b) \<in> {(x, y). r' x y}" 
    if "\<And>a b. r a b \<Longrightarrow> r' (f a) (f b)"
    for r :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and f :: "'a \<Rightarrow> 'b" and r'
    using that by blast
  show ?thesis using compat_wf[to_pred,simplified compat_def,OF A,of R R'] assms by blast
qed

lemma set_comp_eq_iff: "({ f x | x . P x } = { g x | x . Q x }) \<longleftrightarrow>
       (\<forall>x. P x \<longrightarrow> (\<exists>y. Q y \<and> f x = g y)) \<and>
       (\<forall>x. Q x \<longrightarrow> (\<exists>y. P y \<and> g x = f y))"
  by blast

(* method solve methods m = (m ; fail)

named_theorems subst 
named_theorems intros
named_theorems elims

method prop_solver declares intros elims subst =
  (assumption |
  (rule intros) | erule elims |
  subst subst | subst (asm) subst |
  (erule notE ; solve \<open>prop_solver\<close> ))+

lemmas [intros] =
  conjI \<comment> \<open>P \<Longrightarrow> Q \<Longrightarrow> P \<and> Q\<close>
  impI \<comment> \<open>(P \<Longrightarrow> Q) \<Longrightarrow> P \<Longrightarrow> Q\<close>
  disjCI \<comment> \<open>(\<not> Q \<Longrightarrow> P) \<Longrightarrow> P \<or> Q\<close>
  iffI \<comment> \<open>(P \<Longrightarrow> Q) \<Longrightarrow> (Q \<Longrightarrow> P) \<Longrightarrow> P \<longleftrightarrow> Q\<close>
  notI \<comment> \<open>(P \<Longrightarrow> False) \<Longrightarrow> \<not> P\<close>

lemmas [elims] =
  impCE \<comment> \<open>P \<longrightarrow> Q \<Longrightarrow> (\<not> P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R\<close>
  conjE \<comment> \<open>P \<and> Q \<Longrightarrow> (P \<Longrightarrow> Q \<Longrightarrow> R) \<Longrightarrow> R\<close>
  disjE \<comment> \<open>P \<or> Q \<Longrightarrow> (P \<Longrightarrow> R) \<Longrightarrow> (Q \<Longrightarrow> R) \<Longrightarrow> R\<close>
*)
lemma inv_into_aux_1: "(inv_into X f) ` (A \<inter> f ` X) =
        ((inv_into X f) ` A) \<inter> X" 
  if A: "A \<subseteq> f ` X" for f :: "'a \<Rightarrow> 'b" 
  using A
  by (simp add: inf_absorb1 inv_into_into subset_eq)

lemma inv_into_aux_2: "g ` (A \<inter> f ` X) =
        (g ` A) \<inter> X" 
  if A:  "\<And>Y. g ` Y = inv_into X f ` (Y \<inter> f ` X) \<union> 
                      {b | x . x \<in> Y \<and> x \<notin> f ` X}"
         "b \<notin> X"
  for g :: "'b \<Rightarrow> 'a" and f :: "'a \<Rightarrow> 'b" and X :: "'a set"
proof -
  have B: "A \<inter> f ` X \<subseteq> f ` X" using A by blast
  note C = inv_into_aux_1[of "A \<inter> f ` X" f X]
  have D: "\<And>Y. Y \<subseteq> f ` X \<Longrightarrow> g ` Y = inv_into X f ` Y"
    using A by auto
  have E: "(g ` Y) \<inter> X = g ` Y" if "Y \<subseteq> f ` X" for Y 
    using that A 
    by (metis (no_types, lifting) D inf.orderE inv_into_aux_1)
  have eq1: "g ` (A \<inter> f ` X) = inv_into X f ` (A \<inter> f ` X)"
    using C D[OF B] E B by (simp ; metis)
  have F: "g ` A \<subseteq> (inv_into X f ` (A \<inter> f ` X)) \<union> {b}"
    using A(1)[of A] A(2) Un_insert_right by blast
  have G: "inv_into X f ` (A \<inter> f ` X) \<subseteq> g ` A"
    using A by blast
  have eq2: "g ` A \<inter> X = inv_into X f ` (A \<inter> f ` X)"
    using F G A(2) C by auto
  show ?thesis 
    using eq1 eq2 by simp      
qed    

lemma someI_bex: "(SOME x. x \<in> A \<and> P x) \<in> A" "P (SOME x. x \<in> A \<and> P x)"
    if "\<exists>a\<in>A. P a" for A :: "'a set" and P
    using someI2_bex[of A P "\<lambda>x. x \<in> A \<and> P x" , simplified,OF that] 
    by simp+

lemma ex_iff_exI:  
  fixes f g P Q
  assumes "\<And>x. P x \<Longrightarrow> Q (f x)" 
          "\<And>x. Q x \<Longrightarrow> P (g x)"
  shows "(\<exists>x. P x) \<longleftrightarrow> (\<exists>x. Q x)"
  using assms by metis  
  
lemma not_image_E:
  assumes "f y \<notin> f ` Y"
  obtains "y \<notin> Y" using assms imageI by metis

lemma image_Diff_subset: "\<lbrakk> Y \<subseteq> X ; f ` X \<inter> f ` Y = {} \<rbrakk> \<Longrightarrow> f ` (X - Y) = f ` X - f ` Y" 
  by blast 

lemma disjointE:
  assumes "A \<inter> B = {}"
  obtains "\<And>x. x \<notin> A \<or> x \<notin> B"
  using assms by blast

lemma iff_conj_I:
  assumes "P \<or> Q \<Longrightarrow> C" 
      "\<lbrakk> P ; C \<rbrakk> \<Longrightarrow> Q" "\<lbrakk> Q ; C \<rbrakk> \<Longrightarrow> P"
  shows "P \<longleftrightarrow> Q"
  using assms by blast

lemma iff_dist: "(P \<Longrightarrow> (Q \<longleftrightarrow> R)) \<Longrightarrow> P \<and> Q \<longleftrightarrow> P \<and> R" for P Q R by blast

lemma permutation_disj_subset:
  assumes "\<forall>x. \<Omega> x \<in> X \<longleftrightarrow> x \<in> X" "\<forall>x. \<Omega> x \<in> Z \<longleftrightarrow> x \<in> Z" "X = Y \<union> Z"  "Y \<inter> X = {}"
  shows "\<And>x. \<Omega> x \<in> Y \<longleftrightarrow> x \<in> Y"
  using assms by simp

lemma neg_iff_D: 
  assumes "(A \<longleftrightarrow> B)"
  shows "\<not> A \<Longrightarrow> \<not> B" "\<not> B \<Longrightarrow> \<not> A" using assms by auto

lemma Collect_by_func_I:
  assumes "\<And>x. P x \<Longrightarrow> Q (G x)"
     "\<And>x. P x \<Longrightarrow> g (G x) = f x"
     "\<And>x. Q x \<Longrightarrow> P (F x)"
     "\<And>x. Q x \<Longrightarrow> f (F x) = g x" 
   shows "{ f x | x . P x } = { g x | x . Q x }"
  apply (rule Collect_eqI ; intro ex_iff_exI[of _ _ G F] ; elim conjE ; hypsubst_thin)
  using assms by metis+


locale equiv_rel =
  fixes P 
  assumes 
    sym[sym]: "P x y \<Longrightarrow> P y x" and
    trans: "\<lbrakk> P x y ; P y z \<rbrakk> \<Longrightarrow> P x z" 

locale closure_rel_P = equiv_rel +
  fixes A
  assumes 
    refl[intro]: "x \<in> A \<Longrightarrow> P x x" and
    closed: "\<lbrakk> P x y ; x \<in> A \<rbrakk> \<Longrightarrow> y \<in> A"
begin

lemma closed_iff: "P x y \<Longrightarrow> x \<in> A \<longleftrightarrow> y \<in> A" using closed sym by metis

end

lemma closure_rel_empty[intro!,simp]: 
  assumes "equiv_rel P"
  shows "closure_rel_P P {}" 
  apply (intro_locales ; (intro assms)?)
  by (unfold_locales ; simp)
   

lemma closure_rel_combs: 
  assumes "closure_rel_P P X" "closure_rel_P P Y"
  shows "closure_rel_P P (X \<inter> Y)" (is ?goal1)
        "closure_rel_P P (X \<union> Y)" (is ?goal2)
        "closure_rel_P P (X - Y)" (is ?goal3)
proof -
  interpret X: closure_rel_P P X using assms by simp
  interpret Y: closure_rel_P P Y using assms by simp
  show ?goal1 by (metis Int_iff X.closed X.equiv_rel_axioms X.refl Y.closed closure_rel_P.intro closure_rel_P_axioms.intro)
  show ?goal2 by (metis Un_iff X.closed_iff X.equiv_rel_axioms X.refl Y.closed Y.refl closure_rel_P.intro closure_rel_P_axioms.intro)
  show ?goal3 by (metis DiffD1 DiffD2 DiffI X.closed X.equiv_rel_axioms X.refl Y.closed_iff closure_rel_P.intro closure_rel_P_axioms.intro)
qed

end
