theory Universals
  imports Common
begin

record 'u universal_structure =
  universals :: "'u set" ("\<U>\<index>") 
  characterized_by :: "'u \<Rightarrow> 'u \<Rightarrow> bool" ("char'_by\<index>") 
  moment_subsumption :: "'u \<Rightarrow> 'u \<Rightarrow> bool" (infix "\<preceq>\<^sub>m\<index>" 75)

(* UNUSED lemma universal_structure_eq_I:
  fixes X :: "'u universal_structure" and
        Y :: "'u universal_structure" 
  assumes "\<U>\<^bsub>X\<^esub> = \<U>\<^bsub>Y\<^esub>"
          "char_by\<^bsub>X\<^esub> = char_by\<^bsub>Y\<^esub>"
          "(\<preceq>\<^sub>m\<^bsub>X\<^esub>) = (\<preceq>\<^sub>m\<^bsub>Y\<^esub>)"          
        shows "X = Y"
  using assms
  by simp *)
  

definition moment_universals  ("\<U>\<^sub>m\<index>") where
  "\<U>\<^sub>m \<equiv> { U | U U' . char_by U' U }"
  for US (structure)

definition substantial_universals  ("\<U>\<^sub>s\<index>") where
  "\<U>\<^sub>s \<equiv> { U . U \<in> \<U> \<and> (\<forall>U' . \<not> char_by U' U) }"
  for US (structure) 

lemma  subst_moment_univs_disj: "\<U>\<^sub>s \<inter> \<U>\<^sub>m = {}" 
  for US (structure) 
  by (auto simp: substantial_universals_def moment_universals_def)

lemma  subst_moment_univs_disj_2: "\<lbrakk> x \<in> \<U>\<^sub>s ; x \<in> \<U>\<^sub>m \<rbrakk> \<Longrightarrow> False" 
  for US (structure) 
  using subst_moment_univs_disj
  by fastforce


definition substantial_subsumption (infix "\<preceq>\<^sub>s\<index>" 75) where
  "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2 \<equiv> U\<^sub>1 \<in> \<U>\<^sub>s \<and> U\<^sub>2 \<in> \<U>\<^sub>s \<and>
      (\<forall>u\<^sub>2. char_by U\<^sub>2 u\<^sub>2 \<longrightarrow> (\<exists>u\<^sub>1. char_by U\<^sub>1 u\<^sub>1 \<and> u\<^sub>1 \<preceq>\<^sub>m u\<^sub>2))"
  for US (structure)

definition subsumption (infix "\<preceq>\<index>" 75) where
  "U\<^sub>1 \<preceq> U\<^sub>2 \<equiv> U\<^sub>1 \<in> \<U>\<^sub>m \<and> U\<^sub>2 \<in> \<U>\<^sub>m \<and> U\<^sub>1 \<preceq>\<^sub>m U\<^sub>2 \<or>
             U\<^sub>1 \<in> \<U>\<^sub>s \<and> U\<^sub>2 \<in> \<U>\<^sub>s \<and> U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2"
  for US (structure)

definition top_subst_univ ("\<top>\<^sub>s\<index>") where
  "\<top>\<^sub>s \<equiv> THE U. \<forall>U' \<in> \<U>\<^sub>s. U' \<preceq>\<^sub>s U"
  for US (structure)

definition characterizing_set ("char'_set\<index>") 
   where "char_set U \<equiv> { u . char_by U u }"
   for US (structure)

lemma char_set_iff[simp]: "u \<in> char_set U \<longleftrightarrow> char_by U u" 
  for US (structure)
  by (auto simp: characterizing_set_def)

lemma char_set_D: "u \<in> char_set U \<Longrightarrow> char_by U u" 
  for US (structure)
  by (auto simp: characterizing_set_def)

lemma char_set_E[elim!]: 
  fixes US (structure)
  assumes "u \<in> char_set U"  
  obtains "char_by U u" 
  using assms by (auto simp: characterizing_set_def)

lemma char_set_I[intro!]: "char_by U u \<Longrightarrow> u \<in> char_set U" 
  for US (structure)
  by (auto simp: characterizing_set_def)

lemma substantial_subsumption_I[intro!]:
  fixes US (structure)
  assumes "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s" "\<forall>u. char_by U\<^sub>2 u \<longrightarrow> (\<exists>u'. char_by U\<^sub>1 u' \<and> u' \<preceq>\<^sub>m u)"
  shows "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2"
  by (auto simp: substantial_subsumption_def assms)  

lemma substantial_subsumption_E[elim!]:
  fixes US (structure)
  assumes "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2"
  obtains "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s" "\<forall>u. char_by U\<^sub>2 u \<longrightarrow> (\<exists>u'. char_by U\<^sub>1 u' \<and> u' \<preceq>\<^sub>m u)"
  using assms by (auto simp: substantial_subsumption_def)  


locale universal_structure =
  fixes US :: "'u universal_structure" (structure)
  assumes
    finite_univs: "finite \<U>" and 
    characterized_by_scope: "char_by Us Um \<Longrightarrow> Us \<in> \<U>\<^sub>s \<and> Um \<in> \<U>"  and
    characterization_respects_subsumption: "\<lbrakk> char_by U u\<^sub>1 ; u\<^sub>1 \<preceq>\<^sub>m u\<^sub>2 \<rbrakk> \<Longrightarrow> char_by U u\<^sub>2" and
    unique_characterization: "\<forall>U\<^sub>1 U\<^sub>2. U\<^sub>1 \<in> \<U>\<^sub>s \<and> U\<^sub>2 \<in> \<U>\<^sub>s \<and> (\<forall>u. char_by U\<^sub>1 u \<longleftrightarrow> char_by U\<^sub>2 u) \<longrightarrow> U\<^sub>1 = U\<^sub>2" and
    every_moment_univ_characterizes: "\<forall>u \<in> \<U>\<^sub>m. \<exists>U \<in> \<U>\<^sub>s. char_by U u" and
    no_moment_univ_is_characterized: "\<forall>u u'. u \<in> \<U>\<^sub>m \<longrightarrow> \<not> char_by u u'" and
    unique_characterization_introduction:
        "\<forall>u U\<^sub>1 U\<^sub>2. char_by U\<^sub>1 u \<and> char_by U\<^sub>2 u \<longrightarrow> (\<exists>U. char_by U u \<and> U\<^sub>1 \<preceq>\<^sub>s U \<and> U\<^sub>2 \<preceq>\<^sub>s U)" and    
    top_substantial_ex: "\<exists>U \<in> \<U>\<^sub>s. \<forall>U' \<in> \<U>\<^sub>s. U' \<preceq>\<^sub>s U"  and
    moment_subsumes_scope: "U \<preceq>\<^sub>m U' \<Longrightarrow> U \<in> \<U>\<^sub>m \<and> U' \<in> \<U>\<^sub>m" and
    moment_subsumes_refl: "U \<in> \<U>\<^sub>m \<Longrightarrow> U \<preceq>\<^sub>m U" and
    moment_subsumes_antisym: "\<lbrakk> U \<preceq>\<^sub>m U' ; U' \<preceq>\<^sub>m U \<rbrakk> \<Longrightarrow> U = U'" and
    moment_subsumes_trans: "\<lbrakk> U\<^sub>1 \<preceq>\<^sub>m U\<^sub>2 ; U\<^sub>2 \<preceq>\<^sub>m U\<^sub>3 \<rbrakk> \<Longrightarrow> U\<^sub>1 \<preceq>\<^sub>m U\<^sub>3" 

begin

lemma characterized_by_scope_E: 
  assumes "char_by Us Um"
  obtains "Us \<in> \<U>\<^sub>s" "Um \<in> \<U>\<^sub>m" 
  using characterized_by_scope assms 
        moment_universals_def 
  by fastforce

lemma characterized_by_scope_D: 
  assumes "char_by Us Um"
  shows "Us \<in> \<U>\<^sub>s" "Um \<in> \<U>\<^sub>m" 
  using characterized_by_scope_E assms by metis+

lemma universals_eq_un: "\<U> = \<U>\<^sub>m \<union> \<U>\<^sub>s"    
  by (auto simp: substantial_universals_def
        moment_universals_def characterized_by_scope)

lemma universal_exhaust[cases set]:
  assumes "u \<in> \<U>"
  obtains (moment) "u \<in> \<U>\<^sub>m" "u \<notin> \<U>\<^sub>s" |
          (substantial) "u \<in> \<U>\<^sub>s" "u \<notin> \<U>\<^sub>m" 
  using assms subst_moment_univs_disj_2 universals_eq_un by fastforce

lemma universal_I: "u \<in> \<U>\<^sub>m \<or> u \<in> \<U>\<^sub>s \<Longrightarrow> u \<in> \<U>"  
  by (simp add: universals_eq_un) 

lemma subst_subsumes_by_char_set:
  assumes "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s"
  shows "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2 \<longleftrightarrow> char_set U\<^sub>2 \<subseteq> char_set U\<^sub>1" 
proof (intro iffI subsetI ; (simp add: subset_iff)?)
  fix u
  assume as: "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2" "char_by U\<^sub>2 u"
  obtain u\<^sub>1 where A: "char_by U\<^sub>1 u\<^sub>1" "u\<^sub>1 \<preceq>\<^sub>m u"
    using assms as substantial_subsumption_def by metis      
  show "char_by U\<^sub>1 u"
    using characterization_respects_subsumption A by simp
next
  assume "\<forall>u. char_by U\<^sub>2 u \<longrightarrow> char_by U\<^sub>1 u"
  note as = this[rule_format]
  show "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2"
    using moment_subsumes_refl characterized_by_scope_E as
      substantial_subsumption_def assms 
    by metis
qed

lemma subsumesI[intro]:
  assumes "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2 \<or> U\<^sub>1 \<preceq>\<^sub>m U\<^sub>2" 
  shows "U\<^sub>1 \<preceq> U\<^sub>2"
  using subsumption_def moment_subsumes_scope substantial_subsumption_def
      assms by metis

lemma subsumesI_S[intro]:
  assumes "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2" 
  shows "U\<^sub>1 \<preceq> U\<^sub>2"
  using subsumption_def moment_subsumes_scope substantial_subsumption_def
      assms by metis

lemma subsumesI_M[intro]:
  assumes "U\<^sub>1 \<preceq>\<^sub>m U\<^sub>2" 
  shows "U\<^sub>1 \<preceq> U\<^sub>2"
  using subsumption_def moment_subsumes_scope 
      assms by metis


lemma subst_univ_eq_char_set:
  assumes "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s" "char_set U\<^sub>1 = char_set U\<^sub>2"
  shows "U\<^sub>1 = U\<^sub>2"
  using assms unique_characterization char_set_iff 
  by auto

lemma substantial_subsumption_scope:
  assumes "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2"
  shows "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s"
  using assms substantial_subsumption_E by auto

lemma substantial_subsumption_antisym:
  assumes "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2" "U\<^sub>2 \<preceq>\<^sub>s U\<^sub>1"
  shows "U\<^sub>1 = U\<^sub>2"
  supply A = substantial_subsumption_scope[OF assms(1)]
  supply B = subst_subsumes_by_char_set[THEN iffD1, OF A assms(1)] 
            subst_subsumes_by_char_set[THEN iffD1, OF A(2,1) assms(2)]
  supply C = equalityI[OF B]
  using C 
  by (simp add: A(1) A(2) subst_univ_eq_char_set)

(* UNUSED lemma substantial_subsumption_trans:
  assumes "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2" "U\<^sub>2 \<preceq>\<^sub>s U\<^sub>3"
  shows "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>3"
  supply A = assms[THEN substantial_subsumption_E]
  apply (intro substantial_subsumption_I ; rule A(1) ; rule A(2) ; simp)  
  using characterization_respects_subsumption by blast *)
  
(* UNUSED lemma substantial_subsumption_refl:  
  assumes "U \<in> \<U>\<^sub>s"
  shows "U \<preceq>\<^sub>s U"
  by (intro subst_subsumes_by_char_set[THEN iffD2] assms ; simp) *)

(* UNUSED lemma moment_char_set_empty:  "u \<in> \<U>\<^sub>m \<Longrightarrow> char_set u = {}"  
  by (simp add: characterizing_set_def no_moment_univ_is_characterized) *)
  
lemma moment_univs_are_univs: "\<U>\<^sub>m \<subseteq> \<U>"  
  using characterized_by_scope
        every_moment_univ_characterizes 
  by auto


lemma substantial_univs_are_univs: "\<U>\<^sub>s \<subseteq> \<U>"  
  by (auto simp: substantial_universals_def)

lemma subsumesE[elim]:
  assumes "U\<^sub>1 \<preceq> U\<^sub>2" 
  obtains (are_substantials) "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2" |
          (are_moments) "U\<^sub>1 \<preceq>\<^sub>m U\<^sub>2"
  using subsumption_def moment_subsumes_scope assms 
  by metis

lemma at_least_one_subst_univ: "\<U>\<^sub>s \<noteq> {}" 
  using top_substantial_ex by auto


lemma top_ex1: "\<exists>!U. \<forall>U'\<in>\<U>\<^sub>s. U' \<preceq>\<^sub>s U"
  apply (intro ex_ex1I)
proof -
  show "\<exists>U. \<forall>U'\<in>\<U>\<^sub>s. U' \<preceq>\<^sub>s U" 
    using top_substantial_ex by metis  
  fix U\<^sub>1 U\<^sub>2
  assume as: "\<forall>U'\<in>\<U>\<^sub>s. U' \<preceq>\<^sub>s U\<^sub>1" "\<forall>U'\<in>\<U>\<^sub>s. U' \<preceq>\<^sub>s U\<^sub>2"
  then obtain A[simp,intro!]: "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s"
    using at_least_one_subst_univ
    by blast
  { fix U'
    assume as2: "U' \<in> \<U>\<^sub>s"
    obtain B: "U' \<preceq>\<^sub>s U\<^sub>1" "U' \<preceq>\<^sub>s U\<^sub>2" using as as2 by metis
    then obtain D:"char_set U\<^sub>1 \<subseteq> char_set U'" "char_set U\<^sub>2 \<subseteq> char_set U'"
      using subst_subsumes_by_char_set A as2 by metis }
  note R = this(1)[OF A(2)] this(2)[OF A(1)]  
  show "U\<^sub>1 = U\<^sub>2"
    by (intro subst_univ_eq_char_set A equalityI R)
qed

lemma subsumes_disjointD: 
  "\<lbrakk> U \<preceq>\<^sub>s U\<^sub>1 ; U \<preceq>\<^sub>m U\<^sub>2 \<rbrakk> \<Longrightarrow> False"  
  "\<lbrakk> U \<preceq>\<^sub>s U\<^sub>1 ; U\<^sub>2 \<preceq>\<^sub>m U \<rbrakk> \<Longrightarrow> False"
  by (meson moment_subsumes_scope subst_moment_univs_disj_2 substantial_subsumption_def)+

(* UNUSED lemma top_ex1_2: "\<exists>!U. \<forall>U'\<in>\<U>\<^sub>s. U' \<preceq> U"
  using top_ex1  
  by (metis subsumesE subsumesI subsumes_disjointD(1)) *)

lemma top_eq:
  assumes "\<And>U'. U' \<in> \<U>\<^sub>s \<Longrightarrow> U' \<preceq> U"
  shows "\<top>\<^sub>s = U"
  apply (simp only: top_subst_univ_def ; intro the1_equality top_ex1)
   by (meson moment_subsumes_scope subst_moment_univs_disj_2 subsumesE assms)

lemma top_char_set:
  assumes "U \<in> \<U>\<^sub>s" "char_set U = {}"
  shows "\<top>\<^sub>s = U"
  apply (intro top_eq)
  using assms by blast

lemma top_susbtantial_univ[intro!,simp]: "\<top>\<^sub>s \<in> \<U>\<^sub>s" 
  apply (simp add: top_subst_univ_def ; rule the1I2; (intro top_ex1)?)  
  using top_substantial_ex by blast

lemma subst_universal_iff: "u \<in> \<U>\<^sub>s \<longleftrightarrow> u = \<top>\<^sub>s \<or> (\<exists>u'. char_by u u')"
proof (cases "u \<in> \<U>\<^sub>s")
  assume B: "u \<in> \<U>\<^sub>s"
  have B1: "u = \<top>\<^sub>s \<or> (\<exists>u'. char_by u u')"
  proof (intro disjCI ; simp)
    assume "\<forall>U. \<not> char_by u U"
    then have C: "False" if "char_by u U" for U 
      using that by simp
    then have "char_set u = {}" by blast 
    then show "u = \<top>\<^sub>s"  using B top_char_set by auto
  qed
  then show ?thesis using B by metis
next
  assume B: "u \<notin> \<U>\<^sub>s"
  then show ?thesis 
    apply simp
    by (metis characterized_by_scope subsumesI top_eq top_substantial_ex)
qed

lemma moment_universal_iff: "u \<in> \<U>\<^sub>m \<longleftrightarrow> (\<exists>u'. char_by u' u)"
  using every_moment_univ_characterizes universal_I   
        characterized_by_scope_E by auto

(* UNUSED lemma universal_iff: "u \<in> \<U> \<longleftrightarrow> u = \<top>\<^sub>s \<or> (\<exists>u'. char_by u u') \<or> (\<exists>u'. char_by u' u)"
  using universal_exhaust subst_universal_iff moment_universal_iff
        universal_I by metis *)

lemma finite_subst_univs[intro!]: "finite \<U>\<^sub>s" 
  using finite_univs finite_subset substantial_univs_are_univs by blast

(* UNUSED lemma finite_moment_univs[intro!]: "finite \<U>\<^sub>m" 
  using finite_univs finite_subset moment_univs_are_univs by blast *)

lemma subsumes_scope: 
  assumes "U \<preceq> U'"
  obtains (are_substantials) "U \<in> \<U>\<^sub>s" "U' \<in> \<U>\<^sub>s" |
          (are_moments) "U \<in> \<U>\<^sub>m" "U' \<in> \<U>\<^sub>m"
  using assms every_moment_univ_characterizes characterized_by_scope 
  by (meson subsumption_def)


lemma universals_case[cases set]:
  assumes "U \<in> \<U>"
  obtains (is_a_substantial) "U \<in> \<U>\<^sub>s" |
          (is_a_moment) "U \<in> \<U>\<^sub>m"
  using moment_universals_def substantial_universals_def characterized_by_scope assms 
  by fastforce



lemma subst_subsumes_refl: 
  assumes "U \<in> \<U>\<^sub>s"
  shows "U \<preceq>\<^sub>s U" 
    apply (clarsimp simp: substantial_subsumption_def assms)
    subgoal for u\<^sub>2
      apply (intro exI[of _ u\<^sub>2])
      using moment_subsumes_refl characterized_by_scope_E by metis 
    done

lemma subst_subsumes_antisym: 
  assumes "U \<preceq>\<^sub>s U'" "U' \<preceq>\<^sub>s U" 
  shows "U = U'" 
proof -
  obtain A: "U \<in> \<U>\<^sub>s" "U' \<in> \<U>\<^sub>s" using assms by auto    
  then show ?thesis
    using assms apply (simp add: subst_subsumes_by_char_set A)
    apply (intro unique_characterization[rule_format,of U U',simplified char_set_iff[symmetric] A,
          simplified])
    by (auto simp add: characterizing_set_def)
qed  

lemma subst_subsumes_trans: 
  assumes "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2" "U\<^sub>2 \<preceq>\<^sub>s U\<^sub>3"
  shows "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>3" 
proof -
  obtain as: "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s" "U\<^sub>3 \<in> \<U>\<^sub>s" using assms by auto
  then show "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>3"
    using subst_subsumes_by_char_set assms by blast        
qed


lemma subsumes_refl: 
  assumes "U \<in> \<U>"
  shows "U \<preceq> U" 
  using assms apply (cases U ; intro subsumesI)
  subgoal by (intro disjI1 ; clarsimp simp: subst_subsumes_refl)
  using moment_subsumes_refl by simp


(* UNUSED lemma subsumes_antisym: 
  assumes "U \<preceq> U'" "U' \<preceq> U" 
  shows "U = U'" 
proof -
  consider (c1) "U \<preceq>\<^sub>s U'" "U' \<preceq>\<^sub>s U" |
           (c2) "U \<preceq>\<^sub>m U'" "U' \<preceq>\<^sub>m U" 
    using assms 
    by (meson subsumesE subsumes_disjointD(2)) 
  then show ?thesis
    using moment_subsumes_antisym subst_subsumes_antisym by metis
qed *)



(* UNUSED lemma subsumes_trans: 
  assumes "U\<^sub>1 \<preceq> U\<^sub>2" "U\<^sub>2 \<preceq> U\<^sub>3"
  shows "U\<^sub>1 \<preceq> U\<^sub>3" 
proof -
  consider 
      (c1) "U\<^sub>1 \<preceq>\<^sub>m U\<^sub>2" "U\<^sub>2 \<preceq>\<^sub>m U\<^sub>3" "U\<^sub>1 \<in> \<U>\<^sub>m" "U\<^sub>2 \<in> \<U>\<^sub>m" "U\<^sub>3 \<in> \<U>\<^sub>m" |
      (c2) "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2" "U\<^sub>2 \<preceq>\<^sub>s U\<^sub>3" "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s" "U\<^sub>3 \<in> \<U>\<^sub>s"
    using assms 
    by (meson subst_moment_univs_disj_2 subsumption_def)
  then show ?thesis
  proof (cases , (metis moment_subsumes_trans subsumesI)?)
    assume as: "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2" "U\<^sub>2 \<preceq>\<^sub>s U\<^sub>3" "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s" "U\<^sub>3 \<in> \<U>\<^sub>s"
    then have "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>3"
      using subst_subsumes_by_char_set by blast      
    then show "U\<^sub>1 \<preceq> U\<^sub>3" by auto
  qed
qed *)


lemma top_I:
  assumes "\<And>U. \<forall>U' \<in> \<U>\<^sub>s. U' \<preceq> U \<Longrightarrow> P U"
  shows "P \<top>\<^sub>s"
  apply (simp add: top_subst_univ_def ; rule the1I2 ; (intro top_ex1)? )
  using assms by blast

lemma top_subsumes: "U \<in> \<U>\<^sub>s \<Longrightarrow> U \<preceq> \<top>\<^sub>s" using top_I by blast



(* UNUSED lemma top_subst_univ: "\<top>\<^sub>s \<in> \<U>\<^sub>s" 
  using top_I at_least_one_subst_univ 
  by (metis disjoint_iff_not_equal ex_in_conv subst_moment_univs_disj subsumes_scope) *)

lemma unique_introduction_2:
  assumes "u \<in> \<U>\<^sub>m"
  shows "\<exists>!U. char_by U u \<and> (\<forall>U'. char_by U' u \<longrightarrow> U' \<preceq>\<^sub>s U)" (is "\<exists>!U. ?P U")
proof (intro ex_ex1I)
  show "\<exists>U. char_by U u \<and> (\<forall>U'. char_by U' u \<longrightarrow> U' \<preceq>\<^sub>s U)"
  proof (rule ccontr ; simp)
    assume as: "\<forall>U. char_by U u \<longrightarrow> (\<exists>U'. char_by U' u \<and> \<not> U' \<preceq>\<^sub>s U)"
    then have A: "P" if "char_by U u" "\<And>U'. \<lbrakk> char_by U' u ; \<not> U' \<preceq>\<^sub>s U \<rbrakk> \<Longrightarrow> P" for U P
      using that by auto
    define f where "f U \<equiv> SOME U'. char_by U' u \<and> \<not> U' \<preceq>\<^sub>s U" (is "f U \<equiv> SOME U'. ?P U U'") for U
    have f: "char_by (f U) u" if "char_by U u" for U             
      apply (simp add: f_def)
      apply (intro someI_ex[of "?P U",THEN conjunct1])
       using A[OF that] by metis
    have f_2: "\<not> f U \<preceq>\<^sub>s U" if "char_by U u" for U
      apply (simp add: f_def)
      apply (intro someI_ex[of "?P U",THEN conjunct2])
      using A[OF that] by metis
    define g where "g U \<equiv> SOME U'. char_by U' u \<and> U \<preceq>\<^sub>s U' \<and> f U \<preceq>\<^sub>s U'" (is "g U \<equiv> SOME U'. ?P U U'") for U
    have g_E: "P" 
      if as[simp,intro!]: "char_by U u" and P: "\<lbrakk> char_by (g U) u ; U \<preceq>\<^sub>s g U ; f U \<preceq>\<^sub>s g U ; U \<noteq> g U \<rbrakk> \<Longrightarrow> P"
      for U P
    proof -
     have g_1: "U \<preceq>\<^sub>s g U" 
        apply (simp add: g_def)      
        apply (intro someI_ex[of "?P U", THEN conjunct2,THEN conjunct1])
        using f f_2 unique_characterization_introduction[rule_format,of U u "f U"] as by metis
      have g_2: "char_by (g U) u"
        apply (simp add: g_def)      
        using someI_ex[of "?P U", THEN conjunct1]
        using f f_2 unique_characterization_introduction[rule_format,of U u "f U"] as by metis
      have g_3: "f U \<preceq>\<^sub>s g U"    
        apply (simp add: g_def)
        apply (intro someI_ex[of "?P U", THEN conjunct2, THEN conjunct2])
        using f f_2 unique_characterization_introduction[rule_format,of U u "f U"] as by metis  
      have g_4: "U \<noteq> g U" 
        using g_1 g_3 f f_2 as by fastforce    
      show P using g_1 g_2 g_3 g_4 P by blast 
    qed   
    have f1: "char_by (g U) u" if "char_by U u" for U using that g_E by metis
    have f2: "(g ^^ (Suc n)) x = g ((g ^^ n) x)" for n x by simp
    have f3: "U \<preceq>\<^sub>s g U" if "char_by U u" for U using that g_E by metis
    have f4: "U \<noteq> g U" if "char_by U u" for U using that g_E by metis
    have g_n_char_by: "char_by ((g ^^ (Suc n)) x) u" if aas: "char_by x u" for x n
      apply (induct n)
      subgoal using f1 aas by simp
      subgoal premises P for n
        apply (subst f2)
        by (intro f1 P)
      done
    have g_n_char_by': "char_by ((g ^^ n) x) u" if aas: "char_by x u" for x n
      apply (induct n)
      subgoal using f1 aas by simp
      subgoal premises P for n
        apply (subst f2)
        by (intro f1 P)
      done
    have g_n_subs: "x \<preceq>\<^sub>s ((g ^^ (Suc n)) x)" if aas: "char_by x u" for x n
      apply (induct n)
      subgoal using f3 aas by (simp ; metis)
      using subst_subsumes_trans f3 g_n_char_by aas f2 by metis
    have g_n_diff: "(g ^^ (Suc n)) x \<noteq> x" if aas: "char_by x u" for x n
      apply (induct n)
      subgoal  by (rule g_E[OF aas] ; simp)
    proof
      fix n
      assume aas2: "(g ^^ Suc n) x \<noteq> x" "(g ^^ Suc (Suc n)) x = x"
      have A: "x \<preceq>\<^sub>s (g ^^ Suc n) x" using aas g_n_subs by auto
      have "(g ^^ Suc n) x \<preceq>\<^sub>s (g ^^ Suc (Suc n)) x"                
        by (subst f2[of  "Suc n"] ; intro f3 g_n_char_by aas)
      then have "(g ^^ Suc n) x \<preceq>\<^sub>s x" using aas2(2) by simp
      then have "(g ^^ Suc n) x = x" using A subst_subsumes_antisym by simp    
      then show False using aas2(1) by simp
    qed
    
    define uChar where "uChar \<equiv> { U . char_by U u }"
    have uChar_ne: "uChar \<noteq> {}" using every_moment_univ_characterizes assms by (auto simp: uChar_def)
    have uChar_g_closed: "g x \<in> uChar" if "x \<in> uChar" for x
      using that g_E by (auto simp: uChar_def)        
    
    define G where "G x \<equiv> { (g^^n) x | n . n \<in> (UNIV :: nat set)  }" for x
    have G_ins: "G x = insert x { (g^^(Suc n)) x | n . n \<in> (UNIV :: nat set)  }" for x
      apply (auto simp: G_def)
      subgoal premises P for n
        using P apply (induct n ; simp)
        by blast
      subgoal by (intro exI[of _ 0] ; simp)
      subgoal for n by (intro exI[of _ "Suc n"] ; simp)
      done      
    have "0 < n \<Longrightarrow> (\<And>n. P (Suc n)) \<Longrightarrow> P n" for P and n
      by (metis Suc_pred')
    note Suc_pred'
    have G_subset_uChar: "G x \<subseteq> uChar" if "char_by x u" for x
      apply (simp add: G_ins ; auto)
      subgoal G1 using that uChar_def by auto
      subgoal for n
        apply (simp only: f2[symmetric]  uChar_def mem_Collect_eq)
        by (intro g_n_char_by that)
      done
    have uChar_subset_Us: "uChar \<subseteq> \<U>\<^sub>s" 
      apply (auto simp: uChar_def)
      using characterized_by_scope_E by blast
    then have uChar_finite: "finite uChar" using finite_subst_univs finite_subset by auto
    define G_idx where "G_idx x n \<equiv> (g ^^ n) x" for n x
    have G_idx_plus: "G_idx x (n + m) = G_idx ((g ^^ n) x) m" for x n m
      apply (auto simp: G_idx_def) 
      by (metis add.commute comp_eq_dest_lhs funpow_add)     
    have G_idx_inj: "inj (G_idx x)" if "char_by x u" for x
    proof (intro injI ; rule ccontr)
      fix y z
      assume Z: "G_idx x y = G_idx x z" "y \<noteq> z"
      consider (c1) m where "y = Suc m + z"   |
               (c2) m where "z = Suc m + y"
        using Z(2)
        by (metis add.commute add_Suc_right less_imp_Suc_add linorder_neqE_nat) 
      then show False
      proof (cases)
        case c1
        have "((g ^^ Suc m) ((g ^^ z) x)) = (g ^^ z) x"
          using c1 by (metis G_idx_def G_idx_plus Z(1) add.commute)
        then show ?thesis using g_n_diff g_n_char_by' that by metis
      next
        case c2
        have "((g ^^ Suc m) ((g ^^ y) x)) = (g ^^ y) x"
          using c2 by (metis G_idx_def G_idx_plus Z(1) add.commute)
        then show ?thesis using g_n_diff g_n_char_by' that by metis
      qed
    qed
    have "G_idx x ` UNIV = G x" if "char_by x u" for x
      using G_def G_idx_def by auto
    then have G_idx_bij: "bij_betw (G_idx x) UNIV (G x)" if "char_by x u" for x
      using G_idx_inj that by (simp add: bij_betw_imageI) 
    have "infinite (UNIV :: nat set)" by simp
    then have W1: "infinite (G x)" if "char_by x u" for x
      using G_idx_bij[OF that] bij_betw_finite by blast
    have W2: "finite (G x)" if "char_by x u" for x
      using uChar_finite G_subset_uChar that finite_subset by metis
    obtain x where "char_by x u" using assms every_moment_univ_characterizes by auto
    then show False using W1 W2 by simp
  qed
  fix U\<^sub>1 U\<^sub>2
  assume "char_by U\<^sub>1 u \<and> (\<forall>U'. char_by U' u \<longrightarrow> U' \<preceq>\<^sub>s U\<^sub>1)" "char_by U\<^sub>2 u \<and> (\<forall>U'. char_by U' u \<longrightarrow> U' \<preceq>\<^sub>s U\<^sub>2)"  
  then show "U\<^sub>1 = U\<^sub>2"
    using assms by (simp add: subst_subsumes_antisym)    
qed



definition int_univ :: "'u \<Rightarrow> 'u" where
  "int_univ u \<equiv> THE U. char_by U u \<and> (\<forall>U'. char_by U' u \<longrightarrow> U' \<preceq>\<^sub>s U)" 

(* UNUSED lemma init_univ_eq:
  assumes "char_by U u" "\<And>U'. char_by U' u \<Longrightarrow> U' \<preceq>\<^sub>s U"
  shows "int_univ u = U"
  apply (simp only: int_univ_def ; intro the1_equality unique_introduction_2 conjI assms(1) ; clarify?)
  using assms characterized_by_scope_E[OF assms(1)] by metis+ *)


lemma init_univ_I:
  assumes "u \<in> \<U>\<^sub>m"
    "\<And>U. \<lbrakk> char_by U u ; \<And>U'. char_by U' u \<Longrightarrow> U' \<preceq>\<^sub>s U \<rbrakk> \<Longrightarrow> P U"
  shows "P (int_univ u)"
  apply (simp add: int_univ_def ; rule the1I2 , intro unique_introduction_2 assms(1) , elim conjE)
  subgoal premises Q for U
    by (metis assms (2) Q)
  done

(* UNUSED lemma init_univ_char_by[intro!]:
  assumes "u \<in> \<U>\<^sub>m"    
  shows "char_by (int_univ u) u" 
  by (rule init_univ_I[OF assms] ; simp)+ *)

(* UNUSED lemma init_univ_subsumes[intro!]: 
  assumes "char_by U u" 
  shows "U \<preceq>\<^sub>s (int_univ u)"
  apply (rule init_univ_I )
  subgoal using assms characterized_by_scope_E by metis
  using assms by simp  *)

(* lemma char_by_subsumes: 
  assumes "char_by U\<^sub>1 U\<^sub>2" "U\<^sub>2 \<preceq> U\<^sub>3"
  shows "char_by U\<^sub>1 U\<^sub>3"
proof -
  obtain A: "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>m" using assms(1)
    using characterized_by_scope_E by blast
  then obtain B: "U\<^sub>3 \<in> \<U>\<^sub>m" "U\<^sub>2 \<preceq>\<^sub>m U\<^sub>3"
    using assms(2) by (meson subst_moment_univs_disj_2 subsumption_def)
  then show ?thesis 
    using assms characterization_respects_subsumption by metis
qed *)




end



definition terminal_universals :: "'u universal_structure \<Rightarrow> 'u set" ("\<U>\<^sub>\<bottom>\<index>") where
  "\<U>\<^sub>\<bottom> \<equiv> { u . u \<in> \<U>\<^sub>s \<and> (\<forall>u'. u' \<preceq>\<^sub>s u \<longrightarrow> u' = u) }"
  for US (structure)

  
lemma terminal_universal_E:
  fixes US (structure)
  assumes "u \<in> \<U>\<^sub>\<bottom>"
  obtains "u \<in> \<U>\<^sub>s" "\<And>u'. u' \<preceq>\<^sub>s u \<Longrightarrow> u' = u'" 
  using assms by (simp add: terminal_universals_def assms(1))

lemma (in universal_structure) terminal_universal_I :  
  assumes "u \<in> \<U>\<^sub>s" "\<And>u'. u' \<preceq>\<^sub>s u \<Longrightarrow> u \<preceq>\<^sub>s u'"
  shows "u \<in> \<U>\<^sub>\<bottom>"
  apply (simp add: terminal_universals_def assms(1) ; intro allI impI)
  by (intro substantial_subsumption_antisym assms(2) ; simp)



lemma terminal_universal_subset: "\<U>\<^sub>\<bottom> \<subseteq> \<U>\<^sub>s"
  for US (structure)
  using terminal_universal_E 
  by force

(* UNUSED lemma (in universal_structure) terminal_universal_top:
  assumes "\<top>\<^sub>s \<in> \<U>\<^sub>\<bottom>"
  shows "\<U>\<^sub>s = {\<top>\<^sub>s}"
  apply (intro equalityI subsetI ; simp)
  subgoal premises P for U
    apply (intro top_eq[symmetric])
    subgoal premises Q for U'   
    proof -
      have f1: "U \<notin> \<U>\<^sub>m"
    by (meson P subst_moment_univs_disj_2)
    have f2: "U \<preceq> \<top>\<^sub>s"
    using P top_subsumes by blast
    have "\<top>\<^sub>s \<in> {u \<in> \<U>\<^sub>s. \<forall>ua. ua \<preceq>\<^sub>s u \<longrightarrow> ua = u}"
      by (metis assms terminal_universals_def)
      then have "U = \<top>\<^sub>s"
        using f2 f1 by (simp add: subsumption_def)
      then show ?thesis
        using Q top_subsumes by presburger
    qed
    done
  done *)



(* UNUSED lemma (in universal_structure) terminal_universal_iff:
    "\<U>\<^sub>s = {\<top>\<^sub>s} \<longleftrightarrow> \<U>\<^sub>\<bottom> = {\<top>\<^sub>s}"
  using terminal_universal_top 
  by (metis empty_iff insert_iff subset_singleton_iff substantial_subsumption_scope(1) terminal_universal_I terminal_universal_subset) *)
  

end