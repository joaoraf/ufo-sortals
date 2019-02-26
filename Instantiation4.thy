theory Instantiation4
  imports Individuals4 Universals2 ClosedPermutations
begin

record ('i,'u) instantiation_structure =
  indiv_structure :: "'i individual_structure" ("\<I>\<S>\<index>")
  univ_structure :: "'u universal_structure" ("\<U>\<S>\<index>")    
  moment_miof :: "'i \<Rightarrow> 'u \<Rightarrow> bool" (infix "\<Colon>\<^sub>m\<^sub>\<diamondop>\<index>" 75)

abbreviation is_worlds ("\<W>\<^sub>*\<index>") where "\<W>\<^sub>* \<equiv> \<W>\<^bsub>\<I>\<S>\<^esub>" for S (structure)
abbreviation is_individuals ("\<I>\<^sub>*\<index>") where "\<I>\<^sub>* \<equiv> \<I>\<^bsub>\<I>\<S>\<^esub>" for S (structure)
abbreviation is_substantials ("\<S>\<^sub>*\<index>") where "\<S>\<^sub>* \<equiv> \<S>\<^bsub>\<I>\<S>\<^esub>" for S (structure)
abbreviation is_moments ("\<M>\<^sub>*\<index>") where "\<M>\<^sub>* \<equiv> \<M>\<^bsub>\<I>\<S>\<^esub>" for S (structure)
abbreviation is_inheres_in (infix "\<triangleleft>\<^sub>*\<index>" 75) where "(\<triangleleft>\<^sub>*) \<equiv> inheres_in \<I>\<S>" for S (structure)
abbreviation is_similar_to (infix "\<simeq>\<^sub>*\<index>" 75) where "(\<simeq>\<^sub>*) \<equiv> exactly_similar_to \<I>\<S>" for S (structure)
abbreviation is_refers_to (infix "\<hookrightarrow>\<^sub>*\<index>" 75) where "(\<hookrightarrow>\<^sub>*) \<equiv> refers_to \<I>\<S>" for S (structure)
abbreviation is_bearer ("\<beta>\<^sub>*\<index>") where "(\<beta>\<^sub>*) \<equiv> bearer \<I>\<S>" for S (structure)
abbreviation is_ed ("ed\<^sub>*\<index>") where "(ed\<^sub>*) \<equiv> existentially_dependent \<I>\<S>" for S (structure)
abbreviation is_universals ("\<U>\<^sub>*\<index>") where "\<U>\<^sub>* \<equiv> \<U>\<^bsub>\<U>\<S>\<^esub>" for S (structure)
abbreviation is_substantial_universals ("\<U>\<^sub>s\<^sub>*\<index>") where "\<U>\<^sub>s\<^sub>* \<equiv> \<U>\<^sub>s\<^bsub>\<U>\<S>\<^esub>" for S (structure)
abbreviation is_moment_universals ("\<U>\<^sub>m\<^sub>*\<index>") where "\<U>\<^sub>m\<^sub>* \<equiv> \<U>\<^sub>m\<^bsub>\<U>\<S>\<^esub>" for S (structure)
abbreviation is_char_by ("char'_by\<^sub>*\<index>") where "char_by\<^sub>* \<equiv> characterized_by \<U>\<S>" for S (structure)
abbreviation is_char_set ("char'_set\<^sub>*\<index>") where "char_set\<^sub>* \<equiv> characterizing_set \<U>\<S>" for S (structure)
abbreviation is_m_subsumes (infix "\<preceq>\<^sub>m\<^sub>*\<index>" 75) where "(\<preceq>\<^sub>m\<^sub>*) \<equiv> moment_subsumption \<U>\<S>" for S (structure)
abbreviation is_s_subsumes (infix "\<preceq>\<^sub>s\<^sub>*\<index>" 75) where "(\<preceq>\<^sub>s\<^sub>*) \<equiv> substantial_subsumption \<U>\<S>" for S (structure)
abbreviation is_subsumes (infix "\<preceq>\<^sub>*\<index>" 75) where "(\<preceq>\<^sub>*) \<equiv> subsumption \<U>\<S>" for S (structure)
abbreviation is_top_subst_univ ("\<top>\<^sub>s\<^sub>*\<index>") where "\<top>\<^sub>s\<^sub>* \<equiv> top_subst_univ \<U>\<S>" for S (structure)

abbreviation moment_iof :: "('i,'u) instantiation_structure \<Rightarrow> 'i \<Rightarrow> 'i set \<Rightarrow> 'u \<Rightarrow> bool" ("_ \<Colon>\<^sub>m\<index>\<^bsub>_\<^esub> _" [76,1,76] 75) where
  "m \<Colon>\<^sub>m\<^bsub>w\<^esub> u \<equiv> w \<in> \<W>\<^sub>* \<and> m \<in> w \<and> m \<Colon>\<^sub>m\<^sub>\<diamondop> u"
  for IS (structure)

definition substantial_iof :: "('i,'u) instantiation_structure \<Rightarrow> 'i \<Rightarrow> 'i set \<Rightarrow> 'u \<Rightarrow> bool" ("_ \<Colon>\<^sub>s\<index>\<^bsub>_\<^esub> _" [76,1,76] 75) where
  "x \<Colon>\<^sub>s\<^bsub>w\<^esub> U \<equiv> x \<in> \<S>\<^sub>* \<and> U \<in> \<U>\<^sub>s\<^sub>* \<and> w \<in> \<W>\<^sub>* \<and> x \<in> w \<and>
      (\<forall>u \<in> char_set\<^sub>* U. \<exists>m. m \<triangleleft>\<^sub>* x \<and> m \<Colon>\<^sub>m\<^bsub>w\<^esub> u)"
  for IS (structure)

lemma substantial_iof_I:
  fixes IS (structure)
  assumes "x \<in> \<S>\<^sub>*" "U \<in> \<U>\<^sub>s\<^sub>*" "w \<in> \<W>\<^sub>*" "x \<in> w"
      "\<And>u. u \<in> char_set\<^sub>* U \<Longrightarrow> \<exists>m. m \<triangleleft>\<^sub>* x \<and> m \<Colon>\<^sub>m\<^bsub>w\<^esub> u"
    shows "x \<Colon>\<^sub>s\<^bsub>w\<^esub> U"
  using assms by  (auto simp: substantial_iof_def)

lemma substantial_iof_E[elim!]:
  fixes IS (structure)
  assumes "x \<Colon>\<^sub>s\<^bsub>w\<^esub> U"
  obtains "x \<in> \<S>\<^sub>*" "U \<in> \<U>\<^sub>s\<^sub>*" "w \<in> \<W>\<^sub>*" "x \<in> w"
      "\<And>u. u \<in> char_set\<^sub>* U \<Longrightarrow> \<exists>m. m \<triangleleft>\<^sub>* x \<and> m \<Colon>\<^sub>m\<^bsub>w\<^esub> u"
  using assms by  (auto simp: substantial_iof_def)

definition iof :: "('i,'u) instantiation_structure \<Rightarrow> 'i \<Rightarrow> 'i set \<Rightarrow> 'u \<Rightarrow> bool" ("_ \<Colon>\<index>\<^bsub>_\<^esub> _" [76,1,76] 75) where
  "x \<Colon>\<^bsub>w\<^esub> U \<equiv> x \<Colon>\<^sub>s\<^bsub>w\<^esub> U \<or> x \<Colon>\<^sub>m\<^bsub>w\<^esub> U"
  for IS (structure)

lemma iof_S_I: "x \<Colon>\<^sub>s\<^bsub>w\<^esub> U \<Longrightarrow> x \<Colon>\<^bsub>w\<^esub> U"
  for IS (structure)
  by (auto simp: iof_def)

lemma iof_M_I: "x \<Colon>\<^sub>m\<^bsub>w\<^esub> U \<Longrightarrow> x \<Colon>\<^bsub>w\<^esub> U"
  for IS (structure)
  by (auto simp: iof_def)

lemma iof_I[intro!]: "x \<Colon>\<^sub>m\<^bsub>w\<^esub> U \<or> x \<Colon>\<^sub>s\<^bsub>w\<^esub> U \<Longrightarrow> x \<Colon>\<^bsub>w\<^esub> U"
  for IS (structure)
  by (auto simp: iof_def)

lemma iof_E[elim!,cases pred]: 
  fixes IS (structure)
  assumes "x \<Colon>\<^bsub>w\<^esub> U"
  obtains (moment_iof) "x \<Colon>\<^sub>m\<^bsub>w\<^esub> U" |
          (subst_iof) "x \<Colon>\<^sub>s\<^bsub>w\<^esub> U"
  using assms  
  by (simp only: iof_def ; metis)  


definition miof :: "('i,'u) instantiation_structure \<Rightarrow> 'i \<Rightarrow> 'u \<Rightarrow> bool" (infix "\<Colon>\<^sub>\<diamondop>\<index>" 75) where
  "x \<Colon>\<^sub>\<diamondop> u \<equiv> \<exists>w \<in> worlds \<I>\<S>. x \<Colon>\<^bsub>w\<^esub> u"
  for IS (structure)

lemma instantiation_structure_eqI:
  fixes A B :: "('i,'u) instantiation_structure"
  assumes "\<I>\<S>\<^bsub>A\<^esub> = \<I>\<S>\<^bsub>B\<^esub>" "\<U>\<S>\<^bsub>A\<^esub> = \<U>\<S>\<^bsub>B\<^esub>" "moment_miof A = moment_miof B"
  shows "A = B"
  using assms by (cases A ; cases B  ; simp)

locale instantiation_structure_defs =
  fixes IS :: "('i,'u) instantiation_structure" (structure) 
begin

definition rigid where
  "rigid U \<equiv> U \<in> \<U>\<^sub>* \<and> (\<forall>x w\<^sub>1. \<forall>w\<^sub>2 \<in> \<W>\<^sub>*. x \<Colon>\<^bsub>w\<^sub>1\<^esub> U \<and> x \<in> w\<^sub>2 \<longrightarrow> x \<Colon>\<^bsub>w\<^sub>2\<^esub> U)"

definition non_rigid where
  "non_rigid U \<equiv> U \<in> \<U>\<^sub>* \<and> (\<exists>x w\<^sub>1. \<exists>w\<^sub>2 \<in> \<W>\<^sub>*. x \<Colon>\<^bsub>w\<^sub>1\<^esub> U \<and> x \<in> w\<^sub>2 \<and> \<not> x \<Colon>\<^bsub>w\<^sub>2\<^esub> U)"

abbreviation rigid_universals ("\<U>\<^sup>R") where
  "\<U>\<^sup>R \<equiv> { U . rigid U }"

abbreviation non_rigid_universals ("\<U>\<^sup>N") where
  "\<U>\<^sup>N \<equiv> { U . non_rigid U }"

definition equi_instances_S (infix "\<sim>\<^sub>s" 75) where
  "x \<sim>\<^sub>s y \<equiv> x \<in> \<S>\<^sub>* \<and> y \<in> \<S>\<^sub>* \<and> (\<forall>U w. x \<Colon>\<^sub>s\<^bsub>w\<^esub> U \<longleftrightarrow> y \<Colon>\<^sub>s\<^bsub>w\<^esub> U)"

definition equi_instances_M (infix "\<sim>\<^sub>m" 75) where
  "x \<sim>\<^sub>m y \<equiv> x \<in> \<M>\<^sub>* \<and> y \<in> \<M>\<^sub>* \<and> (\<forall>u. x \<Colon>\<^sub>m\<^sub>\<diamondop> u \<longleftrightarrow> y \<Colon>\<^sub>m\<^sub>\<diamondop> u) \<and> \<beta>\<^sub>* x \<sim>\<^sub>s \<beta>\<^sub>* y"

definition equi_instances (infix "\<sim>" 75) where
  "x \<sim> y \<equiv> x \<sim>\<^sub>s y \<or> x \<sim>\<^sub>m y" 

abbreviation "EquiPerms \<equiv> individual_structure_defs.ClosedPerms \<I>\<S> (\<sim>)"

end


locale instantiation_structure =
  instantiation_structure_defs "IS" +
  individual_structure "\<I>\<S>" +
  universal_structure "\<U>\<S>"
  for IS :: "('i,'u) instantiation_structure" (structure) +
  assumes
    moment_miof_scope: "x \<Colon>\<^sub>m\<^sub>\<diamondop> u \<Longrightarrow> x \<in> \<M>\<^sub>* \<and> u \<in> \<U>\<^sub>m\<^sub>*" and    
(*    iof_scope: "x \<Colon>\<^bsub>w\<^esub> u \<Longrightarrow> w \<in> \<W> \<and> x \<in> w \<and> u \<in> \<U>" and*)
    moment_miof_agrees_with_subsumes: "\<lbrakk> U\<^sub>1 \<in> \<U>\<^sub>m\<^sub>* ; U\<^sub>2 \<in> \<U>\<^sub>m\<^sub>* \<rbrakk> \<Longrightarrow> U\<^sub>1 \<preceq>\<^sub>m\<^sub>* U\<^sub>2 \<longleftrightarrow> (\<forall>x. x \<Colon>\<^sub>m\<^sub>\<diamondop> U\<^sub>1 \<longrightarrow> x \<Colon>\<^sub>m\<^sub>\<diamondop> U\<^sub>2)" and
(*     iof_agrees_with_subsumes: "U\<^sub>1 \<preceq> U\<^sub>2 \<longleftrightarrow> U\<^sub>1 \<in> \<U> \<and> (\<forall>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<longrightarrow> x \<Colon>\<^bsub>w\<^esub> U\<^sub>2)" and *)
    at_least_one_instance: "U \<in> \<U>\<^sub>* \<Longrightarrow> \<exists>x w. x \<Colon>\<^bsub>w\<^esub> U" and 
    every_individual_is_iof: "\<lbrakk> w \<in> \<W>\<^sub>* ; x \<in> w \<rbrakk> \<Longrightarrow> \<exists>U. x \<Colon>\<^bsub>w\<^esub> U" and    
    iof_agree_with_characterization: 
      "\<lbrakk> char_by\<^sub>* U u ; x \<Colon>\<^sub>s\<^bsub>w\<^esub> U \<rbrakk> \<Longrightarrow> \<exists>y. y \<triangleleft>\<^sub>* x \<and> y \<Colon>\<^sub>m\<^bsub>w\<^esub> u" and
    moment_iof_agrees_with_similarity_1: "\<lbrakk> m\<^sub>1 \<simeq>\<^sub>* m\<^sub>2 ; m\<^sub>1 \<Colon>\<^sub>m\<^sub>\<diamondop> U \<rbrakk> \<Longrightarrow> m\<^sub>2 \<Colon>\<^sub>m\<^sub>\<diamondop> U" and 
    moment_univ_extensionality: "\<lbrakk> U\<^sub>1 \<in> \<U>\<^sub>m\<^sub>* ; U\<^sub>2 \<in> \<U>\<^sub>m\<^sub>* ; \<forall>x. x \<Colon>\<^sub>m\<^sub>\<diamondop> U\<^sub>1 \<longleftrightarrow> x \<Colon>\<^sub>m\<^sub>\<diamondop> U\<^sub>2 \<rbrakk> \<Longrightarrow> U\<^sub>1 = U\<^sub>2" and
    no_orphan_moments: "\<lbrakk> m \<triangleleft>\<^sub>* x ; w \<in> \<W>\<^sub>* ; m \<in> w \<rbrakk> \<Longrightarrow> \<exists>U u. m \<Colon>\<^sub>\<diamondop> u \<and> x \<Colon>\<^sub>s\<^bsub>w\<^esub> U \<and> char_by\<^sub>* U u"

begin

lemma moment_iof_agrees_with_similarity: 
  assumes "m\<^sub>1 \<simeq>\<^sub>* m\<^sub>2" "m\<^sub>1 \<Colon>\<^sub>m\<^bsub>w\<^sub>1\<^esub> U" "w\<^sub>2 \<in> \<W>\<^sub>*" "m\<^sub>2 \<in> w\<^sub>2"
  shows "m\<^sub>2 \<Colon>\<^sub>m\<^bsub>w\<^sub>2\<^esub> U" 
  using moment_iof_agrees_with_similarity_1[OF assms(1),of U] assms
    by simp
  

lemma moment_iof_scope: "x \<Colon>\<^sub>m\<^bsub>w\<^esub> u \<Longrightarrow> w \<in> \<W>\<^sub>* \<and> x \<in> w \<and> x \<in> \<M>\<^sub>* \<and> u \<in> \<U>\<^sub>m\<^sub>*" 
  using moment_miof_scope
  by blast

lemma moment_iof_agrees_with_subsumes: "\<lbrakk> U\<^sub>1 \<in> \<U>\<^sub>m\<^sub>* ; U\<^sub>2 \<in> \<U>\<^sub>m\<^sub>* \<rbrakk> \<Longrightarrow> U\<^sub>1 \<preceq>\<^sub>m\<^sub>* U\<^sub>2 \<longleftrightarrow> (\<forall>x w. x \<Colon>\<^sub>m\<^bsub>w\<^esub> U\<^sub>1 \<longrightarrow> x \<Colon>\<^sub>m\<^bsub>w\<^esub> U\<^sub>2)" 
  using moment_miof_agrees_with_subsumes  
  by (meson every_individual_exists_somewhere inheres_in_scope moment_miof_scope momentsE)


lemma iof_scope: 
  assumes "x \<Colon>\<^bsub>w\<^esub> u"
  shows "w \<in> \<W>\<^sub>* \<and> x \<in> w \<and> u \<in> \<U>\<^sub>*" 
  using assms apply (cases rule: iof_E)  
  subgoal using moment_iof_scope universal_I by metis
  using substantial_iof_E universal_I by force

lemma iof_scope_D: 
  assumes "x \<Colon>\<^bsub>w\<^esub> u"
  shows "x \<in> \<I>\<^sub>*" "w \<in> \<W>\<^sub>*" "x \<in> w" "u \<in> \<U>\<^sub>*"
  using iof_scope[OF assms] worlds_are_made_of_individuals[of w] by blast+ 

lemma iof_scope_E[cases pred]:
  assumes "x \<Colon>\<^bsub>w\<^esub> u"
  obtains (subst) "w \<in> \<W>\<^sub>*" "x \<in> w" "x \<in> \<S>\<^sub>*" "u \<in> \<U>\<^sub>s\<^sub>*"  |
          (moment) "w \<in> \<W>\<^sub>*" "x \<in> w" "x \<in> \<M>\<^sub>*" "u \<in> \<U>\<^sub>m\<^sub>*" 
proof -
  obtain A: "w \<in> \<W>\<^sub>*" "x \<in> w" "u \<in> \<U>\<^sub>*" using assms iof_scope by auto
  then have B:"x \<in> \<I>\<^sub>*" using worlds_are_made_of_individuals by blast
  have C1: False if "u \<in> \<U>\<^sub>m\<^sub>*" "u \<in> \<U>\<^sub>s\<^sub>*" using that A(3) universal_exhaust by blast
  have C2: False if "x \<in> \<S>\<^sub>*" "x \<in> \<M>\<^sub>*" using that B individuals_cases by blast
  have D1: "x \<in> \<M>\<^sub>* \<and> x \<notin> \<S>\<^sub>* \<and> u \<in> \<U>\<^sub>m\<^sub>* \<and> u \<notin> \<U>\<^sub>s\<^sub>*" if as: "x \<Colon>\<^sub>m\<^bsub>w\<^esub> u" 
    using moment_iof_scope[OF as] 
    apply (clarsimp)
    apply (intro conjI notI)
    subgoal by (frule C2 ; simp)
    by (frule C1 ; simp)

  have D2: "x \<notin> \<M>\<^sub>* \<and> x \<in> \<S>\<^sub>* \<and> u \<notin> \<U>\<^sub>m\<^sub>* \<and> u \<in> \<U>\<^sub>s\<^sub>*" if as: "x \<Colon>\<^sub>s\<^bsub>w\<^esub> u"
    using as apply (simp add: substantial_iof_def[of IS x w u] ; 
                    elim conjE ; intro conjI notI)
    using C1 C2 by metis+
    
  obtain E: "x \<in> \<S>\<^sub>*" "u \<in> \<U>\<^sub>s\<^sub>*" if "x \<Colon>\<^sub>s\<^bsub>w\<^esub> u" using substantial_iof_def by metis
  note F = that[OF A(1,2)]
  show ?thesis          
    apply (rule iof_E[OF assms])
    subgoal by (frule D1 ; simp add: F(2)) 
    by (frule D2 ; simp add: F(1))
qed


lemma iof_moment_rigid: 
  assumes "m \<in> \<M>\<^sub>*" "m \<Colon>\<^bsub>w\<^esub> U" "w' \<in> \<W>\<^sub>*" "m \<in> w'"
  shows "m \<Colon>\<^bsub>w'\<^esub> U" 
  using assms 
  by (meson exactly_similar_refl individual_structure.individuals_cases individual_structure.inheres_in_scope individual_structure_axioms iof_def moment_iof_agrees_with_similarity momentsE substantial_iof_E)
  
lemma char_by_E2:
  assumes "char_by\<^sub>* U\<^sub>1 U\<^sub>2"
  obtains "U\<^sub>1 \<in> \<U>\<^sub>s\<^sub>*" "U\<^sub>2 \<in> \<U>\<^sub>m\<^sub>*" "\<And>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<Longrightarrow> \<exists>m. m \<Colon>\<^bsub>w\<^esub> U\<^sub>2 \<and> m \<triangleleft>\<^sub>* x"
proof -
  obtain A: "U\<^sub>1 \<in> \<U>\<^sub>s\<^sub>*" "\<And>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<Longrightarrow> \<exists>m. m \<Colon>\<^bsub>w\<^esub> U\<^sub>2 \<and> m \<triangleleft>\<^sub>* x" 
    using assms 
    by (meson char_set_I characterized_by_scope instantiation_structure.moment_iof_scope instantiation_structure_axioms iof_def no_moment_univ_is_characterized substantial_iof_E)
  obtain x w where B: "x \<Colon>\<^bsub>w\<^esub> U\<^sub>1" 
    using A(1) at_least_one_instance universal_I 
    by presburger
  then obtain C: "x \<in> \<I>\<^sub>*" "w \<in> \<W>\<^sub>*" "x \<in> w" 
    using iof_scope A(1) using A(2) inheres_in_scope
    by meson
  obtain m where D: "m \<Colon>\<^bsub>w\<^esub> U\<^sub>2" "m \<triangleleft>\<^sub>* x" using A(2) B by meson
  then have "m \<in> \<M>\<^sub>*" using momentsI by simp
  then have E: "U\<^sub>2 \<in> \<U>\<^sub>m\<^sub>*" 
    using substantials_moments_disj momentsE inheres_in_scope
          D(1) iof_scope local.subsumes_refl local.subsumes_scope   
    by (meson assms characterized_by_scope_E)
  show ?thesis using that A E by blast
qed
  
lemma miof_I[intro]:
  assumes "x \<Colon>\<^bsub>w\<^esub> u"
  shows "x \<Colon>\<^sub>\<diamondop> u"
  using assms apply (simp add: miof_def ; intro bexI[of _ w] ; simp?)
  using iof_scope by simp

lemma miof_E[elim]:
  assumes "x \<Colon>\<^sub>\<diamondop> u"
  obtains w where "x \<Colon>\<^bsub>w\<^esub> u" 
  using assms by (simp add: miof_def ; meson)

lemma char_by_scope: 
  assumes "char_by\<^sub>* U U'"
  shows "U \<in> \<U>\<^sub>s\<^sub>*" "U' \<in> \<U>\<^sub>m\<^sub>*"
  using assms char_by_E2 by metis+

lemma  iof_S_U_simp: "x \<Colon>\<^bsub>w\<^esub> u \<Longrightarrow> x \<in> \<S>\<^sub>* \<longleftrightarrow> u \<in> \<U>\<^sub>s\<^sub>*" 
  using iof_scope_E substantials_moments_disj 
  by (metis individual_structure.individuals_cases individual_structure_axioms instantiation_structure.iof_scope instantiation_structure_axioms substantialsE universal_exhaust)

lemma  iof_M_U_simp: "x \<Colon>\<^bsub>w\<^esub> u \<Longrightarrow> x \<in> \<M>\<^sub>* \<longleftrightarrow> u \<in> \<U>\<^sub>m\<^sub>*" 
  using iof_scope_E substantials_moments_disj 
  by (metis individual_structure.individuals_cases individual_structure_axioms instantiation_structure.iof_scope instantiation_structure_axioms substantialsE universal_exhaust)

lemma  iof_S_simp: "x \<in> \<S>\<^sub>* \<or> u \<in> \<U>\<^sub>s\<^sub>* \<Longrightarrow> x \<Colon>\<^bsub>w\<^esub> u \<longleftrightarrow> x \<Colon>\<^sub>s\<^bsub>w\<^esub> u"   
  by (meson individuals_cases instantiation_structure.moment_iof_scope instantiation_structure_axioms iof_E iof_S_I iof_S_U_simp substantialsE)

lemma  iof_M_simp: "x \<in> \<M>\<^sub>* \<or> u \<in> \<U>\<^sub>m\<^sub>* \<Longrightarrow> x \<Colon>\<^bsub>w\<^esub> u \<longleftrightarrow> x \<Colon>\<^sub>m\<^bsub>w\<^esub> u"   
  by (meson individuals_cases iof_E iof_M_I iof_M_U_simp substantial_iof_E substantialsE)

lemma rigid_moment_universals: "u \<in> \<U>\<^sub>m\<^sub>* \<Longrightarrow> rigid u"
  apply (clarsimp simp: rigid_def ; intro conjI allI ballI impI ; (elim conjE)?)
  subgoal G1 using universal_I by simp
  subgoal G2 for x w\<^sub>1 w\<^sub>2
    apply (intro moment_iof_agrees_with_similarity[of x x w\<^sub>1 u w\<^sub>2, THEN iof_I[OF disjI1]] exactly_similar_refl[of x] 
          ; simp?)
    subgoal by (simp add: iof_M_U_simp)    
    by (simp add: iof_M_simp)
  done
  
lemma subtantial_iof_agrees_with_subsumes:
  assumes "x \<Colon>\<^sub>s\<^bsub>w\<^esub> U" "U \<preceq>\<^sub>s\<^sub>* U'"
  shows "x \<Colon>\<^sub>s\<^bsub>w\<^esub> U'"
proof -
  obtain A[simp,intro!]: "x \<in> \<S>\<^sub>*" "U \<in> \<U>\<^sub>s\<^sub>*" "w \<in> \<W>\<^sub>*" "x \<in> w"
    and B: "\<And>u. u \<in> characterizing_set \<U>\<S> U \<Longrightarrow> \<exists>m. m \<triangleleft>\<^sub>* x \<and> m \<Colon>\<^sub>m\<^bsub>w\<^esub> u"
    using substantial_iof_E[OF assms(1)] by metis
  then have B1: "\<And>u. char_by\<^sub>* U u \<Longrightarrow> \<exists>m. m \<triangleleft>\<^sub>* x \<and> m \<Colon>\<^sub>m\<^bsub>w\<^esub> u"
    using characterizing_set_def by simp
  obtain C[simp,intro!]: "U' \<in> \<U>\<^sub>s\<^sub>*" and D: "\<And>u.  char_by\<^sub>* U' u \<Longrightarrow> \<exists>u'. char_by\<^sub>* U u' \<and> u' \<preceq>\<^sub>m\<^sub>* u"
    using substantial_subsumption_E[OF assms(2)] by metis
  show ?thesis
    apply (intro substantial_iof_I A C)
    subgoal premises P for U
      apply (rule exE[OF P[THEN char_set_D, THEN D]] ; elim conjE ; intro B1)      
      using characterization_respects_subsumption by blast
    done
qed

lemma iof_agrees_with_subsumes:
  assumes "x \<Colon>\<^bsub>w\<^esub> U" "U \<preceq>\<^sub>* U'"
  shows "x \<Colon>\<^bsub>w\<^esub> U'"
proof -
  consider (c1) "x \<Colon>\<^sub>s\<^bsub>w\<^esub> U" "U \<preceq>\<^sub>s\<^sub>* U'" | (c2) "x \<Colon>\<^sub>m\<^bsub>w\<^esub> U" "U \<preceq>\<^sub>m\<^sub>* U'"
    using assms(1,2) 
    by (meson iof_M_simp iof_S_simp moment_subsumes_scope substantial_subsumption_scope(1) subsumesE)
  then show ?thesis
    apply cases
    subgoal G1 using subtantial_iof_agrees_with_subsumes  iof_S_I by metis
    subgoal G2 premises P
      using moment_iof_agrees_with_subsumes[of U U',THEN iffD1,rule_format,of w x,OF _  _ P(2,1)] 
                    iof_M_I[of w IS x U'] moment_iof_scope[of w x U'] moment_iof_scope[OF  P(1)] 
                    P(2) moment_subsumes_scope 
      by blast
    done
qed

lemma miof_agrees_with_subsumes:
  assumes "x \<Colon>\<^sub>\<diamondop> U" "U \<preceq>\<^sub>* U'"
  shows "x \<Colon>\<^sub>\<diamondop> U'"
  using assms miof_def iof_agrees_with_subsumes by metis

lemma  not_subst_miof_ex:
  assumes "s\<^sub>y \<in> \<S>\<^sub>*" "U \<in> \<U>\<^sub>s\<^sub>*" "\<not> s\<^sub>y \<Colon>\<^sub>\<diamondop> U" "w \<in> \<W>\<^sub>*" "s\<^sub>y \<in> w"
  shows "\<exists>u. char_by\<^sub>* U u \<and> (\<forall>m. m \<triangleleft>\<^sub>* s\<^sub>y \<and> m \<in> w \<longrightarrow> \<not> m \<Colon>\<^sub>m\<^sub>\<diamondop> u)"    
proof (rule ccontr ; simp only: not_ex de_Morgan_conj not_all not_imp not_not) 
  assume as: "\<forall>u. \<not> char_by\<^sub>* U u \<or> (\<exists>m. (m \<triangleleft>\<^sub>* s\<^sub>y \<and> m \<in> w) \<and> m \<Colon>\<^sub>m\<^sub>\<diamondop> u)"
  then have A: "char_by\<^sub>* U u \<Longrightarrow> \<exists>m. m \<triangleleft>\<^sub>* s\<^sub>y \<and> m \<Colon>\<^sub>m\<^bsub>w\<^esub> u" for u      
    by (simp add: assms)
  then obtain \<sigma> where B: "\<sigma> u \<triangleleft>\<^sub>* s\<^sub>y" "\<sigma> u \<in> w" "\<sigma> u \<Colon>\<^sub>m\<^sub>\<diamondop> u" if "char_by\<^sub>* U u" for u
    using that by moura
  have "s\<^sub>y \<Colon>\<^sub>s\<^bsub>w\<^esub> U"
    apply (intro substantial_iof_I assms)
    apply (elim char_set_E)
    using A by simp 
  then have "s\<^sub>y \<Colon>\<^sub>\<diamondop> U" by (meson iof_S_I miof_I)
  then show False using assms by simp
qed

lemma  not_subst_miof_E:
  assumes "s\<^sub>y \<in> \<S>\<^sub>*" "U \<in> \<U>\<^sub>s\<^sub>*" "\<not> s\<^sub>y \<Colon>\<^sub>\<diamondop> U" "w \<in> \<W>\<^sub>*" "s\<^sub>y \<in> w" 
  obtains u where "char_by\<^sub>* U u" "\<And>m. \<lbrakk> m \<triangleleft>\<^sub>* s\<^sub>y ; m \<in> w \<rbrakk> \<Longrightarrow> \<not> m \<Colon>\<^sub>m\<^sub>\<diamondop> u" 
  using not_subst_miof_ex[OF assms] by metis

lemma equi_instances_S_I[intro!]:
  assumes "x \<in> \<S>\<^sub>*" "y \<in> \<S>\<^sub>*" "\<And>U w. x \<Colon>\<^sub>s\<^bsub>w\<^esub> U \<longleftrightarrow> y \<Colon>\<^sub>s\<^bsub>w\<^esub> U"
  shows "x \<sim>\<^sub>s y"
  using assms by (auto simp: equi_instances_S_def)

lemma equi_instances_S_E[elim!]:
  assumes "x \<sim>\<^sub>s y"
  obtains "x \<in> \<S>\<^sub>*" "y \<in> \<S>\<^sub>*" "\<And>U w. x \<Colon>\<^sub>s\<^bsub>w\<^esub> U \<longleftrightarrow> y \<Colon>\<^sub>s\<^bsub>w\<^esub> U"
  using assms by (auto simp: equi_instances_S_def)

lemma equi_instances_S[simp]:
  "x \<sim>\<^sub>s y \<longleftrightarrow> x \<in> \<S>\<^sub>* \<and> y \<in> \<S>\<^sub>* \<and> (\<forall>U w. x \<Colon>\<^sub>s\<^bsub>w\<^esub> U \<longleftrightarrow> y \<Colon>\<^sub>s\<^bsub>w\<^esub> U)"
  by (auto simp: equi_instances_S_def)

lemma equi_instances_S_refl: "x \<in> \<S>\<^sub>* \<Longrightarrow> x \<sim>\<^sub>s x" by blast
lemma equi_instances_S_sym[sym]: "x \<sim>\<^sub>s y \<Longrightarrow> y \<sim>\<^sub>s x " by auto
lemma equi_instances_S_trans: "\<lbrakk> x \<sim>\<^sub>s y ; y \<sim>\<^sub>s z \<rbrakk> \<Longrightarrow> x \<sim>\<^sub>s z " by auto

lemmas equi_instances_S_eq_rel_props = equi_instances_S_refl equi_instances_S_sym equi_instances_S_trans

lemma equi_instances_M_I[intro!]:
  assumes "x \<in> \<M>\<^sub>*" "y \<in> \<M>\<^sub>*" "\<And>u. x \<Colon>\<^sub>m\<^sub>\<diamondop> u \<longleftrightarrow> y \<Colon>\<^sub>m\<^sub>\<diamondop> u" "\<beta>\<^sub>* x \<sim>\<^sub>s \<beta>\<^sub>* y"
  shows "x \<sim>\<^sub>m y"
  using assms by (auto simp: equi_instances_M_def)

lemma equi_instances_M_E[elim!]:
  assumes "x \<sim>\<^sub>m y"
  obtains "x \<in> \<M>\<^sub>*" "y \<in> \<M>\<^sub>*" "\<And>u. x \<Colon>\<^sub>m\<^sub>\<diamondop> u \<longleftrightarrow> y \<Colon>\<^sub>m\<^sub>\<diamondop> u" "\<beta>\<^sub>* x \<sim>\<^sub>s \<beta>\<^sub>* y"
  using assms by (auto simp: equi_instances_M_def)

lemma equi_instances_M[simp]:
  "x \<sim>\<^sub>m y \<longleftrightarrow> x \<in> \<M>\<^sub>* \<and> y \<in> \<M>\<^sub>* \<and> (\<forall>u. x \<Colon>\<^sub>m\<^sub>\<diamondop> u \<longleftrightarrow> y \<Colon>\<^sub>m\<^sub>\<diamondop> u) \<and> \<beta>\<^sub>* x \<sim>\<^sub>s \<beta>\<^sub>* y"
  by (simp only: equi_instances_M_def)

lemma equi_instances_M_refl: "x \<in> \<M>\<^sub>* \<Longrightarrow> x \<sim>\<^sub>m x"     
  using inheres_in_scope by blast

lemma equi_instances_M_sym[sym]: "x \<sim>\<^sub>m y \<Longrightarrow> y \<sim>\<^sub>m x " by auto
lemma equi_instances_M_trans: "\<lbrakk> x \<sim>\<^sub>m y ; y \<sim>\<^sub>m z \<rbrakk> \<Longrightarrow> x \<sim>\<^sub>m z " by auto

lemmas equi_instances_M_eq_rel_props = equi_instances_M_refl equi_instances_M_sym equi_instances_M_trans

lemma equi_instances_I[intro!]:
  "x \<sim>\<^sub>s y \<or> x \<sim>\<^sub>m y \<Longrightarrow> x \<sim> y"   
  by (auto simp: equi_instances_def)


lemma equi_instances_cases[cases pred]:
  assumes "x \<sim> y"
  obtains (moments) "x \<sim>\<^sub>m y" | (substantials) "x \<sim>\<^sub>s y"  
  using assms by (simp only: equi_instances_def ; metis)

lemma equi_instances_iff:
  "x \<sim> y \<longleftrightarrow> x \<in> \<S>\<^sub>* \<and> y \<in> \<S>\<^sub>* \<and> x \<sim>\<^sub>s y \<or>
             x \<in> \<M>\<^sub>* \<and> y \<in> \<M>\<^sub>* \<and> x \<sim>\<^sub>m y"
   by (simp only: equi_instances_def equi_instances_M_def equi_instances_S_def 
      simp_thms ; intro iffI conjI impI allI ; (elim conjE disjE)? ; simp? ; blast)
  
lemma equi_instances_simps:
   "x \<in> \<S>\<^sub>* \<Longrightarrow> x \<sim> y \<longleftrightarrow> x \<in> \<S>\<^sub>* \<and> y \<in> \<S>\<^sub>* \<and> x \<sim>\<^sub>s y" 
   "x \<in> \<S>\<^sub>* \<Longrightarrow> y \<sim> x \<longleftrightarrow> x \<in> \<S>\<^sub>* \<and> y \<in> \<S>\<^sub>* \<and> y \<sim>\<^sub>s x"
   "x \<in> \<M>\<^sub>* \<Longrightarrow> x \<sim> y \<longleftrightarrow> x \<in> \<M>\<^sub>* \<and> y \<in> \<M>\<^sub>* \<and> x \<sim>\<^sub>m y" 
   "x \<in> \<M>\<^sub>* \<Longrightarrow> y \<sim> x \<longleftrightarrow> x \<in> \<M>\<^sub>* \<and> y \<in> \<M>\<^sub>* \<and> y \<sim>\<^sub>m x"  
   by (simp only: equi_instances_def equi_instances_M_def equi_instances_S_def 
      simp_thms ; intro iffI conjI impI allI ; (elim conjE disjE)? ; simp? ; blast)+
  

declare equi_instances_def[simp]


lemma equi_instance_equiv_rel_P[simp,intro!]: "closure_rel_P (\<sim>) \<I>\<^sub>*"
  apply (unfold_locales)
  subgoal using equi_instances_M_eq_rel_props equi_instances_S_eq_rel_props equi_instances_iff
    substantials_moments_disj by meson
  subgoal using equi_instances_M_eq_rel_props equi_instances_S_eq_rel_props equi_instances_iff
    substantials_moments_disj by (smt equi_instances_simps(3))
  subgoal using equi_instances_M_eq_rel_props equi_instances_S_eq_rel_props equi_instances_iff
    substantials_moments_disj by blast        
  subgoal using equi_instances_M_eq_rel_props equi_instances_S_eq_rel_props equi_instances_iff
    substantials_moments_disj 
    by (meson moments_are_individuals substantialsE)
  done

lemma id_on_equi_iof_perms[intro!,simp]: "id \<in> EquiPerms"  
  using ClosedPerms_iff equi_instances_def id_on_perm  
  using equi_instances_M_refl individuals_moments_substantials by auto

lemma equi_iof_perms_ne[intro!,simp]: "EquiPerms \<noteq> {}" using id_on_equi_iof_perms by blast


end

end
