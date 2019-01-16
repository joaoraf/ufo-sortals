theory Sortals
  imports Main
begin

record ('s,'m) individual_structure =
  substantials :: "'s set" ("\<S>\<index>")
  bearer :: "'m \<Rightarrow> 's" ("\<beta>\<index>")
  exact_similarity :: "'m \<Rightarrow> 'm \<Rightarrow> bool" (infix "\<simeq>\<index>" 75)
  ext_dep :: "'m \<Rightarrow> 'm \<Rightarrow> bool" (infix "\<leftrightarrow>\<index>" 75)
  worlds :: "('s set \<times> 'm set) set" ("\<W>\<index>")
  

locale individual_structure_defs = 
  fixes S :: "('s,'m,'x) individual_structure_scheme" (structure)
begin

definition \<M> :: "'m set" where
  "\<M> \<equiv> { m . \<beta> m \<in> \<S> }"

end

locale individual_structure = individual_structure_defs +
  assumes
    at_least_one_substantial: "\<S> \<noteq> {}" and
    substantial_no_undefined: "undefined \<notin> \<S>" and
    bearer_ext: "\<beta> m \<notin> \<S> \<Longrightarrow> \<beta> m = undefined" and
    ext_dep: "m\<^sub>1 \<leftrightarrow> m\<^sub>2 \<Longrightarrow> m\<^sub>1 \<in> \<M> \<and> m\<^sub>2 \<in> \<M> \<and> \<beta> m\<^sub>1 \<noteq> \<beta> m\<^sub>2" and
    ext_dep_sym[sym]: "m\<^sub>1 \<leftrightarrow> m\<^sub>2 \<Longrightarrow> m\<^sub>2 \<leftrightarrow> m\<^sub>1" and
    ext_dep_trans[trans]: "\<lbrakk> m\<^sub>1 \<leftrightarrow> m\<^sub>2 ; m\<^sub>2 \<leftrightarrow> m\<^sub>3 \<rbrakk> \<Longrightarrow> m\<^sub>1 \<leftrightarrow> m\<^sub>3" and
    exact_sim_scope: "m\<^sub>1 \<simeq> m\<^sub>2 \<Longrightarrow> m\<^sub>1 \<in> \<M> \<and> m\<^sub>2 \<in> \<M>" and
    exact_sim_refl: "m \<in> \<M> \<Longrightarrow> m \<simeq> m" and
    exact_sim_sym[sym]: "m\<^sub>1 \<simeq> m\<^sub>2 \<Longrightarrow> m\<^sub>2 \<simeq> m\<^sub>1" and
    exact_sim_trans[trans]: "\<lbrakk> m\<^sub>1 \<simeq> m\<^sub>2 ; m\<^sub>2 \<simeq> m\<^sub>3 \<rbrakk> \<Longrightarrow> m\<^sub>1 \<simeq> m\<^sub>3" and
    worlds_subst_moment: "(Ss,Ms) \<in> \<W> \<Longrightarrow> Ss \<subseteq> \<S> \<and> Ms \<subseteq> \<M>" and
    moment_ex_dep_bearer: "\<lbrakk> (Ss,Ms) \<in> \<W> ; m \<in> Ms \<rbrakk> \<Longrightarrow> \<beta> m \<in> Ss" and
    ext_dep_ex_dep: "\<lbrakk> (Ss,Ms) \<in> \<W> ; m\<^sub>1 \<in> Ms ;  m\<^sub>1 \<leftrightarrow> m\<^sub>2 \<rbrakk> \<Longrightarrow> m\<^sub>2 \<in> Ms" 
begin

end

record ('s,'m) individual_structure_perm = 
    "('s,'m) individual_structure"  +
  subst_perm :: "'s \<Rightarrow> 's"  ("\<pi>\<^sub>s\<index>") 
  moment_perm :: "'m \<Rightarrow> 'm"  ("\<pi>\<^sub>m\<index>") 

locale individual_structure_perm_defs =
  individual_structure \<Pi>  
  for \<Pi> :: "('s,'m) individual_structure_perm" (structure) 
begin

definition inv_subst_perm ("\<pi>\<^sub>s\<^sup>-\<^sup>1") where 
  "\<pi>\<^sub>s\<^sup>-\<^sup>1 \<equiv> inv_into \<S> \<pi>\<^sub>s"

definition inv_moment_perm ("\<pi>\<^sub>m\<^sup>-\<^sup>1") where 
  "\<pi>\<^sub>m\<^sup>-\<^sup>1 \<equiv> inv_into \<M> \<pi>\<^sub>m"

end

locale individual_structure_perm =
  individual_structure_perm_defs +
  assumes
    subst_perm_scope_1[simp]: "\<pi>\<^sub>s s \<in> \<S> \<longleftrightarrow> s \<in> \<S>" and
    subst_perm_scope_2[simp]: "\<pi>\<^sub>s s \<notin> \<S> \<Longrightarrow> s = undefined" and  
    subst_perm_single: "\<lbrakk> s\<^sub>1 \<in> \<S> ; s\<^sub>2 \<in> \<S> ; \<pi>\<^sub>s s\<^sub>1 = \<pi>\<^sub>s s\<^sub>2 \<rbrakk> \<Longrightarrow> s\<^sub>1 = s\<^sub>2" and
    moment_perm_scope_1[simp]: "\<pi>\<^sub>m m \<in> \<M> \<longleftrightarrow> m \<in> \<M>" and
    moment_perm_scope_2[simp]: "\<pi>\<^sub>m m \<notin> \<M>  \<Longrightarrow> m = undefined" and
    moment_perm_single: "\<lbrakk> m\<^sub>1 \<in> \<M> ; m\<^sub>2 \<in> \<M> ; \<pi>\<^sub>m m\<^sub>1 = \<pi>\<^sub>m m\<^sub>2 \<rbrakk> \<Longrightarrow> m\<^sub>1 = m\<^sub>2" and
    moment_perm_pres_bearers[simp]: "\<beta> (\<pi>\<^sub>m m) = \<pi>\<^sub>s (\<beta> m)" and
    moment_perm_pres_ext_dep: "\<pi>\<^sub>m m\<^sub>1 \<leftrightarrow> \<pi>\<^sub>m m\<^sub>2 \<longleftrightarrow> m\<^sub>1 \<leftrightarrow> m\<^sub>2" and
    perm_preserv_worlds: "(Ss,Ms) \<in> \<W> \<Longrightarrow> (\<pi>\<^sub>s ` Ss, \<pi>\<^sub>m ` Ms) \<in> \<W>" and
    inv_perm_preserv_worlds: "(Ss,Ms) \<in> \<W> \<Longrightarrow> \<exists>Ss' Ms'. (Ss',Ms') \<in> \<W> \<and> \<pi>\<^sub>s ` Ss' = Ss \<and> \<pi>\<^sub>m ` Ms' = Ms"

context individual_structure
begin

definition Perms where
  "Perms \<equiv> { \<Pi> . individual_structure_perm \<Pi> \<and>
                  individual_structure.truncate \<Pi> = individual_structure.truncate S }"

end

locale determinate_individual_structure =
    individual_structure +
  assumes
    perms_id_on_subst: "\<lbrakk> \<Pi> \<in> Perms  ; s \<in> \<S> \<rbrakk> \<Longrightarrow> \<pi>\<^sub>s\<^bsub>\<Pi>\<^esub> s = s"  

locale ambiguous_individual_structure =
    individual_structure +
  assumes
    perms_not_id_on_subst: "\<exists>\<Pi> \<in> Perms. \<exists>s \<in> \<S>. \<pi>\<^sub>s\<^bsub>\<Pi>\<^esub> s \<noteq> s"


record ('s,'m,'mu) moment_universal_structure = "('s,'m) individual_structure" +
  moment_universals :: "'mu set" ("\<U>\<^sub>m\<index>")
  m_iof :: "'m \<Rightarrow> 'mu \<Rightarrow> bool" (infix "\<Colon>\<^sub>m\<index>" 75)

locale moment_universal_structure =
    individual_structure where S = S   
  for S :: "('s,'m,'mu,'xtra) moment_universal_structure_scheme" (structure) +
  assumes
    moment_univs_finite: "finite \<U>\<^sub>m" and
    m_iof_scope: "m \<Colon>\<^sub>m um \<Longrightarrow> m \<in> \<M> \<and> um \<in> \<U>\<^sub>m" and
    m_every_moment_iof: "m \<in> \<M> \<Longrightarrow> \<exists>um \<in> \<U>\<^sub>m. m \<Colon>\<^sub>m um" and
    m_every_mom_univ_inst: "um \<in> \<U>\<^sub>m \<Longrightarrow> \<exists>m \<in> \<M>. m \<Colon>\<^sub>m um" and
    moment_univ_eq: "\<lbrakk> um\<^sub>1 \<in> \<U>\<^sub>m ; um\<^sub>2 \<in> \<U>\<^sub>m ; \<forall>m. m \<Colon>\<^sub>m um\<^sub>1 \<longleftrightarrow> m \<Colon>\<^sub>m um\<^sub>2 \<rbrakk> \<Longrightarrow> um\<^sub>1 = um\<^sub>2" 

record ('s,'m,'mu,'su) substantial_universal_structure = 
    "('s,'m,'mu) moment_universal_structure" +
  subst_universals :: "'su set" ("\<U>\<^sub>s\<index>")
  s_iof :: "'s \<Rightarrow> ('s set \<times> 'm set) \<Rightarrow> 'su \<Rightarrow> bool" ("_ \<Colon>\<index>\<^bsub>_\<^esub> _" [76,1,76] 75)  

locale substantial_universal_structure_defs =
    moment_universal_structure where S = S   
  for S :: "('s,'m,'mu,'su, 'xtra) substantial_universal_structure_scheme" (structure) 
begin

definition charBy :: "'su \<Rightarrow> 'mu \<Rightarrow> bool" where
  "charBy U um \<equiv> U \<in> \<U>\<^sub>s \<and> um \<in> \<U>\<^sub>m \<and> (\<forall>s w. s \<Colon>\<^bsub>w\<^esub> U \<longrightarrow> (\<exists>m. m \<Colon>\<^sub>m um \<and> \<beta> m = s \<and> m \<in> snd w))"

(* definition Top :: "'su" where
  "Top \<equiv> THE U. U \<in> \<U>\<^sub>s \<and> (\<forall>s w. s \<in> \<S> \<and> w \<in> \<W> \<and> s \<in> fst w \<longrightarrow> s \<Colon>\<^bsub>w\<^esub> U)"
*)
(*
definition s_iof :: "'s \<Rightarrow> ('s set \<times> 'm set) \<Rightarrow> 'su \<Rightarrow> bool" ("_ \<Colon>\<^bsub>_\<^esub> _" [76,1,76] 75)
  where "s \<Colon>\<^bsub>w\<^esub> su \<equiv> 
            w \<in> \<W> \<and>
            s \<in> \<S> \<and> 
            su \<in> \<U>\<^sub>s \<and> 
            s \<in> fst w \<and> 
            (\<forall>um. charBy su um \<longrightarrow> (\<exists>m. m \<Colon>\<^sub>m um \<and> \<beta> m = s \<and> m \<in> snd w))"
*)
definition s_subsumes :: "'su \<Rightarrow> 'su \<Rightarrow> bool" (infix "\<preceq>\<^sub>s" 75) where
  "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2 \<equiv> U\<^sub>1 \<in> \<U>\<^sub>s \<and> U\<^sub>2 \<in> \<U>\<^sub>s \<and> (\<forall>s w. s \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<longrightarrow> s \<Colon>\<^bsub>w\<^esub> U\<^sub>2)"  

definition char_of :: "'su \<Rightarrow> 'mu set" where
  "char_of U \<equiv> { um . charBy U um }"

end

locale substantial_universal_structure =
  substantial_universal_structure_defs +
  assumes
    s_iof_scope: "s \<Colon>\<^bsub>w\<^esub> U \<Longrightarrow> s \<in> \<S> \<and> w \<in> \<W> \<and> U \<in> \<U>\<^sub>s" and
    every_subst_is_an_instance: "s \<in> \<S> \<Longrightarrow> \<exists>w U. s \<in> fst w \<and> s \<Colon>\<^bsub>w\<^esub> U" and
    every_subst_univ_has_an_instance: "U \<in> \<U>\<^sub>s \<Longrightarrow> \<exists>s w. s \<Colon>\<^bsub>w\<^esub> U" and
    unique_char: "\<lbrakk> U\<^sub>1 \<in> \<U>\<^sub>s ; U\<^sub>2 \<in> \<U>\<^sub>s ; char_of U\<^sub>1 = char_of U\<^sub>2 \<rbrakk> \<Longrightarrow> U\<^sub>1 = U\<^sub>2"
begin

lemma  univ_eq: 
  assumes "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s" "\<And>s w. s \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<longleftrightarrow> s \<Colon>\<^bsub>w\<^esub> U\<^sub>2"
  shows "U\<^sub>1 = U\<^sub>2" 
  apply (intro unique_char assms(1,2))
  by (auto simp add: char_of_def charBy_def assms)

lemma subst_univ_char_by_eq: 
  assumes "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s"
     "\<forall>um. charBy U\<^sub>1 um \<longleftrightarrow> charBy U\<^sub>2 um"
  shows "U\<^sub>1 = U\<^sub>2"
  apply (intro unique_char assms(1,2))
  using assms(3) by (simp add: char_of_def assms(1,2))

lemma Top_ex: "Top \<in> \<U>\<^sub>s"
proof -
  obtain U where A: "U \<in> \<U>\<^sub>s" "\<And>um.  \<not> charBy U um"
    using top_subst_univ_exists by metis
  let ?P = "\<lambda>U. U \<in> \<U>\<^sub>s \<and> (\<forall>um. \<not> charBy U um)"
  have B: "?P U" using A by auto
  have C: "\<And>U'. ?P U' \<Longrightarrow> U' = U"
    by (intro subst_univ_char_by_eq A allI ; (simp add: A(2))?)
  have D: "\<exists>!U. ?P U" using B C by metis
  then have E: "(THE U. ?P U) = U" using D B by auto
  then have F: "Top = U" using Top_def by auto
  then show ?thesis using A(1) by simp
qed

lemma s_subsumes_scope: "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2 \<Longrightarrow> U\<^sub>1 \<in> \<U>\<^sub>s \<and> U\<^sub>2 \<in> \<U>\<^sub>s"
  using s_subsumes_def by auto

lemma s_subsumes_refl: "U \<in> \<U>\<^sub>s \<Longrightarrow> U \<preceq>\<^sub>s U"
  using s_subsumes_def by auto

lemma s_subsumes_charBy: 
  assumes "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2" 
  shows "char_of U\<^sub>2 \<subseteq> char_of U\<^sub>1"
  apply (intro subsetI ; simp add: char_of_def charBy_def ; safe)
  subgoal using assms s_subsumes_def by auto
  subgoal premises P for x s Ss Ms
    using P[rule_format] assms[simplified s_subsumes_def,simplified]
    by blast
  done
  
lemma s_subsumes_antisym: 
  assumes "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2" "U\<^sub>2 \<preceq>\<^sub>s U\<^sub>1"
  shows "U\<^sub>1 = U\<^sub>2"
  using assms s_subsumes_scope unique_char s_subsumes_charBy by blast

lemma s_subsumes_trans:
  assumes "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>2" "U\<^sub>2 \<preceq>\<^sub>s U\<^sub>3"
  shows "U\<^sub>1 \<preceq>\<^sub>s U\<^sub>3"
  using assms 
  by (simp add: s_subsumes_def)
 

end
    
record 's signature =
  rel_names :: "'s set" ("\<R>\<index>")
  rel_arity :: "'s \<Rightarrow> nat" ("Arity\<index>")

locale signature =
  fixes S :: "('s,'x) signature_scheme" (structure)
  assumes
    rel_names_finite: "finite \<R>" and
    rel_arity_nz: "R \<in> \<R> \<Longrightarrow> 0 < Arity R"

datatype 'v Value = V_Unknown | V_True 'v | V_False

record ('s,'i,'v) individual_structure = "'s signature" +
  individuals :: "'i set" ("\<I>\<index>")
  relations :: "'s \<Rightarrow> 'i list \<Rightarrow> 'v Value" ("REL\<index>")

locale individual_structure = 
    signature S
  for S :: "('s,'i,'v) individual_structure" (structure) +
  assumes
    at_least_one_individual: "\<I> \<noteq> {}" and
    finite_individuals: "finite \<I>" and
    rels_arity: "\<lbrakk> R \<in> \<R> ; REL R X = V_True v \<rbrakk> \<Longrightarrow> length X = Arity R" and
    rels_domain: "\<lbrakk> R \<in> \<R> ; REL R X = V_True v \<rbrakk> \<Longrightarrow> set X \<subseteq> \<I>" and
    rels_irrefl: "\<lbrakk> R \<in> \<R> ; REL R X = V_True v \<rbrakk> \<Longrightarrow> distinct X"
begin

end

locale morphism =
    src: individual_structure where S = \<S> +
    tgt: individual_structure where S = \<T> 
  for \<S> :: "('s,'i\<^sub>1,'v) individual_structure" and
      \<T> :: "('s,'i\<^sub>2,'v) individual_structure" +
  fixes \<phi> :: "'i\<^sub>1 \<Rightarrow> 'i\<^sub>2"
  assumes    
    preserve_individuals: "x \<in> \<I>\<^bsub>\<S>\<^esub> \<Longrightarrow> \<phi> x \<in> \<I>\<^bsub>\<T>\<^esub>" and
    preserve_signature: "\<R>\<^bsub>\<S>\<^esub> \<subseteq> \<R>\<^bsub>\<T>\<^esub>" and
    preserve_arity: "R \<in> \<R>\<^bsub>\<S>\<^esub> \<Longrightarrow> Arity\<^bsub>\<T>\<^esub> R = Arity\<^bsub>\<S>\<^esub> R" and    
    preserve_relations: "\<lbrakk> R \<in> \<R>\<^bsub>\<S>\<^esub> ; REL\<^bsub>\<S>\<^esub> R X \<noteq> V_Unknown \<rbrakk>  \<Longrightarrow> 
                            REL\<^bsub>\<T>\<^esub> R (map \<phi> X) = REL\<^bsub>\<S>\<^esub> R X"


locale inclusion = morphism +
  assumes
    morph_id[simp]: "x \<in> \<I>\<^bsub>\<S>\<^esub> \<Longrightarrow> \<phi> x = x"

locale endomorphism = 
  morphism where \<S> = S and \<T> = S
  for S :: "('s,'i,'v) individual_structure" (structure)

locale permutation = endomorphism +
  assumes morph_is_surj: "\<phi> ` \<I> = \<I>"
begin

lemma morph_is_inj: "inj_on \<phi> \<I>"
  using morph_is_surj src.finite_individuals  
  by (simp add: finite_surj_inj)

lemma morph_bij: "bij_betw \<phi> \<I> \<I>"
  using morph_is_surj morph_is_inj 
  by (simp add: bij_betw_imageI)

end

definition morph_arrows ::  
  "('s,'i\<^sub>1,'v) individual_structure \<Rightarrow> 
   ('s,'i\<^sub>2,'v) individual_structure \<Rightarrow> 
   ('i\<^sub>1 \<Rightarrow> 'i\<^sub>2) set" (infix "\<longmapsto>" 70)
  where "A \<longmapsto> B \<equiv> { \<phi> . morphism A B \<phi> }"

context individual_structure
begin

definition permutations :: "('i \<Rightarrow> 'i) set" ("\<Pi>") where
  "\<Pi> \<equiv> { \<phi> . permutation \<phi> S }"

definition det_individuals :: "'i set" ("\<I>\<^sup>d\<^sup>e\<^sup>t") where
  "\<I>\<^sup>d\<^sup>e\<^sup>t \<equiv> { x . x \<in> \<I> \<and> (\<forall>\<phi> \<in> \<Pi>. \<phi> x  = x) }"

end

record ('s,'u) universal_structure = "'s signature" +
  universals :: "'u set" ("\<U>\<index>")
  specializes :: "'u \<Rightarrow> 'u \<Rightarrow> bool" (infix "\<preceq>\<index>" 75)
  characterization :: "'u \<Rightarrow> ('s \<times> nat) set" ("Char\<index>")

locale universal_structure = 
    signature S 
  for S :: "('s,'u) universal_structure" +
  assumes
    non_empty_universals: "\<U> \<noteq> {}"

end
  

*)

end