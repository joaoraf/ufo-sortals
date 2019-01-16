theory Sortals2
  imports Main
begin

sledgehammer_params [provers=vampire cvc4 spass z3,timeout=60]

record 'i inherence_structure =
  individuals :: "'i set" ("\<I>\<index>")
  inheres_in :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infix "\<triangleleft>\<index>" 75)

lemma inherence_structure_eqI:
  fixes A B :: "'i inherence_structure"
  assumes "\<I>\<^bsub>A\<^esub> = \<I>\<^bsub>B\<^esub>" "(\<triangleleft>\<^bsub>A\<^esub>) = (\<triangleleft>\<^bsub>B\<^esub>)"
  shows "A = B"
  using assms by auto

definition substantials :: "('i,'xtra) inherence_structure_scheme \<Rightarrow> 'i set" ("\<S>\<index>") where
    "\<S> \<equiv> { x . x \<in> \<I> \<and> (\<forall>y. \<not> x \<triangleleft> y) }"
  for IS :: "('i,'xtra) inherence_structure_scheme" (structure)

lemma substantialsI[intro!]:
  fixes IS :: "('i,'xtra) inherence_structure_scheme" (structure)
  assumes "x \<in> \<I>" "\<And>y. \<not> x \<triangleleft> y"
  shows "x \<in> \<S>"
  using assms by (auto simp: substantials_def)

lemma substantialsE[elim!]:
  fixes IS :: "('i,'xtra) inherence_structure_scheme" (structure)
  assumes "x \<in> \<S>"
  obtains "x \<in> \<I>" "\<And>y. \<not> x \<triangleleft> y"
  using assms by (auto simp: substantials_def)

definition moments :: "('i,'xtra) inherence_structure_scheme \<Rightarrow> 'i set" ("\<M>\<index>") where
    "\<M> \<equiv> { x . x \<in> \<I> \<and> (\<exists>y. x \<triangleleft> y) }"
  for IS :: "('i,'xtra) inherence_structure_scheme" (structure)

definition bearer :: "('i,'xtra) inherence_structure_scheme \<Rightarrow> 'i \<Rightarrow> 'i" ("\<beta>\<index>") where
    "\<beta> x \<equiv> if (\<exists>y. x \<triangleleft> y) then (THE y. x \<triangleleft> y) else undefined"
  for IS :: "('i,'xtra) inherence_structure_scheme" (structure)

locale inherence_structure =
  fixes IS :: "('i,'xtra) inherence_structure_scheme" (structure)
  assumes
    undefined_not_in_individuals: "undefined \<notin> \<I>" and
    inheres_in_scope: "x \<triangleleft> y \<Longrightarrow> x \<in> \<I> \<and> y \<in> \<I>" and
    inheres_in_sep: "x \<triangleleft> y \<Longrightarrow> \<not> y \<triangleleft> z \<and> \<not> z \<triangleleft> x" and
    inheres_in_single: "\<lbrakk> x \<triangleleft> y ; x \<triangleleft> z \<rbrakk> \<Longrightarrow> y = z" 
begin

lemma momentsI[intro]:  
  assumes "x \<triangleleft> y"
  shows "x \<in> \<M>"
  using assms inheres_in_scope by (auto simp: moments_def)

lemma momentsE[elim]:
  assumes "x \<in> \<M>"
  obtains y where "x \<triangleleft> y"
  using assms by (auto simp: moments_def)

lemma substantialsI2[intro]:
  assumes "x \<triangleleft> y"
  shows "y \<in> \<S>"
  using inheres_in_sep inheres_in_scope assms substantialsI by metis

lemma individuals_moments_substantials: "\<I> = \<S> \<union> \<M>"
  using inheres_in_scope by (auto simp: substantials_def moments_def)

lemma substantials_moments_disj: "\<S> \<inter> \<M> = {}"
  by (auto simp: substantials_def moments_def)

lemma individuals_cases[cases set]:
  assumes "x \<in> \<I>"
  obtains (substantial) "x \<in> \<S>" "x \<notin> \<M>" | (moment) "x \<in> \<M>" "x \<notin> \<S>"
  using assms individuals_moments_substantials substantials_moments_disj by blast

lemma bearer_eq:
  assumes "x \<triangleleft> y"
  shows "\<beta> x = y"
  using assms inheres_in_single 
  by (auto simp: bearer_def)

lemma bearerI[intro]:
  assumes "x \<in> \<M>" "\<And>y. x \<triangleleft> y \<Longrightarrow> P y"
  shows "P (\<beta> x)"
  using assms apply (auto simp: bearer_def)
  using momentsE assms 
  by (simp add: inheres_in_single the_equality)

end

record 'i existence_structure = "'i inherence_structure" +
  worlds :: "'i set set" ("\<W>\<index>")

lemma existence_structure_eqI:
  fixes A B :: "'i existence_structure"
  assumes "inherence_structure.truncate A = inherence_structure.truncate B"
          "\<W>\<^bsub>A\<^esub> = \<W>\<^bsub>B\<^esub>"
  shows "A = B"
proof -
  have A: "A = inherence_structure.extend (inherence_structure.truncate A) (\<lparr>worlds = worlds A \<rparr>)"
    by (auto simp: inherence_structure.extend_def inherence_structure.truncate_def)

  have B: "B = inherence_structure.extend (inherence_structure.truncate B) (\<lparr>worlds = worlds B \<rparr>)"
    by (auto simp: inherence_structure.extend_def inherence_structure.truncate_def)

  show "A = B"
    by (subst A ; subst B ; simp add: assms)
qed    


definition ed :: "('i,'xtra) existence_structure_scheme \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> bool" ("ed\<index>") where
  "ed x y \<equiv> x \<in> \<I> \<and> y \<in> \<I> \<and> (\<forall>w \<in> \<W>. x \<in> w \<longrightarrow> y \<in> w)"
  for IS :: "('i,'xtra) existence_structure_scheme" (structure) 

locale existence_structure =
  inherence_structure IS
  for IS :: "('i,'xtra) existence_structure_scheme" (structure) +
  assumes
    empty_world: "{} \<in> \<W>" and
    worlds_are_made_of_individuals: "w \<in> \<W> \<Longrightarrow> w \<subseteq> \<I>" and
    every_individual_exists_somewhere: "x \<in> \<I> \<Longrightarrow> \<exists>w \<in> \<W>. x \<in> w" and
    inherence_imp_ed: "x \<triangleleft> y \<Longrightarrow> ed x y"

record 'i individual_structure = "'i existence_structure" +
  ext_dep_upon :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infix "\<rightleftharpoons>\<index>" 75)

lemma individual_structure_eqI:
  fixes A B :: "'i individual_structure"
  assumes "existence_structure.truncate A = existence_structure.truncate B"
          "(\<rightleftharpoons>\<^bsub>A\<^esub>) = (\<rightleftharpoons>\<^bsub>B\<^esub>)"
  shows "A = B"
proof -
  have A: "A = existence_structure.extend (existence_structure.truncate A) (\<lparr>ext_dep_upon = ext_dep_upon A \<rparr>)"
    by (auto simp: existence_structure.extend_def existence_structure.truncate_def)

  have B: "B = existence_structure.extend (existence_structure.truncate B) (\<lparr>ext_dep_upon = ext_dep_upon B \<rparr>)"
    by (auto simp: existence_structure.extend_def existence_structure.truncate_def)

  show "A = B"
    by (subst A ; subst B ; simp add: existence_structure.extend_def assms)
qed    

locale individual_structure =
  existence_structure IS 
  for IS :: "('i,'xtra) individual_structure_scheme" (structure) +
  assumes
    ext_dep_scope: "x \<rightleftharpoons> y \<Longrightarrow> x \<in> \<M> \<and> y \<in> \<M>" and
    ext_dep_diff_bearers: "x \<rightleftharpoons> y \<Longrightarrow> \<beta> x \<noteq> \<beta> y" and 
    ext_dep_imp_ed: "x \<rightleftharpoons> y \<Longrightarrow> ed x y" and
    ext_dep_irrefl: "\<not> x \<rightleftharpoons> x" and
    ext_dep_sym: "x \<rightleftharpoons> y \<Longrightarrow> y \<rightleftharpoons> x" and
    ext_dep_trans: "\<lbrakk> x \<rightleftharpoons> y ; y \<rightleftharpoons> z ; x \<noteq> z \<rbrakk> \<Longrightarrow> x \<rightleftharpoons> z" 

locale individual_structure_morphism =
  src: individual_structure src +
  tgt: individual_structure tgt for
    src :: "('i1,'xtra1) individual_structure_scheme" and
    tgt :: "('i2,'xtra2) individual_structure_scheme" +
  fixes m :: "'i1 \<Rightarrow> 'i2" 
  assumes
    m_scope: "x \<in> \<S>\<^bsub>src\<^esub> \<and> m x \<in> \<S>\<^bsub>tgt\<^esub> \<or> x \<in> \<M>\<^bsub>src\<^esub> \<and> m x \<in> \<M>\<^bsub>tgt\<^esub> \<or> x \<notin> \<I>\<^bsub>src\<^esub> \<and> m x = undefined" and
    m_preserve_inherence: "m x \<triangleleft>\<^bsub>tgt\<^esub> m y \<longleftrightarrow> x \<triangleleft>\<^bsub>src\<^esub> y" and
(*    m_preserve_worlds: 
      "\<W>\<^bsub>src\<^esub> = { Y | X Y w . w \<in> \<W>\<^bsub>tgt\<^esub> \<and> Y \<subseteq> \<I>\<^bsub>src\<^esub> \<and> ((m ` \<I>\<^bsub>src\<^esub>) \<inter> X) = {} \<and> ((m ` Y) \<union> X) = w}" and      *)
    m_ext_dep_closed: "m x \<rightleftharpoons>\<^bsub>tgt\<^esub> y\<^sub>1 \<longleftrightarrow> (\<exists>y\<^sub>2. y\<^sub>1 = m y\<^sub>2 \<and> x \<rightleftharpoons>\<^bsub>src\<^esub> y\<^sub>2)"
begin

end

record 'u universal_structure =
(* universals :: "'u set" ("\<U>\<index>") *)
  substantial_universals :: "'u set" ("\<U>\<^sub>s\<index>")
  moment_universals :: "'u set" ("\<U>\<^sub>m\<index>")
(*  characterized_by :: "'u \<Rightarrow> 'u \<Rightarrow> bool" ("charBy\<index>") *)
  subsumes :: "'u \<Rightarrow> 'u \<Rightarrow> bool" (infix "\<preceq>\<index>" 75)

(* definition moment_universals  ("\<U>\<^sub>m\<index>") where
  "\<U>\<^sub>m \<equiv> { U | U U' . charBy U' U }"
  for US (structure)

definition substantial_universals  ("\<U>\<^sub>s\<index>") where
  "\<U>\<^sub>s \<equiv> { U . U \<in> \<U> \<and> (\<forall>U' . \<not> charBy U' U) }"
  for US (structure) *)

definition universals ("\<U>\<index>") where
  "\<U> \<equiv> \<U>\<^sub>m \<union> \<U>\<^sub>s" for US (structure)

definition top_subst_univ ("\<top>\<^sub>s\<index>") where
  "\<top>\<^sub>s \<equiv> THE U. \<forall>U' \<in> \<U>\<^sub>s. U' \<preceq> U"
  for US (structure)

locale universal_structure =
  fixes US :: "('u,'xtra) universal_structure_scheme" (structure)
  assumes
(*    finite_univs: "finite \<U>" and *)
    finite_subt_univs: "finite \<U>\<^sub>s" and
    finite_moment_univs: "finite \<U>\<^sub>m" and
    subst_moment_univs_disj: "\<U>\<^sub>s \<inter> \<U>\<^sub>m = {}" and
(*    characterized_by_scope: "charBy Us Um \<Longrightarrow> Us \<in> \<U> \<and> Um \<in> \<U>" and *)
    at_least_one_subst_univ: "\<U>\<^sub>s \<noteq> {}" and
    top_substantial_ex: "\<exists>U. \<forall>U' \<in> \<U>\<^sub>s. U' \<preceq> U" and
    subsumes_scope: "U \<preceq> U' \<Longrightarrow> U \<in> \<U>\<^sub>s \<and> U' \<in> \<U>\<^sub>s \<or> U \<in> \<U>\<^sub>m \<and> U' \<in> \<U>\<^sub>m" and
    subsumes_refl: "U \<in> \<U> \<Longrightarrow> U \<preceq> U" and
    subsumes_antisym: "\<lbrakk> U \<preceq> U' ; U' \<preceq> U \<rbrakk> \<Longrightarrow> U = U'" and
    subsumes_trans: "\<lbrakk> U\<^sub>1 \<preceq> U\<^sub>2 ; U\<^sub>2 \<preceq> U\<^sub>3 \<rbrakk> \<Longrightarrow> U\<^sub>1 \<preceq> U\<^sub>3" (* and
    subsumes_char_by: "\<lbrakk> U\<^sub>1 \<preceq> U\<^sub>2 ; charBy U\<^sub>2 U\<^sub>3 \<rbrakk> \<Longrightarrow> \<exists>U\<^sub>4. U\<^sub>4 \<preceq> U\<^sub>3 \<and> charBy U\<^sub>1 U\<^sub>4" and
    char_by_subsumes: "\<lbrakk> U\<^sub>1 \<in> \<U>\<^sub>s ; U\<^sub>2 \<in> \<U>\<^sub>s ; \<forall>U. charBy U\<^sub>1 U \<longrightarrow> charBy U\<^sub>2 U \<rbrakk> \<Longrightarrow> U\<^sub>1 \<preceq> U\<^sub>2" *)
begin

lemma top_eq:
  assumes "\<And>U'. U' \<in> \<U>\<^sub>s \<Longrightarrow> U' \<preceq> U"
  shows "\<top>\<^sub>s = U"
  apply (simp add: top_subst_univ_def ; intro the1_equality ex_ex1I top_substantial_ex ballI assms ; simp?)  
  by (metis subsumes_antisym at_least_one_subst_univ 
      disjoint_iff_not_equal finite.cases 
      finite_subt_univs insertI1 
      subst_moment_univs_disj subsumes_scope)

lemma top_I:
  assumes "\<And>U. \<forall>U' \<in> \<U>\<^sub>s. U' \<preceq> U \<Longrightarrow> P U"
  shows "P \<top>\<^sub>s"
  apply (simp add: top_subst_univ_def ; rule the1I2 ; (intro ex_ex1I top_substantial_ex)?)
  subgoal using top_eq by blast 
  subgoal using assms by blast
  done

lemma top_subsumes: "U \<in> \<U>\<^sub>s \<Longrightarrow> U \<preceq> \<top>\<^sub>s" using top_I by blast

lemma top_subst_univ: "\<top>\<^sub>s \<in> \<U>\<^sub>s" 
  using top_I at_least_one_subst_univ 
  by (metis disjoint_iff_not_equal ex_in_conv subst_moment_univs_disj subsumes_scope)

end

locale universal_sub_structure =
  universal_structure US\<^sub>1 +
  universal_structure US\<^sub>2
  for US\<^sub>1 :: "'u universal_structure" and
        US\<^sub>2 :: "'u universal_structure" +
  assumes
    subst_univs_subset: "\<U>\<^sub>s\<^bsub>US\<^sub>1\<^esub> \<subseteq> \<U>\<^sub>s\<^bsub>US\<^sub>2\<^esub>" and
    moment_univs_subset: "\<U>\<^sub>m\<^bsub>US\<^sub>1\<^esub> \<subseteq> \<U>\<^sub>m\<^bsub>US\<^sub>2\<^esub>" and
(*    char_by_respected: "U\<^sub>1 \<in> \<U>\<^bsub>US\<^sub>1\<^esub> \<Longrightarrow> charBy\<^bsub>US\<^sub>1\<^esub> U\<^sub>1 U\<^sub>2 \<longleftrightarrow> charBy\<^bsub>US\<^sub>2\<^esub> U\<^sub>1 U\<^sub>2" and *)
    subsumption_respected: "U\<^sub>1 \<preceq>\<^bsub>US\<^sub>1\<^esub> U\<^sub>2 \<Longrightarrow> U\<^sub>1 \<preceq>\<^bsub>US\<^sub>2\<^esub> U\<^sub>2" and
    subsumption_up_respected: "\<lbrakk> U\<^sub>1 \<in> \<U>\<^bsub>US\<^sub>1\<^esub> ; U\<^sub>1 \<preceq>\<^bsub>US\<^sub>2\<^esub> U\<^sub>2 \<rbrakk> \<Longrightarrow> U\<^sub>1 \<preceq>\<^bsub>US\<^sub>1\<^esub> U\<^sub>2" 

abbreviation univ_sub_structure (infix "\<sqsubseteq>" 75) where
  "US\<^sub>1 \<sqsubseteq> US\<^sub>2 \<equiv> universal_sub_structure US\<^sub>1 US\<^sub>2"

lemma univ_sub_structure_refl: 
  assumes "universal_structure US"
  shows "US \<sqsubseteq> US"
proof -
  interpret universal_structure US 
    using assms by simp
  show ?thesis
    by (unfold_locales ; auto)
qed

lemma universal_structure_eqI:
  fixes X :: "'u universal_structure" and
        Y :: "'u universal_structure" 
  assumes "universal_structure X" "universal_structure Y"
          "\<U>\<^sub>s\<^bsub>X\<^esub> = \<U>\<^sub>s\<^bsub>Y\<^esub>" "\<U>\<^sub>m\<^bsub>X\<^esub> = \<U>\<^sub>m\<^bsub>Y\<^esub>"
   (*       "charBy\<^bsub>X\<^esub> = charBy\<^bsub>Y\<^esub>" *)
          "(\<preceq>\<^bsub>X\<^esub>) = (\<preceq>\<^bsub>Y\<^esub>)"
  shows "X = Y"
proof -
  note assms[simp]
  interpret X: universal_structure X by simp
  interpret Y: universal_structure Y by simp
  show ?thesis
    apply (cases X ; cases Y ; simp)    
    using X.subsumes_refl X.subsumes_scope Y.subsumes_refl Y.subsumes_scope assms by auto
qed

lemma univ_sub_structure_antisym:
  assumes "US\<^sub>1 \<sqsubseteq> US\<^sub>2" "US\<^sub>2 \<sqsubseteq> US\<^sub>1"
  shows "US\<^sub>1 = US\<^sub>2"
proof -
  interpret SS1: universal_sub_structure US\<^sub>1 US\<^sub>2 using assms(1) by simp
  interpret SS2: universal_sub_structure US\<^sub>2 US\<^sub>1 using assms(2) by simp
  interpret US1: universal_structure US\<^sub>1 
    using SS1.universal_sub_structure_axioms universal_sub_structure_def by blast 
  interpret US2: universal_structure US\<^sub>2 
    using SS2.universal_sub_structure_axioms universal_sub_structure_def by blast 
  show ?thesis
    apply (intro universal_structure_eqI)
    subgoal using SS1.universal_sub_structure_axioms universal_sub_structure_def by blast
    subgoal by (simp add: SS1.universal_structure_axioms)
    subgoal using SS1.subst_univs_subset SS2.subst_univs_subset by blast
    subgoal using SS1.moment_univs_subset SS2.moment_univs_subset by blast
    using SS1.subsumption_respected SS2.subsumption_respected by blast
qed

lemma univ_sub_structure_trans:
  assumes "US\<^sub>1 \<sqsubseteq> US\<^sub>2" "US\<^sub>2 \<sqsubseteq> US\<^sub>3"
  shows "US\<^sub>1 \<sqsubseteq> US\<^sub>3"
proof -
  interpret SS12: universal_sub_structure US\<^sub>1 US\<^sub>2 using assms(1) by simp
  interpret SS23: universal_sub_structure US\<^sub>2 US\<^sub>3 using assms(2) by simp
  interpret US1: universal_structure US\<^sub>1 
    using SS12.universal_sub_structure_axioms universal_sub_structure_def by blast 
  interpret US2: universal_structure US\<^sub>2 
    using SS12.universal_sub_structure_axioms universal_sub_structure_def by blast 
  interpret US3: universal_structure US\<^sub>3 
    using SS23.universal_sub_structure_axioms universal_sub_structure_def by blast
  show ?thesis
    apply (unfold_locales)
    subgoal using SS12.subst_univs_subset SS23.subst_univs_subset by auto
    subgoal using SS12.moment_univs_subset SS23.moment_univs_subset by blast
    subgoal by (simp add: SS12.subsumption_respected SS23.subsumption_respected) 
    subgoal by (metis (no_types, lifting) SS12.subsumption_respected SS12.universal_sub_structure_axioms SS23.universal_sub_structure_axioms UnCI universal_structure.subsumes_refl universal_structure.subsumes_scope universal_sub_structure.axioms(1) universal_sub_structure.subsumption_up_respected universals_def)
    done
qed

definition triv_univ_sub_structure ("\<bottom>\<^sub>s\<^sub>s\<index>") where
  "\<bottom>\<^sub>s\<^sub>s = \<lparr> substantial_universals = {\<top>\<^sub>s}, moment_universals = {},
          subsumes = \<lambda>x y. x = \<top>\<^sub>s \<and> y = \<top>\<^sub>s \<rparr>"
  for US (structure)

interpretation universal_structure "\<bottom>\<^sub>s\<^sub>s\<^bsub>US\<^esub>"
  apply (unfold_locales ; auto simp: triv_univ_sub_structure_def)  
  by (simp add: universals_def)

lemma triv_sub_structure: 
  assumes "universal_structure US"
  shows "\<bottom>\<^sub>s\<^sub>s\<^bsub>US\<^esub> \<sqsubseteq> US"
proof -
  interpret universal_structure US using assms by simp
  show ?thesis
    apply (unfold_locales ; clarsimp simp: triv_univ_sub_structure_def)
    subgoal by (simp add: local.top_subst_univ)
    subgoal by (simp add: local.top_subst_univ local.top_subsumes) 
    subgoal by (metis (no_types, lifting) UnE disjoint_iff_not_equal empty_iff insert_iff local.subst_moment_univs_disj local.subsumes_antisym local.top_subst_univ local.top_subsumes local.universal_structure_axioms universal_structure.select_convs(1) universal_structure.select_convs(2) universal_structure.subsumes_scope universals_def)
    done
qed

record ('i,'u) instantiation_structure =
  indiv_structure :: "'i individual_structure" ("\<I>\<S>\<index>")
  univ_structure :: "'u universal_structure" ("\<U>\<S>\<index>")    
  iof :: "'i \<Rightarrow> 'i set \<Rightarrow> 'u \<Rightarrow> bool" ("_ \<Colon>\<index>\<^bsub>_\<^esub> _" [76,1,76] 75)

definition miof :: "('i,'u) instantiation_structure \<Rightarrow> 'i \<Rightarrow> 'u \<Rightarrow> bool" (infix "\<Colon>\<^sub>\<diamondop>\<index>" 75) where
  "x \<Colon>\<^sub>\<diamondop> u \<equiv> \<exists>w \<in> worlds \<I>\<S>. x \<Colon>\<^bsub>w\<^esub> u"
  for IS (structure)
 
lemma instantiation_structure_eqI:
  fixes A B :: "('i,'u) instantiation_structure"
  assumes "\<I>\<S>\<^bsub>A\<^esub> = \<I>\<S>\<^bsub>B\<^esub>" "\<U>\<S>\<^bsub>A\<^esub> = \<U>\<S>\<^bsub>B\<^esub>" "iof A = iof B"
  shows "A = B"
  using assms by (cases A ; cases B  ; simp)

definition characterized_by  ("char'_by\<index>") where
  "char_by U\<^sub>1 U\<^sub>2 \<equiv> U\<^sub>1 \<in> \<U>\<^sub>s\<^bsub>\<U>\<S>\<^esub> \<and> (\<forall>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<longrightarrow> (\<exists>m. m \<Colon>\<^bsub>w\<^esub> U\<^sub>2 \<and> m \<triangleleft>\<^bsub>\<I>\<S>\<^esub> x))"
  for IS (structure)

locale instantiation_structure_defs =
  fixes IS :: "('i,'u) instantiation_structure" (structure) 
begin

no_notation individuals ("\<I>\<index>")
no_notation substantials ("\<S>\<index>")
no_notation moments ("\<M>\<index>")
no_notation inheres_in (infix "\<triangleleft>\<index>" 75)
no_notation bearer ("\<beta>\<index>") 
no_notation worlds ("\<W>\<index>")

abbreviation is_individuals ("\<I>") where "\<I> \<equiv> individuals \<I>\<S>"
abbreviation is_substantials ("\<S>") where "\<S> \<equiv> substantials \<I>\<S>"
abbreviation is_moments ("\<M>") where "\<M> \<equiv> moments \<I>\<S>"
abbreviation is_inheres_in (infix "\<triangleleft>" 75) where "x \<triangleleft> y \<equiv> inheres_in \<I>\<S> x y"
abbreviation is_bearer ("\<beta>") where "\<beta> \<equiv> bearer \<I>\<S>"
abbreviation is_worlds ("\<W>") where "\<W> \<equiv> worlds \<I>\<S>"

no_notation universals ("\<U>\<index>")
no_notation substantial_universals ("\<U>\<^sub>s\<index>")
no_notation subsumes (infix "\<preceq>\<index>" 75)
no_notation moment_universals ("\<U>\<^sub>m\<index>") 

abbreviation is_universals ("\<U>") where "\<U> \<equiv> universals \<U>\<S>"
abbreviation is_substantial_universals ("\<U>\<^sub>s") where "\<U>\<^sub>s \<equiv> substantial_universals \<U>\<S>"
abbreviation is_moment_universals ("\<U>\<^sub>m") where "\<U>\<^sub>m \<equiv> moment_universals \<U>\<S>"
abbreviation is_subsumes (infix "\<preceq>" 75) where "(\<preceq>) \<equiv> subsumes \<U>\<S>"


definition rigid where
  "rigid U \<equiv> U \<in> \<U> \<and> (\<forall>x w\<^sub>1. \<forall>w\<^sub>2 \<in> \<W>. x \<Colon>\<^bsub>w\<^sub>1\<^esub> U \<and> x \<in> w\<^sub>2 \<longrightarrow> x \<Colon>\<^bsub>w\<^sub>2\<^esub> U)"

definition non_rigid where
  "non_rigid U \<equiv> U \<in> \<U> \<and> (\<exists>x w\<^sub>1. \<exists>w\<^sub>2 \<in> \<W>. x \<Colon>\<^bsub>w\<^sub>1\<^esub> U \<and> x \<in> w\<^sub>2 \<and> \<not> x \<Colon>\<^bsub>w\<^sub>2\<^esub> U)"

abbreviation rigid_universals ("\<U>\<^sup>R") where
  "\<U>\<^sup>R \<equiv> { U . rigid U }"

abbreviation non_rigid_universals ("\<U>\<^sup>N") where
  "\<U>\<^sup>N \<equiv> { U . non_rigid U }"

end


locale instantiation_structure =
  instantiation_structure_defs "IS" +
  individual_structure "\<I>\<S>" +
  universal_structure "\<U>\<S>"
  for IS :: "('i,'u) instantiation_structure" (structure) +
  assumes
    iof_agrees_with_subsumes: "U\<^sub>1 \<preceq> U\<^sub>2 \<longleftrightarrow> U\<^sub>1 \<in> \<U> \<and> (\<forall>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<longrightarrow> x \<Colon>\<^bsub>w\<^esub> U\<^sub>2)" and
    iof_scope: "x \<Colon>\<^bsub>w\<^esub> u \<Longrightarrow> w \<in> \<W> \<and> x \<in> w \<and> u \<in> \<U>" and
    at_least_one_instance: "U \<in> \<U> \<Longrightarrow> \<exists>x w. x \<Colon>\<^bsub>w\<^esub> U" and
    every_individual_is_iof: "\<lbrakk> w \<in> \<W> ; x \<in> w \<rbrakk> \<Longrightarrow> \<exists>U. x \<Colon>\<^bsub>w\<^esub> U" and
    iof_sep: "x \<Colon>\<^bsub>w\<^esub> u \<Longrightarrow> x \<in> \<S> \<longleftrightarrow> u \<in> \<U>\<^sub>s" and    
    iof_moment_constant: "\<lbrakk> m \<in> \<M> ; m \<Colon>\<^bsub>w\<^esub> U ; w' \<in> \<W> ; m \<in> w \<rbrakk> \<Longrightarrow> m \<Colon>\<^bsub>w'\<^esub> U" and
    unique_characterization: "\<lbrakk> U\<^sub>1 \<in> \<U>\<^sub>s ; U\<^sub>2 \<in> \<U>\<^sub>s ; \<forall>U. char_by U\<^sub>1 U \<longleftrightarrow> char_by U\<^sub>2 U \<rbrakk> \<Longrightarrow> U\<^sub>1 = U\<^sub>2" and
    moment_univ_characterizes: "U \<in> \<U>\<^sub>m \<Longrightarrow> \<exists>U' \<in> \<U>\<^sub>s. char_by U U'" and
    unique_moment_per_moment_univ: "\<lbrakk> m\<^sub>1 \<Colon>\<^bsub>w\<^esub> U' ; m\<^sub>2 \<Colon>\<^bsub>w\<^esub> U' ; m\<^sub>1 \<triangleleft> x ; m\<^sub>2 \<triangleleft> x \<rbrakk> \<Longrightarrow> m\<^sub>1 = m\<^sub>2" 
begin

lemma char_by_E[elim!]:
  assumes "char_by U\<^sub>1 U\<^sub>2"
  obtains "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>m" "\<And>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<Longrightarrow> \<exists>m. m \<Colon>\<^bsub>w\<^esub> U\<^sub>2 \<and> m \<triangleleft> x"
proof -
  obtain A: "U\<^sub>1 \<in> \<U>\<^sub>s" "\<And>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<Longrightarrow> \<exists>m. m \<Colon>\<^bsub>w\<^esub> U\<^sub>2 \<and> m \<triangleleft> x" 
    using assms by (auto simp: characterized_by_def)
  obtain x w where B: "x \<Colon>\<^bsub>w\<^esub> U\<^sub>1" 
    using A(1) at_least_one_instance 
    by (metis UnCI universals_def)
  then obtain C: "x \<in> \<I>" "w \<in> \<W>" "x \<in> w" 
    using iof_scope A(1) iof_sep by blast
  obtain m where D: "m \<Colon>\<^bsub>w\<^esub> U\<^sub>2" "m \<triangleleft> x" using A(2) B by blast
  then have "m \<in> \<M>" by auto
  then have E: "U\<^sub>2 \<in> \<U>\<^sub>m" 
    using iof_sep substantials_moments_disj momentsE inheres_in_scope
          D(1) iof_scope local.subsumes_refl local.subsumes_scope 
    by fastforce
  show ?thesis using that A E by blast
qed

lemma char_by_I[intro!]:
  assumes "U\<^sub>1 \<in> \<U>\<^sub>s" "\<And>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<Longrightarrow> \<exists>m. m \<Colon>\<^bsub>w\<^esub> U\<^sub>2 \<and> m \<triangleleft> x"
  shows "char_by U\<^sub>1 U\<^sub>2"
proof -
  obtain x w where B: "x \<Colon>\<^bsub>w\<^esub> U\<^sub>1" 
    using assms(1) at_least_one_instance 
    by (metis UnCI universals_def)
  obtain m where D: "m \<Colon>\<^bsub>w\<^esub> U\<^sub>2" "m \<triangleleft> x" using assms(2) B by blast
  then have "m \<in> \<M>" by auto
  then have E: "U\<^sub>2 \<in> \<U>\<^sub>m" 
    using iof_sep substantials_moments_disj momentsE inheres_in_scope
          D(1) iof_scope local.subsumes_refl local.subsumes_scope 
    by fastforce
  then show ?thesis
    using assms by (auto simp: characterized_by_def)
qed

lemma char_by_subsumes: 
  assumes "char_by U\<^sub>1 U\<^sub>2" "U\<^sub>2 \<preceq> U\<^sub>3"
  shows "char_by U\<^sub>1 U\<^sub>3"
proof (auto)
  obtain A: "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>m" "\<And>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<Longrightarrow> \<exists>m. m \<Colon>\<^bsub>w\<^esub> U\<^sub>2 \<and> m \<triangleleft> x"
    using assms(1) by blast
  show "U\<^sub>1 \<in> \<U>\<^sub>s" using A(1) .  
  obtain B: "U\<^sub>2 \<in> \<U>" "U\<^sub>3 \<in> \<U>" "\<And>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>2 \<Longrightarrow> x \<Colon>\<^bsub>w\<^esub> U\<^sub>3"     
    using assms(2) iof_agrees_with_subsumes
          at_least_one_instance iof_scope 
    by blast
  fix x w
  assume C:"x \<Colon>\<^bsub>w\<^esub> U\<^sub>1"
  then obtain m where D: "m \<Colon>\<^bsub>w\<^esub> U\<^sub>2" "m \<triangleleft> x" using A(3) by blast
  then have "m \<Colon>\<^bsub>w\<^esub> U\<^sub>3" using B(3) by blast
  then show "\<exists>m. m \<Colon>\<^bsub>w\<^esub> U\<^sub>3 \<and> m \<triangleleft> x" using D(2) by blast
qed

lemma subsumes_cases[cases pred]:
  assumes "U\<^sub>1 \<preceq> U\<^sub>2"
  obtains (substantial) "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>s" |
          (moment) "U\<^sub>1 \<in> \<U>\<^sub>m" "U\<^sub>2 \<in> \<U>\<^sub>m"
  using assms subsumes_scope by blast

lemma char_by_subsumes_2:
  assumes "char_by U\<^sub>1 U\<^sub>2" "U\<^sub>3 \<preceq> U\<^sub>1"
  shows "char_by U\<^sub>3 U\<^sub>2"
proof (auto)
  obtain A: "U\<^sub>1 \<in> \<U>\<^sub>s" "U\<^sub>2 \<in> \<U>\<^sub>m" "\<And>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<Longrightarrow> \<exists>m. m \<Colon>\<^bsub>w\<^esub> U\<^sub>2 \<and> m \<triangleleft> x"
    using assms(1) by blast
  show B: "U\<^sub>3 \<in> \<U>\<^sub>s" using assms(2) A subsumes_cases subst_moment_univs_disj by blast
  fix x w
  assume C: "x \<Colon>\<^bsub>w\<^esub> U\<^sub>3"
  then have "x \<Colon>\<^bsub>w\<^esub> U\<^sub>1" using assms(2) iof_agrees_with_subsumes by auto
  then show "\<exists>m. m \<Colon>\<^bsub>w\<^esub> U\<^sub>2 \<and> m \<triangleleft> x" using A(3) by simp
qed

lemma miof_I[intro]:
  assumes "x \<Colon>\<^bsub>w\<^esub> u"
  shows "x \<Colon>\<^sub>\<diamondop> u"
  using assms apply (simp add: miof_def ; intro bexI[of _ w] ; simp?)
  using iof_scope by simp

lemma miof_E[elim]:
  assumes "x \<Colon>\<^sub>\<diamondop> u"
  obtains w where "x \<Colon>\<^bsub>w\<^esub> u" 
  using assms by (auto simp: miof_def)

end

(* record ('i,'u) instantiation_refinement = 
  is_finer :: "('i,'u) instantiation_structure" ("IS\<^sub>f\<index>")
  is_coarser :: "('i,'u) instantiation_structure" ("IS\<^sub>c\<index>")

lemma instantiation_refinement_eqI:
  fixes A B :: "('i,'u) instantiation_refinement" 
  assumes "IS\<^sub>f\<^bsub>A\<^esub> = IS\<^sub>f\<^bsub>B\<^esub>" "IS\<^sub>c\<^bsub>A\<^esub> = IS\<^sub>c\<^bsub>B\<^esub>"
  shows "A = B"
  using assms by (cases A ; cases B ; simp)
*)

locale instantiation_refinement =  
  coarser: instantiation_structure "IS\<^sub>c" +
  finer: instantiation_structure "IS\<^sub>f" +
  universal_sub_structure where US\<^sub>1 = "\<U>\<S>\<^bsub>IS\<^sub>c\<^esub>" and US\<^sub>2 = "\<U>\<S>\<^bsub>IS\<^sub>f\<^esub>"
  for IS\<^sub>c IS\<^sub>f :: "('i,'u) instantiation_structure"  +
  assumes 
    same_substantials[simp]: "substantials \<I>\<S>\<^bsub>IS\<^sub>f\<^esub> = substantials \<I>\<S>\<^bsub>IS\<^sub>c\<^esub>" and
    inheres_in_embedding[simp]:"inheres_in \<I>\<S>\<^bsub>IS\<^sub>c\<^esub> x y \<longleftrightarrow> x \<in> (individuals \<I>\<S>\<^bsub>IS\<^sub>c\<^esub>) \<and> y \<in> (individuals \<I>\<S>\<^bsub>IS\<^sub>c\<^esub>) \<and> inheres_in \<I>\<S>\<^bsub>IS\<^sub>f\<^esub> x y" and
    worlds_embedding[simp]: "worlds \<I>\<S>\<^bsub>IS\<^sub>c\<^esub> = { w \<inter> individuals \<I>\<S>\<^bsub>IS\<^sub>c\<^esub> | w . w \<in> worlds \<I>\<S>\<^bsub>IS\<^sub>f\<^esub> }" and
    iof_embedding[simp]: "x \<Colon>\<^bsub>IS\<^sub>c\<^esub>\<^bsub>w\<^esub> U \<longleftrightarrow> U \<in> (universals (\<U>\<S>\<^bsub>IS\<^sub>c\<^esub>)) \<and> x \<Colon>\<^bsub>IS\<^sub>f\<^esub>\<^bsub>w\<^esub> U"
begin

lemma universals_subset: "universals (\<U>\<S>\<^bsub>IS\<^sub>c\<^esub>) \<subseteq> universals (\<U>\<S>\<^bsub>IS\<^sub>f\<^esub>)"  
  by (simp add: le_supI1 le_supI2 moment_univs_subset subst_univs_subset universals_def)

lemma instantiation_structure_eqI2:
  assumes "universals (\<U>\<S>\<^bsub>IS\<^sub>f\<^esub>) \<subseteq> universals (\<U>\<S>\<^bsub>IS\<^sub>c\<^esub>)"
  shows "IS\<^sub>c = IS\<^sub>f"  
  supply A[simp] = equalityI[OF universals_subset assms]  
  apply (intro instantiation_structure_eqI individual_structure_eqI existence_structure_eqI inherence_structure_eqI)
  apply (auto  simp: inherence_structure.truncate_def existence_structure.truncate_def assms finer.iof_scope  intro!: ext universal_structure_eqI)
  subgoal G1 for x using finer.individuals_moments_substantials finer.inheres_in_scope by auto
  subgoal G2 for x 
    by (metis assms coarser.iof_scope coarser.worlds_are_made_of_individuals finer.every_individual_exists_somewhere finer.every_individual_is_iof finer.iof_scope instantiation_refinement.iof_embedding instantiation_refinement_axioms subsetCE) 
  subgoal G3 for x y by (simp add: G2 finer.inheres_in_scope) 
  subgoal G4 for x y by (simp add: G2 finer.inheres_in_scope) 
  subgoal G5 for x by (metis (no_types, lifting) G2 Int_absorb2 finer.worlds_are_made_of_individuals subset_iff)
  subgoal G6 for x using G2 finer.worlds_are_made_of_individuals by auto
  subgoal G7 for x y by (metis (mono_tags, hide_lams) G1 IntD2 coarser.bearerI coarser.ext_dep_scope coarser.inherence_structure_axioms finer.empty_world finer.every_individual_exists_somewhere finer.every_individual_is_iof finer.iof_moment_constant finer.iof_scope finer.momentsI inf_bot_left inherence_structure.individuals_cases inheres_in_embedding) 
  subgoal G8 for x y by (meson ed_def empty_iff finer.empty_world finer.every_individual_exists_somewhere finer.every_individual_is_iof finer.individual_structure_axioms finer.iof_moment_constant finer.iof_scope individual_structure.ext_dep_imp_ed individual_structure.ext_dep_scope) 
  subgoal G9 by (simp add: coarser.universal_structure_axioms) 
  subgoal G10 by (simp add: finer.universal_structure_axioms)
  subgoal G11 for x  by (simp add: set_rev_mp subst_univs_subset) 
  subgoal G12 for x 
    by (metis Un_iff A coarser.instantiation_structure_axioms instantiation_structure.moment_univ_characterizes characterized_by_def universals_def)
  subgoal G13 for x using moment_univs_subset by blast
  subgoal G14 for x by (meson disjoint_iff_not_equal finer.char_by_E finer.moment_univ_characterizes finer.subst_moment_univs_disj) 
  subgoal G15 for x y by (simp add: subsumption_respected) 
  subgoal G16 for x y by (simp add: assms finer.iof_agrees_with_subsumes subsumption_up_respected) 
  done


end

abbreviation coarser_then :: 
  "('i,'u) instantiation_structure \<Rightarrow> ('i,'u) instantiation_structure \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>\<Colon>" 75) where
  "IS\<^sub>1 \<sqsubseteq>\<^sub>\<Colon> IS\<^sub>2 \<equiv> instantiation_refinement IS\<^sub>1 IS\<^sub>2"

lemma coarser_then_refl:
  assumes "instantiation_structure IS"
  shows "IS \<sqsubseteq>\<^sub>\<Colon> IS"
proof -
  interpret instantiation_structure IS using assms by auto
  show ?thesis
    apply (unfold_locales ; simp?)
    subgoal using inheres_in_scope by auto
    subgoal 
      apply (intro equalityI subsetI; simp?)
      subgoal using worlds_are_made_of_individuals by auto
      subgoal
        apply (elim exE conjE ; simp)
        using worlds_are_made_of_individuals 
        by (simp add: Int_absorb2)
      done    
    using iof_scope by blast
qed

lemma coarser_then_antisym:
  assumes "IS\<^sub>1 \<sqsubseteq>\<^sub>\<Colon> IS\<^sub>2" "IS\<^sub>2 \<sqsubseteq>\<^sub>\<Colon> IS\<^sub>1"
  shows "IS\<^sub>1 = IS\<^sub>2"
proof -
  interpret R12: instantiation_refinement IS\<^sub>1 IS\<^sub>2 using assms(1) by metis
  interpret R21: instantiation_refinement IS\<^sub>2 IS\<^sub>1 using assms(2) by metis
  show ?thesis
    apply (auto intro!: R12.instantiation_structure_eqI2)
    subgoal premises P for U
      using P R21.universals_subset by blast
    done
qed

lemma coarser_then_trans:
  assumes "IS\<^sub>1 \<sqsubseteq>\<^sub>\<Colon> IS\<^sub>2" "IS\<^sub>2 \<sqsubseteq>\<^sub>\<Colon> IS\<^sub>3"
  shows "IS\<^sub>1 \<sqsubseteq>\<^sub>\<Colon> IS\<^sub>3" 
proof -
  interpret R12: instantiation_refinement IS\<^sub>1 IS\<^sub>2 using assms(1) by metis
  interpret R23: instantiation_refinement IS\<^sub>2 IS\<^sub>3 using assms(2) by metis
  show ?thesis
    apply (unfold_locales ; safe?) 
    subgoal G1 for x using R12.subst_univs_subset R23.subst_univs_subset by blast
    subgoal G2 for x using R12.moment_univs_subset R23.moment_univs_subset by auto 
    subgoal G3 for x y by (simp add: R12.subsumption_respected R23.subsumption_respected) 
    subgoal G4 for x y using R12.subsumption_up_respected R12.universals_subset R23.subsumption_up_respected by blast 
    subgoal G5 for x  by (metis R12.same_substantials R23.same_substantials substantialsE substantialsI)
    subgoal G6 for x y by simp 
    subgoal G7 for x  by (metis R12.same_substantials R23.same_substantials substantialsE substantialsI) 
    subgoal G8 for x y by (metis R12.same_substantials R23.same_substantials substantialsE substantialsI)
    subgoal G9 for x y by simp
    subgoal G10 for x y by simp
    subgoal G11 for x y by simp
    subgoal G12 for x y 
      by (metis G8 R12.inheres_in_embedding R23.finer.substantialsI2 R23.inheres_in_embedding R23.same_substantials substantialsE)
    subgoal G13 for x  
    proof -
      assume "x \<in> R12.coarser.is_worlds"
      then have "\<exists>A. x = A \<inter> R12.coarser.is_individuals \<and> A \<in> R12.finer.is_worlds"
        using R12.worlds_embedding by blast
      then show ?thesis
        by (metis (lifting) R12.finer.every_individual_is_iof R23.finer.empty_world R23.finer.iof_scope R23.iof_embedding ex_in_conv)
    qed
    subgoal G14 for _ X
    proof -
      assume A: "X \<in> R23.finer.is_worlds"
      have B: "R12.coarser.is_individuals \<subseteq> R12.finer.is_individuals"        
        using R12.finer.individuals_moments_substantials by auto
      have C: "R12.finer.is_individuals \<subseteq> R23.finer.is_individuals"
        by (metis R12.same_substantials R23.finer.inheres_in_scope R23.inheres_in_embedding R23.same_substantials subsetI substantialsE substantialsI)
      have D: "R12.coarser.is_individuals \<subseteq> R23.finer.is_individuals"
        using B C by blast
      have E: "R12.coarser.is_worlds = {(w \<inter> R12.finer.is_individuals) \<inter> R12.coarser.is_individuals | w . w \<in> R23.finer.is_worlds}"
        using R12.worlds_embedding[simplified R23.worlds_embedding] by auto
      have F: "(X \<inter> R12.finer.is_individuals) \<inter> R12.coarser.is_individuals \<in> R12.coarser.is_worlds" using A E by blast
      then have "(X \<inter> R12.coarser.is_individuals) \<inter> R12.finer.is_individuals  \<in> R12.coarser.is_worlds" using A E by blast
      then show "X \<inter> R12.coarser.is_individuals \<in> R12.coarser.is_worlds" 
        using B 
        by (metis inf.absorb2 inf_commute inf_left_commute) 
    qed
    subgoal G15 for x y z by simp 
    subgoal G16 for x y z by simp 
    subgoal G17 for x y z using R12.coarser.at_least_one_instance by auto
    done
qed

abbreviation strictly_coarser_than (infix "\<sqsubset>\<^sub>\<Colon>" 75) where
  "IS\<^sub>1 \<sqsubset>\<^sub>\<Colon> IS\<^sub>2 \<equiv> IS\<^sub>1 \<sqsubseteq>\<^sub>\<Colon> IS\<^sub>2 \<and> IS\<^sub>1 \<noteq> IS\<^sub>2"

lemma strictly_coarser_than_univs:
  assumes "IS\<^sub>1 \<sqsubset>\<^sub>\<Colon> IS\<^sub>2"
  shows "universals \<U>\<S>\<^bsub>IS\<^sub>1\<^esub> \<subset> universals \<U>\<S>\<^bsub>IS\<^sub>2\<^esub>"
proof -
  obtain A: "IS\<^sub>1 \<sqsubseteq>\<^sub>\<Colon> IS\<^sub>2" "IS\<^sub>1 \<noteq> IS\<^sub>2" using assms by auto
  interpret instantiation_refinement IS\<^sub>1 IS\<^sub>2 using A(1) by auto
  show ?thesis 
    when "universals \<U>\<S>\<^bsub>IS\<^sub>2\<^esub> \<subseteq> universals \<U>\<S>\<^bsub>IS\<^sub>1\<^esub> \<Longrightarrow> False" 
    using that universals_subset by auto
  assume B: "finer.is_universals \<subseteq> coarser.is_universals"
  then show "False" using instantiation_structure_eqI2 A(2) by simp
qed

lemma instantiation_refinement_finite_universals:
  assumes "IS\<^sub>1 \<sqsubset>\<^sub>\<Colon> IS\<^sub>2"
  shows "finite (universals \<U>\<S>\<^bsub>IS\<^sub>1\<^esub>)" "finite (universals \<U>\<S>\<^bsub>IS\<^sub>2\<^esub>)"
proof -
  show G1: "finite (universals \<U>\<S>\<^bsub>IS\<^sub>2\<^esub>)" 
    by (metis assms finite_UnI instantiation_refinement.axioms(2) instantiation_structure.axioms(2) universal_structure.finite_moment_univs universal_structure.finite_subt_univs universals_def)
  show "finite (universals \<U>\<S>\<^bsub>IS\<^sub>1\<^esub>)"
    using G1 strictly_coarser_than_univs finite_subset assms
    by fastforce 
qed

(*
lemma "wfP ((\<sqsubset>\<^sub>\<Colon>) :: ('i,'u) instantiation_structure \<Rightarrow> ('i,'u) instantiation_structure \<Rightarrow> bool)"  
proof -
  define ucount :: "('i,'u) instantiation_structure \<Rightarrow> nat" where
    "ucount IS \<equiv> card (universals \<U>\<S>\<^bsub>IS\<^esub>)" for IS
  have A: "ucount IS\<^sub>1 < ucount IS\<^sub>2" 
    if "IS\<^sub>1 \<sqsubset>\<^sub>\<Colon> IS\<^sub>2" for IS\<^sub>1 IS\<^sub>2 :: "('i,'u) instantiation_structure"    
    by (metis instantiation_refinement_finite_universals
         strictly_coarser_than_univs that psubset_card_mono ucount_def)
  have B: "ucount IS \<noteq> 0" 
    if "instantiation_structure IS" 
    for IS
    using that ucount_def  
    by (metis card_eq_0_iff ex_in_conv finite_UnI instantiation_structure.axioms(2) instantiation_structure.iof_agrees_with_subsumes universal_structure.finite_moment_univs universal_structure.finite_subt_univs universal_structure.top_subst_univ universal_structure.top_subsumes universals_def)
  show "?thesis" 
  proof (intro wfI_min[to_pred] ; simp add: Bex_def)
    fix X :: "('i,'u) instantiation_structure" and Q
    assume AA: "X \<in> Q"
    show "\<exists>X. X \<in> Q \<and> (\<forall>Y. Y \<sqsubset>\<^sub>\<Colon> X \<longrightarrow> Y \<notin> Q)"    
    proof (cases "instantiation_structure X")
      assume AAA: "\<not> instantiation_structure X"
      show ?thesis
      proof (intro exI[of _ "X"] conjI AA allI impI)
          fix Y
          assume "Y \<sqsubset>\<^sub>\<Colon> X"
          then interpret IR: instantiation_refinement Y X by auto
          have "instantiation_structure X" by (simp add: IR.finer.instantiation_structure_axioms)
          then show "Y \<notin> Q" using AAA by blast        
      qed
    next
      assume AAA: "instantiation_structure X"
      show ?thesis
      using AA AAA proof (induct "ucount X" arbitrary: X)
        case 0
        then show ?case using B by metis
      next
        case (Suc x)
        show ?case
          using Suc(1) Suc(2,3,4) Suc(1)[OF Suc(2)]
          sorry
      qed      
    qed

    proof (induct "ucount X")
      case 0
      show ?case 
      proof (cases "instantiation_structure X")
        assume "instantiation_structure X"
        then show ?case using B 0 by metis
      next
        assume AA: "\<not> instantiation_structure X"
        show ?case 
        proof (intro exI[of _ "X"] conjI 0 allI impI)
          fix Y
          assume "Y \<sqsubset>\<^sub>\<Colon> X"
          then interpret IR: instantiation_refinement Y X by auto
          have "instantiation_structure X" by (simp add: IR.finer.instantiation_structure_axioms)
          then show "Y \<notin> Q" using AA by blast
        qed
      qed
    next
      case (Suc x)
      then show ?case sorry
    qed

      apply ()
      
    apply (simp add: wfP_eq_minimal ; safe ; rule ccontr ; simp?)
    subgoal for Q x
    proof -      
      assume AA: "x \<in> Q" "\<forall>z\<in>Q. \<exists>y. y \<sqsubseteq>\<^sub>\<Colon> z \<and> y \<noteq> z \<and> y \<in> Q"
      then obtain y where B: "y \<sqsubseteq>\<^sub>\<Colon> x" "y \<noteq> x" "y \<in> Q" by metis
      have C: "ucount y < ucount x" using A B(1,2) by auto
      show "False"
        using AA B C ucount_def A sledgehammer 
        sorry

*)

inductive_set excluded_moments :: "('i,'u) instantiation_structure \<Rightarrow> 'u \<Rightarrow> 'i set"
  for IS :: "('i,'u) instantiation_structure" (structure) 
    and U :: 'u
  where
    directly_excluded: "\<lbrakk> m \<triangleleft>\<^bsub>\<I>\<S>\<^esub> x ; x \<Colon>\<^sub>\<diamondop> U ; \<forall>um. char_by U um \<longrightarrow> \<not> m \<Colon>\<^sub>\<diamondop> um \<rbrakk> \<Longrightarrow> m \<in> excluded_moments IS U" |
    indirectly_excluded: "\<lbrakk> m' \<in> excluded_moments IS U ; m' \<rightleftharpoons>\<^bsub>\<I>\<S>\<^esub> m \<rbrakk> \<Longrightarrow> m \<in> excluded_moments IS U"

inductive_set excluded_moment_universals :: "('i,'u) instantiation_structure \<Rightarrow> 'u \<Rightarrow> 'u set"
  for IS :: "('i,'u) instantiation_structure" (structure) 
    and U :: 'u
  where
    "\<lbrakk> um \<in> \<U>\<^sub>m\<^bsub>\<U>\<S>\<^esub> ; \<forall>m. m \<Colon>\<^sub>\<diamondop> um \<longrightarrow> m \<in> excluded_moments IS U \<rbrakk> \<Longrightarrow>
        um \<in> excluded_moment_universals IS U"
       
definition project :: "('i,'u) instantiation_structure \<Rightarrow> 'u \<Rightarrow>
                       ('i,'u) instantiation_structure" where
  "project IS U \<equiv> 
      let US = substantial_universals \<U>\<S> ;
          S = substantials \<I>\<S> ;
          M' = excluded_moments IS U ;
          M = moments \<I>\<S> - M' ;
          UM = moment_universals \<U>\<S> - 
               excluded_moment_universals IS U ;
          I = S \<union> M ;
          U = US \<union> UM ;
          subsumes' = (\<lambda>x y. x \<preceq>\<^bsub>\<U>\<S>\<^esub> y \<and> x \<in> U \<and> y \<in> U) ;
          iof' = (\<lambda>x w y. x \<Colon>\<^bsub>w\<^esub> y \<and> x \<in> I) ;
          inheres_in' = (\<lambda>x y. x \<triangleleft>\<^bsub>\<I>\<S>\<^esub> y \<and> x \<in> M) ;         
          ext_dep_upon' = (\<lambda>x y. x \<rightleftharpoons>\<^bsub>\<I>\<S>\<^esub> y \<and> x \<in> M \<and> y \<in> M) ;
          worlds' = { w - M' | w . w \<in> \<W>\<^bsub>\<I>\<S>\<^esub> }
      in
        \<lparr> indiv_structure =
               \<lparr> individuals = I,
                   inheres_in = inheres_in',                   
                   worlds = worlds',
                   ext_dep_upon = ext_dep_upon' \<rparr>,
          univ_structure = 
              \<lparr> substantial_universals = US,
                   moment_universals = UM,
                   subsumes = subsumes' \<rparr> ,             
              iof = iof'
           \<rparr> "
  for IS (structure)

context instantiation_structure
begin

lemma project_simps_individuals[simp]:
  fixes U :: 'u      
  shows "individuals (indiv_structure (project IS U)) =
    substantials \<I>\<S> \<union> moments \<I>\<S> - excluded_moments IS U"
  apply (auto simp: project_def Let_def) 
  subgoal premises P for x
    using P apply (induct)
    subgoal by auto
    using ext_dep_scope momentsE by metis
  done

lemma project_simps_substantials[simp]:
  fixes U :: 'u      
  shows "substantials (indiv_structure (project IS U)) =
    substantials \<I>\<S>"
  apply (auto simp: project_def Let_def) 
  subgoal premises P for x
    using P apply (induct)
    apply auto    
    using P(1) P(3) by blast
  done

lemma project_simps_moments[simp]:
  fixes U :: 'u      
  shows "moments (indiv_structure (project IS U)) =
    moments \<I>\<S> - excluded_moments IS U"
  apply (clarsimp simp: project_def Let_def moments_def set_eq_iff) 
  by (safe ; blast?)

lemma project_simps_inheres_in[simp]:
  fixes U :: 'u      
  shows "inheres_in (indiv_structure (project IS U)) = (\<lambda>x y.
    inheres_in \<I>\<S> x y \<and> x \<notin> excluded_moments IS U)"
  apply (intro ext ;clarsimp simp: project_def Let_def ; safe) 
  by blast
  
lemma project_simps_worlds[simp]:
  fixes U :: 'u      
  shows "worlds (indiv_structure (project IS U)) =
    { w - excluded_moments IS U | w . w \<in> worlds \<I>\<S> }"
  by (clarsimp simp: project_def Let_def ; safe) 

lemma project_simps_ext_dep_upon[simp]:
  fixes U :: 'u      
  shows "ext_dep_upon (indiv_structure (project IS U)) =
    (\<lambda>x y.
    ext_dep_upon \<I>\<S> x y \<and> x \<notin> excluded_moments IS U \<and>
       y \<notin> excluded_moments IS U)"
  apply (intro ext ; clarsimp simp: project_def Let_def ; safe) 
  using ext_dep_scope by auto



lemma project_simps_universals[simp]:
  fixes U :: 'u      
  shows "universals (univ_structure (project IS U)) =
    universals \<U>\<S> - excluded_moment_universals IS U"
  apply (clarsimp simp: project_def Let_def universals_def set_eq_iff
      excluded_moment_universals.simps) 
  apply (safe ; (elim notE)?)
  subgoal G1 by (meson char_by_E disjoint_iff_not_equal local.subst_moment_univs_disj moment_univ_characterizes)
  subgoal using local.subst_moment_univs_disj by blast
  by (simp add: G1)
  

lemma project_simps_moment_universals[simp]:
  fixes U :: 'u      
  shows "moment_universals (univ_structure (project IS U)) =
    moment_universals \<U>\<S> - excluded_moment_universals IS U"
  by (clarsimp simp: project_def Let_def universals_def set_eq_iff) 

lemma project_simps_substantial_universals[simp]:
  fixes U :: 'u      
  shows "substantial_universals (univ_structure (project IS U)) = substantial_universals \<U>\<S>"
  by (clarsimp simp: project_def Let_def universals_def set_eq_iff) 

lemma project_simps_substantial_subsumes[simp]:
  fixes U :: 'u      
  shows "subsumes (univ_structure (project IS U)) = 
    (\<lambda>U\<^sub>1 U\<^sub>2. subsumes \<U>\<S> U\<^sub>1 U\<^sub>2 \<and> 
      (U\<^sub>1 \<in> substantial_universals \<U>\<S> \<or>
       U\<^sub>2 \<in> substantial_universals \<U>\<S> \<or>
       (U\<^sub>1 \<notin> excluded_moment_universals IS U \<and>
         U\<^sub>2 \<notin> excluded_moment_universals IS U))) "
  apply (intro ext ; clarsimp simp: project_def Let_def ; safe)
  subgoal G1 using subsumes_cases by blast
  subgoal using G1 instantiation_structure.moment_univ_characterizes instantiation_structure_axioms by fastforce
  subgoal using subsumes_cases by blast
  subgoal by (meson disjoint_iff_not_equal local.subst_moment_univs_disj local.subsumes_scope)
  subgoal using subsumes_cases by blast
  using local.subsumes_scope by blast

lemma project_simps_iof[simp]:
  fixes U :: 'u      
  shows "iof (project IS U) = 
    (\<lambda>x w u. x \<Colon>\<^bsub>w\<^esub> u \<and> x \<notin> excluded_moments IS U)"
  apply (intro ext ; clarsimp simp: project_def Let_def ; safe)
  subgoal G1 by (meson excluded_moments.simps ext_dep_scope momentsE)
  subgoal G2 by (meson existence_structure.worlds_are_made_of_individuals existence_structure_axioms instantiation_structure.iof_scope instantiation_structure_axioms set_rev_mp)
  by blast

lemma project_instantiation_structure[intro!]:
  assumes "U \<in> substantial_universals \<U>\<S>"
  shows "instantiation_structure (project IS U)"
  apply (intro_locales)  
  subgoal inherence_structure_goal
    apply (unfold_locales ; clarsimp)
    subgoal by (simp add: moments_def substantials_def undefined_not_in_individuals)
    subgoal by (metis Diff_disjoint IntI empty_iff inherence_structure.momentsI inherence_structure.substantialsI2 inherence_structure_axioms project_simps_individuals project_simps_substantials substantialsE)
    subgoal using inheres_in_sep by blast
    by (simp add: inheres_in_single)    
  subgoal existence_structure_goal
    apply (unfold_locales ; clarsimp)
    subgoal using empty_world by blast
    subgoal using existence_structure.worlds_are_made_of_individuals existence_structure_axioms by blast
    subgoal by (metis Diff_iff every_individual_exists_somewhere inheres_in_scope momentsE substantialsE)
    by (metis Diff_empty Diff_partition char_by_E every_individual_exists_somewhere every_individual_is_iof inf.absorb2 inheres_in_scope iof_scope iof_sep local.subst_moment_univs_disj moment_univ_characterizes subsetI substantialsE universals_def)   
  subgoal individual_structure_axioms_goal
    apply (unfold_locales ; clarsimp)
    subgoal using ext_dep_irrefl ext_dep_scope by auto 
    subgoal by (meson empty_iff empty_world every_individual_exists_somewhere every_individual_is_iof individual_structure.ext_dep_scope individual_structure_axioms inheres_in_scope iof_moment_constant iof_scope momentsE)
    subgoal by (meson empty_iff empty_world every_individual_exists_somewhere every_individual_is_iof individual_structure.ext_dep_scope individual_structure_axioms inheres_in_scope iof_moment_constant iof_scope momentsE)
    subgoal by (simp add: ext_dep_irrefl) 
    subgoal using ext_dep_sym by blast 
    using ext_dep_trans by blast
  subgoal universal_structure_axioms_goal 
    apply (unfold_locales ; clarsimp)
    subgoal by (simp add: local.finite_subt_univs)
    subgoal using local.finite_moment_univs by blast
    subgoal using local.subst_moment_univs_disj by auto
    subgoal by (simp add: local.at_least_one_subst_univ)
    subgoal using local.top_substantial_ex by blast
    subgoal G6 using moment_univ_characterizes subsumes_cases by blast
    subgoal by (simp add: local.subsumes_refl) 
    subgoal by (simp add: local.subsumes_antisym)
    using G6 local.subsumes_trans by blast 
  subgoal instantiation_structure_axioms_goal 
    apply (unfold_locales ; clarsimp)
    subgoal G1 by (metis (no_types, lifting) Set.set_insert excluded_moment_universals.simps excluded_moments.cases ext_dep_scope insert_disjoint(1) instantiation_structure.char_by_E instantiation_structure_axioms iof_agrees_with_subsumes iof_sep local.subst_moment_univs_disj local.subsumes_refl local.subsumes_scope moment_univ_characterizes momentsI substantials_moments_disj)
    subgoal G2 premises P for x w u 
    proof -
      have f1: "\<U>\<^sub>m = {}"
        by (metis (no_types) char_by_E inf.absorb2 local.subst_moment_univs_disj moment_univ_characterizes subset_iff) (* 44 ms *)
      obtain II :: "'i \<Rightarrow> 'i set" where
        f2: "\<And>i ia I ua ib Ia ub ic Ib uc. x \<Colon>\<^bsub>w\<^esub> u \<and> II i \<in> \<W> \<and> (\<not> ia \<Colon>\<^bsub>I\<^esub> ua \<or> ia \<in> I) \<and> (i \<notin> \<I> \<or> i \<in> II i) \<and> (\<not> ib \<Colon>\<^bsub>Ia\<^esub> ub \<or> Ia \<in> \<W>) \<and> (\<not> ic \<Colon>\<^bsub>Ib\<^esub> uc \<or> uc \<in> \<U>)"
        using P(1) every_individual_exists_somewhere iof_scope by moura (* 81 ms *)
      then have "\<And>i I u. \<not> i \<Colon>\<^bsub>I\<^esub> u \<or> u \<in> \<U>\<^sub>m \<union> \<U>\<^sub>s"
        by (simp add: universals_def) (* 14 ms *)
      then have "u \<in> \<U>\<^sub>m \<union> \<U>\<^sub>s"
        using f2 by blast (* 17 ms *)
      then have "u \<preceq> u"
      by (simp add: local.subsumes_refl universals_def) (* 1 ms *)
      then show ?thesis
      using f2 f1 by (metis (no_types) Diff_empty G1 disjoint_iff_not_equal every_individual_is_iof excluded_moments.cases ext_dep_scope inf.absorb2 inheres_in_scope iof_sep momentsE momentsI subset_iff substantials_moments_disj sup_bot.left_neutral universals_def) (* 682 ms *)
    qed
    subgoal G3 by (metis Diff_iff at_least_one_instance char_by_E individuals_moments_substantials instantiation_structure.iof_sep instantiation_structure.moment_univ_characterizes instantiation_structure_axioms local.subsumes_scope local.universal_structure_axioms project_simps_individuals project_simps_substantials substantialsE universal_structure.subsumes_refl)
    subgoal G4 using G2 every_individual_is_iof by fastforce
    subgoal G5 by (simp add: iof_sep)
    subgoal by (meson empty_world equals0D iof_moment_constant iof_scope)
    subgoal by (meson char_by_E disjoint_iff_not_equal local.subst_moment_univs_disj moment_univ_characterizes unique_characterization)
    subgoal by (meson char_by_E disjoint_iff_not_equal local.subst_moment_univs_disj moment_univ_characterizes)
    by (simp add: unique_moment_per_moment_univ) 
  done

lemma project_instantiation_refinement[intro!]:
  assumes "U \<in> substantial_universals \<U>\<S>"
  shows "project IS U \<sqsubseteq>\<^sub>\<Colon> IS"
proof -
  interpret IS2: instantiation_structure "project IS U" using assms by auto
  show ?thesis
    apply (unfold_locales ; simp ; safe?)
    subgoal by (meson characterized_by_def excluded_moment_universals.simps moment_univ_characterizes)
    subgoal by blast
    subgoal by blast 
    subgoal using inheres_in_scope by auto
    subgoal by blast
    subgoal using IS2.inherence_structure_axioms inherence_structure.inheres_in_scope by fastforce
    subgoal by (metis Int_Diff individuals_moments_substantials inf.absorb1 worlds_are_made_of_individuals)
    subgoal by (metis Int_Diff individuals_moments_substantials inf.absorb1 worlds_are_made_of_individuals)
    subgoal by (simp add: iof_scope)
    subgoal by (meson excluded_moment_universals.cases instantiation_structure.miof_I instantiation_structure_axioms)
    by (meson empty_iff empty_world excluded_moments.simps ext_dep_scope iof_moment_constant iof_scope momentsI)   
  qed

end

datatype Test1_Substantial =
  T1S_red_big_sphere | T1S_red_small_sphere | T1S_green_big_sphere | T1S_green_small_sphere |
  T1S_red_square | T1S_green_square

datatype Test1_Color = T1C_Red | T1C_Green

datatype Test1_Size = T1SZ_Big | T1SZ_Small

datatype Test1_Shape = T1SH_Sphere | T1SH_Square

datatype Test1_MomentValue = T1MV_Color Test1_Color | T1MV_Size Test1_Size | T1MV_Shape Test1_Shape 

datatype Test1_Moment = T1M Test1_Substantial Test1_MomentValue

datatype Test1_Individual = 
            T1I_Substantial Test1_Substantial | 
            T1I_Moment Test1_Moment | T1I_Undefined

datatype Test1_MomentUniversal = T1MU_Color | T1MU_Size | T1MU_Shape

datatype Test1_SubstantialUniversal = T1SU_things |
  T1SU_colored_things | T1SU_variable_size_things | T1SU_shaped_things | 
  T1SU_spheres | T1SU_squares | T1SU_big_spheres | T1SU_small_spheres | 
  T1SU_green_squares 

datatype Test1_Universals = 
  T1U_MU Test1_MomentUniversal |
  T1U_SU Test1_SubstantialUniversal

context

assumes T1I_Undefined[simp]: "undefined = T1I_Undefined"

begin

private definition test1_substantials where
  "test1_substantials \<equiv> {
    T1I_Substantial T1S_red_big_sphere, T1I_Substantial T1S_red_small_sphere, 
    T1I_Substantial T1S_green_big_sphere, T1I_Substantial T1S_green_small_sphere, 
    T1I_Substantial T1S_red_square, T1I_Substantial T1S_green_square
  }"

private definition test1_moments where
  "test1_moments \<equiv> { 
      T1I_Moment (T1M T1S_red_big_sphere (T1MV_Color T1C_Red)),
      T1I_Moment (T1M T1S_red_big_sphere (T1MV_Size T1SZ_Big)),
      T1I_Moment (T1M T1S_red_big_sphere (T1MV_Shape T1SH_Sphere)),
      T1I_Moment (T1M T1S_red_small_sphere (T1MV_Color T1C_Red)),
      T1I_Moment (T1M T1S_red_small_sphere (T1MV_Size T1SZ_Small)),
      T1I_Moment (T1M T1S_red_small_sphere (T1MV_Shape T1SH_Sphere)),
      T1I_Moment (T1M T1S_green_big_sphere (T1MV_Color T1C_Green)),
      T1I_Moment (T1M T1S_green_big_sphere (T1MV_Size T1SZ_Big)),
      T1I_Moment (T1M T1S_green_big_sphere (T1MV_Shape T1SH_Sphere)),
      T1I_Moment (T1M T1S_green_small_sphere (T1MV_Color T1C_Green)),
      T1I_Moment (T1M T1S_green_small_sphere (T1MV_Size T1SZ_Small)),
      T1I_Moment (T1M T1S_green_small_sphere (T1MV_Shape T1SH_Sphere)),
      T1I_Moment (T1M T1S_red_square (T1MV_Color T1C_Red)),
      T1I_Moment (T1M T1S_red_square (T1MV_Shape T1SH_Square)),
      T1I_Moment (T1M T1S_green_square (T1MV_Color T1C_Green)),
      T1I_Moment (T1M T1S_green_square (T1MV_Shape T1SH_Square)) }"

abbreviation "test1_individuals \<equiv> test1_substantials \<union> test1_moments"

fun test1_inheres_in_1 where
  "test1_inheres_in_1 (T1I_Moment (T1M s\<^sub>1 _)) (T1I_Substantial s\<^sub>2) = (s\<^sub>1 = s\<^sub>2)" |
  "test1_inheres_in_1 _ _ = False"

abbreviation test1_inheres_in where
  "test1_inheres_in m s \<equiv> m \<in> test1_moments \<and> test1_inheres_in_1 m s"

abbreviation "test1_worlds \<equiv> { {}, test1_individuals }"

definition "test1_substantial_universals \<equiv> {
   T1U_SU T1SU_things,
   T1U_SU T1SU_colored_things, 
   T1U_SU T1SU_variable_size_things, 
   T1U_SU T1SU_shaped_things,
   T1U_SU T1SU_spheres, 
   T1U_SU T1SU_squares, 
   T1U_SU T1SU_big_spheres, 
   T1U_SU T1SU_small_spheres, 
   T1U_SU T1SU_green_squares
  }"

definition "test1_moment_universals \<equiv> {
   T1U_MU T1MU_Color, T1U_MU T1MU_Size, T1U_MU T1MU_Shape
  }"

abbreviation "test1_universals \<equiv> test1_substantial_universals \<union> test1_moment_universals"

fun test1_subsumes_1 :: "Test1_Universals \<Rightarrow> Test1_Universals \<Rightarrow> bool" where
    "test1_subsumes_1 (T1U_SU T1SU_spheres) (T1U_SU T1SU_colored_things) = True" 
  | "test1_subsumes_1 (T1U_SU T1SU_spheres) (T1U_SU T1SU_variable_size_things) = True"
  | "test1_subsumes_1 (T1U_SU T1SU_spheres) (T1U_SU T1SU_shaped_things) = True"
  | "test1_subsumes_1 (T1U_SU T1SU_big_spheres) (T1U_SU T1SU_spheres) = True" 
  | "test1_subsumes_1 (T1U_SU T1SU_squares) (T1U_SU T1SU_colored_things) = True" 
  | "test1_subsumes_1 (T1U_SU T1SU_squares) (T1U_SU T1SU_shaped_things) = True"
  | "test1_subsumes_1 (T1U_SU T1SU_small_spheres) (T1U_SU T1SU_spheres) = True"
  | "test1_subsumes_1 (T1U_SU T1SU_green_squares) (T1U_SU T1SU_squares) = True"
  | things: "test1_subsumes_1 (T1U_SU _) (T1U_SU T1SU_things) = True"
  | "test1_subsumes_1 _ _ = False"

lemma test1_subsumes_1_iff:
  "test1_subsumes_1 X Y \<longleftrightarrow>
     (\<exists>XX YY. X = T1I_SU XX \<and> Y = T1I_SU YY \<and>
        (XX = T1SU_spheres \<and> (YY = T1SU_colored_things \<or> YY = T1SU_variable_size_things \<or> YY = T1SU_shaped_things) \<or>
         XX = T1SU_big_spheres \<and> (YY = T1SU_spheres) \<or>
         XX = T1SU_squares \<and> (YY = T1SU_colored_things \<or> YY = T1SU_shaped_things) \<or>
         XX = T1SU_small_spheres \<and> YY = T1SU_spheres \<or>
         XX = T1SU_green_squares \<and> YY = T1SU_squares \<or>
         YY = T1SU_things))"
find_theorems name: "test1_subsumes_1.i"
  using test1_subsumes_1.elims
        
        Test1_Universals.exhaust 
        Test1_SubstantialUniversal.exhaust
        Test1_MomentUniversal.exhaust
oops

lemma test1_subsumes_1_antisym: 
  assumes "test1_subsumes_1 X Y" "test1_subsumes_1 Y X"
  shows "X = Y"
  using assms apply (induct X Y rule: test1_subsumes_1.induct ; simp?)
  subgoal for U
    apply (cases X ; simp?)
    subgoal for W
      apply (cases W ; cases Y ; simp?)
      using Test1_SubstantialUniversal.exhaust test1_subsumes_1.simps by blast+
    done
  done

lemma test1_subsumes_1_scope: "test1_subsumes_1 x y \<Longrightarrow> x \<in> test1_substantial_universals \<and> y \<in> test1_substantial_universals"
  apply (auto)
  by (induct rule: test1_subsumes_1.induct ; (simp add: test1_substantial_universals_def test1_moment_universals_def)?)+


abbreviation "test1_subsumes x y \<equiv> (x \<in> test1_universals \<and> y = x) \<or> test1_subsumes_1\<^sup>+\<^sup>+ x y"

lemma test1_subsumes_scope[elim,cases pred]:
  assumes "test1_subsumes x y"
  obtains (moments) "x \<in> test1_moment_universals" "y = x" |
          (substantial) "x \<in> test1_substantial_universals" "y \<in> test1_substantial_universals"
  using assms apply (rule disjE ; clarsimp)
  subgoal by (simp add: test1_substantial_universals_def test1_moment_universals_def ; blast)
  subgoal premises P
    using P(3,1,2) apply (induct rule: tranclp_induct ; (simp add: test1_substantial_universals_def test1_moment_universals_def)?)
    subgoal by (metis substantial test1_subsumes_1_scope tranclp.simps)
    by (smt Sortals2.test1_subsumes_1.elims(2) T1I_Undefined test1_subsumes_1.simps(10))
  done   
  
lemma test1_subsumes_refl: "x \<in> test1_universals \<Longrightarrow> test1_subsumes x x" by auto

lemma test1_subsumes_trans: 
    "\<lbrakk> test1_subsumes x y ; test1_subsumes y z \<rbrakk> \<Longrightarrow> test1_subsumes x z"
  using tranclp_trans by metis

lemma test1_subsumes_antisym:
    "\<lbrakk> test1_subsumes x y ; test1_subsumes y x \<rbrakk> \<Longrightarrow> x = y"
  using test1_subsumes_scope test1_subsumes_1_antisym 
 (* slow *)
 by (smt local.things test1_subsumes_1.elims(2) test1_subsumes_1.simps tranclp.simps tranclp_trans)


fun test1_iof' :: "Test1_Individual \<Rightarrow> Test1_Universals \<Rightarrow> bool" where
    "test1_iof' (T1I_Moment (T1M _ (T1MV_Color _))) (T1U_MU T1MU_Color) = True"
  | "test1_iof' (T1I_Moment (T1M _ (T1MV_Shape _))) (T1U_MU T1MU_Shape) = True"
  | "test1_iof' (T1I_Moment (T1M _ (T1MV_Size _))) (T1U_MU T1MU_Size) = True"
  | "test1_iof' (T1I_Moment _) _ = False"
  | "test1_iof' (T1I_Substantial T1S_red_big_sphere) (T1U_SU T1SU_big_spheres) = True"
  | "test1_iof' (T1I_Substantial T1S_red_small_sphere) (T1U_SU T1SU_small_spheres) = True"
  | "test1_iof' (T1I_Substantial T1S_green_big_sphere) (T1U_SU T1SU_big_spheres) = True"
  | "test1_iof' (T1I_Substantial T1S_green_small_sphere) (T1U_SU T1SU_small_spheres) = True"
  | "test1_iof' (T1I_Substantial T1S_red_square) (T1U_SU T1SU_squares) = True"
  | "test1_iof' (T1I_Substantial T1S_green_square) (T1U_SU T1SU_green_squares) = True"
  | "test1_iof' _ _ = False"


abbreviation "test1_iof x w U \<equiv> 
  w = test1_individuals \<and>
  (\<exists>U'. test1_subsumes U' U \<and> test1_iof' x U')"



lemma test1_inheres_in_scope:
  assumes "test1_inheres_in m s"
  obtains "m \<in> test1_moments" "s \<in> test1_substantials"
  using assms apply simp
  apply (elim conjE)
  subgoal premises P
    using P(3,1,2) apply (elim test1_inheres_in_1.elims ; simp?)
    subgoal for x y z      
      using Test1_Substantial.exhaust test1_substantials_def by auto
    done
  done

definition "test1_inherence_structure \<equiv> \<lparr> individuals = test1_individuals, inheres_in = test1_inheres_in \<rparr>"

lemma test1_inherence_structure[simp,intro!]: "inherence_structure test1_inherence_structure"
  apply (unfold_locales)
  subgoal  by (auto simp: test1_inherence_structure_def test1_substantials_def test1_moments_def)
  subgoal premises P for x y
    using P apply (simp add: test1_inherence_structure_def ; elim conjE ; simp add: test1_inherence_structure_def)
    apply (elim test1_inheres_in_1.elims ; safe)
    by (auto simp: test1_moments_def test1_substantials_def)
  subgoal premises P for x y
    using P apply (simp add: test1_inherence_structure_def ; elim conjE ; simp add: test1_inherence_structure_def)
    apply (elim test1_inheres_in_1.elims ; safe)
    by (auto simp: test1_moments_def test1_substantials_def)
  subgoal premises P for x y
    using P apply (simp add: test1_inherence_structure_def ; elim conjE ; simp add: test1_inherence_structure_def)
    by (elim test1_inheres_in_1.elims ; safe)
  done

interpretation test1: inherence_structure test1_inherence_structure by simp

definition "test1_existence_structure \<equiv> 
    inherence_structure.extend test1_inherence_structure \<lparr> worlds = test1_worlds \<rparr>"

lemma test1_existence_structure_truncate[simp]:
  "inherence_structure.truncate test1_existence_structure = test1_inherence_structure"
  by (simp add: test1_existence_structure_def inherence_structure.truncate_def inherence_structure.extend_def)

lemma inherence_structure_truncate: "inherence_structure (inherence_structure.truncate X) \<Longrightarrow> inherence_structure X"
  apply (cases X ; (simp add: inherence_structure.truncate_def))  
  subgoal for ind inh more
    apply (unfold_locales ; auto)
    subgoal using inherence_structure.undefined_not_in_individuals by force 
    subgoal using inherence_structure.inheres_in_scope by fastforce
    subgoal using inherence_structure.inheres_in_scope by fastforce 
    subgoal G4 using inherence_structure.inheres_in_sep by force
    subgoal using G4 by blast    
    by (simp add: inherence_structure.inheres_in_single)
  done

lemma inherence_structure_extends_individuals[simp]:
  "\<I>\<^bsub>inherence_structure.extend X Y\<^esub> = \<I>\<^bsub>X\<^esub>"
  apply (cases X ; auto)
  subgoal premises P for x y z
    using P(2) by (simp add: inherence_structure.extend_def)
  subgoal premises P for x y z
    using P(2) by (simp add: inherence_structure.extend_def)
  done

lemma inherence_structure_extends_moments[simp]:
  "\<M>\<^bsub>inherence_structure.extend X Y\<^esub> = \<M>\<^bsub>X\<^esub>"
  apply (cases X ; auto)
  subgoal premises P for x y z
    using P(2) by (simp add: moments_def inherence_structure.extend_def)
  subgoal premises P for x y z
    using P(2) by (simp add: moments_def inherence_structure.extend_def)
  done

lemma inherence_structure_extends_substantials[simp]:
  "\<S>\<^bsub>inherence_structure.extend X Y\<^esub> = \<S>\<^bsub>X\<^esub>"
  apply (cases X ; auto)
  subgoal premises P for x y z
    using P by (auto simp: substantials_def inherence_structure.extend_def)
  subgoal premises P for x y z
    using P by (auto simp add: substantials_def inherence_structure.extend_def)
  done

lemma inherence_structure_extends_inheres_in[simp]:
  "inheres_in (inherence_structure.extend X Y) = inheres_in X"
  by (intro ext ; cases X ; (auto simp: inherence_structure.extend_def))

lemma existence_structure_worls[simp]:
  "worlds test1_existence_structure = test1_worlds"
  by (simp add: test1_existence_structure_def inherence_structure.extend_def)


lemma test1_existence_structure_simps[simp]:
  "individuals test1_existence_structure = test1_individuals"
  "moments test1_existence_structure = test1_moments"
  "inheres_in test1_existence_structure = test1_inheres_in"  
  subgoal by (simp add: test1_existence_structure_def test1_inherence_structure_def)
  subgoal 
    apply (simp add: test1_existence_structure_def moments_def set_eq_iff test1_inherence_structure_def ; safe)
    apply (simp add: test1_moments_def)    
    using test1_inheres_in_1.simps(1) by blast
  subgoal
    by (intro ext ; safe ; (simp add: test1_existence_structure_def test1_inherence_structure_def))
  done

lemma test1_existence_structure[simp,intro!]: "existence_structure test1_existence_structure"
  apply (intro_locales ; (rule inherence_structure_truncate)? ; simp?)  
  subgoal
    apply (unfold_locales ; (simp)? ; safe)
    subgoal for x y
      apply (simp add: ed_def)      
      using test1_inheres_in_scope by blast
    done
  done

interpretation test1: existence_structure test1_existence_structure by simp


definition "test1_individual_structure \<equiv>
    existence_structure.extend test1_existence_structure \<lparr> ext_dep_upon = \<lambda>x y. False \<rparr>"

lemma existence_structure_axioms_truncate: "existence_structure_axioms X = existence_structure_axioms (existence_structure.truncate X)"
  by (cases X ; auto simp: existence_structure.truncate_def existence_structure_axioms_def ed_def)


lemma test1_individual_structure[simp,intro!]: "individual_structure test1_individual_structure"
  apply (intro_locales ; simp?)
  subgoal
    apply (simp add: test1_individual_structure_def existence_structure.extend_def)
    apply (rule inherence_structure_truncate ; simp add: inherence_structure.truncate_def)    
    using test1_inherence_structure[simplified test1_inherence_structure_def] by simp
  subgoal    
    apply (subst existence_structure_axioms_truncate ; simp add: existence_structure.truncate_def 
            test1_individual_structure_def existence_structure_axioms_def test1_existence_structure_def
            test1_inherence_structure_def)
    apply (simp add: inherence_structure.extend_def existence_structure.extend_def ed_def)
    apply auto
    apply (erule test1_inheres_in_1.elims ; simp?)    
    using test1_inheres_in_1.simps(1) test1_inheres_in_scope by blast
  subgoal
    apply (unfold_locales)
    subgoal for x y
      by (simp add: test1_individual_structure_def existence_structure.extend_def)
    by (simp add: test1_individual_structure_def test1_existence_structure_def test1_inherence_structure_def 
               ; simp add: existence_structure.extend_def inherence_structure.extend_def individual_structure.extend_def)+
  done    

interpretation test1: individual_structure test1_individual_structure by simp
      
definition "test1_universal_structure \<equiv>
   \<lparr> substantial_universals = test1_substantial_universals,
     moment_universals = test1_moment_universals,
     subsumes = test1_subsumes \<rparr>"

lemma test1_universal_structure[simp,intro!]: 
    "universal_structure test1_universal_structure"
  apply (unfold_locales ; simp add: test1_universal_structure_def)
  subgoal G1 by (simp add: test1_substantial_universals_def)
  subgoal G2 by (simp add: test1_moment_universals_def)
  subgoal G3 by (simp add: test1_substantial_universals_def test1_moment_universals_def)  
  subgoal G4 by (simp add: test1_substantial_universals_def)
  subgoal G5 
    apply (intro exI[of "\<lambda>U. \<forall>U'\<in>test1_substantial_universals. U = U' \<or> test1_subsumes_1\<^sup>+\<^sup>+ U' U" 
                          "T1U_SU T1SU_things"])
    apply (simp add: test1_substantial_universals_def)
    using local.things tranclp.intros(1) by metis   
  subgoal G6 for U1 U2 using test1_subsumes_scope by blast
  subgoal G7 for U by (metis (no_types, lifting) UnE universal_structure.simps(1) universal_structure.simps(2) universals_def)
  subgoal premises P for U1 U2 
    using P test1_subsumes_antisym by blast
  using test1_subsumes_trans by blast 

interpretation test1: universal_structure test1_universal_structure by simp

definition "test1_instantiation_structure \<equiv> \<lparr>
    indiv_structure = test1_individual_structure,
    univ_structure = test1_universal_structure,
    iof = test1_iof \<rparr>"

context

fixes IS (structure)
assumes IS[simp]: "IS = test1_instantiation_structure"
begin

interpretation instantiation_structure_defs IS .

interpretation individual_structure \<I>\<S>
  by (simp add:  test1_instantiation_structure_def)

interpretation universal_structure \<U>\<S>
  by (simp add:  test1_instantiation_structure_def)

lemma test1_instantiation_structure_iof_agrees_with_subsumes:
    "U\<^sub>1 \<preceq> U\<^sub>2 \<longleftrightarrow> U\<^sub>1 \<in> \<U> \<and> (\<forall>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<longrightarrow> x \<Colon>\<^bsub>w\<^esub> U\<^sub>2)" (is "?P \<longleftrightarrow> ?Q")
proof -
  have A: "U\<^sub>1 \<preceq> U\<^sub>2 \<longleftrightarrow> test1_subsumes U\<^sub>1 U\<^sub>2" by (simp add: test1_instantiation_structure_def test1_universal_structure_def) 
  have B: "x \<Colon>\<^bsub>w\<^esub> U \<longleftrightarrow> test1_iof x w U" for x w U by (simp add: test1_instantiation_structure_def)
  have C: "test1_subsumes U\<^sub>1 U\<^sub>2 \<Longrightarrow> U\<^sub>1 \<in> \<U>"
    apply (cases U\<^sub>1 U\<^sub>2 rule: test1_subsumes_scope ; simp)
    by (simp add: test1_instantiation_structure_def universals_def test1_universal_structure_def )+
  have D: "\<forall>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<longrightarrow> x \<Colon>\<^bsub>w\<^esub> U\<^sub>2" if "test1_subsumes U\<^sub>1 U\<^sub>2"
    apply (auto simp: test1_instantiation_structure_def)
    subgoal using that by blast 
    subgoal using that by blast
    using that by (meson tranclp_trans) 
  have E: "?P \<Longrightarrow> ?Q" using A B C D by metis  
  
  define X where "X \<equiv> { (A,B) | A B . A \<in> test1_universals \<and> B \<in> test1_universals \<and>
                                       (\<forall>x w. x \<Colon>\<^bsub>w\<^esub> A \<longrightarrow> x \<Colon>\<^bsub>w\<^esub> B)}" 
  have X1: "(A,C) \<in> X" if "(A,B) \<in> X" "(B,C) \<in> X" for A B C
    using that X_def by auto
  have X2: "(A,A) \<in> X"  if "A \<in> test1_universals" for A using that X_def by auto
  have X3: "\<And>x w. x \<Colon>\<^bsub>w\<^esub> A \<longleftrightarrow> x \<Colon>\<^bsub>w\<^esub> B" if "(A,B) \<in> X" "(B,A) \<in> X" for A B using that X_def by auto
  have "A = B" if as:"\<And>x w. x \<Colon>\<^bsub>w\<^esub> A \<longleftrightarrow> x \<Colon>\<^bsub>w\<^esub> B" "A \<in> test1_universals" "B \<in> test1_universals" for A B
  using as proof (cases A)
    case (T1U_MU x)
    note P1 = this  
    then show ?thesis
    proof (cases B)
      case (T1U_MU y)
      show ?thesis
        apply (simp add: P1 T1U_MU)
        apply (insert as[simplified P1 T1U_MU] ; cases x ; cases y ; hypsubst ; 
           simp add: test1_substantial_universals_def test1_moment_universals_def
                 test1_instantiation_structure_def ; clarify?)
        subgoal sledgehammer[verbose,timeout=120] sorry
        subgoal sledgehammer[verbose,timeout=120] sorry
        subgoal sledgehammer[verbose,timeout=120] sorry
        subgoal sledgehammer[verbose,timeout=120] sorry
        subgoal sledgehammer[verbose,timeout=120] sorry
        subgoal sledgehammer[verbose,timeout=120] sorry
        done
      proof (cases y ; simp add: P1 T1U_MU ; simp)
        sorry
    next
      case (T1U_SU y)
      then show ?thesis sorry
    qed
  next
    case (T1U_SU x)
    then show ?thesis sorry
  qed


  have X2: "(A,B) \<in> X" if 
  have "test1_subsumes U\<^sub>1 U\<^sub>2" 
    if AA: "U\<^sub>1 \<in> test1_substantial_universals" 
       "\<And>x w. x \<Colon>\<^bsub>w\<^esub> U\<^sub>1 \<Longrightarrow> x \<Colon>\<^bsub>w\<^esub> U\<^sub>2"
  proof -
    have BB:"U\<^sub>1 \<in> test1_universals" using AA(1) by simp
    show ?thesis
      apply (simp add: AA ; cases "U\<^sub>1 = U\<^sub>2" ; simp)
    using that apply (cases U\<^sub>1 ; cases U\<^sub>2 ; clarsimp)
    subgoal for a b by (simp add: test1_substantial_universals_def)
    subgoal for a b by (simp add: test1_substantial_universals_def)
    subgoal for a b 
      apply (clarsimp simp: test1_instantiation_structure_def)
      apply (cases a ; simp ; cases b ; auto simp: test1_substantial_universals_def test1_moment_universals_def)
      (* slow *)      
      by (smt Sortals2.test1_iof'.simps(17) T1I_Undefined Test1_SubstantialUniversal.exhaust local.things test1_iof'.simps(18) test1_iof'.simps(20) test1_iof'.simps(30) test1_iof'.simps(39) test1_iof'.simps(57) test1_subsumes_1.simps(2) test1_subsumes_1.simps(3) test1_subsumes_1.simps(4) test1_subsumes_1.simps(5) test1_subsumes_1.simps(78) test1_subsumes_1.simps(8) tranclp.simps)
    subgoal for a b
      apply (clarsimp simp: test1_instantiation_structure_def)
      sledgehammer sorry
    done
  oops
  
  

end
(* lemma test1_instantiation_structure[simp,intro!]:
    "instantiation_structure test1_instantiation_structure"
  apply ( intro_locales ;
      simp add: test1_instantiation_structure_def test1.inherence_structure_axioms
                existence_structure.axioms(2) test1.existence_structure_axioms 
                individual_structure.axioms(2) )    
  apply (unfold_locales)      
  subgoal G1 for U1 U2 
    apply (auto simp: 
          test1_universal_structure_def
          universals_def)
    subgoal using test1_subsumes_scope by metis
    subgoal by (meson tranclp_trans) 
    subgoal  sorry
    subgoal  sorry
    done
  subgoal G2 for x w u
    apply (auto simp: 
          test1_universal_structure_def
          universals_def 
          test1_individual_structure_def
          test1_existence_structure_def
          test1_inherence_structure_def
          inherence_structure.extend_def
          existence_structure.extend_def)
    subgoal sorry
    subgoal sorry
    subgoal sorry
    subgoal by (metis test1_subsumes_1_scope tranclp.simps)
    done
  subgoal G3 for U sorry
  subgoal G4 for w x sorry
  subgoal G5 for x u  sledgehammer sorry
  subgoal G6 for m w w' sledgehammer sorry
  subgoal G7 for U1 U2  sledgehammer sorry
  subgoal G8 for U  sledgehammer sorry
  subgoal G9 for m\<^sub>1 U' m\<^sub>2 x  sledgehammer sorry
  done *)
    
                

end

(*
locale test = 
  instantiation_structure IS
  for IS :: "('i,'u) instantiation_structure" (structure) +
  fixes red_big_sphere red_small_sphere green_big_sphere green_small_sphere :: 'i and
    red_square green_square :: 'i and
    red_big_sphere_being_red red_big_sphere_being_big red_big_sphere_being_sphere
    red_small_sphere_being_red red_small_sphere_being_small red_small_sphere_being_sphere
    green_big_sphere_being_green green_big_sphere_being_big green_big_sphere_being_sphere
    green_small_sphere_being_green green_small_sphere_being_small green_small_sphere_being_sphere :: 'i and
    red_square_being_red red_square_being_square
    green_square_being_green green_square_being_square :: 'i and
    colored_things variable_size_things shaped_things 
    spheres squares big_spheres small_spheres green_squares :: 'u and
    color_moment size_moment shape_moment :: 'u
  assumes
    substantials[simp]: "substantials \<I>\<S> = { red_big_sphere, red_small_sphere, green_big_sphere, green_small_sphere,
                                    red_square, green_square }" and
    moments[simp]: "moments \<I>\<S> = { 
      red_big_sphere_being_red, red_big_sphere_being_big, red_big_sphere_being_sphere,
      red_small_sphere_being_red, red_small_sphere_being_small, red_small_sphere_being_sphere,
      green_big_sphere_being_green, green_big_sphere_being_big, green_big_sphere_being_sphere,
      green_small_sphere_being_green, green_small_sphere_being_small,
      green_small_sphere_being_sphere 
    }" and
    worlds[simp]: "worlds \<I>\<S> = {{},individuals \<I>\<S>}"
    
begin

private definition "S \<equiv> { red_big, red_small, green_big, green_small }"

end


*)
end



