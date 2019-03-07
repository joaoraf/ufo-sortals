theory Individuals
  imports Common
begin

record 'i individual_structure =
  individuals :: "'i set" ("\<I>\<index>")
  inheres_in :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infix "\<triangleleft>\<index>" 75)
  exactly_similar_to :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infix "\<simeq>\<index>" 75)
  worlds :: "'i set set" ("\<W>\<index>")
  refers_to :: "'i \<Rightarrow> 'i \<Rightarrow> bool" (infix "\<hookrightarrow>\<index>" 75) 


lemma individual_structure_eqI:
  fixes A B :: "'i individual_structure"
  assumes "\<I>\<^bsub>A\<^esub> = \<I>\<^bsub>B\<^esub>" "(\<triangleleft>\<^bsub>A\<^esub>) = (\<triangleleft>\<^bsub>B\<^esub>)" "(\<simeq>\<^bsub>A\<^esub>) = (\<simeq>\<^bsub>B\<^esub>)" 
          "\<W>\<^bsub>A\<^esub> = \<W>\<^bsub>B\<^esub>" "(\<hookrightarrow>\<^bsub>A\<^esub>) = (\<hookrightarrow>\<^bsub>B\<^esub>)"
  shows "A = B"
  using assms by auto

definition substantials :: "'i individual_structure \<Rightarrow> 'i set" ("\<S>\<index>") where
    "\<S> \<equiv> { x . x \<in> \<I> \<and> (\<forall>y. \<not> x \<triangleleft> y) }"
  for IS :: "'i individual_structure" (structure)

lemma substantialsI[intro!]:
  fixes IS :: "'i individual_structure" (structure)
  assumes "x \<in> \<I>" "\<And>y. \<not> x \<triangleleft> y"
  shows "x \<in> \<S>"
  using assms by (auto simp: substantials_def)

lemma substantialsE[elim!]:
  fixes IS :: "'i individual_structure" (structure)
  assumes "x \<in> \<S>"
  obtains "x \<in> \<I>" "\<And>y. \<not> x \<triangleleft> y"
  using assms by (auto simp: substantials_def)

definition moments :: "'i individual_structure \<Rightarrow> 'i set" ("\<M>\<index>") where
    "\<M> \<equiv> { x . x \<in> \<I> \<and> (\<exists>y. x \<triangleleft> y) }"
  for IS :: "'i individual_structure" (structure)

definition bearer :: "'i individual_structure \<Rightarrow> 'i \<Rightarrow> 'i" ("\<beta>\<index>") where
    "\<beta> x \<equiv> if (\<exists>y. x \<triangleleft> y) then (THE y. x \<triangleleft> y) else undefined"
  for IS :: "'i individual_structure" (structure)

definition existentially_dependent :: "'i individual_structure \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> bool" ("ed\<index>") where
  "ed x y \<equiv> x \<in> \<I> \<and> y \<in> \<I> \<and> (\<forall>w \<in> \<W>. x \<in> w \<longrightarrow> y \<in> w)"
  for IS :: "'i individual_structure" (structure) 

lemma ed_I[intro!]: "\<lbrakk> x \<in> \<I> ; y \<in> \<I> ; \<forall>w. w \<in> \<W> \<and> x \<in> w \<longrightarrow> y \<in> w \<rbrakk> \<Longrightarrow> ed x y" for IS (structure)
  by (auto simp: existentially_dependent_def)

(* UNUSED lemma ed_I_1: "\<lbrakk> x \<in> \<I> ; y \<in> \<I> ; \<And>w. \<lbrakk> w \<in> \<W> ; x \<in> w \<rbrakk> \<Longrightarrow> y \<in> w \<rbrakk> \<Longrightarrow> ed x y" for IS (structure)
  by (auto) *)

lemma ed_E[elim!]: "\<lbrakk> ed x y ; \<lbrakk> x \<in> \<I> ; y \<in> \<I> ; \<forall>w. w \<in> \<W> \<and> x \<in> w \<longrightarrow> y \<in> w \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" for IS (structure)
  by (auto simp: existentially_dependent_def)

(* UNUSED lemma ed_E_1: "\<lbrakk> ed x y ; \<And>x y. \<lbrakk> x \<in> \<I> ; y \<in> \<I> ; \<And>w. \<lbrakk> w \<in> \<W> ; x \<in> w \<rbrakk> \<Longrightarrow> y \<in> w \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" for IS (structure)
  by (auto) *)

(* UNUSED lemma ed_refl[intro!]: "x \<in> \<I> \<Longrightarrow> ed x x" for IS (structure)
  using ed_I by metis *)

(* UNUSED lemma ed_trans[trans]: "\<lbrakk> ed x y ; ed y z \<rbrakk> \<Longrightarrow> ed x z" for IS (structure)
  by (auto simp: existentially_dependent_def) *)

lemma moments_subset_individuals[simp,intro!]: "\<M> \<subseteq> \<I>"
  for IS :: "'i individual_structure" (structure)  
  by (simp add: moments_def subset_eq)

lemma substantials_subset_individuals[simp,intro!]: "\<S> \<subseteq> \<I>"
  for IS :: "'i individual_structure" (structure)
  by blast

locale individual_structure_defs = 
  fixes IS :: "'i individual_structure" (structure)
begin

end



locale individual_structure =
  individual_structure_defs  +
  assumes
    undefined_not_in_individuals[iff]: "undefined \<notin> \<I>" and

    inheres_in_scope: "x \<triangleleft> y \<Longrightarrow> x \<in> \<I> \<and> y \<in> \<I>" and
    inheres_in_sep: "x \<triangleleft> y \<Longrightarrow> \<not> y \<triangleleft> z" and
    inheres_in_single[dest]: "\<lbrakk> x \<triangleleft> y ; x \<triangleleft> z \<rbrakk> \<Longrightarrow> y = z" and

    exactly_similar_scope: "x \<simeq> y \<Longrightarrow> x \<in> \<M> \<and> y \<in> \<M>" and
    exactly_similar_refl[intro!]: "x \<in> \<M> \<Longrightarrow> x \<simeq> x" and
    exactly_similar_trans[trans]: "\<lbrakk> x \<simeq> y ; x \<simeq> z \<rbrakk> \<Longrightarrow> x \<simeq> z" and
    exactly_similar_sym[sym]: "x \<simeq> y \<Longrightarrow> y \<simeq> x"  and

    empty_world[iff]: "{} \<in> \<W>" and
    worlds_are_made_of_individuals: "w \<in> \<W> \<Longrightarrow> w \<subseteq> \<I>" and
    every_individual_exists_somewhere: "x \<in> \<I> \<Longrightarrow> \<exists>w \<in> \<W>. x \<in> w" and
    inherence_imp_ed: "x \<triangleleft> y \<Longrightarrow> ed x y" and

    refers_to_scope: "x \<hookrightarrow> y \<Longrightarrow> x \<in> \<M> \<and> y \<in> \<S>" and
    refers_to_diff_bearer: "\<lbrakk> x \<hookrightarrow> y ; x \<triangleleft> z \<rbrakk> \<Longrightarrow> z \<noteq> y" and 
    refers_to_imp_ed: "x \<hookrightarrow> y \<Longrightarrow> ed x y" (* and

    moment_uniqueness: "\<lbrakk> x \<triangleleft> z ; y \<triangleleft> z ; x \<simeq> y ; \<forall>s. x \<hookrightarrow> s \<longleftrightarrow> y \<hookrightarrow> s \<rbrakk> \<Longrightarrow> x = y" *)

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

(* UNUSED lemma substantials_eq_diff: "\<S> = \<I> - \<M>" 
  using individuals_moments_substantials substantials_moments_disj by blast *)

(* UNUSED lemma moments_eq_diff: "\<M> = \<I> - \<S>" 
  using individuals_moments_substantials substantials_moments_disj by blast *)

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

(* UNUSED lemma bearer_eqE:
  assumes "\<beta> x = y"
  obtains "x \<in> \<M> \<Longrightarrow> x \<triangleleft> y"
  using assms by blast *)


lemma inheres_in_scope_2:
  assumes "x \<triangleleft> y"
  obtains "x \<in> \<M>" "y \<in> \<S>"
  using assms 
  by (simp add: momentsI substantialsI2)

lemma inheres_in_scope_D:
  assumes "x \<triangleleft> y"
  shows "x \<in> \<M>" "y \<in> \<S>"
  using assms by (auto elim!: inheres_in_scope_2)  

lemma inheres_in_out_scope: "x \<notin> \<M> \<Longrightarrow> \<not> x \<triangleleft> y" "x \<notin> \<S> \<Longrightarrow> \<not> y \<triangleleft> x"
  using inheres_in_scope_2 by metis+

lemma moments_are_individuals[dest]: "x \<in> \<M> \<Longrightarrow> x \<in> \<I>" 
  by (meson moments_subset_individuals subset_iff)

lemma substantials_are_individuals[dest]: "x \<in> \<S> \<Longrightarrow> x \<in> \<I>" by blast

lemma substantials_moments_disj_2[dest]: "\<lbrakk> x \<in> \<M> ; x \<in> \<S> \<rbrakk> \<Longrightarrow> False" by blast

lemma undefined_not_in_moments[iff]: "undefined \<notin> \<M>"
  by (meson moments_are_individuals undefined_not_in_individuals)
lemma undefined_not_in_substantials[iff]: "undefined \<notin> \<S>" 
  using undefined_not_in_individuals by blast

lemma inheres_in_sep_2[dest]:  "\<lbrakk> x \<triangleleft> y ; y \<triangleleft> z \<rbrakk> \<Longrightarrow> False" 
  using inheres_in_sep by blast

lemma exactly_similar_sym_iff[iff]: "x \<simeq> y \<longleftrightarrow> y \<simeq> x"  
  using exactly_similar_sym by blast

lemma individuals_iff: "x \<in> \<I> \<longleftrightarrow> (\<exists>w. w \<in> \<W> \<and> x \<in> w)" 
  using worlds_are_made_of_individuals
    every_individual_exists_somewhere       
  by (meson contra_subsetD)

(* UNUSED lemma ed_intro_1: "x \<triangleleft> y \<or> x \<hookrightarrow> y  \<Longrightarrow> ed x y" 
  using inherence_imp_ed refers_to_imp_ed by metis *)

lemma ed_scope: "ed x y \<Longrightarrow> x \<in> \<I> \<and> y \<in> \<I>"
  by blast

lemma undefined_simps[iff]: 
  "\<not> undefined \<triangleleft> x" "\<not> x \<triangleleft> undefined"
  "\<not> undefined \<simeq> x" "\<not> x \<simeq> undefined"
  "\<not> undefined \<hookrightarrow> x" "\<not> x \<hookrightarrow> undefined"
  "\<not> ed undefined x" "\<not> ed x undefined"
  using undefined_not_in_moments undefined_not_in_substantials undefined_not_in_individuals
    inheres_in_scope refers_to_scope exactly_similar_scope ed_scope
  by metis+

(* UNUSED lemma bearer_non_moment[simp,intro!]: "\<beta> x \<notin> \<M>"  
  by (metis bearer_def bearer_eq inheres_in_sep momentsE undefined_not_in_moments) *)

lemma bearer_ex1[dest]:
  assumes "w \<in> \<W>" "x \<in> w" "x \<triangleleft> y"
  shows "y \<in> w"
  using assms inherence_imp_ed ed_E by metis


end




end
