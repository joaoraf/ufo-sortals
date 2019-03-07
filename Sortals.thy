theory Sortals
  imports Projection 
begin

context instantiation_structure_defs
begin
definition sortal  where
  "sortal U \<equiv> 
      U \<in> \<U>\<^sub>s\<^sub>* \<and> 
      (\<forall>p \<in> ProjEquiPerms U. (\<forall>x. x \<Colon>\<^sub>\<diamondop> U \<longrightarrow> p x = x))"


lemma sortalI:
  assumes "U \<in> \<U>\<^sub>s\<^sub>*"
    "\<And>p x. \<lbrakk> p \<in> ProjEquiPerms U ; x \<Colon>\<^sub>\<diamondop> U \<rbrakk> \<Longrightarrow> p x = x"
  shows "sortal U"
  using assms by (auto simp: sortal_def)

lemma sortalE:
  assumes "sortal U"
  obtains 
    "U \<in> \<U>\<^sub>s\<^sub>*"
    "\<And>p x. \<lbrakk> p \<in> ProjEquiPerms U ; x \<Colon>\<^sub>\<diamondop> U \<rbrakk> \<Longrightarrow> p x = x" 
  using assms by (auto simp: sortal_def)

lemma sortals_are_substantials: "sortal U \<Longrightarrow> U \<in> \<U>\<^sub>s\<^sub>*" 
  using sortalE by blast

lemma sortal_instances_are_perm_invariant: 
  "\<lbrakk> sortal U ; p \<in> ProjEquiPerms U ; x \<Colon>\<^sub>\<diamondop> U \<rbrakk> \<Longrightarrow>  p x = x" 
  using sortalE by metis

definition Sortals where "Sortals \<equiv> Collect sortal"

lemmas SortalsI[intro!] = CollectI[of sortal,simplified Sortals_def[symmetric]]

lemmas SortalsD[dest!] = CollectD[of _ sortal,simplified Sortals_def[symmetric]]

(*
definition strong_sortal where
  "strong_sortal U \<equiv> U \<in> \<U>\<^sub>s\<^sub>* \<and>      
          (\<forall>w \<in> worlds (project U). \<forall>p \<in> ProjEquiPerms U. p ` w = w \<longrightarrow> (\<forall>x \<in> w. p x = x))"

lemma strong_sortal_I[intro!]:
  fixes U
  assumes "U \<in> \<U>\<^sub>s\<^sub>*" "\<And>w p x. 
    \<lbrakk> w \<in> worlds (project U) ; 
      p \<in> ProjEquiPerms U ; 
      p ` w = w ; x \<in> w \<rbrakk> \<Longrightarrow> p x = x"
  shows "strong_sortal U"
  using assms by (auto simp: strong_sortal_def)

lemma strong_sortal_imp_id:
  fixes U w p x
  assumes 
    "strong_sortal U"
    "w \<in> worlds (project U)"
    "p \<in> ProjEquiPerms U"
    "p ` w = w"
    "x \<in> w"
  shows "p x = x"
  using assms by (auto simp: strong_sortal_def)

lemma strong_sortal_is_subst_sortal[dest]:  "strong_sortal U \<Longrightarrow> U \<in> \<U>\<^sub>s\<^sub>*"
  by (auto simp: strong_sortal_def)

definition "StrongSortals \<equiv> Collect strong_sortal"

lemmas StrongSortalsI[intro!] = CollectI[of strong_sortal,simplified StrongSortals_def[symmetric]]
lemmas StrongSortalsD[dest!] = CollectD[of _ strong_sortal,simplified StrongSortals_def[symmetric]]
*)
end

context instantiation_structure
begin

lemma sortal_mono: 
  assumes "U \<in> Sortals" "U' \<preceq>\<^sub>s\<^sub>* U"
  shows "U' \<in> Sortals"
  apply (intro SortalsI sortalI)
  subgoal using assms(2)  by auto  
proof -
  fix p x
  assume as: "p \<in> ProjEquiPerms U'" "x \<Colon>\<^sub>\<diamondop> U'" 
  have A0: "p \<in> ProjEquiPerms U" 
    using proj_equi_perms_mono[OF assms(2)] subsetD as(1) by metis  
  obtain A: "U \<in> \<U>\<^sub>s\<^sub>*" "U' \<in> \<U>\<^sub>s\<^sub>*"  using assms(2) by auto
  obtain A1: "x \<Colon>\<^sub>\<diamondop> U" using as(2) assms(2) subsumesI_S miof_agrees_with_subsumes by metis  
  obtain B: "\<And>p x. \<lbrakk> p \<in> ProjEquiPerms U ; x \<Colon>\<^sub>\<diamondop> U \<rbrakk> \<Longrightarrow> p x = x" 
    using assms(1) SortalsD sortalE by metis
  then show C: "p x = x" using A0 A1 by metis    
qed

lemma sortal_neg_anti_mono: 
  assumes "U \<notin> Sortals" "U \<preceq>\<^sub>s\<^sub>* U'"
  shows "U' \<notin> Sortals" using assms sortal_mono by metis


(*
lemma strong_sortal_imp_sortal: "StrongSortals \<subseteq> Sortals"
  apply (intro subsetI SortalsI sortalI ; elim StrongSortalsD[elim_format])
  subgoal using strong_sortal_is_subst_sortal by simp
proof -
  fix U p x
  assume A: "p \<in> ProjEquiPerms U" "x \<Colon>\<^sub>\<diamondop> U" "strong_sortal U"   
  let ?IS = "projected_structure U"
  have B[iff]: "U \<in> \<U>\<^sub>s\<^sub>*" using A(3) strong_sortal_is_subst_sortal by simp
  interpret IS': individual_structure ?IS by simp
  obtain C: "p \<in> IS'.Perms" "\<And>x. x \<in> \<I>\<^bsub>?IS\<^esub> \<Longrightarrow> x \<sim> p x"
    using individual_structure_defs.ClosedPermsE[OF A(1)] by metis
  interpret p_perm: individual_structure_permutation_morphism ?IS p
    using C by blast
  have D: "p x = x" if "w \<in> \<W>\<^bsub>?IS\<^esub>" "p ` w = w" "x \<in> w" for w
    using strong_sortal_imp_id[OF A(3),OF _ A(1),where ?x = x] that by metis
  have E: "x \<in> \<S>\<^sub>*" using A(2) B  by (meson iof_S_U_simp miof_E)
  then obtain w where F: "w \<in> \<W>\<^sub>*" "x \<in> w" using individuals_iff by auto
  then obtain w' where G: "w' \<in> \<W>\<^bsub>?IS\<^esub>" "w' = w - excluded_moments U" 
    by auto
  have H: "x \<in> w'" using E F G excluded_moments_are_moments by blast
  have I: "p ` w' = w'"
  show "p x = x" sorry
qed
*)

end

end

