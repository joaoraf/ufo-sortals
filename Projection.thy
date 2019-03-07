theory Projection
  imports Instantiation IndividualSubStructure IndividualMorphisms
begin

context instantiation_structure_defs
begin

definition excluded_moments where
  "excluded_moments U \<equiv> { m . m \<in> \<M>\<^sub>* \<and> \<beta>\<^sub>* m \<Colon>\<^sub>\<diamondop> U \<and> (\<forall>u'. char_by\<^sub>* U u' \<longrightarrow> \<not> m \<Colon>\<^sub>m\<^sub>\<diamondop> u')}"

lemma excluded_moments_I[intro]:
  assumes "m \<in> \<M>\<^sub>*" "\<beta>\<^sub>* m \<Colon>\<^sub>\<diamondop> U"  "\<And>u'. char_by\<^sub>* U u' \<Longrightarrow> \<not> m \<Colon>\<^sub>m\<^sub>\<diamondop> u'"
  shows "m \<in> excluded_moments U"
  using assms by (auto simp: excluded_moments_def)

lemma excluded_moments_E[elim]:
  assumes "m \<in> excluded_moments U" 
  obtains x where "m \<in> \<M>\<^sub>*" "\<beta>\<^sub>* m \<Colon>\<^sub>\<diamondop> U"  "\<And>u'. char_by\<^sub>* U u' \<Longrightarrow> \<not> m \<Colon>\<^sub>m\<^sub>\<diamondop> u'"
  using assms by (auto simp: excluded_moments_def)

lemma excluded_moments_iff:
  "m \<in> excluded_moments U \<longleftrightarrow> m \<in> \<M>\<^sub>* \<and> \<beta>\<^sub>* m \<Colon>\<^sub>\<diamondop> U \<and> (\<forall>u'. char_by\<^sub>* U u' \<longrightarrow> \<not> m \<Colon>\<^sub>m\<^sub>\<diamondop> u')"
  by blast

definition project  where
  "project U \<equiv>  \<lparr>
             individuals = \<I>\<^sub>* - (excluded_moments U),
             inheres_in = (\<lambda>x y. x \<triangleleft>\<^sub>* y \<and> x \<notin> excluded_moments U),
             exactly_similar_to = (\<lambda>x y. x \<simeq>\<^sub>* y \<and> x \<notin> excluded_moments U \<and> y \<notin> excluded_moments U),
             worlds = { w - excluded_moments U | w . w \<in> \<W>\<^sub>* },
             refers_to = (\<lambda>x y. x \<hookrightarrow>\<^sub>* y \<and> x \<notin> excluded_moments U)
          \<rparr>"

lemma project_simps:
  "individuals (project U) = \<I>\<^sub>* - (excluded_moments U)" 
  "inheres_in (project U) =  (\<lambda>x y. x \<triangleleft>\<^sub>* y \<and> x \<notin> excluded_moments U)" 
  "exactly_similar_to (project U) = (\<lambda>x y. x \<simeq>\<^sub>* y \<and> x \<notin> excluded_moments U \<and> y \<notin> excluded_moments U)"
  "worlds (project U)  = { w - excluded_moments U | w . w \<in> \<W>\<^sub>* }" 
  "refers_to (project U) = (\<lambda>x y. x \<hookrightarrow>\<^sub>* y \<and> x \<notin> excluded_moments U)"
  "moments (project U) = \<M>\<^sub>* - excluded_moments U"
  "substantials (project U) = \<S>\<^sub>*"
  by (auto simp add: project_def excluded_moments_def moments_def)    

declare project_simps(2,3,4,5,6,7)[simp]

abbreviation "ProjEquiPerms U \<equiv>
  individual_structure_defs.ClosedPerms (project U) (\<sim>)"

end

context instantiation_structure
begin


context
  fixes U
  assumes U_subst_univ[simp,intro!]:"U \<in> \<U>\<^sub>s\<^sub>*" 
begin

abbreviation projected_structure :: "'i individual_structure" ("IS\<^sup>\<down>")  where
  "IS\<^sup>\<down> \<equiv>  project U"

abbreviation projected_out_moments :: "'i set" ("\<Delta>")  where   
  "\<Delta> \<equiv> excluded_moments U"

private abbreviation projected_moments ("\<M>\<^sup>\<down>")
  where "\<M>\<^sup>\<down> \<equiv> moments IS\<^sup>\<down>"

private abbreviation projected_individuals ("\<I>\<^sup>\<down>")
  where "\<I>\<^sup>\<down> \<equiv> individuals IS\<^sup>\<down>"

private abbreviation projected_worlds ("\<W>\<^sup>\<down>")
  where "\<W>\<^sup>\<down> \<equiv> worlds IS\<^sup>\<down>"

abbreviation projected_inheres_in (infix "\<triangleleft>\<^sup>\<down>" 75)
  where "(\<triangleleft>\<^sup>\<down>) \<equiv> inheres_in IS\<^sup>\<down>"

abbreviation projected_similar_to (infix "\<simeq>\<^sup>\<down>" 75) where
  "(\<simeq>\<^sup>\<down>) \<equiv> exactly_similar_to IS\<^sup>\<down>"

abbreviation projected_refers_to (infix "\<hookrightarrow>\<^sup>\<down>" 75) where
  "(\<hookrightarrow>\<^sup>\<down>) \<equiv> refers_to IS\<^sup>\<down>"


abbreviation projected_bearer ("\<beta>\<^sup>\<down>") where
  "\<beta>\<^sup>\<down> \<equiv> bearer IS\<^sup>\<down>"

abbreviation projected_ed ("ed\<^sup>\<down>") where
  "ed\<^sup>\<down> \<equiv> existentially_dependent IS\<^sup>\<down>"

lemma delta_closed_on_sim[simp,intro!]: "closure_rel_P (\<sim>) \<Delta>"
proof -
  interpret P: closure_rel_P "(\<sim>)" "\<I>\<^sub>*" by simp
  have A: "\<forall>x. x \<in> \<Delta> \<longrightarrow> x \<sim> x" using P.refl inheres_in_scope by auto
  have B: "\<forall>x y. x \<sim> y \<longrightarrow> y \<sim> x" by auto
  have C: "\<forall>x y z. x \<sim> y \<longrightarrow> y \<sim> z \<longrightarrow> x \<sim> z" by (meson P.trans)
  show ?thesis
  proof (unfold_locales ; (atomize (full))? ; (intro A B C)? ; safe)
    fix x y
    assume as: "x \<sim> y" "x \<in> \<Delta>"
    obtain D: "x \<in> \<M>\<^sub>*" "\<beta>\<^sub>* x \<Colon>\<^sub>\<diamondop> U" "\<And>u'. char_by\<^sub>* U u' \<Longrightarrow> \<not> x \<Colon>\<^sub>m\<^sub>\<diamondop> u'"
      using as(2) by blast
    obtain E: "y \<in> \<M>\<^sub>*" "x \<sim>\<^sub>m y" using equi_instances_simps(3)[OF D(1),of y] as(1) by metis
    obtain F[simp]: "\<And>u. x \<Colon>\<^sub>m\<^sub>\<diamondop> u = y \<Colon>\<^sub>m\<^sub>\<diamondop> u" and G: "\<beta>\<^sub>* x \<sim>\<^sub>s \<beta>\<^sub>* y"
      using equi_instances_M_E[OF E(2)] by metis
    obtain H: "\<beta>\<^sub>* x \<in> \<S>\<^sub>*" "\<beta>\<^sub>* y \<in> \<S>\<^sub>*" and I[simp]: "\<And>U w. \<beta>\<^sub>* x \<Colon>\<^sub>s\<^bsub>w\<^esub> U = \<beta>\<^sub>* y \<Colon>\<^sub>s\<^bsub>w\<^esub> U"
      using equi_instances_S_E[OF G] by metis
    obtain w\<^sub>x where J: "\<beta>\<^sub>* x \<Colon>\<^sub>s\<^bsub>w\<^sub>x\<^esub> U" using D(2) H(1) by (meson iof_S_simp miof_E)
    obtain K: "w\<^sub>x \<in> \<W>\<^sub>*" "\<beta>\<^sub>* x \<in> w\<^sub>x" "\<And>u. u \<in> char_set\<^sub>* U \<Longrightarrow> \<exists>m. m \<triangleleft>\<^sub>* \<beta>\<^sub>* x \<and> m \<Colon>\<^sub>m\<^bsub>w\<^sub>x\<^esub> u"
      using substantial_iof_E[OF J] by metis
    obtain L: "\<beta>\<^sub>* y \<Colon>\<^sub>s\<^bsub>w\<^sub>x\<^esub> U" using I[THEN iffD1,OF J(1)] by metis
    then have L1: "\<beta>\<^sub>* y \<in> w\<^sub>x" by blast
    obtain M: "\<beta>\<^sub>* y \<Colon>\<^sub>\<diamondop> U" using L miof_I iof_S_I by metis
    have N: " \<forall>u'. char_by\<^sub>* U u' \<longrightarrow> \<not> y \<Colon>\<^sub>m\<^sub>\<diamondop> u'"
    proof (intro allI impI notI)
      fix u' 
      assume AA: "char_by\<^sub>* U u'" and BB: "y \<Colon>\<^sub>m\<^sub>\<diamondop> u'"
      then have "x \<Colon>\<^sub>m\<^sub>\<diamondop> u'" by simp
      then show False using D(3)[OF AA] by simp      
    qed
    show "y \<in> \<Delta>"
      by (intro excluded_moments_I E(1) M ; atomize (full) ; intro N)
  qed
qed

interpretation delta_closure: closure_rel_P "(\<sim>)" \<Delta> by simp

lemma proj_indiv_closed_on_sim[simp,intro!]: "closure_rel_P (\<sim>) (\<I>\<^sup>\<down>)"
  by (simp only: project_simps(1) ; intro closure_rel_combs(3) ; simp)

lemma substantials_closed_on_sim[simp,intro!]: "closure_rel_P (\<sim>) \<S>\<^sub>*"
  apply (unfold_locales)
  subgoal G1 by blast
  apply (simp only: equi_instances_iff ; elim disjE conjE ; simp)
  using substantials_moments_disj_2 by metis

lemma moments_closed_on_sim[simp,intro!]: "closure_rel_P (\<sim>) \<M>\<^sub>*"
  apply (subgoal_tac "\<M>\<^sub>* = \<I>\<^sub>* - \<S>\<^sub>*")
  subgoal using closure_rel_combs(3)[of "(\<sim>)" "\<I>\<^sub>*" "\<S>\<^sub>*"] by auto
  apply (simp only: individuals_moments_substantials)
  using substantials_moments_disj by blast

lemma projected_out_moments_are_moments:  "\<Delta> \<subseteq> \<M>\<^sub>*"
  by (meson momentsI excluded_moments_iff subsetI)

lemma project_individuals_eq: "\<I>\<^sup>\<down> = \<S>\<^sub>* \<union> \<M>\<^sub>* - \<Delta>"
  by (simp add: project_simps(1) individuals_moments_substantials)

lemma project_individuals_cases:
  assumes "x \<in> \<I>\<^sup>\<down>"
  obtains (c1) "x \<in> \<S>\<^sub>*" | (c2) "x \<in> \<M>\<^sub>*" "x \<notin> \<Delta>"
  using assms by (simp add: project_individuals_eq ; blast)

lemma project_ed_simp[simp]:
  "ed\<^sup>\<down> x y \<longleftrightarrow> ed\<^sub>* x y \<and> x \<notin> \<Delta> \<and> y \<notin> \<Delta>" (is "?A \<longleftrightarrow> ?B")
proof -
  have C: "\<lbrakk> w \<in> \<W>\<^sup>\<down> ; x \<in> w \<rbrakk> \<Longrightarrow> x \<in> \<I>\<^sub>*" for x w
    apply (simp add: project_individuals_eq ; elim exE conjE ; hypsubst ; elim DiffE)
    using worlds_are_made_of_individuals by blast
  show ?thesis
  proof (*   *)
    assume as: "?A"
    then obtain A: "x \<in> \<I>\<^sup>\<down>" "y \<in> \<I>\<^sup>\<down>"
          "\<And>w. \<lbrakk> w \<in> \<W>\<^sup>\<down> ; x \<in> w \<rbrakk> \<Longrightarrow> y \<in> w"
      using ed_E[OF as]  by (simp ; metis)
    note B = A(1,2)[THEN project_individuals_cases]  
    obtain D[simp,intro!]: "x \<in> \<I>\<^sub>*" "y \<in> \<I>\<^sub>*" using B individuals_moments_substantials Un_iff by metis
    obtain E[simp,intro!]: "x \<notin> \<Delta>" "y \<notin> \<Delta>"
      using A(1,2)         
      by (simp add: project_individuals_eq)
    show "?B"
      apply (intro iffI ed_I allI conjI impI; (elim ed_E conjE)? ; simp?)
      subgoal for w
        using A(3)[simplified, OF exI[of _ w], of "w - \<Delta>",simplified] 
        by metis
      done
  next
    assume as: "?B"    
    then obtain "ed\<^sub>* x y" and A[simp,intro!]: "x \<notin> \<Delta>" "y \<notin> \<Delta>" by metis
    then obtain B: "x \<in> \<I>\<^sub>*" "y \<in> \<I>\<^sub>*" "\<And>w. \<lbrakk> w \<in> \<W>\<^sub>* ; x \<in> w \<rbrakk> \<Longrightarrow> y \<in> w" using ed_E by metis
    obtain D[simp,intro!]: "x \<in> \<I>\<^sup>\<down>" "y \<in> \<I>\<^sup>\<down>"
      using A B(1,2) that by (simp add: project_simps(1))      
    show ?A
      by (intro ed_I ; simp add: B project_simps(1) ; clarify
            ; simp add: B(3))
  qed
qed

    
lemma project_individual_structure[intro!,simp]: "individual_structure IS\<^sup>\<down>"
  supply project_simps(1)[simp]
  apply (unfold_locales ; (simp add: excluded_moments_iff)? 
      ; (elim conjE exE)? ; (intro impI allI)?)
  subgoal G1 using inheres_in_scope by blast
  subgoal G2 by blast
  subgoal G3 using inheres_in_sep by blast
  subgoal G4 using exactly_similar_scope by presburger
  subgoal G6 by (simp add: exactly_similar_refl)
  subgoal G7 by blast
  subgoal G8 by (simp add: Diff_mono worlds_are_made_of_individuals)
  subgoal G9 by (metis Diff_iff excluded_moments_E individuals_iff)
  subgoal G10 using inherence_imp_ed by auto
  subgoal G11 by (simp add: refers_to_scope)
  subgoal G12 by (simp add: refers_to_diff_bearer)
  subgoal G13 by (meson refers_to_imp_ed refers_to_scope substantials_moments_disj_2)  
  done

interpretation IS': individual_structure "IS\<^sup>\<down>" using U_subst_univ by simp

lemma project_substructure: "individual_substructure IS\<^sup>\<down> \<I>\<S>"
proof -
  interpret P: individual_structure "IS\<^sup>\<down>" by simp
  show ?thesis
    apply (intro_locales ; unfold_locales ; clarsimp simp: excluded_moments_iff existentially_dependent_def project_simps(1))
    subgoal G1 by (metis Diff_iff excluded_moments_iff )
    subgoal G2 for w
      apply (rule ccontr ; simp)
      subgoal premises P
        apply (rule notE[OF P(2)[rule_format,of w,simplified] P(1)])
        using projected_out_moments_are_moments P(1) 
              worlds_are_made_of_individuals individuals_moments_substantials 
        by blast
      done
    subgoal G3 premises P for w
      using G2[OF P(1)] apply (elim exE conjE)
      subgoal for w'
        apply (intro exI[of _ w] conjI ; (simp add: P(1))?)
        subgoal premises Q
          apply (simp only: Q(1)[symmetric])
          using projected_out_moments_are_moments P(1) 
              worlds_are_made_of_individuals individuals_moments_substantials 
          by blast
        done
      done
    done
qed

lemma project_out_moments_mono[intro!]:
  assumes "U \<preceq>\<^sub>s\<^sub>* U'"
  shows "\<Delta> \<subseteq> excluded_moments U'"
  apply (intro subsetI)
  subgoal for x
    apply (intro excluded_moments_I)
    subgoal G1 using assms bearer_eq miof_agrees_with_subsumes subsumesI_S by auto
    subgoal G2 using bearer_eq by (meson assms excluded_moments_iff miof_agrees_with_subsumes subsumesI_S)    
    using assms char_by_scope(1) subst_subsumes_by_char_set by auto
  done

lemma individuals_exhaust_2:
  obtains "y \<in> \<I>\<^sub>*" "y \<in> \<S>\<^sub>*" "y \<notin> \<M>\<^sub>*" "y \<notin> \<Delta>" "y \<noteq> undefined"  | 
          "y \<in> \<I>\<^sub>*" "y \<notin> \<S>\<^sub>*" "y \<in> \<M>\<^sub>*" "y \<notin> \<Delta>" "y \<noteq> undefined" |
          "y \<in> \<I>\<^sub>*" "y \<notin> \<S>\<^sub>*" "y \<in> \<M>\<^sub>*" "y \<in> \<Delta>" "y \<noteq> undefined" | 
          "y \<notin> \<I>\<^sub>*" "y \<notin> \<M>\<^sub>*" "y \<notin> \<S>\<^sub>*" "y \<notin> \<Delta>" "y = undefined" |
          "y \<notin> \<I>\<^sub>*" "y \<notin> \<M>\<^sub>*" "y \<notin> \<S>\<^sub>*" "y \<notin> \<Delta>" "y \<noteq> undefined" 
proof -  
  have B: "y \<in> \<Delta> \<Longrightarrow> y \<in> \<M>\<^sub>*" using projected_out_moments_are_moments by blast
  have C: "y \<in> \<S>\<^sub>* \<Longrightarrow> y \<in> \<I>\<^sub>*" by blast
  have D: "y \<in> \<M>\<^sub>* \<Longrightarrow> y \<in> \<I>\<^sub>*" by blast
  have E: "y = undefined \<Longrightarrow> y \<notin> \<I>\<^sub>*" by simp  
  have G: "\<lbrakk> y \<notin> \<S>\<^sub>* ; y \<notin> \<M>\<^sub>* \<rbrakk> \<Longrightarrow> y \<notin> \<I>\<^sub>*" by blast  
  have I: "y \<in> \<M>\<^sub>* \<Longrightarrow> y \<notin> \<S>\<^sub>*"  by blast 
  note simps = B C D E G I
  show ?thesis
    by (cases "y \<in> \<I>\<^sub>*" ; cases "y \<in> \<S>\<^sub>*" ; cases "y \<in> \<M>\<^sub>*" ; cases "y \<in> \<Delta>" ; cases "y = undefined"
        ; insert simps that ; metis)
qed 


context
  fixes \<Omega>
  assumes \<Omega>_EquiPerm[iff]: "\<Omega> \<in> EquiPerms" 
begin

lemma \<Omega>_Perm[iff]: "\<Omega> \<in> Perms" and
      \<Omega>_closed_I[simp]: "\<And>x. x \<in> \<I>\<^sub>* \<Longrightarrow> x \<sim> (\<Omega> x)"
  using ClosedPermsE[OF \<Omega>_EquiPerm] by metis+

interpretation  individual_structure_permutation_morphism \<I>\<S> \<Omega>
  using Perms_def by blast


interpretation m_inv: individual_structure_permutation_morphism \<I>\<S> \<Theta>
  using m_inv_individual_structure_permutation_morphism by simp

interpretation IS'_IS: individual_substructure  "IS\<^sup>\<down>" \<I>\<S> 
  using project_substructure by simp

declare IS'_IS.preserve_inherence[simp del]
    IS'_IS.preserve_exact_similarity[simp del]
    IS'_IS.m_preserve_ext_dep[simp del]

lemmas fliped_IS'_IS_simps[simp] = IS'_IS.preserve_inherence[symmetric]
    IS'_IS.preserve_exact_similarity[symmetric]
    IS'_IS.m_preserve_ext_dep[symmetric]


definition proj_morph ("\<Omega>\<^sup>\<down>") where "\<Omega>\<^sup>\<down> y \<equiv> if y \<in> \<I>\<^sup>\<down> then \<Omega> y else undefined"

private lemma worlds1: "{w \<inter> \<Omega> ` \<I>\<^sub>* |w. w \<in> \<W>\<^sub>*} = \<W>\<^sub>*" for w  
  apply (simp ; intro set_eqI ; simp ; intro iffI ; (elim exE)? ; simp?)
  subgoal for w\<^sub>1 
    by (intro exI[of _ w\<^sub>1] ; simp)
  done



lemma m_preserve_m_iof[simp]: 
  fixes y u
  shows "\<Omega> y \<Colon>\<^sub>m\<^sub>\<diamondop> u \<longleftrightarrow> y \<Colon>\<^sub>m\<^sub>\<diamondop> u" 
proof (intro iffI)
  show "\<Omega> y \<Colon>\<^sub>m\<^sub>\<diamondop> u"  if as:  "y \<Colon>\<^sub>m\<^sub>\<diamondop> u"
  proof -
    obtain A: "y \<in> \<M>\<^sub>*" "\<Omega> y \<in> \<M>\<^sub>*" using as 
      by (simp add: moment_miof_scope)      
    have B: "y \<simeq>\<^sub>* \<Omega> y" using m_strong_preserve_similarity[OF A(1)] by simp
    have C: "\<Omega> y \<Colon>\<^sub>m\<^bsub>w\<^sub>2\<^esub> u" if "y \<Colon>\<^sub>m\<^bsub>w\<^sub>1\<^esub> u" "w\<^sub>2 \<in> \<W>\<^sub>*" "\<Omega> y \<in> w\<^sub>2" for w\<^sub>1 w\<^sub>2 u
      using moment_iof_agrees_with_similarity[OF B,of w\<^sub>1 u w\<^sub>2] that by blast
    obtain w\<^sub>1 where AA: "y \<Colon>\<^sub>m\<^bsub>w\<^sub>1\<^esub> u" using as that(1) A(1) \<open>y \<Colon>\<^sub>m\<^sub>\<diamondop> u\<close> every_individual_exists_somewhere by blast
    obtain w\<^sub>2 where BB: "w\<^sub>2 \<in> \<W>\<^sub>*" "\<Omega> y \<in> w\<^sub>2"  using A(2) every_individual_exists_somewhere moments_are_individuals by blast      
    show ?thesis using BB(1) C[OF AA BB] by simp
  qed
  show "y \<Colon>\<^sub>m\<^sub>\<diamondop> u"  if as:  "\<Omega> y \<Colon>\<^sub>m\<^sub>\<diamondop> u"
  proof -
    obtain A: "y \<in> \<M>\<^sub>*" "\<Omega> y \<in> \<M>\<^sub>*" using as 
      using moment_miof_scope by blast    
    have B: "\<Omega> y \<simeq>\<^sub>* y" using m_strong_preserve_similarity[OF A(1)] by simp
    have C: "y \<Colon>\<^sub>m\<^bsub>w\<^sub>2\<^esub> u" if "\<Omega> y \<Colon>\<^sub>m\<^bsub>w\<^sub>1\<^esub> u" "w\<^sub>2 \<in> \<W>\<^sub>*" "y \<in> w\<^sub>2" for w\<^sub>1 w\<^sub>2 u
      using moment_iof_agrees_with_similarity[OF B,of w\<^sub>1 u w\<^sub>2] that by blast
    obtain w\<^sub>1 where AA: "\<Omega> y \<Colon>\<^sub>m\<^bsub>w\<^sub>1\<^esub> u" using as that(1) A(1) \<open>\<Omega> y \<Colon>\<^sub>m\<^sub>\<diamondop> u\<close> every_individual_exists_somewhere 
      by (meson A(2) moments_are_individuals)
    obtain w\<^sub>2 where BB: "w\<^sub>2 \<in> \<W>\<^sub>*" "y \<in> w\<^sub>2"  using A(2) every_individual_exists_somewhere moments_are_individuals by blast      
    show ?thesis using BB(1) C[OF AA BB] by simp
  qed
qed

lemma m_preserve_s_iof:
  fixes x\<^sub>s U\<^sub>s
  shows "\<Omega> x\<^sub>s \<Colon>\<^sub>s\<^bsub>\<Omega> ` w\<^esub> U\<^sub>s \<longleftrightarrow> x\<^sub>s \<Colon>\<^sub>s\<^bsub>w\<^esub> U\<^sub>s" (is "?Q \<longleftrightarrow> ?P")
proof -
  { assume A: "x\<^sub>s \<in> \<S>\<^sub>*" "w \<in> \<W>\<^sub>*" "U\<^sub>s \<in> \<U>\<^sub>s\<^sub>*"
    have "?P \<longleftrightarrow> ?Q" 
    proof
      assume as: "?P"
      then obtain AA: "x\<^sub>s \<in> \<S>\<^sub>*" "U\<^sub>s \<in> \<U>\<^sub>s\<^sub>*" "w \<in> \<W>\<^sub>*" "x\<^sub>s \<in> w" "\<And>u. u \<in> char_set\<^sub>* U\<^sub>s \<Longrightarrow> \<exists>x.  x \<triangleleft>\<^sub>* x\<^sub>s \<and> x \<Colon>\<^sub>m\<^bsub>w\<^esub> u"
        using substantial_iof_E[OF as] by blast
      then have BB: "\<And>u. char_by\<^sub>*  U\<^sub>s u \<Longrightarrow> \<exists>x. x \<triangleleft>\<^sub>* x\<^sub>s \<and> x \<Colon>\<^sub>m\<^bsub>w\<^esub> u" using AA(5) by blast
      have CC: "char_by\<^sub>* U\<^sub>s u \<Longrightarrow> (\<And>x. \<lbrakk> x \<triangleleft>\<^sub>* x\<^sub>s ; x \<Colon>\<^sub>m\<^bsub>w\<^esub> u \<rbrakk> \<Longrightarrow> Q) \<Longrightarrow> Q" for u Q
        using BB by blast
      obtain DD: "\<Omega> x\<^sub>s \<in> \<S>\<^sub>*" "\<Omega> ` w \<in> \<W>\<^sub>*" "\<Omega> x\<^sub>s \<in> \<Omega> ` w"
        using AA(1,3,4) by simp
      show "?Q"
      proof (intro substantial_iof_I AA(2) DD ; elim char_set_E)
        fix u
        assume as1: "char_by\<^sub>* U\<^sub>s u"
        obtain n where AAA: "n \<triangleleft>\<^sub>* x\<^sub>s" "n \<Colon>\<^sub>m\<^bsub>w\<^esub> u" using CC[OF as1] by blast
        then obtain "\<Omega> n \<triangleleft>\<^sub>* \<Omega> x\<^sub>s" "\<Omega> n \<Colon>\<^sub>m\<^bsub>\<Omega> ` w\<^esub> u" by simp
        then show "\<exists>ma. ma \<triangleleft>\<^sub>* \<Omega> x\<^sub>s \<and> ma \<Colon>\<^sub>m\<^bsub>\<Omega> ` w\<^esub> u" by blast
      qed
    next
      assume as: "?Q"
      obtain AA: "\<Omega> x\<^sub>s \<in> \<S>\<^sub>*" "U\<^sub>s \<in> \<U>\<^sub>s\<^sub>*" "\<Omega> ` w \<in> \<W>\<^sub>*" "\<Omega> x\<^sub>s \<in> \<Omega> ` w" "\<And>u. u \<in> char_set\<^sub>* U\<^sub>s \<Longrightarrow> \<exists>z. z \<triangleleft>\<^sub>* \<Omega> x\<^sub>s \<and> z \<Colon>\<^sub>m\<^bsub>\<Omega> ` w\<^esub> u"
        using substantial_iof_E[OF as] by metis
      then have BB: "\<And>u. char_by\<^sub>*  U\<^sub>s u \<Longrightarrow> \<exists>z. z \<triangleleft>\<^sub>* \<Omega> x\<^sub>s \<and> z \<Colon>\<^sub>m\<^bsub>\<Omega> ` w\<^esub> u" using AA(5) by blast
      have CC: "char_by\<^sub>* U\<^sub>s u \<Longrightarrow> (\<And>x. \<lbrakk> x \<triangleleft>\<^sub>* \<Omega> x\<^sub>s ; x \<Colon>\<^sub>m\<^bsub>\<Omega> ` w\<^esub> u \<rbrakk> \<Longrightarrow> Q) \<Longrightarrow> Q" for u Q
        using BB by blast
      obtain DD: "x\<^sub>s \<in> \<S>\<^sub>*" "w \<in> \<W>\<^sub>*" "x\<^sub>s \<in> w"
        using AA(1,3,4) by (metis A(1) A(2) image_eqI m_inv_substantials src_world_inv_m)
      show "?P"
      proof (intro substantial_iof_I AA(2) DD ; elim char_set_E)
        fix u
        assume as1: "char_by\<^sub>* U\<^sub>s u"
        obtain n where AAA: "n \<triangleleft>\<^sub>* \<Omega> x\<^sub>s" "n \<Colon>\<^sub>m\<^bsub>\<Omega> ` w\<^esub> u" using CC[OF as1] by blast
        have BBB: "n = \<Omega> (\<Theta> n)"  using AAA(1) inheres_in_scope by simp
        obtain CCC: "\<Omega> (\<Theta> n) \<triangleleft>\<^sub>* \<Omega> x\<^sub>s" "\<Omega> (\<Theta> n) \<Colon>\<^sub>m\<^bsub>\<Omega> ` w\<^esub> u" 
          using that BBB AAA by metis
        then obtain DDD: "\<Theta> n \<triangleleft>\<^sub>* x\<^sub>s" "\<Theta> n \<Colon>\<^sub>m\<^bsub>w\<^esub> u"          
          by (metis BBB DD(2) image_eqI m_preserve_inherence src_world_inv_m m_preserve_m_iof)
        then show "\<exists>ma. ma \<triangleleft>\<^sub>* x\<^sub>s \<and> ma \<Colon>\<^sub>m\<^bsub>w\<^esub> u" by blast
      qed
    qed }
  note R1 = this
  obtain R2: "x\<^sub>s \<in> \<S>\<^sub>*" "w \<in> \<W>\<^sub>*" "U\<^sub>s \<in> \<U>\<^sub>s\<^sub>*" if "?P \<or> ?Q"    
    using m_w_W by blast
  show ?thesis using R1 R2 by metis
qed

lemma m_preserve_inv_s_iof[simp]:
  fixes x\<^sub>s U\<^sub>s
  shows "x\<^sub>s \<Colon>\<^sub>s\<^bsub>\<Omega> ` w\<^esub> U\<^sub>s \<longleftrightarrow> \<Theta> x\<^sub>s \<Colon>\<^sub>s\<^bsub>w\<^esub> U\<^sub>s" (is "?P \<longleftrightarrow> ?Q")
proof -
  have R1: ?thesis if as: "x\<^sub>s \<in> \<S>\<^sub>*" "w \<in> \<W>\<^sub>*" "U\<^sub>s \<in> \<U>\<^sub>s\<^sub>*"
  proof -
    have A[simp]: "\<Omega> (\<Theta> x\<^sub>s) = x\<^sub>s" using as 
      by (simp add: substantials_are_individuals)
    have B[simp]: "\<Omega> ` \<Theta> ` w = w" using as 
      using tgt_world_m_inv by blast 
    show ?thesis using m_preserve_s_iof[of "\<Theta> x\<^sub>s" "w" U\<^sub>s,simplified A,symmetric] by simp
  qed
  obtain R2: "x\<^sub>s \<in> \<S>\<^sub>*" "w \<in> \<W>\<^sub>*" "U\<^sub>s \<in> \<U>\<^sub>s\<^sub>*" if "?Q \<or> ?P"    
    using m_w_W by blast
  show ?thesis using R1 R2 by metis
qed



lemma miof_moments_iff: "u \<in> \<U>\<^sub>m\<^sub>* \<or> y \<in> \<M>\<^sub>* \<Longrightarrow> y \<Colon>\<^sub>\<diamondop> u \<longleftrightarrow> y \<Colon>\<^sub>m\<^sub>\<diamondop> u" for u y
  using miof_I miof_E iof_I  
  by (metis every_individual_exists_somewhere iof_M_simp moment_miof_scope moments_are_individuals)

lemma miof_substantials_iff: "u \<in> \<U>\<^sub>s\<^sub>* \<or> y \<in> \<S>\<^sub>* \<Longrightarrow> y \<Colon>\<^sub>\<diamondop> u \<longleftrightarrow> (\<exists>w. y \<Colon>\<^sub>s\<^bsub>w\<^esub> u)" for u y
  using miof_I miof_E iof_I    
  by (metis iof_S_simp)

lemma miof_out_scope: "\<lbrakk> u \<notin> \<U>\<^sub>* \<or> y \<notin> \<I>\<^sub>* \<rbrakk> \<Longrightarrow> \<not> y \<Colon>\<^sub>\<diamondop> u" for u y    
  by (meson iof_scope iof_scope_E miof_E moments_are_individuals substantials_are_individuals)

lemmas miof_sep_simps = miof_moments_iff miof_substantials_iff miof_out_scope

lemma m_preserve_miof[simp]: 
  fixes y u
  shows "\<Omega> y \<Colon>\<^sub>\<diamondop> u \<longleftrightarrow> y \<Colon>\<^sub>\<diamondop> u" (is "?P \<longleftrightarrow> ?Q")
  apply (cases "y \<in> \<I>\<^sub>*")
  subgoal inI 
    apply (cases y rule: individuals_cases ; simp add: miof_sep_simps)
    apply (intro ex_iff_exI[where ?f="(`) \<Theta>" and ?g="(`) \<Omega>"] ; simp?)
    subgoal for w
      apply (simp only: m_preserve_s_iof[of y "\<Theta> ` w" u,symmetric])
      apply (cases "w \<in> \<W>\<^sub>*" ; simp)
      subgoal premises P
        using P(4,5) substantial_iof_E by metis
      done
    done 
  subgoal notInI by (simp add: miof_out_scope)
  done

lemma m_projected_out_moments[simp]: "\<And>x. \<Omega> x \<in> \<Delta> \<longleftrightarrow> x \<in> \<Delta>"   
  by (smt \<Omega>_closed_I delta_closure.closed_iff individuals_exhaust_2 m_undefined_1(2))


lemma m_inv_projected_out_moments[simp]: "\<And>x. \<Theta> x \<in> \<Delta> \<longleftrightarrow> x \<in> \<Delta>"
proof -
  fix x
  show "?thesis x"    
  proof -
    have "x \<in> \<M>\<^sub>* \<or> (\<Theta> x \<in> \<Delta>) = (x \<in> \<Delta>)"
      by blast
    then show ?thesis
      by (metis (full_types) m_projected_out_moments[symmetric,of "\<Theta> x"] m_inv_inv_moments_iff m_surjective_on_moments)
  qed
qed



lemma m'_image1: "X \<subseteq> \<I>\<^sup>\<down> \<Longrightarrow> \<Omega>\<^sup>\<down> ` X = \<Omega> ` X"
  by (simp add: subset_iff ; intro set_eqI ; simp add: image_iff Bex_def
        ; intro ex_iff_exI[where ?f=id and ?g=id] ; simp
        ; elim conjE ; hypsubst_thin?
        ; simp add: proj_morph_def) 

private lemma not_image_E:
  assumes "f y \<notin> f ` Y"
  obtains "y \<notin> Y" using assms imageI by metis

private lemma image_Diff_subset: "\<lbrakk> Y \<subseteq> X ; f ` X \<inter> f ` Y = {} \<rbrakk> \<Longrightarrow> f ` (X - Y) = f ` X - f ` Y" 
  by blast 
  

lemma m'_inj_on[intro!,simp]: "inj_on \<Omega>\<^sup>\<down> (\<I>\<^sup>\<down>)"
  apply (intro inj_onI ; simp only: proj_morph_def if_True)
  apply (rule m_injective[THEN inj_onD]) 
  using individuals_moments_substantials IS'_IS.individuals_subset by blast+

private lemma m'_image3: "\<Omega>\<^sup>\<down> ` (\<S>\<^sub>* \<union> (\<M>\<^sub>* - \<Delta>)) = (\<S>\<^sub>* \<union> (\<M>\<^sub>* - \<Delta>))"
  apply (simp only: project_simps(1)[of U,symmetric] set_eq_iff image_iff Bex_def)
  apply (intro allI iffI ; (elim exE conjE ; hypsubst_thin)?)
  subgoal by (metis Diff_iff IS'.individuals_moments_substantials IS'_IS.same_substantials m_inv_individuals m_inv_scope_individuals m_projected_out_moments m_surjective' proj_morph_def project_simps(1) project_simps(6)) 
  subgoal for a apply (intro exI[of _ "\<Theta> a"] ; simp) 
    using proj_morph_def project_individuals_eq by auto
  done

definition world_lift :: "'i set \<Rightarrow> 'i set" ("_\<up>" [1000] 999)
  where "w\<up> \<equiv> SOME w'. w' \<in> \<W>\<^sub>* \<and> w = w' \<inter> - \<Delta>"

definition world_project :: "'i set \<Rightarrow> 'i set" ("_\<down>" [1000] 999)
  where "w\<down> \<equiv> w - \<Delta>"

lemma world_project_I[intro!]: "w \<in> \<W>\<^sub>* \<Longrightarrow> w\<down> \<in> \<W>\<^sup>\<down>"
  by (simp add: world_project_def ; blast)

lemma world_project_subset_2[intro!]: "w \<in> \<W>\<^sub>* \<Longrightarrow> w\<down> \<subseteq> \<I>\<^sub>*"
  apply (simp add: world_project_def)  
  by (meson Diff_subset dual_order.trans worlds_are_made_of_individuals)

lemma world_project_eq_int: 
  assumes "w \<in> \<W>\<^sub>*"
  shows "w\<down> = w \<inter> \<I>\<^sup>\<down>"
proof -
  have A: "A = B \<inter> C" if "A = B - D" "C \<inter> D = {}" "B \<subseteq> C \<union> D" for A B C D :: "'z set"
    using that by blast
  show ?thesis
    apply (intro A[of _ _ \<Delta>])
    subgoal using world_project_def by simp
    subgoal by (simp only: project_simps(1) ; blast)
    subgoal  using worlds_are_made_of_individuals[OF assms] 
      apply (simp only: project_simps(1)) by blast
    done
qed 
   
  

lemma exist_lift[intro!,simp]: 
  assumes "w \<in> \<W>\<^sup>\<down>"
  shows "\<exists>w'. w' \<in> \<W>\<^sub>* \<and> w = w' \<inter> - \<Delta>"
proof -
  have "\<exists>I. w = I - \<Delta> \<and> I \<in> \<W>\<^sub>*"
    using assms by force
  then show ?thesis
    by blast
qed


lemma world_lift_E[elim!]: 
  assumes "w \<in> \<W>\<^sup>\<down>"
  obtains "w\<up> \<in> \<W>\<^sub>*" "w = w\<up> \<inter> \<I>\<^sup>\<down>" "w = w\<up> - \<Delta>"
  using someI_ex[OF exist_lift[OF assms]] world_lift_def   
  by (metis Diff_eq world_project_def world_project_eq_int)
  

lemma world_lift_D:
  assumes "w \<in> \<W>\<^sup>\<down>"
  shows "w\<up> \<in> \<W>\<^sub>*" "w = w\<up> \<inter> - \<Delta>"
  using world_lift_E[OF assms] by blast+

lemma world_lift_project[simp]: 
  assumes "w \<in> \<W>\<^sup>\<down>" 
  shows "(w\<up>)\<down> = w"
  using assms 
  by (metis world_lift_E world_project_def)
  
lemma delta_morph[simp]: "\<Omega> ` \<Delta> = \<Delta>"  
proof -
  note m_projected_out_moments
  note delta_closure.closed delta_closure.closed[OF delta_closure.sym]
  show ?thesis
    apply (intro equalityI subsetI ; (elim imageE)? ; hypsubst_thin?)
    subgoal using m_projected_out_moments by simp
    subgoal for x
      apply (intro rev_image_eqI[of "\<Theta> x"])
      subgoal using m_inv_projected_out_moments by simp
      subgoal 
        apply (subgoal_tac "x \<in> \<I>\<^sub>*" ; simp?)
        by blast
      done
    done
qed


lemma delta_inv_morph[simp]: "\<Theta> ` \<Delta> = \<Delta>"
proof -
  show ?thesis when A: "\<Omega> ` \<Delta> = \<Omega> ` (\<Theta> ` \<Delta>)" (is "?Q")
    apply (rule m_image_injective_on_subsets_of_I[THEN inj_onD])
    subgoal using A by simp
    subgoal 
    proof -
      have "\<And>i. i \<notin> \<Delta> \<or> \<Theta> i \<in> \<I>\<^sub>*"
        using individuals_exhaust_2 by auto
      then show ?thesis
        by blast
    qed    
    using projected_out_moments_are_moments by auto
  have "\<Omega> ` \<Theta> ` \<Delta> = \<Delta>"
    by (meson m_comp_m_inv_I_image' moments_subset_individuals projected_out_moments_are_moments subset_trans)
  then show ?Q
    using delta_morph by simp
qed


lemma proj_morph_world_proj:
  assumes "w \<in> \<W>\<^sub>*"
  shows "\<Omega>\<^sup>\<down> ` w\<down> = (\<Omega> ` w) \<inter> \<I>\<^sup>\<down>" 
proof -
    
  have "\<Omega>\<^sup>\<down> ` w\<down> = \<Omega>\<^sup>\<down> ` (w \<inter> \<I>\<^sup>\<down>)" using assms world_project_eq_int by simp  
  also have "... = \<Omega> ` (w \<inter> \<I>\<^sup>\<down>)" by (simp add: m'_image1)
  oops

lemma delta_in_individuals[intro!,simp]: "\<Delta> \<subseteq> \<I>\<^sub>*"    
    using projected_out_moments_are_moments by auto

lemma m_inv_image_subset_I_down: "X \<subseteq> \<I>\<^sup>\<down> \<Longrightarrow> \<Theta> ` X \<subseteq> \<I>\<^sup>\<down>"
  by (smt IS'.individuals_moments_substantials IS'_IS.moments_subset IS'_IS.same_substantials delta_inv_morph 
      image_Un image_mono inj_on_image_set_diff project_simps(6) instantiation_structure_axioms 
      m_inv.m_injective_on_moments m_inv.m_surjective_on_moments m_inv.m_surjective_on_substantials 
      projected_out_moments_are_moments)

lemma down_image_of_I_eq_I[simp]: "\<Omega>\<^sup>\<down> ` \<I>\<^sup>\<down> = \<I>\<^sup>\<down>"    
  using IS'.individuals_moments_substantials IS'_IS.same_substantials m'_image3 project_simps(6) by presburger


lemma up_image_down_eq_down_image:
  assumes "w \<in> \<W>\<^sup>\<down>"
  shows "(\<Omega> ` w\<up>)\<down> = \<Omega>\<^sup>\<down> ` w"
proof -
  obtain A: "w\<up> \<in> \<W>\<^sub>*" "w = w\<up> - \<Delta>" "w = w\<up> \<inter> \<I>\<^sup>\<down>"
    using world_lift_E assms by metis
  have A1: "w \<subseteq> \<I>\<^sup>\<down>" using assms by blast
  have B: "\<Omega> ` w\<up> \<in> \<W>\<^sub>*" using A(1) m_w_W by blast
  have B1:"\<Omega> ` w\<up> - \<Omega> ` \<Delta> \<subseteq> \<I>\<^sub>*" using B world_project_def world_project_subset_2 by auto  
  have B2: "\<Omega> ` \<Delta> \<subseteq> \<I>\<^sub>*" by (simp)
  note B3 = inj_on_image_set_diff[
      OF m_inv_injective, of "\<Omega> ` w\<up>" "\<Omega> ` \<Delta>",
      OF B1 B2]  
  have C: "(\<Omega> ` w\<up>)\<down> = (\<Omega> ` w\<up>) - \<Delta>"
    using world_project_def by simp
  then have "\<Theta> ` (\<Omega> ` w\<up>)\<down> = \<Theta> ` (\<Omega> ` w\<up> - \<Delta>)"
    by simp
  then have "\<Theta> ` (\<Omega> ` w\<up>)\<down> = \<Theta> ` (\<Omega> ` w\<up> - \<Omega> ` \<Delta>)"
    by simp  
  then have "\<Theta> ` (\<Omega> ` w\<up>)\<down> = \<Theta> ` \<Omega> ` w\<up> - \<Theta> ` \<Omega> ` \<Delta>"
    using B3 by simp
  then have "\<Theta> ` (\<Omega> ` w\<up>)\<down> = w\<up> - \<Delta>" by (simp add: A(1))
  then have D: "\<Theta> ` (\<Omega> ` w\<up>)\<down> = w"  using A(2) by auto
  have E: "\<Theta> ` (\<Omega> ` w\<up>)\<down> \<subseteq> \<I>\<^sup>\<down>"
    using m_inv_image_subset_I_down[of w] assms D IS'.worlds_are_made_of_individuals by presburger
  then have "\<Omega> ` \<Theta> ` (\<Omega> ` w\<up>)\<down> = (\<Omega> ` w\<up>)\<down>"  using B1 C by auto
  then have F: "(\<Omega> ` w\<up>)\<down> = \<Omega> ` w" using D by simp
  have G: "\<Omega> ` w = \<Omega>\<^sup>\<down> ` w" 
    using A1 by (simp add: m'_image1)
  then show ?thesis
    using F by simp
qed

lemma up_inv_image_down_eq_down_inv_image:
  assumes "w \<in> \<W>\<^sup>\<down>"
  shows "(\<Theta> ` w\<up>)\<down> = \<Theta> ` w"
  using assms  
proof -
  assume "w \<in> \<W>\<^sup>\<down>"
  then have "(w\<up>)\<down> = w"
    by (metis world_lift_project)
  then show ?thesis
    using inj_on_image_set_diff world_project_def by auto
qed

lemma m'_morphism[intro!,simp]: "individual_structure_morphism IS\<^sup>\<down> IS\<^sup>\<down> \<Omega>\<^sup>\<down>"
proof -  
  show ?thesis
    apply (unfold_locales)
    subgoal G1 
      apply (simp add: project_simps(1))      
      using proj_morph_def project_individuals_eq by auto      
    subgoal G2
      apply (auto simp: proj_morph_def)
      subgoal using inheres_in_scope_2 by (metis IS'_IS.same_substantials substantialsE)
      using inheres_in_scope_2 project_individuals_eq by auto      
    subgoal G3  by (metis (no_types, lifting) G1 IS'.exactly_similar_scope IS'.moments_are_individuals IS'.substantials_moments_disj_2 IS'_IS.preserve_exact_similarity m_preserve_exact_similarity proj_morph_def)
    subgoal G4 for x y
      apply (intro iffI ; (elim exE conjE ; hypsubst_thin)? ; (intro exI[of _ "\<Theta> y"])? ; simp
          ; (elim conjE)? ; (intro conjI notI)? )  
      subgoal G4_1 
      proof -
        assume a1: "\<Omega>\<^sup>\<down> x \<hookrightarrow>\<^sub>* y"
        assume "\<Omega>\<^sup>\<down> x \<notin> \<Delta>"
        then have "x \<in> \<I>\<^sup>\<down>"
          using a1 proj_morph_def by auto
        then show ?thesis
          using a1 by (metis (no_types) m_inv.m_substantials m_inv_inv_substantials_iff m_inv_scope_substantials m_preserce_refers_to_1 proj_morph_def refers_to_scope)
      qed
      subgoal G4_2 by (metis  m_projected_out_moments proj_morph_def undefined_simps(5))
      subgoal G4_3 using IS'.substantials_are_individuals proj_morph_def refers_to_scope by force
      subgoal G4_4 by (metis DiffI IS'.substantials_are_individuals IS'_IS.same_substantials individuals_moments_substantials m_preserce_refers_to_1 moments_are_individuals proj_morph_def project_individuals_eq refers_to_scope)
      subgoal G4_5 by (metis G4_4  m_projected_out_moments proj_morph_def undefined_simps(5))
      done
    subgoal G5 by (metis (no_types, hide_lams) IS'.undefined_simps(7) IS'.undefined_simps(8) IS'_IS.m_preserve_ed ed_E m_preserve_ed proj_morph_def)
    subgoal G6
    proof (intro morphism_worlds_axiom_iff[THEN iffD2] conjI ballI)
      fix w
      assume A: "w \<in> \<W>\<^sup>\<down>"
      define w' where "w' \<equiv> (\<Omega> ` (w\<up>)) \<down>"
      have B: "\<Omega>\<^sup>\<down> ` w \<inter> \<I>\<^sup>\<down> = \<Omega>\<^sup>\<down> ` w" using A 
        by (metis IS'.worlds_are_made_of_individuals down_image_of_I_eq_I image_mono inf.absorb1)
      have R1: "w' \<in> \<W>\<^sup>\<down>"
        by (simp only: w'_def ; intro world_project_I
           ; simp only: m_w_W ; intro world_lift_D(1) A)
      have R2: "\<Omega>\<^sup>\<down> ` w = w' \<inter> \<Omega>\<^sup>\<down> ` \<I>\<^sup>\<down>"         
        by (simp add: w'_def 
                up_image_down_eq_down_image[OF A] B)            
      show "\<exists>w'\<in>\<W>\<^sup>\<down>. \<Omega>\<^sup>\<down> ` w = w' \<inter> \<Omega>\<^sup>\<down> ` \<I>\<^sup>\<down>"
        by (intro bexI[of _ w'] R1 R2)
    next
      fix w 
      assume A: "w \<in> \<W>\<^sup>\<down>"
      have A1: "w \<subseteq> \<I>\<^sup>\<down>" using A  by blast
      then obtain B: "\<Omega>\<^sup>\<down> ` \<Theta> ` w = w"
          "w \<inter> \<I>\<^sup>\<down> = w" 
        using IS'_IS.individuals_subset m'_image1 m_inv_image_subset_I_down by auto
      define w' where "w' \<equiv> (\<Theta> ` (w\<up>)) \<down>"
      have R1: "w' \<in> \<W>\<^sup>\<down>"
        apply (simp only: w'_def ; intro world_project_I ; simp add: image_iff)         
        using A by blast        
      have R2: "\<Omega>\<^sup>\<down> ` w' = w \<inter> \<Omega>\<^sup>\<down> ` \<I>\<^sup>\<down>"         
        apply (simp add: w'_def)
        apply (simp add:  up_inv_image_down_eq_down_inv_image[OF A])
        by (simp add: B)      
      show "\<exists>w'\<in>\<W>\<^sup>\<down>. \<Omega>\<^sup>\<down> ` w' = w \<inter> \<Omega>\<^sup>\<down> ` \<I>\<^sup>\<down>" 
        by (intro bexI[of _ w'] R1 R2)
    qed    
    done
qed

interpretation m': individual_structure_morphism "IS\<^sup>\<down>" "IS\<^sup>\<down>" "\<Omega>\<^sup>\<down>"
  by simp

lemma m'_permutation[intro!,simp]: "individual_structure_permutation_morphism IS\<^sup>\<down> \<Omega>\<^sup>\<down>"
  apply (unfold_locales)
  subgoal by blast
  subgoal using down_image_of_I_eq_I by blast  
  using proj_morph_def 
  by (simp add: IS'.moments_are_individuals m_strong_preserve_similarity)

interpretation m': individual_structure_permutation_morphism "IS\<^sup>\<down>" "\<Omega>\<^sup>\<down>"
  by simp

end (* "U \<in> \<U>\<^sub>s\<^sub>*" "\<Omega> \<in> EquiPerms"  *)

lemma "EquiPerms \<subseteq> ProjEquiPerms U"
  apply (rule subsetI)  
  apply (intro IS'.substructure_closed_perms[of _ "(\<sim>)"] ; simp?)
  using project_substructure by simp

end (* "U \<in> \<U>\<^sub>s\<^sub>*" *)

context
  fixes U U'
  assumes U_U': "U \<preceq>\<^sub>s\<^sub>* U'"  
begin

lemma U_U'_Univs[simp,intro!]: "U \<in> \<U>\<^sub>s\<^sub>*" "U' \<in> \<U>\<^sub>s\<^sub>*" using U_U' by blast+

interpretation U: individual_structure "projected_structure U"
   by simp

interpretation U': individual_structure "projected_structure U'"
   by simp

lemma proj_out_U_subs_U': "projected_out_moments U \<subseteq> projected_out_moments U'"
  using U_U'
  by (simp add: project_out_moments_mono)

lemma subsumption_imp_proj_substructure:
  "individual_substructure (projected_structure U') (projected_structure U)"
proof -
  note A = proj_out_U_subs_U'[THEN subsetD]
  show ?thesis
   apply (unfold_locales ; simp? ; (intro subsetI DiffI ; (elim DiffE)? ; simp?)?)
    subgoal G1 using A by blast
    subgoal G2 using A by blast
    subgoal G3 using A by meson
    subgoal G4 using A by blast
    subgoal G5 using A using project_simps(1) by auto
    subgoal G6 using A by blast
    subgoal G7 for w
      apply (elim exE conjE ; hypsubst_thin)
      subgoal for w
        apply (intro exI[of _ w] equalityI conjI ; simp?
              ; (intro conjI)? )
        subgoal G7_1 using project_simps(1) by auto
        subgoal G7_2 by (simp add: Diff_mono proj_out_U_subs_U')        
        using project_simps(1) worlds_are_made_of_individuals by fastforce
      done
    subgoal G8
      apply (elim exE conjE ; hypsubst_thin)
      subgoal for w
        apply (rule exI[of _ "w - projected_out_moments U"] ; intro conjI
              ;(intro exI[of _ w])? ; (intro conjI)? ; simp?)
        apply (intro equalityI Int_subset_iff[THEN iffD2] conjI)
        subgoal G8_1 using proj_out_U_subs_U' by (simp add: Diff_mono)
        subgoal G8_2 using proj_out_U_subs_U' by (simp add: Diff_mono project_simps(1) worlds_are_made_of_individuals)        
        using project_simps(1) by auto
      done 
    done
qed

lemma proj_equi_perms_mono: "ProjEquiPerms U \<subseteq> ProjEquiPerms U'"
proof -

  have A: "individual_structure (projected_structure U')"
     by simp
  have B: " individual_substructure (projected_structure U') (projected_structure U)"
    using subsumption_imp_proj_substructure by simp
  have C: "closure_rel_P (\<sim>) \<S>\<^sub>*" by blast
  show ?thesis
    apply (rule subsetI)
    by (rule 
        individual_structure.substructure_closed_perms[of _ "projected_structure U" "(\<sim>)"] ; 
        (simp add: A B C)?)
qed 

end (*  "U \<preceq>\<^sub>s\<^sub>* U'"   *)

end (* instantiation_structure *)

end (* theory *)

