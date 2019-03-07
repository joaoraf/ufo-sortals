theory ClosedPermutations
  imports IndividualMorphisms IndividualSubStructure
begin

context individual_structure_defs
begin

definition ClosedPerms ("\<Pi>\<^bsub>_\<^esub>" [1] 999) where
  "\<Pi>\<^bsub>\<phi>\<^esub> \<equiv> { p . p \<in> Perms \<and> (\<forall>x \<in> \<I>. \<phi> x (p x)) }"

lemma ClosedPermsI[intro!]: 
  assumes "p \<in> Perms" "\<And>x. x \<in> \<I> \<Longrightarrow> \<phi> x (p x)"
  shows "p \<in> \<Pi>\<^bsub>\<phi>\<^esub>"  
  using assms by (auto simp: ClosedPerms_def)

lemma ClosedPermsE[elim!]: 
  assumes "p \<in> \<Pi>\<^bsub>\<phi>\<^esub>"
  obtains "p \<in> Perms" "\<And>x. x \<in> \<I> \<Longrightarrow> \<phi> x (p x)"  
  using assms by (auto simp: ClosedPerms_def)

lemma ClosedPerms_iff: 
  "p \<in> \<Pi>\<^bsub>\<phi>\<^esub> \<longleftrightarrow> p \<in> Perms \<and> (\<forall>x. x \<in> \<I> \<longrightarrow> \<phi> x (p x))"  
  by blast

end


context individual_structure_defs
begin

abbreviation "closure P \<equiv> closure_rel_P P \<I>" 

end

context individual_structure
begin


(* UNUSED lemma closed_perms_mono:
  assumes "closure P" "closure Q" "\<And>x y. P x y \<longrightarrow> Q x y"
  shows "\<Pi>\<^bsub>P\<^esub> \<subseteq> \<Pi>\<^bsub>Q\<^esub>"  
proof -  
  interpret P: closure_rel_P P \<I> using assms by simp
  interpret Q: closure_rel_P Q \<I> using assms by simp
  show ?thesis
    using assms(3) by auto
qed *)

lemma substructure_closed_perms:
  fixes IS'
  assumes "individual_substructure  IS IS'" and
    "closure_rel_P P \<I>\<^bsub>IS'\<^esub>" "closure_rel_P P \<I>"
    "closure_rel_P P \<S>" 
    "\<Omega> \<in> individual_structure_defs.ClosedPerms IS' P"    
  shows "\<Omega> \<in> \<Pi>\<^bsub>P\<^esub>"
proof -
  interpret IS': individual_structure IS' using assms(1) by (simp add: individual_substructure_def)
  interpret IS_IS': individual_substructure  IS IS' using assms(1) by simp
  interpret P1: closure_rel_P P "\<I>\<^bsub>IS'\<^esub>"  using assms by simp
  interpret P2: closure_rel_P P \<I>  using assms by simp
  interpret PS: closure_rel_P P \<S>  using assms by simp
  have moments_subset: "\<M> \<subseteq> \<M>\<^bsub>IS'\<^esub>" using IS_IS'.moments_subset by blast
  have S_IS'[simp]: "\<S>\<^bsub>IS'\<^esub> = \<S>" by (simp add: IS_IS'.same_substantials)
  have closure_P[intro!,simp]: "closure P" by (simp add: P2.closure_rel_P_axioms)
  have closure_P'[intro!,simp]: "IS'.closure P" by (simp add: P1.closure_rel_P_axioms)
  note set_lemmas = individuals_moments_substantials IS'.individuals_moments_substantials[simplified S_IS']
      substantials_moments_disj IS'.substantials_moments_disj[simplified S_IS']
      S_IS'   
  have M'_eq1: "\<M>\<^bsub>IS'\<^esub> = \<I>\<^bsub>IS'\<^esub> - \<S>" 
    using IS'.individuals_moments_substantials set_lemmas(4) by auto
  have M_eq1: "\<M> = \<I> - \<S>" using individuals_moments_substantials Un_Diff by auto
  interpret PM': closure_rel_P P "\<M>\<^bsub>IS'\<^esub>"             
    by (simp add: M'_eq1 ; intro closure_rel_combs(3) ; (simp add: PS.closure_rel_P_axioms)?)
  interpret PM: closure_rel_P P "\<M>"
    by (simp add: M_eq1 ; intro closure_rel_combs(3) ; (simp add: PS.closure_rel_P_axioms)?)
  have A0: "\<M> = \<M>\<^bsub>IS'\<^esub> \<inter> \<I>" 
    apply (intro equalityI) 
    subgoal G1 by (simp add: moments_subset)
    using IS'.substantials_moments_disj by auto      
  interpret P3: closure_rel_P P "\<I>\<^bsub>IS'\<^esub> - \<I>"  using assms closure_rel_combs(3) by blast 
  obtain A: "\<Omega> \<in> IS'.Perms" "\<And>x. x \<in> \<I>\<^bsub>IS'\<^esub> \<Longrightarrow> P x (\<Omega> x)"
    using assms(5) by blast  
  interpret omega_IS': individual_structure_permutation_morphism IS' \<Omega>
    using A(1) by blast
  have B: "\<I> \<subseteq> \<I>\<^bsub>IS'\<^esub>" 
    using moments_subset by (simp add: IS'.individuals_moments_substantials individuals_moments_substantials ; blast)  
  note omega_substantials[simp] = omega_IS'.m_substantials[simplified]
  have aux1: "A \<or> B \<longleftrightarrow> A \<or> C" if "B \<longleftrightarrow> C" for A B C using that by blast
  have aux2: "B \<and> A \<longleftrightarrow> C \<and> A" if "B \<longleftrightarrow> C" for A B C using that by blast
  have C[simp]: "\<Omega> x \<in> \<I> \<longleftrightarrow> x \<in> \<I>" for x
    apply (simp add: individuals_moments_substantials ; intro aux1 ; simp add: M_eq1 ; intro aux2)    
    using B P2.closed_iff assms(5) by blast
  have C1[simp]: "omega_IS'.\<Theta> x \<in> \<S> \<longleftrightarrow> x \<in> \<S>" for x    
    using omega_IS'.m_inv_simps(4) by auto
  have C2[simp]: "omega_IS'.\<Theta> x \<in> \<M> \<longleftrightarrow> x \<in> \<M>" for x
    by (metis A0 C Int_iff individual_structure_injective_morphism.m_inv_scope_moments omega_IS'.individual_structure_injective_morphism_axioms omega_IS'.m_inv_inv_moments_iff omega_IS'.m_inv_simps(5))
  have C3[simp]: "omega_IS'.\<Theta> x \<in> \<I> \<longleftrightarrow> x \<in> \<I>" for x
    by (simp only: individuals_moments_substantials Un_iff C1 C2)
  have D[simp]: "\<Omega> x \<in> \<M> \<longleftrightarrow> x \<in> \<M>" for x
    by (simp add: M_eq1)
  have E[simp]: "omega_IS'.\<Theta> ` \<I> = \<I>"
    apply (intro set_eqI iffI ; (elim imageE)? ; hypsubst_thin?)
    subgoal by simp
    subgoal for x
      apply (intro rev_image_eqI[of "\<Omega> x"] ; simp)
      using B by blast
    done 
  have F[simp]: "\<Omega> ` \<I> = \<I>"
    apply (intro set_eqI iffI ; (elim imageE)? ; hypsubst_thin?)
    subgoal by simp
    subgoal for x
      apply (intro rev_image_eqI[of "omega_IS'.\<Theta> x"] ; simp?)
      using B by auto
    done
  note omega_simps = C D omega_IS'.m_individuals omega_IS'.m_substantials[simplified S_IS']
                        omega_IS'.m_moments S_IS'
  have R1: "individual_structure_morphism IS IS \<Omega>"
    apply (unfold_locales)
    subgoal G1 for x
      apply (intro disjCI ; simp ; elim conjE disjE impCE)
      using set_lemmas by blast
    subgoal G2 for x y
      apply (cases "x \<in> \<I>\<^bsub>IS'\<^esub>")      
      subgoal 
        apply (cases "x \<in> \<M>")
        subgoal by (simp only: IS_IS'.preserve_inherence[of x y] omega_IS'.m_preserve_inherence[of x y]  IS_IS'.preserve_inherence[of "\<Omega> x" "\<Omega> y",symmetric,simplified omega_simps])
        using inheres_in_scope_2 D by blast
      subgoal
        apply (simp add:  IS'.individuals_moments_substantials ; elim conjE)
        using moments_subset by auto
      done
    subgoal G3 for x y
      apply (cases "x \<in> \<M>\<^bsub>IS'\<^esub>")      
      subgoal 
        apply (cases "x \<in> \<M>")
        subgoal by (meson D IS_IS'.preserve_exact_similarity exactly_similar_scope omega_IS'.m_preserve_exact_similarity)            
        using exactly_similar_scope D by meson
      subgoal
        apply (simp add:  M'_eq1 ; cases "x \<in> \<I>" ; elim impCE)
        subgoal using B subsetD by metis
        subgoal using exactly_similar_scope omega_simps(2)  substantials_moments_disj_2 by metis
        subgoal using exactly_similar_scope omega_simps(2)  moments_subset_individuals subsetD by metis
        using exactly_similar_scope omega_simps(2)  moments_subset_individuals subsetD by metis      
      done
    subgoal G4 for x y
      apply (cases "x \<in> \<M>")
      subgoal by (metis D IS_IS'.m_preserve_ext_dep IS_IS'.m_preserve_refers_to omega_IS'.m_preserve_refers_to omega_substantials refers_to_scope)
      using D refers_to_scope by blast
    subgoal G5 for x y
      apply (cases "x \<in> \<I> \<and> y \<in> \<I>" ; (elim conjE)? ; simp?)
      subgoal
        apply (simp flip: IS_IS'.m_preserve_ed)
        using omega_IS'.m_preserve_ed by blast
      subgoal premises P
        using P(1) P(2)[rule_format] ed_scope omega_simps(1) by metis
      done
    apply (subgoal_tac "\<forall>w \<in> \<W>. \<Omega> ` w \<in> \<W>" "\<forall>w \<in> \<W>. omega_IS'.\<Theta> ` w \<in> \<W>" )
    subgoal G6
      apply (intro Collect_by_func_I[where ?G="(`) omega_IS'.\<Theta>" and ?F="(`) \<Omega>"]
            )
      subgoal G6_1 for w by simp
      subgoal G6_2 for w
        apply (intro set_eqI iffI IntI ; (elim imageE IntE) ; hypsubst_thin)
        subgoal G6_2_1 for _ _ y
          by (metis IS_IS'.individuals_subset IS_IS'.m_preserve_worlds_2 Int_iff omega_IS'.m_comp_m_inv_eq' subset_iff)
        subgoal G6_2_2 for _ _ y 
          apply (intro imageI)          
          using C G6_2_1 individuals_iff by auto
        subgoal G6_2_3 for _ y
          apply (intro imageI ; intro rev_image_eqI[of "\<Omega> y"] ; simp ; intro impI)          
          using IS_IS'.individuals_subset by blast
        done
      subgoal G6_3 for w by simp
      subgoal G6_4 premises P for w
        using P(2)[rule_format,OF P(3)] P(3) worlds_are_made_of_individuals by blast
      done
    subgoal G7 premises P
      apply (intro ballI)
      subgoal premises Q for w
        supply A = P[rule_format]
        using IS_IS'.m_preserve_worlds_2[OF Q] Q apply (elim exE conjE)
        subgoal premises U for w'
          using U apply (hypsubst_thin)
          subgoal premises T 
            apply (simp add: inj_on_image_Int[OF omega_IS'.m_inv_injective
              IS'.worlds_are_made_of_individuals[OF T(2)] B])
            apply (subgoal_tac "omega_IS'.\<Theta> ` \<I> = \<I>" ; simp?) 
              subgoal
                apply (subgoal_tac "omega_IS'.\<Theta> ` w' \<in> \<W>\<^bsub>IS'\<^esub>")
                subgoal by (simp add: IS'.worlds_are_made_of_individuals IS_IS'.m_preserve_worlds_1 T(2))
                apply (intro omega_IS'.m_inv_w_W[THEN iffD2])
                subgoal premises _ 
                  using U(2) IS'.worlds_are_made_of_individuals by metis
                using U(2) by simp        
              done
            done   
          done
        done
  proof 
    fix w
    assume as: "w \<in> \<W>"
    then obtain w' where AA: "w = w' \<inter> \<I>" "w' \<in> \<W>\<^bsub>IS'\<^esub>"        
      using IS_IS'.m_preserve_worlds_2 by blast
    have "\<Omega> ` w' \<in> \<W>\<^bsub>IS'\<^esub>" using AA(2) by simp
    then have BB: "(\<Omega> ` w') \<inter> \<I> \<in> \<W>"  using IS_IS'.m_preserve_worlds_1 by simp
    have DD: "(\<Omega> ` w') \<inter> \<I> = \<Omega> ` (w' \<inter> \<I>)" by auto        
    have EE: "\<Omega> ` (w' \<inter> \<I>) = \<Omega> ` w" using AA by simp 
    then show "\<Omega> ` w \<in> \<W>" using DD EE BB by simp 
  qed
  then interpret omega_IS: individual_structure_morphism IS IS \<Omega> by simp
  have R2: "individual_structure_permutation_morphism IS \<Omega>"
    apply (unfold_locales)
    subgoal by (rule inj_on_subset[OF omega_IS'.m_injective] ; intro B)
    subgoal by simp
    subgoal for x
      supply AA = omega_IS'.m_strong_preserve_similarity[of x]
                  IS_IS'.preserve_exact_similarity[of x "\<Omega> x",THEN iffD1]
      apply (intro AA(2)[OF _ _ AA(1)] ; simp?)
      using moments_subset by blast
    done    
  show ?thesis
  proof (intro ClosedPermsI PermI R2)
    fix x
    assume "x \<in> \<I>"
    then show "P x (\<Omega> x)" 
      using IS_IS'.individuals_subset assms(5) by blast
  qed
qed

end

(*
locale closed_individual_structure_permutation =
  individual_structure_permutation_morphism +
  \<phi>: closure_rel_P \<phi> \<I> for \<phi>  +
assumes
  p_closed_perm[iff]: "\<Omega> \<in> \<Pi>\<^bsub>\<phi>\<^esub>" and
  phi_closure[intro!,simp]: "closure \<phi>"
begin

lemma ClosedPerm_is_closed:  "x \<in> \<I> \<Longrightarrow> \<phi> x (\<Omega> x)" 
    using p_closed_perm by blast

lemma ClosedPerm_inv_is_closed:   
  assumes "x \<in> \<I>"
  shows "\<phi> x (\<Theta> x)"      
  using ClosedPerm_is_closed[of "\<Theta> x",simplified,symmetric] assms by metis
   
end *)

end