theory IndividualSubStructure
  imports Individuals4
begin

locale individual_substructure =
  src: individual_structure src +
  tgt: individual_structure tgt for
    src tgt :: "'i individual_structure" +
  assumes
    same_substantials: "\<S>\<^bsub>tgt\<^esub> = \<S>\<^bsub>src\<^esub>" and
    moments_subset: "\<M>\<^bsub>src\<^esub> \<subseteq> \<M>\<^bsub>tgt\<^esub>" and
    preserve_inherence[simp]: "x \<in> \<M>\<^bsub>src\<^esub> \<Longrightarrow> x \<triangleleft>\<^bsub>tgt\<^esub> y \<longleftrightarrow> x \<triangleleft>\<^bsub>src\<^esub> y" and
    preserve_exact_similarity[simp]: "\<lbrakk> x\<^sub>1 \<in> \<M>\<^bsub>src\<^esub> ; x\<^sub>2 \<in> \<M>\<^bsub>src\<^esub> \<rbrakk> \<Longrightarrow> x\<^sub>1 \<simeq>\<^bsub>tgt\<^esub> x\<^sub>2 \<longleftrightarrow> x\<^sub>1 \<simeq>\<^bsub>src\<^esub> x\<^sub>2" and
    m_preserve_ext_dep[simp]: "\<lbrakk> x \<in> \<M>\<^bsub>src\<^esub> ; y \<in> \<S>\<^bsub>src\<^esub> \<rbrakk> \<Longrightarrow> x \<hookrightarrow>\<^bsub>tgt\<^esub> y \<longleftrightarrow> x \<hookrightarrow>\<^bsub>src\<^esub> y" and
    m_preserve_ed: "\<lbrakk> x \<in> \<I>\<^bsub>src\<^esub> ; y \<in> \<I>\<^bsub>src\<^esub> \<rbrakk> \<Longrightarrow> ed\<^bsub>tgt\<^esub> x y \<longleftrightarrow> ed\<^bsub>src\<^esub> x y" and
    m_preserve_refers_to: "x \<hookrightarrow>\<^bsub>src\<^esub> y \<Longrightarrow> x \<hookrightarrow>\<^bsub>tgt\<^esub> y" and
    m_preserve_worlds_1: "w \<in> \<W>\<^bsub>tgt\<^esub> \<Longrightarrow> w \<inter> \<I>\<^bsub>src\<^esub> \<in> \<W>\<^bsub>src\<^esub>"  and
    m_preserve_worlds_2: "w \<in> \<W>\<^bsub>src\<^esub> \<Longrightarrow> \<exists>w'. w' \<in> \<W>\<^bsub>tgt\<^esub> \<and> w = w' \<inter> \<I>\<^bsub>src\<^esub>"
begin

lemma m_preserve_inherence_2: 
  "x \<triangleleft>\<^bsub>src\<^esub> y \<Longrightarrow> x \<triangleleft>\<^bsub>tgt\<^esub> y" and
  "\<lbrakk> x \<in> \<I>\<^bsub>src\<^esub> ; x \<triangleleft>\<^bsub>tgt\<^esub> y \<rbrakk> \<Longrightarrow> x \<triangleleft>\<^bsub>src\<^esub> y"
  using preserve_inherence[of x y] src.momentsI src.individuals_moments_substantials
  subgoal by blast  
  by (metis preserve_inherence same_substantials src.individuals_cases substantialsE)

lemma  m_preserve_worlds: "{ w \<inter> \<I>\<^bsub>src\<^esub> | w . w \<in> \<W>\<^bsub>tgt\<^esub>} = \<W>\<^bsub>src\<^esub>"  
  apply (intro set_eqI ; simp add: m_preserve_worlds_1 ; intro iffI ; (elim exE conjE)? ; simp?)
  subgoal for x w using m_preserve_worlds_1 by simp
  subgoal for w using m_preserve_worlds_2 by blast
  done

lemma individuals_subset: "\<I>\<^bsub>src\<^esub> \<subseteq> \<I>\<^bsub>tgt\<^esub>"
  using tgt.individuals_moments_substantials       
        moments_subset same_substantials
  by auto

lemma src_tgt_eqI:
  assumes "\<M>\<^bsub>src\<^esub> = \<M>\<^bsub>tgt\<^esub>"
  shows "src = tgt"
proof -
  have A[simp]: "\<I>\<^bsub>tgt\<^esub> = \<I>\<^bsub>src\<^esub>"
    using tgt.individuals_moments_substantials assms same_substantials 
          src.individuals_moments_substantials by simp    
  have B[simp]: "\<W>\<^bsub>tgt\<^esub> = \<W>\<^bsub>src\<^esub>"
    apply (intro set_eqI iffI ; frule m_preserve_worlds_1 m_preserve_worlds_2 ; (elim exE conjE)? ; hypsubst?)
    subgoal for x using Int_absorb2 tgt.worlds_are_made_of_individuals by fastforce    
    by (metis A inf.absorb2 inf_commute tgt.worlds_are_made_of_individuals)

  show ?thesis
    apply (intro individual_structure_eqI ext ; simp?)
    subgoal using assms preserve_inherence by blast
    subgoal by (metis assms preserve_exact_similarity src.exactly_similar_scope tgt.exactly_similar_scope)    
    by (metis assms m_preserve_ext_dep same_substantials src.refers_to_scope tgt.refers_to_scope)
qed

lemmas individual_substructure_eqI = src_tgt_eqI

lemma worlds_eqI:
  assumes "\<M>\<^bsub>src\<^esub> = \<M>\<^bsub>tgt\<^esub>"
  shows "\<W>\<^bsub>src\<^esub> = \<W>\<^bsub>tgt\<^esub>"
  using individual_substructure_eqI[OF assms] by simp

end

lemma individual_substructure_refl:
  assumes assms[simp,intro!]:"individual_structure IS"
  shows "individual_substructure IS IS"
proof -
  interpret individual_structure IS using assms by simp
  show ?thesis
    apply (unfold_locales ; simp?)
    subgoal by (simp add: inf.absorb1 worlds_are_made_of_individuals)
    subgoal for w
      apply (intro exI[of _ w] ; simp)      
      by (simp add: inf.absorb1 worlds_are_made_of_individuals)
    done
qed

lemma individual_substructure_antisym:
  assumes "individual_substructure IS\<^sub>1 IS\<^sub>2" "individual_substructure IS\<^sub>2 IS\<^sub>1"
  shows "IS\<^sub>1 = IS\<^sub>2"
proof -
  interpret ISS12: individual_substructure IS\<^sub>1 IS\<^sub>2 using assms by simp
  interpret ISS21: individual_substructure IS\<^sub>2 IS\<^sub>1 using assms by simp
  show ?thesis  
    apply (intro ISS21.individual_substructure_eqI[symmetric])    
    using ISS12.moments_subset ISS21.moments_subset by blast
qed  

lemma individual_substructure_trans:
  assumes "individual_substructure IS\<^sub>1 IS\<^sub>2" "individual_substructure IS\<^sub>2 IS\<^sub>3"
  shows "individual_substructure IS\<^sub>1 IS\<^sub>3"
proof -
  interpret ISS12: individual_substructure IS\<^sub>1 IS\<^sub>2 using assms by simp
  interpret ISS23: individual_substructure IS\<^sub>2 IS\<^sub>3 using assms by simp
  show ?thesis
    apply (unfold_locales)
    subgoal G1 using ISS12.same_substantials ISS23.same_substantials by simp
    subgoal G2 using ISS12.moments_subset ISS23.moments_subset by blast
    subgoal G3 for x y using ISS12.moments_subset by auto
    subgoal G4 for x y 
      using ISS12.preserve_exact_similarity[of x y] ISS23.preserve_exact_similarity[of x y]      
            ISS12.moments_subset       
      by (simp add: subset_eq)
    subgoal G5 for x y
      using ISS12.m_preserve_ext_dep[of x y] ISS23.m_preserve_ext_dep[of x y]      
            ISS12.moments_subset      
      by (metis ISS12.same_substantials subsetCE)
    subgoal G6 for x y
      using ISS12.m_preserve_ed[of x y] ISS23.m_preserve_ed[of x y]
            ISS12.individuals_subset
      by blast
    subgoal G7 for x y
      using ISS12.m_preserve_refers_to[of x y] ISS23.m_preserve_refers_to[of x y]
            ISS12.individuals_subset
      by blast
    subgoal G8 for w
      using ISS12.m_preserve_worlds_1[of "w \<inter> \<I>\<^bsub>IS\<^sub>2\<^esub>"] ISS23.m_preserve_worlds_1[of w]
            ISS12.individuals_subset
      by (simp add: inf.absorb_iff2 inf_assoc)
    subgoal G9 for w
      using ISS12.m_preserve_worlds_2[of w,THEN exE] ISS23.m_preserve_worlds_2      
      by (metis ISS12.individuals_subset inf.absorb_iff2 inf_assoc)
    done
qed

end