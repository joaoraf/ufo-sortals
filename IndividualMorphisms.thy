theory IndividualMorphisms
  imports Individuals4
begin

lemma set_comp_eq_iff_1: "{F x | x . x \<in> A} = {G x | x . x \<in> B} \<longleftrightarrow>
       (\<forall>x \<in> A. \<exists>y \<in> B. F x = G y) \<and>
       (\<forall>x \<in> B. \<exists>y \<in> A. G x = F y)"
  by blast

lemma morphism_worlds_axiom_iff: "{ w \<inter> m ` \<I>\<^bsub>src\<^esub> | w . w \<in> \<W>\<^bsub>tgt\<^esub>} = { m ` w | w . w \<in> \<W>\<^bsub>src\<^esub>} \<longleftrightarrow>
       (\<forall>w \<in> \<W>\<^bsub>src\<^esub>. \<exists>w' \<in> \<W>\<^bsub>tgt\<^esub>. m ` w = w' \<inter> (m ` \<I>\<^bsub>src\<^esub>)) \<and>
       (\<forall>w' \<in> \<W>\<^bsub>tgt\<^esub>. \<exists>w \<in> \<W>\<^bsub>src\<^esub>. m ` w = w' \<inter> (m ` \<I>\<^bsub>src\<^esub>))" 
      (is "?X = ?Y \<longleftrightarrow> ?C \<and> ?D")
proof -
  let ?X = "{w \<inter> m ` \<I>\<^bsub>src\<^esub> |w. w \<in> \<W>\<^bsub>tgt\<^esub>}"
    and ?Y = "{m ` w |w. w \<in> \<W>\<^bsub>src\<^esub>}"
  let "{?F w | w . w \<in> ?A }" = "?X" and
      "{?G w | w . w \<in> ?B }" = "?Y" 
  note A = set_comp_eq_iff_1[of ?F ?A ?G ?B]
  show ?thesis      
    by (simp only: A ; intro iffI ; (elim conjE) ; intro conjI
          ; simp? ; metis)
qed

lemma morphism_worlds_axiomI: 
  assumes "\<And>w. w \<in> \<W>\<^bsub>src\<^esub> \<Longrightarrow> \<exists>w' \<in> \<W>\<^bsub>tgt\<^esub>. m ` w = w' \<inter> (m ` \<I>\<^bsub>src\<^esub>)"
       "\<And>w'. w' \<in> \<W>\<^bsub>tgt\<^esub> \<Longrightarrow> \<exists>w \<in> \<W>\<^bsub>src\<^esub>. m ` w = w' \<inter> (m ` \<I>\<^bsub>src\<^esub>)"
  shows "{ w \<inter> m ` \<I>\<^bsub>src\<^esub> | w . w \<in> \<W>\<^bsub>tgt\<^esub>} = { m ` w | w . w \<in> \<W>\<^bsub>src\<^esub>}" 
  apply (intro morphism_worlds_axiom_iff[THEN iffD2,OF conjI,OF ballI ballI])
  using assms by metis+

locale individual_structure_morphism_defs =
  src: individual_structure_defs src +
  tgt: individual_structure_defs tgt for
    src :: "'i1 individual_structure" and
    tgt :: "'i2 individual_structure" +
  fixes \<Omega> :: "'i1 \<Rightarrow> 'i2" ("m")
begin

definition "tws w \<equiv> SOME w'. w' \<in> \<W>\<^bsub>tgt\<^esub> \<and> m ` w = w' \<inter> m ` \<I>\<^bsub>src\<^esub>"

definition "sws w \<equiv> SOME w'. w' \<in> \<W>\<^bsub>src\<^esub> \<and> m ` w' = w \<inter> m ` \<I>\<^bsub>src\<^esub>"


end

locale individual_structure_morphism =
  individual_structure_morphism_defs src tgt \<Omega> +
  src: individual_structure src +
  tgt: individual_structure tgt for src tgt and \<Omega> ("m") +
  assumes
    m_scope: "x \<in> \<S>\<^bsub>src\<^esub> \<and> m x \<in> \<S>\<^bsub>tgt\<^esub> \<or> x \<in> \<M>\<^bsub>src\<^esub> \<and> m x \<in> \<M>\<^bsub>tgt\<^esub> \<or> x \<notin> \<I>\<^bsub>src\<^esub> \<and> m x \<notin> \<I>\<^bsub>tgt\<^esub>" and
    m_preserve_inherence[simp]: "m x \<triangleleft>\<^bsub>tgt\<^esub> m y \<longleftrightarrow> x \<triangleleft>\<^bsub>src\<^esub> y" and
    m_preserve_exact_similarity[simp]: "m x\<^sub>1 \<simeq>\<^bsub>tgt\<^esub> m x\<^sub>2 \<longleftrightarrow> x\<^sub>1 \<simeq>\<^bsub>src\<^esub> x\<^sub>2" and
    m_preserve_refers_to[simp]: "m x \<hookrightarrow>\<^bsub>tgt\<^esub> y\<^sub>t \<longleftrightarrow> (\<exists>y\<^sub>s. x \<hookrightarrow>\<^bsub>src\<^esub> y\<^sub>s \<and> y\<^sub>t = m y\<^sub>s)" and
    m_preserve_ed: "ed\<^bsub>tgt\<^esub> (m x) (m y) \<Longrightarrow> ed\<^bsub>src\<^esub> x y" and
    m_preserve_worlds[simp]: "{ w \<inter> m ` \<I>\<^bsub>src\<^esub> | w . w \<in> \<W>\<^bsub>tgt\<^esub>} = { m ` w | w . w \<in> \<W>\<^bsub>src\<^esub>}"
begin

lemma m_exhaust:
  assumes "m x = y"
  obtains (substantials) "x \<in> \<S>\<^bsub>src\<^esub>" "m x \<in> \<S>\<^bsub>tgt\<^esub>" | 
          (moments) "x \<in> \<M>\<^bsub>src\<^esub>" "m x \<in> \<M>\<^bsub>tgt\<^esub>" |
          (undefined) "x \<notin> \<I>\<^bsub>src\<^esub>" "m x \<notin> \<I>\<^bsub>tgt\<^esub>"
  using m_scope by metis



lemma m_substantials[iff]: "m x \<in> \<S>\<^bsub>tgt\<^esub> \<longleftrightarrow> x \<in> \<S>\<^bsub>src\<^esub>"
  using m_scope[of x]
  by blast 
  
lemma m_moments[iff]: "m x \<in> \<M>\<^bsub>tgt\<^esub> \<longleftrightarrow> x \<in> \<M>\<^bsub>src\<^esub>"
  using m_scope[of x]  
  by blast

lemma m_individuals[iff]: "m x \<in> \<I>\<^bsub>tgt\<^esub> \<longleftrightarrow> x \<in> \<I>\<^bsub>src\<^esub>"
  using m_scope[of x] src.individuals_moments_substantials tgt.individuals_moments_substantials 
  by blast 

lemmas m_not_substantials = neg_iff_D[OF m_substantials]
  
lemmas m_not_moments = neg_iff_D[OF m_moments]

lemmas m_not_individuals = neg_iff_D[OF m_individuals]

lemma m_undefined[iff]: "m undefined \<notin> \<I>\<^bsub>tgt\<^esub>"  
  using m_scope src.undefined_not_in_individuals 
  by auto

lemma m_undefined_1: "m x = undefined \<Longrightarrow> x \<notin> \<I>\<^bsub>src\<^esub>"
                     "x \<notin> \<I>\<^bsub>src\<^esub> \<Longrightarrow> m x \<notin> \<I>\<^bsub>tgt\<^esub>"  
  subgoal by (rule m_exhaust[of x undefined] ; simp)
  using m_scope src.individuals_moments_substantials by blast

declare m_undefined_1(1)[dest!]

lemma twsE:
  assumes "w \<in> \<W>\<^bsub>src\<^esub>"
  obtains "tws w \<in> \<W>\<^bsub>tgt\<^esub>" "m ` w = tws w \<inter> m ` \<I>\<^bsub>src\<^esub>"
  using someI_bex[of "\<W>\<^bsub>tgt\<^esub>" "\<lambda>w'. m ` w = w' \<inter> m ` \<I>\<^bsub>src\<^esub>",
        simplified tws_def[symmetric]]
      morphism_worlds_axiom_iff[of m src tgt] assms 
  by force

lemma twsD:
  assumes "w \<in> \<W>\<^bsub>src\<^esub>"
  shows "tws w \<in> \<W>\<^bsub>tgt\<^esub>" "m ` w = tws w \<inter> m ` \<I>\<^bsub>src\<^esub>"
  using twsE[OF assms] by metis+

lemma swsE:
  assumes "w \<in> \<W>\<^bsub>tgt\<^esub>"
  obtains "sws w \<in> \<W>\<^bsub>src\<^esub>" "m ` sws w = w \<inter> m ` \<I>\<^bsub>src\<^esub>"
  using someI_bex[of "\<W>\<^bsub>src\<^esub>"  "\<lambda>w'. m ` w' = w \<inter> m ` \<I>\<^bsub>src\<^esub>",
        simplified sws_def[symmetric]]
      morphism_worlds_axiom_iff[of m src tgt] assms 
  by force

lemma swsD:
  assumes "w \<in> \<W>\<^bsub>tgt\<^esub>"
  shows "sws w \<in> \<W>\<^bsub>src\<^esub>" "m ` sws w = w \<inter> m ` \<I>\<^bsub>src\<^esub>"
  using swsE[OF assms] by metis+

lemma m_preserve_worlds_D: 
  "\<And>w. w \<in> \<W>\<^bsub>src\<^esub> \<Longrightarrow> \<exists>w' \<in> \<W>\<^bsub>tgt\<^esub>. m ` w = w' \<inter> (m ` \<I>\<^bsub>src\<^esub>)"
  "\<And>w'. w' \<in> \<W>\<^bsub>tgt\<^esub> \<Longrightarrow> \<exists>w \<in> \<W>\<^bsub>src\<^esub>. m ` w = w' \<inter> (m ` \<I>\<^bsub>src\<^esub>)"
  using m_preserve_worlds[simplified morphism_worlds_axiom_iff]
  by auto

lemma worlds2: "{\<Omega> ` w |w. w \<in> \<W>\<^bsub>src\<^esub>} = (`) \<Omega> ` \<W>\<^bsub>src\<^esub>" 
  using Setcompr_eq_image by metis

end

context individual_structure_morphism_defs
begin

definition \<Theta> ("m'_inv") where m_inv_def:"\<Theta> x \<equiv> if x \<in> \<Omega> ` \<I>\<^bsub>src\<^esub> then  inv_into \<I>\<^bsub>src\<^esub> \<Omega> x else undefined"



end
   
locale individual_structure_injective_morphism =
  individual_structure_morphism  + 
  assumes
    m_injective[intro!,simp]: "inj_on m \<I>\<^bsub>src\<^esub>"
begin

lemma m_injective_on_moments[intro!,simp]: "inj_on m \<M>\<^bsub>src\<^esub>"
  using m_injective moments_subset_individuals
        inj_on_subset 
  by auto

lemma m_injective_on_substantials: "inj_on m \<S>\<^bsub>src\<^esub>"
  using m_injective substantials_subset_individuals
        inj_on_subset 
  by auto

lemma m_inv_individuals: "x \<in> \<I>\<^bsub>src\<^esub> \<Longrightarrow> m_inv (m x) = x"
  using inv_into_f_f m_injective m_inv_def by simp

lemma m_inv_substantials: "x \<in> \<S>\<^bsub>src\<^esub> \<Longrightarrow> m_inv (m x) = x"
  using substantials_subset_individuals m_inv_individuals by auto

lemma m_inv_moments: "x \<in> \<M>\<^bsub>src\<^esub> \<Longrightarrow> m_inv (m x) = x"
  using moments_subset_individuals[of src] m_inv_individuals[of x]  
  by (simp add: src.moments_are_individuals)


lemma m_inv_inv_individuals_iff[simp]: 
  assumes "x \<in> \<I>\<^bsub>tgt\<^esub>"
  shows "m (m_inv x) = x \<longleftrightarrow> x \<in> m ` \<I>\<^bsub>src\<^esub>"
  using assms by (cases "x \<in> m ` \<I>\<^bsub>src\<^esub>" ; simp add: m_inv_def ; (elim imageE)?
      ; (intro notI)? ; (elim notE)? ; simp ; blast)
 
lemmas m_inv_inv_individuals = m_inv_inv_individuals_iff[THEN iffD1] m_inv_inv_individuals_iff[THEN iffD2]

lemma subst_image_subset: "x \<in> m ` \<S>\<^bsub>src\<^esub> \<Longrightarrow> x \<in> m ` \<I>\<^bsub>src\<^esub>" 
  by auto

lemma m_inv_inv_moments_iff[simp]: 
  assumes "x \<in> \<M>\<^bsub>tgt\<^esub>"
  shows "m (m_inv x) = x \<longleftrightarrow> x \<in> m ` \<M>\<^bsub>src\<^esub>"
  using assms apply (cases "x \<in> m ` \<M>\<^bsub>src\<^esub>" ; simp add: m_inv_def ; (elim imageE)?
      ; (intro notI conjI impI)? ; (elim notE imageE)? ; simp? ; hypsubst_thin?
      ; (intro imageI)?)
  subgoal premises P for a b
    using P(1,2,3,4) apply (simp only: P(1)[symmetric])
    apply (thin_tac "m b = m b")
    using P(1) by auto
  by blast+

lemma m_inv_inv_substantials_iff[simp]: 
  assumes "x \<in> \<S>\<^bsub>tgt\<^esub>"
  shows "x \<in> m ` \<S>\<^bsub>src\<^esub> \<longleftrightarrow> m (m_inv x) = x"
  using assms by (auto simp: m_inv_def ; intro imageI ; simp)
          
lemma moment_image_subset: "x \<in> m ` \<M>\<^bsub>src\<^esub> \<Longrightarrow> x \<in> m ` \<I>\<^bsub>src\<^esub>"   
  using src.individuals_moments_substantials by force

lemma individuals_image_iff: "x \<in> m ` \<I>\<^bsub>src\<^esub> \<longleftrightarrow> x \<in> m ` \<S>\<^bsub>src\<^esub> \<or> x \<in> m ` \<M>\<^bsub>src\<^esub>"
  using subst_image_subset moment_image_subset 
  by (metis imageE imageI src.individuals_cases)

lemma m_inv_scope_substantials[simp]: "m_inv x \<in> \<S>\<^bsub>src\<^esub> \<longleftrightarrow> x \<in> m ` \<S>\<^bsub>src\<^esub>"
  apply (simp add: m_inv_def cong: if_cong ; intro conjI impI ; safe ; hypsubst_thin? ; simp? ; intro imageI)  
  by auto
  
 
lemma m_inv_scope_moments[simp]: "m_inv x \<in> \<M>\<^bsub>src\<^esub> \<longleftrightarrow> x \<in> m ` \<M>\<^bsub>src\<^esub>"
  apply (simp add: individuals_image_iff m_inv_def  cong: if_cong ; intro conjI impI ; safe ; hypsubst_thin ; simp?)
  subgoal by (metis m_substantials src.substantials_moments_disj_2 substantialsI)  
  by (simp add: src.moments_are_individuals)

lemma m_inv_scope_individuals[simp]: "m_inv x \<in> \<I>\<^bsub>src\<^esub> \<longleftrightarrow> x \<in> m ` \<I>\<^bsub>src\<^esub>"  
  by (metis inv_into_into m_individuals m_inv_def m_undefined)

lemma sws_unique: 
  assumes "w \<in> \<W>\<^bsub>tgt\<^esub>" 
  shows "\<exists>!w'. w' \<in> \<W>\<^bsub>src\<^esub> \<and> m ` w' = w \<inter> m ` \<I>\<^bsub>src\<^esub>"
  supply aux = morphism_worlds_axiom_iff[of m src tgt,THEN iffD1,
        OF m_preserve_worlds,
        THEN conjunct2,rule_format,OF assms]
proof (intro ex_ex1I , metis aux ;  intro set_eqI ; clarify ; rename_tac w\<^sub>1 w\<^sub>2 x)
  fix w\<^sub>1 w\<^sub>2 x
  assume A1: "w\<^sub>1 \<in> \<W>\<^bsub>src\<^esub>" "m ` w\<^sub>1 = w \<inter> m ` \<I>\<^bsub>src\<^esub>" and
         A2: "w\<^sub>2 \<in> \<W>\<^bsub>src\<^esub>" "m ` w\<^sub>2 = w \<inter> m ` \<I>\<^bsub>src\<^esub>"
  have B[simp]: "m ` w\<^sub>1 = m ` w\<^sub>2" using A1(2) A2(2) by simp
  obtain D: "w \<in> \<W>\<^bsub>src\<^esub> \<Longrightarrow> w \<subseteq> \<I>\<^bsub>src\<^esub>" for w 
    using src.worlds_are_made_of_individuals by auto
  have E: "x \<in> w" if "w \<in> \<W>\<^bsub>src\<^esub>" "x \<in> \<I>\<^bsub>src\<^esub>" "m x \<in> m ` w" for w x
    using inj_on_image_mem_iff
           m_injective D that 
    by metis
  note F = E[where ?x = x and ?w=w\<^sub>1,OF A1(1)]
           E[where ?x = x and ?w=w\<^sub>2,OF A2(1)]
  show "x \<in> w\<^sub>1 \<longleftrightarrow> x \<in> w\<^sub>2"
    apply (intro iffI F)
    using A1 A2 src.worlds_are_made_of_individuals by blast+
qed

lemma sws_equality:
  assumes "w \<in> \<W>\<^bsub>tgt\<^esub>" "w' \<in> \<W>\<^bsub>src\<^esub>" "m ` w' = w \<inter> m ` \<I>\<^bsub>src\<^esub>"
  shows "sws w = w'"
  using some1_equality[OF sws_unique,simplified sws_def[symmetric],
      of w w'] assms by metis

lemma sws_tws_eq_id[simp]: 
  assumes "w \<in> \<W>\<^bsub>src\<^esub>"
  shows "sws (tws w) = w"
  using assms apply (elim twsE)
  by (intro sws_equality assms ; simp)

lemma image_negE: 
  fixes x  :: "'b" and f :: "'a \<Rightarrow> 'b" and A
  assumes "x \<notin> f ` A"
  obtains "\<And>y. y \<in> A \<Longrightarrow> f y \<noteq> x"
  using assms by blast

lemma m_inv_aux_1: "m_inv ` (A \<inter> m ` \<I>\<^bsub>src\<^esub>) = m_inv ` A \<inter> \<I>\<^bsub>src\<^esub>"
  supply individuals_image_iff[simp]
  apply (intro inv_into_aux_2[
    where ?g=m_inv and ?f=m and ?X="\<I>\<^bsub>src\<^esub>" and ?b=undefined,
      of A] src.undefined_not_in_individuals)
  apply (simp add: m_inv_def)
  subgoal for Y
    apply (intro set_eqI)    
    subgoal for x
      apply (simp only: image_iff[of x m_inv])
      apply (cases "x \<in> \<I>\<^bsub>src\<^esub>" ; clarsimp simp: m_inv_def
          ; intro iffI ; (elim exE bexE conjE impCE disjE imageE)?
          ; hypsubst_thin? ; simp?
          ; (elim exE bexE conjE impCE disjE imageE image_negE)?
          ; hypsubst_thin? ; simp?)
      subgoal G1 by blast
      subgoal G1 by blast
      subgoal G1 by blast
      subgoal G1 using moment_image_subset by fastforce
      subgoal G5 by fastforce
      subgoal G6 by fastforce
      subgoal G7 by blast
      subgoal G8 by blast      
      by (metis imageE)
    done
  done

lemma m_inv_aux_2: 
  assumes "A \<subseteq> m ` \<I>\<^bsub>src\<^esub>"
  shows "m_inv ` (A \<inter> m ` \<I>\<^bsub>src\<^esub>) = inv_into \<I>\<^bsub>src\<^esub> m  ` (A \<inter> m ` \<I>\<^bsub>src\<^esub>)"
proof -
  have A: "(\<exists>xa. P xa  \<and> (\<exists>x. Q x xa) \<and> R xa) \<longleftrightarrow> 
        (\<exists>xa x. P xa  \<and> Q x xa \<and> R xa)" for Q :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and P R
    by blast
  have B: "m x \<in> m ` \<S>\<^bsub>src\<^esub> \<longleftrightarrow> x \<in> \<S>\<^bsub>src\<^esub>" for x    
    by (metis imageE imageI m_substantials)
  have C: "m x \<in> m ` \<M>\<^bsub>src\<^esub> \<longleftrightarrow> x \<in> \<M>\<^bsub>src\<^esub>" for x    
    by (metis imageE imageI m_moments)
  have D: "xa \<in> \<I>\<^bsub>src\<^esub> \<Longrightarrow> xa \<notin> \<S>\<^bsub>src\<^esub> \<Longrightarrow> (xa \<in> \<M>\<^bsub>src\<^esub> \<Longrightarrow> P) \<Longrightarrow> P" for xa P 
    using src.individuals_moments_substantials by blast
  show ?thesis
    apply (intro set_eqI)
    subgoal for x
      apply (cases "x \<in> \<I>\<^bsub>src\<^esub>" ; (simp add: image_iff Bex_def)?
          ; intro iffI ; elim exE conjE ; hypsubst_thin ; simp?
          ; (elim conjE disjE)?
          ; (simp add: B C)?
          )
      subgoal G1 using m_inv_def by auto      
      using m_inv_individuals by auto
    done
qed

lemma m_inv_subset_img:
  assumes "A \<subseteq> m ` \<I>\<^bsub>src\<^esub>"
  shows "m_inv ` A = inv_into \<I>\<^bsub>src\<^esub> m ` A" 
  apply (intro set_eqI iffI ; (elim imageE)? ; hypsubst_thin
      ; simp add: image_iff )
  subgoal for x    
    by (intro bexI[of _ x] ; simp only: m_inv_def
            ; intro if_P assms[THEN subsetD] ; simp)
  subgoal for x
    by (intro bexI[of _ x] ; simp only: m_inv_def
            ; intro if_P[symmetric] assms[THEN subsetD] ; simp)
  done

lemma m_image_injective_on_subsets_of_I[intro!,simp]:
  "inj_on ((`) m) (Pow \<I>\<^bsub>src\<^esub>)"
  apply (intro Complete_Lattices.inj_on_image
      inj_on_subset[where ?B="\<Union>(Pow \<I>\<^bsub>src\<^esub>)" and ?A="\<I>\<^bsub>src\<^esub>"]
      m_injective)
   by blast

lemma worlds_in_Pow_I: "\<W>\<^bsub>src\<^esub> \<subseteq> Pow \<I>\<^bsub>src\<^esub>"
  using src.worlds_are_made_of_individuals by blast


lemma m_image_injective_on_worlds[intro!,simp]:
  "inj_on ((`) m) \<W>\<^bsub>src\<^esub>"
  using m_image_injective_on_subsets_of_I
      inj_on_subset src.worlds_are_made_of_individuals
  by blast

lemma m_unique_image:
  assumes "w\<^sub>1 \<in> \<W>\<^bsub>src\<^esub>" "w\<^sub>2 \<in> \<W>\<^bsub>src\<^esub>" "m ` w\<^sub>1 = m ` w\<^sub>2"
  shows "w\<^sub>1 = w\<^sub>2"
  using inj_onD[OF m_image_injective_on_worlds] assms by metis

lemma sws_eq_inv_into: 
  assumes "w \<in> \<W>\<^bsub>tgt\<^esub>"
  shows "sws w =  inv_into \<W>\<^bsub>src\<^esub> (\<lambda>w'. m ` w' \<union> (w - m ` \<I>\<^bsub>src\<^esub>)) w"
proof -    
  have AA: "m ` w' \<union> (w - m ` \<I>\<^bsub>src\<^esub>) = w \<longleftrightarrow> m ` w' = w \<inter> m ` \<I>\<^bsub>src\<^esub>" 
    if as1: "w' \<in> \<W>\<^bsub>src\<^esub>" for w'      
  proof -
    have aux1: "(A \<or> B) \<and> C \<longleftrightarrow> A \<and> C \<or> B \<and> C" for A B C by blast
    have aux2: "m ` A \<inter> m ` B = m ` (A \<inter> B)" if "A \<subseteq> B" for m :: "'r \<Rightarrow> 'w" and A B
      using that by blast
    have BB: "w' \<subseteq> \<I>\<^bsub>src\<^esub>" using as1    by (simp add: src.worlds_are_made_of_individuals)
    have CC: "w' \<inter> \<I>\<^bsub>src\<^esub> = w'" using BB by auto
    have DD: "(A - B) \<inter> B = {}" for A B :: "'z set" by blast
    have EE: "(A \<inter> B) \<union> (A - B) = A" for A B :: "'z set" by blast
    show ?thesis
    proof      
      assume as2: "m ` w' \<union> (w - m ` \<I>\<^bsub>src\<^esub>) = w"
      show "m ` w' = w \<inter> m ` \<I>\<^bsub>src\<^esub>"
        apply (subst as2[symmetric] ; subst Int_Un_distrib2)
        by (subst aux2[OF BB] ; subst CC ; subst DD ; simp)
    next 
      assume as2: "m ` w' = w \<inter> m ` \<I>\<^bsub>src\<^esub>"
      show "m ` w' \<union> (w - m ` \<I>\<^bsub>src\<^esub>) = w"
        by (subst as2 ; subst EE ; simp)
    qed
  qed
  have BB: "(\<lambda>w'. w' \<in> \<W>\<^bsub>src\<^esub> \<and> m ` w' = w \<inter> m ` \<I>\<^bsub>src\<^esub>) = 
        (\<lambda>y. y \<in> \<W>\<^bsub>src\<^esub> \<and> m ` y \<union> (w - m ` \<I>\<^bsub>src\<^esub>) = w)"
    apply (intro ext)
    subgoal for w
      apply (cases "w \<in> \<W>\<^bsub>src\<^esub>" ; simp)
      using AA by metis
    done
  have CC: "(SOME x. P x) = (SOME y. Q y)" if "\<And>x. P x = Q x" for P Q :: "'z \<Rightarrow> bool"    
    by (simp add: that)
  note sws_def[of w] inv_into_def[of "\<W>\<^bsub>src\<^esub>",THEN fun_cong,of _ w,
        of "\<lambda>w'. m ` w' \<union> (w - m ` \<I>\<^bsub>src\<^esub>)", simplified,
          simplified ] 
  have DD: "(A \<Longrightarrow> B \<longleftrightarrow> C) \<Longrightarrow> A \<and> B \<longleftrightarrow> A \<and> C" for A B C
    by blast
  show ?thesis
    apply (simp add: sws_def[of w] inv_into_def[of "\<W>\<^bsub>src\<^esub>",THEN fun_cong,of _ w,
        of "\<lambda>w'. m ` w' \<union> (w - m ` \<I>\<^bsub>src\<^esub>)", simplified,
          simplified ])
    by (intro CC DD ; simp add: AA)
qed    

lemma m_inj_worlds: "w \<in> \<W>\<^bsub>tgt\<^esub> \<Longrightarrow> \<exists>!w'. w' \<in> \<W>\<^bsub>src\<^esub> \<and> w \<inter> m ` \<I>\<^bsub>src\<^esub> = m ` w'"   
  by (metis sws_unique)



lemma m_inv_comp_m_eq'[simp]: 
  fixes y
  shows "\<Theta> (\<Omega> y) = (if y \<in> \<I>\<^bsub>src\<^esub> then y else undefined)"
  apply (cases "y \<in> \<I>\<^bsub>src\<^esub>" ; simp add: m_inv_individuals m_inv_def)         
  by (metis imageE m_individuals)
  
lemma m_inv_comp_m_image': 
  fixes X
  shows "\<Theta> ` \<Omega> ` X = X \<inter> \<I>\<^bsub>src\<^esub> \<union> { undefined | x .  x \<in> X \<and> x \<notin> \<I>\<^bsub>src\<^esub> }"
  apply (intro set_eqI ; simp add: image_iff)    
  by metis

lemma m_inv_comp_m_I_image'[simp]: 
  fixes X assumes "X \<subseteq> \<I>\<^bsub>src\<^esub>"
  shows "\<Theta> ` \<Omega> ` X = X"
  using assms[THEN subsetD] by (intro set_eqI ; simp add: image_iff)      

lemma m_inv_comp_m_I2_image'[simp]: 
  fixes X assumes "X \<in> \<W>\<^bsub>src\<^esub>"
  shows "\<Theta> ` \<Omega> ` X = X"
  using m_inv_comp_m_I_image' src.worlds_are_made_of_individuals assms by metis



lemma m_inv_inj_worlds_1: 
  assumes "w \<in> \<W>\<^bsub>tgt\<^esub>"
  shows "m_inv ` ( w \<inter> m ` \<I>\<^bsub>src\<^esub> ) \<in> \<W>\<^bsub>src\<^esub>"
proof -  
  obtain w' where A: "w' \<in> \<W>\<^bsub>src\<^esub>" "m ` w' = w \<inter> m ` \<I>\<^bsub>src\<^esub>"
    using m_preserve_worlds_D(2)[OF assms] by metis
  have B: "w' \<subseteq> \<I>\<^bsub>src\<^esub>" using A(1) 
    by (simp add: src.worlds_are_made_of_individuals)
  have C: "m_inv ` m ` w' = m_inv ` (w \<inter> m ` \<I>\<^bsub>src\<^esub>)" using A(2) by simp
  then have "w' = m_inv ` (w \<inter> m ` \<I>\<^bsub>src\<^esub>)" using B 
    by auto
  then show ?thesis using A(1) by simp
qed



end

locale individual_structure_surjective_morphism =
  individual_structure_morphism  + 
  assumes
    m_surjective[simp]: "m ` \<I>\<^bsub>src\<^esub> = \<I>\<^bsub>tgt\<^esub>"
begin

lemma m_surjective_on_moments[simp]: "m ` \<M>\<^bsub>src\<^esub> = \<M>\<^bsub>tgt\<^esub>"
  apply (intro set_eqI)
  subgoal for x
    using m_surjective moments_subset_individuals[of src] moments_subset_individuals[of tgt]
      imageE[of x m "\<M>\<^bsub>src\<^esub>"] rev_image_eqI[of _ "\<M>\<^bsub>src\<^esub>" x m]
      src.individuals_moments_substantials 
    by (metis (mono_tags, hide_lams) image_iff m_moments tgt.inheres_in_scope tgt.momentsE)  
  done

lemma m_surjective_on_substantials[simp]: "m ` \<S>\<^bsub>src\<^esub> = \<S>\<^bsub>tgt\<^esub>"
  apply (intro set_eqI)
  subgoal for x
    using m_surjective substantials_subset_individuals[of src] substantials_subset_individuals[of tgt]
      imageE[of x m "\<S>\<^bsub>src\<^esub>"] rev_image_eqI[of _ "\<S>\<^bsub>src\<^esub>" x m]
      src.individuals_moments_substantials       
      by (metis (mono_tags, lifting) f_inv_into_f m_substantials subset_image_iff)  
    done

lemma tgt_worlds[simp]: "w \<in> \<W>\<^bsub>tgt\<^esub> \<longleftrightarrow> w \<in> ((`) m) ` \<W>\<^bsub>src\<^esub>"
proof -
  note m_preserve_worlds
  have AA: "w \<subseteq> m ` \<I>\<^bsub>src\<^esub>" if "w \<in> \<W>\<^bsub>tgt\<^esub>" for w
    using that tgt.worlds_are_made_of_individuals by auto
  have BB: "\<W>\<^bsub>tgt\<^esub> = { w . w \<in> \<W>\<^bsub>tgt\<^esub> }" by auto
  then have CC: "\<W>\<^bsub>tgt\<^esub> = { w \<inter>  m ` \<I>\<^bsub>src\<^esub> | w . w \<in> \<W>\<^bsub>tgt\<^esub> }" 
    apply auto 
    subgoal for x
    proof -
      assume "x \<in> \<W>\<^bsub>tgt\<^esub>"
      then have "x \<in> {I \<inter> m ` \<I>\<^bsub>src\<^esub> |I. I \<in> \<W>\<^bsub>tgt\<^esub>}"
        using individual_structure.worlds_are_made_of_individuals tgt.individual_structure_axioms by fastforce
      then show ?thesis
        by simp
    qed
    subgoal for w  by (metis AA inf_absorb2 inf_sup_aci(1) m_surjective)
    done
  have DD[simp]: "((`) m) ` \<W>\<^bsub>src\<^esub> = {m ` w |w. w \<in> \<W>\<^bsub>src\<^esub>}"
    by auto
  show ?thesis
    using AA BB CC DD m_surjective src.worlds_are_made_of_individuals 
      tgt.worlds_are_made_of_individuals    
    using m_preserve_worlds by auto
qed

lemma m_surj_worlds: "w \<in> \<W>\<^bsub>src\<^esub> \<Longrightarrow> m ` w \<in> \<W>\<^bsub>tgt\<^esub>" 
  by simp

lemma worlds1': "{w \<inter> m ` \<I>\<^bsub>src\<^esub> |w. w \<in> \<W>\<^bsub>tgt\<^esub>} = \<W>\<^bsub>tgt\<^esub>" for w  
  apply (simp ; intro set_eqI ; simp ; intro iffI ; (elim exE conjE imageE)? ; hypsubst_thin? ; simp?)
  subgoal for w    
    by (metis m_surj_worlds m_surjective swsE tgt_worlds)
  subgoal for w        
    using m_preserve_worlds_D(1)
    by (metis m_surjective tgt_worlds)
  done

end


locale individual_structure_bijective_morphism =
  individual_structure_injective_morphism  +
  individual_structure_surjective_morphism 
begin

lemma m_bijective: "bij_betw m \<I>\<^bsub>src\<^esub> \<I>\<^bsub>tgt\<^esub>"
  using m_injective m_surjective bij_betw_def by metis

lemma m_bijective_on_substantials: "bij_betw m \<S>\<^bsub>src\<^esub> \<S>\<^bsub>tgt\<^esub>"
  using m_injective_on_substantials m_surjective_on_substantials bij_betw_def by metis

lemma m_bijective_on_moments: "bij_betw m \<M>\<^bsub>src\<^esub> \<M>\<^bsub>tgt\<^esub>"
  using m_injective_on_moments m_surjective_on_moments bij_betw_def by metis

lemma  m_preserce_refers_to_1[simp]:"m x \<hookrightarrow>\<^bsub>tgt\<^esub> m y \<longleftrightarrow> x \<hookrightarrow>\<^bsub>src\<^esub> y"  
  by (metis m_inv_substantials m_preserve_refers_to m_substantials src.refers_to_scope)

lemma  m_inv_simps[simp]:
  "\<And>x y. m_inv x \<triangleleft>\<^bsub>src\<^esub> m_inv y \<longleftrightarrow> x \<triangleleft>\<^bsub>tgt\<^esub> y" 
  "\<And>x y. m_inv x \<simeq>\<^bsub>src\<^esub> m_inv y \<longleftrightarrow> x \<simeq>\<^bsub>tgt\<^esub> y"
  "\<And>x y. m_inv x \<hookrightarrow>\<^bsub>src\<^esub> m_inv y \<longleftrightarrow> x \<hookrightarrow>\<^bsub>tgt\<^esub> y"
  "\<And>x. m_inv x \<in> \<S>\<^bsub>src\<^esub> \<longleftrightarrow> x \<in> \<S>\<^bsub>tgt\<^esub>"
  "\<And>x. m_inv x \<in> \<M>\<^bsub>src\<^esub> \<longleftrightarrow> x \<in> \<M>\<^bsub>tgt\<^esub>"
  "\<And>x. m_inv x \<in> \<I>\<^bsub>src\<^esub> \<longleftrightarrow> x \<in> \<I>\<^bsub>tgt\<^esub>"
       apply standard
        apply simp_all
  subgoal for x y by (metis individual_structure_injective_morphism.m_inv_scope_substantials individual_structure_injective_morphism_axioms m_inv_inv_individuals_iff m_inv_inv_substantials_iff m_inv_scope_moments m_preserve_inherence m_surjective m_surjective_on_moments m_surjective_on_substantials src.inheres_in_out_scope(1) src.inheres_in_out_scope(2) tgt.moments_are_individuals)
  subgoal for x y by (metis m_inv_inv_individuals(2) m_preserve_inherence m_surjective tgt.inheres_in_scope)
  subgoal for x y by (metis UnI2 m_inv_inv_individuals_iff m_inv_scope_moments m_preserve_exact_similarity m_surjective moment_image_subset src.exactly_similar_scope tgt.exactly_similar_scope tgt.individuals_moments_substantials)
  subgoal for x y
    apply (cases "x \<in> \<I>\<^bsub>tgt\<^esub>" ; simp?)
    subgoal premises P
      using P apply auto
      subgoal by (metis individual_structure_injective_morphism.m_inv_scope_individuals individual_structure_injective_morphism_axioms m_inv_inv_individuals_iff m_preserve_refers_to m_surjective src.ed_scope src.refers_to_imp_ed)
      by (metis individual_structure.refers_to_scope m_inv_inv_moments_iff m_inv_inv_substantials_iff m_preserce_refers_to_1 m_surjective_on_moments m_surjective_on_substantials tgt.individual_structure_axioms)
    subgoal premises P
      using P apply (simp add: m_inv_def ; safe ; simp?)
      using tgt.refers_to_scope by blast
    done
  done

lemma m_inv_image[simp]: "m_inv ` \<I>\<^bsub>tgt\<^esub> = \<I>\<^bsub>src\<^esub>"
  apply (intro set_eqI iffI impI ; (elim imageE)? ; simp?)  
  by (metis m_individuals m_inv_individuals rev_image_eqI)

lemma src_world_Int_indiv[simp]: "w \<in> \<W>\<^bsub>src\<^esub> \<Longrightarrow> w \<inter> \<I>\<^bsub>src\<^esub> = w" 
  by (simp add: inf.absorb1 src.worlds_are_made_of_individuals)

lemma src_world_inv_m[simp]: "w \<in> \<W>\<^bsub>src\<^esub> \<Longrightarrow> w = m_inv ` m ` w"
  by auto

lemma tgt_world_m_inv[simp]: "w \<in> \<W>\<^bsub>tgt\<^esub> \<Longrightarrow> w = m ` m_inv ` w"
  apply auto
  using image_iff m_inv_individuals src.individuals_iff by fastforce  
  

lemma m_inv_individual_structure_morphism[simp,intro!]: "individual_structure_morphism tgt src m_inv"
  apply (unfold_locales)
  subgoal for x
    apply (intro disjCI ; simp ; elim conjE disjE)
    by blast    
  subgoal for x y by simp
  subgoal for x y by simp
  subgoal for x y
    apply (intro iffI ; simp? ; (elim exE conjE ; hypsubst_thin ; simp)?)
    apply (intro exI[of _ "m y"] ; intro conjI)
    subgoal using m_preserve_refers_to m_inv_inv_individuals m_inv_individuals
      by (metis m_inv_simps(3) m_inv_substantials src.refers_to_scope)
    using m_preserve_refers_to m_inv_inv_individuals m_inv_individuals
    by (metis m_inv_substantials src.refers_to_scope)
  subgoal for x y    
    apply (rule ccontr ; elim ed_E ; simp ; elim notE ; intro ed_I ; simp ; intro allI impI ; elim conjE)
    subgoal premises P for w
      supply A = P(1,2) P(3)[rule_format,OF conjI] P(4)[simplified image_iff] P(5)
      using A(4) A(1,2,3,5) apply (elim bexE ; simp ; elim imageE ; hypsubst_thin ; simp)
      subgoal premises Q for w\<^sub>1 z
        apply (intro rev_image_eqI[of "m_inv y" w\<^sub>1 y m, OF Q(5)] Q(1))
        subgoal using Q(2,3) by (simp add: m_inv_individuals)
        using Q(8) by (simp add: m_inv_inv_individuals)
      done
    done
  subgoal
    apply (intro set_eqI iffI CollectI ; (elim CollectE exE conjE ; hypsubst_thin)? ; simp ; (elim imageE ; hypsubst_thin ; rename_tac r t)?)
    subgoal premises P for w
      apply (simp add: image_iff)
      by (intro exI[of _ "m ` w"] ; simp add: P ; intro bexI[of _ w] P ; simp)
    subgoal premises P for r t
      using P by (intro exI[of _ t] ; simp flip: src_world_inv_m)
    done
  done

interpretation m_inv: individual_structure_morphism tgt src m_inv by simp

lemma m_inv_bijective[simp,intro!]: "bij_betw m_inv \<I>\<^bsub>tgt\<^esub> \<I>\<^bsub>src\<^esub>"
  apply (simp add: bij_betw_def ; intro inj_onI ; simp add: m_inv_def)
  using bij_betw_inv_into m_bijective bij_betw_imp_inj_on inj_onD by metis

lemma m_inv_injective[simp,intro!]: "inj_on m_inv \<I>\<^bsub>tgt\<^esub>"
  using bij_betw_imp_inj_on m_inv_bijective by metis

lemma m_inv_individual_structure_injective_morphism[intro!,simp]: "individual_structure_injective_morphism tgt src m_inv"
  by (unfold_locales ; simp)

lemma m_inv_individual_structure_surjective_morphism[intro!,simp]: "individual_structure_surjective_morphism tgt src m_inv"
  by (unfold_locales ; simp)

lemma m_inv_individual_structure_bijective_morphism[intro!,simp]: "individual_structure_bijective_morphism tgt src m_inv"
  by (unfold_locales ; simp)


lemma worlds1': "{w \<inter> m ` \<I>\<^bsub>src\<^esub> |w. w \<in> \<W>\<^bsub>tgt\<^esub>} = \<W>\<^bsub>tgt\<^esub>" for w  
  apply (simp ; intro set_eqI ; simp ; intro iffI ; (elim exE conjE imageE)? ; hypsubst_thin? ; simp?)
  subgoal for w    
    by (metis m_surj_worlds m_surjective swsE tgt_worlds)
  subgoal for w        
    using m_preserve_worlds_D(1) 
    by (metis m_surjective tgt_worlds)
  done

lemma m_preserve_worlds2'[simp]: "(`) m ` \<W>\<^bsub>src\<^esub> = \<W>\<^bsub>tgt\<^esub>"
  using m_preserve_worlds[simplified worlds1' worlds2] by simp

lemma m_comp_m_inv_eq'[simp]: 
  fixes y
  assumes "y \<in> \<I>\<^bsub>tgt\<^esub>"
  shows "\<Omega> (\<Theta> y) =  y"  
  using assms apply (auto simp add: m_inv_def)  
  using m_inv_def m_inv_inv_individuals_iff by auto


(* lemma m_comp_m_inv_image': 
  fixes X
  shows "\<Omega> ` \<Theta> ` X = X \<inter> \<I>\<^bsub>tgt\<^esub> \<union> { undefined | x .  x \<in> X \<and> x \<notin> \<I>\<^bsub>tgt\<^esub> }"
    by (intro set_eqI ; simp add: image_iff ; metis)     
*)
lemma m_comp_m_inv_I_image'[simp]: 
  fixes X assumes "X \<subseteq> \<I>\<^bsub>tgt\<^esub>"
  shows "\<Omega> ` \<Theta> ` X = X"
  using assms[THEN subsetD] by (intro set_eqI ; simp add: image_iff)      

lemma m_comp_m_inv_I2_image'[simp]: 
  fixes X assumes "X \<in> \<W>\<^bsub>tgt\<^esub>"
  shows "\<Omega> ` \<Theta> ` X = X"
  using m_comp_m_inv_I_image' src.worlds_are_made_of_individuals assms
  using tgt_world_m_inv by presburger
  

end

locale individual_structure_permutation_morphism_defs =
   individual_structure_defs IS +
   individual_structure_morphism_defs IS IS \<Omega>  
   for IS (structure) and \<Omega>  
begin

end

locale individual_structure_permutation_morphism =  
  individual_structure_permutation_morphism_defs IS \<Omega> +
  individual_structure IS +
  individual_structure_bijective_morphism IS IS \<Omega> 
  for IS (structure) and \<Omega> +
  assumes
    m_strong_preserve_similarity[intro!]: "x \<in> \<M> \<Longrightarrow> x \<simeq> \<Omega> x"
begin

lemmas m_strong_preserve_similarity_2[intro!] =  m_strong_preserve_similarity[symmetric]

declare tgt_worlds[simp del]

lemmas tgt_worlds_2[simp] = tgt_worlds[symmetric]

lemma m_inv_individual_structure_permutation_morphism[simp,intro!]: "individual_structure_permutation_morphism IS \<Theta>"
proof -
  interpret m_inv: individual_structure_bijective_morphism IS IS \<Theta> by simp 
  show ?thesis
    apply (intro_locales)
  proof (unfold_locales)
    fix x
    assume as: "x \<in> \<M>"
    note inv_simps[simp] =  m_inv_moments[OF as]
    show "x \<simeq> \<Theta> x"
      using m_preserve_exact_similarity[of "x" "\<Theta> x",simplified]
            m_strong_preserve_similarity[OF as]
      using inv_simps(1)      
      by (metis as m_inv.m_inv_moments m_inv.m_inv_simps(2) m_inv.m_not_moments(2) exactly_similar_sym)      
  qed
qed

lemmas worlds1 = worlds1'[simplified]

declare m_preserve_worlds2'[simp del]
lemmas m_preserve_worlds2[simp] = m_preserve_worlds2'[simplified]

declare m_surjective[simp del]

lemmas m_surjective'[simp] = m_surjective[simplified]

lemma m_w_W[simp]: "\<Omega> ` w \<in> \<W> \<longleftrightarrow> w \<in> \<W>" for w
proof -
  have A: "w' \<in> \<W> \<and> w = w' \<inter>  \<I> \<longleftrightarrow> w' \<in> \<W> \<and> w = w'" for w w'
    using worlds_are_made_of_individuals by blast
  have B: "{w \<inter> \<Omega> ` \<I> |w. w \<in> \<W>} = \<W>"  using worlds1 m_surjective[simplified] by simp
  have "w \<in> \<W> \<longleftrightarrow> w \<in> {w \<inter> \<Omega> ` \<I> |w. w \<in> \<W>}"
    by (simp add: worlds1[symmetric,THEN eqset_imp_iff,of w])    
  also have "... \<longleftrightarrow> (\<exists>w'. w' \<in> \<W> \<and> w = w' \<inter>  \<Omega> ` \<I>)"
    by blast
  also have "... \<longleftrightarrow> (\<exists>w'. w' \<in> \<W> \<and> w = w' \<inter>  \<I>)" by auto
  also have "... \<longleftrightarrow> (\<exists>w'. w' \<in> \<W> \<and> w = w')" using A by simp
  show ?thesis
    apply (simp add: m_preserve_worlds[simplified B,THEN eqset_imp_iff,of "\<Omega> ` w",simplified])
    apply (intro iffI ; (elim exE conjE)? ; simp? ; (intro exI[of _ w])? ; simp?)
  proof -
    fix w'
    assume P: "\<Omega> ` w = \<Omega> ` w'" "w' \<in> \<W>"
    note ex_ex = P(1)[THEN eqset_imp_iff,simplified image_def,simplified,simplified Bex_def]
    have w_w': "x \<in> w'" if as: "x \<in> w" for x
    proof - 
      obtain y where AA: "y \<in> w'" "\<Omega> x = \<Omega> y"
        using  ex_ex[THEN iffD1,OF exI[of _ x],of "\<Omega> x",simplified,OF as] by blast
      have BB: "y \<in> \<I>" using AA(1) P(2) individuals_iff by blast
      have BB1: "\<Omega> y \<in> \<I>" using BB by simp
      have BB2: "\<Omega> x \<in> \<I>" using BB1 AA(2) by simp      
      then have CC: "x \<in> \<I>" by simp
      have DD: "x = y"  using m_injective inj_onD AA(2) CC BB by metis
      then show "x \<in> w'" using AA by simp 
    qed

    have w'_w: "x \<in> w" if as: "x \<in> w'" for x
    proof - 
      obtain y where AA: "y \<in> w" "\<Omega> x = \<Omega> y"
        using  ex_ex[THEN iffD2] exI[of _ x] as by blast
      have BB: "y \<in> \<I>" using AA(1) by (metis AA(2) P(2) m_not_individuals(1) m_undefined_1(2) individuals_iff that)
      have BB1: "\<Omega> y \<in> \<I>" using BB by simp
      have BB2: "\<Omega> x \<in> \<I>" using BB1 AA(2) by simp      
      then have CC: "x \<in> \<I>" by simp
      have DD: "x = y"  using m_injective inj_onD AA(2) CC BB by metis
      then show "x \<in> w" using AA by simp 
    qed
    have w_eq_w': "w = w'" using w'_w w_w' by blast      
    then show "w \<in> \<W>" using P(2) by simp
  qed
qed

lemma m_inv_w_W[simp]: "w \<subseteq> \<I> \<Longrightarrow> \<Theta> ` w \<in> \<W> \<longleftrightarrow> w \<in> \<W>" for w
  apply (subst m_w_W[symmetric])
  by (cases "w \<in> \<W>" ; simp?)

end


context individual_structure_defs
begin

definition Perms where "Perms \<equiv> { m . individual_structure_permutation_morphism IS m }"

definition perm_invariant where
  "perm_invariant x \<equiv> \<forall>m \<in> Perms. m x = x"

lemma PermI[intro!]: 
  assumes "individual_structure_permutation_morphism IS m"
  shows "m \<in> Perms"
  using assms by (auto simp: Perms_def)

lemma PermD[dest!]: 
  assumes "m \<in> Perms"
  shows "individual_structure_permutation_morphism IS m"
  using assms by (auto simp: Perms_def)

lemma Perm_iff[simp]: "m \<in> Perms \<longleftrightarrow> individual_structure_permutation_morphism IS m"
  by auto


end

context individual_structure
begin


lemma inv_perm_in_perm[intro!,simp]:
  assumes "m \<in> Perms" 
  shows "individual_structure_morphism_defs.\<Theta> IS m \<in> Perms" (is "?m' \<in> Perms")
  using individual_structure_permutation_morphism.m_inv_individual_structure_permutation_morphism[of IS m]
    assms Perms_def 
  by simp

lemma id_on_perm: "id \<in> Perms"
proof -
  have A[simp]: "id ` X = X" for X :: "'z set" by auto
  show ?thesis    
  apply (auto ; unfold_locales ; (simp only: inj_on_id A)?
        ; simp ; (intro set_eqI iffI conjI disjCI)?
        ; (elim CollectE)? ; simp? ; (elim conjE exE)? ; hypsubst_thin? ; simp?)
    subgoal by blast
    subgoal by (simp add: inf_absorb1 worlds_are_made_of_individuals)
    subgoal using worlds_are_made_of_individuals by auto    
    by (simp add: exactly_similar_refl) 
qed


end

context individual_structure_permutation_morphism
begin

lemma omega_in_perms[intro!,simp]: "\<Omega> \<in> Perms"  
  by (simp add: Perms_def  individual_structure_permutation_morphism_axioms)

end

end