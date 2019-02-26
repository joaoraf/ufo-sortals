theory SortalTheory
  imports Sortals3
begin
find_theorems name: sortal_mono
thm_deps instantiation_structure.sortal_mono
unused_thms Projection3_1 - Sortals3
thy_deps (Sortals3 | Main)
 ML {* val _ = map (writeln)
          (Symtab.keys (Proofterm.thms_of_proof (proof_of (thm "test"))
                                                Symtab.empty)) *}

end