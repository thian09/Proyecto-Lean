import FormalizacionAlgLineal2026.Sec17_Definicion_5_3_SubespacioGenerado

/-!
====================================================================
18. PROPOSICIÓN 5.5: ⟨S⟩ ES UN SUBESPACIO VECTORIAL
====================================================================
-/

/-- Proposición 5.5: ⟨S⟩ es un subespacio vectorial de V. -/
theorem prop_5_5_gen_es_subespacio {V : Type _} (E : EspacioVectorial V) (S : V → Prop) :
    EsSubespacio E (Gen E S) where
  -- I. 0_V ∈ ⟨S⟩ (combinación lineal vacía)
  zero_mem := by
    refine ⟨[], ?_, ?_⟩
    · intro t ht
      cases ht
    · simp only [List.map_nil, E.sumList_nil]
  -- II. Clausura bajo la suma
  add_mem := by
    intro w₁ w₂ ⟨L₁, hL₁, hv₁⟩ ⟨L₂, hL₂, hv₂⟩
    refine ⟨L₁ ++ L₂, ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hL₁ t h
      · exact hL₂ t h
    · rw [hv₁, hv₂]
      simp only [List.map_append]
      exact (E.sumList_append
        (L₁.map (fun t => E.smul t.coef t.vector))
        (L₂.map (fun t => E.smul t.coef t.vector))).symm
  -- III. Clausura bajo producto por escalar
  smul_mem := by
    intro «λ» w ⟨L, hL, hv⟩
    refine ⟨L.map (fun t => ⟨«λ» * t.coef, t.vector⟩), ?_, ?_⟩
    · intro t ht
      rcases List.mem_map.mp ht with ⟨orig, horig, rfl⟩
      exact hL orig horig
    · rw [hv]
      have hmap (xs : List (TerminoCombLin V)) :
          (xs.map (fun t => (⟨«λ» * t.coef, t.vector⟩ : TerminoCombLin V))).map
            (fun t => E.smul t.coef t.vector) =
          (xs.map (fun t => E.smul t.coef t.vector)).map (E.smul «λ») := by
        induction xs with
        | nil => rfl
        | cons head tail ih =>
          simp only [List.map_cons]
          rw [E.ev5_smul_assoc, ih]
      rw [hmap L]
      exact E.smul_sumList «λ» (L.map (fun t => E.smul t.coef t.vector))


