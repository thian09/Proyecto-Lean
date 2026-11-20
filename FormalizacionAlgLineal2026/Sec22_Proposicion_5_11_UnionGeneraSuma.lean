import FormalizacionAlgLineal2026.Sec21_Teorema_5_9_MenorSubespacio

/-!
====================================================================
22. PROPOSICIÓN 5.11: UNIÓN GENERA SUMA
====================================================================
-/

-- La unión de una familia de conjuntos
def UnionFamilia {V : Type _} {I : Type _} (W : I → (V → Prop)) : V → Prop :=
  fun v => ∃ i : I, W i v

/-- Proposición 5.11 (⊆): ∑ Wᵢ ⊆ ⟨⋃ Wᵢ⟩. -/
theorem prop_5_11_sub {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (_hW : ∀ i, EsSubespacio E (W i))
    (v : V) (hv : SumaFamilia E W v) :
    Gen E (UnionFamilia W) v := by
  rcases hv with ⟨L, hL, rfl⟩
  revert hL
  induction L with
  | nil =>
    intro _
    simp only [List.map_nil, E.sumList_nil]
    exact (prop_5_5_gen_es_subespacio E (UnionFamilia W)).zero_mem
  | cons head tail ih =>
    intro hL
    simp only [List.map_cons, E.sumList_cons]
    apply (prop_5_5_gen_es_subespacio E (UnionFamilia W)).add_mem
    · apply prop_5_7_i E (UnionFamilia W)
      exact ⟨head.indice, hL head List.mem_cons_self⟩
    · apply ih
      intro t ht
      exact hL t (List.mem_cons_of_mem head ht)

/-- Proposición 5.11 (⊇): ⟨⋃ Wᵢ⟩ ⊆ ∑ Wᵢ. -/
theorem prop_5_11_sup {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (hW : ∀ i, EsSubespacio E (W i))
    (v : V) (hv : Gen E (UnionFamilia W) v) :
    SumaFamilia E W v := by
  rcases hv with ⟨L, hL, rfl⟩
  revert hL
  induction L with
  | nil =>
    intro _
    simp only [List.map_nil, E.sumList_nil]
    exact (prop_4_27_suma_familia E W hW).zero_mem
  | cons head tail ih =>
    intro hL
    simp only [List.map_cons, E.sumList_cons]
    apply (prop_4_27_suma_familia E W hW).add_mem
    · have ⟨i₀, hi₀⟩ := hL head List.mem_cons_self
      refine ⟨[⟨i₀, E.smul head.coef head.vector⟩], ?_, ?_⟩
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        exact (hW i₀).smul_mem head.coef hi₀
      · simp only [List.map_cons, List.map_nil, E.sumList_cons, E.sumList_nil]
        exact (E.add_zero (E.smul head.coef head.vector)).symm
    · apply ih
      intro t ht
      exact hL t (List.mem_cons_of_mem head ht)

/-- Proposición 5.11 (Completa): ∑ Wᵢ = ⟨⋃ Wᵢ⟩. -/
theorem prop_5_11 {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (hW : ∀ i, EsSubespacio E (W i))
    (v : V) : SumaFamilia E W v ↔ Gen E (UnionFamilia W) v := by
  constructor
  · exact prop_5_11_sub E W hW v
  · exact prop_5_11_sup E W hW v


