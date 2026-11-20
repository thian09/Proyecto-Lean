import FormalizacionAlgLineal2026.Sec20_Corolario_5_8

/-!
====================================================================
21. TEOREMA 5.9: ⟨S⟩ ES EL MENOR SUBESPACIO CONTENIENDO S
====================================================================
-/

/-- Teorema 5.9 (⊆): Si W es un subespacio que contiene S, entonces ⟨S⟩ ⊆ W. -/
theorem teorema_5_9_sub {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (W : V → Prop)
    (hW : EsSubespacio E W)
    (hSW : ∀ v, S v → W v)
    (v : V) (hv : Gen E S v) : W v := by
  rcases hv with ⟨L, hL, rfl⟩
  revert hL
  induction L with
  | nil =>
    intro _
    simp only [List.map_nil, E.sumList_nil]
    exact hW.zero_mem
  | cons head tail ih =>
    intro hL
    simp only [List.map_cons, E.sumList_cons]
    apply hW.add_mem
    · exact hW.smul_mem head.coef (hSW head.vector (hL head List.mem_cons_self))
    · apply ih
      intro t ht
      exact hL t (List.mem_cons_of_mem head ht)

/-- Teorema 5.9 (⊇): ⟨S⟩ es uno de los subespacios que contiene S. -/
theorem teorema_5_9_sup {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (v : V)
    (hv : ∀ W : V → Prop, EsSubespacio E W → (∀ s, S s → W s) → W v) :
    Gen E S v := by
  exact hv (Gen E S) (prop_5_5_gen_es_subespacio E S) (prop_5_7_i E S)

/-- Teorema 5.9 (Completo): ⟨S⟩ = ⋂_{S ⊆ W subespacio} W. -/
theorem teorema_5_9 {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (v : V) :
    Gen E S v ↔ ∀ W : V → Prop, EsSubespacio E W → (∀ s, S s → W s) → W v := by
  constructor
  · intro hv W hW hSW
    exact teorema_5_9_sub E S W hW hSW v hv
  · exact teorema_5_9_sup E S v


