import FormalizacionAlgLineal2026.Sec18_Proposicion_5_5_GenEsSubespacio

/-!
====================================================================
19. PROPOSICIÓN 5.7: PROPIEDADES DEL SUBESPACIO GENERADO
====================================================================
-/

/-- Proposición 5.7, Parte I: S ⊆ ⟨S⟩.
    Cada s ∈ S es una combinación lineal de sí mismo con coeficiente 1. -/
theorem prop_5_7_i {V : Type _} (E : EspacioVectorial V) (S : V → Prop)
    (s : V) (hs : S s) : Gen E S s := by
  refine ⟨[⟨1, s⟩], ?_, ?_⟩
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact hs
  · simp only [List.map_cons, List.map_nil, E.sumList_cons, E.sumList_nil]
    rw [E.ev6_one_smul s]
    exact (E.add_zero s).symm

/-- Proposición 5.7, Parte II: S ⊆ T ⟹ ⟨S⟩ ⊆ ⟨T⟩. -/
theorem prop_5_7_ii {V : Type _} (E : EspacioVectorial V) (S T : V → Prop)
    (hST : ∀ v, S v → T v)
    (v : V) (hv : Gen E S v) : Gen E T v := by
  rcases hv with ⟨L, hL, hv⟩
  exact ⟨L, fun t ht => hST t.vector (hL t ht), hv⟩

/-- Proposición 5.7, Parte III (⟸): Si S es subespacio, entonces ⟨S⟩ ⊆ S. -/
theorem prop_5_7_iii_recip {V : Type _} (E : EspacioVectorial V) (S : V → Prop)
    (hS : EsSubespacio E S)
    (v : V) (hv : Gen E S v) : S v := by
  rcases hv with ⟨L, hL, rfl⟩
  revert hL
  induction L with
  | nil =>
    intro _
    simp only [List.map_nil, E.sumList_nil]
    exact hS.zero_mem
  | cons head tail ih =>
    intro hL
    simp only [List.map_cons, E.sumList_cons]
    apply hS.add_mem
    · exact hS.smul_mem head.coef (hL head List.mem_cons_self)
    · apply ih
      intro t ht
      exact hL t (List.mem_cons_of_mem head ht)

/-- Proposición 5.7, Parte III: ⟨S⟩ = S si, y sólo si, S es un subespacio vectorial de V. -/
theorem prop_5_7_iii {V : Type _} (E : EspacioVectorial V) (S : V → Prop) :
    (∀ v, Gen E S v ↔ S v) ↔ EsSubespacio E S := by
  constructor
  · intro h_eq
    have hS_sub : EsSubespacio E (Gen E S) := prop_5_5_gen_es_subespacio E S
    exact {
      zero_mem := by
        rw [← h_eq]
        exact hS_sub.zero_mem
      add_mem := by
        intro w₁ w₂ hw₁ hw₂
        rw [← h_eq]
        exact hS_sub.add_mem ((h_eq w₁).mpr hw₁) ((h_eq w₂).mpr hw₂)
      smul_mem := by
        intro «λ» w hw
        rw [← h_eq]
        exact hS_sub.smul_mem «λ» ((h_eq w).mpr hw)
    }
  · intro hS v
    constructor
    · exact prop_5_7_iii_recip E S hS v
    · exact prop_5_7_i E S v

/-- Proposición 5.7, Parte IV: ⟨⟨S⟩⟩ = ⟨S⟩. -/
theorem prop_5_7_iv {V : Type _} (E : EspacioVectorial V) (S : V → Prop)
    (v : V) : Gen E (Gen E S) v ↔ Gen E S v := by
  constructor
  · exact prop_5_7_iii_recip E (Gen E S) (prop_5_5_gen_es_subespacio E S) v
  · exact prop_5_7_i E (Gen E S) v


