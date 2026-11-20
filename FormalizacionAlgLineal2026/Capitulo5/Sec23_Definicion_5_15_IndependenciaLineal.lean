import FormalizacionAlgLineal2026.Capitulo5.Sec22_Proposicion_5_11_UnionGeneraSuma

/-!
====================================================================
23. DEFINICIÓN 5.15: (IN)DEPENDENCIA LINEAL
====================================================================
-/

/-- Definición 5.15 (Linealmente independiente, LI): S es LI si toda combinación lineal
    nula de elementos distintos de S es trivial (todos los coeficientes son 0). -/
def EsLI {V : Type _} (E : EspacioVectorial V) (S : V → Prop) : Prop :=
  ∀ (L : List (TerminoCombLin V)),
    (∀ t ∈ L, S t.vector) →
    (List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L) →
    E.sumList (L.map (fun t => E.smul t.coef t.vector)) = E.zero →
    ∀ t ∈ L, t.coef = 0

/-- Definición 5.15 (Linealmente dependiente, LD): S es LD si existe una combinación lineal
    nula no trivial de elementos distintos de S. -/
def EsLD {V : Type _} (E : EspacioVectorial V) (S : V → Prop) : Prop :=
  ∃ (L : List (TerminoCombLin V)),
    (∀ t ∈ L, S t.vector) ∧
    (List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L) ∧
    E.sumList (L.map (fun t => E.smul t.coef t.vector)) = E.zero ∧
    (∃ t ∈ L, t.coef ≠ 0)

/-- LI y LD son la negación una de la otra. -/
theorem li_iff_not_ld {V : Type _} (E : EspacioVectorial V) (S : V → Prop) :
    EsLI E S ↔ ¬ EsLD E S := by
  constructor
  · intro hLI ⟨L, hL_in, hL_dist, hL_sum, ⟨t, ht_mem, ht_ne⟩⟩
    exact ht_ne (hLI L hL_in hL_dist hL_sum t ht_mem)
  · intro hNLD L hL_in hL_dist hL_sum t ht_mem
    open Classical in
    by_cases h_zero : t.coef = 0
    · exact h_zero
    · exfalso
      exact hNLD ⟨L, hL_in, hL_dist, hL_sum, ⟨t, ht_mem, h_zero⟩⟩


