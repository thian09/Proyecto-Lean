import FormalizacionAlgLineal2026.Capitulo5.Sec26_Proposicion_5_21_SacarVectoresLD

/-!
====================================================================
26. COROLARIO 5.23: INDEPENDENCIA LINEAL AL AÑADIR VECTORES
====================================================================
-/

-- Unión de un conjunto con un elemento
def SetUnion {V : Type _} (S : V → Prop) (v₀ : V) : V → Prop :=
  fun v => S v ∨ v = v₀

/-- Lema auxiliar: eliminar un elemento preserva `List.Pairwise`. -/
theorem pairwise_of_pairwise_split {α : Type _} {R : α → α → Prop}
    (L₁ L₂ : List α) (t : α)
    (h_pw : List.Pairwise R (L₁ ++ t :: L₂)) :
    List.Pairwise R (L₁ ++ L₂) := by
  rw [List.pairwise_append] at h_pw ⊢
  rcases h_pw with ⟨h1, h2, h3⟩
  cases h2 with
  | cons _ h2' =>
    exact ⟨h1, h2', fun x hx y hy => h3 x hx y (List.mem_cons_of_mem t hy)⟩

/-- Corolario 5.23 (Versión LD, ⟹): Si I es LI, I ∪ {v₀} es LD y v₀ ∉ I,
    entonces v₀ ∈ ⟨I⟩. -/
theorem corolario_5_23_LD_ida {V : Type _} (E : EspacioVectorial V)
    (I₀ : V → Prop) (v₀ : V)
    (hLI : EsLI E I₀) (hv₀_notin : ¬ I₀ v₀)
    (hLD : EsLD E (SetUnion I₀ v₀)) :
    Gen E I₀ v₀ := by
  have _ := hv₀_notin
  open Classical in
  rcases hLD with ⟨L, hL_mem, hL_pw, hL_sum, ⟨t_nz, ht_nz_mem, ht_nz_coef⟩⟩
  by_cases h_v0 : ∃ t ∈ L, t.vector = v₀
  · -- Caso 2: v₀ sí aparece en L
    rcases h_v0 with ⟨t₀, ht₀_mem, ht₀_vec⟩
    rcases sumList_map_termino_mem_split E L t₀ ht₀_mem with ⟨L₁, L₂, rfl, h_sum_split⟩
    let L' := L₁ ++ L₂
    have hL'_in : ∀ x ∈ L', x ∈ L₁ ++ t₀ :: L₂ :=
      fun x hx => mem_of_mem_split L₁ L₂ t₀ x hx
    have h_ne := pairwise_vector_ne_of_split L₁ L₂ t₀ hL_pw
    have hL'_ne : ∀ x ∈ L', x.vector ≠ v₀ := by
      intro x hx
      have := h_ne x hx
      rw [ht₀_vec] at this
      exact this
    have hL'_I₀ : ∀ x ∈ L', I₀ x.vector := by
      intro x hx
      rcases hL_mem x (hL'_in x hx) with hx_in | hx_eq
      · exact hx_in
      · exfalso; exact hL'_ne x hx hx_eq
    have h_add_zero : E.add (E.smul t₀.coef v₀)
        (E.sumList (L'.map (fun x => E.smul x.coef x.vector))) = E.zero := by
      calc
        E.add (E.smul t₀.coef v₀) (E.sumList (L'.map (fun x => E.smul x.coef x.vector)))
          = E.add (E.smul t₀.coef t₀.vector) (E.sumList (L'.map (fun x => E.smul x.coef x.vector))) := by rw [← ht₀_vec]
        _ = E.sumList ((L₁ ++ t₀ :: L₂).map (fun x => E.smul x.coef x.vector)) := h_sum_split.symm
        _ = E.zero := hL_sum
    by_cases ht0_coef : t₀.coef = 0
    · -- Subcaso 2a: t₀.coef = 0 (imposible por reducción al absurdo)
      have hL'_pw : List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L' :=
        pairwise_of_pairwise_split L₁ L₂ t₀ hL_pw
      have hL'_sum : E.sumList (L'.map (fun x => E.smul x.coef x.vector)) = E.zero := by
        have h_add := h_add_zero
        rw [ht0_coef, prop_4_5_i, E.zero_add] at h_add
        exact h_add
      have ht_nz_L' : t_nz ∈ L' := by
        rcases List.mem_append.mp ht_nz_mem with ht1 | ht2
        · exact List.mem_append.mpr (Or.inl ht1)
        · rw [List.mem_cons] at ht2
          rcases ht2 with rfl | ht2'
          · exfalso; exact ht_nz_coef ht0_coef
          · exact List.mem_append.mpr (Or.inr ht2')
      have h_all_zero := hLI L' hL'_I₀ hL'_pw hL'_sum
      have ht_zero := h_all_zero t_nz ht_nz_L'
      exact False.elim (ht_nz_coef ht_zero)
    · -- Subcaso 2b: t₀.coef ≠ 0
      have h_desp := despeje_escalar E t₀.coef v₀
        (E.sumList (L'.map (fun x => E.smul x.coef x.vector))) ht0_coef h_add_zero
      dsimp [Gen, EsCombinacionLineal]
      refine ⟨smulTerminos (-t₀.coef⁻¹) L', ?_, ?_⟩
      · intro u hu
        rcases smulTerminos_vector (-t₀.coef⁻¹) L' u hu with ⟨x, hx_in, hu_vec⟩
        rw [hu_vec]
        exact hL'_I₀ x hx_in
      · rw [sumList_smulTerminos]
        exact h_desp
  · -- Caso 1: v₀ no aparece en L (imposible por reducción al absurdo)
    have h_not_v0 : ∀ t ∈ L, t.vector ≠ v₀ := by
      intro t ht h_eq
      exact h_v0 ⟨t, ht, h_eq⟩
    have hL_I₀ : ∀ t ∈ L, I₀ t.vector := by
      intro t ht
      rcases hL_mem t ht with h_in | h_eq
      · exact h_in
      · exfalso; exact h_not_v0 t ht h_eq
    have h_all_zero := hLI L hL_I₀ hL_pw hL_sum
    have ht_zero := h_all_zero t_nz ht_nz_mem
    exact False.elim (ht_nz_coef ht_zero)

/-- Corolario 5.23 (Versión LD, ⟸): Si v₀ ∉ I y v₀ ∈ ⟨I⟩, entonces I ∪ {v₀} es LD. -/
theorem corolario_5_23_LD_vuelta {V : Type _} (E : EspacioVectorial V)
    (I₀ : V → Prop) (v₀ : V)
    (hv₀_notin : ¬ I₀ v₀)
    (hv₀_gen : Gen E I₀ v₀) :
    EsLD E (SetUnion I₀ v₀) := by
  rcases hv₀_gen with ⟨L, hL_mem, hL_sum⟩
  let L_norm := normalizeCombLin L
  have h_norm_mem : ∀ u ∈ L_norm, I₀ u.vector :=
    normalizeCombLin_mem_pred I₀ L hL_mem
  have h_norm_pw : List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L_norm :=
    pairwise_normalizeCombLin L
  have h_norm_sum : E.sumList (L_norm.map (fun x => E.smul x.coef x.vector)) = v₀ := by
    rw [sumList_normalizeCombLin E L, ← hL_sum]
  let L_final : List (TerminoCombLin V) := ⟨-1, v₀⟩ :: L_norm
  refine ⟨L_final, ?_, ?_, ?_, ?_⟩
  · intro t ht
    dsimp [L_final] at ht
    rw [List.mem_cons] at ht
    rcases ht with rfl | ht_in
    · right; rfl
    · left; exact h_norm_mem t ht_in
  · dsimp [L_final]
    rw [List.pairwise_cons]
    refine ⟨?_, h_norm_pw⟩
    intro a' ha'
    dsimp
    have ha'_in := h_norm_mem a' ha'
    intro h_eq_vec
    apply hv₀_notin
    have h_eq : a'.vector = v₀ := h_eq_vec.symm
    rw [← h_eq]
    exact ha'_in
  · dsimp [L_final]
    simp only [List.map_cons, E.sumList_cons]
    rw [h_norm_sum, prop_4_5_ii, E.neg_add]
  · refine ⟨⟨-1, v₀⟩, by dsimp [L_final]; exact List.mem_cons_self, neg_one_ne_zero⟩

/-- Corolario 5.23 (Versión LI): I ∪ {v₀} es LI si, y sólo si, v₀ ∉ ⟨I⟩. -/
theorem corolario_5_23_LI {V : Type _} (E : EspacioVectorial V)
    (I₀ : V → Prop) (v₀ : V)
    (hLI : EsLI E I₀) (hv₀_notin : ¬ I₀ v₀) :
    EsLI E (SetUnion I₀ v₀) ↔ ¬ Gen E I₀ v₀ := by
  rw [li_iff_not_ld]
  constructor
  · intro h_not_ld h_gen
    exact h_not_ld (corolario_5_23_LD_vuelta E I₀ v₀ hv₀_notin h_gen)
  · intro h_not_gen h_ld
    exact h_not_gen (corolario_5_23_LD_ida E I₀ v₀ hLI hv₀_notin h_ld)


