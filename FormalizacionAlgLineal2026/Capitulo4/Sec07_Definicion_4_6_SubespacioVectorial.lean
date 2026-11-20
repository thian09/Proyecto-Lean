import FormalizacionAlgLineal2026.Capitulo4.Sec06_Proposicion_4_5_PropiedadesAritmeticas

/-!
====================================================================
7. DEFINICIÓN 4.6: SUBESPACIO VECTORIAL
====================================================================

"Definición 4.6 (Subespacio vectorial). Sea (V, +_V, ·_V) un ℝ-espacio vectorial.
Decimos que W ⊆ V es un subespacio vectorial de V si:
  I.   0_V ∈ W;
  II.  Si w₁, w₂ ∈ W, entonces w₁ +_V w₂ ∈ W;
  III. Si w ∈ W y λ ∈ ℝ, entonces λ ·_V w ∈ W."
-/

/-- Definición 4.6 (Subespacio vectorial): W ⊆ V contiene a 0_V y es cerrado bajo suma y producto por escalar. -/
structure EsSubespacio {V : Type _} (E : EspacioVectorial V) (W : V → Prop) : Prop where
  zero_mem : W E.zero
  add_mem  : ∀ {w₁ w₂ : V}, W w₁ → W w₂ → W (E.add w₁ w₂)
  smul_mem : ∀ («λ» : ℝ) {w : V}, W w → W (E.smul «λ» w)

/-- Si w ∈ W, entonces -w ∈ W (como consecuencia de III tomando λ = -1). -/
theorem EsSubespacio.neg_mem {V : Type _} (E : EspacioVectorial V) {W : V → Prop}
    (hW : EsSubespacio E W) {w : V} (hw : W w) : W (E.neg w) := by
  have h : E.neg w = E.smul (-1) w := (prop_4_5_ii E w).symm
  rw [h]
  exact hW.smul_mem (-1) hw


