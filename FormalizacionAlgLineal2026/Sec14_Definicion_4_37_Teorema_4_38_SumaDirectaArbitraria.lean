import FormalizacionAlgLineal2026.Sec13_Definicion_4_33_Teorema_4_34_SumaDirectaDos

/-!
====================================================================
14. DEFINICIÓN 4.37 Y TEOREMA 4.38: SUMA DIRECTA ARBITRARIA
====================================================================

"Definición 4.37 (Suma directa). Sea (V, +, ·) un ℝ-espacio vectorial.
Si ℱ = {W_i : i ∈ I} es una familia arbitraria de subespacios de V, decimos que
la suma ∑_{i ∈ I} W_i es directa si, para todo i₀ ∈ I:
  W_{i₀} ∩ (∑_{i ∈ I \ {i₀}} W_i) = {0_V}.

Teorema 4.38 (Unicidad de la descomposición de elementos en suma directa).
Sea (V, +, ·) un ℝ-espacio vectorial. Si ℱ = {W_i ⊆ V : i ∈ I} es una familia arbitraria
de subespacios vectoriales de V, la suma ∑_{i ∈ I} W_i es directa si, y sólo si,
la descomposición de cualquier v ∈ ∑_{i ∈ I} W_i como suma finita de elementos no nulos de los W_i,
  v = ∑_{i ∈ I} w_i  con w_i ∈ W_i y #{i ∈ I : w_i ≠ 0} < ∞,
es única (es decir, si hay dos descomposiciones ∑ w_i = ∑ w_i', entonces w_i = w_i' para todo i ∈ I).

Demostración:
(⟹) Si la suma es directa, W_{i₀} ∩ (∑_{i ≠ i₀} W_i) = {0_V}.
  0_V = v - v = ∑ (w_i - w_i').
  Como W_{i₀} ∋ w_{i₀}' - w_{i₀} = ∑_{i ≠ i₀} (w_i - w_i') ∈ ∑_{i ≠ i₀} W_i,
  para todo i₀ ∈ I, w_{i₀}' - w_{i₀} ∈ W_{i₀} ∩ (∑_{i ≠ i₀} W_i) = {0_V}.
  Por lo tanto, w_i = w_i' para todo i.
(⟸) Sean i₀ ∈ I y w_{i₀} ∈ W_{i₀} ∩ (∑_{i ≠ i₀} W_i). Entonces w_{i₀} tiene dos representaciones:
  w_{i₀} = w_{i₀} + 0_V = 0_V + ∑_{i ≠ i₀} w_i.
  Comparando las componentes en W_{i₀}, w_{i₀} = 0_V. Por lo tanto, la suma es directa."
-/

/-- Suma finita de la subfamilia excluyendo el índice i₀: ∑_{i ∈ I \ {i₀}} W_i. -/
def SumaExcluyendo {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (i₀ : I) : V → Prop :=
  fun v => ∃ (L : List (TerminoFamilia I V)),
    (∀ t ∈ L, t.indice ≠ i₀ ∧ W t.indice t.vector) ∧
    v = E.sumList (L.map TerminoFamilia.vector)

theorem SumaExcluyendo.zero_mem {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (i₀ : I) : SumaExcluyendo E W i₀ E.zero := by
  refine ⟨[], ?_, ?_⟩
  · intro t ht; cases ht
  · exact (E.sumList_nil).symm

theorem SumaExcluyendo.add_mem {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (i₀ : I) {u v : V}
    (hu : SumaExcluyendo E W i₀ u) (hv : SumaExcluyendo E W i₀ v) :
    SumaExcluyendo E W i₀ (E.add u v) := by
  rcases hu with ⟨L₁, hL₁, rfl⟩
  rcases hv with ⟨L₂, hL₂, rfl⟩
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro t ht
    rcases List.mem_append.mp ht with h | h
    · exact hL₁ t h
    · exact hL₂ t h
  · simp only [List.map_append]
    exact (E.sumList_append (L₁.map TerminoFamilia.vector) (L₂.map TerminoFamilia.vector)).symm

theorem SumaExcluyendo.smul_mem {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (hW : ∀ i, EsSubespacio E (W i)) (i₀ : I) («λ» : ℝ) {v : V}
    (hv : SumaExcluyendo E W i₀ v) :
    SumaExcluyendo E W i₀ (E.smul «λ» v) := by
  rcases hv with ⟨L, hL, rfl⟩
  refine ⟨L.map (fun t => ⟨t.indice, E.smul «λ» t.vector⟩), ?_, ?_⟩
  · intro t ht
    rcases List.mem_map.mp ht with ⟨orig, horig, rfl⟩
    have h_orig := hL orig horig
    exact ⟨h_orig.1, (hW orig.indice).smul_mem «λ» h_orig.2⟩
  · have hmap (xs : List (TerminoFamilia I V)) :
        (xs.map (fun t => (⟨t.indice, E.smul «λ» t.vector⟩ : TerminoFamilia I V))).map
          TerminoFamilia.vector =
        (xs.map TerminoFamilia.vector).map (E.smul «λ») := by
      induction xs with
      | nil => rfl
      | cons head tail ih => simp only [List.map_cons, ih]
    rw [hmap L]
    exact E.smul_sumList «λ» (L.map TerminoFamilia.vector)

theorem SumaExcluyendo.neg_mem {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (hW : ∀ i, EsSubespacio E (W i)) (i₀ : I) {v : V}
    (hv : SumaExcluyendo E W i₀ v) :
    SumaExcluyendo E W i₀ (E.neg v) := by
  have h : E.neg v = E.smul (-1) v := (prop_4_5_ii E v).symm
  rw [h]
  exact SumaExcluyendo.smul_mem E W hW i₀ (-1) hv

/-- Definición 4.37 (Suma directa arbitraria): Para todo i₀ ∈ I,
    W_{i₀} ∩ (∑_{i ∈ I \ {i₀}} W_i) = {0_V}. -/
def EsSumaDirectaFamilia {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) : Prop :=
  ∀ (i₀ : I) (v : V),
    W i₀ v → SumaExcluyendo E W i₀ v → v = E.zero

/-- Teorema 4.38 (Unicidad de la descomposición en suma directa para familias arbitrarias):
    La suma de la familia es directa si, y sólo si, toda descomposición de un vector v
    en una componente en W_{i₀} y un resto en ∑_{i ≠ i₀} W_i es única para cada i₀ ∈ I. -/
theorem teorema_4_38_unicidad_descomposicion {V : Type _} {I : Type _}
    (E : EspacioVectorial V) (W : I → (V → Prop)) (hW : ∀ i, EsSubespacio E (W i)) :
    EsSumaDirectaFamilia E W ↔
    (∀ (i₀ : I) (w₁ w₂ : V) (resto₁ resto₂ : V),
      W i₀ w₁ → W i₀ w₂ →
      SumaExcluyendo E W i₀ resto₁ → SumaExcluyendo E W i₀ resto₂ →
      E.add w₁ resto₁ = E.add w₂ resto₂ →
      w₁ = w₂ ∧ resto₁ = resto₂) := by
  constructor
  · intro hdir i₀ w₁ w₂ resto₁ resto₂ hw₁ hw₂ hresto₁ hresto₂ heq
    have h_diff : E.add w₁ (E.neg w₂) = E.add resto₂ (E.neg resto₁) :=
      E.sub_eq_sub w₁ resto₁ w₂ resto₂ heq
    have h_in_W : W i₀ (E.add w₁ (E.neg w₂)) :=
      (hW i₀).add_mem hw₁ ((hW i₀).neg_mem E hw₂)
    have h_in_resto : SumaExcluyendo E W i₀ (E.add w₁ (E.neg w₂)) := by
      rw [h_diff]
      exact SumaExcluyendo.add_mem E W i₀ hresto₂ (SumaExcluyendo.neg_mem E W hW i₀ hresto₁)
    have h_zero : E.add w₁ (E.neg w₂) = E.zero :=
      hdir i₀ (E.add w₁ (E.neg w₂)) h_in_W h_in_resto
    have hw_eq : w₁ = w₂ :=
      E.eq_of_add_neg_eq_zero w₁ w₂ h_zero
    have h_zero₂ : E.add resto₂ (E.neg resto₁) = E.zero := by
      rw [← h_diff, h_zero]
    have hresto₂_eq : resto₂ = resto₁ :=
      E.eq_of_add_neg_eq_zero resto₂ resto₁ h_zero₂
    exact ⟨hw_eq, hresto₂_eq.symm⟩
  · intro h_unic i₀ v hw_i₀ h_resto
    have heq : E.add v E.zero = E.add E.zero v := by
      calc
        E.add v E.zero = v              := E.add_zero v
        _              = E.add E.zero v := (E.zero_add v).symm
    have ⟨hw_eq, _⟩ := h_unic i₀ v E.zero E.zero v hw_i₀ (hW i₀).zero_mem
      (SumaExcluyendo.zero_mem E W i₀) h_resto heq
    exact hw_eq


