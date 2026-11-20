import FormalizacionAlgLineal2026.Capitulo4.Sec12_Proposicion_4_27_SumaEsSubespacio

/-!
====================================================================
13. DEFINICIÓN 4.33 Y TEOREMA 4.34: SUMA DIRECTA PARA DOS SUBESPACIOS
====================================================================

"Definición 4.33 (Suma directa, para dos subespacios). Sea (V, +, ·) un ℝ-espacio vectorial.
Si W₁ y W₂ son dos subespacios de V, decimos que la suma W₁ + W₂ es directa si W₁ ∩ W₂ = {0_V}.
En este caso, denotamos W₁ + W₂ por W₁ ⊕ W₂.

Teorema 4.34 (Unicidad de la descomposición de elementos en suma directa, para dos subespacios).
Sea (V, +, ·) un ℝ-espacio vectorial. Si W₁ y W₂ son subespacios vectoriales de V, la suma W₁ + W₂
es directa si, y sólo si, la descomposición de cualquier v ∈ W₁ + W₂ como
  v = w₁ + w₂  con w₁ ∈ W₁ y w₂ ∈ W₂
es única (es decir, w₁ + w₂ = w₁' + w₂' ⟹ w₁ = w₁' y w₂ = w₂').

Demostración:
(⟹) Si W₁ ⊕ W₂ es directa, W₁ ∩ W₂ = {0_V}.
  0_V = v - v = w₁ + w₂ - (w₁' + w₂') ⟺ W₁ ∋ w₁ - w₁' = w₂' - w₂ ∈ W₂.
  Luego w₁ - w₁' = w₂' - w₂ ∈ W₁ ∩ W₂ = {0_V} ⟹ w₁ = w₁' y w₂ = w₂'.
(⟸) Sea v ∈ W₁ ∩ W₂. Notar que v = v + 0_V = 0_V + v son dos descomposiciones de v en W₁ + W₂,
  lo que por hipótesis de unicidad implica, comparando los sumandos de W₁, v = 0_V."
-/

/-- Definición 4.33: La suma binaria W₁ + W₂ es directa si W₁ ∩ W₂ = {0_V}. -/
def EsSumaDirectaDos {V : Type _} (E : EspacioVectorial V) (W₁ W₂ : V → Prop) : Prop :=
  ∀ v : V, InterseccionDos W₁ W₂ v ↔ v = E.zero

theorem EspacioVectorial.sub_eq_sub {V : Type _} (E : EspacioVectorial V)
    (w₁ w₂ w₁' w₂' : V) (h : E.add w₁ w₂ = E.add w₁' w₂') :
    E.add w₁ (E.neg w₁') = E.add w₂' (E.neg w₂) := by
  have h_side1 : E.add (E.add w₁ w₂) (E.add (E.neg w₁') (E.neg w₂)) = E.add w₁ (E.neg w₁') := by
    calc
      E.add (E.add w₁ w₂) (E.add (E.neg w₁') (E.neg w₂))
        = E.add (E.add w₁ (E.neg w₁')) (E.add w₂ (E.neg w₂)) := E.add_assoc_4 w₁ w₂ (E.neg w₁') (E.neg w₂)
      _ = E.add (E.add w₁ (E.neg w₁')) E.zero               := by rw [E.add_neg]
      _ = E.add w₁ (E.neg w₁')                             := E.add_zero _
  have h_side2 : E.add (E.add w₁' w₂') (E.add (E.neg w₁') (E.neg w₂)) = E.add w₂' (E.neg w₂) := by
    calc
      E.add (E.add w₁' w₂') (E.add (E.neg w₁') (E.neg w₂))
        = E.add (E.add w₁' (E.neg w₁')) (E.add w₂' (E.neg w₂)) := E.add_assoc_4 w₁' w₂' (E.neg w₁') (E.neg w₂)
      _ = E.add E.zero (E.add w₂' (E.neg w₂))               := by rw [E.add_neg]
      _ = E.add w₂' (E.neg w₂)                             := E.zero_add _
  calc
    E.add w₁ (E.neg w₁')
      = E.add (E.add w₁ w₂) (E.add (E.neg w₁') (E.neg w₂))   := h_side1.symm
    _ = E.add (E.add w₁' w₂') (E.add (E.neg w₁') (E.neg w₂)) := by rw [h]
    _ = E.add w₂' (E.neg w₂)                                 := h_side2

theorem EspacioVectorial.eq_of_add_neg_eq_zero {V : Type _} (E : EspacioVectorial V)
    (a b : V) (h : E.add a (E.neg b) = E.zero) : a = b := by
  calc
    a = E.add a E.zero               := (E.add_zero a).symm
    _ = E.add a (E.add (E.neg b) b)  := by rw [E.neg_add]
    _ = E.add (E.add a (E.neg b)) b  := (E.ev1_add_assoc a (E.neg b) b).symm
    _ = E.add E.zero b               := by rw [h]
    _ = b                            := E.zero_add b

/-- Teorema 4.34: Caracterización de la suma directa binaria por la unicidad de descomposición. -/
theorem teorema_4_34_unicidad_suma_directa_dos {V : Type _} (E : EspacioVectorial V)
    (W₁ W₂ : V → Prop) (hW₁ : EsSubespacio E W₁) (hW₂ : EsSubespacio E W₂) :
    EsSumaDirectaDos E W₁ W₂ ↔
    (∀ (w₁ w₁' w₂ w₂' : V), W₁ w₁ → W₁ w₁' → W₂ w₂ → W₂ w₂' →
      E.add w₁ w₂ = E.add w₁' w₂' → w₁ = w₁' ∧ w₂ = w₂') := by
  constructor
  · intro hdir w₁ w₁' w₂ w₂' hw₁ hw₁' hw₂ hw₂' heq
    have h_diff_eq : E.add w₁ (E.neg w₁') = E.add w₂' (E.neg w₂) :=
      E.sub_eq_sub w₁ w₂ w₁' w₂' heq
    have h_in_W₁ : W₁ (E.add w₁ (E.neg w₁')) :=
      hW₁.add_mem hw₁ (hW₁.neg_mem E hw₁')
    have h_in_W₂ : W₂ (E.add w₁ (E.neg w₁')) := by
      rw [h_diff_eq]
      exact hW₂.add_mem hw₂' (hW₂.neg_mem E hw₂)
    have h_in_inter : InterseccionDos W₁ W₂ (E.add w₁ (E.neg w₁')) :=
      ⟨h_in_W₁, h_in_W₂⟩
    have h_zero : E.add w₁ (E.neg w₁') = E.zero :=
      (hdir (E.add w₁ (E.neg w₁'))).mp h_in_inter
    have hw₁_eq : w₁ = w₁' :=
      E.eq_of_add_neg_eq_zero w₁ w₁' h_zero
    have h_zero₂ : E.add w₂' (E.neg w₂) = E.zero := by
      rw [← h_diff_eq, h_zero]
    have hw₂'_eq : w₂' = w₂ :=
      E.eq_of_add_neg_eq_zero w₂' w₂ h_zero₂
    exact ⟨hw₁_eq, hw₂'_eq.symm⟩
  · intro h_unic v
    constructor
    · intro ⟨hv₁, hv₂⟩
      have heq : E.add v E.zero = E.add E.zero v := by
        calc
          E.add v E.zero = v              := E.add_zero v
          _              = E.add E.zero v := (E.zero_add v).symm
      have ⟨hw₁, _⟩ := h_unic v E.zero E.zero v hv₁ hW₁.zero_mem hW₂.zero_mem hv₂ heq
      exact hw₁
    · intro hv
      rw [hv]
      exact ⟨hW₁.zero_mem, hW₂.zero_mem⟩


