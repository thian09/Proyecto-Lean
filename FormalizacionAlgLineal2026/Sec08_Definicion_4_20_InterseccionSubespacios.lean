import FormalizacionAlgLineal2026.Sec07_Definicion_4_6_SubespacioVectorial

/-!
====================================================================
8. DEFINICIÓN 4.20: INTERSECCIÓN DE SUBESPACIOS VECTORIALES
====================================================================

"Definición 4.20 (Intersección de subespacios vectoriales). Sea (V, +, ·) un ℝ-espacio vectorial.
Si W₁ y W₂ son dos subespacios vectoriales de V, definimos la intersección de W₁ y W₂ como
siendo el conjunto de los elementos de V que pertenecen simultáneamente a W₁ y a W₂:
  W₁ ∩ W₂ := {v ∈ V : v ∈ W₁ y v ∈ W₂}.
Más generalmente, si ℱ = {W_i : i ∈ I} es una familia arbitraria de subespacios vectoriales de V,
la intersección de los W_i (i ∈ I) es definida por los elementos de V que están simultáneamente en todos los W_i:
  ⋂_{i ∈ I} W_i := {v ∈ V : v ∈ W_i, ∀ i ∈ I}."
-/

/-- Definición 4.20 (Intersección binaria de subespacios vectoriales). -/
def InterseccionDos {V : Type _} (W₁ W₂ : V → Prop) : V → Prop :=
  fun v => W₁ v ∧ W₂ v

/-- Definición 4.20 (Intersección de una familia arbitraria {W_i : i ∈ I}). -/
def InterseccionFamilia {V : Type _} {I : Type _} (W : I → (V → Prop)) : V → Prop :=
  fun v => ∀ i : I, W i v


