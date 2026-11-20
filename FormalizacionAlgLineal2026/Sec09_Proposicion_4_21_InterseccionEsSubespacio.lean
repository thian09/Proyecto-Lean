import FormalizacionAlgLineal2026.Sec08_Definicion_4_20_InterseccionSubespacios

/-!
====================================================================
9. PROPOSICIÓN 4.21: LA INTERSECCIÓN DE SUBESPACIOS ES UN SUBESPACIO
====================================================================

"Proposición 4.21. Sea (V, +, ·) un ℝ-espacio vectorial. Si W₁ y W₂ son subespacios vectoriales
de V, entonces W₁ ∩ W₂ es un subespacio vectorial de V.
Más generalmente, si ℱ = {W_i ⊆ V : i ∈ I} es una familia arbitraria de subespacios vectoriales de V,
la intersección ⋂_{i ∈ I} W_i también es un subespacio vectorial de V.

Demostración:
I.   Como 0_V pertenece a cualquier subespacio vectorial de V, entonces 0_V ∈ W_i para todo i ∈ I
     y por lo tanto 0_V ∈ ⋂_{i ∈ I} W_i;
II.  Sean w₁, w₂ ∈ ⋂_{i ∈ I} W_i. Pertenecen simultáneamente a todos los W_i con i ∈ I, luego
     w₁ + w₂ ∈ W_i para todo i ∈ I y por lo tanto w₁ + w₂ ∈ ⋂_{i ∈ I} W_i;
III. Sean w ∈ ⋂_{i ∈ I} W_i y λ ∈ ℝ. w pertenece a todos los W_i, luego λ · w ∈ W_i para todo i ∈ I
     y por lo tanto λ · w ∈ ⋂_{i ∈ I} W_i."
-/

/-- Proposición 4.21 (Caso general: la intersección de una familia arbitraria de subespacios es un subespacio). -/
theorem prop_4_21_interseccion_familia {V : Type _} {I : Type _}
    (E : EspacioVectorial V) (W : I → (V → Prop))
    (hW : ∀ i : I, EsSubespacio E (W i)) :
    EsSubespacio E (InterseccionFamilia W) where
  zero_mem := by
    intro i
    exact (hW i).zero_mem
  add_mem := by
    intro w₁ w₂ hw₁ hw₂ i
    exact (hW i).add_mem (hw₁ i) (hw₂ i)
  smul_mem := by
    intro «λ» w hw i
    exact (hW i).smul_mem «λ» (hw i)

/-- Proposición 4.21 (Caso binario: la intersección de dos subespacios es un subespacio vectorial). -/
theorem prop_4_21_interseccion_dos {V : Type _}
    (E : EspacioVectorial V) (W₁ W₂ : V → Prop)
    (hW₁ : EsSubespacio E W₁) (hW₂ : EsSubespacio E W₂) :
    EsSubespacio E (InterseccionDos W₁ W₂) where
  zero_mem := ⟨hW₁.zero_mem, hW₂.zero_mem⟩
  add_mem := by
    intro w₁ w₂ hw₁ hw₂
    exact ⟨hW₁.add_mem hw₁.1 hw₂.1, hW₂.add_mem hw₁.2 hw₂.2⟩
  smul_mem := by
    intro «λ» w hw
    exact ⟨hW₁.smul_mem «λ» hw.1, hW₂.smul_mem «λ» hw.2⟩


