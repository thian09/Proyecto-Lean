import FormalizacionAlgLineal2026.Sec01_Definicion_4_1_EspacioVectorial

/-!
====================================================================
2. PROPOSICIÓN 4.3: UNICIDAD DEL NEUTRO Y DEL OPUESTO
====================================================================

"Proposición 4.3 (Unicidad del neutro y opuesto). Sea (V, +, ·) un ℝ-espacio vectorial.
El neutro de la suma (0_V tal que v + 0_V = v para todo v ∈ V) es único.
Además, el opuesto de cualquier elemento v ∈ V (un -v ∈ V tal que v + (-v) = 0_V)
también es único.

Demostración:
Si tuviéramos dos, 0_V y 0_V', entonces 0_V + 0_V', por un lado es 0_V (pues 0_V' es neutro)
y por otro lado es 0_V' (pues 0_V es neutro). Por lo tanto, 0_V = 0_V + 0_V' = 0_V', y el
neutro de la suma es único.

Sea v ∈ V. Supongamos que existieran dos opuestos -v y -v'. Por definición de opuestos,
v + (-v) = 0_V = v + (-v'). Sumando -v a la ecuación..."
-/

/-- Unicidad del elemento neutro (Proposición 4.3, parte 1). -/
theorem prop_4_3_unicidad_neutro {V : Type _} (add : V → V → V)
    (add_comm : ∀ v w : V, add v w = add w v)
    (z₁ z₂ : V)
    (hz₁ : EsNeutroSuma add z₁)
    (hz₂ : EsNeutroSuma add z₂) :
    z₁ = z₂ := by
  calc
    z₁ = add z₁ z₂ := (hz₂ z₁).symm
    _  = add z₂ z₁ := add_comm z₁ z₂
    _  = z₂        := hz₁ z₂

/-- Unicidad del elemento opuesto (Proposición 4.3, parte 2). -/
theorem prop_4_3_unicidad_opuesto {V : Type _} (add : V → V → V)
    (add_assoc : ∀ u v w : V, add (add u v) w = add u (add v w))
    (add_comm : ∀ v w : V, add v w = add w v)
    (z : V) (hz : EsNeutroSuma add z)
    (v w₁ w₂ : V)
    (hw₁ : EsOpuestoSuma add z v w₁)
    (hw₂ : EsOpuestoSuma add z v w₂) :
    w₁ = w₂ := by
  have hz_left : ∀ x : V, add z x = x := by
    intro x
    rw [add_comm]
    exact hz x
  have hw₂_comm : add w₂ v = z := by
    rw [add_comm]
    exact hw₂
  calc
    w₁ = add z w₁          := (hz_left w₁).symm
    _  = add (add w₂ v) w₁ := congrArg (fun t => add t w₁) hw₂_comm.symm
    _  = add w₂ (add v w₁) := add_assoc w₂ v w₁
    _  = add w₂ z          := congrArg (fun t => add w₂ t) hw₁
    _  = w₂                := hz w₂


