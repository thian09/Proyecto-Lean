import FormalizacionAlgLineal2026.Sec09_Proposicion_4_21_InterseccionEsSubespacio

/-!
====================================================================
10. OBSERVACIÓN 4.22 Y EJEMPLO 4.24: UNIÓN DE SUBESPACIOS
====================================================================

"Observación 4.22 (Página 136). Notar que ⋂_{i ∈ I} W_i también es un subespacio vectorial de todos los W_i...

Ejemplo 4.24 (Página 137) (Unión de subespacios vectoriales).
La unión de subespacios vectoriales ni siempre es un subespacio vectorial.
Recordamos que rectas que pasan por el origen son subespacios vectoriales de ℝ² (Ejemplo 4.8).
Pero si consideramos solo las rectas r_x : y = 0 y r_y : x = 0, r_x ∪ r_y no es un subespacio vectorial
de ℝ² porque, por ejemplo, no es cerrado por la suma:
  (1, 0) ∈ r_x y (0, 1) ∈ r_y, pero (1, 0) +_{ℝ²} (0, 1) = (1, 1) ∉ r_x ∪ r_y."
-/

/-- Observación 4.22: La intersección de una familia de subespacios está contenida en cada W_j. -/
theorem obs_4_22_subconjunto {V : Type _} {I : Type _}
    (W : I → (V → Prop)) (j : I) (v : V)
    (hv : InterseccionFamilia W v) : W j v :=
  hv j

-- Estructura canónica del espacio vectorial ℝ² = ℝ × ℝ para el contraejemplo:
def R2 : Type := ℝ × ℝ

noncomputable def R2_add (u v : R2) : R2 :=
  (u.1 + v.1, u.2 + v.2)

noncomputable def R2_smul («λ» : ℝ) (u : R2) : R2 :=
  («λ» * u.1, «λ» * u.2)

noncomputable def R2_EspacioVectorial : EspacioVectorial R2 where
  add := R2_add
  smul := R2_smul
  ev1_add_assoc := by
    intro u v w
    dsimp [R2_add]
    rw [add_assoc, add_assoc]
  ev2_add_comm := by
    intro u v
    dsimp [R2_add]
    rw [add_comm u.1 v.1, add_comm u.2 v.2]
  ev3_ev4 := by
    refine ⟨(0, 0), ?_, ?_⟩
    · intro v
      dsimp [EsNeutroSuma, R2_add]
      rw [add_zero, add_zero]
      cases v; rfl
    · intro v
      refine ⟨(-v.1, -v.2), ?_⟩
      dsimp [EsOpuestoSuma, R2_add]
      rw [add_neg_cancel, add_neg_cancel]
  ev5_smul_assoc := by
    intro «λ» μ v
    dsimp [R2_smul]
    rw [mul_assoc, mul_assoc]
  ev6_one_smul := by
    intro v
    dsimp [R2_smul]
    rw [one_mul, one_mul]
    cases v; rfl
  ev7_smul_add := by
    intro «λ» v w
    dsimp [R2_smul, R2_add]
    rw [mul_add, mul_add]
  ev8_add_smul := by
    intro «λ» μ v
    dsimp [R2_smul, R2_add]
    rw [add_mul, add_mul]

-- Rectas r_x : y = 0 y r_y : x = 0 en ℝ²
def r_x : R2 → Prop := fun p => p.2 = 0
def r_y : R2 → Prop := fun p => p.1 = 0

-- La unión r_x ∪ r_y
def UnionSubespacios (W₁ W₂ : R2 → Prop) : R2 → Prop :=
  fun p => W₁ p ∨ W₂ p

/-- Ejemplo 4.24: La unión de subespacios vectoriales no es necesariamente un subespacio vectorial,
    pues (1, 0) ∈ r_x ∪ r_y y (0, 1) ∈ r_x ∪ r_y, pero su suma (1, 1) ∉ r_x ∪ r_y. -/
theorem ejemplo_4_24_union_no_es_subespacio :
    ¬ (∀ {w₁ w₂ : R2}, UnionSubespacios r_x r_y w₁ → UnionSubespacios r_x r_y w₂ →
        UnionSubespacios r_x r_y (R2_add w₁ w₂)) := by
  intro h_cerrado
  have hw₁ : UnionSubespacios r_x r_y (1, 0) := Or.inl rfl
  have hw₂ : UnionSubespacios r_x r_y (0, 1) := Or.inr rfl
  have h_sum : UnionSubespacios r_x r_y (R2_add (1, 0) (0, 1)) :=
    h_cerrado hw₁ hw₂
  have h_eval : R2_add (1, 0) (0, 1) = (1, 1) := by
    dsimp [R2_add]
    rw [add_zero, add_comm (0:ℝ) 1, add_zero]
  rw [h_eval] at h_sum
  dsimp [UnionSubespacios, r_x, r_y] at h_sum
  cases h_sum with
  | inl h => exact one_ne_zero h
  | inr h => exact one_ne_zero h


