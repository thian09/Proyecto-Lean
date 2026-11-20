import FormalizacionAlgLineal2026.Sec05_ContrasteIdiomatico

/-!
====================================================================
6. PROPOSICIÓN 4.5: OTRAS PROPIEDADES ARITMÉTICAS
====================================================================

"Proposición 4.5 (Otras propiedades aritméticas). Sea (V, +, ·) un ℝ-espacio vectorial.
  I.   Para todo v ∈ V, 0 · v = 0_V;
  II.  Para todo v ∈ V, (-1) · v = -v;
  III. Para todo λ ∈ ℝ, λ · 0_V = 0_V;
  IV.  Si λ · v = 0_V, entonces λ = 0 o v = 0_V.

Demostración:
(I.) Como v = 1 · v (EV6.),
  v = 1 · v = (1 + 0) · v = 1 · v + 0 · v = v + 0 · v ⟺ 0_V = 0 · v (Corolario 4.4).

(II.) Como v = 1 · v (EV6.), y por definición del opuesto (EV4.):
  v + (-v) = 0_V = 0 · v = (1 + (-1)) · v = 1 · v + (-1) · v = v + (-1) · v ⟺ -v = (-1) · v (Corolario 4.4).

(III.) Como 0_V + 0_V = 0_V (EV3.), multiplicando por λ,
  λ · 0_V = λ · (0_V + 0_V) = 0_V + λ · 0_V = λ · 0_V + λ · 0_V ⟺ 0_V = λ · 0_V (Corolario 4.4).

(IV.) Si λ = 0, se sigue de I. Caso contrario,
  λ · v = 0_V ⟹ (λ⁻¹ · λ) · v = λ⁻¹ · 0_V ⟺ v = 0_V."
-/

-- Proyecciones canónicas del elemento neutro y del opuesto aditivo (EV3 y EV4):
noncomputable def EspacioVectorial.zero {V : Type _} (E : EspacioVectorial V) : V :=
  Classical.choose E.ev3_ev4

theorem EspacioVectorial.zero_is_neutro {V : Type _} (E : EspacioVectorial V) :
    EsNeutroSuma E.add E.zero :=
  (Classical.choose_spec E.ev3_ev4).1

noncomputable def EspacioVectorial.neg {V : Type _} (E : EspacioVectorial V) (v : V) : V :=
  Classical.choose ((Classical.choose_spec E.ev3_ev4).2 v)

theorem EspacioVectorial.neg_is_opuesto {V : Type _} (E : EspacioVectorial V) (v : V) :
    EsOpuestoSuma E.add E.zero v (E.neg v) :=
  Classical.choose_spec ((Classical.choose_spec E.ev3_ev4).2 v)

-- Cancelación aditiva por izquierda y por derecha para la estructura EspacioVectorial:
theorem EspacioVectorial.cancelacion {V : Type _} (E : EspacioVectorial V)
    (u v w : V) (h : E.add u v = E.add u w) : v = w :=
  corolario_4_4_cancelacion E.add E.ev1_add_assoc E.ev2_add_comm
    E.zero E.zero_is_neutro u v w (E.neg u) (E.neg_is_opuesto u) h

theorem EspacioVectorial.cancelacion_der {V : Type _} (E : EspacioVectorial V)
    (u v w : V) (h : E.add v u = E.add w u) : v = w := by
  apply E.cancelacion u
  rw [E.ev2_add_comm u v, E.ev2_add_comm u w]
  exact h

-- Propiedades inmediatas del neutro y del opuesto aditivo
theorem EspacioVectorial.add_zero {V : Type _} (E : EspacioVectorial V) (v : V) :
    E.add v E.zero = v :=
  E.zero_is_neutro v

theorem EspacioVectorial.zero_add {V : Type _} (E : EspacioVectorial V) (v : V) :
    E.add E.zero v = v := by
  rw [E.ev2_add_comm]
  exact E.add_zero v

theorem EspacioVectorial.add_neg {V : Type _} (E : EspacioVectorial V) (v : V) :
    E.add v (E.neg v) = E.zero :=
  E.neg_is_opuesto v

theorem EspacioVectorial.neg_add {V : Type _} (E : EspacioVectorial V) (v : V) :
    E.add (E.neg v) v = E.zero := by
  rw [E.ev2_add_comm]
  exact E.add_neg v

/-- Proposición 4.5 (Parte I): Para todo v ∈ V, 0 · v = 0_V. -/
theorem prop_4_5_i {V : Type _} (E : EspacioVectorial V) (v : V) :
    E.smul 0 v = E.zero := by
  have h1 : E.add v (E.smul 0 v) = E.add v E.zero := by
    calc
      E.add v (E.smul 0 v)
        = E.add (E.smul 1 v) (E.smul 0 v) := by rw [E.ev6_one_smul]
      _ = E.smul (1 + 0) v                 := (E.ev8_add_smul 1 0 v).symm
      _ = E.smul 1 v                       := by rw [add_zero]
      _ = v                                := E.ev6_one_smul v
      _ = E.add v E.zero                   := (E.add_zero v).symm
  exact E.cancelacion v (E.smul 0 v) E.zero h1

/-- Proposición 4.5 (Parte II): Para todo v ∈ V, (-1) · v = -v. -/
theorem prop_4_5_ii {V : Type _} (E : EspacioVectorial V) (v : V) :
    E.smul (-1) v = E.neg v := by
  have h1 : E.add v (E.smul (-1) v) = E.add v (E.neg v) := by
    calc
      E.add v (E.smul (-1) v)
        = E.add (E.smul 1 v) (E.smul (-1) v) := by rw [E.ev6_one_smul]
      _ = E.smul (1 + (-1)) v                := (E.ev8_add_smul 1 (-1) v).symm
      _ = E.smul 0 v                         := by rw [add_neg_cancel]
      _ = E.zero                             := prop_4_5_i E v
      _ = E.add v (E.neg v)                  := (E.add_neg v).symm
  exact E.cancelacion v (E.smul (-1) v) (E.neg v) h1

/-- Proposición 4.5 (Parte III): Para todo λ ∈ ℝ, λ · 0_V = 0_V. -/
theorem prop_4_5_iii {V : Type _} (E : EspacioVectorial V) («λ» : ℝ) :
    E.smul «λ» E.zero = E.zero := by
  have hz_add : E.add E.zero E.zero = E.zero := E.add_zero E.zero
  have h1 : E.add (E.smul «λ» E.zero) (E.smul «λ» E.zero) = E.add (E.smul «λ» E.zero) E.zero := by
    calc
      E.add (E.smul «λ» E.zero) (E.smul «λ» E.zero)
        = E.smul «λ» (E.add E.zero E.zero) := (E.ev7_smul_add «λ» E.zero E.zero).symm
      _ = E.smul «λ» E.zero               := by rw [hz_add]
      _ = E.add (E.smul «λ» E.zero) E.zero := (E.add_zero (E.smul «λ» E.zero)).symm
  exact E.cancelacion (E.smul «λ» E.zero) (E.smul «λ» E.zero) E.zero h1

/-- Proposición 4.5 (Parte IV): Si λ · v = 0_V, entonces λ = 0 o v = 0_V. -/
theorem prop_4_5_iv {V : Type _} (E : EspacioVectorial V) («λ» : ℝ) (v : V)
    (h : E.smul «λ» v = E.zero) :
    «λ» = 0 ∨ v = E.zero := by
  open Classical in
  by_cases h_zero : «λ» = 0
  · exact Or.inl h_zero
  · right
    have h_inv : «λ»⁻¹ * «λ» = 1 := inv_mul_cancel₀ h_zero
    calc
      v = E.smul 1 v                := (E.ev6_one_smul v).symm
      _ = E.smul («λ»⁻¹ * «λ») v      := by rw [h_inv]
      _ = E.smul «λ»⁻¹ (E.smul «λ» v) := E.ev5_smul_assoc «λ»⁻¹ «λ» v
      _ = E.smul «λ»⁻¹ E.zero         := by rw [h]
      _ = E.zero                   := prop_4_5_iii E «λ»⁻¹


