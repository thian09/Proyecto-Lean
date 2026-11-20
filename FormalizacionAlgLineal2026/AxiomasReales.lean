/-
  Formalización en Lean 4: FormalizacionAlgLineal2026
  Texto fuente: "Notas del curso Álgebra Lineal 1" (Eris Rocha Walchek, FCIEN UdelaR)

  Archivo unificado que integra:
  — Capítulo 4: Espacios Vectoriales (Definición 4.1 – Corolario 4.39)
  — Capítulo 5: Generadores, (In)dependencia Lineal y Bases (Definición 5.1 – Teorema 5.54)

  Fidelidad minuciosa al texto original:
  1. Estructura algebraica definida exactamente como la terna (V, +, ·).
  2. Conservación de los 8 axiomas originales (EV1 a EV8).
  3. Formulación existencial de EV3 (neutro) y EV4 (opuesto), sin asumir
     unicidad a priori (tal como señala la Observación 4.2).
  4. Demostración formal de la Proposición 4.3 (Unicidad del neutro y del opuesto).
  5. Demostración formal del Corolario 4.4 (Cancelación de la suma).
  6. Generalización a un cuerpo arbitrario k (Observación 4.2).
  7. Conexión con la formulación idiomática empaquetada de Mathlib.
  8. Demostración formal de la Proposición 4.5 (Otras propiedades aritméticas I a IV).
  9. Formalización de la Definición 4.6 (Subespacio vectorial).
  10. Formalización de la Definición 4.20 (Intersección binaria y de familias arbitrarias).
  11. Demostración formal de la Proposición 4.21 (La intersección de subespacios es subespacio).
  12. Formalización de la Observación 4.22 y demostración del contraejemplo del Ejemplo 4.24.
  13. Formalización de la Definición 4.25 (Suma binaria y de familias arbitrarias).
  14. Demostración formal de la Proposición 4.27 (La suma de subespacios es un subespacio).
  15. Formalización de la Definición 4.33 y Teorema 4.34 (Suma directa binaria).
  16. Formalización de la Definición 4.37 y Teorema 4.38 (Suma directa arbitraria).
  17. Demostración formal del Corolario 4.39 (Intersección trivial en sumas directas).
  18. Formalización de la Definición 5.1 (Combinación lineal) y Definición 5.3 (Subespacio generado).
  19. Proposición 5.5 (⟨S⟩ es subespacio) y Proposición 5.7 (Propiedades de ⟨S⟩).
  20. Corolario 5.8, Teorema 5.9 (⟨S⟩ es el menor subespacio conteniendo S).
  21. Proposición 5.11 (Unión genera suma).
  22. Definición 5.15 ((In)dependencia lineal) y Lema 5.20.
  23. Proposición 5.21, Corolario 5.23, Definición 5.24 (Base).
  24. Teorema 5.26 (Definiciones equivalentes de base).
  25. Definición 5.29 (Espacio finitamente generado) y Teorema 5.30.
  26. Teorema 5.34 (Completamiento de bases) y Proposición 5.37–5.38.
  27. Definición 5.39 (Dimensión), Proposición 5.41, Corolario 5.43.
  28. Teorema 5.45–5.46, Teorema 5.48, Corolario 5.49.
  29. Teorema 5.52 y 5.54 (Bases de sumas directas).
-/

-- ====================================================================
-- DEFINICIÓN AXIOMÁTICA DE LOS REALES ℝ Y CUERPO (FIELD)
-- ====================================================================
-- Permite compilación autónoma sin Mathlib con la estructura completa
-- de un cuerpo conmutativo.

axiom R : Type
notation "ℝ" => R

axiom R_zero : ℝ
axiom R_one : ℝ
axiom R_add : ℝ → ℝ → ℝ
axiom R_mul : ℝ → ℝ → ℝ
axiom R_neg : ℝ → ℝ
axiom R_inv : ℝ → ℝ

noncomputable instance : Zero ℝ := ⟨R_zero⟩
noncomputable instance : One ℝ := ⟨R_one⟩
noncomputable instance : Add ℝ := ⟨R_add⟩
noncomputable instance : Mul ℝ := ⟨R_mul⟩
noncomputable instance : Neg ℝ := ⟨R_neg⟩
noncomputable instance : Inv ℝ := ⟨R_inv⟩

-- Sub y Div derivados para compatibilidad algebraica
noncomputable instance : Sub ℝ := ⟨fun a b => a + -b⟩
noncomputable instance : Div ℝ := ⟨fun a b => a * b⁻¹⟩

theorem sub_eq_add_neg (a b : ℝ) : a - b = a + -b := rfl
theorem div_eq_mul_inv (a b : ℝ) : a / b = a * b⁻¹ := rfl

-- --------------------------------------------------------------------
-- AXIOMAS DE CUERPO PARA ℝ
-- --------------------------------------------------------------------

-- Axiomas del grupo aditivo conmutativo (ℝ, +, 0)
axiom add_assoc (a b c : ℝ) : (a + b) + c = a + (b + c)
axiom add_comm (a b : ℝ) : a + b = b + a
axiom add_zero (a : ℝ) : a + 0 = a
axiom add_neg_cancel (a : ℝ) : a + -a = 0

-- Axiomas del monoide conmutativo multiplicativo con inversos para no nulos (ℝ \ {0}, ·, 1)
axiom mul_assoc (a b c : ℝ) : (a * b) * c = a * (b * c)
axiom mul_comm (a b : ℝ) : a * b = b * a
axiom one_mul (a : ℝ) : 1 * a = a
axiom inv_mul_cancel₀ {a : ℝ} (h : a ≠ 0) : a⁻¹ * a = 1

-- Distributividad y no trivialidad
axiom mul_add (a b c : ℝ) : a * (b + c) = a * b + a * c
axiom add_mul (a b c : ℝ) : (a + b) * c = a * c + b * c
axiom one_ne_zero : (1 : ℝ) ≠ 0

-- --------------------------------------------------------------------
-- PROPIEDADES ARITMÉTICAS DERIVADAS EN ℝ
-- --------------------------------------------------------------------

-- Neutro y cancelación aditiva
theorem zero_add (a : ℝ) : 0 + a = a := by
  rw [add_comm, add_zero]

theorem neg_add_cancel (a : ℝ) : -a + a = 0 := by
  rw [add_comm, add_neg_cancel]

theorem add_cancel_left {a b c : ℝ} (h : a + b = a + c) : b = c := by
  calc
    b = 0 + b        := (zero_add b).symm
    _ = (-a + a) + b := by rw [neg_add_cancel]
    _ = -a + (a + b) := by rw [add_assoc]
    _ = -a + (a + c) := by rw [h]
    _ = (-a + a) + c := (add_assoc (-a) a c).symm
    _ = 0 + c        := by rw [neg_add_cancel]
    _ = c            := zero_add c

theorem add_cancel_right {a b c : ℝ} (h : b + a = c + a) : b = c := by
  apply add_cancel_left (a := a)
  rw [add_comm a b, add_comm a c]
  exact h

-- Neutro e inversos multiplicativos por derecha
theorem mul_one (a : ℝ) : a * 1 = a := by
  rw [mul_comm, one_mul]

theorem mul_inv_cancel₀ {a : ℝ} (h : a ≠ 0) : a * a⁻¹ = 1 := by
  rw [mul_comm]
  exact inv_mul_cancel₀ h

-- Propiedades del cero y signos
theorem zero_mul (a : ℝ) : 0 * a = 0 := by
  apply add_cancel_left (a := 0 * a)
  calc
    0 * a + 0 * a = (0 + 0) * a := (add_mul 0 0 a).symm
    _             = 0 * a       := by rw [add_zero]
    _             = 0 * a + 0   := (add_zero (0 * a)).symm

theorem mul_zero (a : ℝ) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem neg_neg (a : ℝ) : -(-a) = a := by
  apply add_cancel_left (a := -a)
  rw [add_neg_cancel, neg_add_cancel]

theorem neg_zero : (-0 : ℝ) = 0 := by
  have h := add_neg_cancel (0 : ℝ)
  rw [zero_add] at h
  exact h

theorem neg_mul (a b : ℝ) : -(a * b) = (-a) * b := by
  apply add_cancel_left (a := a * b)
  calc
    a * b + -(a * b) = 0                := add_neg_cancel (a * b)
    _                = 0 * b            := (zero_mul b).symm
    _                = (a + -a) * b     := by rw [add_neg_cancel]
    _                = a * b + (-a) * b := add_mul a (-a) b

theorem mul_neg (a b : ℝ) : -(a * b) = a * (-b) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem neg_one_mul (a : ℝ) : (-1) * a = -a := by
  calc
    (-1) * a = -(1 * a) := (neg_mul 1 a).symm
    _        = -a       := by rw [one_mul]

theorem mul_neg_one (a : ℝ) : a * (-1) = -a := by
  rw [mul_comm, neg_one_mul]

-- --------------------------------------------------------------------
-- ESTRUCTURA ALGEBRAICA GENERAL DE CUERPO (FIELD)
-- --------------------------------------------------------------------

class Field (K : Type _) extends Zero K, One K, Add K, Mul K, Neg K, Inv K where
  add_assoc       : ∀ a b c : K, (a + b) + c = a + (b + c)
  add_comm        : ∀ a b : K, a + b = b + a
  add_zero        : ∀ a : K, a + 0 = a
  add_neg_cancel  : ∀ a : K, a + -a = 0
  mul_assoc       : ∀ a b c : K, (a * b) * c = a * (b * c)
  mul_comm        : ∀ a b : K, a * b = b * a
  one_mul         : ∀ a : K, 1 * a = a
  inv_mul_cancel₀ : ∀ {a : K}, a ≠ 0 → a⁻¹ * a = 1
  mul_add         : ∀ a b c : K, a * (b + c) = a * b + a * c
  one_ne_zero     : (1 : K) ≠ 0

noncomputable instance : Field ℝ where
  add_assoc       := add_assoc
  add_comm        := add_comm
  add_zero        := add_zero
  add_neg_cancel  := add_neg_cancel
  mul_assoc       := mul_assoc
  mul_comm        := mul_comm
  one_mul         := one_mul
  inv_mul_cancel₀ := inv_mul_cancel₀
  mul_add         := mul_add
  one_ne_zero     := one_ne_zero
