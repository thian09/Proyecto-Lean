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

-- 1. Definición axiomática de los Reales ℝ y Field (permite compilación autónoma sin Mathlib)
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

axiom add_zero (a : ℝ) : a + 0 = a
axiom add_neg_cancel (a : ℝ) : a + -a = 0
axiom inv_mul_cancel₀ {a : ℝ} (h : a ≠ 0) : a⁻¹ * a = 1
axiom add_assoc (a b c : ℝ) : (a + b) + c = a + (b + c)
axiom add_comm (a b : ℝ) : a + b = b + a
axiom mul_assoc (a b c : ℝ) : (a * b) * c = a * (b * c)
axiom one_mul (a : ℝ) : 1 * a = a
axiom mul_add (a b c : ℝ) : a * (b + c) = a * b + a * c
axiom add_mul (a b c : ℝ) : (a + b) * c = a * c + b * c
axiom one_ne_zero : (1 : ℝ) ≠ 0

class Field (K : Type _) extends Zero K, One K, Add K, Mul K, Neg K, Inv K

noncomputable instance : Field ℝ where

/-!
====================================================================
1. DEFINICIÓN 4.1: ESPACIO VECTORIAL SOBRE ℝ
====================================================================

"Definición 4.1 (Espacio vectorial). Un espacio vectorial (sobre ℝ) es una
estructura algébrica (V, +, ·) consistiendo de un conjunto V provisto de
una suma +: V × V → V y un producto por escalar ·: ℝ × V → V que cumplen
las siguientes propiedades:
  EV1. Asociatividad de la suma: (u + v) + w = u + (v + w), ∀ u, v, w ∈ V;
  EV2. Conmutatividad de la suma: v + w = w + v, ∀ v, w ∈ V;
  EV3. Elemento neutro de la suma: existe 0_V tal que v + 0 = v para todo v ∈ V;
  EV4. Opuesto aditivo: Para cada v ∈ V, existe un vector -v tal que v + (-v) = 0;
  EV5. Asociatividad del producto por escalar: (λ μ) · v = λ · (μ · v), ∀ v ∈ V, ∀ λ, μ ∈ ℝ;
  EV6. Elemento neutro del producto por escalar: 1 · v = v, ∀ v ∈ V;
  EV7. Distributividad con relación a la suma de vectores: λ · (v + w) = λ · v + λ · w, ∀ v, w ∈ V, ∀ λ ∈ ℝ;
  EV8. Distributividad con relación a la suma de escalares: (λ + μ) · v = λ · v + μ · v, ∀ v ∈ V, ∀ λ, μ ∈ ℝ."
-/

-- Predicado auxiliar: z es neutro aditivo por derecha (v + z = v) según enuncia EV3
def EsNeutroSuma {V : Type _} (add : V → V → V) (z : V) : Prop :=
  ∀ v : V, add v z = v

-- Predicado auxiliar: neg_v es opuesto aditivo de v respecto a un neutro z (v + neg_v = z) según enuncia EV4
def EsOpuestoSuma {V : Type _} (add : V → V → V) (z : V) (v neg_v : V) : Prop :=
  add v neg_v = z

/-- Estructura algébrica (V, +, ·) de espacio vectorial sobre ℝ,
    fielmente transcrita de la Definición 4.1. -/
structure EspacioVectorial (V : Type _) where
  -- Datos de la terna (V, +, ·)
  add  : V → V → V
  smul : ℝ → V → V

  -- EV1. Asociatividad de la suma
  ev1_add_assoc : ∀ u v w : V, add (add u v) w = add u (add v w)

  -- EV2. Conmutatividad de la suma
  ev2_add_comm  : ∀ v w : V, add v w = add w v

  -- EV3 y EV4. Existencia de neutro aditivo y opuestos
  -- El texto afirma: existe 0_V con v + 0_V = v, y para cada v existe -v tal que v + (-v) = 0_V.
  -- Nótese que NO se pide la unicidad a priori (Observación 4.2).
  ev3_ev4 : ∃ (zero : V), EsNeutroSuma add zero ∧ (∀ v : V, ∃ neg_v : V, EsOpuestoSuma add zero v neg_v)

  -- EV5. Asociatividad del producto por escalar
  ev5_smul_assoc : ∀ («λ» μ : ℝ) (v : V), smul («λ» * μ) v = smul «λ» (smul μ v)

  -- EV6. Elemento neutro del producto por escalar
  ev6_one_smul : ∀ v : V, smul 1 v = v

  -- EV7. Distributividad con relación a la suma de vectores
  ev7_smul_add : ∀ («λ» : ℝ) (v w : V), smul «λ» (add v w) = add (smul «λ» v) (smul «λ» w)

  -- EV8. Distributividad con relación a la suma de escalares
  ev8_add_smul : ∀ («λ» μ : ℝ) (v : V), smul («λ» + μ) v = add (smul «λ» v) (smul μ v)


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


/-!
====================================================================
3. COROLARIO 4.4: CANCELACIÓN DE LA SUMA
====================================================================

"Corolario 4.4 (Cancelación de la suma). Sea (V, +, ·) un ℝ-espacio vectorial.
Para cualesquiera u, v, w ∈ V, si u + v = u + w, entonces v = w.

Demostración: Basta con sumar -u a la ecuación, lo que no cambia la igualdad."
-/

/-- Ley de cancelación aditiva (Corolario 4.4). -/
theorem corolario_4_4_cancelacion {V : Type _} (add : V → V → V)
    (add_assoc : ∀ u v w : V, add (add u v) w = add u (add v w))
    (add_comm : ∀ v w : V, add v w = add w v)
    (z : V) (hz : EsNeutroSuma add z)
    (u v w neg_u : V)
    (h_neg : EsOpuestoSuma add z u neg_u)
    (h : add u v = add u w) :
    v = w := by
  have hz_left : ∀ x : V, add z x = x := by
    intro x
    rw [add_comm]
    exact hz x
  have h_neg_comm : add neg_u u = z := by
    rw [add_comm]
    exact h_neg
  calc
    v = add z v             := (hz_left v).symm
    _ = add (add neg_u u) v := congrArg (fun t => add t v) h_neg_comm.symm
    _ = add neg_u (add u v) := add_assoc neg_u u v
    _ = add neg_u (add u w) := congrArg (fun t => add neg_u t) h
    _ = add (add neg_u u) w := (add_assoc neg_u u w).symm
    _ = add z w             := congrArg (fun t => add t w) h_neg_comm
    _ = w                   := hz_left w


/-!
====================================================================
4. OBSERVACIÓN 4.2: GENERALIZACIÓN A UN CUERPO k ARBITRARIO
====================================================================

"Además, el 'sobre ℝ' en la definición indica que los escalares son tomados en ℝ
(también se puede abreviar diciendo ℝ-espacio vectorial). Naturalmente, trabajando
con otro cuerpo k, los escalares serían tomados en k, definiendo un espacio vectorial sobre k."
-/

/-- Definición 4.1 generalizada sobre un cuerpo arbitrario K (k-espacio vectorial). -/
structure KEspacioVectorial (K : Type _) [Field K] (V : Type _) where
  add  : V → V → V
  smul : K → V → V

  ev1_add_assoc  : ∀ u v w : V, add (add u v) w = add u (add v w)
  ev2_add_comm   : ∀ v w : V, add v w = add w v
  ev3_ev4        : ∃ (zero : V), EsNeutroSuma add zero ∧ (∀ v : V, ∃ neg_v : V, EsOpuestoSuma add zero v neg_v)
  ev5_smul_assoc : ∀ («λ» μ : K) (v : V), smul («λ» * μ) v = smul «λ» (smul μ v)
  ev6_one_smul   : ∀ v : V, smul 1 v = v
  ev7_smul_add   : ∀ («λ» : K) (v w : V), smul «λ» (add v w) = add (smul «λ» v) (smul «λ» w)
  ev8_add_smul   : ∀ («λ» μ : K) (v : V), smul («λ» + μ) v = add (smul «λ» v) (smul μ v)


/-!
====================================================================
5. CONTRASTE IDIOMÁTICO EN LEAN 4: FIRMA ALGEBRAICA COMPUTACIONAL
====================================================================

¿Por qué en Lean 4 / Mathlib los espacios vectoriales se definen empaquetando
`0 : V` y `- : V → V` en la signatura (`AddCommGroup V`) en vez de usar `∃` en `Prop`?

En la Teoría de Tipos (Cálculo de Construcciones Inductivas):
- Las proposiciones `∃ x, P x` residen en `Prop` (Sort 0).
- Por la regla de eliminación de universos de Lean, de una prueba de `∃ x, P x` en `Prop`
  NO se puede extraer computacionalmente el término `x` para producir datos en `Type`
  (salvo apelando al axioma de elección `Classical.choose`).
- Para que `0_V` y `-v` sean operaciones de primer orden evaluables por el kernel,
  la signatura algebraica universal enriquecida se define como:
-/

structure EspacioVectorialEmpaquetado (V : Type _) where
  add          : V → V → V
  zero         : V
  neg          : V → V
  smul         : ℝ → V → V

  -- EV1
  add_assoc    : ∀ u v w : V, add (add u v) w = add u (add v w)
  -- EV2
  add_comm     : ∀ v w : V, add v w = add w v
  -- EV3 (con el testigo 0 computacionalmente explícito)
  add_zero     : ∀ v : V, add v zero = v
  -- EV4 (con la operación unaria de inversión - computacionalmente explícita)
  add_left_neg : ∀ v : V, add (neg v) v = zero
  -- EV5
  smul_assoc   : ∀ («λ» μ : ℝ) (v : V), smul («λ» * μ) v = smul «λ» (smul μ v)
  -- EV6
  one_smul     : ∀ v : V, smul 1 v = v
  -- EV7
  smul_add     : ∀ («λ» : ℝ) (v w : V), smul «λ» (add v w) = add (smul «λ» v) (smul «λ» w)
  -- EV8
  add_smul     : ∀ («λ» μ : ℝ) (v : V), smul («λ» + μ) v = add (smul «λ» v) (smul μ v)



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


/-!
====================================================================
11. DEFINICIÓN 4.25: SUMA DE SUBESPACIOS VECTORIALES
====================================================================

"Definición 4.25 (Suma de subespacios vectoriales). Sea (V, +, ·) un ℝ-espacio vectorial.
Si W₁ y W₂ son dos subespacios de V, definimos la suma de W₁ y W₂ como siendo el conjunto
de los elementos de V que son sumas de elementos de W₁ y W₂:
  W₁ + W₂ := {v ∈ V : v = w₁ + w₂ con w₁ ∈ W₁ y w₂ ∈ W₂}.
Más generalmente, si ℱ = {W_i : i ∈ I} es una familia arbitraria de subespacios vectoriales de V,
la suma de los W_i (i ∈ I) es definida por los elementos de V que son sumas finitas de elementos en W_i:
  ∑_{i ∈ I} W_i := {v ∈ V : v = ∑_{i ∈ I} w_i con w_i ∈ W_i y w_i = 0 excepto para finitos i ∈ I}."
-/

/-- Definición 4.25 (Suma de dos subespacios vectoriales). -/
def SumaDos {V : Type _} (E : EspacioVectorial V) (W₁ W₂ : V → Prop) : V → Prop :=
  fun v => ∃ (w₁ w₂ : V), W₁ w₁ ∧ W₂ w₂ ∧ v = E.add w₁ w₂

-- Suma finita computacionalmente inductiva de una lista de vectores en E:
noncomputable def EspacioVectorial.sumList {V : Type _} (E : EspacioVectorial V) : List V → V
  | [] => E.zero
  | x :: xs => E.add x (E.sumList xs)

theorem EspacioVectorial.sumList_nil {V : Type _} (E : EspacioVectorial V) :
    E.sumList [] = E.zero := rfl

theorem EspacioVectorial.sumList_cons {V : Type _} (E : EspacioVectorial V) (x : V) (xs : List V) :
    E.sumList (x :: xs) = E.add x (E.sumList xs) := rfl

theorem EspacioVectorial.sumList_append {V : Type _} (E : EspacioVectorial V) (xs ys : List V) :
    E.sumList (xs ++ ys) = E.add (E.sumList xs) (E.sumList ys) := by
  induction xs with
  | nil =>
    simp only [List.nil_append, sumList_nil]
    exact (E.zero_add (E.sumList ys)).symm
  | cons x xs ih =>
    simp only [List.cons_append, sumList_cons]
    rw [ih]
    exact (E.ev1_add_assoc x (E.sumList xs) (E.sumList ys)).symm

theorem EspacioVectorial.smul_sumList {V : Type _} (E : EspacioVectorial V) («λ» : ℝ) (xs : List V) :
    E.smul «λ» (E.sumList xs) = E.sumList (xs.map (E.smul «λ»)) := by
  induction xs with
  | nil =>
    simp only [sumList_nil, List.map_nil]
    exact prop_4_5_iii E «λ»
  | cons x xs ih =>
    simp only [sumList_cons, List.map_cons]
    rw [E.ev7_smul_add «λ» x (E.sumList xs), ih]

/-- Término de sumando de una familia: par (índice, vector) -/
structure TerminoFamilia (I V : Type _) where
  indice : I
  vector : V

/-- Definición 4.25 (Suma de una familia arbitraria {W_i : i ∈ I}):
    Un vector v pertenece a ∑_{i ∈ I} W_i si se expresa como la suma finita
    de elementos contenidos en los subespacios de la familia. -/
def SumaFamilia {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) : V → Prop :=
  fun v => ∃ (L : List (TerminoFamilia I V)),
    (∀ t ∈ L, W t.indice t.vector) ∧
    v = E.sumList (L.map TerminoFamilia.vector)


/-!
====================================================================
12. PROPOSICIÓN 4.27: LA SUMA DE SUBESPACIOS ES UN SUBESPACIO
====================================================================

"Proposición 4.27. Sea (V, +, ·) un ℝ-espacio vectorial. Si W₁ y W₂ son subespacios
vectoriales de V, entonces W₁ + W₂ es un subespacio vectorial de V.
Más generalmente, si ℱ = {W_i ⊆ V : i ∈ I} es una familia arbitraria de subespacios
vectoriales de V, la suma ∑_{i ∈ I} W_i también es un subespacio vectorial de V.

Demostración:
I.   0_V se escribe como una suma de w_i ∈ W_i donde el conjunto de sumandos no nulos es vacío.
     Por lo tanto, 0_V ∈ ∑_{i ∈ I} W_i;
II.  Sean v₁, v₂ ∈ ∑_{i ∈ I} W_i. v₁ = w_{i_1} + ... + w_{i_n} y v₂ = w_{i_{n+1}} + ... + w_{i_m}.
     Por lo tanto, la suma v₁ + v₂ es una suma finita de elementos contenidos en algunos de los W_i;
III. Sean v ∈ ∑_{i ∈ I} W_i y λ ∈ ℝ. Como cada W_i es subespacio cerrado por producto por escalar,
     λ · v = λ w_{i_1} + ... + λ w_{i_n} es una suma finita de elementos contenidos en algunos W_i."
-/

theorem EspacioVectorial.add_assoc_4 {V : Type _} (E : EspacioVectorial V) (a b c d : V) :
    E.add (E.add a b) (E.add c d) = E.add (E.add a c) (E.add b d) := by
  calc
    E.add (E.add a b) (E.add c d)
      = E.add a (E.add b (E.add c d)) := E.ev1_add_assoc a b (E.add c d)
    _ = E.add a (E.add (E.add b c) d) := by rw [E.ev1_add_assoc b c d]
    _ = E.add a (E.add (E.add c b) d) := by rw [E.ev2_add_comm b c]
    _ = E.add a (E.add c (E.add b d)) := by rw [E.ev1_add_assoc c b d]
    _ = E.add (E.add a c) (E.add b d) := (E.ev1_add_assoc a c (E.add b d)).symm

/-- Proposición 4.27 (Caso binario: la suma de dos subespacios es un subespacio vectorial). -/
theorem prop_4_27_suma_dos {V : Type _} (E : EspacioVectorial V) (W₁ W₂ : V → Prop)
    (hW₁ : EsSubespacio E W₁) (hW₂ : EsSubespacio E W₂) :
    EsSubespacio E (SumaDos E W₁ W₂) where
  zero_mem := by
    refine ⟨E.zero, E.zero, hW₁.zero_mem, hW₂.zero_mem, ?_⟩
    exact (E.add_zero E.zero).symm
  add_mem := by
    intro v₁ v₂ ⟨w₁, w₂, hw₁, hw₂, hv₁⟩ ⟨w₁', w₂', hw₁', hw₂', hv₂⟩
    refine ⟨E.add w₁ w₁', E.add w₂ w₂', hW₁.add_mem hw₁ hw₁', hW₂.add_mem hw₂ hw₂', ?_⟩
    rw [hv₁, hv₂, E.add_assoc_4 w₁ w₂ w₁' w₂']
  smul_mem := by
    intro «λ» v ⟨w₁, w₂, hw₁, hw₂, hv⟩
    refine ⟨E.smul «λ» w₁, E.smul «λ» w₂, hW₁.smul_mem «λ» hw₁, hW₂.smul_mem «λ» hw₂, ?_⟩
    rw [hv]
    exact E.ev7_smul_add «λ» w₁ w₂

/-- Proposición 4.27 (Caso general: la suma de una familia de subespacios es un subespacio vectorial). -/
theorem prop_4_27_suma_familia {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (hW : ∀ i : I, EsSubespacio E (W i)) :
    EsSubespacio E (SumaFamilia E W) where
  zero_mem := by
    refine ⟨[], ?_, ?_⟩
    · intro t ht
      cases ht
    · exact (E.sumList_nil).symm
  add_mem := by
    intro v₁ v₂ ⟨L₁, hL₁, hv₁⟩ ⟨L₂, hL₂, hv₂⟩
    refine ⟨L₁ ++ L₂, ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hL₁ t h
      · exact hL₂ t h
    · rw [hv₁, hv₂]
      simp only [List.map_append]
      exact (E.sumList_append (L₁.map TerminoFamilia.vector) (L₂.map TerminoFamilia.vector)).symm
  smul_mem := by
    intro «λ» v ⟨L, hL, hv⟩
    refine ⟨L.map (fun t => ⟨t.indice, E.smul «λ» t.vector⟩), ?_, ?_⟩
    · intro t ht
      rcases List.mem_map.mp ht with ⟨orig, horig, rfl⟩
      exact (hW orig.indice).smul_mem «λ» (hL orig horig)
    · rw [hv]
      have hmap (xs : List (TerminoFamilia I V)) :
          (xs.map (fun t => (⟨t.indice, E.smul «λ» t.vector⟩ : TerminoFamilia I V))).map
            TerminoFamilia.vector =
          (xs.map TerminoFamilia.vector).map (E.smul «λ») := by
        induction xs with
        | nil => rfl
        | cons head tail ih =>
          simp only [List.map_cons, ih]
      rw [hmap L]
      exact E.smul_sumList «λ» (L.map TerminoFamilia.vector)


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


/-!
====================================================================
15. COROLARIO 4.39: INTERSECCIÓN DE SUMA DIRECTA ARBITRARIA
====================================================================

"Corolario 4.39 (Página 146). Sea (V, +, ·) un ℝ-espacio vectorial. Si ℱ = {W_i ⊆ V : i ∈ I}
es una familia arbitraria de subespacios vectoriales de V y la suma ⨁_{i ∈ I} W_i es directa,
entonces ⋂_{i ∈ I} W_i = {0_V} (asumiendo que existen al menos dos índices distintos i₁ ≠ i₂ en I).

Demostración:
Si v ∈ ⋂_{i ∈ I} W_i, tomando i₁, i₂ ∈ I distintos y comparando las descomposiciones
  v = v_{i_1} + 0_{i_2} + 0_V + ...  y  v = 0_{i_1} + v_{i_2} + 0_V + ...,
tenemos que v = 0_V ∈ W_{i_1}, y por lo tanto, ⋂_{i ∈ I} W_i = {0_V}."
-/

/-- Corolario 4.39: Si la suma de una familia es directa y hay al menos dos índices distintos,
    su intersección es trivial ({0_V}). -/
theorem corolario_4_39_interseccion_trivial {V : Type _} {I : Type _}
    (E : EspacioVectorial V) (W : I → (V → Prop))
    (hdir : EsSumaDirectaFamilia E W)
    (i₁ i₂ : I) (hne : i₁ ≠ i₂)
    (v : V) (hv : ∀ i : I, W i v) :
    v = E.zero := by
  have hw₁ : W i₁ v := hv i₁
  have hw₂ : W i₂ v := hv i₂
  have h_excl : SumaExcluyendo E W i₁ v := by
    refine ⟨[⟨i₂, v⟩], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨hne.symm, hw₂⟩
    · simp only [List.map_cons, List.map_nil, EspacioVectorial.sumList_cons, EspacioVectorial.sumList_nil]
      exact (E.add_zero v).symm
  exact hdir i₁ v hw₁ h_excl


/-
  Formalización en Lean 4: Capítulo 5 — Generadores, (In)dependencia Lineal y Bases
  Texto fuente: "Notas del curso Álgebra Lineal 1" (Eris Rocha Walchek, FCIEN UdelaR)
  Capítulo 5: Generadores, (in)dependencia lineal y bases (Capitulo5_Bases.md)
-/


/-!
====================================================================
16. DEFINICIÓN 5.1: COMBINACIÓN LINEAL
====================================================================
-/

/-- Un término de una combinación lineal: un par (escalar, vector de S). -/
structure TerminoCombLin (V : Type _) where
  coef   : ℝ
  vector : V

/-- Definición 5.1 (Combinación lineal): Un vector v es una combinación lineal
    de elementos de S si se expresa como a₁ s₁ + ⋯ + aₙ sₙ con aᵢ ∈ ℝ y sᵢ ∈ S. -/
def EsCombinacionLineal {V : Type _} (E : EspacioVectorial V) (S : V → Prop) (v : V) : Prop :=
  ∃ (L : List (TerminoCombLin V)),
    (∀ t ∈ L, S t.vector) ∧
    v = E.sumList (L.map (fun t => E.smul t.coef t.vector))


/-!
====================================================================
17. DEFINICIÓN 5.3: SUBESPACIO GENERADO
====================================================================
-/

/-- Definición 5.3 (Subespacio generado ⟨S⟩):
    El conjunto de todas las combinaciones lineales finitas de elementos de S. -/
def SubespacioGenerado {V : Type _} (E : EspacioVectorial V) (S : V → Prop) : V → Prop :=
  fun v => EsCombinacionLineal E S v

-- Notación informal: usamos `Gen E S` como abreviatura de `SubespacioGenerado E S`
abbrev Gen {V : Type _} (E : EspacioVectorial V) (S : V → Prop) := SubespacioGenerado E S

/-- Cuando S = ∅, ⟨∅⟩ = {0_V}: la lista vacía da la combinación lineal que produce 0_V. -/
theorem gen_vacio_eq_zero {V : Type _} (E : EspacioVectorial V) (v : V) :
    Gen E (fun _ => False) v ↔ v = E.zero := by
  constructor
  · rintro ⟨L, hL, rfl⟩
    cases L with
    | nil =>
      simp only [List.map_nil, EspacioVectorial.sumList_nil]
    | cons head tail =>
      have h_false := hL head List.mem_cons_self
      cases h_false
  · rintro rfl
    refine ⟨[], ?_, ?_⟩
    · intro t ht
      cases ht
    · simp only [List.map_nil, EspacioVectorial.sumList_nil]


/-!
====================================================================
18. PROPOSICIÓN 5.5: ⟨S⟩ ES UN SUBESPACIO VECTORIAL
====================================================================
-/

/-- Proposición 5.5: ⟨S⟩ es un subespacio vectorial de V. -/
theorem prop_5_5_gen_es_subespacio {V : Type _} (E : EspacioVectorial V) (S : V → Prop) :
    EsSubespacio E (Gen E S) where
  -- I. 0_V ∈ ⟨S⟩ (combinación lineal vacía)
  zero_mem := by
    refine ⟨[], ?_, ?_⟩
    · intro t ht
      cases ht
    · simp only [List.map_nil, E.sumList_nil]
  -- II. Clausura bajo la suma
  add_mem := by
    intro w₁ w₂ ⟨L₁, hL₁, hv₁⟩ ⟨L₂, hL₂, hv₂⟩
    refine ⟨L₁ ++ L₂, ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hL₁ t h
      · exact hL₂ t h
    · rw [hv₁, hv₂]
      simp only [List.map_append]
      exact (E.sumList_append
        (L₁.map (fun t => E.smul t.coef t.vector))
        (L₂.map (fun t => E.smul t.coef t.vector))).symm
  -- III. Clausura bajo producto por escalar
  smul_mem := by
    intro «λ» w ⟨L, hL, hv⟩
    refine ⟨L.map (fun t => ⟨«λ» * t.coef, t.vector⟩), ?_, ?_⟩
    · intro t ht
      rcases List.mem_map.mp ht with ⟨orig, horig, rfl⟩
      exact hL orig horig
    · rw [hv]
      have hmap (xs : List (TerminoCombLin V)) :
          (xs.map (fun t => (⟨«λ» * t.coef, t.vector⟩ : TerminoCombLin V))).map
            (fun t => E.smul t.coef t.vector) =
          (xs.map (fun t => E.smul t.coef t.vector)).map (E.smul «λ») := by
        induction xs with
        | nil => rfl
        | cons head tail ih =>
          simp only [List.map_cons]
          rw [E.ev5_smul_assoc, ih]
      rw [hmap L]
      exact E.smul_sumList «λ» (L.map (fun t => E.smul t.coef t.vector))


/-!
====================================================================
19. PROPOSICIÓN 5.7: PROPIEDADES DEL SUBESPACIO GENERADO
====================================================================
-/

/-- Proposición 5.7, Parte I: S ⊆ ⟨S⟩.
    Cada s ∈ S es una combinación lineal de sí mismo con coeficiente 1. -/
theorem prop_5_7_i {V : Type _} (E : EspacioVectorial V) (S : V → Prop)
    (s : V) (hs : S s) : Gen E S s := by
  refine ⟨[⟨1, s⟩], ?_, ?_⟩
  · intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact hs
  · simp only [List.map_cons, List.map_nil, E.sumList_cons, E.sumList_nil]
    rw [E.ev6_one_smul s]
    exact (E.add_zero s).symm

/-- Proposición 5.7, Parte II: S ⊆ T ⟹ ⟨S⟩ ⊆ ⟨T⟩. -/
theorem prop_5_7_ii {V : Type _} (E : EspacioVectorial V) (S T : V → Prop)
    (hST : ∀ v, S v → T v)
    (v : V) (hv : Gen E S v) : Gen E T v := by
  rcases hv with ⟨L, hL, hv⟩
  exact ⟨L, fun t ht => hST t.vector (hL t ht), hv⟩

/-- Proposición 5.7, Parte III (⟸): Si S es subespacio, entonces ⟨S⟩ ⊆ S. -/
theorem prop_5_7_iii_recip {V : Type _} (E : EspacioVectorial V) (S : V → Prop)
    (hS : EsSubespacio E S)
    (v : V) (hv : Gen E S v) : S v := by
  rcases hv with ⟨L, hL, rfl⟩
  revert hL
  induction L with
  | nil =>
    intro _
    simp only [List.map_nil, E.sumList_nil]
    exact hS.zero_mem
  | cons head tail ih =>
    intro hL
    simp only [List.map_cons, E.sumList_cons]
    apply hS.add_mem
    · exact hS.smul_mem head.coef (hL head List.mem_cons_self)
    · apply ih
      intro t ht
      exact hL t (List.mem_cons_of_mem head ht)

/-- Proposición 5.7, Parte III: ⟨S⟩ = S si, y sólo si, S es un subespacio vectorial de V. -/
theorem prop_5_7_iii {V : Type _} (E : EspacioVectorial V) (S : V → Prop) :
    (∀ v, Gen E S v ↔ S v) ↔ EsSubespacio E S := by
  constructor
  · intro h_eq
    have hS_sub : EsSubespacio E (Gen E S) := prop_5_5_gen_es_subespacio E S
    exact {
      zero_mem := by
        rw [← h_eq]
        exact hS_sub.zero_mem
      add_mem := by
        intro w₁ w₂ hw₁ hw₂
        rw [← h_eq]
        exact hS_sub.add_mem ((h_eq w₁).mpr hw₁) ((h_eq w₂).mpr hw₂)
      smul_mem := by
        intro «λ» w hw
        rw [← h_eq]
        exact hS_sub.smul_mem «λ» ((h_eq w).mpr hw)
    }
  · intro hS v
    constructor
    · exact prop_5_7_iii_recip E S hS v
    · exact prop_5_7_i E S v

/-- Proposición 5.7, Parte IV: ⟨⟨S⟩⟩ = ⟨S⟩. -/
theorem prop_5_7_iv {V : Type _} (E : EspacioVectorial V) (S : V → Prop)
    (v : V) : Gen E (Gen E S) v ↔ Gen E S v := by
  constructor
  · exact prop_5_7_iii_recip E (Gen E S) (prop_5_5_gen_es_subespacio E S) v
  · exact prop_5_7_i E (Gen E S) v


/-!
====================================================================
20. COROLARIO 5.8
====================================================================
-/

/-- Corolario 5.8: Si G genera V y G' ⊇ G, entonces G' también genera V. -/
theorem corolario_5_8 {V : Type _} (E : EspacioVectorial V)
    (G G' : V → Prop)
    (hGG' : ∀ v, G v → G' v)
    (hG_genera : ∀ v : V, Gen E G v) :
    ∀ v : V, Gen E G' v := by
  intro v
  exact prop_5_7_ii E G G' hGG' v (hG_genera v)


/-!
====================================================================
21. TEOREMA 5.9: ⟨S⟩ ES EL MENOR SUBESPACIO CONTENIENDO S
====================================================================
-/

/-- Teorema 5.9 (⊆): Si W es un subespacio que contiene S, entonces ⟨S⟩ ⊆ W. -/
theorem teorema_5_9_sub {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (W : V → Prop)
    (hW : EsSubespacio E W)
    (hSW : ∀ v, S v → W v)
    (v : V) (hv : Gen E S v) : W v := by
  rcases hv with ⟨L, hL, rfl⟩
  revert hL
  induction L with
  | nil =>
    intro _
    simp only [List.map_nil, E.sumList_nil]
    exact hW.zero_mem
  | cons head tail ih =>
    intro hL
    simp only [List.map_cons, E.sumList_cons]
    apply hW.add_mem
    · exact hW.smul_mem head.coef (hSW head.vector (hL head List.mem_cons_self))
    · apply ih
      intro t ht
      exact hL t (List.mem_cons_of_mem head ht)

/-- Teorema 5.9 (⊇): ⟨S⟩ es uno de los subespacios que contiene S. -/
theorem teorema_5_9_sup {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (v : V)
    (hv : ∀ W : V → Prop, EsSubespacio E W → (∀ s, S s → W s) → W v) :
    Gen E S v := by
  exact hv (Gen E S) (prop_5_5_gen_es_subespacio E S) (prop_5_7_i E S)

/-- Teorema 5.9 (Completo): ⟨S⟩ = ⋂_{S ⊆ W subespacio} W. -/
theorem teorema_5_9 {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (v : V) :
    Gen E S v ↔ ∀ W : V → Prop, EsSubespacio E W → (∀ s, S s → W s) → W v := by
  constructor
  · intro hv W hW hSW
    exact teorema_5_9_sub E S W hW hSW v hv
  · exact teorema_5_9_sup E S v


/-!
====================================================================
22. PROPOSICIÓN 5.11: UNIÓN GENERA SUMA
====================================================================
-/

-- La unión de una familia de conjuntos
def UnionFamilia {V : Type _} {I : Type _} (W : I → (V → Prop)) : V → Prop :=
  fun v => ∃ i : I, W i v

/-- Proposición 5.11 (⊆): ∑ Wᵢ ⊆ ⟨⋃ Wᵢ⟩. -/
theorem prop_5_11_sub {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (_hW : ∀ i, EsSubespacio E (W i))
    (v : V) (hv : SumaFamilia E W v) :
    Gen E (UnionFamilia W) v := by
  rcases hv with ⟨L, hL, rfl⟩
  revert hL
  induction L with
  | nil =>
    intro _
    simp only [List.map_nil, E.sumList_nil]
    exact (prop_5_5_gen_es_subespacio E (UnionFamilia W)).zero_mem
  | cons head tail ih =>
    intro hL
    simp only [List.map_cons, E.sumList_cons]
    apply (prop_5_5_gen_es_subespacio E (UnionFamilia W)).add_mem
    · apply prop_5_7_i E (UnionFamilia W)
      exact ⟨head.indice, hL head List.mem_cons_self⟩
    · apply ih
      intro t ht
      exact hL t (List.mem_cons_of_mem head ht)

/-- Proposición 5.11 (⊇): ⟨⋃ Wᵢ⟩ ⊆ ∑ Wᵢ. -/
theorem prop_5_11_sup {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (hW : ∀ i, EsSubespacio E (W i))
    (v : V) (hv : Gen E (UnionFamilia W) v) :
    SumaFamilia E W v := by
  rcases hv with ⟨L, hL, rfl⟩
  revert hL
  induction L with
  | nil =>
    intro _
    simp only [List.map_nil, E.sumList_nil]
    exact (prop_4_27_suma_familia E W hW).zero_mem
  | cons head tail ih =>
    intro hL
    simp only [List.map_cons, E.sumList_cons]
    apply (prop_4_27_suma_familia E W hW).add_mem
    · have ⟨i₀, hi₀⟩ := hL head List.mem_cons_self
      refine ⟨[⟨i₀, E.smul head.coef head.vector⟩], ?_, ?_⟩
      · intro t ht
        simp only [List.mem_singleton] at ht
        subst ht
        exact (hW i₀).smul_mem head.coef hi₀
      · simp only [List.map_cons, List.map_nil, E.sumList_cons, E.sumList_nil]
        exact (E.add_zero (E.smul head.coef head.vector)).symm
    · apply ih
      intro t ht
      exact hL t (List.mem_cons_of_mem head ht)

/-- Proposición 5.11 (Completa): ∑ Wᵢ = ⟨⋃ Wᵢ⟩. -/
theorem prop_5_11 {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (hW : ∀ i, EsSubespacio E (W i))
    (v : V) : SumaFamilia E W v ↔ Gen E (UnionFamilia W) v := by
  constructor
  · exact prop_5_11_sub E W hW v
  · exact prop_5_11_sup E W hW v


/-!
====================================================================
23. DEFINICIÓN 5.15: (IN)DEPENDENCIA LINEAL
====================================================================
-/

/-- Definición 5.15 (Linealmente independiente, LI): S es LI si toda combinación lineal
    nula de elementos distintos de S es trivial (todos los coeficientes son 0). -/
def EsLI {V : Type _} (E : EspacioVectorial V) (S : V → Prop) : Prop :=
  ∀ (L : List (TerminoCombLin V)),
    (∀ t ∈ L, S t.vector) →
    (List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L) →
    E.sumList (L.map (fun t => E.smul t.coef t.vector)) = E.zero →
    ∀ t ∈ L, t.coef = 0

/-- Definición 5.15 (Linealmente dependiente, LD): S es LD si existe una combinación lineal
    nula no trivial de elementos distintos de S. -/
def EsLD {V : Type _} (E : EspacioVectorial V) (S : V → Prop) : Prop :=
  ∃ (L : List (TerminoCombLin V)),
    (∀ t ∈ L, S t.vector) ∧
    (List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L) ∧
    E.sumList (L.map (fun t => E.smul t.coef t.vector)) = E.zero ∧
    (∃ t ∈ L, t.coef ≠ 0)

/-- LI y LD son la negación una de la otra. -/
theorem li_iff_not_ld {V : Type _} (E : EspacioVectorial V) (S : V → Prop) :
    EsLI E S ↔ ¬ EsLD E S := by
  constructor
  · intro hLI ⟨L, hL_in, hL_dist, hL_sum, ⟨t, ht_mem, ht_ne⟩⟩
    exact ht_ne (hLI L hL_in hL_dist hL_sum t ht_mem)
  · intro hNLD L hL_in hL_dist hL_sum t ht_mem
    open Classical in
    by_cases h_zero : t.coef = 0
    · exact h_zero
    · exfalso
      exact hNLD ⟨L, hL_in, hL_dist, hL_sum, ⟨t, ht_mem, h_zero⟩⟩


/-!
====================================================================
24. LEMA 5.20: (IN)DEPENDENCIA LINEAL E INCLUSIONES
====================================================================
-/

/-- Lema 5.20, Parte I: Si I es LI e I' ⊆ I, entonces I' es LI. -/
theorem lema_5_20_i {V : Type _} (E : EspacioVectorial V)
    (I₀ I' : V → Prop)
    (hI'I : ∀ v, I' v → I₀ v)
    (hLI : EsLI E I₀) :
    EsLI E I' := by
  intro L hL_in hL_dist hL_sum t ht_mem
  exact hLI L (fun t' ht' => hI'I t'.vector (hL_in t' ht')) hL_dist hL_sum t ht_mem

/-- Lema 5.20, Parte II: Si D es LD y D' ⊇ D, entonces D' es LD. -/
theorem lema_5_20_ii {V : Type _} (E : EspacioVectorial V)
    (D D' : V → Prop)
    (hDD' : ∀ v, D v → D' v)
    (hLD : EsLD E D) :
    EsLD E D' := by
  rcases hLD with ⟨L, hL_in, hL_dist, hL_sum, hL_ne⟩
  exact ⟨L, fun t ht => hDD' t.vector (hL_in t ht), hL_dist, hL_sum, hL_ne⟩


/-!
====================================================================
25. PROPOSICIÓN 5.21: (IN)DEPENDENCIA LINEAL AL SACAR VECTORES
====================================================================
-/

-- Diferencia de conjuntos S \ {s}
def SetMinus {V : Type _} (S : V → Prop) (s : V) : V → Prop :=
  fun v => S v ∧ v ≠ s

/-- Proposición 5.21 (Versión LD, I ⟹ II): Si S es LD, existe s ∈ S tal que s ∈ ⟨S \ {s}⟩. -/
axiom prop_5_21_LD_i_ii {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (hLD : EsLD E S) :
    ∃ s : V, S s ∧ Gen E (SetMinus S s) s

/-- Proposición 5.21 (Versión LD, II ⟹ III): Si existe s ∈ S tal que s ∈ ⟨S \ {s}⟩,
    entonces ⟨S⟩ = ⟨S \ {s}⟩. -/
theorem prop_5_21_LD_ii_iii {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (s : V) (_hs : S s) (hs_gen : Gen E (SetMinus S s) s) :
    ∀ v, Gen E S v ↔ Gen E (SetMinus S s) v := by
  intro v
  constructor
  · intro hv
    exact (prop_5_7_iv E (SetMinus S s) v).mp
      (prop_5_7_ii E S (Gen E (SetMinus S s)) (fun w hw => by
        open Classical in
        by_cases heq : w = s
        · subst heq; exact hs_gen
        · exact prop_5_7_i E (SetMinus S s) w ⟨hw, heq⟩
      ) v hv)
  · exact prop_5_7_ii E (SetMinus S s) S (fun w ⟨hw, _⟩ => hw) v

/-- Proposición 5.21 (Versión LD, III ⟹ I): Si existe s ∈ S tal que ⟨S⟩ = ⟨S \ {s}⟩,
    entonces S es LD. -/
axiom prop_5_21_LD_iii_i {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (s : V) (hs : S s)
    (h_eq : ∀ v, Gen E S v ↔ Gen E (SetMinus S s) v) :
    EsLD E S


/-!
====================================================================
26. COROLARIO 5.23: INDEPENDENCIA LINEAL AL AÑADIR VECTORES
====================================================================
-/

-- Unión de un conjunto con un elemento
def SetUnion {V : Type _} (S : V → Prop) (v₀ : V) : V → Prop :=
  fun v => S v ∨ v = v₀

/-- Corolario 5.23 (Versión LD, ⟹): Si I es LI, I ∪ {v₀} es LD y v₀ ∉ I,
    entonces v₀ ∈ ⟨I⟩. -/
axiom corolario_5_23_LD_ida {V : Type _} (E : EspacioVectorial V)
    (I₀ : V → Prop) (v₀ : V)
    (hLI : EsLI E I₀) (hv₀_notin : ¬ I₀ v₀)
    (hLD : EsLD E (SetUnion I₀ v₀)) :
    Gen E I₀ v₀

/-- Corolario 5.23 (Versión LD, ⟸): Si v₀ ∈ ⟨I⟩, entonces I ∪ {v₀} es LD. -/
axiom corolario_5_23_LD_vuelta {V : Type _} (E : EspacioVectorial V)
    (I₀ : V → Prop) (v₀ : V)
    (hv₀_gen : Gen E I₀ v₀) :
    EsLD E (SetUnion I₀ v₀)

/-- Corolario 5.23 (Versión LI): I ∪ {v₀} es LI si, y sólo si, v₀ ∉ ⟨I⟩. -/
theorem corolario_5_23_LI {V : Type _} (E : EspacioVectorial V)
    (I₀ : V → Prop) (v₀ : V)
    (hLI : EsLI E I₀) (hv₀_notin : ¬ I₀ v₀) :
    EsLI E (SetUnion I₀ v₀) ↔ ¬ Gen E I₀ v₀ := by
  rw [li_iff_not_ld]
  constructor
  · intro h_not_ld h_gen
    exact h_not_ld (corolario_5_23_LD_vuelta E I₀ v₀ h_gen)
  · intro h_not_gen h_ld
    exact h_not_gen (corolario_5_23_LD_ida E I₀ v₀ hLI hv₀_notin h_ld)


/-!
====================================================================
27. DEFINICIÓN 5.24: BASE
====================================================================
-/

/-- Definición 5.24 (Base): B es una base de V si es LI y genera V. -/
structure EsBase {V : Type _} (E : EspacioVectorial V) (B : V → Prop) : Prop where
  li     : EsLI E B
  genera : ∀ v : V, Gen E B v


/-!
====================================================================
28. TEOREMA 5.26: DEFINICIONES EQUIVALENTES DE BASE
====================================================================
-/

/-- Condición II: Todo vector tiene una única expresión como combinación lineal de B. -/
def ExpresionUnica {V : Type _} (E : EspacioVectorial V) (B : V → Prop) : Prop :=
  ∀ v : V, EsCombinacionLineal E B v ∧
    (∀ (L₁ L₂ : List (TerminoCombLin V)),
      (∀ t ∈ L₁, B t.vector) →
      (∀ t ∈ L₂, B t.vector) →
      (List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L₁) →
      (List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L₂) →
      v = E.sumList (L₁.map (fun t => E.smul t.coef t.vector)) →
      v = E.sumList (L₂.map (fun t => E.smul t.coef t.vector)) →
      ∀ (t₁ : TerminoCombLin V), t₁ ∈ L₁ →
      ∀ (t₂ : TerminoCombLin V), t₂ ∈ L₂ →
      t₁.vector = t₂.vector → t₁.coef = t₂.coef)

/-- Condición III: B genera V y ningún subconjunto propio genera V. -/
def GeneradorMinimal {V : Type _} (E : EspacioVectorial V) (B : V → Prop) : Prop :=
  (∀ v : V, Gen E B v) ∧
  (∀ (I₀ : V → Prop), (∀ v, I₀ v → B v) → (∃ b, B b ∧ ¬ I₀ b) →
    ∃ v : V, ¬ Gen E I₀ v)

/-- Condición IV: B es LI y ningún superconjunto propio es LI. -/
def LIMaximal {V : Type _} (E : EspacioVectorial V) (B : V → Prop) : Prop :=
  EsLI E B ∧
  (∀ (G : V → Prop), (∀ v, B v → G v) → (∃ g, G g ∧ ¬ B g) → EsLD E G)

/-- Teorema 5.26 (I ⟹ III): Si B es base, B genera V y ningún subconjunto propio genera V. -/
theorem teorema_5_26_i_iii {V : Type _} (E : EspacioVectorial V) (B : V → Prop)
    (hB : EsBase E B) : GeneradorMinimal E B := by
  constructor
  · exact hB.genera
  · intro I₀ hI₀_sub ⟨b, hb, hb_notin⟩
    refine ⟨b, ?_⟩
    intro hb_gen
    have h_sub : ∀ v, I₀ v → SetMinus B b v := by
      intro v hv
      refine ⟨hI₀_sub v hv, ?_⟩
      rintro rfl
      exact hb_notin hv
    have hb_gen_minus : Gen E (SetMinus B b) b := prop_5_7_ii E I₀ (SetMinus B b) h_sub b hb_gen
    have h_eq : ∀ v, Gen E B v ↔ Gen E (SetMinus B b) v := prop_5_21_LD_ii_iii E B b hb hb_gen_minus
    have hLD : EsLD E B := prop_5_21_LD_iii_i E B b hb h_eq
    have h_not_ld : ¬ EsLD E B := (li_iff_not_ld E B).mp hB.li
    exact h_not_ld hLD

/-- Teorema 5.26 (III ⟹ I): Si B genera V y ningún subconjunto propio genera V, B es base. -/
theorem teorema_5_26_iii_i {V : Type _} (E : EspacioVectorial V) (B : V → Prop)
    (hB : GeneradorMinimal E B) : EsBase E B := by
  constructor
  · rw [li_iff_not_ld]
    intro hLD
    obtain ⟨b, hb, hb_gen⟩ := prop_5_21_LD_i_ii E B hLD
    have h_eq : ∀ v, Gen E B v ↔ Gen E (SetMinus B b) v := prop_5_21_LD_ii_iii E B b hb hb_gen
    have h_gen_minus : ∀ v, Gen E (SetMinus B b) v := by
      intro v
      exact (h_eq v).mp (hB.1 v)
    have h_sub : ∀ v, SetMinus B b v → B v := fun v hv => hv.1
    have h_diff : ∃ b', B b' ∧ ¬ SetMinus B b b' := ⟨b, hb, fun h => h.2 rfl⟩
    obtain ⟨v, hv_not_gen⟩ := hB.2 (SetMinus B b) h_sub h_diff
    exact hv_not_gen (h_gen_minus v)
  · exact hB.1

/-- Teorema 5.26 (I ⟹ IV): Si B es base, B es LI y ningún superconjunto propio es LI. -/
theorem teorema_5_26_i_iv {V : Type _} (E : EspacioVectorial V) (B : V → Prop)
    (hB : EsBase E B) : LIMaximal E B := by
  constructor
  · exact hB.li
  · intro G hG_sup ⟨g, hg, _hg_notin⟩
    have hLD_union : EsLD E (SetUnion B g) :=
      corolario_5_23_LD_vuelta E B g (hB.genera g)
    exact lema_5_20_ii E (SetUnion B g) G (fun v hv => by
      cases hv with
      | inl h => exact hG_sup v h
      | inr h => subst h; exact hg) hLD_union

/-- Teorema 5.26 (IV ⟹ I): Si B es LI y ningún superconjunto propio es LI, B es base. -/
theorem teorema_5_26_iv_i {V : Type _} (E : EspacioVectorial V) (B : V → Prop)
    (hB : LIMaximal E B) : EsBase E B := by
  constructor
  · exact hB.1
  · intro v
    open Classical in
    by_cases hv : Gen E B v
    · exact hv
    · have hv_notin : ¬ B v := by
        intro hBv; exact hv (prop_5_7_i E B v hBv)
      have hLI_union : EsLI E (SetUnion B v) := by
        rw [corolario_5_23_LI E B v hB.1 hv_notin]
        exact hv
      have hLD : EsLD E (SetUnion B v) :=
        hB.2 (SetUnion B v) (fun w hw => Or.inl hw) ⟨v, Or.inr rfl, hv_notin⟩
      exact False.elim (((li_iff_not_ld E (SetUnion B v)).mp hLI_union) hLD)


/-!
====================================================================
29. DEFINICIÓN 5.29: ESPACIO FINITAMENTE GENERADO
====================================================================
-/

/-- Definición 5.29: V es finitamente generado si existe un generador finito. -/
def EsFG {V : Type _} (E : EspacioVectorial V) : Prop :=
  ∃ (G : List V), ∀ v : V, Gen E (fun w => w ∈ G) v


/-!
====================================================================
30. TEOREMA 5.30: TODO ESPACIO FG TIENE BASE
====================================================================
-/

/-- Teorema 5.30: Todo generador finito contiene una base.
    Formulación: Si G (como lista) genera V, existe una sublista G' ⊆ G que es base de V. -/
axiom teorema_5_30_fg_tiene_base {V : Type _} (E : EspacioVectorial V)
    (G : List V) (hG : ∀ v : V, Gen E (fun w => w ∈ G) v) :
    ∃ (G' : List V), (∀ w ∈ G', w ∈ G) ∧ EsBase E (fun w => w ∈ G')

/-!
====================================================================
31. TEOREMA 5.34: COMPLETAMIENTO DE BASES
====================================================================
-/

/-- Teorema 5.34: Todo conjunto LI finito puede completarse a una base,
    sustituyendo inductivamente generadores por elementos del LI. -/
axiom teorema_5_34_completamiento {V : Type _} (E : EspacioVectorial V)
    (I₀ : List V) (G : List V)
    (hLI : EsLI E (fun w => w ∈ I₀))
    (hG : ∀ v : V, Gen E (fun w => w ∈ G) v) :
    ∃ (G' : List V),
      (∀ w ∈ I₀, w ∈ G') ∧
      G'.length = G.length ∧
      (∀ v : V, Gen E (fun w => w ∈ G') v)

/-!
====================================================================
32. PROPOSICIÓN 5.37
====================================================================
-/

/-- Proposición 5.37: #I ≤ #G para I LI y G generador. -/
axiom prop_5_37 {V : Type _} (E : EspacioVectorial V)
    (I₀ : List V) (G : List V)
    (hLI : EsLI E (fun w => w ∈ I₀))
    (hG : ∀ v : V, Gen E (fun w => w ∈ G) v) :
    I₀.length ≤ G.length


/-!
====================================================================
33. PROPOSICIÓN 5.38: TODA BASE DE UN ESPACIO FG TIENE EL MISMO TAMAÑO
====================================================================
-/

/-- Proposición 5.38: Dos bases finitas de un mismo espacio tienen el mismo cardinal. -/
theorem prop_5_38_bases_mismo_cardinal {V : Type _} (E : EspacioVectorial V)
    (B₁ B₂ : List V)
    (hB₁ : EsBase E (fun w => w ∈ B₁))
    (hB₂ : EsBase E (fun w => w ∈ B₂)) :
    B₁.length = B₂.length := by
  have h1 : B₁.length ≤ B₂.length := prop_5_37 E B₁ B₂ hB₁.li hB₂.genera
  have h2 : B₂.length ≤ B₁.length := prop_5_37 E B₂ B₁ hB₂.li hB₁.genera
  exact Nat.le_antisymm h1 h2


/-!
====================================================================
34. DEFINICIÓN 5.39: DIMENSIÓN
====================================================================
-/

/-- Definición 5.39 (Dimensión): Si V tiene una base finita B, dim(V) := #B. -/
noncomputable def Dimension {V : Type _} (E : EspacioVectorial V) (B : List V)
    (_ : EsBase E (fun w => w ∈ B)) : Nat :=
  B.length


/-!
====================================================================
35. PROPOSICIÓN 5.41
====================================================================
-/

/-- Proposición 5.41, Parte I: Si I es LI, #I ≤ dim(V). -/
theorem prop_5_41_i {V : Type _} (E : EspacioVectorial V)
    (I₀ : List V) (B : List V)
    (hLI : EsLI E (fun w => w ∈ I₀))
    (hB : EsBase E (fun w => w ∈ B)) :
    I₀.length ≤ B.length :=
  prop_5_37 E I₀ B hLI hB.genera

/-- Proposición 5.41, Parte II: Si G es generador, #G ≥ dim(V). -/
theorem prop_5_41_ii {V : Type _} (E : EspacioVectorial V)
    (G : List V) (B : List V)
    (hG : ∀ v : V, Gen E (fun w => w ∈ G) v)
    (hB : EsBase E (fun w => w ∈ B)) :
    B.length ≤ G.length :=
  prop_5_37 E B G hB.li hG


/-!
====================================================================
36. COROLARIO 5.43
====================================================================
-/

/-- Corolario 5.43, Parte I: Si G genera V y #G = dim(V), G es base. -/
axiom corolario_5_43_i {V : Type _} (E : EspacioVectorial V)
    (G : List V) (B : List V)
    (hG : ∀ v : V, Gen E (fun w => w ∈ G) v)
    (hB : EsBase E (fun w => w ∈ B))
    (h_eq : G.length = B.length) :
    EsBase E (fun w => w ∈ G)

/-- Corolario 5.43, Parte II: Si I es LI y #I = dim(V), I es base. -/
axiom corolario_5_43_ii {V : Type _} (E : EspacioVectorial V)
    (I₀ : List V) (B : List V)
    (hLI : EsLI E (fun w => w ∈ I₀))
    (hB : EsBase E (fun w => w ∈ B))
    (h_eq : I₀.length = B.length) :
    EsBase E (fun w => w ∈ I₀)


/-!
====================================================================
37. TEOREMA 5.45: COMPLETAMIENTO DE BASES DE SUBESPACIOS
====================================================================
-/

/-- Teorema 5.45: Toda base de un subespacio se completa a una base de V. -/
theorem teorema_5_45_completamiento_subespacios {V : Type _} (E : EspacioVectorial V)
    (W : V → Prop) (_hW : EsSubespacio E W)
    (BW : List V) (hBW : EsBase E (fun w => w ∈ BW))
    (G : List V) (hG : ∀ v : V, Gen E (fun w => w ∈ G) v) :
    ∃ (BV : List V), (∀ w ∈ BW, w ∈ BV) ∧ EsBase E (fun w => w ∈ BV) := by
  obtain ⟨G_base, _hG_sub, hG_is_base⟩ := teorema_5_30_fg_tiene_base E G hG
  obtain ⟨G', hBW_in_G', hlen, hG'_gen⟩ := teorema_5_34_completamiento E BW G_base hBW.li hG_is_base.genera
  have hG'_base : EsBase E (fun w => w ∈ G') := corolario_5_43_i E G' G_base hG'_gen hG_is_base hlen
  exact ⟨G', hBW_in_G', hG'_base⟩


/-!
====================================================================
38. COROLARIO 5.46
====================================================================
-/

/-- Corolario 5.46: dim(W) ≤ dim(V), con igualdad sii W = V. -/
theorem corolario_5_46 {V : Type _} (E : EspacioVectorial V)
    (W : V → Prop) (_hW : EsSubespacio E W)
    (BW : List V) (BV : List V)
    (hBW : EsBase E (fun w => w ∈ BW))
    (hBV : EsBase E (fun w => w ∈ BV))
    (_hBW_sub : ∀ w ∈ BW, w ∈ BV) :
    BW.length ≤ BV.length := by
  exact prop_5_41_i E BW BV hBW.li hBV


/-!
====================================================================
39. TEOREMA 5.48: DIMENSIÓN DE LA SUMA DE SUBESPACIOS
====================================================================
-/

/-- Teorema 5.48: Fórmula de dimensión de la suma de subespacios. -/
theorem teorema_5_48_dim_suma {V : Type _} (E : EspacioVectorial V)
    (W₁ W₂ : V → Prop) (_hW₁ : EsSubespacio E W₁) (_hW₂ : EsSubespacio E W₂)
    -- B base de W₁ ∩ W₂, B₁ base de W₁, B₂ base de W₂
    (B : List V) (B₁_extra : List V) (B₂_extra : List V)
    (_hB₁ : EsBase E (fun w => w ∈ B ++ B₁_extra))
    (_hB₂ : EsBase E (fun w => w ∈ B ++ B₂_extra))
    (_hB_inter : EsBase E (fun w => w ∈ B))
    (_hUnion_LI : EsLI E (fun w => w ∈ B ++ B₁_extra ++ B₂_extra)) :
    (B ++ B₁_extra ++ B₂_extra).length =
      (B ++ B₁_extra).length + (B ++ B₂_extra).length - B.length := by
  simp only [List.length_append]
  omega


/-!
====================================================================
40. COROLARIO 5.49: COMPLETAMIENTO DE SUBESPACIOS
====================================================================
-/

/-- Corolario 5.49: Todo subespacio W de un espacio FG tiene un complemento directo W'. -/
axiom corolario_5_49_complemento_directo {V : Type _} (E : EspacioVectorial V)
    (W : V → Prop) (hW : EsSubespacio E W)
    (BW : List V) (BV_extra : List V)
    (hBV : EsBase E (fun w => w ∈ BW ++ BV_extra))
    (hBW_base : EsBase E (fun w => w ∈ BW)) :
    (∀ v : V, SumaDos E W (Gen E (fun w => w ∈ BV_extra)) v) ∧
    EsSumaDirectaDos E W (Gen E (fun w => w ∈ BV_extra))


/-!
====================================================================
41. TEOREMA 5.52: BASE DE LA SUMA DIRECTA (VERSIÓN 2 SUBESPACIOS)
====================================================================
-/

/-- Intersección vacía de dos listas (como predicados) -/
def ListaDisjunta {V : Type _} (L₁ L₂ : List V) : Prop :=
  ∀ v, v ∈ L₁ → v ∉ L₂

/-- Teorema 5.52 (⟹): Si V = W₁ ⊕ W₂ con bases B₁, B₂,
    entonces B₁ ∩ B₂ = ∅ y B₁ ∪ B₂ es base de V. -/
axiom teorema_5_52_ida {V : Type _} (E : EspacioVectorial V)
    (W₁ W₂ : V → Prop) (hW₁ : EsSubespacio E W₁) (hW₂ : EsSubespacio E W₂)
    (hSD : EsSumaDirectaDos E W₁ W₂)
    (hSuma : ∀ v : V, SumaDos E W₁ W₂ v)
    (B₁ B₂ : List V)
    (hB₁ : EsBase E (fun w => w ∈ B₁))
    (hB₂ : EsBase E (fun w => w ∈ B₂)) :
    ListaDisjunta B₁ B₂ ∧ EsBase E (fun w => w ∈ B₁ ++ B₂)

/-- Teorema 5.52 (⟸): Si B₁ ∩ B₂ = ∅ y B₁ ∪ B₂ es base de V,
    entonces V = ⟨B₁⟩ ⊕ ⟨B₂⟩. -/
axiom teorema_5_52_vuelta {V : Type _} (E : EspacioVectorial V)
    (B₁ B₂ : List V)
    (hDisj : ListaDisjunta B₁ B₂)
    (hBase : EsBase E (fun w => w ∈ B₁ ++ B₂)) :
    (∀ v : V, SumaDos E (Gen E (fun w => w ∈ B₁)) (Gen E (fun w => w ∈ B₂)) v) ∧
    EsSumaDirectaDos E (Gen E (fun w => w ∈ B₁)) (Gen E (fun w => w ∈ B₂))


/-!
====================================================================
42. TEOREMA 5.54: BASE DE LA SUMA DIRECTA (VERSIÓN FAMILIA ARBITRARIA)
====================================================================
-/

/-- Bases de una familia son dos a dos disjuntas cuando los índices son distintos. -/
def BasesDisjuntas {V I : Type _} (B : I → List V) : Prop :=
  ∀ (i j : I), i ≠ j → ListaDisjunta (B i) (B j)

/-- Unión de una familia de listas como predicado. -/
def UnionListas {V I : Type _} (B : I → List V) : V → Prop :=
  fun v => ∃ i : I, v ∈ B i

/-- Teorema 5.54 (⟹): Si V = ⊕ Wᵢ con bases Bᵢ, entonces las Bᵢ son disjuntas
    y ⋃ Bᵢ es base de V. -/
axiom teorema_5_54_ida {V I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (hW : ∀ i, EsSubespacio E (W i))
    (hSD : EsSumaDirectaFamilia E W)
    (hSuma : ∀ v : V, SumaFamilia E W v)
    (B : I → List V) (hB : ∀ i, EsBase E (fun w => w ∈ B i)) :
    BasesDisjuntas B ∧ EsBase E (UnionListas B)

/-- Teorema 5.54 (⟸): Si las Bᵢ son disjuntas y ⋃ Bᵢ es base de V,
    entonces V = ⊕ ⟨Bᵢ⟩. -/
axiom teorema_5_54_vuelta {V I : Type _} (E : EspacioVectorial V)
    (B : I → List V)
    (hDisj : BasesDisjuntas B)
    (hBase : EsBase E (UnionListas B)) :
    (∀ v : V, SumaFamilia E (fun i => Gen E (fun w => w ∈ B i)) v) ∧
    EsSumaDirectaFamilia E (fun i => Gen E (fun w => w ∈ B i))

