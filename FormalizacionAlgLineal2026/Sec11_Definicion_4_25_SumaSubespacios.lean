import FormalizacionAlgLineal2026.Sec10_Observacion_4_22_Ejemplo_4_24_UnionSubespacios

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


