import FormalizacionAlgLineal2026.Capitulo4.Sec06_Proposicion_4_5_PropiedadesAritmeticas
import FormalizacionAlgLineal2026.Capitulo5.Sec16_Definicion_5_1_CombinacionLineal
import FormalizacionAlgLineal2026.Capitulo5.Sec17_Definicion_5_3_SubespacioGenerado
import FormalizacionAlgLineal2026.Capitulo5.Sec23_Definicion_5_15_IndependenciaLineal

/-!
====================================================================
LEMAS AUXILIARES: SUMLIST, TERMINOCOMBLIN Y DESPEJE ESCALAR
====================================================================

Este archivo formaliza los lemas algebraicos y combinatorios fundamentales
sobre listas de combinaciones lineales (`sumList`, `TerminoCombLin`), necesarios
para la manipulación de combinaciones lineales finitas en ℝ-espacios vectoriales
de forma autónoma (sin Mathlib).

En particular, cubre los 4 requerimientos principales:
1. Reordenamiento / extracción de un elemento `t ∈ L` en `sumList`.
2. Lema de despeje escalar (`c · v + w = 0 ∧ c ≠ 0 ⟹ v = (-c⁻¹) · w`).
3. Distributividad de un escalar sobre combinaciones lineales mapeadas.
4. Preservación de desigualdad de vectores en la lista restante bajo `Pairwise`.
-/

/-!
--------------------------------------------------------------------
1. PROPIEDADES ARITMÉTICAS AUXILIARES DE ℝ
--------------------------------------------------------------------
Deducidas estrictamente a partir de `AxiomasReales.lean`.
-/

/-- Neutro aditivo por izquierda en ℝ: `0 + a = a`. -/
theorem zero_add_R (a : ℝ) : 0 + a = a := by
  rw [add_comm, add_zero]

/-- Opuesto aditivo por izquierda en ℝ: `-a + a = 0`. -/
theorem neg_add_cancel_R (a : ℝ) : -a + a = 0 := by
  rw [add_comm, add_neg_cancel]

/-- Ley de cancelación aditiva por izquierda en ℝ. -/
theorem add_cancel_left_R (a b c : ℝ) (h : a + b = a + c) : b = c := by
  calc
    b = 0 + b        := (zero_add_R b).symm
    _ = (-a + a) + b := by rw [neg_add_cancel_R]
    _ = -a + (a + b) := add_assoc (-a) a b
    _ = -a + (a + c) := by rw [h]
    _ = (-a + a) + c := (add_assoc (-a) a c).symm
    _ = 0 + c        := by rw [neg_add_cancel_R]
    _ = c            := zero_add_R c

/-- Producto por cero por izquierda en ℝ: `0 * a = 0`. -/
theorem zero_mul_R (a : ℝ) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    calc
      0 * a + 0 * a = (0 + 0) * a := (add_mul 0 0 a).symm
      _             = 0 * a       := by rw [add_zero]
      _             = 0 * a + 0   := (add_zero (0 * a)).symm
  exact add_cancel_left_R (0 * a) (0 * a) 0 h

/-- Unicidad del opuesto aditivo en ℝ: si `a + b = 0`, entonces `b = -a`. -/
theorem neg_unique_R (a b : ℝ) (h : a + b = 0) : b = -a := by
  calc
    b = 0 + b        := (zero_add_R b).symm
    _ = (-a + a) + b := by rw [neg_add_cancel_R]
    _ = -a + (a + b) := add_assoc (-a) a b
    _ = -a + 0       := by rw [h]
    _ = -a           := add_zero (-a)

/-- Producto de un opuesto en ℝ: `(-a) * b = -(a * b)`. -/
theorem neg_mul_R (a b : ℝ) : (-a) * b = -(a * b) := by
  apply neg_unique_R (a * b)
  calc
    a * b + (-a) * b = (a + -a) * b := (add_mul a (-a) b).symm
    _                = 0 * b        := by rw [add_neg_cancel]
    _                = 0            := zero_mul_R b

/-- Inverso escalar con signo opuesto: `(-c⁻¹) * c = -1` cuando `c ≠ 0`. -/
theorem neg_inv_mul_cancel_R {c : ℝ} (hc : c ≠ 0) : (-c⁻¹) * c = -1 := by
  calc
    (-c⁻¹) * c = -(c⁻¹ * c) := neg_mul_R (c⁻¹) c
    _          = -1         := by rw [inv_mul_cancel₀ hc]

/-!
--------------------------------------------------------------------
2. REQUERIMIENTO 2: LEMA DE DESPEJE ESCALAR
--------------------------------------------------------------------
Si `E.add (E.smul c v) w = E.zero` con `c ≠ 0`, entonces `v = E.smul (-c⁻¹) w`.
-/

/-- Requerimiento 2: Lema de despeje escalar.
    Si `c · v + w = 0` con `c ≠ 0`, entonces `v = (-c⁻¹) · w`. -/
theorem despeje_escalar {V : Type _} (E : EspacioVectorial V)
    (c : ℝ) (v w : V) (hc : c ≠ 0)
    (h : E.add (E.smul c v) w = E.zero) :
    v = E.smul (-c⁻¹) w := by
  have h1 : E.smul (-c⁻¹) (E.add (E.smul c v) w) = E.zero := by
    rw [h, prop_4_5_iii E (-c⁻¹)]
  rw [E.ev7_smul_add, ← E.ev5_smul_assoc, neg_inv_mul_cancel_R hc, prop_4_5_ii] at h1
  have h2 : E.add v (E.add (E.neg v) (E.smul (-c⁻¹) w)) = E.add v E.zero := by
    rw [h1]
  rw [← E.ev1_add_assoc, E.add_neg, E.zero_add, E.add_zero] at h2
  exact h2.symm

/-- Variante con conmutación de sumandos: `w + c · v = 0 ∧ c ≠ 0 ⟹ v = (-c⁻¹) · w`. -/
theorem despeje_escalar_comm {V : Type _} (E : EspacioVectorial V)
    (c : ℝ) (v w : V) (hc : c ≠ 0)
    (h : E.add w (E.smul c v) = E.zero) :
    v = E.smul (-c⁻¹) w := by
  apply despeje_escalar E c v w hc
  rw [E.ev2_add_comm]
  exact h

/-!
--------------------------------------------------------------------
3. REQUERIMIENTO 3: DISTRIBUTIVIDAD DE ESCALAR SOBRE SUMLIST MAP
--------------------------------------------------------------------
`E.smul k (E.sumList (L.map (fun t => E.smul t.coef t.vector))) =
   E.sumList (L.map (fun t => E.smul (k * t.coef) t.vector))`
-/

/-- Requerimiento 3: Distributividad de un escalar `k` sobre una combinación lineal mapeada. -/
theorem smul_sumList_map_smul {V : Type _} (E : EspacioVectorial V)
    (k : ℝ) (L : List (TerminoCombLin V)) :
    E.smul k (E.sumList (L.map (fun t => E.smul t.coef t.vector))) =
      E.sumList (L.map (fun t => E.smul (k * t.coef) t.vector)) := by
  induction L with
  | nil =>
    simp only [List.map_nil, EspacioVectorial.sumList_nil]
    exact prop_4_5_iii E k
  | cons t ts ih =>
    simp only [List.map_cons, EspacioVectorial.sumList_cons]
    rw [E.ev7_smul_add, ← E.ev5_smul_assoc, ih]

/-- Operación que escala los coeficientes de una lista de `TerminoCombLin`. -/
noncomputable def smulTerminos {V : Type _} (c : ℝ) (L : List (TerminoCombLin V)) : List (TerminoCombLin V) :=
  L.map (fun t => ⟨c * t.coef, t.vector⟩)

/-- Los vectores de `smulTerminos c L` son exactamente los vectores originales de `L`. -/
theorem smulTerminos_vector {V : Type _} (c : ℝ) (L : List (TerminoCombLin V)) (u : TerminoCombLin V)
    (hu : u ∈ smulTerminos c L) : ∃ t ∈ L, u.vector = t.vector := by
  rcases List.mem_map.mp hu with ⟨t, ht, rfl⟩
  exact ⟨t, ht, rfl⟩

/-- La combinación lineal de `smulTerminos c L` coincide con escalar por `c` la de `L`. -/
theorem sumList_smulTerminos {V : Type _} (E : EspacioVectorial V)
    (c : ℝ) (L : List (TerminoCombLin V)) :
    E.sumList ((smulTerminos c L).map (fun t => E.smul t.coef t.vector)) =
      E.smul c (E.sumList (L.map (fun t => E.smul t.coef t.vector))) := by
  dsimp [smulTerminos]
  rw [List.map_map]
  exact (smul_sumList_map_smul E c L).symm

/-!
--------------------------------------------------------------------
4. REQUERIMIENTO 1: DESCOMPOSICIÓN Y REORDENAMIENTO DE SUMLIST
--------------------------------------------------------------------
Si `t ∈ L`, la lista se puede descomponer o reordenar tal que:
`sumList (L.map ...) = E.add (E.smul t.coef t.vector) (sumList (L'.map ...))`
donde `L'` es `L` sin el elemento `t`.
-/

/-- Extraer un elemento intermedio en `sumList` equivale a sumarlo por izquierda
    a la concatenación de las partes restantes (asociatividad y conmutatividad). -/
theorem sumList_split {V : Type _} (E : EspacioVectorial V)
    (xs ys : List V) (x : V) :
    E.sumList (xs ++ x :: ys) = E.add x (E.sumList (xs ++ ys)) := by
  rw [EspacioVectorial.sumList_append, EspacioVectorial.sumList_cons,
      EspacioVectorial.sumList_append]
  calc
    E.add (E.sumList xs) (E.add x (E.sumList ys))
      = E.add (E.add (E.sumList xs) x) (E.sumList ys) := (E.ev1_add_assoc (E.sumList xs) x (E.sumList ys)).symm
    _ = E.add (E.add x (E.sumList xs)) (E.sumList ys) := by rw [E.ev2_add_comm (E.sumList xs) x]
    _ = E.add x (E.add (E.sumList xs) (E.sumList ys)) := E.ev1_add_assoc x (E.sumList xs) (E.sumList ys)

/-- Versión mapeada general de `sumList_split` para cualquier función `f : α → V`. -/
theorem sumList_map_split {V α : Type _} (E : EspacioVectorial V)
    (f : α → V) (xs ys : List α) (x : α) :
    E.sumList ((xs ++ x :: ys).map f) = E.add (f x) (E.sumList ((xs ++ ys).map f)) := by
  simp only [List.map_append, List.map_cons]
  exact sumList_split E (xs.map f) (ys.map f) (f x)

/-- Descomposición de la suma de términos con partición explícita `L₁ ++ t :: L₂`. -/
theorem sumList_map_termino_split {V : Type _} (E : EspacioVectorial V)
    (L₁ L₂ : List (TerminoCombLin V)) (t : TerminoCombLin V) :
    E.sumList ((L₁ ++ t :: L₂).map (fun x => E.smul x.coef x.vector)) =
      E.add (E.smul t.coef t.vector)
        (E.sumList ((L₁ ++ L₂).map (fun x => E.smul x.coef x.vector))) :=
  sumList_map_split E (fun x => E.smul x.coef x.vector) L₁ L₂ t

/-- Lema de pertenencia: cualquier elemento de la lista restante `L₁ ++ L₂` pertenecía a `L₁ ++ t :: L₂`. -/
theorem mem_of_mem_split {α : Type _} (L₁ L₂ : List α) (t : α)
    (x : α) (hx : x ∈ L₁ ++ L₂) : x ∈ L₁ ++ t :: L₂ := by
  rw [List.mem_append] at hx ⊢
  rcases hx with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (List.mem_cons_of_mem t h2)

/-- Requerimiento 1 (Formulación con partición explícita `L₁ ++ L₂`):
    Si `t ∈ L`, existen `L₁` y `L₂` tales que `L = L₁ ++ t :: L₂` y
    la suma se descompone con el término de `t` al frente y `L₁ ++ L₂` en la suma restante. -/
theorem sumList_map_termino_mem_split {V : Type _} (E : EspacioVectorial V)
    (L : List (TerminoCombLin V)) (t : TerminoCombLin V) (ht : t ∈ L) :
    ∃ (L₁ L₂ : List (TerminoCombLin V)),
      L = L₁ ++ t :: L₂ ∧
      E.sumList (L.map (fun x => E.smul x.coef x.vector)) =
        E.add (E.smul t.coef t.vector)
          (E.sumList ((L₁ ++ L₂).map (fun x => E.smul x.coef x.vector))) := by
  rcases List.mem_iff_append.mp ht with ⟨L₁, L₂, rfl⟩
  refine ⟨L₁, L₂, rfl, ?_⟩
  exact sumList_map_termino_split E L₁ L₂ t

/-- Requerimiento 1 (Formulación con lista restante `L'`):
    Si `t ∈ L`, existe `L'` (formada por los elementos de `L` salvo `t`) tal que:
    `sumList (L.map ...) = E.add (E.smul t.coef t.vector) (sumList (L'.map ...))`. -/
theorem sumList_map_termino_mem_remove {V : Type _} (E : EspacioVectorial V)
    (L : List (TerminoCombLin V)) (t : TerminoCombLin V) (ht : t ∈ L) :
    ∃ (L' : List (TerminoCombLin V)),
      (∀ x ∈ L', x ∈ L) ∧
      E.sumList (L.map (fun x => E.smul x.coef x.vector)) =
        E.add (E.smul t.coef t.vector)
          (E.sumList (L'.map (fun x => E.smul x.coef x.vector))) := by
  rcases sumList_map_termino_mem_split E L t ht with ⟨L₁, L₂, rfl, h_sum⟩
  refine ⟨L₁ ++ L₂, fun x hx => mem_of_mem_split L₁ L₂ t x hx, h_sum⟩

/-!
--------------------------------------------------------------------
5. REQUERIMIENTO 4: PAIRWISE Y VECTORES DISTINTOS EN LA LISTA RESTANTE
--------------------------------------------------------------------
Si `List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L` y `t ∈ L`,
entonces ningún vector en la lista restante es igual a `t.vector`.
-/

/-- Requerimiento 4: Si `L₁ ++ t :: L₂` tiene vectores distintos dos a dos,
    ningún término en `L₁ ++ L₂` tiene vector igual a `t.vector`. -/
theorem pairwise_vector_ne_of_split {V : Type _}
    (L₁ L₂ : List (TerminoCombLin V)) (t : TerminoCombLin V)
    (h_pw : List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) (L₁ ++ t :: L₂)) :
    ∀ x ∈ L₁ ++ L₂, x.vector ≠ t.vector := by
  intro x hx
  rw [List.mem_append] at hx
  rw [List.pairwise_append] at h_pw
  rcases h_pw with ⟨_, h_cons, h_cross⟩
  cases h_cons with
  | cons h_head _ =>
    rcases hx with hx1 | hx2
    · exact h_cross x hx1 t List.mem_cons_self
    · exact fun h_eq => h_head x hx2 h_eq.symm

/-- Variante con igualdad explícita `L = L₁ ++ t :: L₂`. -/
theorem pairwise_vector_ne_of_mem_split {V : Type _}
    {L L₁ L₂ : List (TerminoCombLin V)} {t : TerminoCombLin V}
    (h_decomp : L = L₁ ++ t :: L₂)
    (h_pw : List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L) :
    ∀ x ∈ L₁ ++ L₂, x.vector ≠ t.vector := by
  subst h_decomp
  exact pairwise_vector_ne_of_split L₁ L₂ t h_pw

/-- Teorema unificado (Requerimientos 1 y 4 integrados):
    Dada una combinación lineal `L` de elementos distintos con `t ∈ L`,
    se extrae `t` obteniendo `L'` tal que:
    1. Todo elemento de `L'` pertenece a `L` (`∀ x ∈ L', x ∈ L`).
    2. Ningún elemento de `L'` repite el vector de `t` (`∀ x ∈ L', x.vector ≠ t.vector`).
    3. La suma se factoriza como `E.add (t...) (sumList L'...)`. -/
theorem combLin_descomposicion_elemento {V : Type _} (E : EspacioVectorial V)
    (L : List (TerminoCombLin V)) (t : TerminoCombLin V) (ht : t ∈ L)
    (h_pw : List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L) :
    ∃ (L' : List (TerminoCombLin V)),
      (∀ x ∈ L', x ∈ L) ∧
      (∀ x ∈ L', x.vector ≠ t.vector) ∧
      E.sumList (L.map (fun x => E.smul x.coef x.vector)) =
        E.add (E.smul t.coef t.vector)
          (E.sumList (L'.map (fun x => E.smul x.coef x.vector))) := by
  rcases sumList_map_termino_mem_split E L t ht with ⟨L₁, L₂, rfl, h_sum⟩
  refine ⟨L₁ ++ L₂, fun x hx => mem_of_mem_split L₁ L₂ t x hx, ?_, h_sum⟩
  exact pairwise_vector_ne_of_split L₁ L₂ t h_pw
