import FormalizacionAlgLineal2026.Sec16_Definicion_5_1_CombinacionLineal

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


