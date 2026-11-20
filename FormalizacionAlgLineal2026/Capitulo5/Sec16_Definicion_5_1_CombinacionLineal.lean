import FormalizacionAlgLineal2026.Capitulo4.Sec15_Corolario_4_39_InterseccionTrivial

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


