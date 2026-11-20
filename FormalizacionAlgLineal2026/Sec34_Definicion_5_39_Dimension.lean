import FormalizacionAlgLineal2026.Sec33_Proposicion_5_38_BasesMismoCardinal

/-!
====================================================================
34. DEFINICIÓN 5.39: DIMENSIÓN
====================================================================
-/

/-- Definición 5.39 (Dimensión): Si V tiene una base finita B, dim(V) := #B. -/
noncomputable def Dimension {V : Type _} (E : EspacioVectorial V) (B : List V)
    (_ : EsBase E (fun w => w ∈ B)) : Nat :=
  B.length


