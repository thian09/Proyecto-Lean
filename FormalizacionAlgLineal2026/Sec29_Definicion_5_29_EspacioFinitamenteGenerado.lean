import FormalizacionAlgLineal2026.Sec28_Teorema_5_26_DefinicionesEquivalentesBase

/-!
====================================================================
29. DEFINICIÓN 5.29: ESPACIO FINITAMENTE GENERADO
====================================================================
-/

/-- Definición 5.29: V es finitamente generado si existe un generador finito. -/
def EsFG {V : Type _} (E : EspacioVectorial V) : Prop :=
  ∃ (G : List V), ∀ v : V, Gen E (fun w => w ∈ G) v


