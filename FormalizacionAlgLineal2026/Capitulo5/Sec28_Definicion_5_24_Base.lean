import FormalizacionAlgLineal2026.Capitulo5.Sec27_Corolario_5_23_AnadirVectoresLI

/-!
====================================================================
27. DEFINICIÓN 5.24: BASE
====================================================================
-/

/-- Definición 5.24 (Base): B es una base de V si es LI y genera V. -/
structure EsBase {V : Type _} (E : EspacioVectorial V) (B : V → Prop) : Prop where
  li     : EsLI E B
  genera : ∀ v : V, Gen E B v


