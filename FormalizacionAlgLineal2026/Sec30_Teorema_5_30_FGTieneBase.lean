import FormalizacionAlgLineal2026.Sec29_Definicion_5_29_EspacioFinitamenteGenerado

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

