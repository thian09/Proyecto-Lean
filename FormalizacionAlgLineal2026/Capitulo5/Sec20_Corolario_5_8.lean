import FormalizacionAlgLineal2026.Capitulo5.Sec19_Proposicion_5_7_PropiedadesGenerado

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


