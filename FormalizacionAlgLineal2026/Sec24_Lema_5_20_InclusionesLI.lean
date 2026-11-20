import FormalizacionAlgLineal2026.Sec23_Definicion_5_15_IndependenciaLineal

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


