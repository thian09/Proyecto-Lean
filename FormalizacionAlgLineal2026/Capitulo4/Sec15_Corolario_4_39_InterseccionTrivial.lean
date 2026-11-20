import FormalizacionAlgLineal2026.Capitulo4.Sec14_Definicion_4_37_Teorema_4_38_SumaDirectaArbitraria

/-!
====================================================================
15. COROLARIO 4.39: INTERSECCIÓN DE SUMA DIRECTA ARBITRARIA
====================================================================

"Corolario 4.39 (Página 146). Sea (V, +, ·) un ℝ-espacio vectorial. Si ℱ = {W_i ⊆ V : i ∈ I}
es una familia arbitraria de subespacios vectoriales de V y la suma ⨁_{i ∈ I} W_i es directa,
entonces ⋂_{i ∈ I} W_i = {0_V} (asumiendo que existen al menos dos índices distintos i₁ ≠ i₂ en I).

Demostración:
Si v ∈ ⋂_{i ∈ I} W_i, tomando i₁, i₂ ∈ I distintos y comparando las descomposiciones
  v = v_{i_1} + 0_{i_2} + 0_V + ...  y  v = 0_{i_1} + v_{i_2} + 0_V + ...,
tenemos que v = 0_V ∈ W_{i_1}, y por lo tanto, ⋂_{i ∈ I} W_i = {0_V}."
-/

/-- Corolario 4.39: Si la suma de una familia es directa y hay al menos dos índices distintos,
    su intersección es trivial ({0_V}). -/
theorem corolario_4_39_interseccion_trivial {V : Type _} {I : Type _}
    (E : EspacioVectorial V) (W : I → (V → Prop))
    (hdir : EsSumaDirectaFamilia E W)
    (i₁ i₂ : I) (hne : i₁ ≠ i₂)
    (v : V) (hv : ∀ i : I, W i v) :
    v = E.zero := by
  have hw₁ : W i₁ v := hv i₁
  have hw₂ : W i₂ v := hv i₂
  have h_excl : SumaExcluyendo E W i₁ v := by
    refine ⟨[⟨i₂, v⟩], ?_, ?_⟩
    · intro t ht
      simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨hne.symm, hw₂⟩
    · simp only [List.map_cons, List.map_nil, EspacioVectorial.sumList_cons, EspacioVectorial.sumList_nil]
      exact (E.add_zero v).symm
  exact hdir i₁ v hw₁ h_excl


/-
  Formalización en Lean 4: Capítulo 5 — Generadores, (In)dependencia Lineal y Bases
  Texto fuente: "Notas del curso Álgebra Lineal 1" (Eris Rocha Walchek, FCIEN UdelaR)
  Capítulo 5: Generadores, (in)dependencia lineal y bases (Capitulo5_Bases.md)
-/


