import FormalizacionAlgLineal2026.Capitulo5.Sec26_Proposicion_5_21_SacarVectoresLD

/-!
====================================================================
26. COROLARIO 5.23: INDEPENDENCIA LINEAL AL AÑADIR VECTORES
====================================================================
-/

-- Unión de un conjunto con un elemento
def SetUnion {V : Type _} (S : V → Prop) (v₀ : V) : V → Prop :=
  fun v => S v ∨ v = v₀

/-- Corolario 5.23 (Versión LD, ⟹): Si I es LI, I ∪ {v₀} es LD y v₀ ∉ I,
    entonces v₀ ∈ ⟨I⟩. -/
axiom corolario_5_23_LD_ida {V : Type _} (E : EspacioVectorial V)
    (I₀ : V → Prop) (v₀ : V)
    (hLI : EsLI E I₀) (hv₀_notin : ¬ I₀ v₀)
    (hLD : EsLD E (SetUnion I₀ v₀)) :
    Gen E I₀ v₀

/-- Corolario 5.23 (Versión LD, ⟸): Si v₀ ∈ ⟨I⟩, entonces I ∪ {v₀} es LD. -/
axiom corolario_5_23_LD_vuelta {V : Type _} (E : EspacioVectorial V)
    (I₀ : V → Prop) (v₀ : V)
    (hv₀_gen : Gen E I₀ v₀) :
    EsLD E (SetUnion I₀ v₀)

/-- Corolario 5.23 (Versión LI): I ∪ {v₀} es LI si, y sólo si, v₀ ∉ ⟨I⟩. -/
theorem corolario_5_23_LI {V : Type _} (E : EspacioVectorial V)
    (I₀ : V → Prop) (v₀ : V)
    (hLI : EsLI E I₀) (hv₀_notin : ¬ I₀ v₀) :
    EsLI E (SetUnion I₀ v₀) ↔ ¬ Gen E I₀ v₀ := by
  rw [li_iff_not_ld]
  constructor
  · intro h_not_ld h_gen
    exact h_not_ld (corolario_5_23_LD_vuelta E I₀ v₀ h_gen)
  · intro h_not_gen h_ld
    exact h_not_gen (corolario_5_23_LD_ida E I₀ v₀ hLI hv₀_notin h_ld)


