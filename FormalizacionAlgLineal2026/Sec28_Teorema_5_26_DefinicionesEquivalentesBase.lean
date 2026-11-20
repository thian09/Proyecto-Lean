import FormalizacionAlgLineal2026.Sec27_Definicion_5_24_Base

/-!
====================================================================
28. TEOREMA 5.26: DEFINICIONES EQUIVALENTES DE BASE
====================================================================
-/

/-- Condición II: Todo vector tiene una única expresión como combinación lineal de B. -/
def ExpresionUnica {V : Type _} (E : EspacioVectorial V) (B : V → Prop) : Prop :=
  ∀ v : V, EsCombinacionLineal E B v ∧
    (∀ (L₁ L₂ : List (TerminoCombLin V)),
      (∀ t ∈ L₁, B t.vector) →
      (∀ t ∈ L₂, B t.vector) →
      (List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L₁) →
      (List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L₂) →
      v = E.sumList (L₁.map (fun t => E.smul t.coef t.vector)) →
      v = E.sumList (L₂.map (fun t => E.smul t.coef t.vector)) →
      ∀ (t₁ : TerminoCombLin V), t₁ ∈ L₁ →
      ∀ (t₂ : TerminoCombLin V), t₂ ∈ L₂ →
      t₁.vector = t₂.vector → t₁.coef = t₂.coef)

/-- Condición III: B genera V y ningún subconjunto propio genera V. -/
def GeneradorMinimal {V : Type _} (E : EspacioVectorial V) (B : V → Prop) : Prop :=
  (∀ v : V, Gen E B v) ∧
  (∀ (I₀ : V → Prop), (∀ v, I₀ v → B v) → (∃ b, B b ∧ ¬ I₀ b) →
    ∃ v : V, ¬ Gen E I₀ v)

/-- Condición IV: B es LI y ningún superconjunto propio es LI. -/
def LIMaximal {V : Type _} (E : EspacioVectorial V) (B : V → Prop) : Prop :=
  EsLI E B ∧
  (∀ (G : V → Prop), (∀ v, B v → G v) → (∃ g, G g ∧ ¬ B g) → EsLD E G)

/-- Teorema 5.26 (I ⟹ III): Si B es base, B genera V y ningún subconjunto propio genera V. -/
theorem teorema_5_26_i_iii {V : Type _} (E : EspacioVectorial V) (B : V → Prop)
    (hB : EsBase E B) : GeneradorMinimal E B := by
  constructor
  · exact hB.genera
  · intro I₀ hI₀_sub ⟨b, hb, hb_notin⟩
    refine ⟨b, ?_⟩
    intro hb_gen
    have h_sub : ∀ v, I₀ v → SetMinus B b v := by
      intro v hv
      refine ⟨hI₀_sub v hv, ?_⟩
      rintro rfl
      exact hb_notin hv
    have hb_gen_minus : Gen E (SetMinus B b) b := prop_5_7_ii E I₀ (SetMinus B b) h_sub b hb_gen
    have h_eq : ∀ v, Gen E B v ↔ Gen E (SetMinus B b) v := prop_5_21_LD_ii_iii E B b hb hb_gen_minus
    have hLD : EsLD E B := prop_5_21_LD_iii_i E B b hb h_eq
    have h_not_ld : ¬ EsLD E B := (li_iff_not_ld E B).mp hB.li
    exact h_not_ld hLD

/-- Teorema 5.26 (III ⟹ I): Si B genera V y ningún subconjunto propio genera V, B es base. -/
theorem teorema_5_26_iii_i {V : Type _} (E : EspacioVectorial V) (B : V → Prop)
    (hB : GeneradorMinimal E B) : EsBase E B := by
  constructor
  · rw [li_iff_not_ld]
    intro hLD
    obtain ⟨b, hb, hb_gen⟩ := prop_5_21_LD_i_ii E B hLD
    have h_eq : ∀ v, Gen E B v ↔ Gen E (SetMinus B b) v := prop_5_21_LD_ii_iii E B b hb hb_gen
    have h_gen_minus : ∀ v, Gen E (SetMinus B b) v := by
      intro v
      exact (h_eq v).mp (hB.1 v)
    have h_sub : ∀ v, SetMinus B b v → B v := fun v hv => hv.1
    have h_diff : ∃ b', B b' ∧ ¬ SetMinus B b b' := ⟨b, hb, fun h => h.2 rfl⟩
    obtain ⟨v, hv_not_gen⟩ := hB.2 (SetMinus B b) h_sub h_diff
    exact hv_not_gen (h_gen_minus v)
  · exact hB.1

/-- Teorema 5.26 (I ⟹ IV): Si B es base, B es LI y ningún superconjunto propio es LI. -/
theorem teorema_5_26_i_iv {V : Type _} (E : EspacioVectorial V) (B : V → Prop)
    (hB : EsBase E B) : LIMaximal E B := by
  constructor
  · exact hB.li
  · intro G hG_sup ⟨g, hg, _hg_notin⟩
    have hLD_union : EsLD E (SetUnion B g) :=
      corolario_5_23_LD_vuelta E B g (hB.genera g)
    exact lema_5_20_ii E (SetUnion B g) G (fun v hv => by
      cases hv with
      | inl h => exact hG_sup v h
      | inr h => subst h; exact hg) hLD_union

/-- Teorema 5.26 (IV ⟹ I): Si B es LI y ningún superconjunto propio es LI, B es base. -/
theorem teorema_5_26_iv_i {V : Type _} (E : EspacioVectorial V) (B : V → Prop)
    (hB : LIMaximal E B) : EsBase E B := by
  constructor
  · exact hB.1
  · intro v
    open Classical in
    by_cases hv : Gen E B v
    · exact hv
    · have hv_notin : ¬ B v := by
        intro hBv; exact hv (prop_5_7_i E B v hBv)
      have hLI_union : EsLI E (SetUnion B v) := by
        rw [corolario_5_23_LI E B v hB.1 hv_notin]
        exact hv
      have hLD : EsLD E (SetUnion B v) :=
        hB.2 (SetUnion B v) (fun w hw => Or.inl hw) ⟨v, Or.inr rfl, hv_notin⟩
      exact False.elim (((li_iff_not_ld E (SetUnion B v)).mp hLI_union) hLD)


