import FormalizacionAlgLineal2026.Capitulo5.Sec24_Lema_5_20_InclusionesLI
import FormalizacionAlgLineal2026.Capitulo5.Sec25_LemasAuxiliares_CombLin

/-!
====================================================================
25. PROPOSICIÓN 5.21: (IN)DEPENDENCIA LINEAL AL SACAR VECTORES
====================================================================
-/

-- Diferencia de conjuntos S \ {s}
def SetMinus {V : Type _} (S : V → Prop) (s : V) : V → Prop :=
  fun v => S v ∧ v ≠ s

/-- Proposición 5.21 (Versión LD, I ⟹ II): Si S es LD, existe s ∈ S tal que s ∈ ⟨S \ {s}⟩. -/
theorem prop_5_21_LD_i_ii {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (hLD : EsLD E S) :
    ∃ s : V, S s ∧ Gen E (SetMinus S s) s := by
  rcases hLD with ⟨L, hS, h_pw, h_sum, ⟨t, ht_mem, ht_coef⟩⟩
  rcases combLin_descomposicion_elemento E L t ht_mem h_pw with ⟨L', hL'_mem, hL'_ne, hL'_sum⟩
  have h_add_zero : E.add (E.smul t.coef t.vector)
      (E.sumList (L'.map (fun x => E.smul x.coef x.vector))) = E.zero := by
    rw [← hL'_sum, h_sum]
  have h_desp := despeje_escalar E t.coef t.vector
    (E.sumList (L'.map (fun x => E.smul x.coef x.vector))) ht_coef h_add_zero
  refine ⟨t.vector, hS t ht_mem, ?_⟩
  dsimp [Gen, EsCombinacionLineal]
  refine ⟨smulTerminos (-t.coef⁻¹) L', ?_, ?_⟩
  · intro u hu
    rcases smulTerminos_vector (-t.coef⁻¹) L' u hu with ⟨x, hx_in, hu_vec⟩
    rw [hu_vec]
    exact ⟨hS x (hL'_mem x hx_in), hL'_ne x hx_in⟩
  · rw [sumList_smulTerminos]
    exact h_desp

/-- Proposición 5.21 (Versión LD, II ⟹ III): Si existe s ∈ S tal que s ∈ ⟨S \ {s}⟩,
    entonces ⟨S⟩ = ⟨S \ {s}⟩. -/
theorem prop_5_21_LD_ii_iii {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (s : V) (_hs : S s) (hs_gen : Gen E (SetMinus S s) s) :
    ∀ v, Gen E S v ↔ Gen E (SetMinus S s) v := by
  intro v
  constructor
  · intro hv
    exact (prop_5_7_iv E (SetMinus S s) v).mp
      (prop_5_7_ii E S (Gen E (SetMinus S s)) (fun w hw => by
        open Classical in
        by_cases heq : w = s
        · subst heq; exact hs_gen
        · exact prop_5_7_i E (SetMinus S s) w ⟨hw, heq⟩
      ) v hv)
  · exact prop_5_7_ii E (SetMinus S s) S (fun w ⟨hw, _⟩ => hw) v

open Classical

/-- Lema auxiliar: el escalar `-1` es no nulo en ℝ. -/
theorem neg_one_ne_zero : (-1 : ℝ) ≠ 0 := by
  intro h
  have h1 : (1 : ℝ) + -1 = 0 := add_neg_cancel 1
  rw [h, add_zero] at h1
  exact one_ne_zero h1

/-- Inserta un término en una lista de términos combinando coeficientes si el vector ya existe. -/
noncomputable def insertTerm {V : Type _} (t : TerminoCombLin V) :
    List (TerminoCombLin V) → List (TerminoCombLin V)
  | [] => [t]
  | x :: xs =>
    if t.vector = x.vector then
      ⟨t.coef + x.coef, x.vector⟩ :: xs
    else
      x :: insertTerm t xs

/-- Los vectores de `insertTerm t L` son `t.vector` o provienen de `L`. -/
theorem mem_insertTerm_vector {V : Type _} (t : TerminoCombLin V)
    (L : List (TerminoCombLin V)) (u : TerminoCombLin V)
    (hu : u ∈ insertTerm t L) :
    u.vector = t.vector ∨ ∃ v ∈ L, u.vector = v.vector := by
  induction L with
  | nil =>
    simp only [insertTerm, List.mem_singleton] at hu
    subst hu
    exact Or.inl rfl
  | cons head tail ih =>
    dsimp [insertTerm] at hu
    split at hu
    · rw [List.mem_cons] at hu
      rcases hu with hu_head | hu_in
      · right
        refine ⟨head, List.mem_cons_self, ?_⟩
        rw [hu_head]
      · right
        exact ⟨u, List.mem_cons_of_mem head hu_in, rfl⟩
    · rw [List.mem_cons] at hu
      rcases hu with hu_head | hu_in
      · right
        refine ⟨head, List.mem_cons_self, ?_⟩
        rw [hu_head]
      · rcases ih hu_in with h_t | ⟨v, hv_in, hv_eq⟩
        · exact Or.inl h_t
        · exact Or.inr ⟨v, List.mem_cons_of_mem head hv_in, hv_eq⟩

/-- Si una propiedad vectorial se cumple para `t` y para todos los términos de `L`, se preserva al insertar. -/
theorem insertTerm_mem_pred {V : Type _} (P : V → Prop) (t : TerminoCombLin V)
    (L : List (TerminoCombLin V)) (ht : P t.vector) (hL : ∀ x ∈ L, P x.vector) :
    ∀ u ∈ insertTerm t L, P u.vector := by
  intro u hu
  rcases mem_insertTerm_vector t L u hu with h_t | ⟨v, hv_in, hv_eq⟩
  · rw [h_t]; exact ht
  · rw [hv_eq]; exact hL v hv_in

/-- La inserción preserva que los vectores sean distintos dos a dos (`List.Pairwise`). -/
theorem pairwise_insertTerm {V : Type _} (t : TerminoCombLin V)
    (L : List (TerminoCombLin V))
    (h_pw : List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L) :
    List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) (insertTerm t L) := by
  induction L with
  | nil =>
    dsimp [insertTerm]
    rw [List.pairwise_cons]
    exact ⟨fun a' ha' => (nomatch ha'), List.Pairwise.nil⟩
  | cons head tail ih =>
    rw [List.pairwise_cons] at h_pw
    rcases h_pw with ⟨h_head_ne, h_tail_pw⟩
    have ih_pw := ih h_tail_pw
    dsimp [insertTerm]
    split
    · rw [List.pairwise_cons]
      refine ⟨?_, h_tail_pw⟩
      intro a' ha'
      dsimp
      exact h_head_ne a' ha'
    · rename_i h_ne
      rw [List.pairwise_cons]
      refine ⟨?_, ih_pw⟩
      intro a' ha'
      rcases mem_insertTerm_vector t tail a' ha' with h_t | ⟨v, hv_in, hv_eq⟩
      · intro h_contra
        apply h_ne
        calc
          t.vector = a'.vector := h_t.symm
          _        = head.vector := h_contra.symm
      · intro h_contra
        have := h_head_ne v hv_in
        apply this
        calc
          head.vector = a'.vector := h_contra
          _           = v.vector  := hv_eq

/-- La combinación lineal resultante de `insertTerm` es la suma del nuevo término y la combinación previa. -/
theorem sumList_insertTerm {V : Type _} (E : EspacioVectorial V)
    (t : TerminoCombLin V) (L : List (TerminoCombLin V)) :
    E.sumList ((insertTerm t L).map (fun x => E.smul x.coef x.vector)) =
      E.add (E.smul t.coef t.vector)
        (E.sumList (L.map (fun x => E.smul x.coef x.vector))) := by
  induction L with
  | nil =>
    simp only [insertTerm, List.map_cons, List.map_nil, E.sumList_cons, E.sumList_nil]
  | cons head tail ih =>
    dsimp [insertTerm]
    split
    · rename_i h_eq
      simp only [List.map_cons, E.sumList_cons]
      rw [E.ev8_add_smul, ← h_eq, E.ev1_add_assoc]
    · simp only [List.map_cons, E.sumList_cons]
      rw [ih]
      rw [← E.ev1_add_assoc, E.ev2_add_comm (E.smul head.coef head.vector), E.ev1_add_assoc]

/-- Normaliza una lista de términos combinando términos con vectores repetidos. -/
noncomputable def normalizeCombLin {V : Type _} : List (TerminoCombLin V) → List (TerminoCombLin V)
  | [] => []
  | t :: ts => insertTerm t (normalizeCombLin ts)

/-- Los términos normalizados preservan cualquier predicado satisfecho por los originales. -/
theorem normalizeCombLin_mem_pred {V : Type _} (P : V → Prop)
    (L : List (TerminoCombLin V)) (hL : ∀ x ∈ L, P x.vector) :
    ∀ u ∈ normalizeCombLin L, P u.vector := by
  induction L with
  | nil =>
    intro u hu
    nomatch hu
  | cons head tail ih =>
    dsimp [normalizeCombLin]
    have h_head : P head.vector := hL head List.mem_cons_self
    have h_tail : ∀ x ∈ tail, P x.vector := fun x hx => hL x (List.mem_cons_of_mem head hx)
    exact insertTerm_mem_pred P head (normalizeCombLin tail) h_head (ih h_tail)

/-- La lista normalizada tiene vectores distintos dos a dos. -/
theorem pairwise_normalizeCombLin {V : Type _} (L : List (TerminoCombLin V)) :
    List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) (normalizeCombLin L) := by
  induction L with
  | nil =>
    dsimp [normalizeCombLin]
    exact List.Pairwise.nil
  | cons head tail ih =>
    dsimp [normalizeCombLin]
    exact pairwise_insertTerm head (normalizeCombLin tail) ih

/-- La combinación lineal normalizada coincide en suma con la lista original. -/
theorem sumList_normalizeCombLin {V : Type _} (E : EspacioVectorial V)
    (L : List (TerminoCombLin V)) :
    E.sumList ((normalizeCombLin L).map (fun x => E.smul x.coef x.vector)) =
      E.sumList (L.map (fun x => E.smul x.coef x.vector)) := by
  induction L with
  | nil =>
    rfl
  | cons head tail ih =>
    dsimp [normalizeCombLin]
    rw [sumList_insertTerm E head (normalizeCombLin tail), ih]
    rfl

/-- Proposición 5.21 (Versión LD, III ⟹ I): Si existe s ∈ S tal que ⟨S⟩ = ⟨S \ {s}⟩,
    entonces S es LD. -/
theorem prop_5_21_LD_iii_i {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (s : V) (hs : S s)
    (h_eq : ∀ v, Gen E S v ↔ Gen E (SetMinus S s) v) :
    EsLD E S := by
  have hs_genS : Gen E S s := prop_5_7_i E S s hs
  have hs_genMinus : Gen E (SetMinus S s) s := (h_eq s).mp hs_genS
  rcases hs_genMinus with ⟨L, hL_mem, hL_sum⟩
  let L_norm := normalizeCombLin L
  have h_norm_mem : ∀ u ∈ L_norm, SetMinus S s u.vector :=
    normalizeCombLin_mem_pred (SetMinus S s) L hL_mem
  have h_norm_pw : List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L_norm :=
    pairwise_normalizeCombLin L
  have h_norm_sum : E.sumList (L_norm.map (fun x => E.smul x.coef x.vector)) = s := by
    rw [sumList_normalizeCombLin E L, ← hL_sum]
  let L_final : List (TerminoCombLin V) := ⟨-1, s⟩ :: L_norm
  refine ⟨L_final, ?_, ?_, ?_, ?_⟩
  · intro t ht
    dsimp [L_final] at ht
    rw [List.mem_cons] at ht
    rcases ht with rfl | ht_in
    · exact hs
    · exact (h_norm_mem t ht_in).1
  · dsimp [L_final]
    rw [List.pairwise_cons]
    refine ⟨?_, h_norm_pw⟩
    intro a' ha'
    dsimp
    have ha'_ne := (h_norm_mem a' ha').2
    intro h_eq_vec
    exact ha'_ne h_eq_vec.symm
  · dsimp [L_final]
    simp only [List.map_cons, E.sumList_cons]
    rw [h_norm_sum, prop_4_5_ii, E.neg_add]
  · refine ⟨⟨-1, s⟩, by dsimp [L_final]; exact List.mem_cons_self, neg_one_ne_zero⟩


