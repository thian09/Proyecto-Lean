import FormalizacionAlgLineal2026.Capitulo5.Sec31_Teorema_5_30_FGTieneBase
import FormalizacionAlgLineal2026.Capitulo5.Sec25_LemasAuxiliares_CombLin
import FormalizacionAlgLineal2026.Capitulo5.Sec27_Corolario_5_23_AnadirVectoresLI

open Classical

/-!
====================================================================
31. TEOREMA 5.34: COMPLETAMIENTO DE BASES (Lemas Auxiliares)
====================================================================
-/

/-- Reemplaza un elemento `target` por `nuevo` en una lista. -/
noncomputable def reemplazarElemento {V : Type _} (target nuevo : V) : List V → List V
  | [] => []
  | x :: xs => if x = target then nuevo :: reemplazarElemento target nuevo xs else x :: reemplazarElemento target nuevo xs

/-- Reemplazar un elemento en una lista preserva su longitud. -/
theorem length_reemplazarElemento {V : Type _} (target nuevo : V) (L : List V) :
    (reemplazarElemento target nuevo L).length = L.length := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    dsimp [reemplazarElemento]
    split <;> (dsimp; rw [ih])

/-- Si `target ∉ L`, reemplazar `target` no modifica la lista. -/
theorem reemplazarElemento_of_not_mem {V : Type _} (target nuevo : V) (L : List V)
    (h : target ∉ L) :
    reemplazarElemento target nuevo L = L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    have hx : x ≠ target := fun h_eq => h (by rw [h_eq]; exact List.mem_cons_self)
    have hxs : target ∉ xs := fun h_in => h (List.mem_cons_of_mem x h_in)
    dsimp [reemplazarElemento]
    split
    · next h_eq => exfalso; exact hx h_eq
    · next h_ne =>
      rw [ih hxs]

/-- Pertenencia tras reemplazo: si `target ∈ L`, pertenecer a la lista reemplazada
    equivale a ser `nuevo` o pertenecer a `L` siendo distinto de `target`. -/
theorem mem_reemplazarElemento {V : Type _} (target nuevo : V) (L : List V) (w : V)
    (h_target : target ∈ L) :
    w ∈ reemplazarElemento target nuevo L ↔ (w = nuevo ∨ (w ∈ L ∧ w ≠ target)) := by
  induction L with
  | nil => cases h_target
  | cons x xs ih =>
    dsimp [reemplazarElemento]
    split
    · next hx =>
      rw [List.mem_cons]
      by_cases h_txs : target ∈ xs
      · rw [ih h_txs]
        constructor
        · intro h
          rcases h with rfl | (rfl | ⟨hw_xs, hw_ne⟩)
          · left; rfl
          · left; rfl
          · right
            exact ⟨List.mem_cons_of_mem x hw_xs, hw_ne⟩
        · intro h
          rcases h with rfl | ⟨hw_L, hw_ne⟩
          · left; rfl
          · rw [List.mem_cons] at hw_L
            rcases hw_L with rfl | hw_xs
            · exfalso; exact hw_ne hx
            · right; right; exact ⟨hw_xs, hw_ne⟩
      · rw [reemplazarElemento_of_not_mem target nuevo xs h_txs]
        constructor
        · intro h
          rcases h with rfl | hw_xs
          · left; rfl
          · right
            refine ⟨List.mem_cons_of_mem x hw_xs, ?_⟩
            intro hw_eq
            apply h_txs
            rw [← hw_eq]
            exact hw_xs
        · intro h
          rcases h with rfl | ⟨hw_L, hw_ne⟩
          · left; rfl
          · rw [List.mem_cons] at hw_L
            rcases hw_L with rfl | hw_xs
            · exfalso; exact hw_ne hx
            · right; exact hw_xs
    · next hx =>
      rw [List.mem_cons]
      have h_txs : target ∈ xs := by
        rw [List.mem_cons] at h_target
        rcases h_target with rfl | h_in
        · exfalso; exact hx rfl
        · exact h_in
      rw [ih h_txs]
      constructor
      · intro h
        rcases h with rfl | (rfl | ⟨hw_xs, hw_ne⟩)
        · right
          refine ⟨List.mem_cons_self, ?_⟩
          intro hw_eq
          exact hx hw_eq
        · left; rfl
        · right
          exact ⟨List.mem_cons_of_mem x hw_xs, hw_ne⟩
      · intro h
        rcases h with rfl | ⟨hw_L, hw_ne⟩
        · right; left; rfl
        · rw [List.mem_cons] at hw_L
          rcases hw_L with rfl | hw_xs
          · left; rfl
          · right; right; exact ⟨hw_xs, hw_ne⟩

/-- No pertenencia a ⟨us⟩ para elementos de un conjunto LI:
    si `u :: us` es LI y `u ∉ us`, entonces `u` no pertenece al subespacio generado por `us`. -/
theorem not_gen_of_li_cons {V : Type _} (E : EspacioVectorial V) (us : List V) (u : V)
    (hLI : EsLI E (fun w => w ∈ u :: us)) (hu_notin : u ∉ us) :
    ¬ Gen E (fun w => w ∈ us) u := by
  intro h_gen
  have hLD : EsLD E (SetUnion (fun w => w ∈ us) u) :=
    corolario_5_23_LD_vuelta E (fun w => w ∈ us) u hu_notin h_gen
  have h_sub : ∀ v, SetUnion (fun w => w ∈ us) u v → (v ∈ u :: us) := by
    intro v hv
    rcases hv with hv_us | rfl
    · exact List.mem_cons_of_mem u hv_us
    · exact List.mem_cons_self
  have hLI_union : EsLI E (SetUnion (fun w => w ∈ us) u) :=
    lema_5_20_i E (fun w => w ∈ u :: us) (SetUnion (fun w => w ∈ us) u) h_sub hLI
  have h_not_ld := (li_iff_not_ld E (SetUnion (fun w => w ∈ us) u)).mp hLI_union
  exact h_not_ld hLD

/-- Si todos los términos con coeficiente no nulo tienen su vector en `S`,
    la suma de la combinación lineal pertenece al subespacio generado `Gen E S`. -/
theorem gen_sumList_of_all_mem {V : Type _} (E : EspacioVectorial V)
    (S : V → Prop) (L : List (TerminoCombLin V))
    (h : ∀ t ∈ L, t.coef ≠ 0 → S t.vector) :
    Gen E S (E.sumList (L.map (fun t => E.smul t.coef t.vector))) := by
  have hW : EsSubespacio E (Gen E S) := prop_5_5_gen_es_subespacio E S
  induction L with
  | nil =>
    simp only [List.map_nil, EspacioVectorial.sumList_nil]
    exact hW.zero_mem
  | cons t ts ih =>
    simp only [List.map_cons, EspacioVectorial.sumList_cons]
    apply hW.add_mem
    · by_cases ht : t.coef = 0
      · rw [ht, prop_4_5_i E t.vector]
        exact hW.zero_mem
      · have ht_S : S t.vector := h t List.mem_cons_self ht
        have ht_gen : Gen E S t.vector := prop_5_7_i E S t.vector ht_S
        exact hW.smul_mem t.coef ht_gen
    · apply ih
      intro x hx hx_coef
      exact h x (List.mem_cons_of_mem t hx) hx_coef

/-- Paso atómico de intercambio del Lema de Steinitz:
    Dado un conjunto `us ⊆ G` y un vector `u` generado por `G` pero no generado por `us`,
    existe un elemento `g_star ∈ G \ us` tal que reemplazar `g_star` por `u` en `G`
    preserva el subespacio generado. -/
theorem steinitz_paso_intercambio {V : Type _} (E : EspacioVectorial V)
    (us : List V) (G : List V) (u : V)
    (hus_sub : ∀ w ∈ us, w ∈ G)
    (hu_genG : Gen E (fun w => w ∈ G) u)
    (hu_not_gen_us : ¬ Gen E (fun w => w ∈ us) u) :
    ∃ (g_star : V),
      g_star ∈ G ∧
      g_star ∉ us ∧
      (∀ v : V, Gen E (fun w => w ∈ reemplazarElemento g_star u G) v ↔ Gen E (fun w => w ∈ G) v) := by
  have _ := hus_sub
  have ⟨L, hL_G, hu_sum⟩ := hu_genG
  let L_norm := normalizeCombLin L
  have hL_norm_G : ∀ x ∈ L_norm, x.vector ∈ G :=
    normalizeCombLin_mem_pred (fun w => w ∈ G) L hL_G
  have h_pw : List.Pairwise (fun t₁ t₂ => t₁.vector ≠ t₂.vector) L_norm :=
    pairwise_normalizeCombLin L
  have h_exists : ∃ t ∈ L_norm, t.coef ≠ 0 ∧ t.vector ∉ us := by
    by_cases h : ∃ t ∈ L_norm, t.coef ≠ 0 ∧ t.vector ∉ us
    · exact h
    · exfalso
      apply hu_not_gen_us
      rw [hu_sum, ← sumList_normalizeCombLin E L]
      apply gen_sumList_of_all_mem
      intro t ht ht_coef
      by_cases h_in : t.vector ∈ us
      · exact h_in
      · exfalso
        exact h ⟨t, ht, ht_coef, h_in⟩
  rcases h_exists with ⟨t_star, ht_star_mem, ht_star_coef, ht_star_notin⟩
  let g_star := t_star.vector
  have hg_star_G : g_star ∈ G := hL_norm_G t_star ht_star_mem
  have hg_star_not_us : g_star ∉ us := ht_star_notin
  rcases sumList_map_termino_mem_split E L_norm t_star ht_star_mem with ⟨L₁, L₂, h_decomp, h_sum_split⟩
  let L' := L₁ ++ L₂
  have hL'_in : ∀ x ∈ L', x ∈ L_norm := by
    rw [h_decomp]
    exact fun x hx => mem_of_mem_split L₁ L₂ t_star x hx
  have hL'_ne : ∀ x ∈ L', x.vector ≠ g_star :=
    pairwise_vector_ne_of_mem_split h_decomp h_pw
  let rest := E.sumList (L'.map (fun x => E.smul x.coef x.vector))
  have hu_eq : u = E.add (E.smul t_star.coef g_star) rest := by
    calc
      u = E.sumList (L.map (fun t => E.smul t.coef t.vector)) := hu_sum
      _ = E.sumList (L_norm.map (fun x => E.smul x.coef x.vector)) := by
        rw [← sumList_normalizeCombLin E L]
      _ = E.add (E.smul t_star.coef g_star) rest := h_sum_split
  have h_zero : E.add (E.smul t_star.coef g_star) (E.add rest (E.neg u)) = E.zero := by
    calc
      E.add (E.smul t_star.coef g_star) (E.add rest (E.neg u))
        = E.add (E.add (E.smul t_star.coef g_star) rest) (E.neg u) := (E.ev1_add_assoc _ _ _).symm
      _ = E.add u (E.neg u) := by rw [← hu_eq]
      _ = E.zero := E.add_neg u
  have h_desp := despeje_escalar E t_star.coef g_star (E.add rest (E.neg u)) ht_star_coef h_zero
  let G' := reemplazarElemento g_star u G
  let S' : V → Prop := fun w => w ∈ G'
  have hW' : EsSubespacio E (Gen E S') := prop_5_5_gen_es_subespacio E S'
  have hu_G' : S' u := by
    dsimp [S']
    rw [mem_reemplazarElemento g_star u G u hg_star_G]
    exact Or.inl rfl
  have hu_gen : Gen E S' u := prop_5_7_i E S' u hu_G'
  have h_neg_u : Gen E S' (E.neg u) := by
    rw [← prop_4_5_ii E u]
    exact hW'.smul_mem (-1) hu_gen
  have h_rest : Gen E S' rest := by
    refine ⟨L', ?_, rfl⟩
    intro x hx
    dsimp [S']
    rw [mem_reemplazarElemento g_star u G x.vector hg_star_G]
    exact Or.inr ⟨hL_norm_G x (hL'_in x hx), hL'_ne x hx⟩
  have h_add : Gen E S' (E.add rest (E.neg u)) := hW'.add_mem h_rest h_neg_u
  have hg_star_gen : Gen E S' g_star := by
    rw [h_desp]
    exact hW'.smul_mem (-t_star.coef⁻¹) h_add
  refine ⟨g_star, hg_star_G, hg_star_not_us, ?_⟩
  intro v
  constructor
  · intro hv
    apply (prop_5_7_iv E (fun w => w ∈ G) v).mp
    apply prop_5_7_ii E S' (Gen E (fun w => w ∈ G)) _ v hv
    intro w hw
    dsimp [S'] at hw
    rw [mem_reemplazarElemento g_star u G w hg_star_G] at hw
    rcases hw with rfl | ⟨hw_G, _⟩
    · exact hu_genG
    · exact prop_5_7_i E (fun w => w ∈ G) w hw_G
  · intro hv
    apply (prop_5_7_iv E S' v).mp
    apply prop_5_7_ii E (fun w => w ∈ G) (Gen E S') _ v hv
    intro w hw
    by_cases hw_eq : w = g_star
    · subst hw_eq
      exact hg_star_gen
    · apply prop_5_7_i E S' w
      dsimp [S']
      rw [mem_reemplazarElemento g_star u G w hg_star_G]
      exact Or.inr ⟨hw, hw_eq⟩

/-- Teorema 5.34: Todo conjunto LI finito puede completarse a una base,
    sustituyendo inductivamente generadores por elementos del LI. -/
theorem teorema_5_34_completamiento {V : Type _} (E : EspacioVectorial V)
    (I₀ : List V) (G : List V)
    (hLI : EsLI E (fun w => w ∈ I₀))
    (hG : ∀ v : V, Gen E (fun w => w ∈ G) v) :
    ∃ (G' : List V),
      (∀ w ∈ I₀, w ∈ G') ∧
      G'.length = G.length ∧
      (∀ v : V, Gen E (fun w => w ∈ G') v) := by
  revert G hG
  induction I₀ with
  | nil =>
    intro G hG
    refine ⟨G, fun w hw => (nomatch hw), rfl, hG⟩
  | cons u us ih =>
    intro G hG
    have hLI_us : EsLI E (fun w => w ∈ us) :=
      lema_5_20_i E (fun w => w ∈ u :: us) (fun w => w ∈ us)
        (fun w hw => List.mem_cons_of_mem u hw) hLI
    rcases ih hLI_us G hG with ⟨G_prev, hus_sub, hlen, hG_prev_gen⟩
    open Classical in
    by_cases hu_in_us : u ∈ us
    · -- Caso redundante: u ya estaba en us
      refine ⟨G_prev, ?_, hlen, hG_prev_gen⟩
      intro w hw
      rw [List.mem_cons] at hw
      rcases hw with hw_eq | hw_us
      · rw [hw_eq]
        exact hus_sub u hu_in_us
      · exact hus_sub w hw_us
    · -- Caso de extensión activa: u ∉ us
      have hu_not_gen := not_gen_of_li_cons E us u hLI hu_in_us
      have hu_genG := hG_prev_gen u
      rcases steinitz_paso_intercambio E us G_prev u hus_sub hu_genG hu_not_gen
        with ⟨g_star, hg_star_G, hg_star_not_us, h_gen_equiv⟩
      let G' := reemplazarElemento g_star u G_prev
      refine ⟨G', ?_, ?_, ?_⟩
      · -- Inclusión: ∀ w ∈ u :: us, w ∈ G'
        intro w hw
        rw [List.mem_cons] at hw
        rcases hw with hw_eq | hw_us
        · rw [hw_eq]
          rw [mem_reemplazarElemento g_star u G_prev u hg_star_G]
          exact Or.inl rfl
        · rw [mem_reemplazarElemento g_star u G_prev w hg_star_G]
          refine Or.inr ⟨hus_sub w hw_us, ?_⟩
          rintro rfl
          exact hg_star_not_us hw_us
      · -- Longitud: G'.length = G.length
        rw [length_reemplazarElemento g_star u G_prev, hlen]
      · -- Generador: ∀ v, Gen E (fun w => w ∈ G') v
        intro v
        rw [h_gen_equiv v]
        exact hG_prev_gen v
