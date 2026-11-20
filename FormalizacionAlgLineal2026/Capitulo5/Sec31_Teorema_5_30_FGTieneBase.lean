import FormalizacionAlgLineal2026.Capitulo5.Sec30_Definicion_5_29_EspacioFinitamenteGenerado

/-!
====================================================================
30. TEOREMA 5.30: TODO ESPACIO FG TIENE BASE
====================================================================
-/

/-- La lista vacía es linealmente independiente. -/
theorem esLI_nil {V : Type _} (E : EspacioVectorial V) :
    EsLI E (fun w => w ∈ ([] : List V)) := by
  intro L hL_mem _ _ t ht
  have ht_in := hL_mem t ht
  cases ht_in

/-- Si x no está en el subespacio generado por B, entonces x no pertenece a B. -/
theorem not_mem_of_not_gen {V : Type _} (E : EspacioVectorial V) (B : List V) (x : V)
    (h_not_gen : ¬ Gen E (fun w => w ∈ B) x) : x ∉ B := by
  intro hx_in
  apply h_not_gen
  exact prop_5_7_i E (fun w => w ∈ B) x hx_in

/-- Si B es LI y x no está generado por B, entonces x :: B es LI. -/
theorem esLI_cons_of_corolario {V : Type _} (E : EspacioVectorial V) (B : List V) (x : V)
    (hLI : EsLI E (fun w => w ∈ B))
    (h_not_gen : ¬ Gen E (fun w => w ∈ B) x) :
    EsLI E (fun w => w ∈ x :: B) := by
  have hx_notin : x ∉ B := not_mem_of_not_gen E B x h_not_gen
  have h_union_LI : EsLI E (SetUnion (fun w => w ∈ B) x) :=
    (corolario_5_23_LI E (fun w => w ∈ B) x hLI hx_notin).mpr h_not_gen
  apply lema_5_20_i E (SetUnion (fun w => w ∈ B) x) (fun w => w ∈ x :: B) _ h_union_LI
  intro w hw
  rw [List.mem_cons] at hw
  rcases hw with rfl | hwB
  · right; rfl
  · left; exact hwB

/-- Transitividad de generadores: si cada elemento de G está generado por B,
    entonces todo vector generado por G también está generado por B. -/
theorem gen_trans_list {V : Type _} (E : EspacioVectorial V) (B G : List V)
    (hBG : ∀ w ∈ G, Gen E (fun u => u ∈ B) w)
    (v : V) (hv : Gen E (fun w => w ∈ G) v) :
    Gen E (fun u => u ∈ B) v := by
  have h_gen_gen : Gen E (Gen E (fun u => u ∈ B)) v :=
    prop_5_7_ii E (fun w => w ∈ G) (Gen E (fun u => u ∈ B)) hBG v hv
  exact (prop_5_7_iv E (fun u => u ∈ B) v).mp h_gen_gen

/-- Algoritmo voraz de extracción inductiva de una base sobre una lista:
    Dada una lista L de vectores, existe una sublista B de L tal que B es linealmente
    independiente y B genera todos los elementos de L. -/
theorem extraer_base_de_lista {V : Type _} (E : EspacioVectorial V) (L : List V) :
    ∃ (B : List V),
      (∀ w ∈ B, w ∈ L) ∧
      EsLI E (fun w => w ∈ B) ∧
      (∀ w ∈ L, Gen E (fun u => u ∈ B) w) := by
  induction L with
  | nil =>
    refine ⟨[], ?_, ?_, ?_⟩
    · intro w hw
      cases hw
    · exact esLI_nil E
    · intro w hw
      cases hw
  | cons x xs ih =>
    rcases ih with ⟨B_xs, hB_sub, hB_li, hB_gen⟩
    open Classical in
    by_cases hx_gen : Gen E (fun u => u ∈ B_xs) x
    · refine ⟨B_xs, ?_, hB_li, ?_⟩
      · intro w hw
        exact List.mem_cons_of_mem x (hB_sub w hw)
      · intro w hw
        rw [List.mem_cons] at hw
        cases hw with
        | inl hw_eq =>
          rw [hw_eq]
          exact hx_gen
        | inr hw_xs =>
          exact hB_gen w hw_xs
    · refine ⟨x :: B_xs, ?_, ?_, ?_⟩
      · intro w hw
        rw [List.mem_cons] at hw
        cases hw with
        | inl hw_eq =>
          rw [hw_eq]
          exact List.mem_cons_self
        | inr hw_B =>
          exact List.mem_cons_of_mem x (hB_sub w hw_B)
      · exact esLI_cons_of_corolario E B_xs x hB_li hx_gen
      · intro w hw
        rw [List.mem_cons] at hw
        cases hw with
        | inl hw_eq =>
          rw [hw_eq]
          apply prop_5_7_i E (fun u => u ∈ x :: B_xs) x
          exact List.mem_cons_self
        | inr hw_xs =>
          have hw_gen := hB_gen w hw_xs
          apply prop_5_7_ii E (fun u => u ∈ B_xs) (fun u => u ∈ x :: B_xs) _ w hw_gen
          intro u hu
          exact List.mem_cons_of_mem x hu

/-- Teorema 5.30: Todo generador finito contiene una base.
    Formulación: Si G (como lista) genera V, existe una sublista G' ⊆ G que es base de V. -/
theorem teorema_5_30_fg_tiene_base {V : Type _} (E : EspacioVectorial V)
    (G : List V) (hG : ∀ v : V, Gen E (fun w => w ∈ G) v) :
    ∃ (G' : List V), (∀ w ∈ G', w ∈ G) ∧ EsBase E (fun w => w ∈ G') := by
  rcases extraer_base_de_lista E G with ⟨G', hG'_sub, hG'_li, hG'_genG⟩
  refine ⟨G', hG'_sub, ⟨hG'_li, ?_⟩⟩
  intro v
  have hvG := hG v
  exact gen_trans_list E G' G hG'_genG v hvG
