import FormalizacionAlgLineal2026.Capitulo4.Sec11_Definicion_4_25_SumaSubespacios

/-!
====================================================================
12. PROPOSICIÓN 4.27: LA SUMA DE SUBESPACIOS ES UN SUBESPACIO
====================================================================

"Proposición 4.27. Sea (V, +, ·) un ℝ-espacio vectorial. Si W₁ y W₂ son subespacios
vectoriales de V, entonces W₁ + W₂ es un subespacio vectorial de V.
Más generalmente, si ℱ = {W_i ⊆ V : i ∈ I} es una familia arbitraria de subespacios
vectoriales de V, la suma ∑_{i ∈ I} W_i también es un subespacio vectorial de V.

Demostración:
I.   0_V se escribe como una suma de w_i ∈ W_i donde el conjunto de sumandos no nulos es vacío.
     Por lo tanto, 0_V ∈ ∑_{i ∈ I} W_i;
II.  Sean v₁, v₂ ∈ ∑_{i ∈ I} W_i. v₁ = w_{i_1} + ... + w_{i_n} y v₂ = w_{i_{n+1}} + ... + w_{i_m}.
     Por lo tanto, la suma v₁ + v₂ es una suma finita de elementos contenidos en algunos de los W_i;
III. Sean v ∈ ∑_{i ∈ I} W_i y λ ∈ ℝ. Como cada W_i es subespacio cerrado por producto por escalar,
     λ · v = λ w_{i_1} + ... + λ w_{i_n} es una suma finita de elementos contenidos en algunos W_i."
-/

theorem EspacioVectorial.add_assoc_4 {V : Type _} (E : EspacioVectorial V) (a b c d : V) :
    E.add (E.add a b) (E.add c d) = E.add (E.add a c) (E.add b d) := by
  calc
    E.add (E.add a b) (E.add c d)
      = E.add a (E.add b (E.add c d)) := E.ev1_add_assoc a b (E.add c d)
    _ = E.add a (E.add (E.add b c) d) := by rw [E.ev1_add_assoc b c d]
    _ = E.add a (E.add (E.add c b) d) := by rw [E.ev2_add_comm b c]
    _ = E.add a (E.add c (E.add b d)) := by rw [E.ev1_add_assoc c b d]
    _ = E.add (E.add a c) (E.add b d) := (E.ev1_add_assoc a c (E.add b d)).symm

/-- Proposición 4.27 (Caso binario: la suma de dos subespacios es un subespacio vectorial). -/
theorem prop_4_27_suma_dos {V : Type _} (E : EspacioVectorial V) (W₁ W₂ : V → Prop)
    (hW₁ : EsSubespacio E W₁) (hW₂ : EsSubespacio E W₂) :
    EsSubespacio E (SumaDos E W₁ W₂) where
  zero_mem := by
    refine ⟨E.zero, E.zero, hW₁.zero_mem, hW₂.zero_mem, ?_⟩
    exact (E.add_zero E.zero).symm
  add_mem := by
    intro v₁ v₂ ⟨w₁, w₂, hw₁, hw₂, hv₁⟩ ⟨w₁', w₂', hw₁', hw₂', hv₂⟩
    refine ⟨E.add w₁ w₁', E.add w₂ w₂', hW₁.add_mem hw₁ hw₁', hW₂.add_mem hw₂ hw₂', ?_⟩
    rw [hv₁, hv₂, E.add_assoc_4 w₁ w₂ w₁' w₂']
  smul_mem := by
    intro «λ» v ⟨w₁, w₂, hw₁, hw₂, hv⟩
    refine ⟨E.smul «λ» w₁, E.smul «λ» w₂, hW₁.smul_mem «λ» hw₁, hW₂.smul_mem «λ» hw₂, ?_⟩
    rw [hv]
    exact E.ev7_smul_add «λ» w₁ w₂

/-- Proposición 4.27 (Caso general: la suma de una familia de subespacios es un subespacio vectorial). -/
theorem prop_4_27_suma_familia {V : Type _} {I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (hW : ∀ i : I, EsSubespacio E (W i)) :
    EsSubespacio E (SumaFamilia E W) where
  zero_mem := by
    refine ⟨[], ?_, ?_⟩
    · intro t ht
      cases ht
    · exact (E.sumList_nil).symm
  add_mem := by
    intro v₁ v₂ ⟨L₁, hL₁, hv₁⟩ ⟨L₂, hL₂, hv₂⟩
    refine ⟨L₁ ++ L₂, ?_, ?_⟩
    · intro t ht
      rcases List.mem_append.mp ht with h | h
      · exact hL₁ t h
      · exact hL₂ t h
    · rw [hv₁, hv₂]
      simp only [List.map_append]
      exact (E.sumList_append (L₁.map TerminoFamilia.vector) (L₂.map TerminoFamilia.vector)).symm
  smul_mem := by
    intro «λ» v ⟨L, hL, hv⟩
    refine ⟨L.map (fun t => ⟨t.indice, E.smul «λ» t.vector⟩), ?_, ?_⟩
    · intro t ht
      rcases List.mem_map.mp ht with ⟨orig, horig, rfl⟩
      exact (hW orig.indice).smul_mem «λ» (hL orig horig)
    · rw [hv]
      have hmap (xs : List (TerminoFamilia I V)) :
          (xs.map (fun t => (⟨t.indice, E.smul «λ» t.vector⟩ : TerminoFamilia I V))).map
            TerminoFamilia.vector =
          (xs.map TerminoFamilia.vector).map (E.smul «λ») := by
        induction xs with
        | nil => rfl
        | cons head tail ih =>
          simp only [List.map_cons, ih]
      rw [hmap L]
      exact E.smul_sumList «λ» (L.map TerminoFamilia.vector)


