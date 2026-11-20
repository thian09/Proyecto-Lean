import FormalizacionAlgLineal2026.Sec41_Teorema_5_52_BaseSumaDirectaDos

/-!
====================================================================
42. TEOREMA 5.54: BASE DE LA SUMA DIRECTA (VERSIÓN FAMILIA ARBITRARIA)
====================================================================
-/

/-- Bases de una familia son dos a dos disjuntas cuando los índices son distintos. -/
def BasesDisjuntas {V I : Type _} (B : I → List V) : Prop :=
  ∀ (i j : I), i ≠ j → ListaDisjunta (B i) (B j)

/-- Unión de una familia de listas como predicado. -/
def UnionListas {V I : Type _} (B : I → List V) : V → Prop :=
  fun v => ∃ i : I, v ∈ B i

/-- Teorema 5.54 (⟹): Si V = ⊕ Wᵢ con bases Bᵢ, entonces las Bᵢ son disjuntas
    y ⋃ Bᵢ es base de V. -/
axiom teorema_5_54_ida {V I : Type _} (E : EspacioVectorial V)
    (W : I → (V → Prop)) (hW : ∀ i, EsSubespacio E (W i))
    (hSD : EsSumaDirectaFamilia E W)
    (hSuma : ∀ v : V, SumaFamilia E W v)
    (B : I → List V) (hB : ∀ i, EsBase E (fun w => w ∈ B i)) :
    BasesDisjuntas B ∧ EsBase E (UnionListas B)

/-- Teorema 5.54 (⟸): Si las Bᵢ son disjuntas y ⋃ Bᵢ es base de V,
    entonces V = ⊕ ⟨Bᵢ⟩. -/
axiom teorema_5_54_vuelta {V I : Type _} (E : EspacioVectorial V)
    (B : I → List V)
    (hDisj : BasesDisjuntas B)
    (hBase : EsBase E (UnionListas B)) :
    (∀ v : V, SumaFamilia E (fun i => Gen E (fun w => w ∈ B i)) v) ∧
    EsSumaDirectaFamilia E (fun i => Gen E (fun w => w ∈ B i))

