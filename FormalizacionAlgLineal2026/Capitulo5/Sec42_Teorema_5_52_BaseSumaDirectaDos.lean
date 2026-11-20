import FormalizacionAlgLineal2026.Capitulo5.Sec41_Corolario_5_49_ComplementoDirecto

/-!
====================================================================
41. TEOREMA 5.52: BASE DE LA SUMA DIRECTA (VERSIÓN 2 SUBESPACIOS)
====================================================================
-/

/-- Intersección vacía de dos listas (como predicados) -/
def ListaDisjunta {V : Type _} (L₁ L₂ : List V) : Prop :=
  ∀ v, v ∈ L₁ → v ∉ L₂

/-- Teorema 5.52 (⟹): Si V = W₁ ⊕ W₂ con bases B₁, B₂,
    entonces B₁ ∩ B₂ = ∅ y B₁ ∪ B₂ es base de V. -/
axiom teorema_5_52_ida {V : Type _} (E : EspacioVectorial V)
    (W₁ W₂ : V → Prop) (hW₁ : EsSubespacio E W₁) (hW₂ : EsSubespacio E W₂)
    (hSD : EsSumaDirectaDos E W₁ W₂)
    (hSuma : ∀ v : V, SumaDos E W₁ W₂ v)
    (B₁ B₂ : List V)
    (hB₁ : EsBase E (fun w => w ∈ B₁))
    (hB₂ : EsBase E (fun w => w ∈ B₂)) :
    ListaDisjunta B₁ B₂ ∧ EsBase E (fun w => w ∈ B₁ ++ B₂)

/-- Teorema 5.52 (⟸): Si B₁ ∩ B₂ = ∅ y B₁ ∪ B₂ es base de V,
    entonces V = ⟨B₁⟩ ⊕ ⟨B₂⟩. -/
axiom teorema_5_52_vuelta {V : Type _} (E : EspacioVectorial V)
    (B₁ B₂ : List V)
    (hDisj : ListaDisjunta B₁ B₂)
    (hBase : EsBase E (fun w => w ∈ B₁ ++ B₂)) :
    (∀ v : V, SumaDos E (Gen E (fun w => w ∈ B₁)) (Gen E (fun w => w ∈ B₂)) v) ∧
    EsSumaDirectaDos E (Gen E (fun w => w ∈ B₁)) (Gen E (fun w => w ∈ B₂))


