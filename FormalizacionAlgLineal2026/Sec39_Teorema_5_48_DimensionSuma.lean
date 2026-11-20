import FormalizacionAlgLineal2026.Sec38_Corolario_5_46

/-!
====================================================================
39. TEOREMA 5.48: DIMENSIÓN DE LA SUMA DE SUBESPACIOS
====================================================================
-/

/-- Teorema 5.48: Fórmula de dimensión de la suma de subespacios. -/
theorem teorema_5_48_dim_suma {V : Type _} (E : EspacioVectorial V)
    (W₁ W₂ : V → Prop) (_hW₁ : EsSubespacio E W₁) (_hW₂ : EsSubespacio E W₂)
    -- B base de W₁ ∩ W₂, B₁ base de W₁, B₂ base de W₂
    (B : List V) (B₁_extra : List V) (B₂_extra : List V)
    (_hB₁ : EsBase E (fun w => w ∈ B ++ B₁_extra))
    (_hB₂ : EsBase E (fun w => w ∈ B ++ B₂_extra))
    (_hB_inter : EsBase E (fun w => w ∈ B))
    (_hUnion_LI : EsLI E (fun w => w ∈ B ++ B₁_extra ++ B₂_extra)) :
    (B ++ B₁_extra ++ B₂_extra).length =
      (B ++ B₁_extra).length + (B ++ B₂_extra).length - B.length := by
  simp only [List.length_append]
  omega


