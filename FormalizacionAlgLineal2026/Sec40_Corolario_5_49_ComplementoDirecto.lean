import FormalizacionAlgLineal2026.Sec39_Teorema_5_48_DimensionSuma

/-!
====================================================================
40. COROLARIO 5.49: COMPLETAMIENTO DE SUBESPACIOS
====================================================================
-/

/-- Corolario 5.49: Todo subespacio W de un espacio FG tiene un complemento directo W'. -/
axiom corolario_5_49_complemento_directo {V : Type _} (E : EspacioVectorial V)
    (W : V → Prop) (hW : EsSubespacio E W)
    (BW : List V) (BV_extra : List V)
    (hBV : EsBase E (fun w => w ∈ BW ++ BV_extra))
    (hBW_base : EsBase E (fun w => w ∈ BW)) :
    (∀ v : V, SumaDos E W (Gen E (fun w => w ∈ BV_extra)) v) ∧
    EsSumaDirectaDos E W (Gen E (fun w => w ∈ BV_extra))


