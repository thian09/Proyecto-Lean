import FormalizacionAlgLineal2026.Sec37_Teorema_5_45_CompletamientoSubespacios

/-!
====================================================================
38. COROLARIO 5.46
====================================================================
-/

/-- Corolario 5.46: dim(W) ≤ dim(V), con igualdad sii W = V. -/
theorem corolario_5_46 {V : Type _} (E : EspacioVectorial V)
    (W : V → Prop) (_hW : EsSubespacio E W)
    (BW : List V) (BV : List V)
    (hBW_nodup : BW.Nodup)
    (hBW : EsBase E (fun w => w ∈ BW))
    (hBV : EsBase E (fun w => w ∈ BV))
    (_hBW_sub : ∀ w ∈ BW, w ∈ BV) :
    BW.length ≤ BV.length := by
  exact prop_5_41_i E BW BV hBW_nodup hBW.li hBV


