import FormalizacionAlgLineal2026.Sec36_Corolario_5_43

/-!
====================================================================
37. TEOREMA 5.45: COMPLETAMIENTO DE BASES DE SUBESPACIOS
====================================================================
-/

/-- Teorema 5.45: Toda base de un subespacio se completa a una base de V. -/
theorem teorema_5_45_completamiento_subespacios {V : Type _} (E : EspacioVectorial V)
    (W : V → Prop) (_hW : EsSubespacio E W)
    (BW : List V) (hBW : EsBase E (fun w => w ∈ BW))
    (G : List V) (hG : ∀ v : V, Gen E (fun w => w ∈ G) v) :
    ∃ (BV : List V), (∀ w ∈ BW, w ∈ BV) ∧ EsBase E (fun w => w ∈ BV) := by
  obtain ⟨G_base, _hG_sub, hG_is_base⟩ := teorema_5_30_fg_tiene_base E G hG
  obtain ⟨G', hBW_in_G', hlen, hG'_gen⟩ := teorema_5_34_completamiento E BW G_base hBW.li hG_is_base.genera
  have hG'_base : EsBase E (fun w => w ∈ G') := corolario_5_43_i E G' G_base hG'_gen hG_is_base hlen
  exact ⟨G', hBW_in_G', hG'_base⟩


