import FormalizacionAlgLineal2026.Sec32_Proposicion_5_37

/-!
====================================================================
33. PROPOSICIÓN 5.38: TODA BASE DE UN ESPACIO FG TIENE EL MISMO TAMAÑO
====================================================================
-/

/-- Proposición 5.38: Dos bases finitas de un mismo espacio tienen el mismo cardinal.
Requiere las hipótesis `B₁.Nodup` y `B₂.Nodup` para que las longitudes de las listas
coincidan con los cardinales de los conjuntos base subyacentes. -/
theorem prop_5_38_bases_mismo_cardinal {V : Type _} (E : EspacioVectorial V)
    (B₁ B₂ : List V)
    (hB₁_nodup : B₁.Nodup)
    (hB₂_nodup : B₂.Nodup)
    (hB₁ : EsBase E (fun w => w ∈ B₁))
    (hB₂ : EsBase E (fun w => w ∈ B₂)) :
    B₁.length = B₂.length := by
  have h1 : B₁.length ≤ B₂.length := prop_5_37 E B₁ B₂ hB₁_nodup hB₁.li hB₂.genera
  have h2 : B₂.length ≤ B₁.length := prop_5_37 E B₂ B₁ hB₂_nodup hB₂.li hB₁.genera
  exact Nat.le_antisymm h1 h2


