import FormalizacionAlgLineal2026.Capitulo5.Sec35_Definicion_5_39_Dimension

/-!
====================================================================
35. PROPOSICIÓN 5.41
====================================================================
-/

/-- Proposición 5.41, Parte I: Si I es LI, #I ≤ dim(V).
Requiere `I₀.Nodup` para garantizar que `I₀.length` coincide con la cardinalidad del conjunto LI. -/
theorem prop_5_41_i {V : Type _} (E : EspacioVectorial V)
    (I₀ : List V) (B : List V)
    (hNodup : I₀.Nodup)
    (hLI : EsLI E (fun w => w ∈ I₀))
    (hB : EsBase E (fun w => w ∈ B)) :
    I₀.length ≤ B.length :=
  prop_5_37 E I₀ B hNodup hLI hB.genera

/-- Proposición 5.41, Parte II: Si G es generador, #G ≥ dim(V).
Requiere `B.Nodup` para que la longitud de la base `B` (que actúa como conjunto LI)
coincida con su dimensión. -/
theorem prop_5_41_ii {V : Type _} (E : EspacioVectorial V)
    (G : List V) (B : List V)
    (hB_nodup : B.Nodup)
    (hG : ∀ v : V, Gen E (fun w => w ∈ G) v)
    (hB : EsBase E (fun w => w ∈ B)) :
    B.length ≤ G.length :=
  prop_5_37 E B G hB_nodup hB.li hG


