import FormalizacionAlgLineal2026.Sec35_Proposicion_5_41

/-!
====================================================================
36. COROLARIO 5.43
====================================================================
-/

/-- Corolario 5.43, Parte I: Si G genera V y #G = dim(V), G es base. -/
axiom corolario_5_43_i {V : Type _} (E : EspacioVectorial V)
    (G : List V) (B : List V)
    (hG : ∀ v : V, Gen E (fun w => w ∈ G) v)
    (hB : EsBase E (fun w => w ∈ B))
    (h_eq : G.length = B.length) :
    EsBase E (fun w => w ∈ G)

/-- Corolario 5.43, Parte II: Si I es LI y #I = dim(V), I es base. -/
axiom corolario_5_43_ii {V : Type _} (E : EspacioVectorial V)
    (I₀ : List V) (B : List V)
    (hLI : EsLI E (fun w => w ∈ I₀))
    (hB : EsBase E (fun w => w ∈ B))
    (h_eq : I₀.length = B.length) :
    EsBase E (fun w => w ∈ I₀)


