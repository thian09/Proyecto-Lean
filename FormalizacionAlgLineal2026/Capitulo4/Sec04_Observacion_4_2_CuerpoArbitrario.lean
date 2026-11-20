import FormalizacionAlgLineal2026.Capitulo4.Sec03_Corolario_4_4_Cancelacion

/-!
====================================================================
4. OBSERVACIÓN 4.2: GENERALIZACIÓN A UN CUERPO k ARBITRARIO
====================================================================

"Además, el 'sobre ℝ' en la definición indica que los escalares son tomados en ℝ
(también se puede abreviar diciendo ℝ-espacio vectorial). Naturalmente, trabajando
con otro cuerpo k, los escalares serían tomados en k, definiendo un espacio vectorial sobre k."
-/

/-- Definición 4.1 generalizada sobre un cuerpo arbitrario K (k-espacio vectorial). -/
structure KEspacioVectorial (K : Type _) [Field K] (V : Type _) where
  add  : V → V → V
  smul : K → V → V

  ev1_add_assoc  : ∀ u v w : V, add (add u v) w = add u (add v w)
  ev2_add_comm   : ∀ v w : V, add v w = add w v
  ev3_ev4        : ∃ (zero : V), EsNeutroSuma add zero ∧ (∀ v : V, ∃ neg_v : V, EsOpuestoSuma add zero v neg_v)
  ev5_smul_assoc : ∀ («λ» μ : K) (v : V), smul («λ» * μ) v = smul «λ» (smul μ v)
  ev6_one_smul   : ∀ v : V, smul 1 v = v
  ev7_smul_add   : ∀ («λ» : K) (v w : V), smul «λ» (add v w) = add (smul «λ» v) (smul «λ» w)
  ev8_add_smul   : ∀ («λ» μ : K) (v : V), smul («λ» + μ) v = add (smul «λ» v) (smul μ v)


