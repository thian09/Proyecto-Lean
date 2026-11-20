import FormalizacionAlgLineal2026.AxiomasReales

/-!
====================================================================
1. DEFINICIÓN 4.1: ESPACIO VECTORIAL SOBRE ℝ
====================================================================

"Definición 4.1 (Espacio vectorial). Un espacio vectorial (sobre ℝ) es una
estructura algébrica (V, +, ·) consistiendo de un conjunto V provisto de
una suma +: V × V → V y un producto por escalar ·: ℝ × V → V que cumplen
las siguientes propiedades:
  EV1. Asociatividad de la suma: (u + v) + w = u + (v + w), ∀ u, v, w ∈ V;
  EV2. Conmutatividad de la suma: v + w = w + v, ∀ v, w ∈ V;
  EV3. Elemento neutro de la suma: existe 0_V tal que v + 0 = v para todo v ∈ V;
  EV4. Opuesto aditivo: Para cada v ∈ V, existe un vector -v tal que v + (-v) = 0;
  EV5. Asociatividad del producto por escalar: (λ μ) · v = λ · (μ · v), ∀ v ∈ V, ∀ λ, μ ∈ ℝ;
  EV6. Elemento neutro del producto por escalar: 1 · v = v, ∀ v ∈ V;
  EV7. Distributividad con relación a la suma de vectores: λ · (v + w) = λ · v + λ · w, ∀ v, w ∈ V, ∀ λ ∈ ℝ;
  EV8. Distributividad con relación a la suma de escalares: (λ + μ) · v = λ · v + μ · v, ∀ v ∈ V, ∀ λ, μ ∈ ℝ."
-/

-- Predicado auxiliar: z es neutro aditivo por derecha (v + z = v) según enuncia EV3
def EsNeutroSuma {V : Type _} (add : V → V → V) (z : V) : Prop :=
  ∀ v : V, add v z = v

-- Predicado auxiliar: neg_v es opuesto aditivo de v respecto a un neutro z (v + neg_v = z) según enuncia EV4
def EsOpuestoSuma {V : Type _} (add : V → V → V) (z : V) (v neg_v : V) : Prop :=
  add v neg_v = z

/-- Estructura algébrica (V, +, ·) de espacio vectorial sobre ℝ,
    fielmente transcrita de la Definición 4.1. -/
structure EspacioVectorial (V : Type _) where
  -- Datos de la terna (V, +, ·)
  add  : V → V → V
  smul : ℝ → V → V

  -- EV1. Asociatividad de la suma
  ev1_add_assoc : ∀ u v w : V, add (add u v) w = add u (add v w)

  -- EV2. Conmutatividad de la suma
  ev2_add_comm  : ∀ v w : V, add v w = add w v

  -- EV3 y EV4. Existencia de neutro aditivo y opuestos
  -- El texto afirma: existe 0_V con v + 0_V = v, y para cada v existe -v tal que v + (-v) = 0_V.
  -- Nótese que NO se pide la unicidad a priori (Observación 4.2).
  ev3_ev4 : ∃ (zero : V), EsNeutroSuma add zero ∧ (∀ v : V, ∃ neg_v : V, EsOpuestoSuma add zero v neg_v)

  -- EV5. Asociatividad del producto por escalar
  ev5_smul_assoc : ∀ («λ» μ : ℝ) (v : V), smul («λ» * μ) v = smul «λ» (smul μ v)

  -- EV6. Elemento neutro del producto por escalar
  ev6_one_smul : ∀ v : V, smul 1 v = v

  -- EV7. Distributividad con relación a la suma de vectores
  ev7_smul_add : ∀ («λ» : ℝ) (v w : V), smul «λ» (add v w) = add (smul «λ» v) (smul «λ» w)

  -- EV8. Distributividad con relación a la suma de escalares
  ev8_add_smul : ∀ («λ» μ : ℝ) (v : V), smul («λ» + μ) v = add (smul «λ» v) (smul μ v)


