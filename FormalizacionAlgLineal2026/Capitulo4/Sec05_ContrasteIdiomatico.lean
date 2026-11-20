import FormalizacionAlgLineal2026.Capitulo4.Sec04_Observacion_4_2_CuerpoArbitrario

/-!
====================================================================
5. CONTRASTE IDIOMÁTICO EN LEAN 4: FIRMA ALGEBRAICA COMPUTACIONAL
====================================================================

¿Por qué en Lean 4 / Mathlib los espacios vectoriales se definen empaquetando
`0 : V` y `- : V → V` en la signatura (`AddCommGroup V`) en vez de usar `∃` en `Prop`?

En la Teoría de Tipos (Cálculo de Construcciones Inductivas):
- Las proposiciones `∃ x, P x` residen en `Prop` (Sort 0).
- Por la regla de eliminación de universos de Lean, de una prueba de `∃ x, P x` en `Prop`
  NO se puede extraer computacionalmente el término `x` para producir datos en `Type`
  (salvo apelando al axioma de elección `Classical.choose`).
- Para que `0_V` y `-v` sean operaciones de primer orden evaluables por el kernel,
  la signatura algebraica universal enriquecida se define como:
-/

structure EspacioVectorialEmpaquetado (V : Type _) where
  add          : V → V → V
  zero         : V
  neg          : V → V
  smul         : ℝ → V → V

  -- EV1
  add_assoc    : ∀ u v w : V, add (add u v) w = add u (add v w)
  -- EV2
  add_comm     : ∀ v w : V, add v w = add w v
  -- EV3 (con el testigo 0 computacionalmente explícito)
  add_zero     : ∀ v : V, add v zero = v
  -- EV4 (con la operación unaria de inversión - computacionalmente explícita)
  add_left_neg : ∀ v : V, add (neg v) v = zero
  -- EV5
  smul_assoc   : ∀ («λ» μ : ℝ) (v : V), smul («λ» * μ) v = smul «λ» (smul μ v)
  -- EV6
  one_smul     : ∀ v : V, smul 1 v = v
  -- EV7
  smul_add     : ∀ («λ» : ℝ) (v w : V), smul «λ» (add v w) = add (smul «λ» v) (smul «λ» w)
  -- EV8
  add_smul     : ∀ («λ» μ : ℝ) (v : V), smul («λ» + μ) v = add (smul «λ» v) (smul μ v)



