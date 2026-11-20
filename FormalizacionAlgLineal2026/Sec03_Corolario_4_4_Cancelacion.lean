import FormalizacionAlgLineal2026.Sec02_Proposicion_4_3_UnicidadNeutroOpuesto

/-!
====================================================================
3. COROLARIO 4.4: CANCELACIÓN DE LA SUMA
====================================================================

"Corolario 4.4 (Cancelación de la suma). Sea (V, +, ·) un ℝ-espacio vectorial.
Para cualesquiera u, v, w ∈ V, si u + v = u + w, entonces v = w.

Demostración: Basta con sumar -u a la ecuación, lo que no cambia la igualdad."
-/

/-- Ley de cancelación aditiva (Corolario 4.4). -/
theorem corolario_4_4_cancelacion {V : Type _} (add : V → V → V)
    (add_assoc : ∀ u v w : V, add (add u v) w = add u (add v w))
    (add_comm : ∀ v w : V, add v w = add w v)
    (z : V) (hz : EsNeutroSuma add z)
    (u v w neg_u : V)
    (h_neg : EsOpuestoSuma add z u neg_u)
    (h : add u v = add u w) :
    v = w := by
  have hz_left : ∀ x : V, add z x = x := by
    intro x
    rw [add_comm]
    exact hz x
  have h_neg_comm : add neg_u u = z := by
    rw [add_comm]
    exact h_neg
  calc
    v = add z v             := (hz_left v).symm
    _ = add (add neg_u u) v := congrArg (fun t => add t v) h_neg_comm.symm
    _ = add neg_u (add u v) := add_assoc neg_u u v
    _ = add neg_u (add u w) := congrArg (fun t => add neg_u t) h
    _ = add (add neg_u u) w := (add_assoc neg_u u w).symm
    _ = add z w             := congrArg (fun t => add t w) h_neg_comm
    _ = w                   := hz_left w


