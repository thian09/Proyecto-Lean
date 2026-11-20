import FormalizacionAlgLineal2026.Capitulo5.Sec32_Teorema_5_34_CompletamientoBases

/-!
====================================================================
32. PROPOSICIÓN 5.37
====================================================================
-/

/-- Proposición 5.37: #I ≤ #G para I LI y G generador.

### Justificación formal de la hipótesis `hNodup : I₀.Nodup`:
En esta formalización de Álgebra Lineal (sin Mathlib), los subconjuntos finitos de vectores
se representan mediante listas (`List V`) y la noción de pertenencia al conjunto se define
a través del predicado inducido `fun w => w ∈ L`.

Sin embargo, existe una discrepancia semántica fundamental entre listas y conjuntos:
- En una lista `L : List V`, `L.length` cuenta las posiciones totales (con multiplicidad).
- El predicado `fun w => w ∈ L` es idempotente respecto a elementos duplicados, por lo que
  colapsa múltiples ocurrencias de un mismo vector a un único elemento en el soporte.

Consecuencia sin la hipótesis `hNodup`:
Si $v \neq 0$ es un vector del espacio y tomamos $I_0 = [v, v, v]$ y $G = [v]$, entonces:
1. `fun w => w ∈ I₀` es el conjunto unitario $\{v\}$, que es linealmente independiente
   (`EsLI E (fun w => w ∈ I₀)` es verdadera).
2. `fun w => w ∈ G` genera el subespacio $\langle v \rangle$ (o todo el espacio si $\dim V = 1$).
3. No obstante, `I₀.length = 3` y `G.length = 1`.
El enunciado original sin `hNodup` permitiría concluir falsamente que $3 \le 1$,
lo cual deriva en una contradicción aritmética inmediata (`False`) haciendo el sistema inconsistente.

Por lo tanto, la hipótesis `hNodup : I₀.Nodup` (ausencia de elementos duplicados en la lista $I_0$)
es indispensable: garantiza que la longitud de la lista `I₀.length` coincida exactamente con la
cardinalidad matemática del conjunto soporte $\#\{w \in V \mid w \in I_0\}$.

(Nota: Para la lista generadora $G$, la presencia de duplicados sólo incrementaría `G.length`,
lo que no compromete la desigualdad $I_0.\text{length} \le G.\text{length}$; la restricción
`Nodup` es estrictamente requerida en el conjunto acotado superiormente $I_0$). -/
theorem prop_5_37 {V : Type _} (E : EspacioVectorial V)
    (I₀ : List V) (G : List V)
    (hNodup : I₀.Nodup)
    (hLI : EsLI E (fun w => w ∈ I₀))
    (hG : ∀ v : V, Gen E (fun w => w ∈ G) v) :
    I₀.length ≤ G.length := by
  rcases teorema_5_34_completamiento E I₀ G hLI hG with ⟨G', hG'_sub, hlen, _⟩
  have h_le : I₀.length ≤ G'.length := List.Nodup.length_le_of_subset hNodup hG'_sub
  rw [hlen] at h_le
  exact h_le


