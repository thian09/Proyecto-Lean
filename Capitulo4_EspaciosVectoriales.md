# Capítulo 4: Espacios vectoriales

**Fuente:** *Notas de Álgebra Lineal I* (FCIEN UdelaR 2026)  
**Autor:** Eris Rocha Walchek  
**Versión para formalización en Lean** (Teoría pura: Definiciones, Proposiciones, Teoremas, Corolarios y Demostraciones)

---

## 4. Axiomática de los espacios vectoriales

### Definición 4.1 (Espacio vectorial)

> **Definición 4.1 (Espacio vectorial).** Un **espacio vectorial** sobre un cuerpo $\mathbb{K}$ (o $\mathbb{K}$-espacio vectorial) es una estructura algebraica $(V, +, \cdot)$ constituida por un conjunto $V$, una operación binaria interna $+: V \times V \to V$ (suma de vectores) y una operación externa $\cdot: \mathbb{K} \times V \to V$ (producto por escalar) que satisfacen los siguientes ocho axiomas:
>
> - **EV1. Asociatividad de la suma:**  
>   $$(u + v) + w = u + (v + w), \quad \forall u, v, w \in V;$$
> - **EV2. Conmutatividad de la suma:**  
>   $$v + w = w + v, \quad \forall v, w \in V;$$
> - **EV3. Elemento neutro de la suma:**  
>   $$\exists 0_V \in V \text{ tal que } v + 0_V = v, \quad \forall v \in V;$$
> - **EV4. Opuesto aditivo:**  
>   $$\forall v \in V, \, \exists -v \in V \text{ tal que } v + (-v) = 0_V;$$
> - **EV5. Asociatividad del producto por escalar:**  
>   $$(\lambda \mu) \cdot v = \lambda \cdot (\mu \cdot v), \quad \forall v \in V, \, \forall \lambda, \mu \in \mathbb{K};$$
> - **EV6. Elemento neutro del producto por escalar:**  
>   $$1_\mathbb{K} \cdot v = v, \quad \forall v \in V;$$
> - **EV7. Distributividad respecto de la suma de vectores:**  
>   $$\lambda \cdot (v + w) = \lambda \cdot v + \lambda \cdot w, \quad \forall v, w \in V, \, \forall \lambda \in \mathbb{K};$$
> - **EV8. Distributividad respecto de la suma de escalares:**  
>   $$(\lambda + \mu) \cdot v = \lambda \cdot v + \mu \cdot v, \quad \forall v \in V, \, \forall \lambda, \mu \in \mathbb{K}. \quad \blacklozenge$$

> **Observación 4.2 (Notación y generalidad del cuerpo).**
> - Los elementos de $V$ se denominan **vectores** y los elementos del cuerpo base $\mathbb{K}$ (tomado usualmente como $\mathbb{R}$) se denominan **escalares**.
> - Cuando las operaciones se sobrentienden por el contexto, se denota al espacio vectorial simplemente por el conjunto subyacente $V$.

---

### Proposición 4.3 (Unicidad del elemento neutro y del opuesto)

> **Proposición 4.3 (Unicidad del neutro y del opuesto).** Sea $(V, +, \cdot)$ un espacio vectorial sobre $\mathbb{K}$.
> 1. El elemento neutro de la suma es único.
> 2. Para cada vector $v \in V$, su opuesto aditivo es único.

#### Demostración
1. **Unicidad del neutro:** Supongamos que existen dos elementos neutros $0_V, 0'_V \in V$. Por ser $0'_V$ neutro aditivo, se tiene $0_V + 0'_V = 0_V$. Por ser $0_V$ neutro aditivo y por conmutatividad (EV2), $0_V + 0'_V = 0'_V$. En consecuencia:
   $$0_V = 0_V + 0'_V = 0'_V.$$
2. **Unicidad del opuesto:** Sea $v \in V$. Supongamos que existen dos opuestos aditivos $-v$ y $-v'$ para $v$. Por definición (EV4), $v + (-v) = 0_V$ y $v + (-v') = 0_V$. Sumando $-v$ por la izquierda a ambos miembros y usando asociatividad (EV1) y conmutatividad (EV2):
   $$-v = -v + 0_V = -v + (v + (-v')) = (-v + v) + (-v') = 0_V + (-v') = -v'.$$
   Por lo tanto, el elemento opuesto es único. $\clubsuit$

---

### Corolario 4.4 (Ley de cancelación de la suma)

> **Corolario 4.4 (Cancelación de la suma).** Sea $(V, +, \cdot)$ un espacio vectorial sobre $\mathbb{K}$. Para cualesquiera $u, v, w \in V$:
> $$u + v = u + w \iff v = w.$$

#### Demostración
($\implies$) Supongamos que $u + v = u + w$. Sumando el opuesto $-u$ a ambos miembros:
$$-u + (u + v) = -u + (u + w).$$
Aplicando la asociatividad (EV1) y la propiedad del opuesto (EV4):
$$(-u + u) + v = (-u + u) + w \implies 0_V + v = 0_V + w.$$
Por la propiedad del neutro (EV3), se concluye $v = w$.  
($\impliedby$) Es inmediato por la buena definición de la operación $+$. $\clubsuit$

---

### Proposición 4.5 (Propiedades aritméticas elementales)

> **Proposición 4.5 (Propiedades aritméticas).** Sea $(V, +, \cdot)$ un espacio vectorial sobre $\mathbb{K}$. Para todo $v \in V$ y todo $\lambda \in \mathbb{K}$:
> 1. $0_\mathbb{K} \cdot v = 0_V$;
> 2. $(-1_\mathbb{K}) \cdot v = -v$;
> 3. $\lambda \cdot 0_V = 0_V$;
> 4. $\lambda \cdot v = 0_V \implies \lambda = 0_\mathbb{K} \lor v = 0_V$.

#### Demostración
1. Utilizando EV6 y EV8:
   $$v = 1_\mathbb{K} \cdot v = (1_\mathbb{K} + 0_\mathbb{K}) \cdot v = 1_\mathbb{K} \cdot v + 0_\mathbb{K} \cdot v = v + 0_\mathbb{K} \cdot v.$$
   Por la ley de cancelación (Corolario 4.4), sumando $-v$:
   $$0_V = 0_\mathbb{K} \cdot v.$$
2. Por la propiedad del opuesto y el ítem 1:
   $$v + (-1_\mathbb{K}) \cdot v \stackrel{\text{EV6}}{=} 1_\mathbb{K} \cdot v + (-1_\mathbb{K}) \cdot v \stackrel{\text{EV8}}{=} (1_\mathbb{K} + (-1_\mathbb{K})) \cdot v = 0_\mathbb{K} \cdot v = 0_V.$$
   Por la unicidad del opuesto aditivo (Proposición 4.3), $(-1_\mathbb{K}) \cdot v = -v$.
3. Por ser $0_V$ elemento neutro, $0_V + 0_V = 0_V$. Aplicando EV7:
   $$\lambda \cdot 0_V = \lambda \cdot (0_V + 0_V) = \lambda \cdot 0_V + \lambda \cdot 0_V.$$
   Por la ley de cancelación (Corolario 4.4):
   $$\lambda \cdot 0_V = 0_V.$$
4. Supongamos que $\lambda \cdot v = 0_V$. Si $\lambda = 0_\mathbb{K}$, la afirmación se cumple. Si $\lambda \neq 0_\mathbb{K}$, existe el inverso multiplicativo $\lambda^{-1} \in \mathbb{K}$. Multiplicando por $\lambda^{-1}$:
   $$v \stackrel{\text{EV6}}{=} 1_\mathbb{K} \cdot v = (\lambda^{-1} \lambda) \cdot v \stackrel{\text{EV5}}{=} \lambda^{-1} \cdot (\lambda \cdot v) = \lambda^{-1} \cdot 0_V \stackrel{\text{3}}{=} 0_V.$$
   Luego, $\lambda = 0_\mathbb{K}$ o $v = 0_V$. $\clubsuit$

---

## 4.1. Subespacios vectoriales

### Definición 4.6 (Subespacio vectorial)

> **Definición 4.6 (Subespacio vectorial).** Sea $(V, +, \cdot)$ un espacio vectorial sobre $\mathbb{K}$. Un subconjunto $W \subseteq V$ es un **subespacio vectorial** de $V$ si satisface las siguientes tres condiciones:
> 1. **Contiene al vector nulo:** $0_V \in W$;
> 2. **Clausura bajo la suma:** $\forall w_1, w_2 \in W, \, w_1 + w_2 \in W$;
> 3. **Clausura bajo el producto por escalar:** $\forall w \in W, \, \forall \lambda \in \mathbb{K}, \, \lambda \cdot w \in W$. $\blacklozenge$

> **Observación 4.7.** Todo subespacio vectorial $W$ de $V$, dotado de las restricciones de las operaciones de $V$, es en sí mismo un espacio vectorial sobre $\mathbb{K}$. Para todo espacio vectorial $V$, los subconjuntos $\{0_V\}$ y $V$ son siempre subespacios vectoriales (subespacios triviales).

---

## 4.2. Construcción de espacios vectoriales canónicos

### 4.2.1. Espacio de matrices
El conjunto $\operatorname{Mat}_{m \times n}(\mathbb{K})$ de las matrices de orden $m \times n$ con coeficientes en $\mathbb{K}$, provisto de la suma de matrices término a término $(A + B)_{ij} = A_{ij} + B_{ij}$ y del producto por escalar $(\lambda A)_{ij} = \lambda A_{ij}$, es un espacio vectorial sobre $\mathbb{K}$, cuyo elemento neutro es la matriz nula $0_{m \times n}$.

### 4.2.2. Espacio de funciones
Sean $A$ un conjunto no vacío y $V$ un espacio vectorial sobre $\mathbb{K}$. El conjunto de todas las funciones de $A$ en $V$, denotado $\mathcal{F}(A, V)$ o $V^A$, es un espacio vectorial sobre $\mathbb{K}$ con las operaciones punto a punto:
- **Suma:** $(f + g)(a) \stackrel{\text{def}}{=} f(a) +_V g(a), \quad \forall a \in A$;
- **Producto por escalar:** $(\lambda \cdot f)(a) \stackrel{\text{def}}{=} \lambda \cdot_V f(a), \quad \forall a \in A, \, \forall \lambda \in \mathbb{K}$.

El elemento neutro aditivo es la función constante nula $0_{V^A}(a) = 0_V$ para todo $a \in A$.

### 4.2.3. Espacios de polinomios
El conjunto $\mathbb{K}[x]$ de polinomios en una indeterminada con coeficientes en $\mathbb{K}$ es un espacio vectorial sobre $\mathbb{K}$ respecto a la adición y producto por escalar canónicos. De igual forma, el conjunto de polinomios en varias variables $\mathbb{K}[x_1, \dots, x_n]$ y el conjunto de polinomios homogéneos de grado $d$, denotado $\mathbb{K}[x_1, \dots, x_n]^{=d}$, constituyen espacios vectoriales sobre $\mathbb{K}$.

### 4.2.4. Espacio de sucesiones
El conjunto de todas las sucesiones con valores en $\mathbb{K}$, denotado $\mathbb{K}^\mathbb{N} = \mathcal{F}(\mathbb{N}, \mathbb{K})$, es un espacio vectorial sobre $\mathbb{K}$ bajo las operaciones término a término:
$$(a_n)_{n \in \mathbb{N}} + (b_n)_{n \in \mathbb{N}} \stackrel{\text{def}}{=} (a_n + b_n)_{n \in \mathbb{N}}, \qquad \lambda \cdot (a_n)_{n \in \mathbb{N}} \stackrel{\text{def}}{=} (\lambda a_n)_{n \in \mathbb{N}}.$$

### 4.2.5. Transporte de estructura mediante biyección
> **Proposición (Transporte de estructura).** Sean $(V, +_V, \cdot_V)$ un $\mathbb{K}$-espacio vectorial, $S$ un conjunto y $f: S \to V$ una biyección. Definiendo en $S$ las operaciones:
> $$s_1 +_S s_2 \stackrel{\text{def}}{=} f^{-1}(f(s_1) +_V f(s_2)), \qquad \lambda \cdot_S s \stackrel{\text{def}}{=} f^{-1}(\lambda \cdot_V f(s)),$$
> la estructura $(S, +_S, \cdot_S)$ es un $\mathbb{K}$-espacio vectorial con neutro $0_S = f^{-1}(0_V)$ y opuesto $-s = f^{-1}(-f(s))$.

---

## 4.3. Operaciones con subespacios

### Definición 4.20 (Intersección de subespacios vectoriales)

> **Definición 4.20 (Intersección de subespacios).** Sea $V$ un espacio vectorial sobre $\mathbb{K}$.
> 1. Si $W_1, W_2 \subseteq V$ son subespacios vectoriales de $V$, su **intersección** es:
>    $$W_1 \cap W_2 \stackrel{\text{def}}{=} \{v \in V : v \in W_1 \land v \in W_2\}.$$
> 2. Si $\{W_i\}_{i \in I}$ es una familia arbitraria de subespacios vectoriales de $V$ (donde $I$ es un conjunto de índices arbitrario), su **intersección** es:
>    $$\bigcap_{i \in I} W_i \stackrel{\text{def}}{=} \{v \in V : \forall i \in I, \, v \in W_i\}. \quad \blacklozenge$$

---

### Proposición 4.21 (La intersección de subespacios es un subespacio)

> **Proposición 4.21.** Sea $V$ un espacio vectorial sobre $\mathbb{K}$ y sea $\{W_i\}_{i \in I}$ una familia arbitraria de subespacios vectoriales de $V$. Entonces la intersección $\bigcap_{i \in I} W_i$ es un subespacio vectorial de $V$. En particular, si $W_1, W_2$ son subespacios de $V$, $W_1 \cap W_2$ es un subespacio vectorial de $V$.

#### Demostración
Verificamos las tres condiciones de la Definición 4.6 para $W = \bigcap_{i \in I} W_i$:
1. **Elemento neutro:** Como cada $W_i$ es subespacio vectorial de $V$, $0_V \in W_i$ para todo $i \in I$. En consecuencia, $0_V \in \bigcap_{i \in I} W_i$.
2. **Clausura bajo la suma:** Sean $u, v \in \bigcap_{i \in I} W_i$. Por definición de intersección, $u \in W_i$ y $v \in W_i$ para todo $i \in I$. Dado que cada $W_i$ es subespacio vectorial, es cerrado bajo la suma, de modo que $u + v \in W_i$ para todo $i \in I$. Por tanto, $u + v \in \bigcap_{i \in I} W_i$.
3. **Clausura bajo producto por escalar:** Sean $u \in \bigcap_{i \in I} W_i$ y $\lambda \in \mathbb{K}$. Entonces $u \in W_i$ para todo $i \in I$. Como cada $W_i$ es subespacio vectorial, $\lambda \cdot u \in W_i$ para todo $i \in I$. Por lo tanto, $\lambda \cdot u \in \bigcap_{i \in I} W_i$.

Se concluye que $\bigcap_{i \in I} W_i$ es un subespacio vectorial de $V$. $\clubsuit$

> **Observación 4.22.** Para todo $j \in I$, $\bigcap_{i \in I} W_i \subseteq W_j$, y por consiguiente $\bigcap_{i \in I} W_i$ es también subespacio vectorial de cada $W_j$.

---

### Definición 4.25 (Suma de subespacios vectoriales)

> **Definición 4.25 (Suma de subespacios).** Sea $V$ un espacio vectorial sobre $\mathbb{K}$.
> 1. Si $W_1, W_2 \subseteq V$ son subespacios vectoriales de $V$, la **suma** de $W_1$ y $W_2$ es:
>    $$W_1 + W_2 \stackrel{\text{def}}{=} \{v \in V : \exists w_1 \in W_1, \, \exists w_2 \in W_2, \, v = w_1 + w_2\}.$$
> 2. Si $\{W_i\}_{i \in I}$ es una familia arbitraria de subespacios vectoriales de $V$, la **suma** de la familia es el conjunto de combinaciones de sumas finitas de elementos de los subespacios:
>    $$\sum_{i \in I} W_i \stackrel{\text{def}}{=} \left\{v \in V : v = \sum_{i \in I} w_i, \text{ donde } w_i \in W_i \text{ para todo } i \in I \text{ y } \{i \in I : w_i \neq 0_V\} \text{ es finito}\right\}. \quad \blacklozenge$$

> **Observación 4.26.**
> - La suma $\sum_{i \in I} W_i$ coincide con el menor subespacio vectorial de $V$ que contiene a la unión $\bigcup_{i \in I} W_i$.
> - Cuando la familia de sumandos no nulos es vacía, el valor de la suma se define como el vector nulo $0_V$.

---

### Proposición 4.27 (La suma de subespacios es un subespacio)

> **Proposición 4.27.** Sea $V$ un espacio vectorial sobre $\mathbb{K}$ y sea $\{W_i\}_{i \in I}$ una familia arbitraria de subespacios vectoriales de $V$. Entonces $\sum_{i \in I} W_i$ es un subespacio vectorial de $V$. En particular, si $W_1, W_2$ son subespacios de $V$, $W_1 + W_2$ es un subespacio vectorial de $V$.

#### Demostración
Verificamos las tres condiciones de la Definición 4.6 para $\sum_{i \in I} W_i$:
1. **Elemento neutro:** Tomando $w_i = 0_V \in W_i$ para todo $i \in I$, el conjunto de índices con $w_i \neq 0_V$ es $\emptyset$ (finito), y $\sum_{i \in I} 0_V = 0_V$. Así, $0_V \in \sum_{i \in I} W_i$.
2. **Clausura bajo la suma:** Sean $u, v \in \sum_{i \in I} W_i$. Existen familias $\{u_i\}_{i \in I}$ y $\{v_i\}_{i \in I}$ con $u_i, v_i \in W_i$, y subconjuntos finitos de soporte $J_1, J_2 \subseteq I$ tales que $u_i = 0_V$ para $i \notin J_1$ y $v_i = 0_V$ para $i \notin J_2$, cumpliendo:
   $$u = \sum_{i \in I} u_i, \qquad v = \sum_{i \in I} v_i.$$
   Entonces:
   $$u + v = \sum_{i \in I} (u_i + v_i).$$
   Para cada $i \in I$, $u_i + v_i \in W_i$ por ser $W_i$ subespacio. Además, si $i \notin J_1 \cup J_2$, entonces $u_i + v_i = 0_V + 0_V = 0_V$. Como la unión de dos conjuntos finitos $J_1 \cup J_2$ es finita, el soporte de $\{u_i + v_i\}_{i \in I}$ es finito. Luego, $u + v \in \sum_{i \in I} W_i$.
3. **Clausura bajo producto por escalar:** Sean $u = \sum_{i \in I} u_i \in \sum_{i \in I} W_i$ y $\lambda \in \mathbb{K}$. Entonces:
   $$\lambda \cdot u = \lambda \cdot \left(\sum_{i \in I} u_i\right) = \sum_{i \in I} (\lambda \cdot u_i).$$
   Como cada $W_i$ es subespacio, $\lambda \cdot u_i \in W_i$. Además, si $u_i = 0_V$, entonces $\lambda \cdot u_i = 0_V$, por lo que el soporte de $\{\lambda \cdot u_i\}_{i \in I}$ está contenido en el soporte finito de $\{u_i\}_{i \in I}$ y es, por tanto, finito. Así, $\lambda \cdot u \in \sum_{i \in I} W_i$.

En conclusión, $\sum_{i \in I} W_i$ es un subespacio vectorial de $V$. $\clubsuit$

> **Observación 4.28.** Para todo $j \in I$, $W_j \subseteq \sum_{i \in I} W_i$. Por lo tanto, cada $W_j$ es un subespacio vectorial de $\sum_{i \in I} W_i$.

---

### Definición 4.33 (Suma directa binaria)

> **Definición 4.33 (Suma directa binaria).** Sean $W_1$ y $W_2$ subespacios vectoriales de un espacio vectorial $V$. Se dice que la suma $W_1 + W_2$ es una **suma directa** si:
> $$W_1 \cap W_2 = \{0_V\}.$$
> En tal caso, la suma se denota por $W_1 \oplus W_2$. $\blacklozenge$

---

### Teorema 4.34 (Caracterización de la suma directa binaria por unicidad de descomposición)

> **Teorema 4.34 (Unicidad de descomposición en suma directa binaria).** Sean $W_1$ y $W_2$ subespacios vectoriales de un espacio vectorial $V$. La suma $W_1 + W_2$ es directa si, y sólo si, todo vector $v \in W_1 + W_2$ admite una descomposición única de la forma
> $$v = w_1 + w_2, \quad \text{con } w_1 \in W_1 \text{ y } w_2 \in W_2.$$
> Es decir, si $w_1 + w_2 = w'_1 + w'_2$ con $w_1, w'_1 \in W_1$ y $w_2, w'_2 \in W_2$, entonces $w_1 = w'_1$ y $w_2 = w'_2$.

#### Demostración
($\implies$) Supongamos que la suma es directa, es decir, $W_1 \cap W_2 = \{0_V\}$. Sea $v \in W_1 + W_2$ y supongamos que existen dos descomposiciones:
$$v = w_1 + w_2 = w'_1 + w'_2 \quad (w_1, w'_1 \in W_1, \, w_2, w'_2 \in W_2).$$
Restando términos a ambos lados:
$$w_1 - w'_1 = w'_2 - w_2.$$
Como $w_1, w'_1 \in W_1$ y $W_1$ es subespacio, $w_1 - w'_1 \in W_1$. Análogamente, como $w_2, w'_2 \in W_2$, $w'_2 - w_2 \in W_2$. Por la igualdad, dicho vector pertenece simultáneamente a $W_1$ y a $W_2$:
$$w_1 - w'_1 = w'_2 - w_2 \in W_1 \cap W_2.$$
Puesto que $W_1 \cap W_2 = \{0_V\}$, se deduce:
$$w_1 - w'_1 = 0_V \implies w_1 = w'_1, \qquad w'_2 - w_2 = 0_V \implies w_2 = w'_2.$$
Por lo tanto, la descomposición es única.

($\impliedby$) Supongamos que la descomposición de cada elemento en $W_1 + W_2$ es única. Sea $v \in W_1 \cap W_2$. Entonces podemos escribir el vector $v$ de dos maneras como suma de un elemento de $W_1$ y un elemento de $W_2$:
$$v = \underbrace{v}_{\in W_1} + \underbrace{0_V}_{\in W_2} \quad \text{y} \quad v = \underbrace{0_V}_{\in W_1} + \underbrace{v}_{\in W_2}.$$
Por la hipótesis de unicidad de la descomposición, se debe verificar la igualdad componente a componente:
$$v = 0_V.$$
En consecuencia, $W_1 \cap W_2 = \{0_V\}$, probando que la suma es directa. $\clubsuit$

---

### Definición 4.37 (Suma directa general)

> **Definición 4.37 (Suma directa general).** Sea $\{W_i\}_{i \in I}$ una familia arbitraria de subespacios vectoriales de un espacio vectorial $V$. Se dice que la suma $\sum_{i \in I} W_i$ es una **suma directa** si, para todo $i_0 \in I$:
> $$W_{i_0} \cap \left(\sum_{i \in I \setminus \{i_0\}} W_i\right) = \{0_V\}.$$
> En tal caso, la suma se denota por $\bigoplus_{i \in I} W_i$. $\blacklozenge$

> **Observación 4.36.** Para dos subespacios $\{W_1, W_2\}$, la condición general se reduce a $W_1 \cap W_2 = \{0_V\}$, coincidiendo exactamente con la Definición 4.33. Para una familia finita $\{W_1, \dots, W_k\}$, la condición exige que para cada $j \in \{1, \dots, k\}$:
> $$W_j \cap \left(\sum_{i \neq j} W_i\right) = \{0_V\}.$$

---

### Teorema 4.38 (Caracterización de la suma directa general por unicidad de descomposición)

> **Teorema 4.38 (Unicidad de descomposición en suma directa general).** Sea $\{W_i\}_{i \in I}$ una familia arbitraria de subespacios vectoriales de un espacio vectorial $V$. La suma $\sum_{i \in I} W_i$ es directa si, y sólo si, todo vector $v \in \sum_{i \in I} W_i$ se expresa de manera única como una familia de componentes $\{w_i\}_{i \in I}$ de soporte finito con $w_i \in W_i$ tal que:
> $$v = \sum_{i \in I} w_i.$$
> Es decir, si $\sum_{i \in I} w_i = \sum_{i \in I} w'_i$ con $w_i, w'_i \in W_i$ (ambas sumas de soporte finito), entonces $w_i = w'_i$ para todo $i \in I$.

#### Demostración
($\implies$) Supongamos que la suma es directa, es decir, para todo $i_0 \in I$:
$$W_{i_0} \cap \left(\sum_{i \in I \setminus \{i_0\}} W_i\right) = \{0_V\}.$$
Sea $v \in \bigoplus_{i \in I} W_i$ y supongamos que existen dos descomposiciones con soporte finito:
$$v = \sum_{i \in I} w_i = \sum_{i \in I} w'_i \quad (w_i, w'_i \in W_i).$$
Restando ambas expresiones:
$$0_V = \sum_{i \in I} (w_i - w'_i).$$
Fijemos un índice arbitrario $i_0 \in I$. Aislamos el término correspondiente a $i_0$:
$$w'_{i_0} - w_{i_0} = \sum_{i \in I \setminus \{i_0\}} (w_i - w'_i).$$
Notemos que:
- El miembro izquierdo pertenece a $W_{i_0}$ puesto que $w_{i_0}, w'_{i_0} \in W_{i_0}$.
- El miembro derecho es una suma finita de elementos en $W_i$ con $i \neq i_0$, por lo que pertenece a $\sum_{i \in I \setminus \{i_0\}} W_i$.

Por consiguiente:
$$w'_{i_0} - w_{i_0} \in W_{i_0} \cap \left(\sum_{i \in I \setminus \{i_0\}} W_i\right) = \{0_V\}.$$
Deducimos que $w'_{i_0} - w_{i_0} = 0_V$, es decir, $w_{i_0} = w'_{i_0}$. Como $i_0 \in I$ fue arbitrario, $w_i = w'_i$ para todo $i \in I$, garantizando la unicidad de la descomposición.

($\impliedby$) Supongamos que la descomposición de cada elemento en la suma es única. Sea $i_0 \in I$ arbitrario y sea
$$u \in W_{i_0} \cap \left(\sum_{i \in I \setminus \{i_0\}} W_i\right).$$
Por estar en la suma de los demás subespacios, existen $w_i \in W_i$ para $i \in I \setminus \{i_0\}$, casi todos nulos, tales que:
$$u = \sum_{i \in I \setminus \{i_0\}} w_i.$$
Definiendo $w_{i_0} = 0_V$, podemos expresar $u$ como:
$$u = 0_V + \sum_{i \in I \setminus \{i_0\}} w_i.$$
Por otra parte, como $u \in W_{i_0}$, podemos escribirlo como:
$$u = u + \sum_{i \in I \setminus \{i_0\}} 0_V.$$
Estas son dos descomposiciones de $u$ en $\sum_{i \in I} W_i$. Por la unicidad de la representación, las componentes en cada subespacio deben coincidir. En particular, comparando la componente correspondiente al índice $i_0$:
$$u = 0_V.$$
Por lo tanto:
$$W_{i_0} \cap \left(\sum_{i \in I \setminus \{i_0\}} W_i\right) = \{0_V\},$$
lo cual demuestra que la suma es directa. $\clubsuit$

---

### Corolario 4.39 (Intersección trivial en suma directa)

> **Corolario 4.39.** Sea $\{W_i\}_{i \in I}$ una familia arbitraria de subespacios vectoriales de un espacio vectorial $V$. Si la suma $\bigoplus_{i \in I} W_i$ es directa y $\#I \ge 2$, entonces la intersección de la familia es trivial:
> $$\bigcap_{i \in I} W_i = \{0_V\}.$$

#### Demostración
Sea $v \in \bigcap_{i \in I} W_i$. Tomemos dos índices distintos $j, k \in I$ ($j \neq k$). Como $v \in W_j$ y $v \in W_k \subseteq \sum_{i \in I \setminus \{j\}} W_i$, se tiene que:
$$v \in W_j \cap \left(\sum_{i \in I \setminus \{j\}} W_i\right).$$
Por ser la suma directa (Definición 4.37), esta intersección es $\{0_V\}$. Por lo tanto, $v = 0_V$. Concluimos que $\bigcap_{i \in I} W_i = \{0_V\}$. $\clubsuit$

---

### Observación 4.40 (Condición necesaria y contrarrecíproco)

> **Observación 4.40.**
> 1. El recíproco del Corolario 4.39 es **falso** en general para familias de 3 o más subespacios: tener $\bigcap_{i \in I} W_i = \{0_V\}$ (e incluso tener $W_j \cap W_k = \{0_V\}$ para todo $j \neq k$) **no** garantiza que la suma sea directa.
> 2. Por el contrarrecíproco del Corolario 4.39, si $\bigcap_{i \in I} W_i \neq \{0_V\}$, entonces la suma $\sum_{i \in I} W_i$ no es directa.
