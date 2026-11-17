# Capítulo 5: Generadores, (in)dependencia lineal y bases
**Fuente:** *Notas de Álgebra Lineal I* (FCIEN UdelaR 2026)  
**Autor:** Eris Rocha Walchek  
**Versión:** 27 de junio de 2026 (Páginas 157–193)

---

## Definición 5.1 (Combinación lineal)

> **Definición 5.1 (Combinación lineal).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Una **combinación lineal** de $v_1, \dots, v_n \in V$ es una expresión de la forma
> $$a_1 v_1 + \dots + a_n v_n, \quad \text{con } a_1, \dots, a_n \in \mathbb{R}. \quad \blacklozenge$$

> **Observación 5.2.** Combinaciones lineales serán *siempre finitas*, mismo que se traten de combinaciones lineales de elementos de un conjunto infinito.

---

## 5.1. Subespacio generado

### Definición 5.3 (Subespacio generado)

> **Definición 5.3 (Subespacio generado).** Sean $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial y $S \subseteq V$ un subconjunto. Definimos el **subespacio generado** por $S$ por
> $$\langle S \rangle_\mathbb{R} = \{v \in V : v = a_1 s_1 + \dots + a_n s_n, \text{ con } a_i \in \mathbb{R} \text{ y } s_i \in S\},$$
> es decir, es el conjunto de todas las combinaciones lineales finitas de elementos de $S$. Decimos que los elementos de $S$ son los **generadores** de $\langle S \rangle_\mathbb{R}$.
> 
> Si $S = \emptyset$, definimos $\langle \emptyset \rangle_\mathbb{R} = \{0\}. \quad \blacklozenge$

> **Observación 5.4 (Notación).** Otras notaciones posibles son $\operatorname{span}(S)$ (o $\operatorname{gen}(S)$ en español) o $\langle S \rangle$, omitiendo el cuerpo.

---

### Proposición 5.5

> **Proposición 5.5.** Sean $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial y $S \subseteq V$ un subconjunto. Entonces, $\langle S \rangle$ es un subespacio vectorial de $V$.

#### Demostración
Mostramos las tres condiciones de la definición 4.6:

I. Como $0_V = 0 \cdot s$ para cualquier $s \in S$, $0 \in \langle S \rangle_\mathbb{R}$;

II. Sean $v, w \in \langle S \rangle_\mathbb{R}$. Entonces
$$v = a_1 s_1 + \dots + a_n s_n \quad \text{y} \quad w = b_1 s'_1 + \dots + b_m s'_m,$$
con $a_1, \dots, a_n, b_1, \dots, b_m \in \mathbb{R}$ y $s_1, \dots, s_n, s'_1, \dots, s'_m \in S$. Así,
$$v + w = a_1 s_1 + \dots + a_n s_n + b_1 s'_1 + \dots + b_m s'_m$$
es una combinación lineal finita de elementos de $S$, luego $v + w \in \langle S \rangle_\mathbb{R}$;

III. Sean $v \in \langle S \rangle_\mathbb{R}$. Entonces
$$v = a_1 s_1 + \dots + a_n s_n,$$
con $a_1, \dots, a_n \in \mathbb{R}$ y $s_1, \dots, s_n \in S$. Para todo $\lambda \in \mathbb{R}$,
$$\lambda \cdot v = \lambda a_1 s_1 + \dots + \lambda a_n s_n$$
es una combinación lineal finita de elementos de $S$, luego $\lambda \cdot v \in \langle S \rangle_\mathbb{R}$. $\clubsuit$

---

### Proposición 5.7 (Propiedades del subespacio generado)

> **Proposición 5.7 (Propiedades del subespacio generado).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Para cualesquiera subconjuntos $S, T \subseteq V$:
> 
> I. $S \subseteq \langle S \rangle_\mathbb{R}$;  
> II. $S \subseteq T \implies \langle S \rangle_\mathbb{R} \subseteq \langle T \rangle_\mathbb{R}$;  
> III. $\langle S \rangle_\mathbb{R} = S$ si, y sólo si, $S$ es un subespacio vectorial de $V$;  
> IV. $\langle \langle S \rangle_\mathbb{R} \rangle_\mathbb{R} = \langle S \rangle_\mathbb{R}$.

#### Demostración
**(I.)** Cada $s \in S$ es una combinación lineal de si mismo con coeficiente $1$, y por lo tanto $s \in \langle S \rangle_\mathbb{R}$.

**(II.)** Una combinación lineal $v \in \langle S \rangle_\mathbb{R}$ de elementos de $S$, por $S \subseteq T$, es una combinación lineal de elementos de $T$, y por lo tanto, $v \in \langle T \rangle_\mathbb{R}$. Así, $\langle S \rangle_\mathbb{R} \subseteq \langle T \rangle_\mathbb{R}$.

**(III.)** La implicación directa es automática. Para la recíproca, por I, $\langle S \rangle_\mathbb{R} \supseteq S$. Para la otra inclusión, sea $v \in \langle S \rangle_\mathbb{R}$. Entonces
$$v = a_1 s_1 + \dots + a_n s_n,$$
con $a_1, \dots, a_n \in \mathbb{R}$ y $s_1, \dots, s_n \in S$. Como $S$ es un subespacio vectorial de $V$, es cerrado por la suma y el producto por escalar. En particular, cualquier combinación lineal de elementos de $S$, y por lo tanto $v$, pertenece a $S$.

**(IV.)** Se sigue de III ya que $\langle S \rangle_\mathbb{R}$ es un subespacio vectorial de $V$. $\clubsuit$

---

### Corolario 5.8

> **Corolario 5.8.** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $G$ genera $V = \langle G \rangle_\mathbb{R}$ y $G' \supseteq G$, entonces $G'$ también genera $V = \langle G' \rangle_\mathbb{R}$.

#### Demostración
Por II de la Proposición 5.7, $G \subseteq G' \implies V = \langle G \rangle_\mathbb{R} \subseteq \langle G' \rangle_\mathbb{R}$. Por otro lado, $\langle G' \rangle_\mathbb{R}$ es un subespacio vectorial de $V$, luego $\langle G' \rangle_\mathbb{R} \subseteq V$. Por lo tanto, $V = \langle G' \rangle_\mathbb{R}$. $\clubsuit$

---

### Teorema 5.9 ($\langle S \rangle_\mathbb{R}$ es el menor subespacio conteniendo $S$)

> **Teorema 5.9 ($\langle S \rangle_\mathbb{R}$ es el menor subespacio conteniendo $S$).** Sean $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial y $S \subseteq V$ un subconjunto. Entonces $\langle S \rangle_\mathbb{R}$ es la intersección de todos los subespacios de $V$ que contienen $S$:
> $$\langle S \rangle_\mathbb{R} = \bigcap_{\substack{S \subseteq W \\ W \text{ subespacio de } V}} W.$$
> En otras palabras, $\langle S \rangle_\mathbb{R}$ es el menor subespacio de $V$ conteniendo $S$.

#### Demostración
Mostraremos ambas las inclusiones:

($\subseteq$) Sea $v \in \langle S \rangle_\mathbb{R}$. Entonces
$$v = a_1 s_1 + \dots + a_n s_n$$
con $a_1, \dots, a_n \in \mathbb{R}$ y $s_1, \dots, s_n \in S$. Si $W$ es cualquier subespacio de $V$ conteniendo $S$, entonces $s_1, \dots, s_n \in W$. Por la clausura de las operaciones en $W$, concluimos que $v \in W$. Eso vale para todo $W$ conteniendo $S$, luego $\langle S \rangle_\mathbb{R} \subseteq \bigcap_{S \subseteq W \subseteq V}^{\text{sub}} W$.

($\supseteq$) Entre los subespacios de $V$ que contienen $S$ está el propio $\langle S \rangle_\mathbb{R}$. Como la intersección de los $W$ está contenida en todos los $W$ simultáneamente, $\langle S \rangle_\mathbb{R} \supseteq \bigcap_{S \subseteq W \subseteq V}^{\text{sub}} W$. $\clubsuit$

> **Observación 5.10.** El subespacio generado $\langle S \rangle_\mathbb{R}$ es, entonces, la “clausura lineal” de $S$ en $V$.

---

### Proposición 5.11 (Unión genera suma)

> **Proposición 5.11 (Unión genera suma).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $\mathcal{F} = \{W_i \subseteq V : i \in I\}$ es una familia arbitraria de subespacios vectoriales de $V$,
> $$\sum_{i \in I} W_i = \left\langle \bigcup_{i \in I} W_i \right\rangle_\mathbb{R}.$$
> Osea, la suma de los $W_i$ es el menor subespacio de $V$ que contiene todos los $W_i$.

#### Demostración
Mostraremos ambas las inclusiones:

($\subseteq$) Sea $w \in \sum_{i \in I} W_i$. Entonces se descompone en una suma finita $w = \sum_{i \in I} w_i$ con $w_i \in W_i \subseteq \bigcup_{i \in I} W_i$, que en particular es una combinación lineal, y por lo tanto, $w \in \langle \bigcup_{i \in I} W_i \rangle_\mathbb{R}$.

($\supseteq$) Sea $w \in \langle \bigcup_{i \in I} W_i \rangle_\mathbb{R}$. Entonces $w = a_{i_1} w_{i_1} + \dots + a_{i_n} w_{i_n}$ con $w_{i_k} \in W_{i_k}$. Pero $w'_{i_k} = a_{i_k} w_{i_k} \in W_{i_k}$ por la clausura del producto por escalar, luego, $w = w'_{i_1} + \dots + w'_{i_n} \in \sum_{i \in I} W_i$. $\clubsuit$

> **Observación 5.13.** Una formulación alternativa para la Proposición 5.11 es:  
> Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $\mathcal{F} = \{S_i \subseteq V : i \in I\}$ es una familia arbitraria de subconjuntos de $V$,
> $$\sum_{i \in I} \langle S_i \rangle_\mathbb{R} = \left\langle \bigcup_{i \in I} S_i \right\rangle_\mathbb{R}.$$
> Osea, la suma de los subespacios generados es el menor subespacio de $V$ que contiene todos los $S_i$.

---

## 5.2. (In)dependencia lineal

### Definición 5.15 ((In)dependencia lineal)

> **Definición 5.15 ((In)dependencia lineal).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Un subconjunto $S \subseteq V$ se dice **linealmente independiente (LI)** si toda combinación lineal que es nula es trivial, es decir:
> $$a_1 s_1 + \dots + a_n s_n = 0_V \text{ con } a_i \in \mathbb{R}, s_i \in S \implies a_1 = \dots = a_n = 0.$$
> Caso contrario, es decir, si existe una combinación lineal nula no trivial:
> $$\text{existen } s_1, \dots, s_n \in S \text{ con } a_1 s_1 + \dots + a_n s_n = 0_V \text{ y } a_i \neq 0 \text{ para algún } i \in \{1, \dots, n\},$$
> decimos que $S$ es **linealmente dependiente (LD)**.  
> Con tal definición, se sigue que $\emptyset$ es linealmente independiente. $\blacklozenge$

> **Observación 5.16.**  
> 1. Es importante notar que $S$ puede ser infinito, pero combinaciones lineales son “testeadas” para subconjuntos finitos de $S$, pues apenas combinaciones lineales finitas son posibles.  
> 2. Si $\{v_1, \dots, v_n\}$ es un conjunto LD, la existencia de una combinación lineal nula no trivial es equivalente a la posibilidad de expresar uno de los vectores que tenga un coeficiente no nulo (digamos $v_{i_0}$ es tal que $a_{i_0} \neq 0$) como una combinación lineal de los demás:
> $$a_1 v_1 + \dots + a_{i_0} v_{i_0} + \dots + a_n v_n = 0_V \iff v_{i_0} = -\frac{1}{a_{i_0}}(a_1 v_1 + \dots + a_{i_0-1} v_{i_0-1} + a_{i_0+1} v_{i_0+1} + \dots + a_n v_n).$$

> **Observación 5.17.** En la Definición 5.15 se trabaja con familias finitas de vectores extraídos de un conjunto, de modo que cada vector está asociado a un único coeficiente en la combinación lineal (los términos en la combinación lineal son vectores distintos dos a dos).

---

### Lema 5.20 ((In)dependencia lineal y inclusiones)

> **Lema 5.20 ((In)dependencia lineal y inclusiones).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial.
> 
> I. Si $I \subseteq V$ es LI y $I' \subseteq I$, entonces $I'$ es LI;  
> II. Si $D \subseteq V$ es LD y $D' \supseteq D$, entonces $D'$ es LD.

#### Demostración
(I.) Si $a_1 v_1 + \dots + a_n v_n = 0$ es cualquier combinación lineal nula de elementos en $I'$, por $I' \subseteq I$, es una combinación lineal nula de elementos en $I$, y por $I$ ser LI, es trivial. Luego $I'$ es LI.

(II.) Si $a_1 v_1 + \dots + a_n v_n = 0$ es una combinación lineal nula no trivial de elementos en $D$ (que existe por $D$ ser LD), entonces también lo es en $D' \supseteq D$, luego $D'$ es LD. $\clubsuit$

---

### Proposición 5.21 ((In)dependencia lineal al sacar vectores)

> **Proposición 5.21 ((In)dependencia lineal al sacar vectores).** Sean $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial y $S \subseteq V$ un subconjunto de $V$.
> 
> **(Versión LD)** Son equivalentes:  
> I. $S$ es LD;  
> II. Existe $s \in S$ tal que $s \in \langle S \setminus \{s\} \rangle_\mathbb{R}$;  
> III. Existe $s \in S$ tal que $\langle S \rangle_\mathbb{R} = \langle S \setminus \{s\} \rangle_\mathbb{R}$.
> 
> **(Versión LI)** Son equivalentes:  
> I'. $S$ es LI;  
> II'. Para todo $s \in S$, $s \notin \langle S \setminus \{s\} \rangle_\mathbb{R}$; *(en el texto original dice: «Existe $s \in S$ tal que $s \notin \langle S \setminus \{s\} \rangle_\mathbb{R}$», pero en la demostración se señala explícitamente que I', II' y III' son las negaciones lógicas de I, II y III)*;  
> III'. Para todo $s \in S$, $\langle S \rangle_\mathbb{R} \supsetneq \langle S \setminus \{s\} \rangle_\mathbb{R}$ *(en el texto original dice «Existe $s \in S$ tal que $\langle S \rangle_\mathbb{R} \supsetneq \langle S \setminus \{s\} \rangle_\mathbb{R}$»)*.
> 
> Además, las versiones LD y LI de este resultado son equivalentes entre si.

#### Demostración
Primero notamos que la versión LI es la contrarrecíproca de la versión LD: I', II' y III' son las negaciones de I, II y III respectivamente, así un triple de afirmaciones son equivalentes entre sí si y solo si, el triple de los contrarrecíprocos también lo es. Así, basta con mostrar la versión LD.

(I $\implies$ II) Si $S$ es LD, existe una combinación lineal nula no trivial $a_1 s_1 + \dots + a_n s_n = 0$ con $a_1, \dots, a_n \in \mathbb{R}$ no todos nulos y $s_1, \dots, s_n \in S$. Digamos, sin perdida de generalidad, que $a_1 \neq 0$. Así,
$$s_1 = -\frac{1}{a_1}(a_2 s_2 + \dots + a_n s_n) \in \langle S \setminus \{s_1\} \rangle_\mathbb{R}.$$

(II $\implies$ III) Por un lado, se sigue de Proposición 5.7.II que $S \setminus \{s\} \subseteq S \implies \langle S \setminus \{s\} \rangle_\mathbb{R} \subseteq \langle S \rangle_\mathbb{R}$. Por otro lado, como $s \in \langle S \setminus \{s\} \rangle_\mathbb{R}$, entonces $S \subseteq \langle S \setminus \{s\} \rangle_\mathbb{R}$ y de Proposición 5.7.II,IV,
$$S \subseteq \langle S \setminus \{s\} \rangle_\mathbb{R} \implies \langle S \rangle_\mathbb{R} \subseteq \langle \langle S \setminus \{s\} \rangle_\mathbb{R} \rangle_\mathbb{R} = \langle S \setminus \{s\} \rangle_\mathbb{R},$$
concluyendo la prueba de la igualdad.

(III $\implies$ I) Si $s = 0_V$, entonces $S$ es automáticamente LD (Ejemplo 5.18.1). Caso contrario, como $s \in \langle S \rangle_\mathbb{R} = \langle S \setminus \{s\} \rangle_\mathbb{R}$,
$$s = a_1 s_1 + \dots + a_n s_n, \quad a_1, \dots, a_n \in \mathbb{R} \text{ no todos nulos y } s_1, \dots, s_n \in S \setminus \{s\}.$$
Luego,
$$-s + a_1 s_1 + \dots + a_n s_n = 0$$
es una combinación lineal nula no trivial de elementos de $S$, y por lo tanto, $S$ es LD. $\clubsuit$

> **Observación 5.22.** La proposición anterior caracteriza conjuntos LD como conteniendo vectores “redundantes” que pueden ser eliminados sin perjudicar el espacio generado. También caracteriza conjuntos LI como los conjuntos en que todos los vectores son “necesarios”, y si falta uno, no es posible alcanzar todo el espacio generado original.

---

### Corolario 5.23 (Independencia lineal al añadir vectores)

> **Corolario 5.23 (Independencia lineal al añadir vectores).** Sean $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial, $I \subsetneq V$ un subconjunto LI de $V$ y $v_0 \in V \setminus I$.
> 
> **(Versión LD)** $I \cup \{v_0\}$ es LD si, y sólo si, $v_0 \in \langle I \rangle_\mathbb{R}$.  
> **(Versión LI)** $I \cup \{v_0\}$ es LI si, y sólo si, $v_0 \notin \langle I \rangle_\mathbb{R}$.

#### Demostración
Nuevamente, la versión LI es el contrarrecíproco de la versión LD, y por lo tanto son equivalentes, bastando con demostrar una de ellas.

Demostraremos la versión LD.

($\implies$) Como $I$ es LI y $I \cup \{v_0\}$ es LD, una combinación lineal nula no trivial en $I \cup \{v_0\}$ necesariamente involucra $v_0$ con coeficiente $a_0$ no nulo, caso contrario sería una combinación lineal nula no trivial de elementos en $I$ lo que contradice $I$ ser LI. Así, sea una tal combinación
$$a_0 v_0 + a_1 v_1 + \dots + a_n v_n = 0_V \implies v_0 = -\frac{1}{a_0}(a_1 v_1 + \dots + a_n v_n) \in \langle I \rangle_\mathbb{R}.$$

($\impliedby$) Como $v_0 = a_1 v_1 + \dots + a_n v_n \in \langle I \rangle_\mathbb{R}$,
$$v_0 - a_1 v_1 - \dots - a_n v_n = 0_V$$
es una combinación lineal nula no trivial de elementos en $I \cup \{v_0\}$, que es LD. $\clubsuit$

---

## 5.3. Bases

### Definición 5.24 (Base)

> **Definición 5.24 (Base).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Una **base** de $V$ es un subconjunto $B \subseteq V$ que es LI y genera $V$. $\blacklozenge$

---

### Teorema 5.26 (Definiciones equivalentes de base)

> **Teorema 5.26 (Definiciones equivalentes de base).** Sean $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial y $B$ un subconjunto de $V$. Son equivalentes:
> 
> I. $B$ es una base de $V$, es decir, $B$ es LI y genera $V$;
> 
> II. Para todo $v \in V$, existe una única forma de expresar $v$ como combinación lineal de elementos de $B$: para cada $b \in B$, existe $a_b \in \mathbb{R}$ tales que
> $$v = \sum_{b \in B} a_b \cdot b,$$
> con los $a_b$ “casi todos nulos”, es decir, $0 \le \#\{b \in B : a_b \neq 0\} < \infty$. En otras palabras, $v$ se expresa unicamente como combinación lineal finita de vectores en $B$;
> 
> III. $B$ genera $V = \langle B \rangle_\mathbb{R}$. Además, si $I \subsetneq B$ es un subconjunto propio de $B$, entonces $I$ no genera $V \supsetneq \langle I \rangle_\mathbb{R}$;
> 
> IV. $B$ es LI. Además, si $G \supsetneq B$ es un superconjunto propio de $B$, entonces $G$ no es LI.

#### Demostración
Mostraremos que I es equivalente a cada otra afirmación.

**(I $\implies$ II)** Es suficiente mostrar que
$$V = \bigoplus_{b \in B} \langle b \rangle_\mathbb{R},$$
ya que el Teorema 4.38 implica la existencia de una única descomposición de cada $v \in V$ en suma finita de elementos de la forma $a_b \cdot b \in \langle b \rangle_\mathbb{R}$ con $b \in B$, o sea, en combinación lineal finita de términos de $B$.

- **Suma:** Ya tenemos la inclusión $\sum_{b \in B} \langle b \rangle_\mathbb{R} \subseteq V$, por ser subespacio. Por otro lado, sea $v \in V$. Como $B$ es un generador de $V$, podemos expresar
$$v = \underbrace{a_1 b_1}_{\in \langle b_1 \rangle_\mathbb{R}} + \dots + \underbrace{a_n b_n}_{\in \langle b_n \rangle_\mathbb{R}} \in \langle b_1 \rangle_\mathbb{R} + \dots + \langle b_n \rangle_\mathbb{R} \subseteq \sum_{b \in B} \langle b \rangle_\mathbb{R},$$
lo que nos da la otra inclusión.

- **Suma directa:** Mostremos ahora que la suma $\sum_{b \in B} \langle b \rangle_\mathbb{R}$ es directa. Para eso, fijemos cada $b_0 \in B$ y investiguemos $b \in \langle b_0 \rangle_\mathbb{R} \cap \sum_{b \in B \setminus \{b_0\}} \langle b \rangle_\mathbb{R}$.  
Por un lado, $b = a_0 b_0$. Por otro lado, $b$ es una combinación lineal finita de elementos de $B \setminus \{b_0\}$, de donde
$$a_0 b_0 = \underbrace{a_1 b_1 + \dots + a_n b_n}_{\text{en } B \setminus \{b_0\}} \implies -a_0 b_0 + a_1 b_1 + \dots + a_n b_n = 0_V \stackrel{B \text{ es LI}}{\implies} a_0 = 0,$$
y luego $b = 0_V$. Por lo tanto, la suma es directa.

**(II $\implies$ I)** Si para todo $v \in V$ existe una única forma de exprimirlo como combinación lineal de términos de $B$, en particular existe una. Por lo tanto, $v \in \langle B \rangle_\mathbb{R} = V$.

Para mostrar que $B$ es LI, primero notamos que $0_V \notin B$, caso contrario ninguna expresión de $v$ en combinación de elementos de $B$ sería única: bastaría con añadir $a 0_V$ para cualquier $a \neq 0$ para obtener una otra expresión válida:
$$v = \underbrace{a_1 b_1 + \dots + a_n b_n}_{\text{expresión en términos de } b_1, \dots, b_n \in B} = \underbrace{a_1 b_1 + \dots + a_n b_n + a 0_V}_{\text{expresión en términos de } b_1, \dots, b_n, 0_V \in B};$$
las expresiones son distintas porque en la primera el coeficiente de $0_V$ es $0$ y en la segunda el coeficiente de $0_V$ es $a \neq 0$.

Sea una combinación lineal nula de términos distintos en $B$ dada por
$$a_1 b_1 + \dots + a_n b_n = 0_V.$$
Si tal combinación tuviera un coeficiente no nulo, entonces tendría por lo menos dos, caso contrario, sería del tipo $a_1 b_1 = 0$ con $a_1 \neq 0$ y eso implicaría $b_1 = 0_V \in B$, lo que ya mostramos no ser posible. Supongamos $a_1 \neq 0$. Entonces
$$b_1 = \underbrace{1 \cdot b_1}_{\text{expresión en términos de } b_1 \in B} = \underbrace{-\frac{1}{a_1}(a_2 b_2 + \dots + a_n b_n)}_{\text{expresión en términos de } b_2, \dots, b_n \in B}$$
son dos expresiones distintas de $b_1$, con términos en dos subconjuntos distintos de $B$, lo que contradice la unicidad de la expresión de cualquier $v \in V$ en combinación lineal de términos de $B$.

La contradicción viene de suponer que existieran coeficientes no nulos en la combinación lineal nula. Por lo tanto, concluimos que todos los coeficientes son nulos y $B$ es LI.

**(I $\implies$ III)** Sea $b \in B \setminus I$. Si $I$ generase $V$, entonces
$$b \in \langle I \rangle_\mathbb{R} \implies b = a_1 b_1 + \dots + a_n b_n, \quad \text{con } a_1, \dots, a_n \in \mathbb{R} \setminus \{0\} \text{ y } b_1, \dots, b_n \in I \subseteq B.$$
Pero, en ese caso,
$$b - a_1 b_1 - \dots - a_n b_n = 0_V$$
sería una combinación lineal nula de términos distintos en $B$ no trivial (ya que el coeficiente de $b$ es $1$), lo que contradice $B$ ser LI. Por lo tanto, $\langle I \rangle_\mathbb{R} \neq V$ y $I$ no genera $V$.

**(III $\implies$ I)** Queda mostrar que $B$ es LI. Supongamos que existiera una combinación lineal nula no trivial de distintos términos en $B$: $a_1 b_1 + \dots + a_n b_n = 0_V$. Podemos suponer todos los coeficientes no nulos. Si $n = 1$, osea, $a_1 b_1 = 0$, entonces $b_1 = 0_V$ y el subconjunto propio $B \setminus \{b_1\}$ de $B$ sería un generador de $V$, lo que contradice la hipótesis. Si $n > 1$, entonces
$$b_1 = -\frac{1}{a_1}(a_2 b_2 + \dots + a_n b_n) \neq 0_V \implies b_1 \in \langle B \setminus \{b_1\} \rangle_\mathbb{R}.$$
En ese caso el subconjunto propio $B \setminus \{b_1\}$ de $B$ también sería un generador de $V$: como $\langle B \rangle_\mathbb{R} = V$, todo vector $v \in V$ se puede escribir como
$$v = \alpha_1 b_1 + \alpha_2 b'_2 + \dots + \alpha_n b'_n = -\frac{\alpha_1}{a_1}(a_2 b_2 + \dots + a_n b_n) + \alpha_2 b'_2 + \dots + \alpha_n b'_n \in \langle B \setminus \{b_1\} \rangle_\mathbb{R},$$
lo que nuevamente contradice la hipótesis. Por lo tanto, tal combinación lineal nula no trivial no existe y $B$ es LI.

**(I $\implies$ IV)** Sea $g \in G \setminus B$. Entonces $g \in V = \langle B \rangle_\mathbb{R}$ y por lo tanto o $g = 0_V$, lo que ya hace con que $G$ sea LD, o $g \neq 0_V$ y podemos escribir
$$g = a_1 b_1 + \dots + a_n b_n$$
con los coeficientes que podemos suponer no nulos. Así,
$$g - a_1 b_1 - \dots - a_n b_n = 0_V$$
es una combinación lineal nula no trivial de distintos términos en $G$, que por lo tanto es LD.

**(IV $\implies$ I)** Queda mostrar que $B$ genera $V$. Si no generase, existiera $v \in V \setminus \langle B \rangle_\mathbb{R}$, haciendo con que $B \cup \{v\}$ fuera LI: de hecho, si
$$a v + a_1 b_1 + \dots + a_n b_n = 0_V$$
es una combinación lineal nula de distintos términos $b_1, \dots, b_n \in B$ y coeficientes $a, a_1, \dots, a_n$ no nulos, entonces o $a v = 0_V \implies v = 0_V$, que obviamente está en el generado por $B$, o
$$v = -\frac{1}{a}(a_1 b_1 + \dots + a_n b_n) \in \langle B \rangle_\mathbb{R},$$
nuevamente estando $v$ en el generado por $B$, una contradicción. Luego, una tal combinación lineal nula no trivial no es posible, y por lo tanto $B \cup \{v\}$ sería LI. Eso contradice la hipótesis, y esta contradicción viene de suponer la existencia de $v \in V \setminus \langle B \rangle_\mathbb{R}$. Por lo tanto, $\langle B \rangle_\mathbb{R} = V$. $\clubsuit$

> **Observación 5.27.**  
> 1. La condición III del Teorema 5.26 nos dice que la base es un generador minimal: cualquier subconjunto más chico no genera. Por otro lado, la condición IV nos dice que la base es un conjunto LI maximal: cualquier superconjunto más grande no es LI.  
> 2. Si $V = \{0\}$ es el $\mathbb{R}$-espacio vectorial trivial, $B = \emptyset$ cumple las condiciones I–IV del Teorema 5.26 por vacuidad, siendo la base de $V$.  
> 3. La versión anterior de este teorema pedía $V$ no trivial y $v \neq 0_V$ en II, pero eso se revela no ser necesario para la demostración.

> **Observación 5.28 (Prueba alternativa de I $\implies$ II sin usar suma directa).**  
> Suponemos $V$ no trivial.  
> Sea $v = 0_V$. Una expresión de $v$ en términos de $B$ existe (la con todos los coeficientes nulos). Que es única sigue de $B$ ser LI, ya que cualquier combinación lineal nos daría
> $$0_V = a_1 b_1 + \dots + a_n b_n \implies a_1 = \dots = a_n = 0.$$
> Sea $v \neq 0_V$. Mostraremos que la expresión de $v$ en términos de la base $B$ existe y después que es única.  
> Para verificar que existe, usamos que $B$ genera $V$ para notar que $v \in V = \langle B \rangle_\mathbb{R}$. Para verificar que es única, comparamos dos posibles expresiones
> $$v = a_1 b_1 + \dots + a_n b_n = a'_1 b'_1 + \dots + a'_m b'_m$$
> y notamos que
> $$v - v = 0 = a_1 b_1 + \dots + a_n b_n - a'_1 b'_1 - \dots - a'_m b'_m$$
> es una combinación lineal nula de términos en $B$. Queremos invocar la independencia lineal de $B$, pero podría pasar que algunos de los $b_i$ fueran iguales a algunos de los $b'_j$, y concluir de arriba que los coeficientes son cero sería tratar dos apariciones del mismo vector como términos distintos.  
> - Si todos los términos son distintos, es decir, $\{b_1, \dots, b_n\} \cap \{b'_1, \dots, b'_m\} = \emptyset$, entonces podemos usar directamente que $B$ es LI para concluir que $a_1 = \dots = a_n = a'_1 = \dots = a'_m = 0$, lo que resultaría en
> $$v = a_1 b_1 + \dots + a_n b_n = 0_V,$$
> una contradicción con $v \neq 0_V$.  
> - Si hay términos repetidos, digamos que hay $k \le \min\{n, m\}$ elementos entre los $b_1, \dots, b_n$ que coinciden con $k$ elementos entre los $b'_1, \dots, b'_m$ (como la expresión de $v$ presupone términos distintos, no es posible que un $b_i$ corresponda a mas de un $b'_j$ y viceversa). Podemos renombrar los elementos para que los $k$ primeros sean los correspondientes repetidos, es decir, $b_1 = b'_1, \dots, b_k = b'_k$ y los demás $b_{k+1}, \dots, b_n$ y $b'_{k+1}, \dots, b'_m$ (pudiendo incluso no existir) no tienen nada en común. Entonces,
> $$0 = (a_1 - a'_1)b_1 + \dots + (a_k - a'_k)b_k + a_{k+1}b_{k+1} + \dots + a_n b_n - a'_{k+1}b'_{k+1} - \dots - a'_m b'_m$$
> es una combinación lineal nula de términos distintos de $B$ (es decir, cada elemento de $B$ que aparece en la combinación está asociado a un único coeficiente), lo que nos permite invocar su independencia lineal para concluir que
> $$a_1 = a'_1, \dots, a_k = a'_k, \quad a_{k+1} = \dots = a_n = 0 \quad \text{y} \quad a'_{k+1} = \dots = a'_m = 0,$$
> lo que significa que las expresiones de $v$ consideradas son necesariamente iguales:
> $$v = a_1 b_1 + \dots + a_k b_k + 0 \cdot b_{k+1} + \dots + 0 \cdot b_n = a'_1 b'_1 + \dots + a'_k b'_k + 0 \cdot b'_{k+1} + \dots + 0 \cdot b'_m.$$
> En todo caso, la expresión de $v \neq 0_V$ como combinación lineal de elementos de $B$ es única.

---

### 5.3.1. Espacios finitamente generados

#### Definición 5.29 (Espacio finitamente generado)

> **Definición 5.29 (Espacio finitamente generado).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Decimos que $V$ es **finitamente generado (FG)** si existe un generador $G$ de $V$ tal que $\#G < \infty$. $\blacklozenge$

---

#### Teorema 5.30 (Todo espacio FG tiene base)

> **Teorema 5.30 (Todo espacio FG tiene base).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial finitamente generado. Si $G$ es un generador finito de $V$, entonces existe un subconjunto $G' \subseteq G$ que es una base de $V$.  
> En particular, $V$ admite una base finita.

##### Demostración
La idea es empezar con un generador $G$ de $V$ y sacar tantos elementos cuanto necesarios para que $G$ se vuelva LI, y por lo tanto sea una base.

Sea $G$ un generador finito de $V$. Si $G$ es LI, entonces $G$ es ya base y concluimos. Caso contrario, $G$ es LD, y por lo tanto, existe $g_1 \in G$ tal que $g_1 \in \langle G \setminus \{g_1\} \rangle_\mathbb{R}$ (Corolario 5.23, versión LD) y lo sacamos, obteniendo $G_1 = G \setminus \{g_1\}$, otro generador de $V$.

Si $G_1$ es LI, entonces $G_1$ es ya base y concluimos. Caso contrario, repetimos el procedimiento. Como $G$ es finito, el proceso también es finito, y por lo tanto termina en un cierto paso $k$, de donde existe $G_k = G \setminus \{g_1, \dots, g_k\}$ que genera $V$ y es LI, por lo tanto siendo una base de $V$. $\clubsuit$

> **Observación 5.31.** La demostración de 5.30 es recursiva, lo que significa que un paso del proceso está definido en términos del paso anterior, y que un paso inicial que empieza toda la recursión está bien definido.  
> En forma de algoritmo, la demostración del Teorema 5.30 se expresa así:
> - $G_0 \stackrel{\text{def}}{=} G$;
> - Para todo $k \in \{0, \dots, \#G\}$:
>   1. ¿Es $G_k$ LI? Si sí, **FIN**.
>   2. Si no, existe $g_k \in G_k$ tal que $\langle G_k \setminus \{g_k\} \rangle_\mathbb{R} = \langle G_k \rangle_\mathbb{R}$;
>   3. $G_{k+1} \stackrel{\text{def}}{=} G_k \setminus \{g_k\}$;
>   4. Incrementar $k$ a $k + 1$ y volver a 1.
> 
> Un procedimiento recursivo descrito por un algoritmo es una prueba válida si el algoritmo termina. En este caso, sabemos que el algoritmo termina porque en la peor de las hipótesis, sacamos todos los elementos de $G$ y nos quedamos con $\emptyset$, que es LI y por lo tanto cumple la condición que rompe el bucle.

---

#### Teorema 5.34 ((FG) Completamiento de bases)

> **Teorema 5.34 ((FG) Completamiento de bases).** Sean $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial finitamente generado, $I \subseteq V$ un subconjunto LI finito y $G$ un generador finito de $V$. Entonces, existe un generador $G'$ de $V$ tal que $I \subseteq G'$ y $\#G = \#G'$.  
> En particular, existe una base de $V$ que contiene $I$. En otras palabras, es posible completar $I$ hasta una base de $V$.

##### Demostración
Sea $G = \{g_1, \dots, g_n\}$ un generador finito de $V$ y $I = \{\iota_1, \dots, \iota_m\}$ un subconjunto LI finito de $V$. Entonces cada $\iota_i \in I$ se puede expresar como combinación lineal de los elementos en $G$:
$$\begin{cases}
\iota_1 = a_{11} g_1 + \dots + a_{1n} g_n \\
\vdots \\
\iota_m = a_{m1} g_1 + \dots + a_{mn} g_n.
\end{cases}$$
La idea ahora es “invertir el sistema”, sustituyendo inductivamente cada $g_i$ por $\iota_i$.

**Paso 1:** Empezamos con $\iota_1$. Como uno de los coeficientes $a_{1i}$ es no nulo, ya que $0_V \notin I$, podemos reordenar los $g_1, \dots, g_n$ para suponer $a_{11} \neq 0$:
$$\iota_1 = a_1^{(1)} g_1 + a_2^{(1)} g_2 + \dots + a_n^{(1)} g_n \implies g_1 = \frac{1}{a_1^{(1)}} \iota_1 - \frac{a_2^{(1)}}{a_1^{(1)}} g_2 - \dots - \frac{a_n^{(1)}}{a_1^{(1)}} g_n.$$
Así, cambiamos $G$ por $G_1 = \{\iota_1, g_2, \dots, g_n\}$.

Ahora mostraremos como ese proceso puede ser iterado para $1 < k \le \min\{m, n\}$ (notar que para que los procedimientos estén bien definidos, necesitamos $k \le m$ y $k \le n$).

**Paso $k$:** del paso $k - 1$, obtenemos
$$G_{k-1} = \{\iota_1, \dots, \iota_{k-1}, g_k, \dots, g_n\},$$
que es un generador de $V$ con cardinal $\#G$. Así, podemos expresar
$$\iota_k = a_1^{(k)} \iota_1 + \dots + a_{k-1}^{(k)} \iota_{k-1} + a_k^{(k)} g_k + \dots + a_n^{(k)} g_n.$$
Algún de los $g_k, \dots, g_n$ tiene un coeficiente no nulo: caso contrario, $\iota_k$ sería una combinación lineal de los $\iota_1, \dots, \iota_{k-1}$, lo que contradice $I$ ser LI. Reordenando los $g_k, \dots, g_n$, podemos suponer que $a_k^{(k)} \neq 0$ (notar que eso no afecta los $g_1, \dots, g_{k-1}$, no deshaciendo reordenaciones anteriores). Así,
$$g_k = -\frac{1}{a_k^{(k)}} (a_1^{(k)} \iota_1 + \dots + a_{k-1}^{(k)} \iota_{k-1} - \iota_k + a_{k+1}^{(k)} g_{k+1} + \dots + a_n^{(k)} g_n).$$
En particular, $G_k \stackrel{\text{def}}{=} \{\iota_1, \dots, \iota_k, g_{k+1}, \dots, g_n\}$ es un generador de $V$.

Notar que el paso $k - 1$ implica el paso $k$ para todo $1 \le k \le \min\{m, n\}$. Además, ya mostramos que el paso 1 es posible. Por inducción, el último paso, $k = \min\{m, n\}$, es posible. Mostraremos ahora que $\min\{m, n\} = m$, es decir, $m \le n$ y todos los $\iota_i \in I$ fueran usados.

Si $m > n$, eso significa que reemplazamos todos los $g_j$ con $\iota_i$, pero quedaron $\iota_{n+1}, \dots, \iota_m \in I$ sin usar. Por un lado, $G' = \{\iota_1, \dots, \iota_n\}$ es un generador de $V$, y entonces
$$\iota_m = a_1 \iota_1 + \dots + a_n \iota_n \iff a_1 \iota_1 + \dots + a_n \iota_n - \iota_m = 0,$$
que es una combinación lineal nula no trivial de elementos de $I$, contradiciendo $I$ ser LI. Luego, $m \le n$.

Finalmente, como $m \le n \implies \min\{m, n\} = m$ el último paso sustituyó el último $\iota_m$ por un $g_m$. Por lo tanto, $G' = G_m$ cumple las condiciones del enunciado.

Si no quedaron otros $g_m$, es decir, $m = n$ y $G_n = I$ es tanto LI cuanto un generador, ya tenemos una base. Caso contrario, $I \subseteq G_n = \{\iota_1, \dots, \iota_m, g_{m+1}, \dots, g_n\}$ es un generador de $V$ que contiene a $I$, con algunos $g_j$ sobresalientes.

Resta eliminar los redundantes, que necesariamente están entre los $g_{m+1}, \dots, g_n$ sobresalientes ya que los otros $\iota_1, \dots, \iota_m$ forman un conjunto LI. Usando la mesma técnica de la demostración del Teorema 5.30, sacamos vectores de $G_n$ hasta quedar con un subconjunto $G' \subseteq G_n$ que es una base de $V$. Notar que $I \subseteq G'$ ya que si uno de los $\iota_i$ está presente en una combinación lineal nula no trivial, necesariamente involucra algún $g_j \in G_n \setminus I$, que puede ser eliminado en su lugar. $\clubsuit$

> **Observación 5.35.** La recursión del paso $k$, escrita en detalles, se hace así:
> - $\iota_k$ se expresa en combinación lineal de $g_1, \dots, g_n$, escribimos $\iota_k = \operatorname{CombLin}(g_1, \dots, g_n)$ para evitar las expresiones explícitas.
> - El $g_1$ se expresa como $g_1 = \operatorname{CombLin}(\iota_1, g_2, \dots, g_n)$. Sustituyendo en la expresión de $\iota_k$, esto nos da
>   $$\iota_k = \operatorname{CombLin}(\iota_1, g_2, \dots, g_n).$$
> - En el paso $1 \le i \le k$, ya sustituimos los $g_1, \dots, g_{i-1}$ por $\iota_1, \dots, \iota_{i-1}$, pudiendo expresar
>   $$\iota_k = \operatorname{CombLin}(\iota_1, \dots, \iota_{i-1}, g_i, \dots, g_n).$$
>   Como $g_i = \operatorname{CombLin}(\iota_1, \dots, \iota_i, g_{i+1}, \dots, g_n)$, sustituyendo en la expresión de $\iota_k$, nos da
>   $$\iota_k = \operatorname{CombLin}(\iota_1, \dots, \iota_i, g_{i+1}, \dots, g_n).$$

---

### 5.3.2. Dimensión

#### Proposición 5.37

> **Proposición 5.37.** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial finitamente generado. Si $G$ es un generador de $V$ y $I \subseteq V$ es LI, entonces $\#I \le \#G$.

##### Demostración
Por el Teorema 5.34, es posible hallar un generador $G'$ tal que $I \subseteq G'$ y $\#G' = \#G$. Por lo tanto, $\#I \le \#G' = \#G$. $\clubsuit$

---

#### Proposición 5.38 (Toda base de un espacio FG tiene el mismo tamaño)

> **Proposición 5.38 (Toda base de un espacio FG tiene el mismo tamaño).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial finitamente generado. Si $B$ y $B'$ son bases de $V$, entonces $\#B = \#B'$.

##### Demostración
Sean $B$ y $B'$ dos bases. Como $B$ es LI y $B'$ es un generador, por la Proposición 5.37, $\#B \le \#B'$. Por otro lado, $B'$ es LI y $B$ es un generador, y por la misma proposición, $\#B \ge \#B'$. Por lo tanto, $\#B = \#B'$. $\clubsuit$

---

#### Definición 5.39 (Dimensión)

> **Definición 5.39 (Dimensión).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial.
> - Si $V$ es finitamente generado, llamamos **dimensión** al cardinal de cualquier base de $V$ (que es igual para todas las bases por la Proposición 5.38). Denotamos $\dim_\mathbb{R}(V)$, y frecuentemente denotamos $\dim_\mathbb{R}(V) < \infty$ para indicar que es finita.
> - Si $V$ no es finitamente generado, decimos que $V$ tiene **dimensión infinita**, y denotamos $\dim_\mathbb{R}(V) = \infty$. $\blacklozenge$

> **Observación 5.40.**  
> 1. Si el cuerpo está claro por el contexto, se puede omitirlo de la notación. La dimensión de un espacio depende del cuerpo base: por ejemplo, $\dim_\mathbb{R}(\mathbb{R}) = 1$, pero $\dim_\mathbb{Q}(\mathbb{R}) = \infty$.  
> 2. La dimensión del espacio trivial $V = \{0\}$ es $\dim(V) = \#\emptyset = 0$, y ese es el único espacio vectorial sobre $\mathbb{R}$ con tal dimensión.

---

#### Proposición 5.41

> **Proposición 5.41.** Sean $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial finitamente generado.
> 
> I. Si $I$ es un subconjunto LI de $V$, entonces $\#I \le \dim(V)$, siendo válida la igualdad si, y sólo si, $I$ es una base de $V$;  
> II. Si $G$ es un generador de $V$, entonces $\#G \ge \dim(V)$, siendo válida la igualdad si, y sólo si, $G$ es una base de $V$.

##### Demostración
(I.) Si $I$ es LI, por el Teorema de completamiento de bases (Teorema 5.34), existe una base $B$ tal que $I \subseteq B \implies \#I \le \#B = \dim(V)$.  
Para mostrar la equivalencia, si $\#I = \#B = \dim(V)$, entonces $I \subseteq B \implies I = B$ es una base. Por otro lado, si $I$ es una base, $\#I = \dim(V)$ por definición.

(II.) Si $G$ es un generador de $V$, por el Teorema 5.30, existe una base $B$ tal que $B \subseteq G \implies \#G \ge \#B = \dim(V)$. $\clubsuit$

> **Observación 5.42.**  
> 1. En particular, la Proposición 5.41 nos muestra que un subconjunto LI en un espacio vectorial finitamente generado es finito;  
> 2. La versión LD de la Proposición 5.41 es: si $D \subseteq V$ es tal que $\#D > \dim(V)$, entonces $D$ es LD.  
> 3. Usando la Proposición 5.37 y la Proposición 5.41, recuperamos la noción de base como un “equilibrio” entre la tendencia minimizadora de ser LI, y la tendencia maximizadora de ser un generador: si $I$ es un subconjunto LI y $G$ es un generador, entonces $\#I \le \dim(V) \le \#G$, y vale la igualdad si, y sólo si, ambos $I$ y $G$ son bases.

---

#### Corolario 5.43 ((FG) generar + dimensión = base; LI + dimensión = base)

> **Corolario 5.43 ((FG) generar + dimensión = base; LI + dimensión = base).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial finitamente generado.
> 
> I. Si $G$ genera $V$ y $\#G = \dim(V)$, entonces $G$ es una base de $V$;  
> II. Si $I \subseteq V$ es LI y $\#I = \dim(V)$, entonces $I$ es una base de $V$.

##### Demostración
Se sigue directamente de la Proposición 5.41. $\clubsuit$

---

### 5.3.3. Subespacios de espacios finitamente generados

#### Teorema 5.45 ((FG) Completamiento de bases de subespacios)

> **Teorema 5.45 ((FG) Completamiento de bases de subespacios).** Sean $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial finitamente generado y $W$ un subespacio vectorial. Si $B_W$ es una base de $W$, existe una base $B_V$ de $V$ tal que $B_W \subseteq B_V$.  
> En otras palabras, es posible completar una base de $W$ hasta una base de $V$.

##### Demostración
Eso es consecuencia del Teorema del Completamiento de bases (Teorema 5.34) para $I = B_W$, que es finito y LI. $\clubsuit$

---

#### Corolario 5.46

> **Corolario 5.46.** Sean $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial finitamente generado y $W$ un subespacio vectorial. Entonces $W$ es finitamente generado y $\dim_\mathbb{R}(W) \le \dim_\mathbb{R}(V)$, valiendo la igualdad si, y sólo si, $W = V$.

##### Demostración
Si $B_W$ es una base de $W$, por el Teorema 5.45, es posible completarla a una base $B_V$ de $V$. Así, $\dim_\mathbb{R}(W) = \#B_W \le \#B_V = \dim_\mathbb{R}(V)$.

Si $\#B_W = \#B_V$ y $B_W \subseteq B_V$, entonces $B_W = B_V \implies W = \langle B_W \rangle_\mathbb{R} = \langle B_V \rangle_\mathbb{R} = V$. La otra implicación es automática. $\clubsuit$

---

#### Teorema 5.48 ((FG), Dimensión de la suma de subespacios)

> **Teorema 5.48 ((FG), Dimensión de la suma de subespacios).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial finitamente generado. Si $W_1$ y $W_2$ son subespacios vectoriales de $V$,
> $$\dim(W_1 + W_2) = \dim(W_1) + \dim(W_2) - \dim(W_1 \cap W_2).$$
> En particular, si la suma es directa:
> $$\dim(W_1 \oplus W_2) = \dim(W_1) + \dim(W_2).$$

##### Demostración
Sea $B$ una base para $W_1 \cap W_2$. Como $W_1 \cap W_2$ es un subespacio tanto de $W_1$ cuanto de $W_2$, por el Teorema del completamiento de bases (Teorema 5.45), existen bases $B_1$ para $W_1$ y $B_2$ para $W_2$ tales que $B \subseteq B_1$ y $B \subseteq B_2$.

Por la Proposición 5.11, $W_1 + W_2 = \langle B_1 \cup B_2 \rangle_\mathbb{R}$. Mostraremos que $B_1 \cup B_2$ es LI para concluir que es una base de $W_1 + W_2$.

Para eso, vamos escribir $B = \{b_1, \dots, b_n\}$, $B_1 = \{b_1, \dots, b_n, b_{n+1}^{(1)}, \dots, b_{n+p}^{(1)}\}$ y $B_2 = \{b_1, \dots, b_n, b_{n+1}^{(2)}, \dots, b_{n+q}^{(2)}\}$. Tomamos una combinación lineal nula (notar que todos los términos son distintos):
$$\alpha_1 b_1 + \dots + \alpha_n b_n + \beta_1 b_{n+1}^{(1)} + \dots + \beta_p b_{n+p}^{(1)} + \gamma_1 b_{n+1}^{(2)} + \dots + \gamma_q b_{n+q}^{(2)} = 0.$$

Separando los términos en $B_1 \setminus B$, obtenemos
$$W_1 \ni \beta_1 b_{n+1}^{(1)} + \dots + \beta_p b_{n+p}^{(1)} = -(\alpha_1 b_1 + \dots + \alpha_n b_n + \gamma_1 b_{n+1}^{(2)} + \dots + \gamma_q b_{n+q}^{(2)}) \in W_2$$
$$\beta_1 b_{n+1}^{(1)} + \dots + \beta_p b_{n+p}^{(1)} \in W_1 \cap W_2.$$

Si algún $\beta_i$ fuera no nulo, entonces
$$\beta_1 b_{n+1}^{(1)} + \dots + \beta_p b_{n+p}^{(1)} = a_1 b_1 + \dots + a_n b_n \implies \beta_1 b_{n+1}^{(1)} + \dots + \beta_p b_{n+p}^{(1)} - a_1 b_1 - \dots - a_n b_n = 0$$
sería una combinación lineal nula no trivial de términos distintos en $B_1$, lo que no es posible por $B_1$ ser LI. Por lo tanto, $\beta_1 = \dots = \beta_p = 0$.

De la misma forma, separando los términos en $B_2 \setminus B$, obtenemos
$$W_2 \ni \gamma_1 b_{n+1}^{(2)} + \dots + \gamma_q b_{n+q}^{(2)} = -(\alpha_1 b_1 + \dots + \alpha_n b_n + \beta_1 b_{n+1}^{(1)} + \dots + \beta_p b_{n+p}^{(1)}) \in W_1,$$
y podemos concluir, usando un razonamiento análogo, que $\gamma_1 = \dots = \gamma_q = 0$.

Volviendo a la expresión original, quedamos con
$$\alpha_1 b_1 + \dots + \alpha_n b_n = 0 \implies \alpha_1 = \dots = \alpha_n = 0$$
pues $B$ es LI. Por lo tanto, la combinación lineal nula es trivial, y
$$B_1 \cup B_2 = \{b_1, \dots, b_n, b_{n+1}^{(1)}, \dots, b_{n+p}^{(1)}, b_{n+1}^{(2)}, \dots, b_{n+q}^{(2)}\}.$$

Por lo tanto, se sigue del principio de la inclusión-exclusión (Proposición A.1) que
$$\dim(W_1 + W_2) = \# B_1 \cup B_2 = \# B_1 + \# B_2 - \#(B_1 \cap B_2) = \dim(W_1) + \dim(W_2) - \dim(W_1 \cap W_2).$$

Si la suma es directa, entonces $W_1 \cap W_2 = \{0\} \implies \dim(W_1 \cap W_2) = 0$. $\clubsuit$

---

#### Corolario 5.49 ((FG) Completamiento de subespacios)

> **Corolario 5.49 ((FG) Completamiento de subespacios).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial finitamente generado. Para todo subespacio $W \subseteq V$, existe un subespacio $W' \subseteq V$ tal que $V = W \oplus W'$.

##### Demostración
Sea $B_W = \{b_1, \dots, b_m\}$ una base de $W$, que completamos para una base $B_V = \{b_1, \dots, b_m, b_{m+1}, \dots, b_n\}$ de $V$. Sea $W' = \langle B_V \setminus B_W \rangle_\mathbb{R}$. Entonces $W + W' = \langle B_W \cup (B_V \setminus B_W) \rangle_\mathbb{R} = \langle B_V \rangle_\mathbb{R} = V$. Además, si $v \in W \cap W'$, entonces
$$v = a_1 b_1 + \dots + a_m b_m = a_{m+1} b_{m+1} + \dots + a_n b_n \implies a_1 b_1 + \dots + a_m b_m - a_{m+1} b_{m+1} - \dots - a_n b_n = 0_V$$
es una combinación lineal nula con todos los términos distintos. Como $B_V$ es LI,
$$a_1 = \dots = a_m = a_{m+1} = \dots = a_n = 0 \implies v = 0_V.$$
Luego $W \cap W' = \{0_V\} \implies V = W \oplus W'$. $\clubsuit$

> **Observación 5.50.** Notar que ni el completamiento de bases de subespacios y ni el completamiento de subespacios son únicos.

---

### 5.3.4. Bases y suma directa

#### Teorema 5.52 (Base de la suma directa, versión 2 subespacios)

> **Teorema 5.52 (Base de la suma directa, versión 2 subespacios).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial.
> 
> Si $W_1$ y $W_2$ son subespacios vectoriales de $V$ tales que $V = W_1 \oplus W_2$, y existen bases $B_1$ para $W_1$ y $B_2$ para $W_2$, entonces $B_1 \cap B_2 = \emptyset$ y $B_1 \cup B_2$ es una base para $V$.
> 
> Recíprocamente, si $B_1$ y $B_2$ son subconjuntos de $V$ tales que $B_1 \cap B_2 = \emptyset$ *(el texto original menciona $B_1 \cap B_2 = \{0_V\}$, pero las bases no contienen al vector nulo y en la propia demostración se usa $B_1 \cap B_2 = \emptyset$)* y $B_1 \cup B_2$ es una base de $V$, entonces $V = W_1 \oplus W_2$ con $W_1 = \langle B_1 \rangle_\mathbb{R}$ y $W_2 = \langle B_2 \rangle_\mathbb{R}$.
> 
> En particular, $V$ es finitamente generado si, y sólo si, $W_1$ y $W_2$ lo son.

##### Demostración
($\implies$) Mostremos cada parte separadamente:

- ($B_1 \cap B_2 = \emptyset$) Si $b \in B_1 \cap B_2$, entonces $b \in W_1 \cap W_2 = \{0_V\}$, luego $b = 0_V$. Como $B_1$ y $B_2$ son LI, no contienen $0_V$, y por lo tanto, la intersección es vacía.

- ($B_1 \cup B_2$ genera $V$) Se sigue de la Proposición 5.11 que $\langle B_1 \cup B_2 \rangle_\mathbb{R} = W_1 + W_2 = V$.

- ($B_1 \cup B_2$ es LI). Sean $B_1 = \{b_1^{(1)}, \dots, b_m^{(1)}\}$ y $B_2 = \{b_1^{(2)}, \dots, b_n^{(2)}\}$. Sea
$$\alpha_1 b_1^{(1)} + \dots + \alpha_m b_m^{(1)} + \beta_1 b_1^{(2)} + \dots + \beta_n b_n^{(2)} = 0_V$$
una combinación lineal nula (notar que como $B_1 \cap B_2 = \emptyset$, todos los términos son distintos). Entonces
$$W_1 \ni \alpha_1 b_1^{(1)} + \dots + \alpha_m b_m^{(1)} = -\beta_1 b_1^{(2)} - \dots - \beta_n b_n^{(2)} \in W_2.$$
Luego, estando en la intersección $W_1 \cap W_2 = \{0_V\}$, ambas las “subcombinaciones” son nulas y, por $B_1$ y $B_2$ ser LI, son triviales, es decir
$$\alpha_1 = \dots = \alpha_m = 0 \quad \text{y} \quad \beta_1 = \dots = \beta_n = 0.$$
Por lo tanto, la combinación lineal nula con que empezamos es trivial, y $B_1 \cup B_2$ es LI.

($\impliedby$) Por la Proposición 5.11,
$$W_1 + W_2 = \langle \underbrace{B_1 \cup B_2}_{\text{base de } V} \rangle_\mathbb{R} = V.$$
Queda mostrar que la suma es directa. Si $v \in W_1 \cap W_2$, entonces
$$v = \alpha_1 b_1^{(1)} + \dots + \alpha_m b_m^{(1)} \in W_1 \quad \text{y} \quad v = \beta_1 b_1^{(2)} + \dots + \beta_n b_n^{(2)} \in W_2$$
donde $B_1 = \{b_1^{(1)}, \dots, b_m^{(1)}\}$ y $B_2 = \{b_1^{(2)}, \dots, b_n^{(2)}\}$. Luego,
$$v - v = 0_V = \alpha_1 b_1^{(1)} + \dots + \alpha_m b_m^{(1)} - \beta_1 b_1^{(2)} - \dots - \beta_n b_n^{(2)}$$
es una combinación lineal nula de términos distintos (ya que $B_1 \cap B_2 = \emptyset$) en $B_1 \cup B_2$ que, siendo una base de $V$, es LI. Luego, $\alpha_1 = \dots = \alpha_m = \beta_1 = \dots = \beta_n = 0$ y $v = 0_V$.

Para la última afirmación, si $V$ es finitamente generado también lo es cualquier subespacio. Recíprocamente, si $W_1$ y $W_2$ son finitamente generados, entonces $B_1$ y $B_2$ son finitos, y por lo tanto $B_1 \cup B_2$ también es finito. Como $B_1 \cup B_2$ es una base para $V$, entonces $V$ es finitamente generado. $\clubsuit$

---

#### Teorema 5.54 (Base de la suma directa)

> **Teorema 5.54 (Base de la suma directa).** Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial.
> 
> Si $\mathcal{F} = \{W_i \subseteq V : i \in I\}$ es una familia arbitraria de subespacios de $V$ tales que $V = \bigoplus_{i \in I} W_i$, y existen una base $B_i$ para cada $W_i$, entonces $B_i \cap B_j = \emptyset$ para todo $i \neq j \in I$ y $\bigcup_{i \in I} B_i$ es una base para $V$.
> 
> Recíprocamente, si $\{B_i \subseteq V : i \in I\}$ son subconjuntos de $V$ tales que $B_i \cap B_j = \emptyset$ para todo $i \neq j \in I$ y $\bigcup_{i \in I} B_i$ es una base de $V$, entonces $V = \bigoplus_{i \in I} W_i$ con $W_i = \langle B_i \rangle_\mathbb{R}$ para todo $i \in I$.
> 
> En particular, $V$ es finitamente generado si, y sólo si, $\{i \in I : W_i \neq \{0_V\}\}$ es finito y todos los $W_i$ son finitamente generados.

##### Demostración
($\implies$) Mostremos cada parte:

- ($B_i \cap B_j = \emptyset$) Sean $i, j \in I$ distintos y $b \in B_i \cap B_j$. Entonces $b \in W_i \cap \left(\sum_{k \in I \setminus \{i\}} W_k\right) = \{0_V\}$, luego $b = 0_V$. Como $B_i$ y $B_j$ son LI, no contienen $0_V$, y por lo tanto, la intersección es vacía.

- ($\bigcup_{i \in I} B_i$ genera $V$) Se sigue de la Proposición 5.11,
$$\left\langle \bigcup_{i \in I} B_i \right\rangle_\mathbb{R} = \sum_{i \in I} W_i = V.$$

- ($\bigcup_{i \in I} B_i$ es LI) Sea una combinación lineal finita nula $\alpha_1 b_1 + \dots + \alpha_n b_n = 0$ de términos distintos de $\bigcup_{i \in I} B_i$. Agrupando por bases a que pertenecen originalmente, podemos reorganizar la misma ecuación del siguiente modo: definimos para cada $i \in I$
$$v_i := \sum_{b_k \in B_i} \alpha_k b_k \in W_i$$
(recordando que una suma vacía tiene valor $0_V$, por definición). Entonces
$$\sum_{i \in I} v_i = 0_V$$
es una suma con finitos términos no nulos.

Como la suma es directa, por el Teorema 4.38, existe un único modo de descomponer $0_V$ en la suma directa: con todos los $v_i = 0_V$. Luego, como $B_i$ es base de $W_i$, es LI, y por lo tanto todos los coeficientes de los $b_k$ que componen cada $v_i$ son nulos. Así, la combinación original es trivial.

($\impliedby$) Por la Proposición 5.11,
$$\sum_{i \in I} W_i = \left\langle \bigcup_{i \in I} B_i \right\rangle_\mathbb{R} = V.$$

Queda ver que la suma es directa. Queremos mostrar que para todo $i_0 \in I$,
$$W_{i_0} \cap \sum_{i \in I \setminus \{i_0\}} W_i = \{0_V\}.$$

Sea $v \in W_{i_0} \cap \sum_{i \in I \setminus \{i_0\}} W_i$. Supongamos $v \neq 0_V$. Entonces $v \in W_{i_0}$ y $v$ se expresa como una suma de $w_i \in W_i$ ($i \neq i_0$) con apenas finitos términos no nulos:
$$v = w_{i_1} + \dots + w_{i_n}, \quad \text{con } w_{i_k} \in W_{i_k} \text{ no nulos y } i_0 \notin \{i_1, \dots, i_n\}.$$

Escribiendo cada vector en términos de su base correspondiente, tenemos combinaciones lineales finitas
$$v = \sum_{r}^{<\infty} \alpha_r b_r^{(i_0)}, \quad b_r^{(i_0)} \in B_{i_0} \quad \text{y} \quad v = \sum_{k=1}^n \sum_s^{<\infty} \beta_s^{(i_k)} b_s^{(i_k)}, \quad b_s^{(i_k)} \in B_{i_k}$$
(en las sumas en $r$ y $s$ no indicamos qué índices recorren, solo que son finitos).

Luego,
$$0_V = v - v = \sum_r^{<\infty} \alpha_r b_r^{(i_0)} - \sum_{k=1}^n \sum_s^{<\infty} \beta_s^{(i_k)} b_s^{(i_k)}$$
es una combinación lineal nula no trivial de elementos de $\bigcup_{i \in I} B_i$ con todos los términos distintos, ya que $B_{i_0} \cap B_i = \emptyset$ si $i \neq i_0$. Eso contradice el hecho de que $\bigcup_{i \in I} B_i$ es LI por ser base. Luego, $v = 0_V$. Por lo tanto,
$$W_{i_0} \cap \sum_{i \in I \setminus \{i_0\}} W_i = \{0_V\} \quad \text{para todo } i_0 \in I,$$
y la suma es directa.

Para la última afirmación, si $V$ es finitamente generado, entonces todo subespacio $W_i$ lo es. Recíprocamente, si cada $W_i$ es finitamente generado, entonces cada $B_i$ es finito. Si además sólo hay finitos índices $i$ tales que $W_i \neq \{0_V\}$, entonces $\bigcup_{i \in I} B_i$ es finita, y como es base de $V$, concluimos $V$ es finitamente generado. $\clubsuit$
