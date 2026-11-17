# Extracto de Notas de Álgebra Lineal I (FCIEN UdelaR 2026)
**Autor:** Eris Rocha Walchek  
**Versión:** 27 de junio de 2026  

---

## Proposición 4.5 (Página 127) y Demostración

> **Proposición 4.5** *(Otras propiedades aritméticas)*. Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial.
> 
> I. Para todo $v \in V$, $0 \cdot v = 0_V$;  
> II. Para todo $v \in V$, $(-1) \cdot v = -v$;  
> III. Para todo $\lambda \in \mathbb{R}$, $\lambda \cdot 0_V = 0_V$;  
> IV. Si $\lambda \cdot v = 0_V$, entonces $\lambda = 0$ o $v = 0_V$;

### Demostración
**(I.)** Como $v = 1 \cdot v$ (EV6.),
$$v = 1 \cdot v = (1 + 0) \cdot v \stackrel{\text{EV8.}}{=} 1 \cdot v + 0 \cdot v \stackrel{\text{EV6.}}{=} v + 0 \cdot v \stackrel{\text{Corolario 4.4}}{\iff} 0_V = 0 \cdot v.$$

**(II.)** Como $v = 1 \cdot v$ (EV6.), y por definición del opuesto (EV4.):
$$v + (-v) = 0_V \stackrel{\text{I.}}{=} 0 \cdot v = (1 + (-1)) \cdot v \stackrel{\text{EV8.}}{=} 1 \cdot v + (-1) \cdot v = v + (-1) \cdot v \stackrel{\text{Corolario 4.4}}{\iff} -v = (-1) \cdot v.$$

**(III.)** Como $0_V + 0_V = 0_V$ (EV3.), multiplicando por $\lambda$,
$$\lambda \cdot 0_V = \lambda \cdot (0_V + 0_V) \stackrel{\text{EV7., EV3.}}{=} 0_V + \lambda \cdot 0_V = \lambda \cdot 0_V + \lambda \cdot 0_V \stackrel{\text{Corolario 4.4}}{\iff} 0_V = \lambda \cdot 0_V.$$

**(IV.)** Si $\lambda = 0$, se sigue de I. Caso contrario,
$$\lambda \cdot v = 0_V \stackrel{\text{mult. p/ } \lambda^{-1}}{\implies} (\lambda^{-1} \cdot \lambda) \cdot v = \lambda^{-1} \cdot 0_V \stackrel{\text{III}}{\iff} v = 0_V. \quad \clubsuit$$

---

## Definición 4.6 (Página 128)

> **Definición 4.6** *(Subespacio vectorial)*. Sea $(V, +_V, \cdot_V)$ un $\mathbb{R}$-espacio vectorial. Decimos que $W \subseteq V$ es un **subespacio vectorial** de $V$ si:
> 
> I. $0_V \in W$;  
> II. Si $w_1, w_2 \in W$, entonces $w_1 +_V w_2 \in W$;  
> III. Si $w \in W$ y $\lambda \in \mathbb{R}$, entonces $\lambda \cdot_V w \in W$. $\blacklozenge$

---

## Definición 4.20 (Página 135)

> **Definición 4.20** *(Intersección de subespacios vectoriales)*. Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $W_1$ y $W_2$ son dos subespacios vectoriales de $V$, definimos la **intersección** de $W_1$ y $W_2$ como siendo el conjunto de los elementos de $V$ que pertenecen simultáneamente a $W_1$ y a $W_2$:
> $$W_1 \cap W_2 \stackrel{\text{def}}{=} \{v \in V : v \in W_1 \text{ y } v \in W_2\}.$$
> Más generalmente, si $\mathcal{F} = \{W_i : i \in I\}$ es una familia[^37] arbitraria de subespacios vectoriales de $V$, la **intersección** de los $W_i$ ($i \in I$) es definida por los elementos de $V$ que están simultáneamente en todos los $W_i$:
> $$\bigcap_{i \in I} W_i \stackrel{\text{def}}{=} \{v \in V : v \in W_i\ \forall i \in I\}. \quad \blacklozenge$$

[^37]: **Nota al pie original [37]:** Familia es siempre usado como sinónimo de conjunto (especialmente para conjuntos de conjuntos). Los indices ni necesitan ser un conjunto ordenado como $\mathbb{N}$ o $\mathbb{R}$, lo que dificulta entender como se organizan sus elementos, pero sigue siendo algo bien definido. Considerar casos pequeños (como $I = \{1, 2\}$, $I = \{1, 2, 3\}$,...) y ordenados ($\mathbb{N}$, $\mathbb{Z}$,...) para ayudar a entender si parece demasiado complicado.

---

## Proposición 4.21 (Página 136) y Demostración

> **Proposición 4.21**. Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $W_1$ y $W_2$ son subespacios vectoriales de $V$, entonces $W_1 \cap W_2$ es un subespacio vectorial de $V$.
> 
> Más generalmente, si $\mathcal{F} = \{W_i \subseteq V : i \in I\}$ es una familia arbitraria de subespacios vectoriales de $V$, la intersección $\bigcap_{i \in I} W_i$ también es un subespacio vectorial de $V$.

### Demostración
Mostramos el caso general dejando el caso de dos subespacios a ser usado como un “guía” para la demostración.

Mostraremos las 3 condiciones que definen subespacio vectorial (Definición 4.6):

I. Como $0_V$ pertenece a cualquier subespacio vectorial de $V$, entonces $0_V \in W_i$ para todo $i \in I$ y por lo tanto $0_V \in \bigcap_{i \in I} W_i$;

II. Sean $w_1, w_2 \in \bigcap_{i \in I} W_i$. Por definición de la intersección, los $w_1$ y $w_2$ pertenecen simultáneamente a todos los $W_i$ con $i \in I$, y como estos son subespacios de $V$, son cerrados por la suma, luego $w_1 + w_2 \in W_i$ para todo $i \in I$ y por lo tanto $w_1 + w_2 \in \bigcap_{i \in I} W_i$;

III. Sean $w \in \bigcap_{i \in I} W_i$ y $\lambda \in \mathbb{R}$. Por definición de la intersección, $w$ pertenece simultáneamente a todos los $W_i$ con $i \in I$, y como estos son subespacios de $V$, son cerrados por el producto por escalar real, luego $\lambda \cdot w \in W_i$ para todo $i \in I$ y por lo tanto $\lambda \cdot w \in \bigcap_{i \in I} W_i$.

Cumpliendo las definición, $\bigcap_{i \in I} W_i$ es un subespacio vectorial de $V$. $\clubsuit$

---

## Definición 4.25 (Página 138)

> **Definición 4.25** *(Suma de subespacios vectoriales)*. Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $W_1$ y $W_2$ son dos subespacios de $V$, definimos la **suma** de $W_1$ y $W_2$ como siendo el conjunto de los elementos de $V$ que son sumas de elementos de $W_1$ y $W_2$:
> $$W_1 + W_2 \stackrel{\text{def}}{=} \{v \in V : v = w_1 + w_2 \text{ con } w_1 \in W_1 \text{ y } w_2 \in W_2\}.$$
> Más generalmente, si $\mathcal{F} = \{W_i : i \in I\}$ es una familia arbitraria de subespacios vectoriales de $V$, la **suma** de los $W_i$ ($i \in I$) es definida por los elementos de $V$ que son sumas *finitas* de elementos en $W_i$ para algunos $i \in I$:
> $$\sum_{i \in I} W_i \stackrel{\text{def}}{=} \left\{v \in V : v = \sum_{i \in I} w_i \text{ con } w_i \in W_i \text{ y } w_i = 0 \text{ excepto para finitos } i \in I\right\}. \quad \blacklozenge$$

---

## Proposición 4.27 (Páginas 138–139) y Demostración

> **Proposición 4.27**. Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $W_1$ y $W_2$ son subespacios vectoriales de $V$, entonces $W_1 + W_2$ es un subespacio vectorial de $V$.
> 
> Más generalmente, si $\mathcal{F} = \{W_i \subseteq V : i \in I\}$ es una familia arbitraria de subespacios vectoriales de $V$, la suma $\sum_{i \in I} W_i$ también es un subespacio vectorial de $V$.

### Demostración
Mostramos el caso general dejando el caso de dos subespacios a ser usado como un “guía” para la demostración.

Mostraremos las 3 condiciones que definen subespacio vectorial (Definición 4.6):

I. $0_V$ si escribe como una suma de $w_i \in W_i$ donde el conjunto $\{i \in I : w_i \neq 0_V\}$ de sumandos no nulos es vacío (en particular, finito). Por lo tanto, $0_V \in \sum_{i \in I} W_i$;

II. Sean $v_1, v_2 \in \sum_{i \in I} W_i$. Por definición de la suma, los $v_1$ y $v_2$ si expresan como sumas finitas (posiblemente vacías) de elementos no nulos en algunos de los $W_i$:
$$v_1 = w_{i_1} + \dots + w_{i_n} \quad \text{y} \quad v_2 = w_{i_{n+1}} + \dots + w_{i_m},$$
con $\{i_1, \dots, i_n, i_{n+1}, \dots, i_m\} \subseteq I$ y $w_{i_k} \in W_{i_k}$ para todo $k$. Por lo tanto, la suma
$$v_1 + v_2 = w_{i_1} + \dots + w_{i_n} + w_{i_{n+1}} + \dots + w_{i_m}$$
es una suma finita (posiblemente vacía) de elementos no nulos contenidos en algunos de los $W_i$ y por lo tanto $w_1 + w_2 \in \sum_{i \in I} W_i$;

III. Sean $v \in \sum_{i \in I} W_i$ y $\lambda \in \mathbb{R}$. Por definición de la suma, $v$ si expresa como suma finita (posiblemente vacía) de elementos no nulos en algunos de los $W_i$:
$$v_1 = w_{i_1} + \dots + w_{i_n},$$
con $\{i_1, \dots, i_n\} \subseteq I$ y $w_{i_k} \in W_{i_k}$ para todo $k$. Como cada $W_i$ es un subespacio vectorial, cerrado por el producto por escalar, $\lambda \cdot w_{i_k} \in W_{i_k}$ para todo $k$. Por lo tanto, el producto por escalar
$$\lambda \cdot v = \underbrace{\lambda w_{i_1}}_{\in W_{i_1}} + \dots + \underbrace{\lambda w_{i_n}}_{\in W_{i_n}}$$
es una suma finita (posiblemente vacía) de elementos no nulos contenidos en algunos de los $W_i$ y por lo tanto $\lambda \cdot v \in \sum_{i \in I} W_i$.

Cumpliendo la definición, $\sum_{i \in I} W_i$ es un subespacio vectorial de $V$. $\clubsuit$

---

## Nota sobre los números 4.22 y 4.24

En el texto original de *NotasAlgLineal2026*:
* El ítem **4.22** es la **Observación 4.22** (pág. 136) y el ítem **4.24** es el **Ejemplo 4.24** (pág. 137, no tiene demostración).
* Por otro lado, la definición de suma directa para dos subespacios y su teorema de unicidad (con demostración) corresponden a la **Definición 4.33** y al **Teorema 4.34** (pág. 143), los cuales forman el par análogo previo a la **Definición 4.37** y al **Teorema 4.38**.

Para total fidelidad y cobertura completa de ambas posibilidades, se transcriben a continuación tanto la Observación 4.22 y Ejemplo 4.24, como la Definición 4.33 y el Teorema 4.34 con su demostración:

### Opción A: Observación 4.22 y Ejemplo 4.24

> **Observación 4.22 (Página 136).** Notar que $\bigcap_{i \in I} W_i$ también es un subespacio vectorial de todos los $W_i$: como $\bigcap_{i \in I} W_i \subseteq W_i$ y las operaciones de cada $W_i$ son las mismas de $V$, entonces $\bigcap_{i \in I} W_i \subseteq W_i$ también es cerrado por la suma y el producto por escalar de cada $W_i$, siendo de estos un subespacio. $\heartsuit$

> **Ejemplo 4.24 (Página 137) (Unión de subespacios vectoriales).** La unión de subespacios vectoriales ni siempre es un subespacio vectorial.
> 
> Recordamos que rectas que pasan por el origen son subespacios vectoriales de $\mathbb{R}^2$ (Ejemplo 4.8). Así, podemos expresar $\mathbb{R}^2$ como la unión de *todas* las rectas que pasan por el origen, y así la unión de tales subespacios vectoriales es (trivialmente) un subespacio vectorial. Pero si consideramos solo las rectas $r_x : y = 0$ y $r_y : x = 0$, $r_x \cup r_y$ no es un subespacio vectorial de $\mathbb{R}^2$ porque, por ejemplo, no es cerrado por la suma:
> $$(1, 0) \in r_x \text{ y } (0, 1) \in r_y, \text{ pero } (1, 0) +_{\mathbb{R}^2} (0, 1) = (1, 1) \notin r_x \cup r_y. \quad \spadesuit$$

---

### Opción B: Definición 4.33 y Teorema 4.34 (Páginas 143–144) y Demostración

> **Definición 4.33** *(Suma directa, para dos subespacios)*. Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $W_1$ y $W_2$ son dos subespacios de $V$, decimos que la suma $W_1 + W_2$ es **directa** si $W_1 \cap W_2 = \{0_V\}$. En este caso, denotamos $W_1 + W_2$ por $W_1 \oplus W_2$. $\blacklozenge$

> **Teorema 4.34** *(Unicidad de la descomposición de elementos en suma directa, para dos subespacios)*. Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $W_1$ y $W_2$ son subespacios vectoriales de $V$, la suma $W_1 + W_2$ es directa si, y sólo si, la descomposición de cualquier $v \in W_1 + W_2$ como
> $$v = w_1 + w_2 \quad \text{con } w_1 \in W_1 \text{ y } w_2 \in W_2$$
> es única, es decir, si
> $$v = w_1 + w_2 = w_1' + w_2' \quad \text{con } w_1, w_1' \in W_1 \text{ y } w_2, w_2' \in W_2, \text{ entonces } w_1 = w_1' \text{ y } w_2 = w_2'.$$

#### Demostración
($\implies$) Si la suma $W_1 \oplus W_2$ es directa, entonces $W_1 \cap W_2 = \{0_V\}$.

Sea $v \in W_1 \oplus W_2$. Supongamos que haya dos descomposiciones de $v$ en sumas
$$v = w_1 + w_2 = w_1' + w_2',$$
con $w_1, w_1' \in W_1$ y $w_2, w_2' \in W_2$. Así,
$$0_V = v - v = w_1 + w_2 - (w_1' + w_2') \iff W_1 \ni w_1 - w_1' = w_2' - w_2 \in W_2$$

Luego, $w_1 - w_1' = w_2' - w_2 \in W_1 \cap W_2$. Pero la intersección es $\{0_V\}$, y por lo tanto
$$w_1 - w_1' = 0_V = w_2' - w_2 \implies w_1 = w_1' \text{ y } w_2 = w_2'.$$

($\impliedby$) Sea $v \in W_1 \cap W_2$. Notar que, si $v \neq 0_V$,
$$v = \underbrace{v}_{\in W_1} + \underbrace{0_V}_{\in W_2} = \underbrace{0_V}_{\in W_1} + \underbrace{v}_{\in W_2}$$
son dos descomposiciones distintas de $v$ en $W_1 + W_2$, lo que por hipótesis implica, comparando los sumandos de $W_1$, $v = 0_V$. $\clubsuit$

---

## Definición 4.37 (Página 144)

> **Definición 4.37** *(Suma directa)*. Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $\mathcal{F} = \{W_i : i \in I\}$ es una familia arbitraria de subespacios de $V$, decimos que la suma $\sum_{i \in I} W_i$ es **directa** si, para todo $i_0 \in I$,
> $$W_{i_0} \cap \left(\sum_{i \in I \setminus \{i_0\}} W_i\right) = \{0_V\}. \quad \blacklozenge$$

---

## Teorema 4.38 (Página 145) y Demostración

> **Teorema 4.38** *(Unicidad de la descomposición de elementos en suma directa)*. Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $\mathcal{F} = \{W_i \subseteq V : i \in I\}$ es una familia arbitraria de subespacios vectoriales de $V$, la suma $\sum_{i \in I} W_i$ es directa si, y sólo si, la descomposición de cualquier $v \in \sum_{i \in I} W_i$ como suma finita de elementos no nulos de los $W_i$,
> $$v = \sum_{i \in I} w_i \quad \text{con } w_i \in W_i \text{ y } \#\{i \in I : w_i \neq 0\} < \infty,$$
> es única, es decir, si hay dos descomposiciones en esas condiciones
> $$v = \sum_{i \in I} w_i = \sum_{i \in I} w_i',$$
> entonces $w_i = w_i'$ para todo $i \in I$.

### Demostración
($\implies$) Si la suma $\bigoplus_{i \in I} W_i$ es directa, $W_{i_0} \cap \left(\sum_{i \in I \setminus \{i_0\}} W_i\right) = \{0_V\}$.

Sea $v \in \bigoplus_{i \in I} W_i$. Supongamos que haya dos descomposiciones de $v$:
$$v = \sum_{i \in I} w_i = \sum_{i \in I} w_i',$$
con $w_i, w_i' \in W_i$ y ambas las sumas consistan de finitos elementos no nulos. Así,
$$0_V = v - v = \sum_{i \in I} (w_i - w_i')$$

Como
$$W_{i_0} \ni w_{i_0}' - w_{i_0} = \sum_{i \in I \setminus \{i_0\}} (w_i - w_i') \in \sum_{i \in I \setminus \{i_0\}} W_i,$$
para todo $i_0 \in I$, $w_{i_0}' - w_{i_0} \in W_{i_0} \cap \left(\sum_{i \in I \setminus \{i_0\}} W_i\right) = \{0_V\}$. Por lo tanto, $w_i = w_i'$ para todo $i$ y las descomposiciones son iguales.

($\impliedby$) Sean $i_0 \in I$ y $w_{i_0} \in W_{i_0} \cap \left(\sum_{i \in I \setminus \{i_0\}} W_i\right)$. Entonces $w_{i_0}$ tiene dos representaciones
$$w_{i_0} = \underbrace{w_{i_0}}_{\in W_{i_0}} + \underbrace{0_V + \dots}_{i \neq i_0} = \underbrace{0_V}_{\in W_{i_0}} + \sum_{i \in I \setminus \{i_0\}} w_i.$$

Comparando las componentes en $W_{i_0}$, $w_{i_0} = 0_V$. Por lo tanto, para todo $i_0 \in I$,
$$W_{i_0} \cap \left(\sum_{i \in I \setminus \{i_0\}} W_i\right) = \{0_V\}$$
y, por definición, la suma $\sum_{i \in I} W_i$ es directa. $\clubsuit$

---

## Corolario 4.39 (Página 146) y Demostración

> En particular, si la suma de subespacios es directa, su intersección es trivial:
> 
> **Corolario 4.39**. Sea $(V, +, \cdot)$ un $\mathbb{R}$-espacio vectorial. Si $\mathcal{F} = \{W_i \subseteq V : i \in I\}$ es una familia arbitraria de subespacios vectoriales de $V$ y la suma $\bigoplus_{i \in I} W_i$ es directa, entonces $\bigcap_{i \in I} W_i = \{0_V\}$.

### Demostración
Si $v \in \bigcap_{i \in I} W_i$, tomando $i_1, i_2 \in I$ distintos y comparando las descomposiciones
$$v = \underbrace{v}_{\in W_{i_1}} + \underbrace{0_V}_{\in W_{i_2}} + \underbrace{0_V + \dots}_{i \notin \{i_1, i_2\}} \quad \text{y} \quad v = \underbrace{0_V}_{\in W_{i_1}} + \underbrace{v}_{\in W_{i_2}} + \underbrace{0_V + \dots}_{i \notin \{i_1, i_2\}},$$
tenemos que $v = 0_V \in W_{i_1}$, y por lo tanto, $\bigcap_{i \in I} W_i = \{0_V\}$. $\clubsuit$
