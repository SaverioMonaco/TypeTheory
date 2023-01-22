# Appunti di Teoria dei Tipi: <a name="su"></a>

---

1.  [Introduzione della Teoria dei Tipi](#int)
2.  [Prime regole della teoria dei tipi dipendenti di Martin-Löf](#reglof)
3.  [Regole strutturali](#regstru)
4.  [Regole (principali) del tipo singoletto](#regsin)
5.  [Altre regole strutturali derivabili](#regdev)
6.  [Schema generale di produzione di regole definenti un tipo e i suoi termini](#protip)
7.  [Perché la teoria dei tipi può essere pensata come un linguaggio di programmazione funzionale?](#tipcod)
8.  [Regole del tipo dei numeri naturali](#regnat)
9.  [Somma tra numeri naturali](#sommanat)
10. [Tipo delle liste di un tipo](#liste)
11. [Somma disgiunta](#somdis)
12. [Tipo uguaglianza proposizionale](#ugprop)
13. [Tipo Somma indiciata Forte](#strindsumtype)
    * 13.1 [La somma indiciata forte è un potenziamento con tipi dipendenti del tipo prodotto cartesiano](#prodcart)
    * 13.2 [Uso del tipo $\Sigma_{x\in B} C(x)$ ](#usisiff)
    * 13.3 [Tipo prodotto cartesiano come congiunzione logica](#conjlog)
14. [Tipo prodotto dipendente](#prodip)
* [Esercizi](#exs)
---

## 1. Introduzione della Teoria dei Tipi <a name="int"></a>
#### Parentesi storica:
* **(~ 1910)** In _Principia Mathematica_ Russel offre con la Teoria dei tipi una soluzione al problema dell'inconsistenza degli insiemi di Frege.
  La teoria degli insiemi di Frege era scritta in un linguaggio $\mathcal{L}$ del primo ordine:

  $$\mathcal{L}: and, \lor, \to, tt, \perp, \forall x, \exists y$$

  Inoltre viene aggiunto il simbolo di appartenenza tra insiemi:

  $$1 \in Nat $$

  Dove 1 è un insieme singoletto (avente solo un elemento) e Nat è l'insieme dei naturali

  `La logica di Frege = Logica del primo ordine  +  predicato di appartenenza
  `

  Come assiomi ha messo le regole della: 

  ``
  Logica classica + Assioma di comprensione
  `` 

  **Assioma di comprensione**: Dato $\varphi(x)$ formula, $\exists y \forall x (x\in y \leftrightarrow\varphi(x))$ s.t. $y\equiv[x|\varphi(x)]$

  **Teorema: La teoria di Frege è contraddittoria**

  **Proof:** Dall'assioma di comprensione, se consideriamo

  $$y = [x|x \notin x] \quad \to \quad \varphi(x) = x\notin x$$ 

  Otteniamo:

  $$\exists y \forall x \space(x\in y \leftrightarrow x \notin x)$$

  $y$ è l'insieme che contiene esattamente gli insiemi che non contengono se stessi.

  <span style="color:green">(Come fa un insieme a contenere o non contenere se stesso?
  Considera questi due esempi:</span>
  <ul>
  <span style="color:green"><li>L'insieme delle mele, ogni elemento è una mela, l'insieme delle mele non è un elemento dell'insieme delle mele, quindi non contiene se stesso</li></span>
  <span style="color:green"><li>L'insieme di tutto ciò che non è una mela, l'insieme di tutto ciò che non è una mela non è una mela e può essere considerato come elemento appartenente a se stesso</li>)</span>
  </ul>

  Se l'insieme $y$, ovvero l'insieme che contiene gli insiemi che non si contengono, contiene se stesso $(x\in y)$, allora l'insieme non contiene se stesso $(\varphi(x) = x\notin x)$, mentre per definizione se l'insieme non contiene se stesso allora contiene se stesso.

## 2. Prime regole della teoria dei tipi dipendenti di Martin-Löf <a name="reglof"></a>
<div style="text-align: right"><span style="color:orange">Lezione 6</span></div>

In questo capitolo inizieremo ad usare una notazione della logica per la derivazione di conclusioni / formulazione di giudizi:

$$\frac{\text{(molteplici) ipotesi/ giudizi}}{\text{(unica) conclusione / giudizio}}$$

La teoria dei Tipi di Martin-Loef è stata formulata usando la nozione di **giudizio** (alla Frege), in un giudizio si asserisce qualcosa (come vero). Per asserire questo qualcosa, vengono introdotte **4 forme di giudizio** che serviranno come building blocks di tutta la teoria.

#### Forme di Giudizio:
* **Giudizio di Tipo**: A type $[\Gamma]$
  
  "_A type sotto contesto Gamma_"

  A è un tipo (possibilmente dipendente da variabili del contesto $\Gamma$) possibilmente indiciato da variabile nel contesto $\Gamma$

* **Giudizio di uguaglianza tra Tipi**: A = B type $[\Gamma]$
  
  "_A è uguale a B type sotto contesto Gamma_"
  
  Il tipo A dipendente da $\Gamma$ è uguale al tipo B dipendente da $\Gamma$.

* **Giudizio di Tipo**: a $\in$ A type $[\Gamma]$
  
  "_a appartiene ad A sotto contesto Gamma_"

  a è un elemento del tipo A possibilmente indiciato (ovvero dipendente da $\Gamma$)
* **Giudizio di Tipo**: a = b $\in$ A type $[\Gamma]$
  
  "_a è uguale a b sotto contesto Gamma_" 

  a è uguale a b è un giudizio che indica che a è un elemento del tipo A dipendente da $\Gamma$ è uguale in modo definizionale/computazionale al termine b come elemento del tipo A dipendente da $\Gamma$

* **Giudizio Ausiliario** 
  
  $$\varnothing\space cont \quad \text{F-c)}\space\space\frac{A\space\space type\space\space[\Gamma]}{\Gamma,x \in A \space cont} ((x\in A)\space not\space in\space\space \Gamma)$$

  "_Il vuoto è un contesto. Se A è un tipo sotto contesto Gamma, allora posso estendere il contesto gamma con una variabile x di A a patto che_ $x \in A$ _non compaia in Gamma_"

  Questa regola è ausiliaria perché può essere derivata dalle altre, in un contesto minimalista sarebbe meglio ometterla perché una teoria con meno regole è preferibile, ma metterla rende tutto più facile.

<span style="color:green">**Cosa è esattamente un contesto?**<br>Un contesto è l'insieme di regole/predicati che abbiamo già ricavato. Dopo sarà più chiaro quando faremo l'albero di derivazione.</span>

<span style="color:green">**Cosa è un tipo dipendente?** <br> Un esempio di tipo dipendente è un vettore (o matrice) che dipende da un altro tipo (ad esempio il tipo dei natrurali se vogliamo costruire un array di elementi naturali).</span>

<span style="color:green">**Qual è la differenza tra uguaglianza definizionale e computazionale?** <br> </span>

**Nota** $a \in A$ della teoria dei tipi indica una appartenenza **differente** dal concetto insiemistico:

* In set Theory abbiammo 
  
  $$1 \in Nat $$

  Dove 1 è un insieme singoletto (avente solo un elemento) e Nat è l'insieme dei naturali
  <br>
* Nella teoria dei tipi (di Russel)
  
  $$1 \in Nat $$

  1 è un elemento e non un tipo, mentre Nat è un tipo. Stiamo imponendo una gerarchia (elemento<tipo) per evitare il paradosso di Russel della teoria di Frege. 

<span style="color:green">**Perché la teoria di Frege è inconsistente? (il paradosso di Russel)** <br> TODO</span>

#### Regole di formazione dei tipi singoletto 
Il singoletto è il tipo generale più semplice da studiare, poiché per definizione contiene un singolo elemento. Qui enunciamo le regole per la formazione dei suddetti tipi:

* **Regola di Formazione del tipo singoletto**
  
  $$\text{S)}\space\space\frac{\Gamma \space\space cont}{N_1 \space type \space\space[\Gamma]}$$
  
  _"Se Gamma è un contesto, allora N1 è un tipo sotto contesto Gamma"_

* **Regola di introduzione della $*$ nel singoletto**
  
$$\text{I-S)}\space\space\frac{\Gamma \space\space cont}{* \in N_1 \space\space[\Gamma]}$$

_"Se Gamma è un contesto allora star appartiene ad N1 sotto contesto Gamma"_

Regola che mi permette di dire come fare a scrivere funzioni dal tipo singoletto verso qualsiasi altro tipo:

* **Regola di Eliminazione**
  
  $$\text{E-S)}\space\space\frac{t_1 \in N_1\space\space[\Gamma]\quad M(z) \space\space type \space\space [\Gamma, z\in N_1]\quad c\in M(*)\space\space [\Gamma]}{El_{N_1}(t,c) \in \underbrace{M(t)}_{M(z)[z/t]}\space\space[\Gamma]}$$

  _"Se t1 è un termine di tipo N1 sotto contesto Gamma ed M(z) è un tipo dipendente da Gamma e z in tipo N1 e so che c  tipo M (*) sotto contesto Gamma allora posso dedurre l'eliminatore."_

  Noi riusciamo a trovare elementi di tipo M(t) (l'eliminatore), se noi sappiamo cosa succede in M(*). In altre parole riusciamo ad avere una funzione che ci porta da N1 (tramite $t \in N_1$) a $M(t)$

* **Seconda regola di Eliminazione** 
   
$$\text{C-S)}\space\space\frac{M(z) \space\space type\space\space[\Gamma, z \in N_1]\quad c \in M(*)\space [\Gamma]}{El_{N_1}(*,c)= c \in M(*)\space\space[\Gamma]}$$
  
_"Se M(z) è un tipo sotto contesto Gamma e z in N1, e c appartiene ad M(*) sotto contesto Gamma allora l'eliminatore EL(*,c) è uguale a c in M(*) sotto contesto Gamma"_

In questa regola cominciamo a mettere un'uguaglianza.

---
## 3. Regole strutturali <a name="regstru"></a>
  <div style="text-align: right"><span style="color:orange">Lezione 7</span></div>

**Definizione:** Derivazione = albero ($\pi$) i cui nodi sono dati da regole di inferenza della forma:

$$\frac{J_1, ..., J_n}{J}$$

$J_1, ..., J_n$ sono le premesse, J è la conclusione.

L'unico assioma della teoria dei tipi è che il vuoto è un contesto $(:= [\space\space]\space cont)$ quindi per ogni derivazione dovremmo partire dall'assunzione $[\space\space]\space cont$

In Logica (calcolo dei sequenti) esiste un assioma di identità:

$$\phi \vdash \phi$$

_"Se phi è vera allora possiamo derivare phi"_

Possiamo aggiungere un assioma equivalente alla teoria dei tipi:
* **Regola di Costruzione delle variabili**
  
$$\frac{\Gamma,\space x\in A,\space \Delta \space cont}{x\in A\space[\Gamma,\space x\in A,\space \Delta]}$$

_"Se abbiamo x in A e pensiamo x in A come proposizione allora possiamo dedurre x in A"_.

#### 3.1 Regole dell'uguaglianza
Oltre a questa regola possiamo aggiungere regole per la relazione di equivalenza:
* _"uguaglianza tra tipi è una relazione di equivalenza"_
* _"uguaglianza tra termini è pure una relazione di equivalenza"_

Queste due regole a parole inducono delle regole della teoria dei tipi abbastanza ovvie:
* **Regola di riflessività** 
  
$$\frac{A\space type \space[\Gamma]}{A=A\space\space type \space[\Gamma]}$$

* **Regola di simmetria** 
  
$$\frac{A= B\space\space type \space[\Gamma]}{B=A\space\space type \space[\Gamma]}$$

* **Regola di transitività** 
  
$$\frac{A= B\space\space type \space[\Gamma]\quad B= C\space\space type \space[\Gamma]}{A=C\space\space type \space[\Gamma]}$$

* **Riflessività dei termini**
  
$$\frac{a \in A\space type \space[\Gamma]}{a=a\in A\space\space type \space[\Gamma]}$$

* **Simmetria dei termini**
  
$$\frac{a = b \in A\space type \space[\Gamma]}{b=a\in A\space\space type \space[\Gamma]}$$

* **Transitività dei termini**
  
$$\frac{a = b \in A\space type \space[\Gamma]\quad b = c \in A\space type \space[\Gamma]}{a=c\in A\space\space type \space[\Gamma]}$$

**Definizioni:** Regole proprie del calcolo e regole derivabili/ammissibili:
* **Regole proprie del calcolo**: sono le regole (quelle viste fin'ora) che vanno a definire la nostra teoria, vengono date come punto di partenza di tutta la teoria stessa (perché dal nulla possiamo derivare ben poco)
* **Regole ammissibili**: Sono regole di fatto ammissibili, sono derivate dalle regole del calcolo e servono per abbreviare le definizioni (anziché partire dalle poche regole proprie del calcolo ad ogni derivazione)

#### 3.2 Regole di sostituzione (regole derivabili)
Vedi dispensa

#### 3.3 Regole di indebolimento (regole derivabili)
Vedi dispenza

L'idea delle regole di indebolimento è che se noi abbiamo un qualcosa derivabile sotto contesto Gamma, e sappiamo che $[\Gamma,\Delta]$ è un contesto, allora allo stesso modo possiamo derivare lo stesso giudizio col contesto esteso $[\Gamma,\Delta]$

$$\frac{J [\Gamma] \quad  [\Gamma,\Delta]\space cont}{J\space[\Gamma,\Delta]}$$

#### 3.4 Regole di Scambio
Vedi dispensa

Quando definiamo un contesto, stiamo anche indicando una sorta di progressione/costruzione del contesto stesso:

$$[\Gamma, \Delta]$$

Prima abbiamo definito Gamma e poi Delta.

Le regole di scambio permettono di scambiare l'ordine dei due sotto-contesti. Ovviamente questo può essere fatto se il secondo contesto non dipende da tipi del primo contesto.

---
## 4. Regole (principali) del tipo singoletto <a name="regsin"></a>
  <div style="text-align: right"><span style="color:orange">Lezione 8</span></div>
Come già accennato, il singoletto è il tipo più semplice, e le sue regole saranno paradigmatiche per gli altri tipi.

* **Regola di formazione del singoletto**
  
  $$\text{F-S)}\space \frac{\Gamma \space cont}{N_1 \space type \space \space [\Gamma]}$$


Possiamo già usare delle regole per creare i primi alberi di derivazione:
**Esempio**
Partiamo dal contesto vuoto (unico assioma della teoria dei tipi):

$$
\begin{matrix}
\text{F-S)} & [\space\space] \space cont \\
\hline
\text{F-C)} & N_1 \space type \space [\space\space] \\
\hline 
 & [x_1\in N_1]\space cont
\end{matrix}\qquad := \pi_1$$

Continuando, possiamo allungare $\pi_1$ aggiungendo un altro elemento:

$$\begin{matrix}
\text{F-S)} & [\space\space] \space cont \\
\hline
\text{F-C)} & N_1 \space type \space [\space\space] \\
\hline 
\text{F-S)} & [x_1\in N_1]\space cont\\
\hline
\text{F-C)} &N_1 \space type \space [x_1\in N_1] \\ 
\hline 
& [x_1\in N_1, x_2\in N_1]\space cont
\end{matrix}$$

Possiamo generalizzare ottenendo: 
$[x_1\in N_1,..., x_n\in N_1]\space cont$ dalle solo due regole di formazione del singoletto e formazione del contesto.

**Nota:** Il contesto non è telescopico (dove un sotto-contesto dipende da un altro), quindi volendo possiamo usare le regole di scambio a piacimento.

* **Regola di Introduzione del singoletto**
  
$$\text{I-S)}\space \frac{\Gamma \space cont}{* \in N_1 \space \space [\Gamma]}$$
  

* **Regola di Eliminazione del singoletto**
  
$$\text{E-S)}\space \frac{t_1 \in N_1 \space [\Gamma] \quad M(z) \space type \space [\Gamma, z \in N_1]\quad  c\in \overbrace{M(*)}^{M(z)[z/*]} \space \space [\Gamma]}{El_{N_1}(t, c) \in M(t)\space \space [\Gamma]}$$

* **Regola di Conversione del singoletto**

$$\text{C-S)}\space \frac{\quad M(z) \space type \space [\Gamma, z \in N_1]\quad  c\in M(*) \space[\Gamma]}{El_{N_1}(*, c) = c \in M(t)\space \space [\Gamma]}$$

La regola di eliminazione si può equivalentemente scrivere in un altro modo:
* **Regola di Eliminazione del singoletto 2**
  
$$\text{E-S)}_\text{Dipendente}\space \frac{M(z) \space type \space [\Gamma, z \in N_1]\quad  c\in M(*) \space \space [\Gamma]}{El_{N_1}(z, c) \in M(z)\space \space [\Gamma, z\in N_1]}$$

Si può dimostrare che usando $\text{E-S)}_{dip}$ + regole di sostituzione è equivalente ad $\text{E-S)}$.

L'eliminatore rappresenta un _ricorsore_: è una funzione definita per ricorsione su $N_1$:

* $El_{N_1}(z,c)[z/\ast] = El_{N_1}(\ast,c) = c \in M(\ast)$

***Nota personale:*** Fino a questo momento c'è un po' di confusione per quanto riguarda il concetto di singoletto e di Eliminatore: Se $El_{N_1}(\ast,c) = c$ dove $\ast$ è un elemento del singoletto, poiché il singoletto possiede un solo elemento per definizione, non dovrebbero essere tutti gli eliminatori uguali? Perché definire più termini del singoletto?

Credo che la risposta stia nel fatto di uguaglianza definizionale vs uguaglianza matematica ma ancora non mi è totalmente chiaro.

---
  <div style="text-align: right"><span style="color:orange">Lezione 9</span></div>

## 5. Altre regole strutturali derivabili <a name="regdev"></a>
Aggiungiamo altre regole strutturali (derivabili) molto utili per semplificare le future dimostrazioni. Sono regole derivabili, quindi possono essere ottenute dalla teoria che abbiamo enunciato e non postulate.

* **Primo Sanitary Check:**

$$
\frac{[\Gamma,\Delta]\space cont}{\Gamma \space cont}
$$

Se abbiamo derivato un contesto esteso, anche un pezzo del contesto può essere derivabile (occhio alle dipendenze! non stiamo scrivendo come conclusione $\Delta$ cont perché potrebbe dipendere da $\Gamma$).

* **Secondo Sanitary Check:**

$$\frac{J_1,...,J_n}{J}$$

  è derivabile, significa che $J_1, ..., J_n$ sono derivabili e quindi $J$ è derivabile dalla teoria.

* **Terzo Sanitary Check:**

$$\frac{A = B \space type \space [\Gamma]}{A \space type \space [\Gamma]}\qquad\qquad \frac{A = B \space type \space [\Gamma]}{B \space type \space [\Gamma]}$$

* **Quarto Sanitary Check:**

$$\frac{a\in A \space [\Gamma]}{A \space type \space [\Gamma]}$$

* **Quinto Sanitary Check:**

$$\frac{a = b\in A \space [\Gamma]}{a \in A \space [\Gamma]}\qquad\qquad \frac{a = b\in A \space [\Gamma]}{b \in A \space [\Gamma]}$$

---
#### Esercizio E1: Regola E-S) $\to$ Regola E-S)$_{dip}$
Ricordiamo la **Regola di Eliminazione del singoletto**
  
$$\text{E-S)}\space \frac{t_1 \in N_1 \space [\Gamma] \quad M(z) \space type \space [\Gamma, z \in N_1]\quad  c\in M(*) \space \space [\Gamma]}{El_{N_1}(t, c) \in M(t)\space \space [\Gamma]}$$

Notiamo che in questa regola:
  * $t$ è un termine qualsiasi, $t$ sta come metavariabile del tipo $N_1$
  * $N_1$ è un tipo fissato
  * $z$ è un termine che serve solo a dire che $M$ è un tipo qualsiasi che può dipendere da $N_1$
  * $\ast$ è una costante fissa, ma $c$ ed $M$ sono metavariabili.

Quindi possiamo dire che la regola di eliminazione è uno schema di regole, dove al posto di $t$, $M$, $c$ e $\Gamma$ possiamo mettere quello che vogliamo.

Possiamo riscrivere quindi la regola E-S) usando altri termini:
$$ \frac{t_1 \in N_1 \space [\Sigma] \quad M(\omega) \space type \space [\Sigma, \omega \in N_1]\quad  c\in M(*) \space \space [\Sigma]}{El_{N_1}(t, c) \in M(t)\space \space [\Sigma]}$$

Poniamo $\Sigma = \Gamma, z\in N_1$

$$\begin{matrix}
    \space & [\Gamma, z \in N_1] \space cont \\
    \hline
    \space & \overbrace{M(z) \space type \space [\Gamma, z\in N_1 ]}^{\text{per ipotesi}}\qquad z \in N_1 [\Gamma, z_\in N_1]\\
    \hline 
   \space  & c \in M(\ast) \space [\Gamma] \qquad  [\Gamma, z\in N_1]\space cont\\
   \hline
   \space  & \overbrace{M(z) \space type \space [\Gamma, z \in N_1, \omega \in N_1]}^{\text{per ipotesi}} \quad c \in M(\ast) \space [\Gamma, z\in N_1] \\
   \hline
    \text{F-S)} & [\Gamma, z\in N_1] \space cont \qquad [\Gamma, z\in N_1, \omega \in N_1] \space cont\\
    \hline
   \space  & N_1 \space type \space [\Gamma, z\in N_1]\qquad \omega\in N_1 \space [\Gamma, z\in N_1, \omega \in N_1]\\ 
   \hline
 ind & \overbrace{M(z) \space type\space[\Gamma, z\in N_1]}^{\text{per ipotesi}} \qquad [\Gamma,z\in N_1, \omega\in N_1] \space cont \\
 \hline
 sub & M(z) \space type \space [\Gamma, z\in N_1, \omega \in N_1] \quad \omega\in N_1 \space [\Gamma, z\in N_1, \omega \in N_1] \\ 
 \hline
 \space & M(\omega)\space type \space [\Gamma, z\in N_1] \\
 \hline
 \space & El_{N_1}(z, c) \in M(z)\space \space [\Gamma, z\in N_1] \\
\end{matrix}$$

$\text{E-S)}_{dip}$ è derivabile.

#### Altra interpretazione della regola di eliminazione:
Dalla regola di eliminazione dipendente:

$$\text{E-S)}_\text{Dip}\space \frac{\varphi(\omega) \space prop \space [\Gamma, \omega \in N_1]\quad  c\in \varphi(*) \space \space [\Gamma]}{El_{N_1}(\omega, c) \in \varphi(\omega)\space \space [\Gamma, \omega\in N_1]}$$

La tesi $El_{N_1}(\omega, c) \in \varphi(\omega)\space \space [\Gamma, \omega\in N_1]$ significa inoltre che $\varphi(\omega)$ è vera, quindi la regola di eliminazione può essere riscritta come:

$$\frac{\varphi(\ast) \text{ è vera} \space [\Gamma]}{\varphi(\omega) \text{ è vera}\space [\Gamma, \omega \in N_1]}$$

La regola di eliminazione tiene in se la regola di induzione, ovvero se hai la regola per l'elemento canonico $\ast$ allora la proposizione è vera per ogni elemento di $N_1$

---
  <div style="text-align: right"><span style="color:orange">Lezione 10</span></div>

## 6. Schema generale di produzione di regole definenti un tipo e i suoi termini  <a name="protip"></a>

1. Si danno le regole di formazione del tipo K

  $$\frac{[\Gamma] \space cont}{K \space type \space [\Gamma]}$$

2. Si danno le regole di introduzione dei suoi elementi canonici

  $$\frac{[\Gamma]\space cont}{\ast \in K \space [\Gamma]}$$

3. Si danno le regole di Eliminazione definienti un costruttore $El_K$ che a partire da elementi di $K$ ha valori in un tipo $M(z) \space type \space [\Gamma, z\in K]$ avendo come ipotesi/premessa che siano dati degli elementi in $M(z)$ sui valori canonici di K

4. Si danno le regole di conversione che stabiliscono che gli eliminatori in (3) sono di fatto definiti per ricorsione a partire dalle ipotesi appena dette.

5. Si danno le regole che stabiliscono che i costruttori di $K$ (in (2) e in (3)) conservano le uguaglianze definizionali dei termini da cui dipendono.

$$\frac{a_1, ..., a_n \in A}{costruttorre(a_1,...,a_n)\in B}$$

Il costruttore deve osservare la seguente regola:

$$\frac{\text{se }\quad a_1 = b_1 \in A_1, ..., a_n = b_n \in A_n}{cost(a_1,...,a_n) = cost(b_1, ..., b_n)}$$

Quindi vogliamo la seguente regola:

$$\frac{t_1 = t_2 \in N_1 \space [\Gamma] \quad c_1=c_2 \in M(\ast)\space [\Gamma]}{El_{N1}(t_1, c_1)= El_{N1}(t_2, c_2) \in M(t_1)\space [\Gamma]}$$

---
  <div style="text-align: right"><span style="color:orange">Lezione 11</span></div>

## 7. Perché la teoria dei tipi può essere pensata come un linguaggio di programmazione funzionale? <a name="tipcod"></a>
_"L'ugualianza definizionale tra dermini della teoria dei tipi (di Martin-Loef) è computabile"_

Ovvero esiste un programma/algoritmo tale che:

$$H \space : \space Giudizi \to \lbrace 0,1\rbrace$$

$$H(J)=\begin{cases}1 & \text{sse J è derivaible}\\ 0 & \text{sse J NON è derivabile}\end{cases}$$

Inoltre $J$ può essere:
* $A \space type \space [\Gamma]$
* $A = B \space type \space [\Gamma]$
* $a\in A \space [\Gamma]$
* $a = b \in A \space [\Gamma]$
* $[\Gamma]\space cont$

Quando ci interfacciamo tramite la teoria dei tipi con un proof assistant, il proof assistant ci dirà se un giudizio formulato come nella lista sopra sarà corretto oppure no.

**Nota**: Questa proprietà vale per teorie dei tipi dette "intensionali" o "computabili". Esempio: COQ, mentre per la HOTT non si sa ancora.

...

---
  <div style="text-align: right"><span style="color:orange">Lezione 12</span></div>

## 8. Regole del tipo dei numeri naturali <a name="regnat"></a>
1. **Regola di formazione del tipo numeri naturali**

$$\text{F-Nat)}\space\frac{\Gamma\space cont}{Nat\space type\space [\Gamma]}$$

2. **Regola di introduzione dei naturali**

$$\text{I-Nat)}\space\frac{\Gamma\space cont}{0 \in Nat\space [\Gamma]}\qquad \text{I-Nat2)}\space\frac{m \in Nat \space [\Gamma]}{succ(m) \in Nat\space [\Gamma]}$$

3. **Regola di eliminazione dei naturali (ricorsione dei naturali)**

**Def: Primitiva ricorsione** Se vogliamo definire un ricorsore $ rec: Nat^n \times Nat \to Nat$ dati:
- $g_0$ funzione $g_0 : Nat^m \to Nat$  
- $g_1$ funzione $g_1 : Nat^n \times Nat \times Nat\to Nat$ 

$$\begin{cases}
rec(n_1, n_m, 0)&:=g_0(n_1,n_m) \\
rec(n_1, n_m, k+1)&:=g_1(n_1, n_m, rec(n_1, n_m, k))
\end{cases}$$

Quindi la regola di eliminazione dei naturali sarà:

$$\frac{t\in Nat\space [\Gamma]\quad M(z) \space type \space [\Gamma, z\in Nat]\quad c\in M(0) \space [\Gamma]\quad e(x,y) \in M(succ(x))\space [\Gamma, x\in Nat, y\in M(x)]}{El_{Nat}(t, c, e) \in M(t)\space [\Gamma]} \quad \text{E-Nat)}$$

* $t$ rappresenta l'indice della ricorsione;
* $M$ è la funzione che ci porta dai naturali al valore;
* $c$ è il valore che il ricorsore assume sullo 0;
* $e$ ci serve per fare il passo successivo, x rappresenta il passo a cui siamo arrivati, e y il valore a cui siamo.

4. **Regola di Conversione**

   Questa regola indica il comportamento della ricorsione al numero 0 (primo termine della ricorsione)

$$\frac{M(z) \space type \space [\Gamma, z\in Nat]\quad c \in M(0)\space [\Gamma]\quad e(x,y)\in M(succ(x))\space [\Gamma, x \in Nat, y \in M(x)]}{El_{Nat}(0,c,e) = c \in M(0)\space [\Gamma]}\space {C_1\text{-S)}}
$$

5. **Seconda Regola di Conversione**
    
    Questa regola indica il comportamento della ricorsione quando passiamo da $m$ a $succ(m)$ $(m\to m+1)$

$$\frac{m \in Nat \space [\Gamma] \quad M(z) \space type \space [\Gamma, z\in Nat]\quad c \in M(0)\space [\Gamma]\quad e(x,y)\in M(succ(x))\space [\Gamma, x \in Nat, y \in M(x)]}{El_{Nat}(succ(m),c,e) = e(m, El_{Nat}(m,c,e)) \in M(succ(m))\space [\Gamma]}\space {C_2\text{-S)}}
$$

---
  <div style="text-align: right"><span style="color:orange">Lezione 13</span></div>

## 9. Somma tra numeri naturali <a name="sommanat"></a>

Quello che vogliamo fare in questa sezione è scrivere l'operatore '+' come un eliminatore:

$$w + z \in Nat\space \space (w \in Nat, z\in Nat)$$

In [E2](#elsomma) vi è il procedimento su come ottenere la somma come eliminatore. Il risultato è:

$$\text{E-Nat}_{dip})\quad \frac{\begin{matrix}Nat \space type \space [\omega\in Nat, z\in Nat]\\ 
\omega \in Nat \space [\omega \in Nat]\\ 
succ(y)\in Nat \space[\omega\in Nat, x \in Nat, y \in Nat]\end{matrix}}{El_{Nat}(z,\omega,(x,y).succ(y))\in Nat\space [\omega\in Nat, z\in Nat]}$$

Verifichiamo i valori della somma:

Per la regola di converisone abbiamo che:

$$El_{Nat}(0,\omega, (x,y).succ(y))\to_1 \omega$$

Ovvero $\omega + 0 = \omega$.

Per $succ(0)$ abbiamo invece:

$$El_{Nat}(succ(0), \omega, (x,y).succ(y))\to_1$$

$$\to_1 succ(El_{Nat}(0,\omega,(x,y).succ(y)))\to_1 succ(\omega)\in Nat$$

Ovvero  $\omega + 1 = succ(\omega)$

> _"L'uguaglianza definizionale tra numeri naturali in teoria dei tipi di Martin-Loef (con le regole date) **NON** è l'uguaglianza aritmetica in matematica."_

Abbiamo quindi creato una forma di somma che chiameremo $+_1$, quindi abbiamo creato un programma che calcosa:

$$\omega +_1 z  = El_{Nat}(z,\omega, (x,y).succ(y))$$

Non è l'unico programa, avremmo potuto creare quello che applica la somma al secondo termine $\omega + z \to z + \omega$, ma avrebbe coinvolto scambio di variabili etc.

> Cosa succede se io al posto di $\omega$ metto 0?

$$\omega +_1 z [w/0] := El_{Nat}(0,z,(x,y).succ(y))$$

Questa è una brutta notizia, perché $\omega +_1 z [w/0] := El_{Nat}(0,z,(x,y).succ(y))$ è in forma normale, non si riesce a ridurre a nulla perché è già ridotto. Quindi 

$$0+_1 z \quad\text{ è già un valore}$$

Mentre

$$\omega +_1 0 \to_1 \omega \quad \text{ per la regola di conversione}$$

Quindi **NON** si deriva che:

$$0 +_1 z = z \in Nat \space [z\in Nat]$$

Mentre 

$$ \omega +_1 0 = \omega \in Nat \space [\omega \in Nat]$$

Non esiste nessuna strategia deterministica per ridurre $0+z$ a $z$

> La relazione di uguaglianza definizionale in Nat con variabili **NON** è in generale la relazione di uguaglianza aritmetica.

--- 
<div style="text-align: right"><span style="color:orange">Lezione 14</span></div>

## 10. Tipo delle liste di un tipo <a name="liste"></a>

### Regole di formazione
* **Regola di formazione delle lise**

$$\text{F-List)}\quad \frac{A \space type \space [\Gamma]}{list(A) \space type \space [\Gamma]}$$

* **Regola di uguaglianza tra tipi**

$$\text{Eq-list}\quad \frac{A_1 = A_2 \space type \space [\Gamma]}{list(A_1)=list(A_2)\space type \space[\Gamma]}$$

Prima volta che utilizziamo il giudizio di uguaglianza tra tipi, abbiamo bisogno di scrivere il fatto che le liste preservano l'uguaglianza tra tipi. Questo ci servirà nel caso in cui $A_1$ e $A_2$ sono dei tipi dipendenti.

### Regole di introduzione

* **Regola di introduzione della lista vuota**

  Per introdurre la lista vuota, non possiamo mettere come ipotesi "$[\Gamma] \space cont$" non è sufficiente perché il tipo $A$ potrebbe essere mal-formato, ovvero non tipato. E' una sottigliezza.

$$\text{$I_1$-list)}\quad \frac{list(A) \space type \space [\Gamma]}{nil \in list(A)\space [\Gamma]}$$

* **Regola di estensione della lista**

   $$\text{$I_2$-list)}\quad\frac{S \in list(A)\space [\Gamma]\quad a\in A\space [\Gamma]}{\underbrace{cons}_{\text{constructor}}(S,a) \in list(A)\space [\Gamma]}$$

   $cons(S,a)$ corrisponde alla lista S con a appendato.

* **Regola di uguaglianza delle liste**

   $$\text{eq-$I_2$-list)}\quad\frac{S_1 = S_2 \in list(A)\space [\Gamma]\quad a_1 = a_2 \in A\space [\Gamma]}{cons(s_1,a_1)= cons(s_2,a_2) \in list(A)\space [\Gamma]}$$

**Nota**: non mettiamo una regola di uguaglianza delle liste vuote perché $nil$ è una costante ed è uguale a se stessa per la riflessività della uguaglianza.

### Regole di riduzione
Prima di introdurre le regole di riduzione ed eliminazione, notiamo che esiste una relazione insiemistica tra i numeri naturali e le liste di singoletti:

$$\begin{matrix}
& Nat & \longleftrightarrow & List(N_1) \\
\hline
h\space type\space list(N_1) & lenght(h) & \longleftrightarrow & h \\
& 0 & \longleftrightarrow & nil\\
& & \vdots & \\
& 5 & \longleftrightarrow & [\ast,\ast,\ast,\ast,\ast]\\
& & \vdots & \\
\end{matrix}$$

* **Regole di riduzione**

$$\frac{s_1\to_1 s_2}{cons(s_1,a)\to_1 cons(s_2,a)}\qquad \frac{a_1\to a_2}{cons(s,a_1)\to_1 cons(s,a_2)}$$

Notiamo che se abbiamo una lista del tipo singoletto $N_1$

$$\begin{cases}
cons(nil, \ast) \equiv [\ast]\\
cons(nil, x) \space \space x \in N_1
\end{cases}$$

Entrambe sono forme normali e non avremo modo per dire che sono uguali (definizionalmente).

### Regole di eliminazione

* **Prima regola di eliminazione**

$$\text{E-list)}\quad\frac{\begin{matrix}
M(z) \space type \space [\Gamma,z\in list(A)]\quad t\in list(A)\space [\Gamma] \quad c \in M(nil)\space [\Gamma]\\
e(x,w,y) \in M(cons(x,w)) \space [\Gamma, x\in list(A), w \in A, y \in M(x)]
\end{matrix}}{El_{list}(t, c, (x,w,y).e(x,w,y)) \in M(t) \space [\Gamma]}$$

Come al solito, per motivi pratici conviene usare la forma dipendente: 

$$\text{E-list)}_{dip}\quad\frac{\begin{matrix} M(z) \space type \space [\Gamma,z\in list(A)]\quad c \in M(nil)\space [\Gamma]\\
e(x,w,y) \in M(cons(x,w)) \space [\Gamma, x\in list(A), w \in A, y \in M(x)]
\end{matrix}}{El_{list}(z, c, (x,w,y).e(x,w,y)) \in M(z) \space [\Gamma, z\in list(A)]}$$

Dove $M(z)$ è una meta-variabile per un tipo qualsiasi, come meta-variabile potrei usare anche la lettera $D$:

$$\text{E-list)}_{dip}\quad\frac{\begin{matrix} D \space type \space [\Gamma,z\in list(A)]\quad c \in D[z/nil]\space [\Gamma]\\
e(x,w,y) \in D[z/cons(x,w)]\space [\Gamma, x\in list(A), w \in A, y \in D[z/x]]
\end{matrix}}{El_{list}(z, c, e) \in D \space [\Gamma, z\in list(A)]}$$

* **Regola di uguaglianza dell'eliminatore**

$$\text{Eq-E-list)}_{dip}\quad\frac{\begin{matrix} t_1 = t_2 \in list(A) \space [\Gamma] \quad c_1 = c_2 \in M(nil) \space [\Gamma]\\
e_1(x,w,y) = e_2(x,w,y) \in M(cons(x,w)) \space [\Gamma, x\in list(A), w \in A, y \in M(x)]
\end{matrix}}{El_{list}(t_1, c_1, e_1) = El_{list}(t_2, c_2, e_2) \in M(t_1)\space [\Gamma]}$$

Dove $M(t_1)= M(t_2)$ per le regole di costruzione quindi nella tesi avremmo anche potuto scrivere $M(t_2)$.

* **Regole di riduzione dell'eliminatore**

$$\frac{t_1\to_1 t_2}{El_{list}(t_1,c,e)\to_1 El_{list}(t_2, c,e)}\qquad\frac{c_1\to_1 c_2}{El_{list}(t,c_1,e)\to_1 El_{list}(t,c_2,e)}$$

(Assioma)

$$El_{list}(nil,c,e)\to_1 c$$

* **Regole di conversione**

  1.

$$C_1\text{-list})\qquad \frac{\begin{matrix}
M(z) \space type \space [\Gamma,z\in list(A)] \quad c\in M(nil) \space [\Gamma]\\
e(x,w,y) \in M(cons(x,w)) \space [\Gamma, x\in list(A), w \in A, y \in M(x)]
\end{matrix}}{El_{list}(nil,c,e)=c \in M(nil)\space [\Gamma]}$$

  2. 

$$C_2\text{-list})\qquad \frac{\begin{matrix}
M(z) \space type \space [\Gamma,z\in list(A)] \quad c\in M(nil) \space [\Gamma]\\
S \in list(A)\space [\Gamma] \quad a \in A \space [\Gamma]\\
\overbrace{e(x,w,y)}^{h} \in M(cons(x,w)) \space [\Gamma, x\in list(A), w \in A, y \in M(x)]
\end{matrix}}{El_{list}(cons(S,a),c,e)=\underbrace{e(s,a,El_{list}(s,c,e))}_{h[x/s, w/a, y/El_{list}(s,c,e)]} \in M(cons(s,a))\space [\Gamma]}$$

  * $\beta$-riduzione associata a $C_2$:

    $$El_{list}(cons(s,a),c,e)\to_1 e(s,a,El_{list}(s,c,e))$$ 

--- 
<div style="text-align: right"><span style="color:orange">Lezione 15</span></div>

## 11. Somma disgiunta (disjoint-sum type)<a name="somdis"></a>
La somma disgiunta è un tipo induttivo come quelli già visti: $N_1$ (singoletto), $Nat$ (naturali), $list(A)$ lista.

Piccolo spoiler, questo tipo ci servirà a costruire gli insiemi finiti a partire dal tipo singoletto:

Si può dimostrare ([EX4](#exbool)) la seguente relazione:
$$N_1 + N_1 \to \space type \space Bool$$

Prima di introdurre le regole relative al tipo, introduciamo brevemente la _somma disgiunta_.

> Da [__Wikipedia__](https://en.wikipedia.org/wiki/Disjoint_union): Spiegazione della somma disgiunta
> 
Considera due set:

$$\begin{cases}
  A_0 = \lbrace 5,6,7 \rbrace \\
  A_1 = \lbrace 5,6   \rbrace
\end{cases}$$
  
Per creare il set somma disgiunta, indiciamo gli elementi dei due set in base al set di partenza:

$$\begin{cases}
  A_0^\ast = \lbrace (5,0),(6,0),(7,0) \rbrace \\
  A_1^\ast = \lbrace (5,1),(6,1)   \rbrace
\end{cases}$$

La somma disgiunta dei due set $A_0$ e $A_1$ è l'unione dei due set indiaicati: 

$$A_0 \sqcup A_1 = A_0^\ast \sqcup A_1^\ast = \lbrace (5,0),(6,0),(7,0), (5,1),(6,1)  \rbrace$$

Le funzioni $inl(a)$ e $inr(a)$ che verranno introdotte nelle regole del tipo, servono a trasformare l'elemento da $A$ in $A^\ast$

> $\space$


### Regole di Formazione

* **Regola di formazione**

$$\text{F-+)}\quad \frac{B \space type \space [\Gamma]\quad C \space type \space [\Gamma]}{B+C \space type \space [\Gamma]}$$

### Regole di introduzione

* **Prima regola di introduzione**

$$\text{I$_1$-+)}\quad \frac{b \in B \space [\Gamma]\quad B+C \space type \space [\Gamma]}{inl(b) \in B+C \space [\Gamma]}$$

* **Seconda regola di introduzione**

$$\text{I$_2$-+)}\quad \frac{
  c \in C \space [\Gamma]\quad B+C \space type \space [\Gamma]}{inr(c) \in B+C \space [\Gamma]}$$

Ovviamente per come sono costruiti i due tipi sopra, solo $inr(c)$ ed $inl(b)$ fanno parte del tipo somma disgiunta $B+C$, nel caso degenere invece in cui si ha $A+A$ non importa come mettiamo il termine $a$, $inr(a)$ ed $inl(a)$ sono entrambi $\in A+A$, questo implica che:

$$A + A\quad \text{non è isomorfo ad}\quad A$$

### Regole di uguaglianza
* **Regola di uguaglianza**

$$\text{eq-F-+)}\quad\frac{B_1 = B_2 \space type \space [\Gamma]\quad C_1 = C_2 \space type \space [\Gamma]}{B_1 + C_1 = B_2 + C_2\space type \space [\Gamma]}$$

### Regole di eliminazione 

$$\text{E-+)}\quad\frac{\begin{matrix}
M(z) \space type \space [\Gamma, z\in B+C]\qquad t \in B+C \space [\Gamma]\\
e_B(x_1)\in M(inl(x)) \space [\Gamma, x_1\in B] \quad e_C(x_2)\in M(inr(x_2))\space [\Gamma, x_2 \in C]
\end{matrix}}{El_+(t, e_B, e_C)\in M(t)\space [\Gamma]} $$

Dove $e_B$ ed $e_C$ indicano rispettivamente cosa succede se l'elemento viene inserito da sinistra o da destra.

Come sempre inseriamo la regola variante più pratica:

$$\text{E-+)}_{dip}\quad\frac{\begin{matrix}
M(z) \space type \space [\Gamma, z\in B+C]\\
e_B(x_1)\in M(inl(x)) \space [\Gamma, x_1\in B] \quad e_C(x_2)\in M(inr(x_2))\space [\Gamma, x_2 \in C]
\end{matrix}}{El_+(z, e_B, e_C)\in M(z)\space [\Gamma, z \in B+C]} $$

### Regole di conversione
Le regole sono due, perché dobbiamo coprire i casi in cui l'elemento provenga da sinistra o da destra.

* **Regola di Conversione per elemento da sinistra**
  
$$\text{C1)}\quad\frac{\begin{matrix}
M(z) \space type \space [\Gamma, z\in B+C] \quad b \in B \space [\Gamma]\\
e_B(x_1)\in M(inl(x)) \space [\Gamma, x_1\in B] \quad e_C(x_2)\in M(inr(x_2))\space [\Gamma, x_2 \in C]
\end{matrix}}{El_+(inj(b), e_B, e_C)=e_B(b)\in M(inl(b))\space [\Gamma]}$$

* **Regola di Conversione per elemento da destra**
  
$$\text{C2)}\quad\frac{\begin{matrix}
M(z) \space type \space [\Gamma, z\in B+C] \quad c \in C \space [\Gamma]\\
e_B(x_1)\in M(inl(x)) \space [\Gamma, x_1\in B] \quad e_C(x_2)\in M(inr(x_2))\space [\Gamma, x_2 \in C]
\end{matrix}}{El_+(inj(b), e_B, e_C)=e_C(c)\in M(inr(c))\space [\Gamma]}$$


Possiamo interpretare la formula di relazione del tipo somma disgiunta come un OR logico (a sinistra):

$$\text{E-+)}_{dip}\quad\frac{\begin{matrix}
M(z) \space type \space [\Gamma, z\in B+C]\\
e_B(x_1)\in M(inl(x)) \space [\Gamma, x_1\in B] \quad e_C(x_2)\in M(inr(x_2))\space [\Gamma, x_2 \in C]
\end{matrix}}{El_+(z, e_B, e_C)\in M(z)\space [\Gamma, z \in B+C]} $$

$$\downarrow$$

$$\frac{\begin{matrix}
\xi \space prop \space [\Gamma]\\
\xi \text{ è vero} \space [\Gamma, \beta \text{ è vero}] \quad \xi \text{ è vero} \space [\Gamma, \gamma \text{ è vero}]
\end{matrix}}{\xi \text{ è vero} \space [\Gamma, \beta\lor \gamma \text{ è vero}]} $$

$$\downarrow$$

$$\frac{\beta\space prop \space [\Gamma] \qquad \gamma \space prop \space [\Gamma]}{\beta \lor\gamma \space prop\space [\Gamma]}$$

--- 
<div style="text-align: right"><span style="color:orange">Lezione 16</span></div>

## 12. Tipo uguaglianza proposizionale (o identità proposizionale)<a name="ugprop"></a>
(Tipo di uguaglianza di Martin-Loef)

Questo è un esempio di **Tipo dipendente** in modo primitivo.

### Regola di formazione:

$$\text{F-Id)}\quad \frac{A \space type \space [\Gamma] \quad a \in A \space [\Gamma] \quad b \in A \space [\Gamma]}{Id(A,a,b)\space type \space [\Gamma]}$$

$Id(A,a,b)$ viene pensata come una proposizione che verrà abitata dalle sue dimostrazioni.

### Regole di uguaglianza

$$\frac{A_1=A_2\space type \space [\Gamma]\quad a_1 = a_2 \in A_1\space [\Gamma]\quad b_1 = b_2 \in A_1\space [\Gamma]}{Id(A_1,a_1,b_1) = Id(A_2, a_2, b_2) \space type \space [\Gamma]}$$

### Regole di introduzione
L'uguaglianza è riflessiva, ogni elemento è uguale proposizionalmente a se stesso:

$$\text{I-Id)}\quad \frac{a\in A\space [\Gamma]}{id(a)\in Id(A,a,a)\space [\Gamma]}$$

$$\text{eq-I-Id)}\quad \frac{a_1 = a_2 \in A\space [\Gamma]}{id(a_1) = id(a_2) \in \underbrace{Id(A,a_1,a_1)}_{= Id(A,a_2, a_2)}\space [\Gamma]}$$

### Regole di eliminazione

* **Regola derivabile**: _"Gli elementi del tipo Identità sono generati intuitivamente a partire dagli elementi canonici, in altre parole, il Tipo Identità si dice generato intuitivamente dalla proprietà riflessiva degli elementi di A"_
$$\frac{A \space type \space [\Gamma]\quad [\Gamma, z_1\in A,z_2\in A]}{Id(A,z_1,z_2)\space type \space [\Gamma, z_1\in A, z_2\in A]}$$

L'eliminatore che costruiremo non dipenderà solo da un elemento di $Id(A,a,b)$ ma vogliamo che dipenda anche da $a$ e $b$ stessi, quindi il tipo di partenza $M$ sarà $M(z_1,z_2,z_3) \space type \space [\Gamma, z_1 \in A, z_2\in A, z_3 \in Id(A,z_1,z_2)]$

$$\text{E-Id)}\quad \frac{\begin{matrix}
M(z_1,z_2,z_3) \space type \space [\Gamma, z_1 \in A, z_2\in A, z_3 \in Id(A,z_1,z_2)]\\
a \in A \space [\Gamma]\quad b \in A \space [\Gamma] \\
t \in Id (A,a,b)\space [\Gamma]\\
e(x) \in M(x,x,id(x))\space [\Gamma,x\in A]
\end{matrix}}{El_{Id}(t,(x).e(x))\in M(a,b,t)\space [\Gamma]}$$

$\space$

$$\text{E-Id)}_{dip}\quad \frac{\begin{matrix}
M(z_1,z_2,z_3) \space type \space [\Gamma, z_1 \in A, z_2\in A, z_3 \in Id(A,z_1,z_2)]\\
e(x) \in M(x,x,id(x))\space [\Gamma,x\in A]
\end{matrix}}{El_{Id}(t,(x).e(x))\in M(a,b,t) \space [\Gamma, z_1\in A, z_2 \in A, z_3\in Id(A,z_1,z_2)]}$$

### Regola di conversione

$$\text{C-Id)}\quad \frac{a\in A\space [\Gamma]\quad e(x) \in M(x,x,id(x))\space [\Gamma, x\in A]}{El_{Id}(id(a),(x).e(x)) = e(a) \in M(a,a,id(a))\space [\Gamma]}$$

### Lemma

E' derivabile la seguente proprietà:

$$\frac{a=b\in A\space [\Gamma]}{id(a)\in Id(A,a,b)}$$

Ovvero il tipo uguaglianza proposizionale rende uguali termini che sono uguali definizionalmente, in generale il viceversa **NON** vale

$$p\in Id(A,a,b) \qquad\begin{matrix}\longrightarrow\\ \leftarrow NO\end{matrix}\qquad a=b\in A\space [\Gamma] $$

**Dimostrazione:**

Sappiamo che:

$$\frac{\begin{matrix}a=b\in A\space [\Gamma] \\
\hline
a\in A\space [\Gamma]\end{matrix}}{id(a)\in Id(A,a,a)\space[\Gamma]}$$

Inoltre dalle regole di del tipo abbiamo:

$$\frac{\begin{matrix}a\in A \space [\Gamma]\\
\hline 
A \space type \space [\Gamma]\end{matrix}}{A = A \space type \space [\Gamma]}$$

Inoltre sempre dall'ipotesi $a\in A\space [\Gamma]$ e usando l'ipotesi $a=b\in A\space [\Gamma]$ abbiamo:

$$\frac{a\in A \space [\Gamma]\quad a=b\in A \space [\Gamma]}{Id(A,a,a)=Id(A,a,b) \space type \space [\Gamma]}$$

Combinando il tutto otteniamo

$$\frac{id(a)\in Id(A,a,a) \space [\Gamma]\quad Id(A,a,a)=Id(A,a,b) \space type \space [\Gamma]}{id(a)\in Id(A,a,b)\space [\Gamma]}$$

--- 
<div style="text-align: right"><span style="color:orange">Lezione 17</span></div>

## 13. Tipo Somma indiciata Forte <a name="strindsumtype"></a>

Questo tipo (induttivo) è un _"potenziamento (indiciato) espressivo"_ del tipo somma [disgiunta binaria](#somdis) che abbiamo già visto.

$\dot{\cup}$ è il simbolo di unione disgiunta,

Dal punto di vista set-teoretico la somma indiciata forte rappresenta l'unione disgiunta di una famiglia di insiemi:

$$\dot{\cup}_{x\in B \space set}C(x) := \lbrace(b,c) \quad b\in B \space and \space c\in C(b)\rbrace$$

### Regole di Formazione:
Il tipo somma indiciata forte è un tipo induttivo di tipi dipendenti:

$$\Sigma\text{-F)}\quad \frac{C(x)\space type \space [\Gamma,x\in B]}{\sum_{x\in B} C(x)\space type \space[\Gamma]}$$

### Regola di Introduzione

$$\Sigma\text{-I)}\quad \frac{\begin{matrix}
\sum_{x\in B} C(x)\space type \space [\Gamma]\\
b\in B\space [\Gamma]\space c\in C(b) \space [\Gamma]\end{matrix}}{<b,c> \in \sum_{x\in B} C(x)\space [\Gamma]}$$

Dove $\lt b,c \gt$ indica la coppia dei termini $b$ e $c$.

### Regole di uguaglianza

$$\text{eq-F-$\Sigma$)}\quad\frac{B_1=B_2 \space type \space [\Gamma] \quad C_1(x)=C_2(x) \space type \space [\Gamma,x\in B]}{\sum_{x\in B_1}C_1(x) = \sum_{x\in B_2}C_2(x)\space type \space[\Gamma]}$$

$$\text{eq-I-$\Sigma$)}\quad\frac{b_1=b_2 \in B\space [\Gamma] \quad c_1(x)=c_2\in C(b_1) \space type \space [\Gamma]}{<b_1,c_1> = <b_2,c_2> \in \sum_{x\in B}C(x) \space[\Gamma]}$$

### Regole di riduzione

$$\frac{b_1\to_1 b_2}{<b_1,c>\to_1 <b_2,c>}\qquad \frac{c_1\to_1 c_2}{<b,c_1>\to_1 <b,c_2>}$$

$$El_{\Sigma}(<b,c>,e)\to_1 e(b,c)$$

### Regole di eliminazione

$$\text{E-$\Sigma$)}\quad\frac{\begin{matrix}
M(z)\space type \space [\Gamma,z\in \sum_{x\in B}C(x)]\\
t \in \sum_{x_\in B}C(x)\space [\Gamma]\\
e(x,y) \in M(<x,y>) \space [\Gamma,x\in B,y \in C(x)]
\end{matrix}}{El_{\Sigma}(t,(x,y).e(x,y))\in M(t)\space [\Gamma]}$$

$$\text{E-$\Sigma$)}_{dip}\quad\frac{\begin{matrix}
M(z)\space type \space [\Gamma,z\in \sum_{x\in B}C(x)]\\
e(x,y) \in M(<x,y>) \space [\Gamma,x\in B,y \in C(x)]
\end{matrix}}{El_{\Sigma}(t,(x,y).e(x,y))\in M(t)\space [\Gamma, z\in \sum_{x\in B}C(x)]}$$

**Regola di uguaglianza dell'eliminatore**

$$\text{eq-E-$\Sigma$)}\quad\frac{\begin{matrix}
M(z)\space type \space [\Gamma,z\in \sum_{x\in B}C(x)]\\
t_1 = t_2 \in \sum_{x_\in B}C(x)\space [\Gamma]\\
e_1(x,y) = e_2(x,y) \in M(<x,y>) \space [\Gamma,x\in B,y \in C(x)]
\end{matrix}}{El_{\Sigma}(t_1,e_1)=El_{\Sigma}(t_2,e_2)\in M(t)\space [\Gamma]}$$

### Regola di conversione
$$\text{C-$\Sigma$)}\quad\frac{\begin{matrix}
M(z)\space type \space [\Gamma,z\in \sum_{x\in B}C(x)]\\
b \in B\space[\Gamma]\quad c \in C(b)\space [\Gamma]\\
e(x,y)\in M(<x,y>) \space [\Gamma,x\in B,y \in C(x)]
\end{matrix}}{El_{\Sigma}(<b,c>,e)=e(b,c)\in M(<b,c>)\space [\Gamma]}$$

--- 
<div style="text-align: right"><span style="color:orange">Lezione 18</span></div>

### 13.1 "La somma indiciata forte è un potenziamento con tipi dipendenti del tipo prodotto cartesiano" <a name="prodcart"></a>

$$\Sigma_{x\in B} C(x) \equiv \dot{\cup}_{x\in B} C(x) := \lbrace (b,c) : b \in B, c \in C(b)\rbrace$$

Se noi consideriamo $C(x) = C'\space$ tipo costante (non dipendente):

$$\Sigma_{x\in B} C \equiv \dot{\cup}_{x\in B} C := \lbrace (b,c) : b \in B, c \in C'\rbrace \simeq B \times C'$$

Quindi il prodotto cartesiano sarà definito come:

$$B\times C  := \Sigma_{x\in B} C$$

$$\frac{B \space type \space [\Gamma] \quad \frac{C \space type \space [\Gamma]}{C \space type \space [\Gamma, \space x\in B]}\space ind)}{B\times C := \Sigma_{x\in B} C}\quad \text{F-$\Sigma$)}$$

#### Regole del tipo prodotto cartesiano:

* **Formazione** 

$$\frac{B \space type \space [\Gamma]\quad C \space type \space [\Gamma]}{B\times C \space type \space [\Gamma]}$$

* **Introduzione**

$$\frac{b\in B\space [\Gamma]\quad c \in C \space [\Gamma]}{<b,c>\in B\times C\space [\Gamma]}$$

* **Eliminazione**

$$\frac{d\in B\times C\space [\Gamma]}{\pi_1 d \in B\space [\Gamma]}\quad \frac{d \in B\times C\space [\Gamma]}{\pi_2 d \in C\space [\Gamma]}$$

$\pi_1 d$ e $\pi_2 d$ sono "proiezioni" applicate su $d$, se consideriamo $d:=<b,c>$ allora:

$$\begin{cases}
\pi_1 d =\pi_1 <b,c> = b \in B\qquad & \pi_1(<,b,c>)\to_1 b\\
\pi_2 d = \pi_2 <b,c> = c \in C & \pi_2(<,b,c>)\to_1 c
\end{cases}$$

$$\frac{b\in B\space [\Gamma]\quad c \in C\space [\Gamma]}{\pi_1 (<b,c>) = b \in B\space [\Gamma]}\quad \frac{b\in B\space [\Gamma]\quad c \in C\space [\Gamma]}{\pi_2 (<b,c>) = c \in B\space [\Gamma]}$$

I costruttori si ricavano dalla regola di eliminazione (dipendente) del prodotto indiciato forte, adattato per $C(x)=C$

Ricordiamo la regola di eliminazione (dipendente):

$$\text{E-$\Sigma$)}_{dip}\quad\frac{\begin{matrix}
M(z)\space type \space [\Gamma,z\in \sum_{x\in B}C(x)]\\
e(x,y) \in M(<x,y>) \space [\Gamma,x\in B,y \in C(x)]
\end{matrix}}{El_{\Sigma}(t,(x,y).e(x,y))\in M(t)\space [\Gamma, z\in \sum_{x\in B}C(x)]}$$

Nel caso del prodotto cartesiano avremo:

$$\frac{?}{\pi_1 z\in \underbrace{B}_{M(z)} \space [z\in \Sigma_{x\in B} C]}$$

$$\frac{\begin{matrix}
B \space type \space [\Gamma,z\in \sum_{x\in B}C]\\
e(x,y)\equiv x \in  B\space [\Gamma,x\in B,y \in C]
\end{matrix}}{\underbrace{El_{\Sigma}(z,(x,y).x)}_{\pi_1 z}\in B \space [z\in \Sigma_{x\in B} C]}$$

Analogamente per la seconda proiezione abbiamo:

$$\frac{\begin{matrix}
B \space type \space [\Gamma,z\in \sum_{x\in B}C]\\
e(x,y)\equiv y \in  B\space [\Gamma,x\in B,y \in C]
\end{matrix}}{\underbrace{El_{\Sigma}(z,(x,y).y)}_{\pi_2 z}\in C \space [z\in \Sigma_{x\in B} C]}$$

E' possibile definire le proiezioni anche nel caso generale della somma indiciata forte seguendo lo stesso metodo:

$$\begin{cases}
\pi_1 z := El_{\Sigma}(z, (x,y).x) \in B \space [\Gamma, z \in \Sigma_{x\in B} C(x)]\\
\pi_2 z := El_{\Sigma}(z,(x,y).y)\in C(\pi_1 z)\space [\Gamma, z \in \Sigma_{x\in B}C(x)]
\end{cases}$$

--- 
<div style="text-align: right"><span style="color:orange">Lezione 19</span></div>

### 13.2 Uso del tipo $\Sigma_{x\in B} C(x)$ <a name="usisif"></a>

1. **Unione indiciata insiemistica**
2. **Uso set-teoretico** (Assioma di separazione)
3. **Uso logico**
   
* **Uso set-teoretico:**

Cosa dice l'assioma di separazione?

_Dato_ $B$ _insieme_:

$$\text{\textit{esiste}} \quad\lbrace x\in B | \underbrace{\phi(x)}_{\text{predicato}}\rbrace$$

Per cui per ogni y insieme:

$$y\in \lbrace x\in B | \phi(x)\rbrace\space\space \text{vale} \space\longleftrightarrow \phi(y) \space \space \text{vale}$$

Introduciamo la seguente proposizione in base all'assioma:

$$\frac{\phi(x) \space prop\space(type) \space[\Gamma, x \in B]}{\Sigma_{x\in B} \phi(x)\space type \space [\Gamma]}$$

Tramite il tipo somma indiciata forte, le proposizioni sono indicate con il tipo delle loro dimostrazioni

$$<b,pf> \in \Sigma_{x\in B}\phi(x)$$

Dove $pf \in \phi(b)$ dice che $b$ soddisfa $\phi(x)$

Con questa costruzione abbiamo:

$$z \in \lbrace \underbrace{x\in B}_{\Sigma_{x\in B} C(x)}|\phi(x)\rbrace \Longleftrightarrow \phi(\pi_1 z) \space \space \text{vale}$$

Grazie al tipo di somma indiciata forte introdotta di Martin-Loef e in particolare grazie a questa proprietà, è stato possibile inglobare la Set-Theory nella teoria dei tipi.

* **Uso logico**
  
Se:

$$\frac{\underbrace{C(x)}_{=\phi(x)\space\text{proposizione}}type \space \underbrace{[x\in B]}_{set}}{\exist_{x\in B}\phi(x) :=\Sigma_{x\in B}\phi(x) \space \underbrace{type}_{\to \space prop} \space [\Gamma]}$$

Se noi invece di considerare il set ed applicare l'assioma di separazione, lo consideriamo come proposizione, allora vediamo che le sue regole rappresentano il tipo della _quantificazione esistenziale in Logica_ $\exist$.

---

**Definizione** Un _proof-term_è un elemento $t\in \phi\space [\Gamma]$ ove $\phi$ è una proposizione.

Consideriamo $\xi\space prop \space [\Gamma, x_1\in \phi_1, ..., x_n \in \phi_n]$

$\xi$ dipende dal contesto $\Gamma$ e da le $n$ proprietà $\phi$

Se consideriamo un _proof-term_:

$$pf\in \xi\space prop \space [\Gamma, x_1\in \phi_1, ..., x_n \in \phi_n]$$

Allora 

$$\xi\space\space\text{è vero}\quad [\Gamma,\phi_1\space\space\text{è vero},...,\phi_n\space\space\text{è vero}] $$

$$\equiv$$

$$\phi_1, ...,\phi_n \vdash \xi$$

Consideriamo le regole di introduzione e di eliminazione con le proposizioni:

* **Regola di introduzione**
  
$$\text{I)}\quad\frac{\begin{matrix}
(\exist_{x\in B} \phi(x)\space \space \text{ben formato} \space type \space [\Gamma])\\
b \in B\space [\Gamma]\quad \underbrace{c \in \phi(b)\space [\Gamma]}_{\phi(b) \space\space\text{è vera}\space [\Gamma,\gamma_1,...,\gamma_n]}
\end{matrix}}{\underbrace{\lt b,c\gt \in \Sigma_{x\in B}C(x)\space [\Gamma]}_{\exist_{x\in B}\phi(x) \space\space \text{è vera}\space [\Gamma]}}
$$

La regola di introduzione non è altro che la regola del calcolo dei seguenti che dice:

$$\frac{\gamma_1,...\gamma_n\vdash \phi(b)}{\gamma_1,...,\gamma_n \vdash\exist_{x\in B}\phi(x)}$$

* **Regola di Eliminazione**

La regola di eleminazione per il tipo somma indiciata forte è:

$$\text{E-$\Sigma$)}_{dip}\quad\frac{\begin{matrix}
M(z)\space type \space [\Gamma,z\in \sum_{x\in B}C(x)]\\
e(x,y) \in M(<x,y>) \space [\Gamma,x\in B,y \in C(x)]
\end{matrix}}{El_{\Sigma}(t,(x,y).e(x,y))\in M(t)\space [\Gamma, z\in \sum_{x\in B}C(x)]}$$

Supponiamo una nuova proposizione $\xi \space prop \space [\Gamma]$

$$\text{E)}_{dip}\to \frac{\begin{matrix}
\xi \space prop \space [\Gamma]\\
\xi \space \space \text{è vero}\space [\Gamma,x\in B, \phi(x)\space\text{vero}]
\end{matrix}}{\xi \space\text{vero}\space [\Gamma, \exist_{x \in B}\phi(x)]}$$

La regola di eliminazione non è altro che la regola del calcolo dei seguenti che dice:

$$\frac{\gamma_1, ..., \gamma_n, \phi(x)\vdash_{\Gamma,x\in B}\quad\xi}{\gamma_1,...,\gamma_n,\exist_{x\in B}\phi(x)\vdash_\Gamma \quad \xi}$$

### 13.3 Tipo prodotto cartesiano come congiunzione logica <a name="conjlog"></a>

Il tipo prodotto cartesiano permette di indicare la congiunzione logica di due preposizioni:

Se abbiamo due preposizioni 

$$\phi \space prop \space [\Gamma]\qquad \qquad \psi \space prop \space [\Gamma]$$

La loro congiunzione logica può essere scritta come il loro prodotto cartesiano:

$$\phi \& \psi:= \phi\times\psi$$

Questa definizione è corretta, infatti dalla definizione del prodotto cartesiano abbiamo:

$$\frac{a\in \phi\space [\Gamma] \quad b \in \psi \space [\Gamma]}{\lt a,b \gt \in \phi\times\psi}\quad \to \quad \frac{\phi \space \text{vero}\space [\Gamma]\quad \psi \space \text{vero}\space [\Gamma]}{\phi\&\psi \space \text{vero}}$$ 

Dalla regola sopra sappiamo che se le sue parti sono vere, allora la congiunzione è vera. Ci serve dimostrare l'opposto:

Tramite la regola di eliminazione del prodotto cartesiano abbiamo:

$$\frac{d\in B\times C\space [\Gamma]}{\pi_1 d \in B\space [\Gamma]}\quad \frac{d \in B\times C\space [\Gamma]}{\pi_2 d \in C\space [\Gamma]}$$

$$\downarrow$$

$$\frac{\phi\&\psi \space \text{vero}}{\phi\space \text{vero}}\quad\frac{\phi\&\psi \space \text{vero}}{\psi\space \text{vero}}$$

--- 
<div style="text-align: right"><span style="color:orange">Lezione 20</span></div>

## 14. Tipo prodotto dipendente <a name="prodip"></a>


---
---
[Torna su](#su)
# Esercizi: <a name="exs"></a>
0. [Due è un numero naturale](#duenat)
1. [z+2 è un numero naturale se z è un numero naturale](#zpiuduenat)
2. [Eliminatore della somma tra naturali](#elsomma)
3. [Lunghezza di una lista di naturali](#exlh)
4. [Il tipo `Bool` è la somma digiunta di due tipi singoletto](#exbool)
5. [Simmetria dell'uguaglianza](#exidsymm)
6. [Successore conserva l'uguaglianza proposizionale](#exsuccid)
   
---
## E0: $2\in Nat\space [\space]$ <a name="duenat"></a>
Vogliamo dimostrare che 2 appartiene ai naturali (con contesto vuoto, non ci serve).

Useremo prima la regola di introduzione dei naturali per introdurre 0 come prova di un numero naturale: $0\in Nat\space [\space]$.

Dopodiché useremo due volte la seconda regola di introduzione dei numeri naturali che dice che se un numero è naturale, allora il suo successivo è un numero naturale.

Schematicamente:

$$
\begin{matrix}
 \text{I-Nat)}  & [\space] \\ 
 \hline
 \text{I-Nat2)} & 0 \in Nat \space[\space] \\
 \hline
 \text{I-Nat2)} & succ(0) \in Nat \space [\space] \\
 \hline 
                & \underbrace{succ(succ(0))}_{2} \in Nat \space [\space]
\end{matrix}
$$

## E1: $z+2\in Nat \space [z\in Nat]$ <a name="zpiuduenat"></a>
Vogliamo dimostrare che dato un $z$ appartenente ai naturali (contesto), $z+2$ appartiene ai naturali.

Per dimostrare ciò ricordiamo le seguenti regole di riduzione:

 * R1: 

     $$\frac{t_1 \to t_2}{El_{Nat}(t_1, c,e)\to El_{Nat}(t_2, c,e)}$$ 

 * R2: 

     $$\frac{c_1\to c_2}{El_{Nat}(t, c_1,e)\to El_{Nat}(t, c_2,e)}$$

 * R3: 

     $$\frac{t_1\to t_2}{succ(t_1)\to succ(t_2)}$$

Ricordiamo inoltre le regole di conversione del tipo dei numeri naturali:

  * C1: 

     $$El_{Nat}(0,c,e)\to_1 c$$
  
  * C2:
    
     $$El_{Nat}(succ(m),c,e)\to_1 e(m,El_{Nat}(m,c,e))$$

  
Vogliamo costruire l'eliminatore adatto usando la regola di eliminazione dipendente dei naturali:

$$E\text{-}{Nat})_ {dip}\quad \frac{M(z)\space type \space [\Gamma, z\in Nat]\quad c \in M(0) \quad e(x,y)\in M(succ(x)) \space [x\in Nat, y \in M(x)]}{El(z,c,e)\in M(z) \space [\Gamma, z\in Nat]}$$

Però vogliamo qualcosa del tipo:

$$\frac{?}{El_{Nat}(z,2,?)\in Nat \space [z\in Nat]}$$

Da E0 possiamo scrivere $2\in Nat \space [\space]$ come ipotesi:

$$\frac{2\in Nat \space [\space] \quad ?}{El_{Nat}(z,2,?)\in Nat \space [z\in Nat]}$$

Ci serve la funzione $e$ che ci dice il comportamento della ricorsione:

$$\begin{matrix}
e &= (x,y).succ(y) \leftarrow \text{Nozione del $\lambda$ calcolo}\\
&=succ(y) \in Nat \space [x\in Nat, y \in Nat]\space\space\space\space\space\space\space
\end{matrix}$$

$$\frac{2\in Nat \space [\space] \quad succ(y) \in Nat}{El_{Nat}(z,2,(x,y).succ(y))\in Nat \space [z\in Nat]}$$

Abbiamo ottenuto il nostro eliminatore, imponiamo il comportamento sull'elemento canonico tramite la regola di conversione:

$$El_{Nat}(z,2,(x,y).succ(y))[z/0] = El_{Nat}(0,2,(x,y).succ(y))\to_1 2$$

Vediamo cosa succede ad 1:

1. $$El_{Nat}(succ(0),2,(x,y).succ(y))\to_1 succ(\underbrace{El_{Nat}(0,2,(x,y).succ(y))}_{2}) = 3$$

## E2: Somma tra naturali <a name="elsomma"></a>

Ricordiamo ancora la regola di eliminazione dei naturali:

$$E\text{-}{Nat})_ {dip}\quad \frac{M(z)\space type \space [\Gamma, z\in Nat]\quad c \in M(0) \quad e(x,y)\in M(succ(x)) \space [x\in Nat, y \in M(x)]}{El_{Nat}(z,c,e)\in M(z) \space [\Gamma, z\in Nat]}$$

Che vogliamo adattare alla somma.

Il risultato è un elemento dei numeri naturali $El_{Nat}(z,c,e)\in Nat [\Gamma, z \in Nat]$. Quindi nella ipotesi stessa inseriremo in $M(z)$ the type $Nat$:

$$E\text{-}{Nat})_ {dip}\quad \frac{Nat\space type \space [\Gamma, z\in Nat]\quad c \in M(0) \quad e(x,y)\in M(succ(x)) \space [x\in Nat, y \in M(x)]}{El_{Nat}(z,c,e)\in Nat \space [\Gamma, z\in Nat]}$$

Per la regola di conversione, possiamo ottenere c. Poiché $\omega + 0 = \omega$, allora $c = \omega$:

$$E\text{-}{Nat})_ {dip}\quad \frac{\begin{matrix}
Nat\space type \space [\omega\in Nat, z\in Nat]\\
\omega \in Nat\space[\omega \in Nat]\\
e(x,y)\in M(succ(x)) \space [x\in Nat, y \in M(x)]
\end{matrix}}{El_{Nat}(z,\omega,e)\in Nat \space [\omega \in Nat, z\in Nat]}$$

Rimane solo la $e$. Per $z=0$ abbiamo:

$$\omega + 0 = \omega$$
 
Per $z=succ(m)$ abbiamo:

$$\omega + succ(m) = succ(\underbrace{\omega + m}_{y})$$

$$E\text{-}{Nat})_ {dip}\quad \frac{\begin{matrix}Nat\space type \space [\omega\in Nat, z\in Nat]\\
\omega \in Nat\space[\omega \in Nat]\\ 
succ(y) \in Nat \space [\omega\in Nat, x \in Nat, y \in Nat]
\end{matrix}}{El_{Nat}(z,\omega,(x,y).succ(y))\in Nat \space [\omega \in Nat, z\in Nat]}$$

Verifichiamo i valori della somma:

Per la regola di converisone abbiamo che:

$$El_{Nat}(0,\omega, (x,y).succ(y))\to_1 \omega$$

Ovvero $\omega + 0 = \omega$.

Per $succ(0)$ abbiamo invece:

$$El_{Nat}(succ(0), \omega, (x,y).succ(y))\to_1$$

$$\to_1 succ(El_{Nat}(0,\omega,(x,y).succ(y)))\to_1 succ(\omega)\in Nat$$

Ovvero  $\omega + 1 = succ(\omega)$

## E3: Definire tramite deliminatore delle liste: $lh(z)\in Nat \space [z\in list(Nat)]$ <a name="exlh"></a>

Come sempre, partiamo dalla definizione $\text{E-list)}_{dip}$

$$\text{E-list)}_{dip}\quad\frac{\begin{matrix} M(z) \space type \space [\Gamma,z\in list(A)]\quad c \in M(nil)\space [\Gamma]\\
e(x,w,y) \in M(cons(x,w)) \space [\Gamma, x\in list(A), w \in A, y \in M(x)]
\end{matrix}}{El_{list}(z, c, (x,w,y).e(x,w,y)) \in M(z) \space [\Gamma, z\in list(A)]}$$

L'eliminatore è un programma che prende una lista di naturali: $z, \space z\in list(Nat)$ che produce in output la _lunghezza della lista_ il quale è un termine intero: $lh(z)\in Nat$.

Quindi $M(z) \equiv Nat\space$ e $\space list(A)\equiv list(Nat)$

$$\frac{\begin{matrix} Nat \space type \space [\Gamma,z\in list(Nat)]\quad c \in M(nil)\space [\Gamma]\\
e(x,w,y) \in M(cons(x,w)) \space [\Gamma, x\in list(A), w \in A, y \in M(x)]
\end{matrix}}{El_{list}(z, c, (x,w,y).e(x,w,y)) \in Nat \space [\Gamma, z\in list(Nat)]}$$

Per quanto riguarda l'elemento $c$, questo coincide col primo elemento della ricorsione, $0\equiv c \in Nat$

$$\frac{\begin{matrix} Nat \space type \space [\Gamma,z\in list(Nat)]\quad 0 \in Nat\space [\Gamma]\\
e(x,w,y) \in M(cons(x,w)) \space [\Gamma, x\in list(A), w \in A, y \in M(x)]
\end{matrix}}{El_{list}(z, 0, (x,w,y).e(x,w,y)) \in Nat \space [\Gamma, 0\in Nat, z\in list(Nat)]}$$

Per quanto riguarda la funzione $e$, notiamo che:

$$lh(cons(S,a)) = succ(lh(S))$$

Ovvero, la lunghezza di una lista + un elemento equivale alla lunghezza della lista + 1

$$\frac{\begin{matrix} Nat \space type \space [z\in list(Nat)]\quad 0 \in Nat\space [\space]\\
succ(y) \in Nat \space [x\in list(Nat), w \in Nat, y \in Nat]
\end{matrix}}{El_{list}(z, 0, (x,w,y).succ(y)) \in Nat \space [0\in Nat, z\in list(Nat)]}$$

(Per completezza, bisognerebbe derivare anche ogni ipotesi)

Per la regola di conversione abbiamo:

$$El_{list}(nil, 0, (x,w,y).succ(y))\to_1 0$$

Mentre per $z = cons(nil, a)\space \space a \in A$

$$El_{list}(cons(nil,a),0,(x,w,y).succ(y))\to_1$$
$$\to_1 succ(El_{list}(nil,0,(x,w,y).succ(y)))\to_1 succ(0) \equiv 1$$

## E4: Il tipo `Bool` è la somma digiunta di due tipi singoletto <a name="exbool"></a>
Prendiamo un generico singoletto $N_1$ ed il suo elemento canonico $\ast$.

Allora possiamo definire i valori `true` e `false` tramite l'inserimento a sinistra e destra:

$$\ast \in N_1 \space \to \begin{cases}
inl(\ast) &:= true\\
inr(\ast) &:= false
\end{cases}$$

Quindi $N_1 + N_1$ è isomorfo a $Bool$

## E5: Simmetria dell'uguaglianza <a name="exidsymm"></a>
In questo esercizio useremo l'eliminatore del tipo Uguaglianza proposizionale. Questo esercizio si risolve in maniera leggermente diversa, considerando il concetto di _"prova/testimone"_.

In particolare, in questo esercizi, l'obiettivo è trovare una funzione:

$$h_1(z_1,z_2,z_3)\in Id(A,z_2,z_1) \space[\Gamma, z_1 \in A, z_2\in A, z_3 \in Id(A,z_1, z_2)]$$

Che cosa vuol dire?

Vuol dire che vogliamo trovare un qualcosa $h_1$ che appartenga al tipo $Id(A,z_2,z_1)$, ovvero, vogliamo trovare un elemento di un tipo, se l'elemento appartiene al tipo, e se il tipo è abitato, vuol dire che è proposizionalmente vero.

Quindi, vogliamo trovare una prova $(h_1)$ che $z_2=z_1$ in $A$ sotto il contesto che $z_1=z_2$ è vero $z_3\in Id(A,z_1,z_2)$

Iniziamo con la dimostrazione: la regola di eliminazione dipendente è:

$$\text{E-Id)}_{dip}\quad \frac{\begin{matrix}
M(z_1,z_2,z_3) \space type \space [\Gamma, z_1 \in A, z_2\in A, z_3 \in Id(A,z_1,z_2)]\\
e(x) \in M(x,x,id(x))\space [\Gamma,x\in A]
\end{matrix}}{El_{Id}(t,(x).e(x))\in M(a,b,t) \space [\Gamma, z_1\in A, z_2 \in A, z_3\in Id(A,z_1,z_2)]}$$

E come detto, la conclusione del giudizio è:

$$\frac{?}{h_1(z_1,z_2,z_3)\in Id(A,z_2,z_1)\space [\Gamma,z_1\in A,z_2\in A, z_3\in Id(A,z_1,z_2)]}$$

Comparando le due regole otteniamo:

$$M(z_1,z_2,z_3)=Id(A,z_2,z_1)$$

$$\frac{\begin{matrix}
Id(A,z_2,z_1)\space type \space [\Gamma, z_1\in A,z_2\in A, _3 \in Id(A,z_1,z_2)]\\
? \in Id(A,x,x) \space [\Gamma, x\in A]
\end{matrix}}{h_1(z_1,z_2,z_3)\in Id(A,z_2,z_1)\space [\Gamma,z_1\in A,z_2\in A, z_3\in Id(A,z_1,z_2)]}$$

In "?" abbiamo bisogno di una prova di $Id(A,x,x)$ che è $id(x)$ per le regole di introduzione:

$$\frac{\begin{matrix}
Id(A,z_2,z_1)\space type \space [\Gamma, z_1\in A,z_2\in A, _3 \in Id(A,z_1,z_2)]\\
id(x) \in Id(A,x,x) \space [\Gamma, x\in A]
\end{matrix}}{h_1(z_1,z_2,z_3)\in Id(A,z_2,z_1)\space [\Gamma,z_1\in A,z_2\in A, z_3\in Id(A,z_1,z_2)]}$$

## E6: Successore conserva l'uguaglianza proposizionale <a name="exsuccid"></a>
Analogamente all'esercizio precedente possiamo dimostrare tramite la stessa regola che il successore conserva l'uguaglianza proposizionale, ovvero la conclusione sarà:

$$h_2(z_1,z_2,z_3)\in Id(Nat, succ(z_1),succ(z_2)) \space [z_1\in Nat, z_2\in Nat, z_3\in Id(Nat,z_1,z_2)]$$

Ovvero se noi abbiamo una prova che $z_1 = z_2$  ovvero $z_3\in Id(Nat,z_1,z_2)$ vogliamo verificare che $succ(z_1)= succ(z_2)$ ovvero $h_2(z_1,z_2,z_3)\in Id(Nat, succ(z_1),succ(z_2))$

Iniziamo con la dimostrazione:

$$\frac{?}{h_2(z_1,z_2,z_3)\in Id(Nat, succ(z_1),succ(z_2)) \space [z_1\in Nat, z_2\in Nat, z_3\in Id(Nat,z_1,z_2)]}$$

$M(z_1,z_2,z_3) = Id(Nat,succ(z_1),succ(z_2))$ (Per farlo dovremmo dimostrare $Id(Nat,succ(z_1),succ(z_2)) \space type \space [\Sigma]$)

$$\frac{\begin{matrix}
Id(Nat,succ(z_1), succ(z_2))\space type \space [z_1\in Nat, z_2\in Nat]\\
id(succ(x)) \in Id(Nat,succ(x), succ(x)) \space [x\in Nat] \quad \text{(Da dimostrare)}
\end{matrix}}{h_2(z_1,z_2,z_3)\in Id(Nat, succ(z_1),succ(z_2)) \space [z_1\in Nat, z_2\in Nat, z_3\in Id(Nat,z_1,z_2)]}$$





---
[Torna su](#exs)