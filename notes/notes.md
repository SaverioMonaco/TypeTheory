## 1. Introduzione della Teoria dei Tipi
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

## 2. Prime regole della teoria dei tipi dipendenti di Martin Loef
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
## 3. Regole strutturali
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
## 4. Regole (principali) del tipo singoletto
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

## 5. Altre regole strutturali derivabili
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
    \text{F-S)} & [\Gamma, z\in N_1] \space cont \qquad [\Gamma, z\in N_1, \omega \in N_1] \space cont\\ \hline
   \space  & N_1 \space type \space [\Gamma, z\in N_1]\qquad \omega\in N_1 \space [\Gamma, z\in N_1, \omega \in N_1]\\ 
   \hline
 ind & \overbrace{M(z) \space type\space[\Gamma, z\in N_1]}^{\text{per ipotesi}} \qquad [\Gamma,z\in N_1, \omega\in N_1] \space cont \\
 \hline
 sub & M(z) \space type \space [\Gamma, z\in N_1, \omega \in N_1] \quad \omega\in N_1 \space [\Gamma, z\in N_1, \omega \in N_1] \\ 
 \hline
 \space & M(\omega)\space type \space [\Gamma, z\in N_1] \\
 \hline
 \space & El_{N_1}(z, c) \in M(z)\space \space [\Gamma, z\in N_1]
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

## 6. Schema generale di produzione di regole definenti un tipo e i suoi termini 

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