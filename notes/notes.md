## 1. Introduzione della Teoria dei Tipi
niente
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
  $$\varnothing\space cont \quad \text{F-c)}\space\space\frac{A\space\space type\space\space[\Gamma]}{\Gamma,x \in A \spacecont} ((x\in A)\space not\space in\space\space \Gamma)$$
  "_Il vuoto è un contesto. Se A è un tipo sotto contesto Gamma, allora posso estendere il contesto gamma con una variabile x di A a patto che $x\in A$ non compaia in Gamma_"

  Questa regola è ausiliaria perch può essere derivata dalle altre, in un contesto minimalista sarebbe meglio ometterla perché una teoria con meno regole è preferibile, ma metterla rende tutto più facile.

<span style="color:green">**Cosa è esattamente un contesto?**<br>Un contesto è l'insieme di regole/predicati che abbiamo già ricavato. Dopo sarà più chiaro quando faremo l'albero di derivazione.</span>

<span style="color:green">**Cosa è un tipo dipendente?** <br> Un esempio di tipo dipendente è un vettore (o matrice) che dipende da un altro tipo (ad esempio il tipo dei natrurali se vogliamo costruire un array di elementi naturali).</span>

<span style="color:green">**Qual è la differenza tra uguaglianza definizionale e computazionale?** <br> </span>

**Nota** $a \in A$ della teoria dei tipi indica una appartenenza **differente** dal concetto insiemistico:
* In set Theory abbiammo 
  $$\underbrace{1}_\text{è un insieme} \in \underbrace{Nat}_\text{è un insieme} $$
  Dove 1 è un insieme singoletto (avente solo un elemento)
  <br>
* Nella teoria dei tipi (di Russel)
  $$\underbrace{1}_\text{è un elemento} \in \underbrace{Nat}_\text{è un tipo} $$
  1 è un elemento e non un tipo. Stiamo imponendo una gerarchia (elemento<tipo) per evitare il paradosso di Russel della teoria di Frege. 

<span style="color:green">**Perché la teoria di Frege è inconsistente? (il paradosso di Russel)** <br> TODO</span>

#### Regole di formazione dei tipi singoletto 
Il singoletto è il tipo generale più semplice da studiare, poiché per definizione contiene un singolo elemento. Qui enunciamo le regole per la formazione dei suddetti tipi:
* **Regola di Formazione del tipo singoletto**
  $$\text{S)}\space\space\frac{\Gamma \space\spacecont}{N_1 \spacetype \space\space[\Gamma]}$$_"Se Gamma è un contesto, allora N1 è un tipo sotto contesto Gamma"_

* **Regola di introduzione della * nel singoletto**
$$\text{I-S)}\space\space\frac{\Gamma \space\spacecont}{* \in N_1 \space\space[\Gamma]}$$_"Se Gamma è un contesto allora star appartiene ad N1 sotto contesto Gamma"_

Regola che mi permette di dire come fare a scrivere funzioni dal tipo singoletto verso qualsiasi altro tipo:
* **Regola di Eliminazione**
  $$\text{E-S)}\space\space\frac{t_1 \in N_1\space\space[\Gamma]\quad M(z) \space\spacetype \space\space [\Gamma, z\in N_1]\quad c\in M(*)\space\space [\Gamma]}{El_{N_1}(t,c) \in \underbrace{M(t)}_{M(z)[z/t]}\space\space[\Gamma]}$$
  _"Se t1 è un termine di tipo N1 sotto contesto Gamma ed M(z) è un tipo dipendente da Gamma e z in tipo N1 e so che c  tipo M (*) sotto contesto Gamma allora posso dedurre l'eliminatore."_

  Noi riusciamo a trovare elementi di tipo M(t) (l'eliminatore), se noi sappiamo cosa succede in M(*). In altre parole riusciamo ad avere una funzione che ci porta da N1 (tramite $t \in N_1$) a $M(t)$

* **Seconda regola di Eliminazione** $$\text{C-S)}\space\space\frac{M(z) \space\spacetype\space\space[\Gamma, z \in N_1]\quad c \in M(*)\space [\Gamma]}{El_{N_1}(*,c)= c \in M(*)\space\space[\Gamma]}$$_"Se M(z) è un tipo sotto contesto Gamma e z in N1, e c appartiene ad M(*) sotto contesto Gamma allora l'eliminatore EL(*,c) è uguale a c in M(*) sotto contesto Gamma"_
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
$$
\begin{matrix}
\text{F-S)} & [\space\space] \space cont \\
\hline
\text{F-C)} & N_1 \space type \space [\space\space] \\
\hline 
\text{F-S)} & [x_1\in N_1]\space cont\\ \hline
\text{F-C)} &N_1 \space type \space [x_1\in N_1] \\ \hline 
 & [x_1\in N_1, x_2\in N_1]\space cont
\end{matrix}$$
Possiamo generalizzare ottenendo:
$ [x_1\in N_1,..., x_n\in N_1]\space cont$ dalle solo due regole di formazione del singoletto e formazione del contesto.

**Nota:** Il contesto non è telescopico (dove un sotto-contesto dipende da un altro), quindi volendo possiamo usare le regole di scambio a piacimento.

* **Regola di Introduzione del singoletto**
  
$$\text{I-S)}\space \frac{\Gamma \space cont}{* \in N_1 \space \space [\Gamma]}$$
  

* **Regola di Eliminazione del singoletto**
  
$$\text{E-S)}\space \frac{t_1 \in N_1 \space [\Gamma] \quad M(z) \space type \space [z \in N_1]\quad  c\in \overbrace{M(*)}^{M(z)[z/*]} \space \space [\Gamma]}{El_{N_1}(t, c) \in M(t)\space \space [\Gamma]}$$

* **Regola di Conversione del singoletto**

$$\text{C-S)}\space \frac{\quad M(z) \space type \space [\Gamma, z \in N_1]\quad  c\in M(*) \space[\Gamma]}{El_{N_1}(*, c) = c \in M(t)\space \space [\Gamma]}$$

La regola di eliminazione si può equivalentemente scrivere in un altro modo:
* **Regola di Eliminazione del singoletto 2**
  
$$\text{E-S)}_\text{Dipendente}\space \frac{M(z) \space type \space [\Gamma, z \in N_1]\quad  c\in M(*) \space \space [\Gamma]}{El_{N_1}(z, c) \in M(z)\space \space [\Gamma, z\in N_1]}$$

Si può dimostrare che usando $\text{E-S)}_{dip}$ + regole di sostituzione è equivalente ad $\text{E-S)}$.

L'eliminatore rappresenta un _ricorsore_: è una funzione definita per ricorsione su $N_1$:
* $El_{N_1}(z,c)[z/*] = El_{N_1}(*,c) = c \in M(*)$

***Nota personale:*** Fino a questo momento c'è un po' di confusione per quanto riguarda il concetto di singoletto e di Eliminatore: Se $El_{N_1}(*,c) = c$ dove $*$ è un elemento del singoletto, poiché il singoletto possiede un solo elemento per definizione, non dovrebbero essere tutti gli eliminatori uguali? Perché definire più termini del singoletto?

Credo che la risposta stia nel fatto di uguaglianza definizionale vs uguaglianza matematica ma ancora non mi è totalmente chiaro.

---
  <div style="text-align: right"><span style="color:orange">Lezione 9</span></div>