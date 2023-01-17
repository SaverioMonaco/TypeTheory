# 1. Introduzione della Teoria dei Tipi
niente
# 2. Prime regole della teoria dei tipi dipendenti di Martin Loef
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
  $$\varnothing\, cont \quad \text{F-c)}\,\,\frac{A\,\, type\,\,[\Gamma]}{\Gamma,x \in A \,cont} ((x\in A)\, not\, in\,\, \Gamma)$$
  "_Il vuoto è un contesto. Se A è un tipo sotto contesto Gamma, allora posso estendere il contesto gamma con una variabile x di A a patto che $x\in A$ non compaia in Gamma_"

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
  $$\text{S)}\,\,\frac{\Gamma \,\,cont}{N_1 \,type \,\,[\Gamma]}$$_"Se Gamma è un contesto, allora N1 è un tipo sotto contesto Gamma"_

* **Regola di introduzione della * nel singoletto**
$$\text{I-S)}\,\,\frac{\Gamma \,\,cont}{* \in N_1 \,\,[\Gamma]}$$_"Se Gamma è un contesto allora star appartiene ad N1 sotto contesto Gamma"_

Regola che mi permette di dire come fare a scrivere funzioni dal tipo singoletto verso qualsiasi altro tipo:
* **Regola di Eliminazione**
  $$\text{E-S)}\,\,\frac{t_1 \in N_1\,\,[\Gamma]\quad M(z) \,\,type \,\, [\Gamma, z\in N_1]\quad c\in M(*)\,\, [\Gamma]}{El_{N_1}(t,c) \in \underbrace{M(t)}_{M(z)[z/t]}\,\,[\Gamma]}$$
  _"Se t1 è un termine di tipo N1 sotto contesto Gamma ed M(z) è un tipo dipendente da Gamma e z in tipo N1 e so che c  tipo M (*) sotto contesto Gamma allora posso dedurre l'eliminatore."_

  Noi riusciamo a trovare elementi di tipo M(t) (l'eliminatore), se noi sappiamo cosa succede in M(*). In altre parole riusciamo ad avere una funzione che ci porta da N1 (tramite $t \in N_1$) a $M(t)$

* **Seconda regola di Eliminazione** $$\text{C-S)}\,\,\frac{M(z) \,\,type\,\,[\Gamma, z \in N_1]\quad c \in M(*)\, [\Gamma]}{El_{N_1}(*,c)= c \in M(*)\,\,[\Gamma]}$$_"Se M(z) è un tipo sotto contesto Gamma e z in N1, e c appartiene ad M(*) sotto contesto Gamma allora l'eliminatore EL(*,c) è uguale a c in M(*) sotto contesto Gamma"_
  In questa regola cominciamo a mettere un'uguaglianza.