# Typechecker per Cubical Type Theory

[![WIP](https://img.shields.io/badge/Stato-Lavoro%20in%20Corso-yellow)](https://github.com/tuo-repo)

Questo progetto è un'implementazione sperimentale di un typechecker per **Cubical Type Theory** (CTT), basato su un algoritmo di typechecking bidirezionale. Il codice è attualmente in fase di sviluppo ed è ispirato al repository [anders](https://github.com/groupoid/anders/tree/main) del gruppo [groupoid](https://github.com/groupoid), guidato da @5HT

## Cos'è la Cubical Type Theory?

La **Cubical Type Theory** è un'estensione costruttiva della Type Theory che fornisce un'interpretazione diretta dell'**assioma di univalenza** della Homotopy Type Theory (HoTT). A differenza degli approcci classici, CTT introduce nozioni geometriche come **path types** (tipi di cammini), **composizioni omotopiche** e **operazioni di trasporto**, permettendo una manipolazione esplicita di strutture ad alta dimensione (come omotopie e equivalenze).

### Caratteristiche Principali:
- **Path Types**: Tipi che rappresentano cammini tra elementi (`PathP`).
- **Trasporto**: Operazione per spostare elementi lungo cammini (`Transp`).
- **Composizione Omotopica**: Costruzione di elementi in contesti di incollamento (`HComp`).
- **Sistemi e Cofibre**: Gestione di condizioni parziali tramite connettivi logici (`System`, `Im`, `Join`).
- **Universi Kan e Pre-universi**: Gerarchia di universi con proprietà di Kan.

## Stato Attuale del Progetto (WIP)

Il typechecker è in **fase attiva di sviluppo** e supporta attualmente:
- Sintassi base di CTT (lambda, Pi tipi, applicazioni).
- Costrutti per path types, trasporto, composizione omotopica.
- Connettivi logici per cofibre (`And`, `Or`, `Neg`).
- Tipi base (`Unit`, `Bool`, `Empty`) e loro eliminatori.
- Gestione di contesti e ambienti di valutazione.
- Algoritmo bidirezionale con inferenza (`infer`) e verifica (`check`).

## Algoritmo Bidirezionale di Typechecking

L'algoritmo bidirezionale separa il processo di typechecking in due fasi:

1. **Inferenza del Tipo (`infer`):**
   - Deduce il tipo di un termine dal contesto.
   - Esempio: Per `fn x:A. x`, inferisce `Pi(x:A). A`.

2. **Verifica del Tipo (`check`):**
   - Verifica che un termine abbia un tipo specifico.
   - Esempio: Verifica che `Bool` abbia tipo `U0`.

**Flusso Principale:**
- **Lambda:** Verifica l'annotazione, estende il contesto, inferisce il corpo.
- **Applicazione:** Inferisce il tipo della funzione, verifica l'argomento, sostituisce nel codominio.
- **Path Types:** Verifica la linea, gli estremi, e restituisce un universo Kan.
