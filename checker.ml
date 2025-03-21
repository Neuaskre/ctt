(*
 * Implementazione di Cubical Type Theory in Standard ML.
 * Questo codice definisce i costrutti sintattici, la valutazione, l'inferenza di tipi,
 * e funzioni ausiliarie per la manipolazione dei termini.
 *)

(*
 * Definizione del tipo term che rappresenta i termini del linguaggio.
 * I costruttori includono variabili, lambda astrazioni, applicazioni, tipi dipendenti,
 * path types, operazioni di trasporto e composizione, sistemi, connettivi logici,
 * e costrutti per tipi base e induttivi.
 *)
datatype term =
    Var of string                       (* Variabile (nome) *)
  | Lam of string * term * term         (* Lambda astrazione: x, annotazione, corpo *)
  | App of term * term                  (* Applicazione di funzione *)
  | Pi of string * term * term          (* Tipo dipendente: x, dominio, codominio *)
  | PathP of term * term * term         (* Path type: linea, estremi a e b *)
  | Transp of term * term               (* Trasporto lungo un path *)
  | HComp of term * term * term * term  (* Composizione omotopica *)
  | System of term list * term          (* Sistema di termini con condizione *)
  | Dir of bool                         (* Direzione dell'intervallo (true=1, false=0) *)
  | And of term * term                  (* Congiunzione logica *)
  | Or of term * term                   (* Disgiunzione logica *)
  | Neg of term                         (* Negazione logica *)
  | Ref of term                         (* Riflessività (path costante) *)
  | Kan of int                          (* Universo Kan (livello n) *)
  | Pre of int                          (* Pre-universo (livello n) *)
  | Unit                                (* Tipo unità *)
  | Bool                                (* Tipo booleano *)
  | True                                (* Valore vero *)
  | False                               (* Valore falso *)
  | Empty                               (* Tipo vuoto *)
  | IndEmpty of term                    (* Eliminatore per Empty *)
  | IndUnit of term                     (* Eliminatore per Unit *)
  | IndBool of term                     (* Eliminatore per Bool *)
  | Glue of term                        (* Costrutto Glue per equivalenze *)
  | GlueElem of term * term * term      (* Elemento di Glue *)
  | Unglue of term * term * term        (* Operazione inversa di Glue *)
  | Im of term                          (* Costrutto Im (cofibra) *)
  | Inf of term                         (* Infinito (cofibra) *)
  | Join of term                        (* Join (cofibra) *)
  | IndIm of term * term                (* Eliminatore per Im *)
  | VI                                  (* Tipo intervallo (I) *)

(*
 * Tipo value rappresenta i valori valutati durante l'esecuzione.
 * Corrisponde ai termini chiusi e valutati, con costruttori analoghi a term.
 * Include informazioni aggiuntive per l'ambiente di valutazione.
 *)
datatype value =
    VPre of int                         (* Valore pre-universo *)
  | VKan of int                         (* Valore universo Kan *)
  | VVar of string                      (* Variabile (ambiente chiuso) *)
  | VHole                               (* Buco (per errori) *)
  | VPi of value * (string * term * (string * value) list) (* Tipo dipendente valutato *)
  | VSig of value * (string * term * (string * value) list) (* Tipo Sigma valutato *)
  | VLam of value * (string * term * (string * value) list) (* Lambda valutato *)
  | VApp of value * value               (* Applicazione valutata *)
  | VPair of bool * value * value       (* Coppia (flag per proiezioni) *)
  | VFst of value                       (* Proiezione sinistra *)
  | VSnd of value                       (* Proiezione destra *)
  | VPathP of value * value * value     (* Path valutato *)
  | VRef of value                       (* Riflessività valutata *)
  | VJ of value                         (* Operatore J valutato *)
  | VPLam of value                      (* Lambda per path *)
  | VTransp of value * value            (* Trasporto valutato *)
  | VHComp of value * value * value * value (* Composizione omotopica valutata *)
  | VSystem of value list * value       (* Sistema valutato *)
  | VPartialP of value * value          (* Partial type valutato *)
  | VGlue of value                      (* Glue valutato *)
  | VGlueElem of value * value * value  (* Elemento Glue valutato *)
  | VUnglue of value * value * value    (* Unglue valutato *)
  | VEmpty                              (* Tipo vuoto valutato *)
  | VIndEmpty of value                  (* Eliminatore Empty valutato *)
  | VUnit                               (* Tipo unità valutato *)
  | VStar                               (* Valore unità *)
  | VIndUnit of value                   (* Eliminatore Unit valutato *)
  | VBool                               (* Tipo booleano valutato *)
  | VFalse                              (* Valore falso valutato *)
  | VTrue                               (* Valore vero valutato *)
  | VIndBool of value                   (* Eliminatore Bool valutato *)
  | VIm of value                        (* Im valutato *)
  | VInf of value                       (* Inf valutato *)
  | VJoin of value                      (* Join valutato *)
  | VIndIm of value * value             (* Eliminatore Im valutato *)
  | VDir of bool                        (* Direzione valutata *)
  | VAnd of value * value               (* Congiunzione valutata *)
  | VOr of value * value                (* Disgiunzione valutata *)
  | VNeg of value                       (* Negazione valutata *)
  | VVI                                 (* Tipo intervallo valutato *)

(* Contesto di tipo: associazione nomi a tipi *)
type context = (string * term) list

(* Contesto di valutazione: associazione nomi a valori *)
type evalContext = (string * value) list

(* Funzioni ausiliarie per la valutazione *)

(* Valuta la congiunzione logica su valori Dir *)
fun evalAnd (VDir d1, VDir d2) = VDir (d1 andalso d2)
  | evalAnd _ = raise Fail "Argomenti non validi per And"

(* Valuta la disgiunzione logica su valori Dir *)
fun evalOr (VDir d1, VDir d2) = VDir (d1 orelse d2)
  | evalOr _ = raise Fail "Argomenti non validi per Or"

(* Valuta la negazione logica su valori Dir *)
fun evalNeg (VDir d) = VDir (not d)
  | evalNeg _ = raise Fail "Argomento non valido per Neg"

(* Ricerca una variabile nel contesto di valutazione *)
fun lookupVar (x: string, []) = raise Fail ("Variabile non legata: " ^ x)
  | lookupVar (x, (y, v)::ctx) = if x = y then v else lookupVar (x, ctx)

(* Proiezione sinistra per coppie valutate *)
fun vfst (VPair (_, v, _)) = v
  | vfst _ = raise Fail "Atteso valore coppia"

(* Proiezione destra per coppie valutate *)
fun vsnd (VPair (_, _, v)) = v
  | vsnd _ = raise Fail "Atteso valore coppia"

(* Valutazione principale dei termini *)
fun eval ctx (Var x) = lookupVar (x, ctx)
  | eval ctx (Lam (x, a, e)) = 
      let val aVal = eval ctx a
          val ctx' = (x, aVal) :: ctx
      in VLam (aVal, (x, e, ctx')) end
  | eval ctx (App (f, e)) = app (eval ctx f, eval ctx e)
  | eval ctx (Pi (x, a, b)) = VPi (eval ctx a, (x, b, ctx))
  | eval ctx (PathP (p, a, b)) = VPathP (eval ctx p, eval ctx a, eval ctx b)
  | eval ctx (Transp (p, i)) = VTransp (eval ctx p, eval ctx i)
  | eval ctx (HComp (t, r, u, u0)) = VHComp (eval ctx t, eval ctx r, eval ctx u, eval ctx u0)
  | eval ctx (System (ts, phi)) = VSystem (map (eval ctx) ts, eval ctx phi)
  | eval ctx (Dir d) = VDir d
  | eval ctx (And (a, b)) = evalAnd (eval ctx a, eval ctx b)
  | eval ctx (Or (a, b)) = evalOr (eval ctx a, eval ctx b)
  | eval ctx (Neg a) = evalNeg (eval ctx a)
  | eval ctx (Ref a) = VRef (eval ctx a)
  | eval ctx (Kan n) = VKan n
  | eval ctx (Pre n) = VPre n
  | eval ctx Unit = VUnit
  | eval ctx Bool = VBool
  | eval ctx True = VTrue
  | eval ctx False = VFalse
  | eval ctx Empty = VEmpty
  | eval ctx (IndEmpty e) = VIndEmpty (eval ctx e)
  | eval ctx (IndUnit e) = VIndUnit (eval ctx e)
  | eval ctx (IndBool e) = VIndBool (eval ctx e)
  | eval ctx (Glue e) = VGlue (eval ctx e)
  | eval ctx (GlueElem (r, u, a)) = VGlueElem (eval ctx r, eval ctx u, eval ctx a)
  | eval ctx (Unglue (r, u, e)) = VUnglue (eval ctx r, eval ctx u, eval ctx e)
  | eval ctx (Im e) = VIm (eval ctx e)
  | eval ctx (Inf e) = VInf (eval ctx e)
  | eval ctx (Join e) = VJoin (eval ctx e)
  | eval ctx (IndIm (a, b)) = VIndIm (eval ctx a, eval ctx b)
  | eval ctx VI = VVI

(* Applicazione di valori valutati *)
and app (VLam (a, (x, body, env)), arg) = eval ((x, arg) :: env) body
  | app (VPLam p, arg) = VApp (VPLam p, arg)
  | app (f, arg) = raise Fail "Impossibile applicare valore non-funzione"

(* Funzioni di pretty-printing per debug *)

(* Converte un termine in stringa *)
fun ppTerm (Var x) = x
  | ppTerm (Lam (x, a, e)) = "fn " ^ x ^ ":" ^ ppTerm a ^ ". " ^ ppTerm e
  | ppTerm (App (e1, e2)) = "(" ^ ppTerm e1 ^ " " ^ ppTerm e2 ^ ")"
  | ppTerm (Pi (x, a, b)) = "Pi(" ^ x ^ ":" ^ ppTerm a ^ "). " ^ ppTerm b
  | ppTerm (PathP (p, a, b)) = "Path " ^ ppTerm p ^ " " ^ ppTerm a ^ " " ^ ppTerm b
  | ppTerm (Transp (p, i)) = "transp " ^ ppTerm p ^ " " ^ ppTerm i
  | ppTerm (HComp (t, r, u, u0)) = "hcomp " ^ ppTerm t ^ " " ^ ppTerm r ^ " " ^ ppTerm u ^ " " ^ ppTerm u0
  | ppTerm (System (ts, phi)) = "system " ^ String.concatWith " " (map ppTerm ts) ^ " | " ^ ppTerm phi
  | ppTerm (Dir true) = "1"
  | ppTerm (Dir false) = "0"
  | ppTerm (And (a, b)) = "(" ^ ppTerm a ^ " /\\ " ^ ppTerm b ^ ")"
  | ppTerm (Or (a, b)) = "(" ^ ppTerm a ^ " \\/ " ^ ppTerm b ^ ")"
  | ppTerm (Neg a) = "~" ^ ppTerm a
  | ppTerm (Ref a) = "refl " ^ ppTerm a
  | ppTerm (Kan n) = "U" ^ Int.toString n
  | ppTerm (Pre n) = "Pre" ^ Int.toString n
  | ppTerm Unit = "Unit"
  | ppTerm Bool = "Bool"
  | ppTerm True = "true"
  | ppTerm False = "false"
  | ppTerm Empty = "Empty"
  | ppTerm (IndEmpty e) = "indEmpty " ^ ppTerm e
  | ppTerm (IndUnit e) = "indUnit " ^ ppTerm e
  | ppTerm (IndBool e) = "indBool " ^ ppTerm e
  | ppTerm (Glue e) = "Glue " ^ ppTerm e
  | ppTerm (GlueElem (r, u, a)) = "glueElem " ^ ppTerm r ^ " " ^ ppTerm u ^ " " ^ ppTerm a
  | ppTerm (Unglue (r, u, e)) = "unglue " ^ ppTerm r ^ " " ^ ppTerm u ^ " " ^ ppTerm e
  | ppTerm (Im e) = "Im " ^ ppTerm e
  | ppTerm (Inf e) = "Inf " ^ ppTerm e
  | ppTerm (Join e) = "Join " ^ ppTerm e
  | ppTerm (IndIm (a, b)) = "indIm " ^ ppTerm a ^ " " ^ ppTerm b
  | ppTerm VI = "I"

(* Converte un valore valutato in stringa *)
fun ppValue (VPre n) = "Pre" ^ Int.toString n
  | ppValue (VKan n) = "U" ^ Int.toString n
  | ppValue (VVar x) = x
  | ppValue VHole = "<?>"
  | ppValue (VPi (a, (x, _, _))) = "Pi(" ^ x ^ ":" ^ ppValue a ^ ").(...)"
  | ppValue (VSig (a, (x, _, _))) = "Sig(" ^ x ^ ":" ^ ppValue a ^ ").(...)"
  | ppValue (VLam (a, (x, _, _))) = "fn " ^ x ^ ":" ^ ppValue a ^ " => ..."
  | ppValue (VApp (f, arg)) = "(" ^ ppValue f ^ " " ^ ppValue arg ^ ")"
  | ppValue (VPair (_, v1, v2)) = "(" ^ ppValue v1 ^ ", " ^ ppValue v2 ^ ")"
  | ppValue (VFst v) = "fst " ^ ppValue v
  | ppValue (VSnd v) = "snd " ^ ppValue v
  | ppValue (VPathP (p, a, b)) = "Path " ^ ppValue p ^ " " ^ ppValue a ^ " " ^ ppValue b
  | ppValue (VRef v) = "refl " ^ ppValue v
  | ppValue (VJ v) = "J " ^ ppValue v
  | ppValue (VPLam p) = "plam"
  | ppValue (VTransp (p, i)) = "transp " ^ ppValue p ^ " " ^ ppValue i
  | ppValue (VHComp (t, r, u, u0)) = "hcomp(...)"
  | ppValue (VSystem (vs, phi)) = "system [...]"
  | ppValue (VPartialP (phi, u)) = "partialP"
  | ppValue VEmpty = "Empty"
  | ppValue (VIndEmpty v) = "indEmpty " ^ ppValue v
  | ppValue VUnit = "Unit"
  | ppValue VStar = "*"
  | ppValue (VIndUnit v) = "indUnit " ^ ppValue v
  | ppValue VBool = "Bool"
  | ppValue VTrue = "true"
  | ppValue VFalse = "false"
  | ppValue (VIndBool v) = "indBool " ^ ppValue v
  | ppValue (VDir d) = if d then "1" else "0"
  | ppValue (VAnd (a, b)) = "(" ^ ppValue a ^ " /\\ " ^ ppValue b ^ ")"
  | ppValue (VOr (a, b)) = "(" ^ ppValue a ^ " \\/ " ^ ppValue b ^ ")"
  | ppValue (VNeg a) = "~" ^ ppValue a
  | ppValue (VGlue e) = "Glue " ^ ppValue e
  | ppValue (VGlueElem (r, u, a)) = "glueElem " ^ ppValue r ^ " " ^ ppValue u ^ " " ^ ppValue a
  | ppValue (VUnglue (r, u, e)) = "unglue " ^ ppValue r ^ " " ^ ppValue u ^ " " ^ ppValue e
  | ppValue (VIm e) = "Im " ^ ppValue e
  | ppValue (VInf e) = "Inf " ^ ppValue e
  | ppValue (VJoin e) = "Join " ^ ppValue e
  | ppValue (VIndIm (a, b)) = "indIm " ^ ppValue a ^ " " ^ ppValue b
  | ppValue VVI = "I"

(* Inferenza di tipi e controllo *)

(*
 * Funzione principale per l'inferenza del tipo di un termine.
 * Utilizza il contesto per risolvere le variabili e verifica i costrutti.
 *)
fun infer ctx (Var x) =
      (case List.find (fn (y, _) => y = x) ctx of
           SOME (_, ty) => ty
         | NONE => raise Fail ("Variabile non legata: " ^ x))
  | infer ctx (Lam (x, a, e)) =
      let val _ = check ctx a (Kan 0)  (* Verifica che l'annotazione sia un Kan 0 *)
          val ctx' = (x, a) :: ctx     (* Estende il contesto con la variabile x *)
          val b = infer ctx' e         (* Inferisce il tipo del corpo nel nuovo contesto *)
      in Pi (x, a, b) end             (* Restituisce il tipo dipendente *)
  | infer ctx (App (f, e)) =
      (case infer ctx f of
           Pi (x, a, b) => (check ctx e a; subst x e b)  (* Verifica l'argomento e sostituisce *)
         | ty => raise Fail ("Atteso tipo Pi, ottenuto: " ^ ppTerm ty))
  | infer ctx (Pi (x, a, b)) =
      let val _ = check ctx a (Kan 0)  (* Dominio deve essere Kan 0 *)
          val ctx' = (x, a) :: ctx     (* Estende il contesto *)
          val _ = check ctx' b (Kan 0) (* Codominio deve essere Kan 0 *)
      in Kan 0 end                     (* Il tipo Pi stesso è Kan 0 *)
  | infer ctx (PathP (p, a, b)) =
      let val pTy = infer ctx p
          (* Verifica che p sia una funzione da VI a Kan 0 *)
          val () = if alphaEq pTy (Pi ("i", VI, Kan 0)) then ()
                   else raise Fail "PathP richiede una linea Pi(i:I).U0"
          (* Verifica che a e b siano gli estremi corretti *)
          val () = check ctx a (App (p, Dir false))
          val () = check ctx b (App (p, Dir true))
      in Kan 0 end
  | infer ctx (Transp (p, i)) =
      (check ctx p (PathP (Pi ("i", VI, Kan 0), Kan 0, Kan 0)); (* p deve essere un path di universi *)
       check ctx i VI;                                           (* i deve essere nell'intervallo *)
       Kan 0)                                                    (* Il risultato è Kan 0 *)
  | infer ctx (HComp (t, r, u, u0)) =
      (check ctx t (Kan 0);      (* t deve essere Kan 0 *)
       check ctx r VI;           (* r deve essere nell'intervallo *)
       check ctx u (Pi ("i", VI, Kan 0)); (* u deve essere una famiglia su VI *)
       check ctx u0 (Kan 0);     (* u0 deve essere Kan 0 *)
       Kan 0)                    (* Il risultato è Kan 0 *)
  | infer ctx (System (ts, phi)) =
      (check ctx phi VI;                  (* phi deve essere nell'intervallo *)
       List.app (fn t => check ctx t (Kan 0)) ts; (* Ogni termine nel sistema deve essere Kan 0 *)
       Kan 0)                             (* Il risultato è Kan 0 *)
  | infer ctx (Dir d) = VI                (* Dir d ha tipo VI *)
  | infer ctx (And (a, b)) = (check ctx a VI; check ctx b VI; VI) (* And richiede VI *)
  | infer ctx (Or (a, b)) = (check ctx a VI; check ctx b VI; VI)  (* Or richiede VI *)
  | infer ctx (Neg a) = (check ctx a VI; VI)                       (* Neg richiede VI *)
  | infer ctx (Ref a) = PathP (Kan 0, a, a) (* Ref a è un path costante su a *)
  | infer ctx (Kan n) = Kan (n + 1)        (* L'universo Kan n è di livello n+1 *)
  | infer ctx (Pre n) = Pre (n + 1)        (* Pre-universo è di livello n+1 *)
  | infer ctx Unit = Kan 0                 (* Unit è Kan 0 *)
  | infer ctx Bool = Kan 0                 (* Bool è Kan 0 *)
  | infer ctx True = Bool                  (* True è di tipo Bool *)
  | infer ctx False = Bool                 (* False è di tipo Bool *)
  | infer ctx Empty = Kan 0                (* Empty è Kan 0 *)
  | infer ctx (IndEmpty e) = infer ctx e   (* Eliminatore per Empty eredita il tipo *)
  | infer ctx (IndUnit e) = infer ctx e    (* Eliminatore per Unit eredita il tipo *)
  | infer ctx (IndBool e) = infer ctx e    (* Eliminatore per Bool eredita il tipo *)
  | infer ctx (Glue e) = infer ctx e       (* Glue eredita il tipo *)
  | infer ctx (GlueElem (r, u, a)) = infer ctx a (* GlueElem ha il tipo di a *)
  | infer ctx (Unglue (r, u, e)) = infer ctx e  (* Unglue eredita il tipo *)
  | infer ctx (Im e) = infer ctx e         (* Im eredita il tipo *)
  | infer ctx (Inf e) = Im (infer ctx e)   (* Inf costruisce un Im *)
  | infer ctx (Join e) = infer ctx e       (* Join eredita il tipo *)
  | infer ctx (IndIm (a, b)) = infer ctx b (* Eliminatore per Im eredita il tipo *)
  | infer ctx VI = Kan 0                   (* VI è Kan 0 *)

(*
 * Funzione di controllo del tipo: verifica che il termine e abbia tipo ty.
 * Utilizza l'inferenza e confronta i tipi normalizzati.
 *)
and check ctx e ty =
  let val ty' = infer ctx e                (* Inferisce il tipo di e *)
      val nTy = normalize ctx ty           (* Normalizza il tipo atteso *)
      val nTy' = normalize ctx ty'         (* Normalizza il tipo inferito *)
  in if alphaEq nTy nTy' then ()           (* Confronta i tipi normalizzati *)
     else raise Fail ("Mancata corrispondenza di tipo: atteso " ^ ppTerm ty ^ ", ottenuto " ^ ppTerm ty')
  end

(* Normalizzazione e alpha-equivalenza *)

(*
 * Normalizza un termine applicando sostituzioni e semplificazioni.
 * Attualmente gestisce solo variabili e costrutti principali.
 *)
and normalize ctx (Var x) =
      (case List.find (fn (y, _) => y = x) ctx of
           SOME (_, t) => t
         | NONE => Var x)
  | normalize ctx (Pi (x, a, b)) = Pi (x, normalize ctx a, normalize ctx b)
  | normalize ctx (PathP (p, a, b)) = PathP (normalize ctx p, normalize ctx a, normalize ctx b)
  | normalize ctx (And (a, b)) = And (normalize ctx a, normalize ctx b)
  | normalize ctx (Or (a, b)) = Or (normalize ctx a, normalize ctx b)
  | normalize ctx (Neg a) = Neg (normalize ctx a)
  | normalize ctx VI = VI
  | normalize ctx t = t  (* Altri casi non gestiti *)

(*
 * Verifica l'alpha-equivalenza tra due termini.
 * Confronta strutturalmente i termini, ignorando i nomi delle variabili legate.
 *)
and alphaEq (Var x) (Var y) = x = y
  | alphaEq (Pi (x1, a1, b1)) (Pi (x2, a2, b2)) =
      alphaEq a1 a2 andalso alphaEq b1 b2  (* Ignora il nome della variabile *)
  | alphaEq (PathP (p1, a1, b1)) (PathP (p2, a2, b2)) =
      alphaEq p1 p2 andalso alphaEq a1 a2 andalso alphaEq b1 b2
  | alphaEq (Kan n) (Kan m) = n = m
  | alphaEq (Pre n) (Pre m) = n = m
  | alphaEq VI VI = true
  | alphaEq (Dir d1) (Dir d2) = d1 = d2
  | alphaEq Unit Unit = true
  | alphaEq Bool Bool = true
  | alphaEq True True = true
  | alphaEq False False = true
  | alphaEq Empty Empty = true
  | alphaEq (And (a1, b1)) (And (a2, b2)) = alphaEq a1 a2 andalso alphaEq b1 b2
  | alphaEq (Or (a1, b1)) (Or (a2, b2)) = alphaEq a1 a2 andalso alphaEq b1 b2
  | alphaEq (Neg a) (Neg b) = alphaEq a b
  | alphaEq _ _ = false

(* Sostituzione di una variabile con un termine in un altro termine *)
and subst x e (Var y) = if x = y then e else Var y
  | subst x e (Lam (y, a, t)) = Lam (y, subst x e a, subst x e t)
  | subst x e (App (t1, t2)) = App (subst x e t1, subst x e t2)
  | subst x e (Pi (y, a, b)) = Pi (y, subst x e a, subst x e b)
  | subst x e (PathP (p, a, b)) = PathP (subst x e p, subst x e a, subst x e b)
  | subst x e (Transp (p, i)) = Transp (subst x e p, subst x e i)
  | subst x e (HComp (t, r, u, u0)) =
      HComp (subst x e t, subst x e r, subst x e u, subst x e u0)
  | subst x e (System (ts, phi)) = System (map (subst x e) ts, subst x e phi)
  | subst x e (Dir d) = Dir d
  | subst x e (And (a, b)) = And (subst x e a, subst x e b)
  | subst x e (Or (a, b)) = Or (subst x e a, subst x e b)
  | subst x e (Neg a) = Neg (subst x e a)
  | subst x e (Ref a) = Ref (subst x e a)
  | subst x e (Kan n) = Kan n
  | subst x e (Pre n) = Pre n
  | subst x e Unit = Unit
  | subst x e Bool = Bool
  | subst x e True = True
  | subst x e False = False
  | subst x e Empty = Empty
  | subst x e (IndEmpty e') = IndEmpty (subst x e e')
  | subst x e (IndUnit e') = IndUnit (subst x e e')
  | subst x e (IndBool e') = IndBool (subst x e e')
  | subst x e (Glue e') = Glue (subst x e e')
  | subst x e (GlueElem (r, u, a)) = GlueElem (subst x e r, subst x e u, subst x e a)
  | subst x e (Unglue (r, u, e')) = Unglue (subst x e r, subst x e u, subst x e e')
  | subst x e (Im e') = Im (subst x e e')
  | subst x e (Inf e') = Inf (subst x e e')
  | subst x e (Join e') = Join (subst x e e')
  | subst x e (IndIm (a, b)) = IndIm (subst x e a, subst x e b)
  | subst x e VI = VI

(* Test e validazione *)

(*
 * Funzione di test che verifica l'inferenza e la valutazione di diversi termini.
 * Utilizza un contesto predefinito e stampa i risultati.
 *)
fun testTerms () =
  let
    (* Contesto di tipi predefinito *)
    val typeCtx = [ ("A", Kan 0)
          , ("B", Kan 0)
          , ("a", Kan 0)
          , ("b", Kan 0)
          , ("f", Pi("x", Kan 0, Kan 0))
          , ("r", VI)
          , ("u", VI)
          ]
    
    (* Conversione del contesto di tipi in contesto di valutazione *)
    val evalCtx = map (fn (x, t) => (x, eval [] t)) typeCtx
    
    (* Termini di test *)
    val id = Lam("x", Var "A", Var "x")
    val const = Lam("x", Var "A", Lam("y", Var "B", Var "x"))
    val piTest = Pi("x", Var "A", Var "A")
    val andTest = And(Dir true, Dir false)
    val orTest = Or(Dir true, Dir false)
    val negTest = Neg(Dir true)
    val refTest = Ref(Var "a")
    val indEmptyTest = IndEmpty(Empty)
    val indUnitTest = IndUnit(Unit)
    val indBoolTest = IndBool(Bool)
    val glueTest = Glue(Var "A")
    val glueElemTest = GlueElem(Var "r", Var "u", Var "a")
    val unglueTest = Unglue(Var "r", Var "u", Var "a")
    val imTest = Im(Var "a")
    val infTest = Inf(Var "a")
    val joinTest = Join(Var "a")
    val indImTest = IndIm(Var "A", Var "a")
    
    (* Test aggiuntivi per la valutazione *)
    val lamNegTest = App(Lam("x", VI, Neg(Var "x")), Dir true)

    val hcompTest = HComp(Kan 0, Dir true, Lam("i", VI, Kan 0), True)
    val systemTest = System([True, False], And(Dir true, Dir false))
    
    val tests = [ id, const, piTest, andTest, orTest, negTest, refTest,
                  indEmptyTest, indUnitTest, indBoolTest, glueTest, glueElemTest, 
                  unglueTest, imTest, infTest, joinTest, indImTest,
                  lamNegTest ]
    
    (* Esegue un singolo test, stampando il termine, tipo e valutazione *)
    fun runTest t =
      (print ("Termine: " ^ ppTerm t ^ "\n");
       (print ("Tipo: " ^ ppTerm (infer typeCtx t) ^ "\n");
        print ("Valutazione: ");
        (print (ppValue (eval evalCtx t) ^ "\n\n") handle Fail err => print ("Errore: " ^ err ^ "\n\n"))))
  in
    List.app runTest tests
  end

val _ = testTerms ()