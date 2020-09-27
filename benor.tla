------------------------------- MODULE benor -------------------------------
EXTENDS Integers, Sequences, FiniteSets
CONSTANT N, F, MAXROUND,INPUT
\* INPUT= <<0,1,1,1>> e.g. for N=4, binary consensus
 
ASSUME F<N
Procs == 1..N

(*
--algorithm benor
{ variable p1Msg={}, p2Msg={};  \* phase 1 messages board & phase 2 messages board
                                
  
  define{
  
    Value(M) == {msg[3]: msg \in M}
    P1Value(r) == {msg \in p1Msg: msg[2] = r}
    P2Value(r) == {msg \in p2Msg: msg[2] = r}
    P1SentMsg(r,v) == {msg \in p1Msg: msg[2] = r /\ msg[3] = v}
    P2SentMsg(r,v) == {msg \in p2Msg: msg[2] = r /\ msg[3] = v}
    
    
  }
  
  \* Phase 1- Check for the values to be proposed for the second phase from the majority nodes
  macro P1Macro(r){
  
    await (Cardinality(P1Value(r)) >= N-F);
    if (\E v \in {0,1}: 2 * Cardinality(P1SentMsg(r,v))>N) {
    
        \* select p2v value based on majority nodes proposed value in this round and propose the same to phase 2
        p2v := CHOOSE v \in Value(P1Value(r)): 2* Cardinality(P1SentMsg(r,v))>N; 
    }
  }
  macro P2Macro(r){
   
    await (Cardinality(P2Value(r)) >= N-F);
    if (\E v \in {0,1}: Cardinality(P2SentMsg(r,v)) >= F+1){
    
        \* If there are atleast F+1 proposal messages with value = 0, then decide value 0, or
        \* If there are atleast F+1 proposal messages with value = 1, then decide value 1
        p1v := CHOOSE v \in Value(P2Value(r)) : v # -1;
        decided := {p1v};
        }
        
    else if (\E v \in Value(P2Value(r)) : v # -1){
        p1v := CHOOSE v \in Value(P2Value(r)) : v # -1;
        }
    else with (rand \in {0,1}) {
        \* A random value either 0 or 1 is being proposed for the next round in case if there was no value. 
        p1v := rand;
        }
    
  }  
 

  fair process (p \in Procs)
  variable r=1, p1v=INPUT[self], p2v=-1, decided={},x,y;
  { 
     
  S: while(r<= MAXROUND){
        \* program is run until value is not decided as 0 or 1, or MAXROUND is reached
        x := <<self,r,p1v>>;
        p1Msg := p1Msg \union {x};
        p2v := -1;
  P1:   P1Macro(r);
        y := <<self, r, p2v>>;
        p2Msg := p2Msg \union {y};
  P2:   P2Macro(r);
        r := r+1;
             
     }\* end while
  }\* end process


} \* end algorithm
*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-fb64ef8c1bb7abedb3b423ea2fc7138e
CONSTANT defaultInitValue
VARIABLES p1Msg, p2Msg, pc

(* define statement *)
Value(M) == {msg[3]: msg \in M}
P1Value(r) == {msg \in p1Msg: msg[2] = r}
P2Value(r) == {msg \in p2Msg: msg[2] = r}
P1SentMsg(r,v) == {msg \in p1Msg: msg[2] = r /\ msg[3] = v}
P2SentMsg(r,v) == {msg \in p2Msg: msg[2] = r /\ msg[3] = v}

VARIABLES r, p1v, p2v, decided, x, y

vars == << p1Msg, p2Msg, pc, r, p1v, p2v, decided, x, y >>

ProcSet == (Procs)

Init == (* Global variables *)
        /\ p1Msg = {}
        /\ p2Msg = {}
        (* Process p *)
        /\ r = [self \in Procs |-> 1]
        /\ p1v = [self \in Procs |-> INPUT[self]]
        /\ p2v = [self \in Procs |-> -1]
        /\ decided = [self \in Procs |-> {}]
        /\ x = [self \in Procs |-> defaultInitValue]
        /\ y = [self \in Procs |-> defaultInitValue]
        /\ pc = [self \in ProcSet |-> "S"]

S(self) == /\ pc[self] = "S"
           /\ IF r[self]<= MAXROUND
                 THEN /\ x' = [x EXCEPT ![self] = <<self,r[self],p1v[self]>>]
                      /\ p1Msg' = (p1Msg \union {x'[self]})
                      /\ p2v' = [p2v EXCEPT ![self] = -1]
                      /\ pc' = [pc EXCEPT ![self] = "P1"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                      /\ UNCHANGED << p1Msg, p2v, x >>
           /\ UNCHANGED << p2Msg, r, p1v, decided, y >>

P1(self) == /\ pc[self] = "P1"
            /\ (Cardinality(P1Value(r[self])) >= N-F)
            /\ IF \E v \in {0,1}: 2 * Cardinality(P1SentMsg(r[self],v))>N
                  THEN /\ p2v' = [p2v EXCEPT ![self] = CHOOSE v \in Value(P1Value(r[self])): 2* Cardinality(P1SentMsg(r[self],v))>N]
                  ELSE /\ TRUE
                       /\ p2v' = p2v
            /\ y' = [y EXCEPT ![self] = <<self, r[self], p2v'[self]>>]
            /\ p2Msg' = (p2Msg \union {y'[self]})
            /\ pc' = [pc EXCEPT ![self] = "P2"]
            /\ UNCHANGED << p1Msg, r, p1v, decided, x >>

P2(self) == /\ pc[self] = "P2"
            /\ (Cardinality(P2Value(r[self])) >= N-F)
            /\ IF \E v \in {0,1}: Cardinality(P2SentMsg(r[self],v)) >= F+1
                  THEN /\ p1v' = [p1v EXCEPT ![self] = CHOOSE v \in Value(P2Value(r[self])) : v # -1]
                       /\ decided' = [decided EXCEPT ![self] = {p1v'[self]}]
                  ELSE /\ IF \E v \in Value(P2Value(r[self])) : v # -1
                             THEN /\ p1v' = [p1v EXCEPT ![self] = CHOOSE v \in Value(P2Value(r[self])) : v # -1]
                             ELSE /\ \E rand \in {0,1}:
                                       p1v' = [p1v EXCEPT ![self] = rand]
                       /\ UNCHANGED decided
            /\ r' = [r EXCEPT ![self] = r[self]+1]
            /\ pc' = [pc EXCEPT ![self] = "S"]
            /\ UNCHANGED << p1Msg, p2Msg, p2v, x, y >>

p(self) == S(self) \/ P1(self) \/ P2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Procs: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-96a4ac3a4d93dfcfcd4b0fd2df28a44e

Agreement == \A j,k \in Procs: Cardinality(decided[j])=1  /\ Cardinality(decided[k])=1 => decided[j]=decided[k]

MinorityReport == ~ \A j \in Procs: decided[j]={0}

Progress  == <> (\A j \in Procs: Cardinality(decided[j])>0)

\* Exclude failed processes

=========================================================
=============================================================================
\* Modification History
\* Last modified Tue Jul 14 16:26:33 EDT 2020 by g_hus
\* Last modified Fri Jul 03 18:15:09 EDT 2020 by Sheryl Evangelene
\* Last modified Mon Jun 29 19:19:55 EDT 2020 by Sheryl Evangelene
\* Last modified Wed Jun 24 08:37:04 EDT 2020 by bekir
\* Created Wed Jun 24 07:53:22 EDT 2020 by bekir


\*
\* Team Member    Name                            UB Name     #UBID
\* #1             Sheryl Evangelene Pulikandala   sherylev    50288214
\* #2             Gulfam Hussain                  gulfamhu    50315477

\* References:
\* Lecture slides, recordings and piazza discussion
\* Book- The-PlusCal-Algorithm-Language
\* Book- Practical TLA+ by Hillel Wayne
\* https://learntla.com/pluscal/a-simple-spec/
\* Dr. Murat blog page
\* https://lamport.azurewebsites.net/pubs/pluscal.pdf
\* https://lamport.azurewebsites.net/tla/c-manual.pdf
