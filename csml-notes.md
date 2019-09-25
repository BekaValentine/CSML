# Notes on CSML

## Requirements for OpSem component

We need to be able to indicate at least the following:

- The order of execution
  - Entering a node, where might we go from there?
  - Exiting to a node from a subnode, where might we go from there?
- Which variables are declared or changed
- Which variables are de-scoped

## Notes on language design

- Simple algebraic datatypes with concrete and abstract syntaxes
  - Use standard CSML notation for this part
- No builtin types like list or set. Everything is syntactic and explicit.
- No need for builtin support for stacks and environments, just use the existing builtin types. We can conventionally just expect that stack and environment types will be declared as such.
  - To use a type as a stack or environment or whatever, the external user of the program would constrain its types appropriately. E.g., if we expect stacks to be stacks of `Value`s, then the external user of the spec will only accept as valid an appropriately named type that is defined to be `Value`.
- Need some way to define inferences rules or step relations, depending on which is more necessary. Probably inference rules, because some step relations have conditional stepping.
  - Aren't inference rules just dependent datatypes? Well, not quite, because the proofs of them can't be referenced within the language itself, only declared.
  - Syntax for this should use the abstract syntax of the language, not the concrete syntax.
- Should do some amount of checking of the specs themselves: are all the variables/types in scope? AST vars are a subset of CST vars?

#### Example Program

```spec

syntactic Term M, N, P ::=
  | x          ~  x                (Variable)
  | pair(M;N)  ~  "<" M "," N ">"  (Pair)
  | fst(P)     ~  "fst" P          (Fst)
  | snd(P)     ~  "snd" P          (Snd)
  | lam(x.M)   ~  "\\" x "." M     (Lambda)
  | app(M;N)   ~  M N              (Application)
  ;;

syntactic Value U, V ::=
  | pair(U;V)     ~  "<" U "," V ">"    (Pair)
  | lam(x.M)      ~  "\\" x "." M       (Lambda)
  ;;

syntactic Frame F ::=
  | in-pair-l(N)  ~  "<" "_" "," N ">"  (Pair Left)
  | in-pair-r(U)  ~  "<" U "," "_" ">"  (Pair Right)
  | in-fst()      ~  "fst" "_"          (Fst Scrutinee)
  | in-snd()      ~  "snd" "_"          (Snd Scrutinee)
  | in-app-l(N)   ~  "_" N              (Application Function)
  | in-app-r(U)   ~  U "_"              (Application Argument)
  ;;

syntactic Context K ::=
  | done() ~ "<>" (EmptyStack)
  | continue(K;F) ~ K "," F (NonEmptyStack)
  ;;

syntactic Machine S ::=
  | enter(K;M)  ~  K ">>" M  (Entering State)
  | exit(K,V)   ~  K "<<" V  (Exiting State)
  ;;

predicate step(S_0, S_1) =
    
    -- pair(M;N)
  | [enter pair left]  !- step( enter(K; pair(M,N))                ,  enter(continue(K;in-pair-l(N)); M) )
  | [exit pair left]   !- step( continue(K;exit(in-pair-l(N)); U)  ,  enter(continue(K;in-pair-r(U)), N) )
  | [exit pair right]  !- step( continue(K;exit(in-pair-r(U)); V)  ,  exit(K; pair(U;V))                 )
  
    -- fst(P)
  | [enter fst]  !- step( enter(K; fst(P))                       ,  enter(continue(K;in-fst()); P) )
  | [exit fst]   !- step( exit(continue(K;in-fst()); pair(U;_))  ,  exit(K; U)                     )

    -- snd(P)
  | [enter snd]  !- step( enter(K; snd(P))                       ,  enter(continue(K;in-snd()); P) )
  | [exit snd]   !- step( exit(continue(K;in-snd()); pair(_;V))  ,  exit(K; V)                     )

    -- lam(x.M)
  | [enter lam]  !- step( enter(K; lam(x.M))  ,  exit(K; lam(x.M)) )

    -- app(M;N)
  | [enter app left]  !- step( enter(K; app(M;N))                       ,  enter(continue(K;in-app-l(N)); M) )
  | [exit app left]   !- step( exit(continue(K;in-app-l(N)); U)         ,  enter(continue(K;in-app-r(U)); N) )
  | [exit app right]  !- step( exit(continue(K;in-app-r(lam(x.M))); V)  ,  enter(K; SUBST(V;x;M))            )
  ;;

predicate steps(S_0, S_1) =
  | [refl]                                    !-  steps(S, S)
  | [step]  step(S_0, S_1) , steps(S_1, S_2)  !-  steps(S_0, S_2)
  ;;

predicate eval(M,V) =
  | [pair]  eval(M;U) , eval(N,V)   !-  eval(pair(M;N), pair(U;V))
  | [fst]   eval(P; pair(U,_))      !-  eval(fst(P), U)
  | [snd]   eval(P; pair(_,V))      !-  eval(snd(P), V)
  | [lam]                           !-  eval(lam(x.M), lam(x.M))
  | [app]   eval(M; lam(x.M'))      ,
            eval(N; V)              ,
            eval(SUBST(V;x;M'), U)  !-  eval(app(M;N), U)
  ;;

syntactic Type A, B, C ::=
  | prod(A;B)  ~  A "*" B   (Product)
  | fun(A;B)   ~  A "->" B  (Function)
  ;;

syntactic CtxJ J ::=  vty(x;A)  ~  x ":" A  (Variable Type Judgment);;

syntactic Ctx G = List CtxJ;;

predicate hastype(G,M,A) =
  | [var]   vty(x;A) in G                        !-  hastype(G, x, A)
  | [pair]  hastype(G, M, A) , hastype(G, N, B)  !-  hastype(G, pair(M;N), prod(A;B))
  | [fst]   hastype(G, P, prod(A;B))             !-  hastype(G, fst(P), A)
  | [snd]   hastype(G, P, prod(A;B))             !-  hastype(G, snd(P), B)
  | [lam]   hastype(vty(x;A):G, M, B)            !-  hastype(G, lam(x.M), fun(A;B))
  | [app]   hastype(G, M, fun(A;B))              ,
            hastype(G, N, A)                     !-  hastype(G, app(M;N), B)
  ;;

```
