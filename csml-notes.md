# Notes on CSML

## Requirements for OpSem component

We need to be able to indicate at least the following:

- The order of execution
  - Entering a node, where might we go from there?
  - Exiting to a node from a subnode, where might we go from there?
- Which variables are declared or changed
- Which variables are de-scoped

## Questions

Some questions arise when considering how to design this. Namely:

### Should this be an independent language or should it be written in QL?

Pros:

- Allows us to make the notation simple, elegant, and readable.
- Allows us to make the notation parallel standards in CS.
- Useful for not just QL, but possible other tools as well.

Cons:

- Is another language to have to learn.
  - Counterpoint: programmers know lots of languages.
  - Counterpoint: this is only for extractor development, so expecting someone to learn a language for the extractor generator seems rereasonable
- Requires a specification and implementation.

### How much of the operational semantics should be encoded?

If we encode more stuff, we need to be able to represent more aspects of the
abstract machine. This could get arbitrarily complex.

Pros for generic opsem tool:

- Having a generic operational semantics tool would be useful beyond just QL.

Cons for generic opsem tool:

- It would require a semi-broad set of built in tools and types to allow for
  fairly comprehensive coverange.

### Pipeline from Spec DSL to Extractor

```

        ,---> alex+happy translator ---> alex+happy parser
        |
spec ---+---> db schema generator
        |
        `---> ql generator (using opsem for cfg, dataflow)

```

### Notes on CSML

- Simple algebraic datatypes with concrete and abstract syntaxes
  - Use standard CSML notation for this part
- Builtin support for list, set, multiset, and map types
  - This entails having a notion of pattern matching for each, probably
    - list matching is [xs\*, y, zs\*]
    - set and multiset matching is {x, ys\*}, {{x, ys\*}}
    - map matching is [[foo: x, kvs\*]]
    - all allow wildcards for the 'tail'-like variables
      - ie [_\*, y, _\*], {x, _\*}, {{x, _\*}}, [[foo: x, _\*]]
    - generic `in` operator?  `M in G` means...
      - `G = [_\*, M, _\*]` for lists
      - `G = {M, _\*}` for sets
      - `G = {{M, _\*}}` for multisets
      - nothing for maps? use `key in` and `value in` instead? or `K is V in Map` or something like that
      - alternative is to just force people to use the patterns like above to be e
    - should multisets have counts? eg. `{{ 5 x }}` or should they just use repetition?
      - if counts, is ther a difference between `{{ }}` and `{{ 0 x }}`? hopefully not! but what is Conor's World Types, then?
    - probably should also include notation for things like addition (`G,x`), removal (either `G\\x` or `G-x`), and updates on maps (`G[x=M]`)
      - These would be type-based sugar. E.g. `G,x` for lists means `G2` plus the constraint `G = [elE\*] and G2 = [elE*,x]`, while for maps `G[x=M]` means `G2` plus the constraint `G = [[elG*, x = _]] and G2 = [[elG*, x = M]]`.
- No need for builtin support for stacks and environments, just use the existing builtin types. We can conventionally just expect that stack and environment types will be declared as such.
  - To use a 
- Need some way to define inferences rules or step relations, depending on which is more necessary. Probably inference rules, because some step relations have conditional stepping.
  - Aren't inference rules just dependent datatypes? Well, not quite, because the proofs of them can't be referenced within the language itself, only declared.
  - Syntax for this should use the abstract syntax of the language, not the concrete syntax.
- Should do some amount of checking of the specs themselves: are all the variables/types in scope? AST vars are a subset of CST vars?

#### Example Program

```spec

syntax Term M, N, P
  ::= x          ~  x                (Variable)
    | pair(M;N)  ~  "<" M "," N ">"  (Pair)
    | fst(P)     ~  "fst" P          (Fst)
    | snd(P)     ~  "snd" P          (Snd)
    | lam(x.M)   ~  "\\" x "." M     (Lambda)
    | app(M;N)   ~  M N              (Application)
    ;;

syntax Value U, V
  ::= pair(U;V)     ~  "<" U "," V ">"    (Pair)
    | lam(x.M)      ~  "\\" x "." M       (Lambda)
    ;;

syntax Frame F
  ::= in-pair-l(N)  ~  "<" "_" "," N ">"  (Pair Left)
    | in-pair-r(U)  ~  "<" U "," "_" ">"  (Pair Right)
    | in-fst()      ~  "fst" "_"          (Fst Scrutinee)
    | in-snd()      ~  "snd" "_"          (Snd Scrutinee)
    | in-app-l(N)   ~  "_" N              (Application Function)
    | in-app-r(U)   ~  U "_"              (Application Argument)
    ;;

syntax Context K = List Frame;;

syntax Machine S
  ::= enter(K;M)  ~  K ">>" M  (Entering State)
    | exit(K,V)   ~  K "<<" V  (Exiting State)
    ;;

meta Term  SUBST(U;x;M)  ~  "[" U "/" x "]" M   (Substitution);;

predicate step(M,N) =
    
    -- pair(M;N)
  | [enter pair left]  step( enter(K; pair(M,N))      ,  enter(in-pair-l(N):K; M) )
  | [exit pair left]   step( exit(in-pair-l(N):K; U)  ,  enter(in-pair-r(U):K, N) )
  | [exit pair right]  step( exit(in-pair-r(U):K; V)  ,  exit(K; pair(U;V))       )
  
    -- fst(P)
  | [enter fst]  step( enter(K; fst(P))             ,  enter(in-fst():K; P) )
  | [exit fst]   step( exit(in-fst():K; pair(U;_))  ,  exit(K; U) )

    -- snd(P)
  | [enter snd]  step( enter(K; snd(P))             ,  enter(in-snd():K; P) )
  | [exit snd]   step( exit(in-snd():K; pair(_;V))  ,  exit(K; V)           )

    -- lam(x.M)
  | [enter lam]  step( enter(K; lam(x.M))  ,  exit(K; lam(x.M)) )

    -- app(M;N)
  | [enter app left]  step( enter(K; app(M;N))             ,  enter(in-app-l(N):K; M) )
  | [exit app left]   step( exit(in-app-l(N):K; U)         ,  enter(in-app-r(U):K; N) )
  | [exit app right]  step( exit(in-app-r(lam(x.M)):K; V)  ,  enter(K; SUBST(V;x;M))  )
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

syntax Type A, B, C
  ::= prod(A;B)  ~  A "*" B   (Product)
    | fun(A;B)   ~  A "->" B  (Function)
    ;;

syntax CtxJ J ::=  vty(x;A)  ~  x ":" A  (Variable Type Judgment);;

syntax Ctx G = List CtxJ;;

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
