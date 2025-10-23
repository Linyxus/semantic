#import "@preview/ctheorems:1.1.3": *

#set page(margin: 0.4in, numbering: "1")
#set heading(numbering: "1.1")
#set text(font: "CommitMono", weight: "regular", size: 9pt)
#show math.equation: set text(font: "Latin Modern Math", size: 11pt)
#show: thmrules

#set document(
  title: "Semantic Type Soundness for System Capless",
  author: "Yichen Xu"
)

#align(center)[
  #v(3em)
  #text(size: 17pt, weight: "bold")[
    Semantic Type Soundness for System Capless
  ] \
  #v(1em)
  Yichen Xu\
  Autumn 2025
  #v(2em)
]

#let systemname(s) = text(font: "Latin Modern Sans 12", weight: "light", size: 12pt)[#s]
#let capt = move(dy: -0.3em)[#h(-0.5em) #text(size: 0.7em)[$∧$] #h(-0.5em)]
#let infrule(name, from, to) = $ #from / #to quad sans("(")sans(#name)sans(")") $
#let turnstile = text(size: 0.9em)[$tack.r$]
#let sturnstile = text(size: 0.9em)[$models$]
#let typ(cs, ctx, e, t) = $ #cs\; #ctx turnstile #e : #t $
#let wf(ctx, obj) = $ #ctx turnstile #obj sans("wf") $
#let subtyp(ctx, t1, t2) = $ #ctx turnstile #t1 <: #t2 $
#let pack(c, x) = $ angle.l #c, #x angle.r $
#let sem(body) = $ lr([|#body|])$
#let semtyp(cs, ctx, exp, t) = $ #cs\; #ctx sturnstile #exp : #t $
#let semctxtyp(ctx, typenv, heap) = $ (#ctx, #typenv) sturnstile #heap $
#let fun = $lambda$

// Theorem environments
#let theorem = thmbox("theorem", "Theorem", fill: rgb("#e8f4f8"))
#let proposition = thmbox("proposition", "Proposition", fill: rgb("#e8f4f8"))
#let lemma = thmbox("lemma", "Lemma", fill: rgb("#efe6ff"))
#let corollary = thmbox("corollary", "Corollary", fill: rgb("#e8f4f8"))
#let definition = thmbox("definition", "Definition", fill: rgb("#f0f0f0"))
#let remark = thmplain("remark", "Remark")
#let example = thmplain("example", "Example")
#let proof = thmproof("proof", "Proof")

#show "Capless": it => systemname(it)
#show "CC": it => $systemname("CC")_(<:square)$
#show "Unit": it => $sans("Unit")$
#show "Capability": it => $sans("Capability")$

This document drafts semantic type soundness for System Capless.
We first formally define System Capless,
then sketch logical type soundness proof for it.

= Definitions of System Capless

The following sections define System Capless.

== Syntax

#figure(
  grid(
    columns: 2,
    gutter: 5em,
    $
    x,y,z &quad & quad& sans(bold("Term Variable")) \
    T, U &quad & quad& sans(bold("Type Variable")) \
    c &quad & quad& sans(bold("Capture Variable")) \
    S, R quad&:=quad & quad quad& sans(bold("Shape Type")) \
    && top quad&sans("Top") \
    && X quad&sans("Type Variable") \
    && (x: T) -> E quad&sans("Function") \
    && [X<:S] -> E quad&sans("Type Function") \
    && [c <: B] -> E quad&sans("Capture Function") \
    && "Unit" quad&sans("Unit") \
    && "Capability" quad&sans("Capability") \
    S, R quad&:=quad & quad quad S capt C quad&sans(bold("Shape Type")) \
    E, F &quad:=quad & quad quad quad&sans(bold("Existential Type")) \
    && exists c. T quad&sans("existential type") \
    && T quad&sans("capturing type") \
    theta quad&:=quad & quad quad quad&sans(bold("Capture")) \
    && x quad&sans("variable") \
    && c quad&sans("capability") \
    C quad&:=quad & {theta_1,dots,theta_n} quad&sans(bold("Capture Set")) \
    B quad&:=quad & * quad|quad C quad&sans(bold("Capture Bound")) \
    $,
    $
    s, t, u quad&:=quad & quad quad&sans(bold("Term")) \
    && a quad&sans("answer") \
    && x thin y quad&sans("application") \
    && x[S] quad&sans("type application") \
    && x[C] quad&sans("capture application") \
    && "let" x = t "in" u quad&sans("let") \
    && "unpack" t "as" pack(c,x) "in" u quad&sans("unpack") \
    a quad&:=quad & quad quad& sans(bold("Answer")) \
    && x quad&sans("variable") \
    && v quad&sans("value") \
    v quad&:=quad & quad quad& sans(bold("Value")) \
    && () quad&sans("Unit") \
    && lambda (x: T). t quad&sans("Function") \
    && lambda [X<:S]. t quad&sans("Type Function") \
    && lambda [c <: B]. t quad&sans("Capture Function") \
    && pack(C,x) quad&sans("Packing") \
    Gamma quad&:=quad &   quad& sans(bold("Type Context")) \
    && [] quad&sans("") \
    && Gamma,x:T quad&sans("") \
    && Gamma,X<:S quad&sans("") \
    && Gamma,c<:B quad&sans("") \
    Sigma quad&:=quad & dot | Sigma, x mapsto v | Sigma, x mapsto bold("cap") quad& sans(bold("Store")) \
    $
  ),
  caption: "Syntax of System Capless.",
) <syntax_defs>

@syntax_defs defines the syntax of System Capless.
It is an extension of System CC.

== Type System

#figure(
[

#align(left)[
#text(weight: "bold")[Typing] $quad typ(C, Gamma, t, E)$
]

#grid(
  columns: 2,
  gutter: 1em,

  infrule(
    "var", 
    $x: S capt C in Gamma$,
    $typ({x}, Gamma, x, S capt {x})$,
  ),

  infrule(
    "sub",
    $typ(C_1, Gamma, e, T_1) quad wf(Gamma, C_2\, T_2) \
     subtyp(Gamma, T_1, T_2) quad subtyp(Gamma, C_1, C_2)$,
    $typ(C_2, Gamma, e, T_2)$,
  ),

  infrule(
    "var", 
    $$,
    $typ({}, Gamma, (), "Unit")$,
  ),

  infrule(
    "abs",
    $typ(C, (Gamma, x: T), t, E)$,
    $typ({}, Gamma, lambda (x: T) t, ((x: T) -> E) capt (C \\ {x}))$,
  ),

  infrule(
    "tabs",
    $typ(C, (Gamma, X<:S), t, E)$,
    $typ({}, Gamma, lambda [X<:S] t, ([X<:S] -> E) capt C)$,
  ),

  infrule(
    "cabs",
    $typ(C, (Gamma, c<:B), t, E) quad 
     wf(Gamma, C)$,
    $typ({}, Gamma, lambda [c<:B] t, ([X<:S] -> E) capt C)$,
  ),

  infrule(
    "app",
    $typ(C, Gamma, x, ((z: T) -> E) capt C_f) quad
     typ(C, Gamma, y, T)$,
    $typ(C, Gamma, x thin y, [z:=x]E)$,
  ),

  infrule(
    "tapp",
    $typ(C, Gamma, x, ([X<:S] -> E) capt C_f)$,
    $typ(C, Gamma, x[S], [X:=S]E)$,
  ),

  infrule(
    "capp",
    $typ(C, Gamma, x, ([c<:B] -> E) capt C_f) quad
     subtyp(Gamma, C, B)$,
    $typ(C, Gamma, x[C], [c:=C]E)$,
  ),

  infrule(
    "pack",
    $typ(C, Gamma, x, [c:=C]T)$,
    $typ(C, Gamma, angle.l C\, x angle.r, exists c. T)$,
  ),

)

#infrule(
  "let",
  $typ(C, Gamma, t, T) quad typ(C, (Gamma, x: T), u, U) quad wf(Gamma, C\, U)$,
  $typ(C, Gamma, "let" x = t "in" u, U)$,
)

#infrule(
  "unpack",
  $typ(C, Gamma, t, exists c. T) quad typ(C, (Gamma, c<:*, x: T), u, U) quad wf(Gamma, (C\\{x})\, U)$,
  $typ(C\\{x}, Gamma, "unpack" t "as" angle.l c\, x angle.r "in" u, U)$,
)

#align(left)[
#text(weight: "bold")[Subcapturing] #h(1em)
$subtyp(Gamma, C_1, C_2), subtyp(Gamma, C, B)$
]

#grid(
  columns: 2,
  gutter: 2em,

  infrule(
    "sc-subset",
    $C_1 subset.eq C_2$,
    $subtyp(Gamma, C_1, C_2)$
  ),

  infrule(
    "sc-trans",
    $subtyp(Gamma, C_1, C_2) quad subtyp(Gamma, C_2, C_3)$,
    $subtyp(Gamma, C_1, C_3)$
  ),

  infrule(
    "sc-union",
    $subtyp(Gamma, C_1, C) quad subtyp(Gamma, C_2, C)$,
    $subtyp(Gamma, C_1 union C_2, C)$
  ),

  infrule(
    "sc-var",
    $x : S capt C in Gamma$,
    $subtyp(Gamma, {x}, C)$
  ),

  infrule(
    "sc-cvar",
    $c <: C in Gamma$,
    $subtyp(Gamma, {c}, C)$
  ),

  infrule(
    "sc-bound",
    "",
    $subtyp(Gamma, C, *)$
  ),
)

#align(left)[
#text(weight: "bold")[Subtyping] $quad subtyp(Gamma, E_1, E_2)$
]

#grid(
  columns: 2,
  gutter: 2em,

  infrule(
    "top",
    $$,
    $subtyp(Gamma, S, top)$
  ),

  infrule(
    "refl",
    $$,
    $subtyp(Gamma, S, S)$
  ),

  infrule(
    "trans",
    $subtyp(Gamma, S_1, S_2) quad subtyp(Gamma, S_2, S_3)$,
    $subtyp(Gamma, S_1, S_3)$
  ),

  infrule(
    "tvar",
    $X<:S in Gamma$,
    $subtyp(Gamma, X, S)$
  ),

  infrule(
    "exists",
    $subtyp((Gamma,c<:*), T_1, T_2)$,
    $subtyp(Gamma, exists c. T_1, exists c. T_2)$
  ),

  infrule(
    "fun",
    $subtyp(Gamma, T_2, T_1) quad subtyp((Gamma,x:T_2), E_1, E_2)$,
    $subtyp(Gamma, (x: T_1) -> E_1, (x: T_2) -> E_2)$
  ),

  infrule(
    "tfun",
    $subtyp(Gamma, S_2, S_1) quad subtyp((Gamma,X<:S_2), E_1, E_2)$,
    $subtyp(Gamma, [X<:S_1] -> E_1, [X<:S_2] -> E_2)$
  ),

  infrule(
    "cfun",
    $subtyp(Gamma, B_2, B_1) quad subtyp((Gamma,c<:B_2), E_1, E_2)$,
    $subtyp(Gamma, [c<:B_1] -> E_1, [c<:B_2] -> E_2)$
  ),
)

],
caption: "Type System of System Capless.",
placement: auto,
) <typing_defs>

@typing_defs defines the type system of System Capless.

== Operational Semantics

#figure(
[
$
Sigma | x thin y &-->^{} Sigma | [z:=y]t & quad "if " Sigma(x) = lambda (z: T) t quad&quad sans("(e-apply)") \
Sigma | x thin y &-->^{x} Sigma | () & quad "if " Sigma(x) = bold("cap") "and" Sigma(y) = () quad&quad sans("(e-invoke)") \
Sigma | x[S] &-->^{} Sigma | [X:=top]t & quad "if " Sigma(x) = lambda [X<:S'] t quad&quad sans("(e-tapply)") \
Sigma | x[C] &-->^{} Sigma | [c:={}]t & quad "if " Sigma(x) = lambda [c<:B] t quad&quad sans("(e-capply)") \
Sigma | "let" x = t "in" u &-->^C Sigma' | "let" x = t' "in" u & quad "if " Sigma | t -->^C Sigma' | t' quad&quad sans("(e-ctx1)") \
Sigma | "unpack" t "as" angle.l c\, x angle.r "in" u &-->^C Sigma' | "unpack" t' "as" angle.l c\, x angle.r "in" u & quad "if " Sigma | t -->^C Sigma' | t' quad&quad sans("(e-ctx2)") \
Sigma | "let" x = y "in" t &-->^{} Sigma | [x:=y]t & quad "" quad&quad sans("(e-rename)") \
Sigma | "let" x = v "in" t &-->^{} (Sigma,x mapsto v) | t & quad "" quad&quad sans("(e-lift)") \
Sigma | "unpack" pack(c',x') "as" pack(c,x) "in" u &-->^{} Sigma | [c:=c'][x:=x']u & quad "" quad&quad sans("(e-unpack)") \
$
],
caption: "Operational Semantics of System Capless.",
placement: auto,
) <evaluation_defs>

@evaluation_defs defines the small-step evaluation relation,
$Sigma | s -->^C Sigma' | s'$,
for System Capless.
This evaluation relation is indexed by a capability set $C$,
restricting the program from using capabilities outside $C$ during evaluation.
We write
$Sigma | s -->^C_* Sigma' | s' $
for the reflexive, transitive closure of
$Sigma | s -->^C Sigma' | s'$,
with all $C$ being all capability sets along the trace unioned together.
In other words,
given $Sigma_1 | t_1 -->^C_1 Sigma_2 | t_2 -->^C_2 ... -->^C_n Sigma_(n+1) | t_(n+1)$,
we have $Sigma_1 | t_1 -->^(C_1 union C_2 union ... union C_n)_* Sigma_(n+1) | t_(n+1)$.


#figure(
[

#grid(
  columns: 2,
  column-gutter: 4em,
  row-gutter: 1em,

  infrule(
    "bs-ans",
    $Q(a)(Sigma)$,
    $Sigma | a ->>^C Q$,
  ),

  infrule(
    "bs-apply",
    $Sigma(x) = lambda (z: T) t quad Sigma | [z:=y]t ->>^C Q$,
    $Sigma | x thin y ->>^C Q$,
  ),

  infrule(
    "bs-tapply",
    $Sigma(x) = lambda [X<:S] t quad Sigma | [X:=top]t ->>^C Q$,
    $Sigma | x[S'] ->>^C Q$,
  ),

  infrule(
    "bs-capply",
    $Sigma(x) = lambda [c<:B] t quad Sigma | [c:={}]t ->>^C Q$,
    $Sigma | x[C'] ->>^C Q$,
  ),

  infrule(
    "bs-invoke",
    $Sigma(x) = bold("cap") quad Sigma(y) = () \
    Q(())(Sigma) quad x in C$,
    $Sigma | x thin y ->>^C Q$
  ),


)

#infrule(
  "bs-let",
  $Sigma | t ->>^C Q'\
  (forall v forall Sigma', 
    Sigma subset.sq Sigma' -> Q'(v)(Sigma') -> (Sigma',x mapsto v) | u ->>^C Q)\
  (forall z forall Sigma', 
    Sigma subset.sq Sigma' -> Q'(z)(Sigma') -> Sigma' | [x:=z]u ->>^C Q)$,
  $Sigma | "let" x = t "in" u ->>^C Q$
)

#infrule(
  "bs-unpack",
  $Sigma | t ->>^C Q'\
  (forall C' forall z forall Sigma', 
    Sigma subset.sq Sigma' -> Q'(pack(C',z))(Sigma') -> Sigma | [x:=z][c:={}]u ->>^C Q)$,
  $Sigma | "unpack" t "as" pack(c,x) "in" u ->>^C Q$
)

],
caption: "Big-Step Evaluation for System Capless.",
placement: auto,
) <fig:bigstep>

@fig:bigstep defines a big-step evaluation relation.
$Sigma | t ->>^C Q$
means that for any possible evaluation $Sigma | t -->^C_* Sigma' | a$,
the resulting configuration satisfies the postcondition $Q$.

#proposition[
  Given $Sigma | t ->>^C Q$,
  there exist $Sigma'$ and $a$ such that $Sigma subset.sq Sigma' and Q(a)(Sigma')$.
] <prop:bigstep_to_smallstep_exists>

#proposition[
  Given $Sigma | t ->>^C Q$,
  for any $Sigma'$ and $a$ such that $Sigma | t -->^C_* Sigma' | a$,
  we have $Q(a)(Sigma')$.
] <prop:bigstep_to_smallstep>

#proposition[
  If $forall Sigma' forall a, (Sigma | t -->^C_* Sigma' | a) -> Q(a)(Sigma')$,
  then $Sigma | t ->>^C Q$.
] <prop:smallstep_to_bigstep>

@prop:bigstep_to_smallstep_exists,
@prop:bigstep_to_smallstep,
and @prop:smallstep_to_bigstep
establish the equivalence between small-step evaluation and big-step evaluation.

= Semantic Type Soundness

== Type Denotation

The types are interpreted into predicates.
The interpretation is done under a type environment $rho$,
which maps type variables to predicates
of the type $"CaptureSet" -> "Term" -> "Heap" -> "Prop"$
(representing the denotation function for shape types parameterized by capability sets);
term variables to capability sets;
and capture variables to capability sets.

Given predicates $P$ and $Q$ of type
$"CaptureSet" -> "Term" -> "Heap" -> "Prop"$,
we write
$P => Q$
for the logical implication between them:
$P => Q  "iff"  forall C forall t forall Sigma, P(C)(t)(Sigma) -> Q(C)(t)(Sigma)$.

We write $Sigma_1 subset.sq Sigma_2$
for subsumption between stores:
$Sigma_1 subset.sq Sigma_2 "iff" forall x, Sigma_1(x) = e -> Sigma_2(x) = e$.
Here $e$ can be either a value $v$ or a capability $bold("cap")$.

We write $cal(C)$ for a capture set that contains only capabilities in the store $Sigma$,
i.e. $cal(C) = {x_1, dots, x_n}$ and $forall i, Sigma(x_i) = bold("cap")$.
The store is inferred from the context in which $cal(C)$ is used.

We write $Sigma(t)$ for resolving a term $t$ in the store $Sigma$.
Basically, if $t$ is a variable $x$, then $Sigma(t) = Sigma(x)$;
otherwise, $Sigma(t) = t$.

We write $sem(S)_(rho,dot)$ as a shorthand for
$fun cal(C). sem(S)_(rho,cal(C))$.

We first define the denotation of capture sets and capture bounds,
which maps them to sets of capabilities.
$
sem({})_rho &= {} \
sem({x})_rho &= rho(x) \
sem({c})_rho &= rho(c) \
sem(C_1 union C_2)_rho &= sem(C_1) union sem(C_2) \
sem(*)_rho &= NN \
$

Type denotations are defined as follows.
The denotation function now acts on shape types and takes a capability set as an additional parameter.
$
sem(top)_(rho,cal(C)) &= fun t. fun Sigma. sans("True") \
sem("Unit")_(rho,cal(C)) &= fun t. fun Sigma. thin thin t = () \
sem("Capability")_(rho,cal(C)) &= fun t. fun Sigma. exists z.
  z in sem(C)_rho and Sigma(z) = bold("cap") \
sem(X)_(rho,cal(C)) &= rho(X)(sem(C)_rho) \
sem((x: T) -> E)_(rho,cal(C)) &=
  fun t. fun Sigma.
    exists T_0 t_0,
    Sigma(t) = lambda (z : T_0) t_0 and \
    & quad forall z forall Sigma',
      Sigma subset.sq Sigma' ->
      sem(T)_(rho) (z)(Sigma') ->
      sem(E)^e_(([x:=sem(C_T)_rho]rho),cal(C))([x:=z]t_0)(Sigma') \
    & "where" T = S_T capt C_T \
sem([X<:S] -> E)_(rho,cal(C)) &=
  fun t. fun Sigma.
    exists S_0 t_0,
    Sigma(t) = lambda [X<: S_0] t_0 and \
    & quad forall P forall Sigma',
      Sigma subset.sq Sigma' ->
      (P => sem(S)_(rho,dot)) ->
      sem(E)^e_(([X:=P]rho),cal(C))([x:=top]t_0)(Sigma') \
sem([c<:B] -> E)_(rho,cal(C)) &=
  fun t. fun Sigma.
    exists B_0 t_0,
    Sigma(t) = lambda [c<:B_0] t_0 and \
    & quad forall C_0 forall Sigma',
      Sigma subset.sq Sigma' ->
      (C_0 subset.eq sem(B)_rho) ->
      sem(E)^e_(([c:=C_0]rho),cal(C))([x:={}]t_0)(Sigma') \
sem(S capt C)_rho &= sem(S)_(rho,sem(C)_rho) \
sem(exists c. T)_rho &=
  fun t. fun Sigma.
    exists cal(C), sem(T)_([c:=cal(C)]rho) (t)(Sigma) \
sem(E)^e_(rho,cal(C)) &= fun t. fun Sigma.
  Sigma | t ->>^cal(C) sem(E)_rho
$

Then, we need to define semantic typing for contexts $semctxtyp(Gamma, rho, Sigma)$.

$
semctxtyp([], rho, Sigma) &:= sans("True") \
semctxtyp((Gamma, x: S capt C), rho, Sigma) &:=
  sem(S)_(rho,sem(C)_rho) (x)(Sigma) and rho(x) = sem(C)_rho and semctxtyp(Gamma, rho, Sigma) \
semctxtyp((Gamma, X<:S), rho, Sigma) &:=
  (rho(X) => sem(S)_(rho,dot)) and semctxtyp(Gamma, rho, Sigma) \
semctxtyp((Gamma, c<:B), rho, Sigma) &:=
  (rho(c) subset.eq sem(B)_rho) and semctxtyp(Gamma, rho, Sigma) \
$

Finally, we can define semantic typing:
$
semtyp(C, Gamma, t, T) :=
  forall rho forall Sigma,
    semctxtyp(Gamma, rho, Sigma) ->
    sem(T)_rho^e (t)(Sigma)
$

#theorem("Fundamental Theorem of Semantic Type Soundness")[
  If $typ(C, Gamma, t, T)$ then $semtyp(C, Gamma, t, T)$.
  That is, syntactic typing implies semantic typing.
] <thm:fundamental>
