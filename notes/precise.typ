#import "@preview/ctheorems:1.1.3": *

#set page(margin: 0.4in, numbering: "1")
#set heading(numbering: "1.1")
// #set text(font: "CommitMono", weight: "regular", size: 9pt)
#show math.equation: set text(font: "Latin Modern Math", size: 11pt)
#show: thmrules

#let title = "Precisely Capless: An Effecty Take on Capture Checking"

#set document(
  title: title,
  author: "Yichen Xu"
)

#align(center)[
  #v(3em)
  #text(size: 17pt, weight: "bold")[
    #title
  ] \
  #v(1em)
  Yichen Xu\
  Autumn 2025
  #v(2em)
]

#let systemname(s) = text(font: "Latin Modern Sans 12", weight: "light", size: 12pt)[#s]
#let capt = move(dy: -0.26em)[#h(-0.4em) #text(size: 0.65em)[∧] #h(-0.4em)]
#let infrule(name, from, to) = $ #from / #to quad sans("(")sans(#name)sans(")") $
#let turnstile = text(size: 0.9em)[$tack.r$]
#let sturnstile = text(size: 0.9em)[$models$]
#let typ(cs, ctx, e, t) = $ #cs\; #ctx turnstile #e : #t $
#let wf(ctx, obj) = $ #ctx turnstile #obj sans("wf") $
#let subtyp(ctx, t1, t2) = $ #ctx turnstile #t1 <: #t2 $
#let pack(c, x) = $ lr(chevron.l #c, #x chevron.r) $
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
    $typ({}, Gamma, x, S capt {x})$,
  ),

  infrule(
    "sub",
    $typ(C_1, Gamma, e, T_1) quad wf(Gamma, C_2\, T_2) \
     subtyp(Gamma, T_1, T_2) quad subtyp(Gamma, C_1, C_2)$,
    $typ(C_2, Gamma, e, T_2)$,
  ),

  infrule(
    "unit", 
    $$,
    $typ({}, Gamma, (), "Unit")$,
  ),

  infrule(
    "abs",
    $typ(C, (Gamma, x: T), t, E) quad wf(Gamma, C)$,
    $typ({}, Gamma, lambda (x: T) t, ((x: T) -> E) capt C)$,
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
    $typ(C_f, Gamma, x thin y, [z:=x]E)$,
  ),

  infrule(
    "tapp",
    $typ(C, Gamma, x, ([X<:S] -> E) capt C_f)$,
    $typ(C_f, Gamma, x[S], [X:=S]E)$,
  ),

  infrule(
    "capp",
    $typ(C, Gamma, x, ([c<:B] -> E) capt C_f) quad
     subtyp(Gamma, C, B)$,
    $typ(C_f, Gamma, x[C], [c:=C]E)$,
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
