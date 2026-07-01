import Semantic.CoreCapybara.Semantics.Heap

/-!
# Prototype: world-parametrized step-indexed store typing (Ahmed/Iris style)

## SUPERSEDED (Phase 1) — see `Denotation/StepIndexedFlat.lean`

Validating the keystone here surfaced a genuine obstruction: the dependent `World : Nat → Type`
family below needs a *content-fabricating* `extend : World n → World (n+1)`, whose canonical
padding at the bottom level would have to be simultaneously `True` (to satisfy a cell's
agreement clause) and structural (to match e.g. `unit`) — impossible.  So the naive coherence
`val_denot T (n+1) (extend w) ↔ val_denot T n w` is FALSE at the index boundary; `restrict`
of a stored relation intrinsically needs `extend` to lift its argument, so downward-closure
for nested cells cannot be proved with this shape.

The corrected model keeps the world **flat** and stratifies with an index *truncation*
(`approx`) instead of a dependent tower — no `extend`, no boundary.  It is built, with the
keystone (non-expansiveness) and both read/write soundness proven `sorryAx`-free, in
`Denotation/StepIndexedFlat.lean`.  This file is kept only as the record of the dead end.

Scratch file, imported by nothing.  Goal: validate that a store typing whose stored
relations are **world-parametrized** (carry the store typing they will be evaluated against,
stratified by the step index to break the circularity) supports BOTH read and write of
higher-order cell content — the thing the frozen-relation `KripkeModel.lean` cannot do.

## The circularity and how the index breaks it

A faithful cell relation must store the content type's *denotation as a world-parametrized
object* `StoreTyping → Memory → Exp → Prop`, so that the cell's `R ≈ val_denot Tc` is a
world-STABLE comparison (preserved when the store grows, because the stored `R` is preserved
verbatim and the comparison ranges over all worlds).  But `StoreTyping := Loc → Option (… ↦
StoreTyping → …)` is non-strictly-positive.  The step index stratifies it: a relation stored
at index `n+1` is parametrized by worlds at index `n` only.

`World n` = store typing usable at `n` further observation steps; a relation it stores is
parametrized by `World n` worlds (one step down).

## restrict / extend form a retraction (NON-degenerate)

`restrict ∘ extend = id` (valid induction at the lower index), but `extend ∘ restrict ≠ id`
(that would recurse at the *same* index — not well-founded).  So `extend` is a genuine
section and `restrict` a retraction: `World (n+1)` is strictly larger than `World n`; the
worlds do NOT collapse.  This is exactly the step-index stratification we want.

The crux remaining lemma is **coherence** `val_denot T (m+1) (extend w) ↔ val_denot T m w`
(non-expansiveness of `val_denot`), which feeds **downward-closure**
`val_denot T (n+1) w → val_denot T n (restrict w)`, which is what makes **write** sound.
-/

namespace CoreCapybara
namespace StepIndexedProto

/-- The step-indexed world.  `World (n+1)` maps each location to a relation parametrized by
worlds at the strictly lower index `n` (`▷`, the later-step).  `World 0` is trivial (no
further steps can be observed). -/
def World : Nat → Type
  | 0 => Unit
  | n + 1 => Nat → Option (World n → Memory → Exp {} → Prop)

/-- A semantic relation usable at index `n`: parametrized by an `n`-world (the world it will
be checked against), a memory, and an expression. -/
abbrev SemRel (n : Nat) : Type := World n → Memory → Exp {} → Prop

/-- Look up a location's stored relation in an `(n+1)`-world. -/
def World.lookup {n : Nat} (w : World (n + 1)) (l : Nat) : Option (SemRel n) :=
  w l

/- **Restriction / extension between adjacent index levels.**  `restrict` drops a world one
observation step (forgetting the top level of nesting); `extend` pads it back with a
canonical lower approximation.  Each location's stored relation is reindexed by precomposing
with the dual operation.  Mutually recursive, decreasing on the index. -/
mutual
def World.restrict : {n : Nat} → World (n + 1) → World n
  | 0, _ => ()
  | _ + 1, w => fun l => (w l).map (fun f w'' => f (World.extend w''))
def World.extend : {n : Nat} → World n → World (n + 1)
  | 0, _ => fun _ => none
  | _ + 1, w => fun l => (w l).map (fun g w''' => g (World.restrict w'''))
end

/-- **The world-parametrized step-indexed value relation.**  At index `0` nothing can be
observed (`True`).  The `cell` case at index `n+1` reads the location's stored relation
`R : SemRel n` and asserts it agrees with `val_denot Tc n` over **all** `n`-worlds — a
comparison independent of the *outer* world, which is what makes the cell relation monotone
for free.  Recursion strictly decreases the index (the `▷` step). -/
def val_denot : (T : Ty .capt {}) → (n : Nat) → World n → Memory → Exp {} → Prop
  | .unit, _, _, m, e => resolve m.heap e = some .unit
  | .cell _ _, 0, _, m, e =>
      ∃ l n0 ℓ0, e = .var (.free l) ∧ m.lookup l = some (.capability (.mcell n0 ℓ0))
  | .cell _ Tc, n + 1, w, m, e =>
      ∃ l n0 ℓ0 R, e = .var (.free l) ∧
        m.lookup l = some (.capability (.mcell n0 ℓ0)) ∧
        w l = some R ∧
        ∀ (w' : World n) (m' : Memory) (e' : Exp {}),
          R w' m' e' ↔ val_denot Tc n w' m' e'
  | _, _, _, _, _ => True
termination_by _ n => n

/-- `restrict` retracts `extend`: padding a world then truncating recovers it.  (The other
composite `extend ∘ restrict` is NOT the identity — that is what keeps the levels distinct.) -/
theorem World.restrict_extend : ∀ {n : Nat} (w : World n), World.restrict (World.extend w) = w
  | 0, w => rfl
  | _ + 1, w => by
    funext l
    change ((w l).map (fun g w''' => g (World.restrict w'''))).map
      (fun f w'' => f (World.extend w'')) = w l
    rw [Option.map_map]
    cases hwl : w l with
    | none => rfl
    | some g =>
      simp only [Option.map_some, Function.comp]
      congr 1
      funext w''
      rw [World.restrict_extend w'']

end StepIndexedProto
end CoreCapybara
