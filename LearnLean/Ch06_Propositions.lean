/-!
# Chapter 6 — Propositions Are Types, Proofs Are Programs

Here is the idea the whole system rests on, and you already know enough to
see it. Everything in this chapter is a rearrangement of things you learned
in Chapters 1–5. **You are not learning a new language. You are noticing
that the language you learned was already a proof language.**

The correspondence (Curry–Howard):

| Logic                   | Programming                        |
|-------------------------|------------------------------------|
| proposition `P`         | a type                             |
| proof of `P`            | a value of that type               |
| `P → Q`                 | function type                      |
| `P ∧ Q`                 | pair / structure                   |
| `P ∨ Q`                 | sum type (inductive, 2 ctors)      |
| `True`                  | `Unit` (one trivial value)         |
| `False`                 | `Empty` (no values at all)         |
| `¬P`                    | `P → Empty`                        |
| `∀ x, P x`              | dependent function                 |
| `∃ x, P x`              | dependent pair                     |

Proving something = constructing a value. That's it. That's the trick.

There is a companion applet for this chapter:
`applets/curry-howard.html` — open it in a browser alongside this file.
-/

namespace Ch06

/-! ## 1. A proposition is a type -/

#check (2 + 2 = 4)            -- Prop  ← this is a *type*, not a Bool!
#check (2 + 2 = 5)            -- also Prop. Being false doesn't stop it existing.

/-
`2 + 2 = 5` is a perfectly good type. It just happens to have no values.
"Proving it false" means "showing the type is uninhabited".
-/

#check Prop                   -- Type
#check True
#check False

/-! ## 2. A proof is a term of that type -/

theorem two_plus_two : 2 + 2 = 4 := rfl

#check two_plus_two           -- 2 + 2 = 4

/-
`rfl` is a *value* — the proof of reflexivity, `a = a`. Lean checks that
both sides reduce to the same thing, then accepts `rfl` as inhabiting the
type `2 + 2 = 4`. Nothing else happened. No solver, no search.
-/

#print two_plus_two

/-
`theorem` and `def` are the same command. Really.
(The `set_option` just silences a style linter that would otherwise nag you
to write `theorem` here — which rather proves the point.)
-/
set_option linter.all false in
def two_plus_two' : 2 + 2 = 4 := rfl

/-
The only difference: `theorem` marks the result irrelevant for compilation
(proofs get erased), and Lean won't unfold it during evaluation. Same
underlying mechanism.
-/

/-! ## 3. Implication is just a function -/

variable (P Q R : Prop)

/-- The identity function, retyped. Compare: `def id (x : α) : α := x`. -/
theorem self_implies : P → P :=
  fun h => h

/-- Constant function, retyped. -/
theorem imp_intro : P → (Q → P) :=
  fun hp => fun _ => hp

/-- Function composition, retyped. This is *modus ponens chaining*. -/
theorem imp_trans : (P → Q) → (Q → R) → (P → R) :=
  fun hpq hqr => fun hp => hqr (hpq hp)

/-
Stare at `imp_trans` for a moment. It is literally `∘`. You wrote this
function in Chapter 1 without knowing it was a theorem of propositional
logic.
-/

/-! ## 4. Conjunction is a pair -/

#print And                    -- structure And (a b : Prop) : Prop with left, right

theorem and_comm' : P ∧ Q → Q ∧ P :=
  fun h => ⟨h.right, h.left⟩

/-
`⟨_, _⟩` — the anonymous constructor from Chapter 4, on a structure whose
fields happen to be proofs. `h.left` is field access. Same syntax, same
meaning, and now it's logic.
-/

theorem and_assoc' : (P ∧ Q) ∧ R → P ∧ (Q ∧ R) :=
  fun h => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩

/-! ## 5. Disjunction is a sum type -/

#print Or                     -- inductive Or with inl, inr

theorem or_intro_left : P → P ∨ Q :=
  fun hp => Or.inl hp

/-- To *use* an `Or`, you must handle both cases — a pattern match. -/
theorem or_comm' : P ∨ Q → Q ∨ P :=
  fun h =>
    match h with
    | Or.inl hp => Or.inr hp
    | Or.inr hq => Or.inl hq

/-! ## 6. `False` and negation

`False` is an inductive type with **zero** constructors. Nothing can build
one. So if someone hands you a `False`, they've handed you an impossibility,
and you may conclude anything — that's `False.elim`. -/

#print False
#check @False.elim            -- False → C   (for *any* C)

-- `¬P` is *defined* as `P → False`. Not a primitive.
#print Not

theorem not_not_intro : P → ¬¬P :=
  fun hp => fun hnp => hnp hp

/-
Follow the types: `¬¬P` is `(P → False) → False`. So we take `hnp : P → False`,
and we have `hp : P`, so `hnp hp : False`. Done. Pure function application.
-/

theorem contradiction_implies_anything : P → ¬P → Q :=
  fun hp hnp => absurd hp hnp

/-! ## 7. `∀` is a dependent function, `∃` is a dependent pair -/

theorem forall_example : ∀ n : Nat, n + 0 = n :=
  fun _ => rfl

#check forall_example         -- ∀ (n : Nat), n + 0 = n

/-
Compare the type of a normal function: `Nat → Nat`. Here the *return type*
mentions the argument: `(n : Nat) → n + 0 = n`. That's all `∀` is —
Lean even lets you write it either way.
-/

theorem exists_example : ∃ n : Nat, n * n = 49 :=
  ⟨7, rfl⟩

/-
A proof of `∃ x, P x` is a pair: the witness, and the proof that it works.
Constructive logic has no "there exists but I can't tell you which".
-/

/-! ## 8. Prop vs Bool — a distinction that matters

`isEven 4` is a `Bool`: a value you can compute and branch on.
`4 % 2 = 0` is a `Prop`: a statement you can prove.
`decide` bridges them when the Prop is decidable. -/

#check (4 % 2 == 0)           -- Bool
#check (4 % 2 = 0)            -- Prop
#eval (4 % 2 == 0)            -- true
-- #eval (4 % 2 = 0)          -- error: can't evaluate a Prop

theorem four_is_even : 4 % 2 = 0 := by decide

/-!
## Exercises

**Term mode only** for this chapter — build the proof as a value, using
`fun`, `⟨_, _⟩`, `.left`, `.right`, `Or.inl`, `Or.inr`, and `match`.
No tactics yet; that's Chapter 7. The point is to feel that these are
programs.

Your feedback signal here is the yellow **"declaration uses `sorry`"**
warning. When it disappears, you've proven it.
-/

/-- **6.1** — Currying, as a theorem of logic. -/
theorem curry : (P ∧ Q → R) → (P → Q → R) :=
  sorry

/-- **6.2** — And uncurrying. -/
theorem uncurry : (P → Q → R) → (P ∧ Q → R) :=
  sorry

/-- **6.3** — Distribute a function over a conjunction. -/
theorem and_map : (P → Q) → (P ∧ R → Q ∧ R) :=
  sorry

/-- **6.4** — Case-analysis on the left of a disjunction. -/
theorem or_map : (P → Q) → (P ∨ R → Q ∨ R) :=
  sorry

/-- **6.5** — Eliminating a disjunction into a common conclusion.
This is "proof by cases", and it is a `match`. -/
theorem or_elim : (P → R) → (Q → R) → (P ∨ Q → R) :=
  sorry

/-- **6.6** — Contraposition. Remember `¬X` unfolds to `X → False`. -/
theorem contrapositive : (P → Q) → (¬Q → ¬P) :=
  sorry

/-- **6.7** — One half of De Morgan. (The other half needs classical logic —
try it and see where you get stuck. That's a real and famous wall.) -/
theorem demorgan : ¬P ∧ ¬Q → ¬(P ∨ Q) :=
  sorry

/-- **6.8** — From a contradiction, anything. Use `False.elim` or `absurd`. -/
theorem explosion : P ∧ ¬P → Q :=
  sorry

/-- **6.9** — A witness for an existential. -/
theorem exists_cube : ∃ n : Nat, n * n * n = 27 :=
  sorry

/-- **6.10** — Push a function under an existential. You'll need to
destructure the incoming pair — `fun ⟨w, hw⟩ => ...` works. -/
theorem exists_map (f : Nat → Nat) (p q : Nat → Prop)
    (h : ∀ n, p n → q (f n)) : (∃ n, p n) → (∃ m, q m) :=
  sorry

/-! ## Playground

  * Try to prove `¬¬P → P`. You will fail. This is **not** your fault:
    it's not provable constructively. Lean offers `Classical.byContradiction`
    as an axiom when you want it. `#check Classical.em`.
  * `#print axioms two_plus_two` — see exactly what a proof depends on.
    Now try `#print axioms` on a theorem you proved with `Classical.em`.
  * What is `Nat.le`? `#print Nat.le`. Ordering is an inductive type too.
  * `#check @Eq` — even equality is just an inductive family with one
    constructor, `rfl`. Everything is made of the same three ideas.
-/

#print axioms two_plus_two

end Ch06
