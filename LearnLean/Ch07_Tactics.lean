/-!
# Chapter 7 — Tactics: Writing Proofs Backwards

Chapter 6 built proofs by hand, as terms. That works, and it's honest, but
past a certain size it's like writing assembly.

A **tactic** is a program that builds a proof term for you. `by` switches
into tactic mode; inside, you manipulate a **goal state** until nothing is
left. Lean assembles the term behind your back.

**The single most important habit in this chapter**: put your cursor on
*each line inside a `by` block* and read the InfoView. It shows you the
hypotheses you have and the goal you owe. Tactic proofs are unreadable
otherwise — and completely readable once you're watching the state.

Companion applet: `applets/tactic-state.html`.
-/

namespace Ch07

variable (P Q R : Prop)

/-! ## 1. The goal state

A goal looks like this:

    P Q : Prop
    hp : P
    ⊢ Q ∧ P

Everything above the `⊢` is what you *have*. Below it is what you *owe*.
Every tactic either changes what you owe, or gives you something new to
have.
-/

/-! ## 2. The starter kit -/

/-- `intro` — move a `→` or `∀` from the goal into your hypotheses.
It's the tactic version of `fun`. -/
example : P → P := by
  intro hp
  -- state now:  hp : P ⊢ P
  exact hp

/-- `exact` — "this term is exactly the proof". The bridge back to Ch. 6. -/
example : P → Q → P := by
  intro hp _
  exact hp

/-- `apply` — work backwards through an implication. -/
example (h : P → Q) : P → Q := by
  intro hp
  apply h        -- goal was Q; h : P → Q; so now the goal is P
  exact hp

/-- `constructor` — split an `∧` (or any single-constructor goal) into parts. -/
example (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp     -- the `·` focuses on one goal. Type it as \.
  · exact hq

/-- `cases` — destructure a hypothesis. The tactic version of `match`. -/
example : P ∧ Q → Q ∧ P := by
  intro h
  cases h with
  | intro hp hq => exact ⟨hq, hp⟩

/-- `rcases`-style pattern intro works directly in `intro` too: -/
example : P ∧ Q → Q ∧ P := by
  intro ⟨hp, hq⟩
  exact ⟨hq, hp⟩

/-- `left` / `right` — choose a side of an `∨` goal. -/
example (hp : P) : P ∨ Q := by
  left
  exact hp

/-- Case analysis on an `∨` hypothesis. -/
example : P ∨ Q → Q ∨ P := by
  intro h
  cases h with
  | inl hp => right; exact hp
  | inr hq => left; exact hq

/-! ## 3. The workhorses for arithmetic and data -/

/-- `rfl` — both sides compute to the same value. -/
example : 2 + 2 = 4 := by rfl

/-- `decide` — the proposition is decidable, so just run the decision procedure. -/
example : 7 % 3 = 1 := by decide

/-- `simp` — rewrite with the simp set until nothing changes. -/
example (xs : List Nat) : (xs ++ []).length = xs.length := by simp

/-- `omega` — a complete decision procedure for linear arithmetic over
`Nat` and `Int`. Astonishingly useful; reach for it constantly. -/
example (a b : Nat) (h : a + 2 = b) : b - a = 2 := by omega

example (n : Nat) : n < n + 1 := by omega

/-! ## 4. `induction` — the tactic that earns its keep

For any inductive type, `induction` gives you one goal per constructor,
with an induction hypothesis for each recursive field. -/

theorem add_zero' (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    -- ih : k + 0 = k
    simp

theorem zero_add' (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp

/-
Interesting asymmetry: `n + 0 = n` is true by `rfl` alone (Lean's `+`
recurses on the *second* argument, so `n + 0` reduces immediately), but
`0 + n = n` genuinely needs induction. The definition you chose determines
which facts are free and which cost work. This is a real and recurring
theme in formalization.
-/

theorem length_append (xs ys : List α) :
    (xs ++ ys).length = xs.length + ys.length := by
  induction xs with
  | nil => simp
  | cons h t ih => simp [ih]; omega

/-! ## 5. `calc` — chained reasoning that reads like a blackboard -/

example (a b : Nat) (h1 : a = b) (h2 : b = 5) : a + 1 = 6 := by
  calc a + 1 = b + 1 := by rw [h1]
    _ = 5 + 1 := by rw [h2]
    _ = 6 := by rfl

/-- `rw` — rewrite the goal using an equation, left-to-right. -/
example (a b : Nat) (h : a = b) : a + a = b + b := by
  rw [h]

/-! ## 6. Tactics for when you are stuck

  * `exact?`      — searches the library for a term that closes the goal
  * `apply?`      — same, but for backwards steps
  * `simp?`       — shows you which lemmas `simp` used
  * `decide`      — try it on anything finite
  * `omega`       — try it on anything about `Nat`/`Int` arithmetic
  * `grind`       — a strong general-purpose finisher, worth trying
  * `sorry`       — admit the goal and move on; come back later

Uncomment and run this to watch `exact?` shop for a lemma: -/

-- example (n : Nat) : 0 ≤ n := by exact?

/-!
## Exercises

Same feedback rule as Chapter 6: the yellow **"declaration uses `sorry`"**
warning is your red light. Prove it away.

Try to use tactics here even where you could write a term — the goal is to
build the reflex of reading the goal state.
-/

/-- **7.1** -/
example : P ∧ Q → P := by
  sorry

/-- **7.2** -/
example : P → Q → P ∧ Q := by
  sorry

/-- **7.3** — you'll need `intro`, `cases`, and both `left`/`right`. -/
example : (P ∨ Q) → (Q ∨ P) := by
  sorry

/-- **7.4** — distributing over a disjunction. -/
example : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  sorry

/-- **7.5** — `omega` alone will do it. Confirm that it does, then try
proving it without `omega` to appreciate the tactic. -/
example (n : Nat) (h : n > 3) : n * 2 > 6 := by
  sorry

/-- **7.6** — induction on `n`. -/
theorem add_succ_comm (n m : Nat) : n + (m + 1) = (n + 1) + m := by
  sorry

/-- **7.7** — the sum 0 + 1 + ... + n, times 2, is n * (n + 1).
Harder than it looks: `omega` handles *linear* arithmetic, and the goal
here is quadratic. Sketch for the `succ` case:
  * `show 2 * ((k + 1) + sumTo k) = (k + 1) * (k + 1 + 1)` to state the
    unfolded goal explicitly,
  * `rw [Nat.mul_add, ih]` to use the induction hypothesis,
  * then `simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm]` to normalize the
    products, and `omega` to finish.
Or skip all that and try `grind [sumTo]`. Do both — the contrast is the
lesson. -/
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  sorry

/-- **7.8** — a list fact. Induct on `xs`; `simp` handles most of it. -/
theorem map_length (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  sorry

/-- **7.9** — appending nothing changes nothing. -/
theorem append_nil (xs : List α) : xs ++ [] = xs := by
  sorry

/-- **7.10** — associativity of append. -/
theorem append_assoc (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  sorry

/-! ## Playground

  * Write the same proof twice — once in term mode, once in tactic mode —
    then `#print` both. Sometimes the tactic proof is *enormous*. That's
    fine; nobody reads it, the kernel does.
  * `set_option trace.Meta.Tactic.simp true in` before a `simp` shows you
    every rewrite it performed. Educational, and occasionally horrifying.
  * How far can `decide` go? `example : ∀ n < 100, n * n ≥ n := by decide`
  * Try `grind` on the exercises above. Where does it succeed instantly,
    and where does it fail?
-/

end Ch07
