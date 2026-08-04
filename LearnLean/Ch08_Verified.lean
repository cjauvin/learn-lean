/-!
# Chapter 8 — Verified Programming: Where the Two Halves Meet

You now have both halves. Chapters 1–5: writing programs. Chapters 6–7:
writing proofs. This chapter is the reason anyone bothers with Lean —
because in Lean these are the *same activity*, you can write a program and
then prove it does what you claimed, in the same file, checked by the same
compiler.

Three escalating techniques, in order of how much they change your code:

1. **Prove properties afterwards** — code unchanged, theorems added.
2. **Demand proofs as arguments** — the caller must justify the call.
3. **Put the invariant in the type** — illegal states stop existing.
-/

namespace Ch08

/-! ## 1. Prove properties afterwards

Your code doesn't change at all. You just start making claims about it,
and the compiler starts checking them. -/

def double (n : Nat) : Nat := 2 * n

theorem double_even (n : Nat) : double n % 2 = 0 := by
  simp [double, Nat.mul_mod_right]

theorem double_mono (a b : Nat) (h : a ≤ b) : double a ≤ double b := by
  simp [double]; omega

/-- A property of a function you wrote in Chapter 3. -/
def mySum : List Nat → Nat
  | [] => 0
  | h :: t => h + mySum t

theorem sum_append (xs ys : List Nat) :
    mySum (xs ++ ys) = mySum xs + mySum ys := by
  induction xs with
  | nil => simp [mySum]
  | cons h t ih => simp [mySum, ih]; omega

/-- Map fusion — a real compiler optimization, proven correct in three lines.
Traversing twice equals traversing once with the composed function. -/
theorem map_map' (f : α → β) (g : β → γ) (xs : List α) :
    (xs.map f).map g = xs.map (fun x => g (f x)) := by
  induction xs with
  | nil => rfl
  | cons h t ih => simp [ih]

/-
Think about what that last theorem is. It's a rewrite rule a compiler would
love to apply, and you have just *proved it sound* rather than hoping. This
is what "verified compiler" means, scaled up.
-/

/-! ## 2. Demand proofs as arguments

Sometimes a function only makes sense under a condition. Instead of
returning `Option` and making every caller handle a case that can't happen,
demand the condition up front — as a *proof argument*. -/

def divExact (a b : Nat) (_h : b ≠ 0) : Nat := a / b

-- #eval divExact 10 0 ...   ← you cannot even write this call.
#eval divExact 10 2 (by decide)

/-
`(by decide)` is a proof, supplied inline, that `2 ≠ 0`. The proof is erased
at runtime — it costs nothing. It exists purely to stop you at compile time.

Contrast with the `Option` approach from Chapter 5. Both are valid designs.
`Option` pushes the burden to the caller's *runtime*; a proof argument
pushes it to the caller's *compile time*.
-/

/-- The head of a list, given a proof that it isn't empty. Total, no `Option`. -/
def firstOf (xs : List α) (h : xs ≠ []) : α :=
  match xs, h with
  | x :: _, _ => x

#eval firstOf [10, 20, 30] (by decide)

/-! ## 3. Put the invariant in the type

The strongest move: make the bad value impossible to construct. -/

-- `Fin n` is "a natural number, together with a proof it is `< n`".
-- Out-of-bounds indexing becomes a type error.
#check (⟨2, by decide⟩ : Fin 5)
#eval ([10, 20, 30, 40, 50].get ⟨2, by decide⟩)

/-- A subtype: `{ x : α // p x }` is "an `x` bundled with a proof of `p x`". -/
def Positive := { n : Nat // n > 0 }

def three : Positive := ⟨3, by decide⟩

#eval three.val

/-- Now division by a `Positive` needs no check *and* no proof argument —
the proof travelled inside the value. -/
def safeDivide (a : Nat) (b : Positive) : Nat := a / b.val

#eval safeDivide 100 three

/-- Length-indexed lists. The type records how many elements there are, so
a length mismatch is caught by the type checker. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

namespace Vec

def toList : Vec α n → List α
  | .nil => []
  | .cons h t => h :: toList t

/-- `zip` on `Vec` needs no "what if the lengths differ" case — the shared
`n` in the signature makes that unrepresentable. Compare Exercise 3.4. -/
def zip : Vec α n → Vec β n → Vec (α × β) n
  | .nil, .nil => .nil
  | .cons a as, .cons b bs => .cons (a, b) (zip as bs)

def ofThree (a b c : α) : Vec α 3 := .cons a (.cons b (.cons c .nil))

#eval (zip (ofThree 1 2 3) (ofThree "a" "b" "c")).toList

end Vec

/-
Notice what did *not* happen in `Vec.zip`: no `| .nil, .cons _ _ => ...`
branch, and Lean did not complain about a missing case. It knows those
cases are impossible, because the index `n` cannot be both `0` and `k+1`.
The type did the work.
-/

/-!
## Exercises

This is the boss level. Some of these are genuinely hard — that is the
point. If one resists for more than twenty minutes, `sorry` it, move on,
and come back. That is exactly how real formalization goes.

Useful moves: `induction xs with | nil => ... | cons h t ih => ...`,
`simp [ih]`, `omega`, `rw [...]`, `cases`, `split`.
-/

/-! ### Warm-up: properties of your own functions -/

def myLength : List α → Nat
  | [] => 0
  | _ :: t => 1 + myLength t

def myAppend : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: myAppend xs ys

/-- **8.1** — Appending nothing changes nothing. -/
theorem append_nil (xs : List α) : myAppend xs [] = xs := by
  sorry

/-- **8.2** — Lengths add. -/
theorem length_append (xs ys : List α) :
    myLength (myAppend xs ys) = myLength xs + myLength ys := by
  sorry

/-- **8.3** — Append is associative. -/
theorem append_assoc (xs ys zs : List α) :
    myAppend (myAppend xs ys) zs = myAppend xs (myAppend ys zs) := by
  sorry

/-! ### The classic: reverse is an involution

This needs a *helper lemma* first. That's the real lesson here — most
theorems of interest are not provable directly, and finding the right
lemma to prove first is the actual skill. -/

def myReverse : List α → List α
  | [] => []
  | x :: xs => myAppend (myReverse xs) [x]

/-- **8.4** — How `reverse` interacts with `append`. You'll need 8.1 and 8.3.
Prove this one first; 8.5 is impossible without it. -/
theorem reverse_append (xs ys : List α) :
    myReverse (myAppend xs ys) = myAppend (myReverse ys) (myReverse xs) := by
  sorry

/-- **8.5** — Reversing twice gets you back. Use 8.4 in the `cons` case. -/
theorem reverse_reverse (xs : List α) : myReverse (myReverse xs) = xs := by
  sorry

/-! ### Specifying a sort

Now the full job: define what "sorted" *means*, then prove the algorithm
achieves it. This is the shape of every real verification effort — the
specification is a thing you write, and getting it right is half the work. -/

/-
A note on the name: plain `insert` collides with core Lean's
`Insert.insert`, and the ambiguity quietly breaks `simp [insert]`. Naming
is load-bearing here in a way it isn't in most languages.
-/
def insertInto (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertInto x ys

def isort : List Nat → List Nat
  | [] => []
  | x :: xs => insertInto x (isort xs)

#eval isort [5, 2, 8, 1]

/-- "`x` is ≤ every element of the list." A helper predicate — and choosing
to introduce it is the single decision that makes the whole proof tractable. -/
def LeAll (x : Nat) : List Nat → Prop
  | [] => True
  | y :: ys => x ≤ y ∧ LeAll x ys

/-- The specification. -/
def Sorted : List Nat → Prop
  | [] => True
  | x :: xs => LeAll x xs ∧ Sorted xs

/-- **8.6** — `LeAll` is downward-closed: if `x ≤ y` and `y` bounds the
whole list, then so does `x`. Induction on `ys`; `omega` for the arithmetic,
`trivial` closes a goal of `True`. -/
theorem le_all_trans (x y : Nat) (ys : List Nat) (hxy : x ≤ y) (h : LeAll y ys) :
    LeAll x ys := by
  sorry

/-- **8.7** — Inserting an element that `y` already bounds keeps `y` a bound.
Induction on `xs`. Use `simp only [insertInto]` to unfold one step, then
`split` to handle the `if`. -/
theorem le_all_insertInto (y x : Nat) (xs : List Nat) (hyx : y ≤ x)
    (h : LeAll y xs) : LeAll y (insertInto x xs) := by
  sorry

/-- **8.8** — The main event: inserting into a sorted list keeps it sorted.
The two branches of the `if` need 8.6 and 8.7 respectively. `rename_i hxy`
grabs the hypothesis `split` introduced. -/
theorem insertInto_sorted (x : Nat) (xs : List Nat) (h : Sorted xs) :
    Sorted (insertInto x xs) := by
  sorry

/-- **8.9** — Therefore insertion sort sorts. Given 8.8, this is three lines.
You have now proved a sorting algorithm correct. -/
theorem isort_sorted (xs : List Nat) : Sorted (isort xs) := by
  sorry

/-- **8.10** — Sorting preserves length. (A weak version of "it's a
permutation of the input" — the full statement needs multisets. Worth
noticing: `isort_sorted` alone does *not* prove the sort is correct.
`fun _ => []` also produces sorted output.) -/
theorem insertInto_length (x : Nat) (xs : List Nat) :
    (insertInto x xs).length = xs.length + 1 := by
  sorry

/-- **8.11** — ...and therefore so does `isort`. -/
theorem isort_length (xs : List Nat) : (isort xs).length = xs.length := by
  sorry

/-! ### Dependent types -/

/-- **8.12** — `map` for length-indexed vectors. Note that the type
*guarantees* your implementation preserves length — there's no way to write
a buggy one that compiles. -/
def Vec.map (f : α → β) : Vec α n → Vec β n :=
  sorry

#guard (Vec.map (· * 2) (Vec.ofThree 1 2 3)).toList == [2, 4, 6]

/-- **8.13** — Safe indexing into a `Vec` with a `Fin`. No bounds check
at runtime, no `Option`, no possibility of failure.
Hint: match on both the vector and the `Fin`; `Fin` has patterns
`⟨0, _⟩` and `⟨i + 1, hi⟩`. For the recursive call you must supply a proof
that `i < n` — `by omega` will find it. -/
def Vec.get : Vec α n → Fin n → α :=
  sorry

#guard Vec.get (Vec.ofThree 10 20 30) ⟨1, by decide⟩ == 20

/-! ## Playground — where to go next

You have the whole language now. Directions, pick by taste:

  * **Mathlib.** Add it and the mathematical universe opens up:
    `lake env lean` gets slower, but `linarith`, `ring`, `field_simp`,
    `nlinarith` and 1.5M lines of mathematics arrive. See README.md.
  * **Verified data structures.** Red-black trees with the invariants in
    the type. Balanced-ness becomes unrepresentable-if-wrong.
  * **A verified interpreter.** Extend Chapter 2's `Expr`, write a compiler
    to a stack machine, and prove `run (compile e) = eval e`. This is a
    genuinely beautiful ~150-line project and a rite of passage.
  * **Metaprogramming.** `macro`, `elab`, custom syntax categories. Lean is
    written in Lean; you can extend the parser from inside your file.
  * **Natural Number Game** (online) if you want more proof drilling.
  * **Theorem Proving in Lean 4** and **Functional Programming in Lean** —
    the two canonical books, both free online. See README.md for links.
-/

end Ch08
