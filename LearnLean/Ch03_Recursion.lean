/-!
# Chapter 3 — Lists, Recursion, and Why Lean Refuses to Loop

Lean is **total**: every function must be proven to terminate. There is no
`while (true)`. This sounds like a straitjacket. It's actually the price of
admission for the thing that makes Lean special — if functions could loop
forever, then "a proof" could loop forever, and a non-terminating proof
proves nothing.

So: Lean accepts recursion it can *see* shrinking. This chapter is about
learning to write recursion in a shape Lean believes.
-/

namespace Ch03

/-! ## 1. `List` is just an inductive type

  inductive List (α : Type) where
    | nil
    | cons (head : α) (tail : List α)

`[1, 2, 3]` is sugar for `1 :: 2 :: 3 :: []`, and `::` is `cons`.
The `α` makes it **polymorphic**: one definition, works for any element type.
-/

#print List

#eval [1, 2, 3]
#eval 1 :: 2 :: 3 :: []          -- identical
#eval ([] : List Nat)

#check [1, 2, 3]                 -- List Nat
#check ["a", "b"]                -- List String

/-! ## 2. Recursion over lists: always the same two cases -/

def length : List α → Nat
  | []      => 0
  | _ :: t  => 1 + length t

#eval length [10, 20, 30]

/-
The recursive call is on `t`, which is *structurally smaller* than `_ :: t`.
Lean sees this and is satisfied. This is called **structural recursion**.
-/

def sum : List Nat → Nat
  | []     => 0
  | h :: t => h + sum t

#eval sum [1, 2, 3, 4, 5]

/-- Notice this one takes a *function* as an argument. -/
def map (f : α → β) : List α → List β
  | []     => []
  | h :: t => f h :: map f t

#eval map (· * 10) [1, 2, 3]
#eval map toString [1, 2, 3]

/-! ## 3. When Lean says no

Uncomment the block below and read the error. Lean cannot see `n` getting
smaller — because it isn't.

```
def collatz (n : Nat) : Nat :=
  if n <= 1 then 0
  else if n % 2 == 0 then 1 + collatz (n / 2)
  else 1 + collatz (3 * n + 1)
```

The Collatz conjecture is *unproven mathematics*. Lean is right to refuse:
nobody knows whether this terminates. That's a remarkable error message to
get from a compiler.

Escape hatches exist when you need them:
  * `termination_by` + `decreasing_by` — prove termination yourself
  * `partial def` — opt out of totality (the function becomes opaque to proofs)
-/

/-- A recursion Lean can't see structurally, rescued by an explicit measure.
`termination_by` names the quantity that shrinks; `decreasing_by` proves it. -/
def halveDown : Nat → List Nat
  | 0 => []
  | n + 1 => (n + 1) :: halveDown ((n + 1) / 2)
termination_by n => n
decreasing_by omega

#eval halveDown 100

/-! ## 4. Fold — recursion, packaged

Almost every list function you'll ever write is a fold in disguise. -/

def foldr (f : α → β → β) (init : β) : List α → β
  | []     => init
  | h :: t => f h (foldr f init t)

#eval foldr (· + ·) 0 [1, 2, 3, 4]        -- sum
#eval foldr (· * ·) 1 [1, 2, 3, 4]        -- product
#eval foldr (fun _ n => n + 1) 0 [7, 8]   -- length

/-
Read `foldr f init [a, b, c]` as literally replacing the constructors:

    a :: (b :: (c :: []))
    a `f` (b `f` (c `f` init))

A fold is "swap every `::` for `f`, and `[]` for `init`". Once you see it,
you can't unsee it.
-/

/-!
## Exercises

Rule for this chapter: **no library functions**. Write the recursion yourself.
That's the whole point.
-/

/-- **3.1** — Reverse a list. The obvious solution is quadratic; that's fine
for now. Hint: `xs ++ ys` appends. -/
def reverse : List α → List α
  | [] => []
  | h :: t => reverse t ++ [h]

#guard reverse [1, 2, 3] == [3, 2, 1]
#guard reverse ([] : List Nat) == []
#guard reverse ["a"] == ["a"]

/-- **3.2** — Keep only the elements satisfying `p`. -/
def filter (p : α → Bool) : List α → List α
  | [] => []
  | h :: t => if p h then h :: filter p t else filter p t

#guard filter (· % 2 == 0) [1, 2, 3, 4, 5, 6] == [2, 4, 6]
#guard filter (fun _ => false) [1, 2, 3] == []

/-- **3.3** — The largest element, or `none` for an empty list.
`Option α` is either `none` or `some x` — Lean's null-safety. -/
def maximum? : List Nat → Option Nat
  | [] => none
  | h :: t =>
    match maximum? t with
      | none => h
      | some m => if h > m then h else m

#guard maximum? [3, 1, 4, 1, 5] == some 5
#guard maximum? [] == none
#guard maximum? [7] == some 7
#guard maximum? [7, 7] == some 7

/-- **3.4** — Zip two lists into pairs, stopping at the shorter one.
You'll need to match on *both* arguments at once: `| h1 :: t1, h2 :: t2 => ...` -/
def zip : List α → List β → List (α × β)
  | _, _ => sorry

#guard zip [1, 2, 3] ["a", "b"] == [(1, "a"), (2, "b")]
#guard zip ([] : List Nat) ["x"] == []

/-- **3.5** — `take n xs` returns the first `n` elements.
Which argument shrinks here? Match on both. -/
def take : Nat → List α → List α
  | _, _ => sorry

#guard take 2 [1, 2, 3, 4] == [1, 2]
#guard take 0 [1, 2, 3] == []
#guard take 99 [1, 2] == [1, 2]

/-- **3.6** — Insert `x` into an already-sorted list, keeping it sorted. -/
def insert (x : Nat) : List Nat → List Nat
  | _ => sorry

#guard insert 3 [1, 2, 4, 5] == [1, 2, 3, 4, 5]
#guard insert 0 [1, 2] == [0, 1, 2]
#guard insert 9 [1, 2] == [1, 2, 9]

/-- **3.7** — Insertion sort, built on `insert`. Two lines. -/
def isort : List Nat → List Nat
  | _ => sorry

#guard isort [3, 1, 4, 1, 5, 9, 2, 6] == [1, 1, 2, 3, 4, 5, 6, 9]
#guard isort [] == []

/-- **3.8** — Now express `map` as a `foldr`. No explicit recursion allowed —
the body should be a single call to `foldr`. -/
def mapViaFold (f : α → β) (xs : List α) : List β :=
  sorry

#guard mapViaFold (· + 1) [1, 2, 3] == [2, 3, 4]

/-- **3.9** — And `reverse` as a `foldr`. This one is a genuine puzzle.
What do you have to fold *into*? -/
def reverseViaFold (xs : List α) : List α :=
  sorry

#guard reverseViaFold [1, 2, 3] == [3, 2, 1]

/-- **3.10** — Fast reverse, using an **accumulator**. This runs in linear
time instead of quadratic. The trick: carry the answer-so-far downward
instead of building it up on the way out.
Fill in the helper; `reverseFast` is written for you. -/
def revGo : List α → List α → List α
  | _, _ => sorry

def reverseFast (xs : List α) : List α := revGo xs []

#guard reverseFast [1, 2, 3, 4] == [4, 3, 2, 1]
#guard reverseFast ([] : List Nat) == []

/-! ## Playground

  * `#eval (List.range 20).filter (· % 3 == 0)` — the real library is rich.
    Type `List.` and pause to see autocomplete; it's a good way to browse.
  * Write `flatten : List (List α) → List α`.
  * Write `mergeSort`. It needs `termination_by` — a good fight to pick.
  * Curiosity: what does `#eval length (List.range 100000)` do? And
    `#eval sum (List.range 100000)`? One of these may blow the stack. Why?
-/

#eval (List.range 20).filter (· % 3 == 0)

end Ch03
