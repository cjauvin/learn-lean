/-!
# Chapter 5 — Failure, Effects, and `do`

Lean has no `null`, no exceptions, and no ambient mutable state. So how do
you write a program that can fail, or read a file, or count things?

You *return* the effect instead of performing it. `Option` says "might be
missing". `Except` says "might fail, with a reason". `IO` says "talks to the
world". And they all share one interface, which is where `do` comes in.
-/

namespace Ch05

/-! ## 1. `Option` — the honest null -/

def safeDiv (a b : Nat) : Option Nat :=
  if b == 0 then none else some (a / b)

#eval safeDiv 10 2
#eval safeDiv 10 0

/-
Now chain three of them. Written by hand, it's a staircase of matches: -/

def calcUgly (a b c : Nat) : Option Nat :=
  match safeDiv 100 a with
  | none => none
  | some x =>
    match safeDiv x b with
    | none => none
    | some y =>
      match safeDiv y c with
      | none => none
      | some z => some (z + 1)

#eval calcUgly 2 5 2

/-! ## 2. `do` — the same thing, unstaircased -/

def calcNice (a b c : Nat) : Option Nat := do
  let x ← safeDiv 100 a
  let y ← safeDiv x b
  let z ← safeDiv y c
  return z + 1

#eval calcNice 2 5 2
#eval calcNice 2 0 2          -- none: the whole chain short-circuits

/-
`let x ← e` means "run `e`; if it produced a value, bind it to `x`;
otherwise stop and propagate the failure." The `←` (type `\l`) is the
*only* new idea. `calcNice` and `calcUgly` compile to the same thing.

The plain `let x := e` (no arrow) is still ordinary binding, no effect.
-/

/-! ## 3. `Except` — failure that explains itself -/

inductive DivError where
  | divByZero
  | negativeInput (n : Int)
  deriving Repr

/-
Aside, and a nice callback to Chapter 4: core Lean gives `Except` no `BEq`
instance, so `#guard` on an `Except` won't compile. We just... add one.
Nothing in the standard library needs to know or be recompiled.
-/
instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

def checkedDiv (a b : Int) : Except DivError Int :=
  if b == 0 then .error .divByZero
  else if a < 0 then .error (.negativeInput a)
  else .ok (a / b)

#eval checkedDiv 10 2
#eval checkedDiv 10 0
#eval checkedDiv (-4) 2

/-- Identical `do` syntax, different monad. -/
def twoDivs (a b c : Int) : Except DivError Int := do
  let x ← checkedDiv a b
  let y ← checkedDiv x c
  return y

#eval twoDivs 100 5 2
#eval twoDivs 100 0 2

/-! ## 4. `IO` — actually doing something -/

def hello : IO Unit := do
  IO.println "Hello from inside IO."
  IO.println "This line runs second, genuinely."

#eval hello

def askAndDouble : IO Unit := do
  let now ← IO.monoMsNow
  IO.println s!"Milliseconds since boot: {now}"

#eval askAndDouble

/-
`#eval` on an `IO` action *runs* it. That makes the InfoView a real
scratchpad — you can print, read the clock, list a directory, all inline.
-/

/-! ## 5. Loops inside `do` -/

def countdown (n : Nat) : IO Unit := do
  for i in List.range n |>.reverse do
    IO.println s!"{i + 1}..."
  IO.println "Liftoff."

#eval countdown 3

/-- Mutable-looking state inside `do`. It's still pure underneath —
`mut` compiles to threading the value through. -/
def sumTo (n : Nat) : Nat := Id.run do
  let mut total := 0
  for i in List.range (n + 1) do
    total := total + i
  return total

#eval sumTo 100

/-
`Id.run` runs the trivial monad — meaning: "I want `do` notation and `mut`,
but no actual effects." This is how you write imperative-looking pure code
in Lean, and it's completely respectable. `sumTo` is a pure function; you
could prove theorems about it.
-/

/-! ## 6. What a monad actually is

Two operations. That's all. -/

#check @pure                  -- α → m α                    ("wrap a value")
#check @bind                  -- m α → (α → m β) → m β      ("then")

#eval (pure 5 : Option Nat)
#eval bind (some 5) (fun x => some (x + 1))
#eval some 5 >>= fun x => some (x + 1)     -- >>= is bind, type \>>=

/-
And `do` is *just* sugar for nested `bind`. Every monad you meet — Option,
Except, IO, State, parsers, probability distributions — is a different
answer to "what does 'then' mean here?"
-/

/-!
## Exercises
-/

/-- **5.1** — Look up a key in an association list. -/
def lookup (key : String) : List (String × Nat) → Option Nat
  | _ => sorry

#guard lookup "b" [("a", 1), ("b", 2)] == some 2
#guard lookup "z" [("a", 1), ("b", 2)] == none

/-- **5.2** — Given a name, look up the person's age *and* their city
(from two separate tables) and format them. Use `do`. -/
def ages : List (String × Nat) := [("ada", 36), ("alan", 41)]
def cities : List (String × Nat) := [("ada", 44), ("grace", 55)]

def profile (name : String) : Option String := do
  sorry

#guard profile "ada" == some "ada: 36 / 44"
#guard profile "alan" == none
#guard profile "grace" == none

/-- **5.3** — The first element of a list, or `none`. Then **5.4** uses it. -/
def head? : List α → Option α
  | _ => sorry

#guard head? [1, 2, 3] == some 1
#guard head? ([] : List Nat) == none

/-- **5.4** — The *second* element of a list, using `do` and `head?` twice.
Hint: you'll want the tail. Match it out, or use `List.tail`. -/
def second? (xs : List α) : Option α := do
  sorry

#guard second? [1, 2, 3] == some 2
#guard second? [1] == none
#guard second? ([] : List Nat) == none

/-- **5.5** — Turn a list of `Option`s into an `Option` of a list:
`none` if *any* element is `none`, otherwise all the values.
This is a genuinely useful function (the library calls it `sequence`). -/
def allSome : List (Option α) → Option (List α)
  | _ => sorry

#guard allSome [some 1, some 2, some 3] == some [1, 2, 3]
#guard allSome [some 1, none, some 3] == (none : Option (List Nat))
#guard allSome ([] : List (Option Nat)) == some []

/-- **5.6** — A safe square root over `Except`. Reject negatives with a
message; otherwise return the `Float.sqrt`. -/
def safeSqrt (x : Float) : Except String Float :=
  sorry

#guard safeSqrt 9.0 == Except.ok 3.0
#guard safeSqrt (-1.0) == Except.error "negative input"

/-- **5.7** — Evaluate an expression tree that can divide by zero.
Reuse the `Expr` idea from Chapter 2, now with failure. Use `do`. -/
inductive Expr where
  | lit (n : Int)
  | add (a b : Expr)
  | div (a b : Expr)
  deriving Repr

def Expr.eval : Expr → Except String Int
  | _ => sorry

#guard Expr.eval (.add (.lit 1) (.lit 2)) == Except.ok 3
#guard Expr.eval (.div (.lit 10) (.lit 2)) == Except.ok 5
#guard Expr.eval (.div (.lit 10) (.lit 0)) == Except.error "divide by zero"
#guard Expr.eval (.add (.lit 1) (.div (.lit 1) (.lit 0))) == Except.error "divide by zero"

/-- **5.8** — Sum the *even* numbers from 0 to n, imperatively, with
`Id.run do`, `let mut`, and a `for` loop. -/
def sumEvensTo (n : Nat) : Nat := Id.run do
  sorry

#guard sumEvensTo 10 == 30
#guard sumEvensTo 0 == 0
#guard sumEvensTo 1 == 0

/-! ## Playground

  * `#eval (← IO.getEnv "HOME")` won't work at top level — but
    `#eval do IO.println (← IO.getEnv "HOME")` will. Why?
  * `#eval IO.FS.readFile "lakefile.toml"` — Lean can touch your disk.
  * Write a `State` monad from scratch:
    `def State (σ α : Type) := σ → α × σ` plus a `Monad` instance.
    It's about fifteen lines and it will teach you more than any explanation.
  * `#eval [1,2,3].flatMap fun x => [x, x*10]` — this is `bind` for lists
    (Lean keeps it under a name rather than the `>>=` operator). What does
    "then" mean for a list? Nondeterminism: *every* choice, all at once.
-/

#eval [1,2,3].flatMap fun x => [x, x*10]

end Ch05
