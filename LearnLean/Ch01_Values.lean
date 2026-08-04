/-!
# Chapter 1 — Values, Types, and Functions

Welcome. Lean has no REPL in the usual sense: **the file _is_ the REPL**.
You write a command, and the answer appears in the InfoView pane on the right.
If you don't see it, hit `Ctrl+Shift+Enter` (or `Cmd+Shift+Enter`) to open it.

Three commands you will use constantly:

| Command  | Asks Lean                          |
|----------|------------------------------------|
| `#eval`  | "run this and show me the value"   |
| `#check` | "what is the *type* of this?"      |
| `#print` | "show me the definition"           |

Put your cursor on any line below and watch the InfoView.
-/

namespace Ch01

/-! ## 1. Everything has a type -/

#eval 2 + 3
#eval "Lean" ++ " " ++ "rocks"
#eval (3 : Int) - 10        -- Int can go negative
#eval 3 - 10                -- Nat can't! It floors at 0. Surprised? Good.

#check 2 + 3                -- Nat
#check "hello"              -- String
#check true                 -- Bool
#check (2.5 : Float)        -- Float

/-
`Nat` is the type of natural numbers 0, 1, 2, ... It has *no* negatives, so
subtraction saturates at zero. This is not a bug — it's a design choice that
makes `Nat` easy to reason about later. When you want negatives, say `Int`.
-/

/-! ## 2. Types are values too

This is the first genuinely mind-bending thing about Lean. `Nat` is a value,
and it has a type, and *that* has a type, forever. -/

#check Nat                  -- Type
#check Type                 -- Type 1
#check Type 1               -- Type 2

/-! ## 3. Definitions -/

def greeting : String := "Hello"

def answer : Nat := 42

#eval greeting
#eval answer

/-! ## 4. Functions

Note the shape: `def name (arg : ArgType) : ReturnType := body`
-/

def square (n : Nat) : Nat := n * n

#eval square 7              -- no parentheses! `square 7`, not `square(7)`

/-
Functions are **curried**: a two-argument function is really a function that
returns a function. Look at the type Lean reports below.
-/

def add (a : Nat) (b : Nat) : Nat := a + b

#check add                  -- Nat → Nat → Nat
#check add 3                -- Nat → Nat    ← partially applied!

def addThree : Nat → Nat := add 3
#eval addThree 10

-- Anonymous functions (lambdas). `fun x => ...` or the unicode `λ x => ...`
#eval (fun x => x * 2) 21
#eval (λ x => x * 2) 21     -- identical; type `\lambda` to get λ

/-! ## 5. Conditionals and `let` -/

def absDiff (a b : Nat) : Nat :=
  if a > b then a - b else b - a

#eval absDiff 3 10

def hypotenuseIsh (a b : Nat) : Nat :=
  let a2 := a * a
  let b2 := b * b
  a2 + b2

#eval hypotenuseIsh 3 4

/-!
## Exercises

Replace each `sorry` with a real implementation. The `#guard` lines below each
exercise are your test suite: they turn **red** while wrong and go **silent**
when correct. Silence is success.

Note: while a definition contains `sorry`, `#guard` reports
"cannot evaluate code because ... uses 'sorry'". That's expected — it's the
red light telling you there's work to do.
-/

/-- **1.1** — Return `n` doubled. -/
def double (n : Nat) : Nat :=
  n * 2

#guard double 0 == 0
#guard double 21 == 42

/-- **1.2** — The maximum of three numbers. -/
def max3 (a b c : Nat) : Nat :=
  [a, b, c].max?.getD 0

#guard max3 1 2 3 == 3
#guard max3 9 2 3 == 9
#guard max3 1 9 3 == 9
#guard max3 4 4 4 == 4

/-- **1.3** — Is `n` even? Hint: `n % 2` gives the remainder. -/
def isEven (n : Nat) : Bool :=
  n % 2 == 0

#guard isEven 0 == true
#guard isEven 7 == false
#guard isEven 12 == true

/-- **1.4** — Greet someone by name: `greet "Ada"` should give `"Hello, Ada!"` -/
def greet (name : String) : String :=
  "Hello, " ++ name ++ "!"

#guard greet "Ada" == "Hello, Ada!"
#guard greet "Lean" == "Hello, Lean!"

/-- **1.5** — FizzBuzz, one number at a time.
Return `"Fizz"` for multiples of 3, `"Buzz"` for multiples of 5,
`"FizzBuzz"` for multiples of both, and the number as a string otherwise.
Hint: `toString n` converts a `Nat` to a `String`. -/
def fizzbuzz (n : Nat) : String :=
  if n % 3 == 0 && n % 5 == 0 then "FizzBuzz"
  else if n % 3 == 0 then "Fizz"
  else if n % 5 == 0then "Buzz"
  else toString n

#guard fizzbuzz 1 == "1"
#guard fizzbuzz 3 == "Fizz"
#guard fizzbuzz 5 == "Buzz"
#guard fizzbuzz 15 == "FizzBuzz"
#guard fizzbuzz 7 == "7"

/-- **1.6** — Function *composition*, by hand.
`applyTwice f x` should apply `f` to `x`, then apply `f` to the result.
Notice the type: `f` is itself an argument. Functions are ordinary values. -/
def applyTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#guard applyTwice (· + 3) 10 == 16
#guard applyTwice (· * 2) 5 == 20

/-
That `(· + 3)` is Lean's shorthand for `fun x => x + 3`. The `·` (type `\.`)
marks the hole where the argument goes. It's used everywhere in real Lean code.
-/

/-! ## Playground

Scratch space — nothing here is graded. Try to make Lean surprise you.
Some prompts, if you want them:
  * What does `#eval 2 ^ 64` give? What about `#eval (2 : UInt64) ^ 63 * 2`?
  * What is the type of `#check fun x => x`? Why is it strange?
  * Can you write a function that takes a function and returns a function?
-/

#eval 2 ^ 64
#check fun x => x

end Ch01
