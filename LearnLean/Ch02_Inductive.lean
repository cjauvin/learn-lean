/-!
# Chapter 2 — Inductive Types and Pattern Matching

In most languages you get a fixed menu of built-in types plus classes/structs.
In Lean, almost every type — including `Bool`, `Nat`, and `List` — is *defined
in the library* using one mechanism: **inductive types**.

An inductive type is declared by listing the ways to *build* a value.
Those ways are called **constructors**. That's the whole idea.

To convince you, we're going to rebuild `Bool` and `Nat` from nothing.
-/

namespace Ch02

/-! ## 1. Enumerations: the simplest inductives -/

inductive Direction where
  | north
  | south
  | east
  | west
  deriving Repr, DecidableEq

/-
`deriving Repr` teaches Lean how to *print* the value (so `#eval` works).
`deriving DecidableEq` gives us `==`. Without these, both would fail.
-/

#eval Direction.north
#check Direction.north

open Direction   -- lets us write `north` instead of `Direction.north`

/-- Pattern matching: one branch per constructor. -/
def opposite (d : Direction) : Direction :=
  match d with
  | north => south
  | south => north
  | east  => west
  | west  => east

#eval opposite north

/-
**Try this**: comment out the `| west => east` line above and watch Lean
complain. It knows the constructors, so it knows when you missed one.
Exhaustiveness checking, for free.
-/

/-! ## 2. Rebuilding `Bool`

There is nothing primitive about booleans. Two constructors, no arguments. -/

inductive MyBool where
  | tt
  | ff
  deriving Repr, DecidableEq

def MyBool.not : MyBool → MyBool
  | tt => ff
  | ff => tt

/-
Notice the style above: we skipped `match` entirely. When a definition is
*only* a match on its arguments, you can write the patterns directly after
the `:=`-less signature. This is called **equation-style** definition and
it's very common in Lean.
-/

def MyBool.and : MyBool → MyBool → MyBool
  | tt, b => b
  | ff, _ => ff

#eval MyBool.and MyBool.tt MyBool.ff

/-! ## 3. Rebuilding `Nat` — recursion enters

Here's the leap. A constructor is allowed to take an argument **of the type
being defined**. That single move gives you infinity out of two lines. -/

inductive MyNat where
  | zero
  | succ (n : MyNat)
  deriving Repr

/-
Read it as: "a MyNat is either zero, or the successor of some other MyNat."

  0 = zero
  1 = succ zero
  2 = succ (succ zero)
  3 = succ (succ (succ zero))

This *is* how Lean's real `Nat` is defined. `#print Nat` and see for yourself.
The literal `3` is just sugar. (The compiler secretly uses GMP bignums for
speed, but the mathematical definition is the one above.)
-/

#print Nat

open MyNat

def two : MyNat := succ (succ zero)
#eval two

/-- Addition, by recursion on the *second* argument. -/
def MyNat.add : MyNat → MyNat → MyNat
  | m, zero    => m
  | m, succ n  => succ (MyNat.add m n)

/-
Trace it yourself:
  add 2 1
    = add 2 (succ zero)
    = succ (add 2 zero)
    = succ 2
    = 3                              ✓

Every recursive call peels one `succ` off the second argument, so it must
reach `zero`. Lean checks this — it will *reject* a recursion it can't see
terminating. More on that in Chapter 3.
-/

def toNat : MyNat → Nat
  | zero => 0
  | succ n => toNat n + 1

#eval toNat (MyNat.add two two)   -- 4

/-! ## 4. Constructors can carry data -/

inductive Shape where
  | circle (radius : Float)
  | rect (width height : Float)
  | triangle (base height : Float)
  deriving Repr

def area : Shape → Float
  | .circle r     => 3.14159 * r * r
  | .rect w h     => w * h
  | .triangle b h => b * h / 2

/-
The `.circle` shorthand: when Lean already knows the expected type, you can
drop the type name and write just `.constructor`. You'll see this everywhere.
-/

#eval area (.circle 1.0)
#eval area (.rect 3.0 4.0)

/-!
## Exercises
-/

/-- **2.1** — Turn a `Direction` into a compass string: `"N"`, `"S"`, `"E"`, `"W"`. -/
def compass : Direction → String
  | north => "N"
  | south => "S"
  | east => "E"
  | west => "W"

#guard compass north == "N"
#guard compass south == "S"
#guard compass east == "E"
#guard compass west == "W"

/-- **2.2** — Rotate a direction 90° clockwise (north ↦ east ↦ south ↦ west ↦ north). -/
def rotateCW : Direction → Direction
  | north => east
  | south => west
  | east => south
  | west => north

#guard rotateCW north == east
#guard rotateCW east == south
#guard rotateCW south == west
#guard rotateCW west == north

/-- **2.3** — `MyBool.or`. Four cases, but you can cover them in only *two*
pattern lines by using a wildcard `_`, like `MyBool.and` did.

There are two such answers — one matches on the first argument, one on the
second. They compute the same results but are *not* interchangeable; see
the note below once you've found one. -/
def MyBool.or : MyBool → MyBool → MyBool
  | b, ff => b
  | _, tt => tt

#guard MyBool.or MyBool.tt MyBool.ff == MyBool.tt
#guard MyBool.or MyBool.ff MyBool.ff == MyBool.ff
#guard MyBool.or MyBool.ff MyBool.tt == MyBool.tt

/-
**The note.** Whichever argument you matched on, *that* argument is the one
Lean can reduce without knowing the other. If you wrote `| tt, _ => tt`
first, then `or tt b` collapses to `tt` for an unknown `b`. If you wrote
`| b, ff => b` first, then `or b ff` collapses to `b` instead — and the
other one gets stuck.

You can watch it happen. One of these two lines type-checks and the other
does not; swap your definition around and they trade places:

    example (b : MyBool) : MyBool.or MyBool.tt b = MyBool.tt := rfl
    example (b : MyBool) : MyBool.or b MyBool.ff = b := rfl

Nothing is wrong with either definition — they agree on every input. But
the *order you match in* decides which facts are free and which cost you a
proof. It comes back in Chapter 7, where `n + 0 = n` is true by `rfl` and
`0 + n = n` needs a whole induction, for exactly this reason.
-/

/-- **2.4** — Convert a `Nat` into a `MyNat`. This is the inverse of `toNat`.
Hint: recurse on the `Nat`. The patterns you want are `0` and `n + 1`. -/
def ofNat : Nat → MyNat
  | 0 => zero
  | n + 1 => succ (ofNat n)

#guard toNat (ofNat 0) == 0
#guard toNat (ofNat 5) == 5

/-- **2.5** — Multiplication on `MyNat`, defined using only `MyNat.add`,
recursion, and the two constructors. No cheating via `Nat`!
Hint: `m * 0 = 0` and `m * (n+1) = m * n + m`. -/
def MyNat.mul : MyNat → MyNat → MyNat
  | _, zero => zero
  | m, succ n => MyNat.add (MyNat.mul m n) m

#guard toNat (MyNat.mul (ofNat 3) (ofNat 4)) == 12
#guard toNat (MyNat.mul (ofNat 0) (ofNat 9)) == 0
#guard toNat (MyNat.mul (ofNat 7) (ofNat 1)) == 7

/-- **2.6** — The perimeter of a `Shape`. Use `2.0 * 3.14159 * r` for a circle,
and for the triangle just pretend it's equilateral: `3.0 * base`. -/
def perimeter : Shape → Float
  | .circle r => 2.0 * 3.14159 * r
  | .rect w h => 2.0 * w + 2.0 * h
  | .triangle b _ => 3.0 * b

#guard perimeter (.rect 3.0 4.0) == 14.0
#guard perimeter (.triangle 5.0 2.0) == 15.0

/-- **2.7** — A tiny expression language. This is the shape of every
interpreter, compiler, and query engine you will ever write.

Fill in `eval`. -/
inductive Expr where
  | lit (n : Int)
  | neg (e : Expr)
  | add (a b : Expr)
  | sub (a b : Expr)
  | mul (a b : Expr)
  deriving Repr

def Expr.eval : Expr → Int
  | .lit n => n
  | .neg e => -e.eval
  | .add a b => a.eval + b.eval
  | .sub a b => a.eval - b.eval
  | .mul a b => a.eval * b.eval

-- (2 + 3) * 4  =  20
#guard Expr.eval (.mul (.add (.lit 2) (.lit 3)) (.lit 4)) == 20
#guard Expr.eval (.neg (.lit 7)) == -7
#guard Expr.eval (.add (.neg (.lit 5)) (.lit 5)) == 0
#guard Expr.eval (.sub (.lit 5) (.lit 7)) == -2

/-- **2.8** — Count how many `lit` nodes an expression contains. -/
def Expr.countLits : Expr → Nat
  | .lit _ => 1
  | .neg e => e.countLits
  | .add a b => a.countLits + b.countLits
  | .sub a b => a.countLits + b.countLits
  | .mul a b => a.countLits + b.countLits

#guard Expr.countLits (.lit 1) == 1
#guard Expr.countLits (.mul (.add (.lit 2) (.lit 3)) (.lit 4)) == 3
#guard Expr.countLits (.neg (.neg (.lit 0))) == 1

def Expr.pretty : Expr →  String
  | .lit n => toString n
  | .neg e => "-" ++ pretty e
  | .add a b => "(" ++ a.pretty ++ " + " ++ b.pretty ++ ")"
  | .sub a b => "(" ++ a.pretty ++ " - " ++ b.pretty ++ ")"
  | .mul a b => "(" ++ a.pretty ++ " * " ++ b.pretty ++ ")"

#guard Expr.pretty (.lit 1) == "1"
#guard Expr.pretty (.neg (.lit 2)) == "-2"

#guard Expr.pretty (.mul (.add (.lit 2) (.lit 3)) (.lit 4)) == "((2 + 3) * 4)"
#guard Expr.pretty (.neg (.lit 7)) == "-7"
#guard Expr.pretty (.add (.neg (.lit 5)) (.lit 5)) == "(-5 + 5)"
#guard Expr.pretty (.sub (.lit 5) (.lit 7)) == "(5 - 7)"

/-! ## Playground

Ideas:
  * Add a `sub` constructor to `Expr`. Then — before fixing anything —
    save and look at the errors. Every function that pattern-matches on
    `Expr` now reports `Missing cases: (sub _ _)`, so the compiler has
    handed you a complete, guaranteed-exhaustive list of what to update.
    Work down the squiggles; when the last one goes, you are provably
    finished. This is what exhaustiveness checking buys you as a
    *refactoring* tool, and it's the reason a catch-all `| _ => ...` is a
    real tradeoff: with one, adding `sub` would produce no error at all,
    and the new constructor would silently take the wrong branch forever.
  * Write `Expr.pretty : Expr → String` producing `"((2 + 3) * 4)"`.
  * Define `inductive Tree where | leaf | node (l : Tree) (v : Nat) (r : Tree)`
    and write `size`, `depth`, and `mirror`.
-/

end Ch02
