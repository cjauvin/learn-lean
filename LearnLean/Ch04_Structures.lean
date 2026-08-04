/-!
# Chapter 4 — Structures, Polymorphism, and Type Classes

Chapter 2 gave us "a value is one of *these* shapes" (inductives, sum types).
This chapter gives us "a value has *all* of these fields" (structures, product
types), and then the thing that ties Lean's whole library together:
**type classes**.

If you know Haskell's typeclasses or Rust's traits, you're home already.
If you know Java interfaces — same idea, but you can add an implementation to
a type you don't own, long after the fact.
-/

namespace Ch04

/-! ## 1. Structures -/

structure Point where
  x : Float
  y : Float
  deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }
def p1 : Point := ⟨3.0, 4.0⟩          -- anonymous constructor: type ⟨ as \<>

#eval p1
#eval p1.x                            -- field access
#eval Point.x p1                      -- ...is just sugar for this

/-- Functional update: copy `p`, change one field. -/
def mirrorX (p : Point) : Point := { p with y := -p.y }

#eval mirrorX p1

/-
A structure is secretly an inductive with exactly one constructor. Lean just
generates the field accessors for you. `#print Point` shows the machinery.
-/

/-! ## 2. Methods, via namespaces

There is no `class`-with-methods in Lean. Instead: a function in the type's
namespace can be called with dot notation. That's the entire trick. -/

def Point.norm (p : Point) : Float :=
  Float.sqrt (p.x * p.x + p.y * p.y)

#eval p1.norm                         -- because p1 : Point, this finds Point.norm

/-! ## 3. Polymorphic structures -/

structure Pair (α β : Type) where
  fst : α
  snd : β
  deriving Repr

#eval Pair.mk 1 "one"
#check (⟨1, "one"⟩ : Pair Nat String)

-- Lean's built-in product type `α × β` is exactly this.
#eval (1, "one")
#eval (1, "one").fst

/-! ## 4. Type classes — the real subject

A type class is a *promise* that a type supports some operations. -/

class Describable (α : Type) where
  describe : α → String

instance : Describable Point where
  describe p := s!"a point at ({p.x}, {p.y})"

instance : Describable Bool where
  describe b := if b then "the truth" else "a lie"

#eval Describable.describe p1
#eval Describable.describe true

/-
`s!"..."` is string interpolation — `{expr}` inside splices in the value.
It needs the spliced type to have a `ToString` instance. Which is, of course,
another type class.
-/

/-- Classes compose. This function works for *any* describable type. -/
def announce [Describable α] (x : α) : String :=
  "Behold: " ++ Describable.describe x

#eval announce p1
#eval announce false

/-
Read `[Describable α]` as "given that α is describable". It's an argument
Lean fills in *automatically* by searching for a matching instance. That
search is why `+` works on `Nat`, `Int`, `Float`, matrices, and polynomials
without any of them knowing about each other.
-/

/-! ## 5. Implementing the standard classes

This is where type classes stop being an abstraction exercise. Give your
type the right instances and it slots into the whole language. -/

structure Money where
  cents : Int
  deriving Repr, BEq, DecidableEq

instance : ToString Money where
  toString m := s!"${m.cents / 100}.{(m.cents % 100).natAbs}"

instance : Add Money where
  add a b := ⟨a.cents + b.cents⟩

instance : Neg Money where
  neg a := ⟨-a.cents⟩

#eval toString (Money.mk 1250)
#eval Money.mk 1250 + Money.mk 375     -- `+` now works, because of `Add Money`
#eval -Money.mk 500

/-
Notice you never wrote `Money.add`. You wrote an `Add` *instance*, and the
`+` notation found it. Every operator in Lean works this way.
-/

/-! ## 6. `Functor` — a class over a type *constructor*

The classes above ranged over types (`α : Type`). This one ranges over
things-that-take-a-type (`f : Type → Type`) — like `List`, `Option`, `Array`. -/

#check @Functor.map          -- {f} → [Functor f] → (α → β) → f α → f β

#eval (· * 2) <$> [1, 2, 3]           -- <$> is Functor.map (type \<$>)
#eval (· * 2) <$> (some 21)
#eval (· * 2) <$> (none : Option Nat)

/-- Your own container, made mappable. -/
inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (v : α) (r : Tree α)
  deriving Repr

def Tree.map (f : α → β) : Tree α → Tree β
  | .leaf => .leaf
  | .node l v r => .node (l.map f) (f v) (r.map f)

instance : Functor Tree where
  map := Tree.map

def sample : Tree Nat := .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)

#eval (· * 10) <$> sample

/-!
## Exercises
-/

/-- **4.1** — The squared distance between two points.
(Squared, so we avoid `sqrt` in the tests.) -/
def Point.dist2 (a b : Point) : Float :=
  sorry

#guard Point.dist2 ⟨0.0, 0.0⟩ ⟨3.0, 4.0⟩ == 25.0
#guard Point.dist2 ⟨1.0, 1.0⟩ ⟨1.0, 1.0⟩ == 0.0

/-- **4.2** — Swap the two components of a `Pair`. Note how the type
signature alone almost forces the implementation. -/
def Pair.swap (p : Pair α β) : Pair β α :=
  sorry

#guard (Pair.swap ⟨1, "a"⟩).fst == "a"
#guard (Pair.swap ⟨1, "a"⟩).snd == 1

/-- **4.3** — Make `Direction` describable. Fill in the instance body so that
each direction describes itself as `"heading north"`, `"heading south"`, etc. -/
inductive Direction where
  | north | south | east | west
  deriving Repr, DecidableEq

instance : Describable Direction where
  describe := sorry

#guard Describable.describe Direction.north == "heading north"
#guard Describable.describe Direction.west == "heading west"

/-- **4.4** — Give `Money` a `Sub` instance so `-` works between two `Money`s. -/
instance : Sub Money where
  sub := sorry

#guard Money.mk 1000 - Money.mk 250 == Money.mk 750

/-- **4.5** — Give `Money` an `LT`-free ordering via `Ord`. `Ord` requires
`compare : α → α → Ordering`, where `Ordering` is `.lt`, `.eq`, or `.gt`.
Hint: `compare` already exists for `Int`. -/
instance : Ord Money where
  compare := sorry

#guard compare (Money.mk 100) (Money.mk 200) == Ordering.lt
#guard compare (Money.mk 200) (Money.mk 200) == Ordering.eq
#guard compare (Money.mk 300) (Money.mk 200) == Ordering.gt

/-- **4.6** — A polymorphic `Describable` instance: *any* list of describable
things is itself describable. Produce a comma-joined description.
Hint: `String.intercalate ", " listOfStrings`, and `xs.map f`. -/
instance [Describable α] : Describable (List α) where
  describe := sorry

#guard Describable.describe [true, false] == "the truth, a lie"

/-- **4.7** — Sum the values in a `Tree Nat`. (A `leaf` contributes 0.) -/
def Tree.sum : Tree Nat → Nat
  | _ => sorry

#guard Tree.sum sample == 6
#guard Tree.sum (.leaf : Tree Nat) == 0

/-- **4.8** — In-order traversal of a tree into a list. -/
def Tree.toList : Tree α → List α
  | _ => sorry

#guard Tree.toList sample == [1, 2, 3]
#guard Tree.toList (.leaf : Tree Nat) == []

/-! ## Playground

  * `#eval sample.toList` — dot notation works on *your* types too, once
    `Tree.toList` exists. Try it after solving 4.8.
  * Write `instance : ToString Point`. Then `#eval s!"{p1}"` starts working.
  * `#check @Add.add` and `#print Add`. Type classes are just structures;
    instances are just values. There is no magic layer — only inference.
  * Add `instance : Append Money`? Should you? (No. But try it and see that
    Lean lets you. Instance design is a taste question.)
-/

end Ch04
