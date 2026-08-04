/-! Solutions — Chapter 4. -/
namespace Sol04

structure Point where
  x : Float
  y : Float
  deriving Repr

structure Pair (α β : Type) where
  fst : α
  snd : β
  deriving Repr

class Describable (α : Type) where
  describe : α → String

instance : Describable Bool where
  describe b := if b then "the truth" else "a lie"

structure Money where
  cents : Int
  deriving Repr, BEq, DecidableEq

inductive Tree (α : Type) where
  | leaf
  | node (l : Tree α) (v : α) (r : Tree α)
  deriving Repr

def sample : Tree Nat := .node (.node .leaf 1 .leaf) 2 (.node .leaf 3 .leaf)

-- 4.1
def Point.dist2 (a b : Point) : Float :=
  let dx := a.x - b.x
  let dy := a.y - b.y
  dx * dx + dy * dy
#guard Point.dist2 ⟨0.0, 0.0⟩ ⟨3.0, 4.0⟩ == 25.0
#guard Point.dist2 ⟨1.0, 1.0⟩ ⟨1.0, 1.0⟩ == 0.0

-- 4.2
def Pair.swap (p : Pair α β) : Pair β α := ⟨p.snd, p.fst⟩
#guard (Pair.swap ⟨1, "a"⟩).fst == "a"
#guard (Pair.swap ⟨1, "a"⟩).snd == 1

-- 4.3
inductive Direction where
  | north | south | east | west
  deriving Repr, DecidableEq

instance : Describable Direction where
  describe
    | .north => "heading north"
    | .south => "heading south"
    | .east  => "heading east"
    | .west  => "heading west"
#guard Describable.describe Direction.north == "heading north"
#guard Describable.describe Direction.west == "heading west"

-- 4.4
instance : Sub Money where
  sub a b := ⟨a.cents - b.cents⟩
#guard Money.mk 1000 - Money.mk 250 == Money.mk 750

-- 4.5
instance : Ord Money where
  compare a b := compare a.cents b.cents
#guard compare (Money.mk 100) (Money.mk 200) == Ordering.lt
#guard compare (Money.mk 200) (Money.mk 200) == Ordering.eq
#guard compare (Money.mk 300) (Money.mk 200) == Ordering.gt

-- 4.6
instance [Describable α] : Describable (List α) where
  describe xs := String.intercalate ", " (xs.map Describable.describe)
#guard Describable.describe [true, false] == "the truth, a lie"

-- 4.7
def Tree.sum : Tree Nat → Nat
  | .leaf => 0
  | .node l v r => l.sum + v + r.sum
#guard Tree.sum sample == 6
#guard Tree.sum (.leaf : Tree Nat) == 0

-- 4.8
def Tree.toList : Tree α → List α
  | .leaf => []
  | .node l v r => l.toList ++ [v] ++ r.toList
#guard Tree.toList sample == [1, 2, 3]
#guard Tree.toList (.leaf : Tree Nat) == []

end Sol04
