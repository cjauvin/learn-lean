/-! Solutions — Chapter 5. -/
namespace Sol05

instance [BEq ε] [BEq α] : BEq (Except ε α) where
  beq
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false

-- 5.1
def lookup (key : String) : List (String × Nat) → Option Nat
  | [] => none
  | (k, v) :: rest => if k == key then some v else lookup key rest
#guard lookup "b" [("a", 1), ("b", 2)] == some 2
#guard lookup "z" [("a", 1), ("b", 2)] == none

-- 5.2
def ages : List (String × Nat) := [("ada", 36), ("alan", 41)]
def cities : List (String × Nat) := [("ada", 44), ("grace", 55)]

def profile (name : String) : Option String := do
  let age ← lookup name ages
  let city ← lookup name cities
  return s!"{name}: {age} / {city}"
#guard profile "ada" == some "ada: 36 / 44"
#guard profile "alan" == none
#guard profile "grace" == none

-- 5.3
def head? : List α → Option α
  | [] => none
  | h :: _ => some h
#guard head? [1, 2, 3] == some 1
#guard head? ([] : List Nat) == none

-- 5.4
def second? (xs : List α) : Option α := do
  let _ ← head? xs
  head? xs.tail
#guard second? [1, 2, 3] == some 2
#guard second? [1] == none
#guard second? ([] : List Nat) == none

-- 5.5
def allSome : List (Option α) → Option (List α)
  | [] => some []
  | x :: xs => do
    let v ← x
    let rest ← allSome xs
    return v :: rest
#guard allSome [some 1, some 2, some 3] == some [1, 2, 3]
#guard allSome [some 1, none, some 3] == (none : Option (List Nat))
#guard allSome ([] : List (Option Nat)) == some []

-- 5.6
def safeSqrt (x : Float) : Except String Float :=
  if x < 0.0 then .error "negative input" else .ok (Float.sqrt x)
#guard safeSqrt 9.0 == Except.ok 3.0
#guard safeSqrt (-1.0) == Except.error "negative input"

-- 5.7
inductive Expr where
  | lit (n : Int)
  | add (a b : Expr)
  | div (a b : Expr)
  deriving Repr

def Expr.eval : Expr → Except String Int
  | .lit n => .ok n
  | .add a b => do
    let x ← a.eval
    let y ← b.eval
    return x + y
  | .div a b => do
    let x ← a.eval
    let y ← b.eval
    if y == 0 then .error "divide by zero" else .ok (x / y)
#guard Expr.eval (.add (.lit 1) (.lit 2)) == Except.ok 3
#guard Expr.eval (.div (.lit 10) (.lit 2)) == Except.ok 5
#guard Expr.eval (.div (.lit 10) (.lit 0)) == Except.error "divide by zero"
#guard Expr.eval (.add (.lit 1) (.div (.lit 1) (.lit 0))) == Except.error "divide by zero"

-- 5.8
def sumEvensTo (n : Nat) : Nat := Id.run do
  let mut total := 0
  for i in List.range (n + 1) do
    if i % 2 == 0 then
      total := total + i
  return total
#guard sumEvensTo 10 == 30
#guard sumEvensTo 0 == 0
#guard sumEvensTo 1 == 0

end Sol05
