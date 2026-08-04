/-! Solutions — Chapter 2. -/
namespace Sol02

inductive Direction where
  | north | south | east | west
  deriving Repr, DecidableEq
open Direction

inductive MyBool where
  | tt | ff
  deriving Repr, DecidableEq

inductive MyNat where
  | zero
  | succ (n : MyNat)
  deriving Repr
open MyNat

def MyNat.add : MyNat → MyNat → MyNat
  | m, zero   => m
  | m, succ n => succ (MyNat.add m n)

def toNat : MyNat → Nat
  | zero => 0
  | succ n => toNat n + 1

inductive Shape where
  | circle (radius : Float)
  | rect (width height : Float)
  | triangle (base height : Float)
  deriving Repr

-- 2.1
def compass : Direction → String
  | north => "N"
  | south => "S"
  | east  => "E"
  | west  => "W"
#guard compass north == "N"
#guard compass south == "S"
#guard compass east == "E"
#guard compass west == "W"

-- 2.2
def rotateCW : Direction → Direction
  | north => east
  | east  => south
  | south => west
  | west  => north
#guard rotateCW north == east
#guard rotateCW east == south
#guard rotateCW south == west
#guard rotateCW west == north

-- 2.3
def MyBool.or : MyBool → MyBool → MyBool
  | .tt, _ => .tt
  | .ff, b => b
#guard MyBool.or MyBool.tt MyBool.ff == MyBool.tt
#guard MyBool.or MyBool.ff MyBool.ff == MyBool.ff
#guard MyBool.or MyBool.ff MyBool.tt == MyBool.tt

-- 2.4
def ofNat : Nat → MyNat
  | 0 => zero
  | n + 1 => succ (ofNat n)
#guard toNat (ofNat 0) == 0
#guard toNat (ofNat 5) == 5

-- 2.5
def MyNat.mul : MyNat → MyNat → MyNat
  | _, zero   => zero
  | m, succ n => MyNat.add (MyNat.mul m n) m
#guard toNat (MyNat.mul (ofNat 3) (ofNat 4)) == 12
#guard toNat (MyNat.mul (ofNat 0) (ofNat 9)) == 0
#guard toNat (MyNat.mul (ofNat 7) (ofNat 1)) == 7

-- 2.6
def perimeter : Shape → Float
  | .circle r     => 2.0 * 3.14159 * r
  | .rect w h     => 2.0 * (w + h)
  | .triangle b _ => 3.0 * b
#guard perimeter (.rect 3.0 4.0) == 14.0
#guard perimeter (.triangle 5.0 2.0) == 15.0

-- 2.7
inductive Expr where
  | lit (n : Int)
  | neg (e : Expr)
  | add (a b : Expr)
  | mul (a b : Expr)
  deriving Repr

def Expr.eval : Expr → Int
  | .lit n   => n
  | .neg e   => -e.eval
  | .add a b => a.eval + b.eval
  | .mul a b => a.eval * b.eval
#guard Expr.eval (.mul (.add (.lit 2) (.lit 3)) (.lit 4)) == 20
#guard Expr.eval (.neg (.lit 7)) == -7
#guard Expr.eval (.add (.neg (.lit 5)) (.lit 5)) == 0

-- 2.8
def Expr.countLits : Expr → Nat
  | .lit _   => 1
  | .neg e   => e.countLits
  | .add a b => a.countLits + b.countLits
  | .mul a b => a.countLits + b.countLits
#guard Expr.countLits (.lit 1) == 1
#guard Expr.countLits (.mul (.add (.lit 2) (.lit 3)) (.lit 4)) == 3
#guard Expr.countLits (.neg (.neg (.lit 0))) == 1

end Sol02
