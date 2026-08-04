/-! Solutions — Chapter 3. -/
namespace Sol03

def foldr (f : α → β → β) (init : β) : List α → β
  | []     => init
  | h :: t => f h (foldr f init t)

-- 3.1
def reverse : List α → List α
  | []     => []
  | h :: t => reverse t ++ [h]
#guard reverse [1, 2, 3] == [3, 2, 1]
#guard reverse ([] : List Nat) == []
#guard reverse ["a"] == ["a"]

-- 3.2
def filter (p : α → Bool) : List α → List α
  | []     => []
  | h :: t => if p h then h :: filter p t else filter p t
#guard filter (· % 2 == 0) [1, 2, 3, 4, 5, 6] == [2, 4, 6]
#guard filter (fun _ => false) [1, 2, 3] == []

-- 3.3
def maximum? : List Nat → Option Nat
  | []     => none
  | h :: t =>
    match maximum? t with
    | none   => some h
    | some m => some (max h m)
#guard maximum? [3, 1, 4, 1, 5] == some 5
#guard maximum? [] == none
#guard maximum? [7] == some 7

-- 3.4
def zip : List α → List β → List (α × β)
  | h1 :: t1, h2 :: t2 => (h1, h2) :: zip t1 t2
  | _, _ => []
#guard zip [1, 2, 3] ["a", "b"] == [(1, "a"), (2, "b")]
#guard zip ([] : List Nat) ["x"] == []

-- 3.5
def take : Nat → List α → List α
  | 0, _ => []
  | _, [] => []
  | n + 1, h :: t => h :: take n t
#guard take 2 [1, 2, 3, 4] == [1, 2]
#guard take 0 [1, 2, 3] == []
#guard take 99 [1, 2] == [1, 2]

-- 3.6
def insert (x : Nat) : List Nat → List Nat
  | []     => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys
#guard insert 3 [1, 2, 4, 5] == [1, 2, 3, 4, 5]
#guard insert 0 [1, 2] == [0, 1, 2]
#guard insert 9 [1, 2] == [1, 2, 9]

-- 3.7
def isort : List Nat → List Nat
  | []     => []
  | h :: t => insert h (isort t)
#guard isort [3, 1, 4, 1, 5, 9, 2, 6] == [1, 1, 2, 3, 4, 5, 6, 9]
#guard isort [] == []

-- 3.8
def mapViaFold (f : α → β) (xs : List α) : List β :=
  foldr (fun x acc => f x :: acc) [] xs
#guard mapViaFold (· + 1) [1, 2, 3] == [2, 3, 4]

-- 3.9  The trick: fold into a *function*, then apply it to [].
--      Each element becomes "append me at the end of whatever you're given".
def reverseViaFold (xs : List α) : List α :=
  foldr (fun x acc => acc ++ [x]) [] xs
#guard reverseViaFold [1, 2, 3] == [3, 2, 1]

-- 3.10
def revGo : List α → List α → List α
  | [], acc => acc
  | h :: t, acc => revGo t (h :: acc)

def reverseFast (xs : List α) : List α := revGo xs []
#guard reverseFast [1, 2, 3, 4] == [4, 3, 2, 1]
#guard reverseFast ([] : List Nat) == []

end Sol03
