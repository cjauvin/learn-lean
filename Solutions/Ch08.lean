/-! Solutions — Chapter 8. -/
namespace Sol08

def myLength : List α → Nat
  | [] => 0
  | _ :: t => 1 + myLength t

def myAppend : List α → List α → List α
  | [], ys => ys
  | x :: xs, ys => x :: myAppend xs ys

-- 8.1
theorem append_nil (xs : List α) : myAppend xs [] = xs := by
  induction xs with
  | nil => rfl
  | cons h t ih => simp [myAppend, ih]

-- 8.2
theorem length_append (xs ys : List α) :
    myLength (myAppend xs ys) = myLength xs + myLength ys := by
  induction xs with
  | nil => simp [myAppend, myLength]
  | cons h t ih => simp [myAppend, myLength, ih]; omega

-- 8.3
theorem append_assoc (xs ys zs : List α) :
    myAppend (myAppend xs ys) zs = myAppend xs (myAppend ys zs) := by
  induction xs with
  | nil => rfl
  | cons h t ih => simp [myAppend, ih]

def myReverse : List α → List α
  | [] => []
  | x :: xs => myAppend (myReverse xs) [x]

-- 8.4  Needs 8.1 (nil case) and 8.3 (cons case).
theorem reverse_append (xs ys : List α) :
    myReverse (myAppend xs ys) = myAppend (myReverse ys) (myReverse xs) := by
  induction xs with
  | nil => simp [myAppend, myReverse, append_nil]
  | cons h t ih => simp [myAppend, myReverse, ih, append_assoc]

-- 8.5  Needs 8.4.
theorem reverse_reverse (xs : List α) : myReverse (myReverse xs) = xs := by
  induction xs with
  | nil => rfl
  | cons h t ih => simp [myReverse, reverse_append, ih, myAppend]

/- Sorting. Note the name `insertInto`: plain `insert` collides with core
   Lean's `Insert.insert`, and the ambiguity breaks `simp [insert]`. -/

def insertInto (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertInto x ys

def isort : List Nat → List Nat
  | [] => []
  | x :: xs => insertInto x (isort xs)

def LeAll (x : Nat) : List Nat → Prop
  | [] => True
  | y :: ys => x ≤ y ∧ LeAll x ys

def Sorted : List Nat → Prop
  | [] => True
  | x :: xs => LeAll x xs ∧ Sorted xs

-- 8.6
theorem le_all_trans (x y : Nat) (ys : List Nat) (hxy : x ≤ y) (h : LeAll y ys) :
    LeAll x ys := by
  induction ys with
  | nil => trivial
  | cons z zs ih => exact ⟨by have := h.left; omega, ih h.right⟩

-- 8.7
theorem le_all_insertInto (y x : Nat) (xs : List Nat) (hyx : y ≤ x)
    (h : LeAll y xs) : LeAll y (insertInto x xs) := by
  induction xs with
  | nil => exact ⟨hyx, trivial⟩
  | cons z zs ih =>
    simp only [insertInto]
    split
    · exact ⟨hyx, h⟩
    · exact ⟨h.left, ih h.right⟩

-- 8.8  The two branches of the `if` need the two lemmas above.
theorem insertInto_sorted (x : Nat) (xs : List Nat) (h : Sorted xs) :
    Sorted (insertInto x xs) := by
  induction xs with
  | nil => exact ⟨trivial, trivial⟩
  | cons y ys ih =>
    simp only [insertInto]
    split
    · rename_i hxy
      exact ⟨⟨hxy, le_all_trans x y ys hxy h.left⟩, h⟩
    · rename_i hxy
      exact ⟨le_all_insertInto y x ys (by omega) h.left, ih h.right⟩

-- 8.9
theorem isort_sorted (xs : List Nat) : Sorted (isort xs) := by
  induction xs with
  | nil => trivial
  | cons h t ih => exact insertInto_sorted h (isort t) ih

-- 8.10
theorem insertInto_length (x : Nat) (xs : List Nat) :
    (insertInto x xs).length = xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [insertInto]; split <;> simp [ih]

theorem isort_length (xs : List Nat) : (isort xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons h t ih => simp [isort, insertInto_length, ih]

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

namespace Vec
def toList : Vec α n → List α
  | .nil => []
  | .cons h t => h :: toList t

def ofThree (a b c : α) : Vec α 3 := .cons a (.cons b (.cons c .nil))

-- 8.11
def map (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons h t => .cons (f h) (map f t)

-- 8.12
def get : Vec α n → Fin n → α
  | .cons h _, ⟨0, _⟩ => h
  | .cons _ t, ⟨i + 1, hi⟩ => get t ⟨i, by omega⟩
end Vec

#guard (Vec.map (· * 2) (Vec.ofThree 1 2 3)).toList == [2, 4, 6]
#guard Vec.get (Vec.ofThree 10 20 30) ⟨1, by decide⟩ == 20

end Sol08
