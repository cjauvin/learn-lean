/-! Solutions — Chapter 7. -/
namespace Sol07

variable (P Q R : Prop)

-- 7.1
example : P ∧ Q → P := by
  intro h
  exact h.left

-- 7.2
example : P → Q → P ∧ Q := by
  intro hp hq
  constructor
  · exact hp
  · exact hq

-- 7.3
example : (P ∨ Q) → (Q ∨ P) := by
  intro h
  cases h with
  | inl hp => right; exact hp
  | inr hq => left; exact hq

-- 7.4
example : P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro ⟨hp, hqr⟩
  cases hqr with
  | inl hq => left;  exact ⟨hp, hq⟩
  | inr hr => right; exact ⟨hp, hr⟩

-- 7.5
example (n : Nat) (h : n > 3) : n * 2 > 6 := by
  omega

-- 7.6
theorem add_succ_comm (n m : Nat) : n + (m + 1) = (n + 1) + m := by
  omega

-- 7.7
def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) + sumTo n

theorem sumTo_formula (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    show 2 * ((k + 1) + sumTo k) = (k + 1) * (k + 1 + 1)
    rw [Nat.mul_add, ih]
    simp [Nat.mul_add, Nat.add_mul, Nat.mul_comm]
    omega

-- The same thing, if you'd rather let the machine do it:
theorem sumTo_formula' (n : Nat) : 2 * sumTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih => grind [sumTo]

-- 7.8 / 7.9 / 7.10 — these are all in `simp`'s default set already,
-- which is itself the lesson: check whether the library knows it first.
theorem map_length (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by simp

theorem append_nil (xs : List α) : xs ++ [] = xs := by simp

theorem append_assoc (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by simp

-- ...and here they are the honest way, by induction, which is what
-- you should try first if you want the practice:
theorem map_length' (f : α → β) (xs : List α) :
    (xs.map f).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons h t ih => simp [ih]

theorem append_nil' (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => rfl
  | cons h t ih => simp

theorem append_assoc' (xs ys zs : List α) :
    (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  induction xs with
  | nil => rfl
  | cons h t ih => simp [ih]

end Sol07
