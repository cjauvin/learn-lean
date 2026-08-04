/-! Solutions — Chapter 6. Term mode throughout, as the chapter asks. -/
namespace Sol06

variable (P Q R : Prop)

-- 6.1
theorem curry : (P ∧ Q → R) → (P → Q → R) :=
  fun h hp hq => h ⟨hp, hq⟩

-- 6.2
theorem uncurry : (P → Q → R) → (P ∧ Q → R) :=
  fun h hpq => h hpq.left hpq.right

-- 6.3
theorem and_map : (P → Q) → (P ∧ R → Q ∧ R) :=
  fun f h => ⟨f h.left, h.right⟩

-- 6.4
theorem or_map : (P → Q) → (P ∨ R → Q ∨ R) :=
  fun f h =>
    match h with
    | Or.inl hp => Or.inl (f hp)
    | Or.inr hr => Or.inr hr

-- 6.5
theorem or_elim : (P → R) → (Q → R) → (P ∨ Q → R) :=
  fun f g h =>
    match h with
    | Or.inl hp => f hp
    | Or.inr hq => g hq

-- 6.6  `¬Q` is `Q → False`, so `hnq (f hp) : False`, which is what `¬P` owes.
theorem contrapositive : (P → Q) → (¬Q → ¬P) :=
  fun f hnq hp => hnq (f hp)

-- 6.7
theorem demorgan : ¬P ∧ ¬Q → ¬(P ∨ Q) :=
  fun h hor =>
    match hor with
    | Or.inl hp => h.left hp
    | Or.inr hq => h.right hq

-- 6.8
theorem explosion : P ∧ ¬P → Q :=
  fun h => absurd h.left h.right

-- 6.9
theorem exists_cube : ∃ n : Nat, n * n * n = 27 :=
  ⟨3, rfl⟩

-- 6.10
theorem exists_map (f : Nat → Nat) (p q : Nat → Prop)
    (h : ∀ n, p n → q (f n)) : (∃ n, p n) → (∃ m, q m) :=
  fun ⟨w, hw⟩ => ⟨f w, h w hw⟩

end Sol06
