-- import data.nat.basic

-- open nat
-- #check nat

inductive my_nat
| zero : my_nat
| succ : my_nat → my_nat
notation `ℕ'` := my_nat

open my_nat

def my_add : my_nat → my_nat → my_nat
| m zero      := m
| m (succ n') := succ (my_add m n')



notation m `+` n := my_add m n

instance : has_zero my_nat := ⟨zero⟩

lemma zero_add (n : ℕ') : 0 + n = n := begin
  induction n with n' ih,
  -- Base Case
  refl,
  -- Inductive Step
  simp [my_add],
  apply ih,
end



-- def closest_pair (p q : point) (ps : list point) : Prop :=
--   (p ∈ ps) ∧
--   (q ∈ ps) ∧
--   (p ≠ q) ∧
--   (∀ (r s : point),
--       (same_pair (p, q) (r, s) ↔ ∥ p - q ∥ = ∥ r - s ∥) ∧
--      (¬(same_pair (p, q) (r, s)) ↔ ∥ p - q ∥ < ∥ r - s ∥))

-- def cp_with_help (p q : point) (ps : list point) (c : ℕ⁺) : Prop :=
--   (closest_pair p q ps) ∧ (1 < ∥ p - q ∥) ∧ (∥ p - q ∥ ≤ c)

-- def find_closest_pair (ps : list point) (c : ℕ⁺) : (point × point) := sorry

-- theorem find_closest_pair_correct :
--   ∀ (ps : list point) (c : ℕ⁺),
--     (∃ (p q : point),
--       (closest_pair p q ps) ∧ (1 < ∥ p - q ∥) ∧ (∥ p - q ∥ ≤ c)) →
--     (∃ (p q : point),
--       find_closest_pair ps c = (p, q) ∧
--       closest_pair p q ps)

