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



lemma aux_gives_closest_pair:
  ∀ (g : grid_2D),
    -- If there's a closest pair within distance `c`,
    (∃ (p q : point),
      cp_with_help p q g.ps g.c) →
    -- TODO we'll need a supposition that the closest pair is within distance `c`
    (∃ (p q : point),
      aux g g.ps = some (p, q)
      ∧ closest_pair p q g.ps) := begin
  intros g cp_help,
  apply cp_with_help_and_cp_in_balls_implies_closest_pair,
  assumption,
  apply aux_finds_closest_pair_in_ball_union,
  simp,
end


lemma grid_pts_dot_c_with_c_eq_c :
  ∀ (c : ℕ⁺) (ps : list point),
    (grid_points c ps).c = c := sorry

lemma grid_pts_dot_ps_with_ps_eq_ps :
  ∀ (c : ℕ⁺) (ps : list point),
    (grid_points c ps).ps = ps := sorry
