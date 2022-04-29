import data.nat.basic
import data.rat.basic
import data.rat.order
import data.int.basic
import data.int.order
import algebra.group_power.order

def point := ℤ × ℤ
-- def point := ℚ × ℚ
instance : has_repr point :=
  ⟨λ p, "(" ++ (repr p.1) ++ ", " ++ (repr p.2) ++ ")"⟩
instance : has_add point :=
  ⟨λ p₁ p₂, (p₁.1 + p₂.1, p₁.2 + p₂.2)⟩
instance : has_sub point :=
  ⟨λ p₁ p₂, (p₁.1 - p₂.1, p₁.2 - p₂.2)⟩
instance : has_neg point :=
  ⟨λ p, (-p.1, -p.2)⟩
instance : inhabited point :=
  ⟨(0, 0)⟩


-- NOTE: This is the *squared* ℓ₂ norm.  It should be fine for our purposes,
-- because it's a monotonic isomorphism, but we should think some more to make
-- sure.
-- instance : has_norm point :=
--   ⟨λ p, ⟩

#check ℕ

-- lemma coe_nat_to_int_preserves_leq :
--   ∀ (x y : ℕ), x ≤ y → (↑x : ℤ) ≤ (↑y : ℤ)
--   :=
--   begin
--     sorry
--   end

-- lemma coe_nat_times_coe_nat_eq_coe_nat_times_nat :
--   ∀ (x y : ℕ), x ≤ y → (↑x : ℤ) ≤ (↑y : ℤ)


-- lemma square_positive : ∀ (x : ℤ), x * x ≥ 0 :=
-- begin
--   intros x,
--   cases x,
--   simp [int.mul],
--   apply sq_nonneg,
--   sorry,
--   sorry
-- end

-- lemma pos_implies_of_nat : ∀ (x : ℤ), (0 ≤ x) → (∃ (n : ℕ), (x = int.of_nat n)) :=
-- begin
--   intros x x_nonneg,
--   cases x,
--   apply exists.intro x,
--   refl,
--   simp at x_nonneg,
--   contradiction
-- end

-- NOTE: We don't want to use the `has_norm` typeclass, because that asserts the
-- result is a real.
def point_norm (p : point) : ℤ :=
  p.1 * p.1 + p.2 * p.2

notation `∥` e `∥` := point_norm e

lemma int_nonneg_add :
  ∀ (x y : ℤ), int.nonneg x → int.nonneg y → int.nonneg (x + y) := begin
    sorry
end

lemma int_x_times_x_nonneg :
  ∀ (x : ℤ), int.nonneg (x * x) := begin
    sorry
end

lemma nonneg_iff_leq_zero :
  ∀ (x : ℤ), int.nonneg x ↔ 0 ≤ x := begin
    sorry
  end

lemma a_nonneg_times_b_nonneq_means_a_times_b_nonneg :
  ∀ (a b : ℤ), int.nonneg a → int.nonneg b → int.nonneg (a * b) := begin
    sorry
end

lemma lift_nat_nonneg :
  ∀ (n : ℕ), int.nonneg ↑n := begin
    sorry
end

lemma x_div_plus_y_div_eq_x_plus_y_div_minus_sum_mod_div :
  ∀ (x y z : ℤ), x/z + y/z = (x + y)/z - (x % z + y % z) := begin
    sorry
  end

lemma x_div_y_times_y :
  ∀ (x y : ℤ), (x / y) * y = x - x % y := begin
    sorry
end

lemma point_norm_nonneg :
  ∀ (p : point), int.nonneg (∥ p ∥) := begin
    intros p,
    unfold point_norm,
    apply int_nonneg_add,
    apply int_x_times_x_nonneg,
    apply int_x_times_x_nonneg
end

lemma point_norm_add_comm :
  ∀ (p q : point), ∥ p + q ∥ = ∥ q + p ∥ := begin
    sorry
end

lemma point_norm_sub_comm :
  ∀ (p q : point), ∥ p - q ∥ = ∥ q - p ∥ := begin
    sorry
end

lemma not_leq_and_gt : ∀ (p : point) (n : ℤ),
  ¬((∥p∥ ≤ n) ∧ (n < ∥p∥)) := begin
    sorry
end


-- lemma sum_nonneg_nonneg :
--   ∀ (x y : ℚ), (x ≥ 0) → (y ≥ 0) → (x + y ≥ 0) :=
--   begin
--     intros p q p_nonneg q_nonneg,

--   end



/-
def point_norm (p : point) : ℚ :=
  p.1 * p.1 + p.2 * p.2

notation `∥` e `∥` := point_norm e

lemma x_times_x_nonneg :
  ∀ (x : ℚ), rat.nonneg (x * x) := begin
    sorry
end

lemma point_norm_nonneg :
  ∀ (p : point), rat.nonneg ∥ p ∥ := begin
    intros p,
    unfold point_norm,
    apply rat.nonneg_add,
    apply x_times_x_nonneg,
    apply x_times_x_nonneg
  end
-/

#eval ((1, 2) : point) + ((-3, -4) : point)

-- def point_hash : point → ℕ
-- | (a, b) := a.num.nat_abs * a.denom * b.num.nat_abs * b.denom
def point_hash : point → ℕ
| (a, b) := a.nat_abs + b.nat_abs

#eval point_hash (1, 4)
