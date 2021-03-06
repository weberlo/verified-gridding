import data.hash_map
import data.nat.basic
import data.rat.basic
import data.real.basic
import data.real.sqrt
import data.rat.sqrt
import analysis.normed.group.basic

import core.util
import core.point
import core.grid

def pt_in_ball (p q : point) (c : ℕ⁺) (qs : list point) : Prop :=
  q ∈ qs ∧
  q ≠ p ∧
  ∥q - p∥ ≤ c

-- def min_dist_pair_aux : list (point × ℚ) → option (point × ℚ)
-- | [] := none
-- | ((p, d) :: pds) :=
--     match min_dist_pair_aux pds with
--     | none :=
--         some (p, d)
--     | some (p', d') :=
--         some (if d < d' then (p, d) else (p', d'))
--     end

-- def min_dist_pair : list (point × ℚ) → option point
-- | [] := none
-- | pds := min_dist_pair_aux pds >>= (λ (p : point × ℚ), some p.1)

def min_dist_pair (p : point) : list point → option (point × point)
| [] := none
| (q :: ps') :=
    let pq' := min_dist_pair ps' in
    if point_lt' (p, q) pq' then some (p, q) else pq'

/-
  All points within distance `c` from the current point are included in the list.
-/

/-
  Get minimum distance pair, wrt the grid `g`, with `p` as the center of the
  pair, and only considering the neighbors of `p`.
-/
def mdp_with (p : point) (g : grid_2D) : option (point × point) :=
  let ps := get_neighbs p g in
  min_dist_pair p ps

lemma range_in_hypercube :
  ∀ (i j : ℤ) (n : ℕ),
    ((-(↑n) ≤ i) ∧ (i ≤ n) ∧
     (-(↑n) ≤ j) ∧ (j ≤ n))
    ↔
    (i, j) ∈ (get_hypercube n) := sorry

lemma norm_bd_on_coords :
  ∀ (a b : ℤ) (c : ℕ),
    ∥(a, b)∥ ≤ c →
    a*a ≤ c ∧ b*b ≤ c := sorry
  -- (Something bounding `a` and `b` below and above by (+|-)nat.sqrt(c) (not sure whether inclusive or exclusive))

-- lemma nat_sqrt_plus_one_sq_gt_nat :
--   ∀ (c : ℕ),
--     ((nat.sqrt c) + 1)*((nat.sqrt c) + 1) > c := sorry

lemma sq_neg_lt :
  ∀ (a b : ℤ),
    a ≤ 0 →
    b ≤ 0 →
    a < b →
    b*b < a*a := begin
  intros a b h1 h2 h3,
  sorry
end

lemma sq_nonneg_lt :
  ∀ (a b : ℤ),
    a ≥ 0 →
    b ≥ 0 →
    a < b →
    a*a < b*b := begin
  intros a b h1 h2 h3,
  exact mul_lt_mul'' h3 h3 h1 h1,
end

lemma nat_ge_zero :
  ∀ (n : ℕ), n ≥ 0 := begin
  intros n,
  linarith,
end

lemma ge_neg_le :
  ∀ (n : ℤ),
    n ≥ 0 →
    -n ≤ 0 := begin
  intros n h,
  linarith,
end

lemma coe_nat_int_ge :
  ∀ (n : ℕ),
  n ≥ 0 →
  (↑n : ℤ) ≥ 0 := begin
  intros n h,
  simp [h],
end

lemma lt_to_le :
  ∀ (a b : ℤ),
    a < b → a ≤ b := begin
  intros a b h,
  linarith,
end

lemma neg_sq_sq :
  ∀ (a : ℤ),
    (-a)*(-a) = a*a := begin
  intros a,
  ring,
end

lemma succ_sqrt_sq_gt_orig :
  ∀ (c : ℕ),
    ((nat.sqrt c) + 1) * ((nat.sqrt c) + 1) > c := begin
  intros c,
  exact nat.lt_succ_sqrt c,
end

lemma coe_preserves_lt :
  ∀ (a b : ℕ),
    a < b →
    (↑a : ℤ) < ↑b := begin
  intros a b h,
  simp [h],
end

lemma coe_preserves_ge :
  ∀ (a b : ℕ),
    a ≥ b →
    (↑a : ℤ) ≥ ↑b := begin
  intros a b h,
  linarith,
end

lemma coe_nat_nat_nop :
  ∀ (n : ℕ),
    (↑n : ℕ) = n := begin
  intros n,
  simp,
end

lemma bounded_norm_in_hypercube:
  ∀ (ab : ℤ × ℤ) (c : ℕ),
    ∥ab∥ ≤ c →
    (ab ∈ get_hypercube ((nat.sqrt c) + 1)) := begin
  intros ab c ab_le_c,
  cases ab with a b,
  apply (range_in_hypercube a b ((nat.sqrt c) + 1)).mp,
  split,
  {
    by_cases h : -↑((nat.sqrt c) + 1) ≤ a,
    assumption,
    simp at h,
    have a_sq_le_c_and_b_sq_le_c: a*a ≤ c ∧ b*b ≤ c := begin
      apply norm_bd_on_coords,
      assumption,
    end,
    have h : a < -(↑(nat.sqrt c) + 1) := begin
      simp,
      rw [add_comm],
      exact h,
    end,
    have sq_succ_sqrt_lt_sq_a : -(↑(nat.sqrt c) + 1) * -(↑(nat.sqrt c) + 1) < a * a := begin
      apply sq_neg_lt,
      {
        have succ_sqrt_ge_zero : ↑(nat.sqrt c) + 1 ≥ 0 := begin
          apply nat_ge_zero,
        end,
        have neg_succ_sqrt_le_zero : -(↑(↑(nat.sqrt c) + 1) : ℤ) ≤ 0 := begin
          apply ge_neg_le,
          apply coe_nat_int_ge,
          assumption,
        end,
        have h_le : a ≤ -(↑(nat.sqrt c) + 1) := begin
          apply lt_to_le,
          assumption,
        end,
        apply le_trans,
        exact h_le,
        simp at *,
        exact neg_succ_sqrt_le_zero,
      },
      {
        have succ_sqrt_ge_zero : ↑(nat.sqrt c) + 1 ≥ 0 := begin
          apply nat_ge_zero,
        end,
        have neg_succ_sqrt_le_zero : -(↑(↑(nat.sqrt c) + 1) : ℤ) ≤ 0 := begin
          apply ge_neg_le,
          apply coe_nat_int_ge,
          assumption,
        end,
        simp at *,
        exact neg_succ_sqrt_le_zero,
      },
      {
        exact h,
      },
    end,
    rw [neg_sq_sq] at sq_succ_sqrt_lt_sq_a,
    have succ_sqrt_c_sq_gt_c : ((nat.sqrt c) + 1) * ((nat.sqrt c) + 1) > c := begin
      apply succ_sqrt_sq_gt_orig,
    end,
    cases a_sq_le_c_and_b_sq_le_c with a_sq_le_c b_sq_le_c,
    have c_lt_a_sq : (↑c : ℤ) < a*a := begin
      fapply lt_trans,
      exact ↑((nat.sqrt c + 1) * (nat.sqrt c + 1)),
      simp at succ_sqrt_c_sq_gt_c,
      apply coe_preserves_lt,
      assumption,
      simp,
      assumption,
    end,
    exfalso,
    apply not_le_and_gt,
    split,
    exact a_sq_le_c,
    exact c_lt_a_sq,
  },
  split,
  {
    by_cases h : a ≤ ↑(nat.sqrt c + 1),
    { assumption, },
    simp at h,
    have a_sq_le_c_and_b_sq_le_c: a*a ≤ c ∧ b*b ≤ c := begin
      apply norm_bd_on_coords,
      assumption,
    end,
    have sq_succ_sqrt_lt_sq_a : (↑(nat.sqrt c) + 1) * (↑(nat.sqrt c) + 1) < a * a := begin
      apply sq_nonneg_lt,
      {
        have succ_sqrt_ge_zero : ↑(nat.sqrt c) + 1 ≥ 0 := begin
          apply nat_ge_zero,
        end,
        apply coe_preserves_ge,
        rw [coe_nat_nat_nop] at succ_sqrt_ge_zero,
        exact succ_sqrt_ge_zero,
      },
      {
        have succ_sqrt_ge_zero : ↑(nat.sqrt c) + 1 ≥ 0 := begin
          apply nat_ge_zero,
        end,
        fapply le_trans,
        exact (↑(nat.sqrt c) + 1),
        simp only [ge] at succ_sqrt_ge_zero,
        apply coe_preserves_ge,
        rw [coe_nat_nat_nop] at succ_sqrt_ge_zero,
        exact succ_sqrt_ge_zero,
        apply lt_to_le,
        exact h,
      },
      {
        exact h,
      },
    end,
    have succ_sqrt_c_sq_gt_c : ((nat.sqrt c) + 1) * ((nat.sqrt c) + 1) > c := begin
      apply succ_sqrt_sq_gt_orig,
    end,
    cases a_sq_le_c_and_b_sq_le_c with a_sq_le_c b_sq_le_c,
    have c_lt_a_sq : (↑c : ℤ) < a*a := begin
      fapply lt_trans,
      exact ↑((nat.sqrt c + 1) * (nat.sqrt c + 1)),
      simp at succ_sqrt_c_sq_gt_c,
      apply coe_preserves_lt,
      assumption,
      simp,
      assumption,
    end,
    exfalso,
    apply not_le_and_gt,
    split,
    exact a_sq_le_c,
    exact c_lt_a_sq,
  },
  split,
  {
    by_cases h : -↑((nat.sqrt c) + 1) ≤ b,
    assumption,
    simp at h,
    have a_sq_le_c_and_b_sq_le_c: a*a ≤ c ∧ b*b ≤ c := begin
      apply norm_bd_on_coords,
      assumption,
    end,
    have h : b < -(↑(nat.sqrt c) + 1) := begin
      simp,
      rw [add_comm],
      exact h,
    end,
    have sq_succ_sqrt_lt_sq_a : -(↑(nat.sqrt c) + 1) * -(↑(nat.sqrt c) + 1) < b * b := begin
      apply sq_neg_lt,
      {
        have succ_sqrt_ge_zero : ↑(nat.sqrt c) + 1 ≥ 0 := begin
          apply nat_ge_zero,
        end,
        have neg_succ_sqrt_le_zero : -(↑(↑(nat.sqrt c) + 1) : ℤ) ≤ 0 := begin
          apply ge_neg_le,
          apply coe_nat_int_ge,
          assumption,
        end,
        have h_le : b ≤ -(↑(nat.sqrt c) + 1) := begin
          apply lt_to_le,
          assumption,
        end,
        apply le_trans,
        exact h_le,
        simp at *,
        exact neg_succ_sqrt_le_zero,
      },
      {
        have succ_sqrt_ge_zero : ↑(nat.sqrt c) + 1 ≥ 0 := begin
          apply nat_ge_zero,
        end,
        have neg_succ_sqrt_le_zero : -(↑(↑(nat.sqrt c) + 1) : ℤ) ≤ 0 := begin
          apply ge_neg_le,
          apply coe_nat_int_ge,
          assumption,
        end,
        simp at *,
        exact neg_succ_sqrt_le_zero,
      },
      {
        exact h,
      },
    end,
    rw [neg_sq_sq] at sq_succ_sqrt_lt_sq_a,
    have succ_sqrt_c_sq_gt_c : ((nat.sqrt c) + 1) * ((nat.sqrt c) + 1) > c := begin
      apply succ_sqrt_sq_gt_orig,
    end,
    cases a_sq_le_c_and_b_sq_le_c with a_sq_le_c b_sq_le_c,
    have c_lt_a_sq : (↑c : ℤ) < b*b := begin
      fapply lt_trans,
      exact ↑((nat.sqrt c + 1) * (nat.sqrt c + 1)),
      simp at succ_sqrt_c_sq_gt_c,
      apply coe_preserves_lt,
      assumption,
      simp,
      assumption,
    end,
    exfalso,
    apply not_le_and_gt,
    split,
    exact b_sq_le_c,
    exact c_lt_a_sq,
  },
  {
    by_cases h : b ≤ ↑(nat.sqrt c + 1),
    { assumption, },
    simp at h,
    have a_sq_le_c_and_b_sq_le_c: a*a ≤ c ∧ b*b ≤ c := begin
      apply norm_bd_on_coords,
      assumption,
    end,
    have sq_succ_sqrt_lt_sq_a : (↑(nat.sqrt c) + 1) * (↑(nat.sqrt c) + 1) < b*b := begin
      apply sq_nonneg_lt,
      {
        have succ_sqrt_ge_zero : ↑(nat.sqrt c) + 1 ≥ 0 := begin
          apply nat_ge_zero,
        end,
        apply coe_preserves_ge,
        rw [coe_nat_nat_nop] at succ_sqrt_ge_zero,
        exact succ_sqrt_ge_zero,
      },
      {
        have succ_sqrt_ge_zero : ↑(nat.sqrt c) + 1 ≥ 0 := begin
          apply nat_ge_zero,
        end,
        fapply le_trans,
        exact (↑(nat.sqrt c) + 1),
        simp only [ge] at succ_sqrt_ge_zero,
        apply coe_preserves_ge,
        rw [coe_nat_nat_nop] at succ_sqrt_ge_zero,
        exact succ_sqrt_ge_zero,
        apply lt_to_le,
        exact h,
      },
      {
        exact h,
      },
    end,
    have succ_sqrt_c_sq_gt_c : ((nat.sqrt c) + 1) * ((nat.sqrt c) + 1) > c := begin
      apply succ_sqrt_sq_gt_orig,
    end,
    cases a_sq_le_c_and_b_sq_le_c with a_sq_le_c b_sq_le_c,
    have c_lt_a_sq : (↑c : ℤ) < b*b := begin
      fapply lt_trans,
      exact ↑((nat.sqrt c + 1) * (nat.sqrt c + 1)),
      simp at succ_sqrt_c_sq_gt_c,
      apply coe_preserves_lt,
      assumption,
      simp,
      assumption,
    end,
    exfalso,
    apply not_le_and_gt,
    split,
    exact b_sq_le_c,
    exact c_lt_a_sq,
  }
end

lemma in_ball_exists_idx :
  ∀ (p q : point) (c : ℕ⁺) (qs : list point),
    pt_in_ball p q c qs →
    (∃ (a b : ℤ),
      (∥(a, b)∥ ≤ c) ∧ (p + (a, b) = q)) := sorry

lemma q_in_ball_means_grid_idx_in_get_idxs :
  ∀ (p q : point) (c : ℕ⁺) (qs : list point),
  pt_in_ball p q c qs →
  (get_grid_idx q) ∈ (get_idxs p c) := begin
  intros p q c qs q_in_p_ball,
  have exists_idx : (∃ (a b : ℤ), (∥(a, b)∥ ≤ c) ∧ (p + (a, b) = q)) := begin
    apply in_ball_exists_idx,
    assumption,
  end,
  cases exists_idx with a exists_idx,
  cases exists_idx with b exists_idx,
  unfold pt_in_ball at q_in_p_ball,
  cases q_in_p_ball with q_in_qs q_ne_p_and_bded_norm,
  cases q_ne_p_and_bded_norm with q_ne_p q_bded_norm,
  simp [point_norm] at q_bded_norm,
  simp [get_idxs, get_grid_idx],
  fapply exists.intro,
  exact a,
  fapply exists.intro,
  exact b,
  split,
  {
    apply bounded_norm_in_hypercube,
    exact exists_idx.left,
  },
  {
    exact exists_idx.right,
  }
end

lemma x_in_some_l_x_in_join_ls :
  ∀ (x : point) (ls : list (list point)),
    (∃ (l : list point), x ∈ l ∧ l ∈ ls) →
    x ∈ ls.join := sorry

lemma x_in_grid_idxs_x_in_find_res :
  ∀ (p x : point) (g : grid_2D),
    (get_grid_idx x ∈ get_idxs p g.c) →
    (∃ l, (in_opt_list x l) ∧ (l ∈ (get_idxs p g.c).map g.data.find)) := sorry

lemma some_l_in_ls_l_in_lift :
  ∀ {α} (l : list α) (ls : list (option (list α))),
    some l ∈ ls →
    l ∈ list.map lift_option_list ls := begin
  sorry
end

lemma get_neighbs_gets_neighbs :
  ∀ (p : point) (g : grid_2D),
    ∀ (x : point),
      (pt_in_ball p x g.c g.ps) →
      (x ∈ get_neighbs p g) := begin
  intros p g x x_in_ball,
  simp only [get_neighbs],
  have grid_idx_x_in_idxs : (get_grid_idx x) ∈ (get_idxs p g.c) := begin
    apply q_in_ball_means_grid_idx_in_get_idxs,
    assumption,
  end,
  apply (list.mem_filter.mpr),
  split,
  {
    apply x_in_some_l_x_in_join_ls,
    have x_in_opt_list : (∃ l, (in_opt_list x l) ∧ (l ∈ (get_idxs p g.c).map g.data.find)) := begin
      apply x_in_grid_idxs_x_in_find_res,
      assumption,
    end,
    cases x_in_opt_list with l x_in_opt_list,
    cases x_in_opt_list with x_in_opt_list l_in_res,
    cases l,
    { cases x_in_opt_list, },
    fapply exists.intro,
    exact l,
    split,
    unfold in_opt_list at x_in_opt_list,
    assumption,
    apply some_l_in_ls_l_in_lift,
    assumption,
  },
  {
    unfold pt_in_ball at x_in_ball,
    exact x_in_ball.right.left,
  },
end

lemma min_dist_pair_closest :
  ∀ (p : point) (ps : list point),
    ∀ (x : point),
      (x ∈ ps) →
      (min_dist_pair p ps ≤ some (p, x)) :=
begin
  sorry
end

-- lemma min_dist_pair_includes_center :
--   ∀ (p : point) (ps : list point),
--     (∃ (z w : point), min_dist_pair p ps = some (z, w)) →
--     (∃ (q : point), min_dist_pair p ps = some (p, q)) := begin
--   sorry
-- end

-- lemma pt_in_ball_mdp_is_some :
--   ∀ (p : point) (g : grid_2D),
--     (∃ (x : point), pt_in_ball p x g.c g.ps) →
--     (∃ (x : point), mdp_with p g = some (p, x)) := begin
--   intros p g exists_x_in_ball,
--   simp [mdp_with],
--   cases exists_x_in_ball with x exists_x_in_ball,
--   have x_in_neighbs : x ∈ get_neighbs p g := begin
--     apply get_neighbs_gets_neighbs,
--     assumption,
--   end,
--   have mdp_le_px : min_dist_pair p (get_neighbs p g) ≤ some (p, x) := begin
--     apply min_dist_pair_closest,
--     assumption,
--   end,
--   have mdp_is_some : ∃ (z w : point), min_dist_pair p (get_neighbs p g) = some (z, w) := begin
--     apply option_pt_le_some_eq_some,
--     exact mdp_le_px,
--   end,
--   apply min_dist_pair_includes_center,
--   assumption,
-- end

lemma get_min_dist_pair_correct :
  ∀ (p : point) (g : grid_2D),
    ∀ (x : point),
      (pt_in_ball p x g.c g.ps) →
      ((mdp_with p g) ≤ some (p, x)) := begin
  intros p g x x_in_ball,
  simp [mdp_with],
  apply min_dist_pair_closest,
  apply get_neighbs_gets_neighbs,
  assumption,
end

lemma min_dist_pair_in_ball :
  ∀ (p q : point) (g : grid_2D),
    (mdp_with p g = some (p, q)) →
    pt_in_ball p q g.c g.ps := begin
  sorry
end

-- lemma get_neighbs_contains_all_within_ball :
--   ∀ (c : ℕ⁺) (ps : list point) (p q : point) (g : grid_2D),
--     (∥ p - q ∥ ≤ c) →
--     (q ∈ get_neighbs p g) := begin
--   sorry
-- end


def aux (g : grid_2D) : list point → option (point × point)
| [] := none
| (p :: ps) :=
    let rec_res := aux ps in
    let curr_res := mdp_with p g in
    -- TODO figure out why we can't get decidable to work on `point_le`.
    if point_lt' curr_res rec_res then curr_res else rec_res


/-
We can only get `none` if `c` wasn't actually a valid hint.
-/
def find_closest_pair
  (c : ℕ⁺)
  (points : list point)
  : option (point × point) :=
  let g := grid_points c points in
  aux g points >>= (
    λ pq : point × point,
      if ∥ pq.1 - pq.2 ∥ > c
      then none
      else some pq
  )


#eval find_closest_pair ⟨3, by simp⟩ [(0, 0), (2, 0), (5, 0)]
#eval find_closest_pair ⟨4, by simp⟩ [(0, 0), (2, 0), (5, 0)]
#eval find_closest_pair ⟨7, by simp⟩ [(0, 0), (2, 2), (5, 0)]
#eval find_closest_pair ⟨8, by simp⟩ [(0, 0), (2, 2), (5, 0)]

def closest_pair (p q : point) (ps : list point) : Prop :=
  (p ∈ ps) ∧
  (q ∈ ps) ∧
  (p ≠ q) ∧
  (∀ (r s : point), r ≠ s → ∥p - q∥ ≤ ∥r - s∥)

/-
  Closest pair with help
-/
def cp_with_help (p q : point) (ps : list point) (c : ℕ⁺) : Prop :=
  (closest_pair p q ps) ∧ (1 < ∥ p - q ∥) ∧ (∥ p - q ∥ ≤ c)

inductive closest_pair_in_ball_union (c : ℕ⁺) (qs : list point) : option (point × point) → list point → Prop
| no_ball : closest_pair_in_ball_union none []
| cons_ball_no_update (xy : option (point × point)) (p : point) (ps' : list point) :
    closest_pair_in_ball_union xy ps' →
    (∀ (q : point),
      pt_in_ball p q c qs →
      (xy ≤ some (p, q))) →
    closest_pair_in_ball_union xy (p :: ps')
| cons_ball_update
    (xy : option (point × point))
    (p : point)
    (ps' : list point)
    (q : point) :
    (
      pt_in_ball p q c qs ∧
      (∀ (x : point), (pt_in_ball p x c qs) → ∥q - p∥ ≤ ∥x - p∥) ∧
      some (p, q) < xy
    ) →
    closest_pair_in_ball_union xy ps' →
    closest_pair_in_ball_union (some (p, q)) (p :: ps')


lemma point_lt_iff_point_lt'_eq_true :
  ∀ (xy zw : option (point × point)),
    xy < zw ↔ (point_lt' xy zw = true) := begin
  intros xy zw,
  constructor,
  sorry,
  sorry,
end

lemma opt_point_le_some_implies_is_some :
  ∀ (xy : option (point × point)) (z w : point),
    xy ≤ some (z, w) ↔ (∃ (x y : point), xy = some (x, y)) := begin
  sorry,
end

lemma get_mdp_includes_center_pt :
  ∀ (p : point) (g : grid_2D),
    (∃ (q : point), (mdp_with p g) = some (p, q)) ∨
    (mdp_with p g) = none := begin
  sorry
end

lemma closer_than_pt_in_ball_is_in_ball :
  ∀ (p x y : point) (c : ℕ⁺) (qs : list point),
    pt_in_ball p y c qs →
    some (p, x) ≤ some (p, y) →
    pt_in_ball p x c qs := begin
  sorry
end

lemma aux_monotonic_in_pt_list :
  ∀ (c : ℕ⁺) (g : grid_2D) (p : point) (ps' : list point),
    (aux g (p :: ps')) ≤ (aux g ps')
     := begin
  intros c qs ps' p,
  sorry,
end

lemma cp_in_ball_union_downward_closed :
  ∀ (c : ℕ⁺) (xy zw : option (point × point)) (qs ps : list point),
    closest_pair_in_ball_union c qs zw ps →
    xy ≤ zw →
    closest_pair_in_ball_union c qs xy ps
     := begin
  sorry,
end

lemma pt_in_ball_subset_to_pt_in_ball :
  ∀ (ps' ps : list point) (p q : point) (c : ℕ⁺),
    pt_in_ball p q c ps' →
    ps' ⊆ ps →
    pt_in_ball p q c ps := sorry


lemma aux_finds_closest_pair_in_ball_union:
  ∀ (g : grid_2D),
    -- `aux` finds the closest pair in union of balls of radius ≤ `c`
    -- (intersected with `qs`) around all points in `ps`.
    (∀ (ps : list point),
      ps ⊆ g.ps →
      closest_pair_in_ball_union g.c g.ps (aux g ps) ps) := begin
  intros g ps ps_subseteq_qs,
  induction ps,
  {
    apply closest_pair_in_ball_union.no_ball,
  },
  {
    rename [ps_hd → p, ps_tl → ps'],
    have ps'_subseteq_qs : ps' ⊆ g.ps :=
      (list.cons_subset.mp ps_subseteq_qs).right,
    have ih : closest_pair_in_ball_union g.c g.ps (aux g ps') ps' := ps_ih ps'_subseteq_qs,
    clear ps_ih,
    by_cases (
      ∃ (q : point),
        pt_in_ball p q g.c g.ps ∧
        (∀ (x : point), pt_in_ball p x g.c g.ps → ∥ q - p ∥ ≤ ∥ x - p ∥) ∧
        some (p, q) < (aux g ps')),
    -- Case: there is a point within a ball of `p` that is closer than the
    -- recursive result.
    {
      -- Load up the environment with useful facts.
      cases h with q hq,
      have h_min_dist_pair : ∀ (x : point), (pt_in_ball p x g.c g.ps) → ((mdp_with p g) ≤ some (p, x)) := begin
        intros x x_in_ball,
        apply get_min_dist_pair_correct,
        assumption,
      end,
      have min_dist_pair_closer_than_q : mdp_with p g ≤ some (p, q) := begin
        exact h_min_dist_pair q hq.left,
      end,
      have min_dist_pair_closer_than_rec_res : mdp_with p g < aux g ps' := begin
        apply option_pt_le_lt_trans,
        assumption,
        exact hq.right.right,
      end,
      have min_dist_pair_closer_than_rec_res_bool :
        point_lt'
          (mdp_with p g)
          (aux g ps') = true :=
        (point_lt_iff_point_lt'_eq_true (mdp_with p g) (aux g ps')).mp min_dist_pair_closer_than_rec_res,
      simp [aux, min_dist_pair_closer_than_rec_res_bool],
      have md_pair_is_some: (∃ (x y : point), mdp_with p g = some (x, y)) := begin
        exact ((opt_point_le_some_implies_is_some (mdp_with p g) p q).mp min_dist_pair_closer_than_q),
      end,
      cases md_pair_is_some with x md_pair_is_some',
      cases md_pair_is_some' with y md_pair_is_some'',
      rw [md_pair_is_some''],
      have x_eq_p : x = p := begin
        have md_pair_disj :
          (∃ (z : point), mdp_with p g = some (p, z)) ∨
          mdp_with p g = none := begin
          exact (get_mdp_includes_center_pt p g),
        end,
        cases md_pair_disj,
        {
          cases md_pair_disj with z hz,
          rw [md_pair_is_some''] at hz,
          cases hz,
          refl,
        },
        {
          rw [md_pair_is_some''] at md_pair_disj,
          cases md_pair_disj,
        },
      end,
      rw [x_eq_p] at *,

      fapply closest_pair_in_ball_union.cons_ball_update,
      exact (aux g ps'),
      {
        constructor,
        {
          rw [md_pair_is_some''] at min_dist_pair_closer_than_q,
          apply closer_than_pt_in_ball_is_in_ball,
          exact hq.left,
          assumption,
        },
        constructor,
        {
          intros z z_in_ball,
          have q_closer_than_z : ∥q - p∥ ≤ ∥z - p∥ := hq.right.left z z_in_ball,
          have y_closer_than_q : ∥y - p∥ ≤ ∥q - p∥ := begin
            rw [md_pair_is_some''] at min_dist_pair_closer_than_q,
            simp [has_le.le, point_le] at min_dist_pair_closer_than_q ⊢,
            rw point_norm_symm y p,
            rw point_norm_symm q p,
            assumption,
          end,
          exact le_trans y_closer_than_q q_closer_than_z,
        },
        {
          rw [md_pair_is_some''] at min_dist_pair_closer_than_q,
          apply option_pt_le_lt_trans,
          exact min_dist_pair_closer_than_q,
          exact hq.right.right,
        },
      },
      {
        exact ih,
      },
    },
    -- Case: there is *no* point within a ball of `p` that is closer than the
    -- recursive result.
    {
      apply closest_pair_in_ball_union.cons_ball_no_update,
      {
        apply cp_in_ball_union_downward_closed,
        exact ih,
        apply aux_monotonic_in_pt_list,
        exact g.c,
      },
      {
        intros q q_in_ball,
        have mdp_p_closest : ∀ (x : point), pt_in_ball p x g.c g.ps → (mdp_with p g) ≤ some (p, x) := begin
          apply get_min_dist_pair_correct,
        end,
        -- aux ps' ≤ mdp p
        -- intuitively, by `h`
        have aux_ps'_le_mdp_p : aux g ps' ≤ mdp_with p g := begin
          by_cases aux_ps'_le_mdp_p : aux g ps' ≤ mdp_with p g,
          { assumption, },
          {
            have mdp_p_lt_aux_ps' : mdp_with p g < aux g ps' :=
              (neg_le_iff_lt (aux g ps') (mdp_with p g)).mp aux_ps'_le_mdp_p,
            have mdp_p_eq_some_p_z_or_none : (∃ (y : point), mdp_with p g = some (p, y)) ∨ (mdp_with p g) = none := get_mdp_includes_center_pt p g,
            have mdp_p_eq_some : ∃ (z w : point), mdp_with p g = some (z, w) := begin
               apply option_pt_le_some_eq_some,
               apply get_min_dist_pair_correct,
               apply pt_in_ball_subset_to_pt_in_ball,
               exact q_in_ball,
               refl,
            end,
            have mdp_p_eq_some : (∃ (y : point), mdp_with p g = some (p, y)) := begin
              cases mdp_p_eq_some with z mdp_p_eq_some',
              cases mdp_p_eq_some' with w mdp_p_eq_some'',
              cases mdp_p_eq_some_p_z_or_none,
              { assumption, },
              {
                 rw [mdp_p_eq_some_p_z_or_none] at mdp_p_eq_some'',
                 contradiction,
              },
            end,
            cases mdp_p_eq_some with y mdp_p_eq_some',
            have h_premise :
              pt_in_ball p y g.c g.ps ∧
              (∀ (x : point), pt_in_ball p x g.c g.ps → ∥y - p∥ ≤ ∥x - p∥) ∧
              some (p, y) < aux g ps' := begin
                rw [mdp_p_eq_some'] at mdp_p_closest,
                simp only [has_le.le, point_le] at mdp_p_closest ⊢,
                rw [point_norm_sub_comm p y] at mdp_p_closest,
                have mdp_p_closest' : ∀ (x : point), (pt_in_ball p x g.c g.ps) → (∥y - p∥.le ∥x - p∥) := begin
                  intros x,
                  rw [point_norm_sub_comm x p],
                  apply mdp_p_closest,
                end,
                have mdp_p_in_ball : pt_in_ball p y g.c g.ps := begin
                  apply min_dist_pair_in_ball,
                  exact mdp_p_eq_some',
                end,
                rw [mdp_p_eq_some'] at mdp_p_lt_aux_ps',
                constructor,
                exact mdp_p_in_ball,
                constructor,
                exact mdp_p_closest',
                exact mdp_p_lt_aux_ps',
            end,
            exfalso,
            apply h,
            fapply exists.intro,
            exact y,
            exact h_premise,
          },
        end,
        -- mdp p ≤ q
        -- intuitively, by univ property of `mdp` given by `mdp_correct` lemma
        have mdp_p_le_q : mdp_with p g ≤ some (p, q) := begin
          apply mdp_p_closest,
          apply pt_in_ball_subset_to_pt_in_ball,
          exact q_in_ball,
          refl,
        end,
        -- ¬(mdp p < aux ps')
        have mdp_not_lt_aux : ¬(point_lt'
          (mdp_with p g)
          (aux g ps')) := begin
          intros mdp_p_lt_aux_ps',
          apply not_x_le_y_and_gt_y,
          exact aux_ps'_le_mdp_p,
          simp [has_lt.lt],
          exact ((point_lt_iff_point_lt' _ _).mpr mdp_p_lt_aux_ps'),
        end,
        simp [aux, mdp_not_lt_aux],
        apply option_pt_le_trans,
        exact aux_ps'_le_mdp_p,
        exact mdp_p_le_q,
      }
    }
  },
end

-- lemma cp_in_ball_union_in_ps :
--   ∀ (c : ℕ⁺) (z w : point) (ps qs : list point),
--     closest_pair_in_ball_union c qs (some (z, w)) ps →
--     z ∈ ps := sorry

lemma cp_in_ball_union_closer_than_all_pts_in_dist_c :
  ∀ (c : ℕ⁺) (r s : point) (zw : option (point × point)) (ps qs : list point),
    ps ⊆ qs →
    r ∈ ps →
    pt_in_ball r s c qs →
    closest_pair_in_ball_union c qs zw ps →
    zw ≤ some (r, s) := begin
  intros
    c r s zw ps qs
    ps_subset_qs r_in_ps s_in_r_ball zw_cp_in_balls,
  induction zw_cp_in_balls,
  {
    cases r_in_ps,
  },
  {
    rename [
      zw_cp_in_balls_xy → zw,
      zw_cp_in_balls_p → p,
      zw_cp_in_balls_ps' → ps',
      zw_cp_in_balls_ᾰ → zw_cp_in_union_ps'_balls,
      zw_cp_in_balls_ᾰ_1 → zw_closest_in_p_ball,
      zw_cp_in_balls_ih → ih
    ],
    cases r_in_ps,
    {
      rw [r_in_ps] at *,
      apply zw_closest_in_p_ball,
      assumption,
    },
    {
      have ps_decomp : p ∈ qs ∧ ps' ⊆ qs := begin
        apply list.cons_subset.mp,
        assumption,
      end,
      apply ih,
      exact ps_decomp.right,
      exact r_in_ps,
    }
  },
  {
    rename [
      zw_cp_in_balls_xy → zw',
      zw_cp_in_balls_p → p,
      zw_cp_in_balls_ps' → ps',
      zw_cp_in_balls_q → q,
      zw_cp_in_balls_ᾰ → q_closest_in_p_ball_and_pq_le_zw',
      zw_cp_in_balls_ᾰ_1 → zw_cp_in_union_ps'_balls,
      zw_cp_in_balls_ih → ih
    ],
    cases r_in_ps,
    {
      rw [r_in_ps] at *,
      simp [has_le.le, point_le],
      rw [point_norm_sub_comm p q, point_norm_sub_comm p s],
      apply q_closest_in_p_ball_and_pq_le_zw'.right.left,
      assumption,
    },
    {
      apply option_pt_lt_to_le,
      apply option_pt_lt_le_trans,
      exact q_closest_in_p_ball_and_pq_le_zw'.right.right,
      have ps_decomp : p ∈ qs ∧ ps' ⊆ qs := begin
        apply list.cons_subset.mp,
        assumption,
      end,
      apply ih,
      exact ps_decomp.right,
      exact r_in_ps,
    }
  }
end

lemma some_cp_in_balls_in_pt_list_and_neq :
  ∀ (c : ℕ⁺) (x y : point) (xy : option (point × point)) (ps : list point),
    xy = some (x, y) →
    closest_pair_in_ball_union c ps xy ps →
    x ∈ ps ∧ y ∈ ps ∧ x ≠ y := sorry

lemma cp_with_help_and_cp_in_balls_implies_closest_pair :
  ∀ (c : ℕ⁺) (ps : list point) (xy : option (point × point)),
    -- If there's a closest pair within distance `c`
    (∃ (p q : point),
      cp_with_help p q ps c) →
    -- and `xy` gives the closest pair in all balls of radius ≥ `c` around
    -- points in `ps`,
    (closest_pair_in_ball_union c ps xy ps) →
    -- then `xy` contains the closest pair in all `ps`.
    ∃ (x y : point),
      xy = some (x, y) ∧ (closest_pair x y ps) := begin
  intros c ps xy h_cp_help h_cp_in_ball_union,
  cases h_cp_help with p h_cp_help,
  cases h_cp_help with q h_cp_help,
  unfold cp_with_help closest_pair at h_cp_help,
  have xy_leq_pq : xy ≤ some (p, q) := begin
    fapply cp_in_ball_union_closer_than_all_pts_in_dist_c,
    exact c,
    exact ps,
    exact ps,
    refl,
    exact h_cp_help.left.left,
    unfold pt_in_ball,
    repeat {split},
    exact h_cp_help.left.right.left,
    apply ne.symm,
    exact h_cp_help.left.right.right.left,
    rw [point_norm_sub_comm],
    exact h_cp_help.right.right,
    assumption,
  end,
  have xy_is_some : ∃ (x y : point), xy = some (x, y) := begin
    apply option_pt_le_some_eq_some,
    exact xy_leq_pq,
  end,
  cases xy_is_some with x xy_is_some,
  cases xy_is_some with y xy_is_some,
  have x_sub_y_leq_p_sub_q : ∥x - y∥ ≤ ∥p - q∥ := begin
    rw [xy_is_some] at xy_leq_pq,
    simp [has_le.le, point_le] at xy_leq_pq ⊢,
    exact xy_leq_pq,
  end,
  have xy_closest : closest_pair x y ps := begin
    unfold closest_pair,
    have xy_in_pt_list_and_neq : x ∈ ps ∧ y ∈ ps ∧ x ≠ y := begin
      apply some_cp_in_balls_in_pt_list_and_neq,
      exact xy_is_some,
      exact h_cp_in_ball_union,
    end,
    repeat {split},
    { exact xy_in_pt_list_and_neq.left, },
    { exact xy_in_pt_list_and_neq.right.left, },
    { exact xy_in_pt_list_and_neq.right.right, },
    {
      intros r s r_neq_s,
      have pq_le_rs : ∥p - q∥ ≤ ∥r - s∥ := begin
        apply h_cp_help.left.right.right.right,
        exact r_neq_s,
      end,
      apply int_le_trans,
      exact x_sub_y_leq_p_sub_q,
      exact pq_le_rs,
    }
  end,
  fapply exists.intro,
  exact x,
  fapply exists.intro,
  exact y,
  exact ⟨xy_is_some, xy_closest⟩,
end


lemma aux_gives_closest_pair:
  ∀ (g : grid_2D),
    (∃ (p q : point),
      cp_with_help p q g.ps g.c) →
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

theorem find_closest_pair_correct :
  ∀ (c : ℕ⁺) (ps : list point),
    -- If there's a closest pair within distance `c`
    (∃ (p q : point),
      cp_with_help p q ps c) →
    -- then our algorithm finds a closest pair.
    (∃ (p q : point),
      (find_closest_pair c ps) = some (p, q) ∧
      closest_pair p q ps) := begin
  intros c ps exists_pair,
  have aux_gives_closest :
    (∃ (p q : point),
        aux (grid_points c ps) ps = some (p, q)
        ∧ closest_pair p q ps) := begin
    have expand_ps : aux (grid_points c ps) ps = aux (grid_points c ps) (grid_points c ps).ps := begin
      congr,
      symmetry,
      apply grid_pts_dot_ps_with_ps_eq_ps,
    end,
    rw [expand_ps],
    have dumb_rw :
      (∃ (p q : point), aux (grid_points c ps) (grid_points c ps).ps = some (p, q) ∧ closest_pair p q (grid_points c ps).ps) →
      (∃ (p q : point), aux (grid_points c ps) (grid_points c ps).ps = some (p, q) ∧ closest_pair p q ps) := begin
      intros h,
      cases h with p h',
      cases h' with q h'',
      fapply exists.intro,
      exact p,
      fapply exists.intro,
      exact q,
      constructor,
      exact h''.left,
      rw [grid_pts_dot_ps_with_ps_eq_ps] at h'',
      exact h''.right,
    end,
    apply dumb_rw,
    apply aux_gives_closest_pair,
    rw [grid_pts_dot_ps_with_ps_eq_ps, grid_pts_dot_c_with_c_eq_c],
    assumption,
  end,
  cases aux_gives_closest with p aux_gives_closest,
  cases aux_gives_closest with q aux_gives_closest,

  fapply exists.intro,
  exact p,
  fapply exists.intro,
  exact q,

  simp [find_closest_pair],
  apply and.intro,
  {
    fapply exists.intro,
    exact p,
    fapply exists.intro,
    exact q,
    apply and.intro,
    exact aux_gives_closest.left,

    have aux_closest_dist_leq_c : (∥p - q∥ ≤ ↑c) := begin
      cases exists_pair with p' exists_pair,
      cases exists_pair with q' exists_pair,
      have aux_closer_than_cp : ∥p - q∥ ≤ ∥p' - q'∥ := begin
        unfold closest_pair at aux_gives_closest,
        apply aux_gives_closest.right.right.right.right,
        exact exists_pair.left.right.right.left,
      end,
      apply int_le_trans,
      exact aux_closer_than_cp,
      exact exists_pair.right.right,
    end,

    by_cases (↑c < ∥p - q∥),

    rw [←coe_to_ℕ_then_ℤ_eq_coe_to_ℤ] at h,
    simp [h],
    fapply not_leq_and_gt,
    exact (p - q),
    exact c,
    apply and.intro,
    exact aux_closest_dist_leq_c,
    exact h,
    rw [←coe_to_ℕ_then_ℤ_eq_coe_to_ℤ] at h,
    simp [h],
  },
  {
    exact aux_gives_closest.right,
  }
end

