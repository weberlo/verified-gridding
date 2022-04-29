import data.hash_map
import data.nat.basic
import data.rat.basic
import data.real.basic
import data.real.sqrt
import data.rat.sqrt
import analysis.normed.group.basic

import core.point
import core.grid


def min_dist_point_aux : list (point × ℚ) → option (point × ℚ)
| [] := none
| ((p, d) :: pds) :=
    match min_dist_point_aux pds with
    | none :=
        some (p, d)
    | some (p', d') :=
        some (if d < d' then (p, d) else (p', d'))
    end

def min_dist_point : list (point × ℚ) → option point
| [] := none
| pds := min_dist_point_aux pds >>= (λ (p : point × ℚ), some p.1)

lemma min_dist_point_finds_min :
  ∀ (pds : list (point × ℚ)),
    pds = [] ∨
    (∃ (p : (point × ℚ)),
      pds.mem p ∧
      min_dist_point pds = p.1 ∧
      ∀ (q : (point × ℚ)),
        pds.mem q → p.2 < q.2)
:=
begin
  intros pds,
  cases pds,
    apply or.inl,
    refl,
  apply or.inr,
  apply exists.intro,
  -- I get the feeling that we're not going about proving existentials
  -- correctly.  Look up some examples in Lean.
  sorry
end


/-
  All points within distance `t` from the current point are included in the list.
-/
-- TODO the grid needs to store the t value that defines it, to be able to state
-- this theorem.
-- theorem get_neighbs_gets_neighbs :
--   ∀ p g bucket_idx,
--     let N := get_neighbs p g bucket_idx in
--     ∀ n ∈ N, ∥ n - p ∥ ≤ g.t


def aux
  (c : ℕ)
  (c_nonzero : c > 0)
  (g : grid_2D) : list point → option (point × point)
| [] := none
| (p :: ps) :=
    let rec_res := aux ps in
    let N := get_neighbs p g in
    let point_dist_pairs : list (point × ℚ) := N.map (λ q, (q, ∥ p - q ∥)) in
    let curr_res :=
      match min_dist_point point_dist_pairs with
      | some q := some (p, q)
      | none := none
      end
    in
    match (curr_res, rec_res) with
    | (some _, none) := curr_res
    | (none, some _) := rec_res
    | (some (p', q'), some (p'', q'')) :=
        if ∥ p' - q' ∥ < ∥ p'' - q'' ∥
        then curr_res
        else rec_res
    | (none, none) := none
end

/-
We can only get `none` if `c` wasn't actually a valid hint.
-/
def find_closest_pair
  (c : ℕ)
  (c_nonzero : c > 0)
  (points : list point)
  : option (point × point) :=
  let g := grid_points c c_nonzero points in
  aux c c_nonzero g points >>= (
    λ pq : point × point,
      if ∥ pq.1 - pq.2 ∥ > c
      then none
      else some pq
  )



#eval find_closest_pair 3 (by simp) [(0, 0), (2, 0), (5, 0)]
#eval find_closest_pair 4 (by simp) [(0, 0), (2, 0), (5, 0)]
#eval find_closest_pair 7 (by simp) [(0, 0), (2, 2), (5, 0)]
#eval find_closest_pair 8 (by simp) [(0, 0), (2, 2), (5, 0)]

#reduce ({1, 2} : set ℕ) = ({})


def closest_pair (p q : point) (ps : list point) : Prop :=
  (p ∈ ps) ∧
  (q ∈ ps) ∧
  (p ≠ q) ∧
  (∀ (r s : point),
      (((p = r ∧ q = s) ∨ (p = s ∧ q = r)) ↔ (∥ p - q ∥ = ∥ r - s ∥)) ∧
     (¬((p = r ∧ q = s) ∨ (p = s ∧ q = r)) ↔ (∥ p - q ∥ < ∥ r - s ∥)))


lemma not_x_lt_y_and_gt_y :
  ∀ (x y : ℤ),
    ¬(x < y ∧ y < x) := begin
  sorry
end

lemma not_lt_and_not_gt_implies_eq :
  ∀ (x y : ℤ),
    ¬(x < y) →
    ¬(y < x) →
    x = y := begin
  sorry
end

lemma two_closest_pairs_implies_same :
  ∀ (x y z w : point) (ps : list point),
    (closest_pair x y ps) → (closest_pair z w ps) → ((x = z ∧ y = w) ∨ (x = w ∧ y = z)) := begin
  intros x y z w ps cp_xy cp_zw,
  have sep_xy : _ := cp_xy.right.right.right,
  have sep_zw : _ := cp_zw.right.right.right,

  by_cases xy_lt_zw : ∥ x - y ∥ < ∥ z - w ∥;
  by_cases zw_lt_xy : ∥ z - w ∥ < ∥ x - y ∥,

  /-
    Case (∥x - y∥ < ∥z - w∥) ∧ (∥z - w∥ < ∥x - y∥)
  -/
  exact false.elim ((not_x_lt_y_and_gt_y (∥ x - y ∥) (∥ z - w ∥)) ⟨xy_lt_zw, zw_lt_xy⟩),

  /-
    Case (∥x - y∥ < ∥z - w∥) ∧ ¬(∥z - w∥ < ∥x - y∥)
  -/
  have xy_neq_zw : ¬(x = z ∧ y = w ∨ x = w ∧ y = z) := begin
    exact ((sep_xy z w).right.mpr xy_lt_zw)
  end,
  have zw_lt_xy' : ∥z - w∥ < ∥x - y∥ := begin
    have xy_neq_zw' : ¬(z = x ∧ w = y ∨ z = y ∧ w = x) := begin
      intros h,
      have xy_eq_zw : x = z ∧ y = w ∨ x = w ∧ y = z := begin
        cases h,
        simp [h],
        simp [h],
      end,
      contradiction,
    end,
    exact ((sep_zw x y).right.mp xy_neq_zw')
  end,
  contradiction,

  /-
    Case ¬(∥x - y∥ < ∥z - w∥) ∧ (∥z - w∥ < ∥x - y∥)
  -/
  have zw_neq_xy : ¬(z = x ∧ w = y ∨ z = y ∧ w = x) := begin
    exact ((sep_zw x y).right.mpr zw_lt_xy)
  end,
  have xy_lt_zw' : ∥x - y∥ < ∥z - w∥ := begin
    have xy_neq_zw' : ¬(x = z ∧ y = w ∨ x = w ∧ y = z) := begin
      intros h,
      have xy_eq_zw : z = x ∧ w = y ∨ z = y ∧ w = x := begin
        cases h,
        simp [h],
        simp [h],
      end,
      contradiction,
    end,
    exact ((sep_xy z w).right.mp xy_neq_zw')
  end,
  contradiction,

  /-
    Case ¬(∥x - y∥ < ∥z - w∥) ∧ ¬(∥z - w∥ < ∥x - y∥)
  -/
  have norm_xy_eq_norm_zw : ∥ x - y ∥ = ∥ z - w ∥ := begin
    apply not_lt_and_not_gt_implies_eq,
    assumption,
    assumption,
  end,
  exact ((sep_xy z w).left.mpr norm_xy_eq_norm_zw),
end


lemma exists_closest_pair_implies_nonempty :
  ∀ (ps : list point), (∃ (p q : point), closest_pair p q ps) → ps ≠ [] :=
begin
  sorry
end

lemma aux_gives_closest_pair:
  ∀ (ps : list point) (c : ℕ) (c_nonzero : c > 0),
    ps ≠ [] →
    -- TODO we'll need a supposition that the closest pair is within distance `c`
    (∃ (p q : point),
      aux c c_nonzero (grid_points c c_nonzero ps) ps = some (p, q)
      ∧ closest_pair p q ps) := begin
  sorry
end


-- TODO see if there's a simpler way to phrase this.
theorem find_closest_pair_correct :
  ∀ (c : ℕ) (c_nonzero : c > 0) (ps : list point),
    -- If all points are at least distance 1 from each other
    (∀ (p q : point), p ∈ ps ∧ q ∈ ps → ∥ p - q ∥ > 1) →
    -- and there's a closest pair
    (∃ (p q : point),
      (closest_pair p q ps) ∧ (1 < ∥ p - q ∥) ∧ (∥ p - q ∥ ≤ c)) →
      -- then our algorithm finds the closest pair.
      (∃ (p q : point),
        (find_closest_pair c c_nonzero ps) = some (p, q) ∧
        closest_pair p q ps) :=
begin
  intros c c_nonzero ps all_pts_dist_gt_one exists_pair,

  have ps_nonempty : ps ≠ [] := begin
    apply exists_closest_pair_implies_nonempty,
    cases exists_pair,
    cases exists_pair_h,
    fapply exists.intro,
    exact exists_pair_w,
    fapply exists.intro,
    exact exists_pair_h_w,
    exact exists_pair_h_h.left,
  end,

  have aux_gives_closest :
    (∃ (p q : point),
        aux c c_nonzero (grid_points c c_nonzero ps) ps = some (p, q)
        ∧ closest_pair p q ps) := begin
    apply aux_gives_closest_pair,
    exact ps_nonempty,
  end,
  cases aux_gives_closest,
  cases aux_gives_closest_h,

  fapply exists.intro,
  exact aux_gives_closest_w,
  fapply exists.intro,
  exact aux_gives_closest_h_w,

  simp [find_closest_pair],
  apply and.intro,
  fapply exists.intro,
  exact aux_gives_closest_w,
  fapply exists.intro,
  exact aux_gives_closest_h_w,
  apply and.intro,
  exact aux_gives_closest_h_h.left,

  have aux_closest_dist_leq_c : (∥aux_gives_closest_w - aux_gives_closest_h_w∥ ≤ ↑c) := begin
    cases exists_pair,
    cases exists_pair_h,

    rename [
      aux_gives_closest_w → x,
      aux_gives_closest_h_w → y,
      exists_pair_w → z,
      exists_pair_h_w → w
    ],
    have cp_xy : closest_pair x y ps := aux_gives_closest_h_h.right,
    have cp_zw : closest_pair z w ps := exists_pair_h_h.left,
    have xy_eq_zw : ((x = z ∧ y = w) ∨ (x = w ∧ y = z)) := begin
      apply two_closest_pairs_implies_same,
      assumption,
      assumption,
    end,
    cases xy_eq_zw;
    cases xy_eq_zw;
    rw [←xy_eq_zw_left, ←xy_eq_zw_right] at exists_pair_h_h,

    exact exists_pair_h_h.right.right,

    rw [point_norm_sub_comm x y],
    exact exists_pair_h_h.right.right,
  end,

  by_cases (↑c < ∥aux_gives_closest_w - aux_gives_closest_h_w∥),

  simp [h],
  fapply not_leq_and_gt,
  exact (aux_gives_closest_w - aux_gives_closest_h_w),
  exact c,
  apply and.intro,
  exact aux_closest_dist_leq_c,
  exact h,

  simp [h],
  exact aux_gives_closest_h_h.right,
end

