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

-- lemma min_dist_point_finds_min :
--   ∀ (pds : list (point × ℚ)),
--     pds = [] ∨
--     (∃ (p : (point × ℚ)),
--       pds.mem p ∧
--       min_dist_point pds = p.1 ∧
--       ∀ (q : (point × ℚ)),
--         pds.mem q → p.2 < q.2)
-- :=
-- begin
--   intros pds,
--   cases pds,
--     apply or.inl,
--     refl,
--   apply or.inr,
--   apply exists.intro,
--   -- I get the feeling that we're not going about proving existentials
--   -- correctly.  Look up some examples in Lean.
--   sorry
-- end


/-
  All points within distance `t` from the current point are included in the list.
-/
-- TODO the grid needs to store the t value that defines it, to be able to state
-- this theorem.
-- theorem get_neighbs_gets_neighbs :
--   ∀ p g bucket_idx,
--     let N := get_neighbs p g bucket_idx in
--     ∀ n ∈ N, ∥ n - p ∥ ≤ g.t

/-
  Get minimum distance pair, wrt the grid `g`, with `p` as the center of the
  pair, and only considering the neighbors of `p`.
-/
def mdp_with (p : point) (g : grid_2D) : option (point × point) :=
    let N := get_neighbs p g in
    let point_dist_pairs : list (point × ℚ) := N.map (λ q, (q, ∥ p - q ∥)) in
    match min_dist_point point_dist_pairs with
    | some q := some (p, q)
    | none := none
    end


lemma get_neighbs_contains_all_within_ball :
  ∀ (c : ℕ⁺) (ps : list point) (p q : point) (g : grid_2D),
    (∥ p - q ∥ ≤ c) → (q ∈ get_neighbs p g) := begin
  sorry
end

-- lemma mdp_with_correct :
--   ∀ (p q : point) (g : grid_2D),
--     ∥ p - q ∥ ≤ g.c →
--       ∃ (x : point),
--         mdp_with p g = some (x, p) ∧
--         ∥ p - x ∥ ≤ ∥ p - q ∥ := begin
--   sorry
-- end



def aux (g : grid_2D) : list point → option (point × point)
| [] := none
| (p :: ps) :=
    let rec_res := aux ps in
    -- let N := get_neighbs p g in
    -- let point_dist_pairs : list (point × ℚ) := N.map (λ q, (q, ∥ p - q ∥)) in
    -- let curr_res :=
    --   match min_dist_point point_dist_pairs with
    --   | some q := some (p, q)
    --   | none := none
    --   end
    -- in
    let curr_res := mdp_with p g in
    -- TODO figure out why we can't get decidable to work on `point_le`.
    if point_lt' curr_res rec_res then curr_res else rec_res
    -- match (curr_res, rec_res) with
    -- | (some _, none) := curr_res
    -- | (none, some _) := rec_res
    -- | (some (p', q'), some (p'', q'')) :=
    --     if ∥ p' - q' ∥ < ∥ p'' - q'' ∥
    --     then curr_res
    --     else rec_res
    -- | (none, none) := none
-- end


def pt_in_ball (p q : point) (c : ℕ⁺) (qs : list point) : Prop :=
  q ∈ qs ∧
  q ≠ p ∧
  ∥q - p∥ ≤ c


lemma get_min_dist_pair_correct :
  ∀ (p : point) (g : grid_2D),
    ∀ (x : point),
      (pt_in_ball p x g.c g.ps) →
      ((mdp_with p g) ≤ some (p, x)) := begin
  sorry
end

lemma min_dist_pair_in_ball :
  ∀ (p q : point) (g : grid_2D),
    mdp_with p g = some (p, q) →
    pt_in_ball p q g.c g.ps := begin
  sorry
end


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

#reduce ({1, 2} : set ℕ) = ({})


-- def closest_pair (p q : point) (ps : list point) : Prop :=
--   (p ∈ ps) ∧
--   (q ∈ ps) ∧
--   (p ≠ q) ∧
--   (∀ (r s : point),
--       (((p = r ∧ q = s) ∨ (p = s ∧ q = r)) ↔ (∥ p - q ∥ = ∥ r - s ∥)) ∧
--      (¬((p = r ∧ q = s) ∨ (p = s ∧ q = r)) ↔ (∥ p - q ∥ < ∥ r - s ∥)))

def closest_pair (p q : point) (ps : list point) : Prop :=
  (p ∈ ps) ∧
  (q ∈ ps) ∧
  (p ≠ q) ∧
  (∀ (r s : point), r ≠ s → ∥p - q∥ ≤ ∥r - s∥)
    --   (((p = r ∧ q = s) ∨ (p = s ∧ q = r)) ↔ (∥ p - q ∥ = ∥ r - s ∥)) ∧
    --  (¬((p = r ∧ q = s) ∨ (p = s ∧ q = r)) ↔ (∥ p - q ∥ < ∥ r - s ∥)))

/-
  TODO the definitions might be useful if proofs become too cumbersome.
  The `has_le` definition could simplify the merge step in our algorithm (and
  thus the reasoning).

inductive closest_pair' : option (point × point) → list point → Prop
| cp_empty : closest_pair' none []
| cp_singleton (p : point) : closest_pair' none (p :: [])
| cp_cons_no_update (p : point) (ps' : list point) (xy : option (point × point)) :
    closest_pair' xy ps' →
    (∀ (q : point), q ∈ ps' → (xy ≤ some (p, q))) →
    closest_pair' xy (p :: ps')
| cp_cons_update (p q : point) (ps' : list point) (xy : option (point × point)) :
    closest_pair' xy ps' →
    q ∈ ps' →
    some (p, q) ≤ xy →
    closest_pair' (some (p, q)) (p :: ps')
-/


/-
  Closest pair with help
-/
def cp_with_help (p q : point) (ps : list point) (c : ℕ⁺) : Prop :=
  (closest_pair p q ps) ∧ (1 < ∥ p - q ∥) ∧ (∥ p - q ∥ ≤ c)


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

lemma exists_q_in_range_implies_aux_finds_it:
  ∀ (q : point) (qs' : list point) (ps : list point) (c : ℕ⁺),
    (∃ (p : point), p ∈ ps ∧ ∥p - q∥ ≤ ↑c) →
    (∃ (x y : point),
      aux (grid_points c ps) (q :: qs') = some (x, y) ∧
      ∀ (p : point),
        p ∈ ps →
        ∥p - q∥ ≤ ↑c →
        ∥x - y∥ ≤ ∥p - q∥) := begin
  sorry
end


inductive closest_pair_in_ball_union (c : ℕ⁺) (qs : list point) : option (point × point) → list point → Prop
| no_ball : closest_pair_in_ball_union none []
| cons_ball_no_update (xy : option (point × point)) (p : point) (ps' : list point) :
    closest_pair_in_ball_union xy ps' →
    (∀ (q : point),
      pt_in_ball p q c ps' →
      (xy ≤ some (p, q))) →
    closest_pair_in_ball_union xy (p :: ps')
| cons_ball_update
    (xy : option (point × point))
    (p : point)
    (ps' : list point)
    (q : point) :
    (
      pt_in_ball p q c qs ∧
      (∀ (x : point), (pt_in_ball p x c qs) → ∥ q - p ∥ ≤ ∥ x - p ∥) ∧
      some (p, q) < xy
    ) →
    closest_pair_in_ball_union xy ps' →
    closest_pair_in_ball_union (some (p, q)) (p :: ps')


-- lemma aux_monotonic_in_pt_list :
--   ∀ (c : ℕ⁺) (qs : list point) (p : point) (ps : list point),
--     ∃ (xy zw : option (point × point)),
--       (xy = aux (grid_points c ps) ps) ∧
--       (zw = aux (grid_points c ps) (p :: ps)) ∧
--       match (xy, zw) with
--       | (none, none) := true
--       | (some xy', none) := false
--       | (none, some zw') := true
--       | (some xy', some zw') := ∥ zw'.1 - zw'.2 ∥ ≤ ∥ xy'.1 - xy'.2 ∥
--       end := begin
--   sorry,
-- end


lemma closest_pair_monotonic_in_pt_list :
  ∀ (c : ℕ⁺) (qs : list point) (p : point) (ps' : list point),
    (closest_pair_in_ball_union c qs (aux (grid_points c qs) ps') ps') →
    (closest_pair_in_ball_union c qs (aux (grid_points c qs) (p :: ps')) ps') := begin
  intros c qs p ps' cp_aux_ps'_for_ps',

  cases cp_aux_ps'_for_ps',

  apply closest_pair_in_ball_union.no_ball,

  rename [cp_aux_ps'_for_ps'_p → p', cp_aux_ps'_for_ps'_ps' → ps'],
  apply closest_pair_in_ball_union.cons_ball,

  sorry,

  sorry,

end


/-
  Expresses the property that all points in `ps` are > distance `ε` from each
  other.
-/
def eps_separated (ps : list point) (ε : ℕ⁺) : Prop :=
  (∀ (p q : point), p ∈ ps → q ∈ ps → ∥ p - q ∥ > ε)

lemma cp_with_help_implies_eps_separated :
  ∀ (p q : point) (ps : list point) (c : ℕ⁺),
    cp_with_help p q ps c → eps_separated ps 1 := begin
  sorry
end

lemma grid_pts_dot_c_is_arg_c :
  ∀ (c : ℕ⁺) (qs : list point),
    (grid_points c qs).c = c := sorry

lemma grid_pts_dot_ps_is_arg_ps :
  ∀ (c : ℕ⁺) (ps : list point),
    (grid_points c ps).ps = ps := sorry

lemma point_le_iff_point_le'_eq_true :
  ∀ (xy zw : option (point × point)),
    xy ≤ zw ↔ (point_le' xy zw = true) := begin
  intros xy zw,
  constructor,
  sorry,
  sorry,
end

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
               exact ps'_subseteq_qs,
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
          assumption,
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

lemma cp_in_ball_union_closer_than_all_pts_in_dist_c :
  ∀ (c : ℕ⁺) (p q : point) (xy : option (point × point)) (ps qs : list point),
    ps ⊆ qs →
    p ∈ ps →
    q ∈ ps →
    ∥p - q∥ ≤ c →
    closest_pair_in_ball_union c qs xy ps →
    xy ≤ some (p, q) := sorry

lemma in_sublist_in_list :
  ∀ (p : point) (ps qs : list point),
    p ∈ ps →
    ps ⊆ qs →
    p ∈ qs := sorry

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
  cases h_cp_help with p h_cp_help',
  cases h_cp_help' with q h_cp_help'',
  unfold cp_with_help closest_pair at h_cp_help'',
  have xy_leq_pq : xy ≤ some (p, q) := begin
    apply cp_in_ball_union_closer_than_all_pts_in_dist_c,
    refl,
    exact h_cp_help''.left.left,
    exact h_cp_help''.left.right.left,
    exact h_cp_help''.right.right,
    exact h_cp_in_ball_union,
  end,
  have xy_is_some : ∃ (x y : point), xy = some (x, y) := begin
    apply option_pt_le_some_eq_some,
    exact xy_leq_pq,
  end,
  cases xy_is_some with x xy_is_some',
  cases xy_is_some' with y xy_is_some'',
  have x_sub_y_leq_p_sub_q : ∥x - y∥ ≤ ∥p - q∥ := begin
    rw [xy_is_some''] at xy_leq_pq,
    simp [has_le.le, point_le] at xy_leq_pq ⊢,
    exact xy_leq_pq,
  end,
  have xy_closest : closest_pair x y ps := begin
    unfold closest_pair,
    have xy_in_pt_list_and_neq : x ∈ ps ∧ y ∈ ps ∧ x ≠ y := begin
      apply some_cp_in_balls_in_pt_list_and_neq,
      exact xy_is_some'',
      exact h_cp_in_ball_union,
    end,
    repeat {split},
    { exact xy_in_pt_list_and_neq.left, },
    { exact xy_in_pt_list_and_neq.right.left, },
    { exact xy_in_pt_list_and_neq.right.right, },
    {
      intros r s r_neq_s,
      sorry,
    }
  end,
  sorry,
end


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



-- TODO see if there's a simpler way to phrase this.
theorem find_closest_pair_correct :
  ∀ (c : ℕ⁺) (ps : list point),
    -- If there's a closest pair within distance `c`
    (∃ (p q : point),
      cp_with_help p q ps c) →
    -- then our algorithm finds a closest pair.
    (∃ (p q : point),
      (find_closest_pair c ps) = some (p, q) ∧
      closest_pair p q ps) :=
begin
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

