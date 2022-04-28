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
    let grid_idx := get_grid_idx p c in
    let N := get_neighbs p g grid_idx in
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


#eval find_closest_pair 7 (by simp) test_points
#eval find_closest_pair 8 (by simp) test_points

#reduce ({1, 2} : set ℕ) = ({})


def closest_pair (p q : point) (ps : list point) : Prop :=
  (p ∈ ps) ∧
  (q ∈ ps) ∧
  -- (ps.mem p) ∧
  -- (ps.mem q) ∧
  (∀ (r s : point),
      ((∥ r - s ∥ = ∥ p - q ∥)
          → (({r, s} : set point) = ({p, q} : set point))) ∧
      (({r, s} : set point) ≠ ({p, q} : set point))
          → (∥ p - q ∥ < ∥ r - s ∥))


-- TODO see if there's a simpler way to phrase this.
theorem find_closest_pair_correct :
  ∀ (c : ℕ) (c_nonzero : c > 0) (ps : list point),
    (∃ (p : point) (q : point),
      (closest_pair p q ps) ∧ (1 < ∥ p - q ∥) ∧ (∥ p - q ∥ ≤ c)) →
      (∃ (p : point) (q : point),
        (find_closest_pair c c_nonzero ps) = some (p, q) ∧
        closest_pair p q ps) :=
begin
  intros c c_nonzero ps exists_pair,
  apply exists.intro,
  apply exists.intro,
  simp [find_closest_pair],
  apply and.intro,
  apply exists.intro,
  apply exists.intro,
  sorry,
  sorry
end
