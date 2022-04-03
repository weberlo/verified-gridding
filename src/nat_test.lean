import data.hash_map
import data.nat.basic
import data.rat.basic
import data.real.basic
import data.real.sqrt
import data.rat.sqrt
import analysis.normed.group.basic

#check real.sqrt

def point := ℤ × ℤ
instance : has_repr point :=
  ⟨λ p, "(" ++ (repr p.1) ++ ", " ++ (repr p.2) ++ ")"⟩
instance : has_add point :=
  ⟨λ p₁ p₂, (p₁.1 + p₂.1, p₁.2 + p₂.2)⟩
instance : has_sub point :=
  ⟨λ p₁ p₂, (p₁.1 - p₂.1, p₁.2 - p₂.2)⟩
instance : inhabited point :=
  ⟨(0, 0)⟩


-- NOTE: This is the *squared* ℓ₂ norm.  It should be fine for our purposes,
-- because it's a monotonic isomorphism, but we should think some more to make
-- sure.
-- instance : has_norm point :=
--   ⟨λ p, ⟩

-- NOTE: We don't want to use the `has_norm` typeclass, because that asserts the
-- result is a real.
def point_norm (p : point) : ℚ :=
  p.1 * p.1 + p.2 * p.2

local notation `∥` e `∥` := point_norm e

#eval ((1, 2) : point) + ((-3, -4) : point)

-- The definition happens to align with points here, but they're conceptually
-- different.
def grid_idx := ℤ × ℤ
instance : has_add grid_idx :=
  ⟨λ p₁ p₂, (p₁.1 + p₂.1, p₁.2 + p₂.2)⟩
instance : has_repr grid_idx :=
  ⟨λ p, "(" ++ (repr p.1) ++ ", " ++ (repr p.2) ++ ")"⟩


def point_hash : point → ℕ
| (a, b) := a.nat_abs + b.nat_abs

#eval point_hash (1, 4)

def grid_2D := hash_map grid_idx (λ _, list point)

-- Lean won't let us define the overlapping instance here, since there's already
-- an instance for sigma types generally.
-- instance : has_repr (Σ (a : grid_idx), list point) :=
--  ⟨λ p, ""⟩
instance : has_repr grid_2D :=
  ⟨λ g, "[" ++ (g.entries.map
    (λ (p : Σ (a : grid_idx), list point),
      (" {" ++ repr p.1 ++ ": " ++ repr p.2 ++ "} ").to_list)).join.as_string ++ "]"⟩

#check list

def get_bucket_idx (p : point) (C : ℕ) : (ℤ × ℤ) :=
  (p.1 / C, p.2 / C)

-- `C` is an upper bound on the closest pair distance.
def grid_points (C : ℕ) (C_nonzero : C ≠ 0) : list point → grid_2D
| [] := mk_hash_map point_hash
| (x :: xs) :=
    let g := grid_points xs in
    -- TODO could just use `g.modify`
    let bucket_idx := get_bucket_idx x C in
    let l := match g.find bucket_idx with
      | none := []
      | some l' := l'
      end
    in
    g.insert bucket_idx (x :: l)

def test_points : list point :=
  [(0, 0), (2, 2)]

#check (grid_points 3 (by simp) test_points).entries

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

def aux
  (C : ℕ)
  (C_nonzero : C ≠ 0)
  (g : grid_2D) : list point → option (point × point)
| [] := none
| (p :: ps) :=
    let rec_res := aux ps in
    let bucket_idx := get_bucket_idx p C in
    let kernel : list (ℤ × ℤ) :=
      [
        (-1, 1), (0, 1), (1, 1),
        (-1, 0), (0, 0), (1, 0),
        (-1, -1), (0, -1), (1, -1)
      ]
    in
    -- `N` = neighbors
    let N := kernel.map (λ offs, g.find (bucket_idx + offs)) in
    let point_dist_pair_lists : list (list (point × ℚ)) := N.map (λ mq,
      match mq with
      | none := []
      | (some l) := l.map (λ q, (q, ∥ p - q ∥))
      end
    ) in
    let point_dist_pairs := point_dist_pair_lists.join.filter
      (λ qd, qd.1 ≠ p) in
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
We can only get `none` if `C` wasn't actually a valid hint.
-/
def find_closest_pair
  (C : ℕ)
  (C_nonzero : C ≠ 0)
  (points : list point)
  : option (point × point) :=
  let g := grid_points C C_nonzero points in
  aux C C_nonzero g points >>= (
    λ pq : point × point,
      if ∥ pq.1 - pq.2 ∥ > C
      then none
      else some pq
  )


#eval find_closest_pair 7 (by simp) test_points
#eval find_closest_pair 8 (by simp) test_points

-- def hash_map_test : hash_map (ℚ × ℚ) (λ _, list point) :=
--   let res := mk_hash_map {point} {λ _, list point} point_hash 31 in
--   res


-- def close_pairs : list
