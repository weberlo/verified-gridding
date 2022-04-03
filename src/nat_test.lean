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
instance : has_norm point :=
  ⟨λ p, p.1 * p.1 + p.2 * p.2⟩

#eval ((1, 2) : point) + ((-3, -4) : point)

-- The definition happens to align with points here, but they're conceptually
-- different.
def grid_idx := ℤ × ℤ
instance : has_add grid_idx :=
  ⟨λ p₁ p₂, (p₁.1 + p₂.1, p₁.2 + p₂.2)⟩


def point_hash : point → ℕ
| (a, b) := a.nat_abs + b.nat_abs

#eval point_hash (1, 4)

def grid_2D := hash_map grid_idx (λ _, list point)

-- `C` is an upper bound on the closest pair distance.
def grid_points (C : ℕ) (C_nonzero : C ≠ 0) : list point → grid_2D
| [] := mk_hash_map point_hash
| (x :: xs) :=
    let g := grid_points xs in
    -- TODO could just use `g.modify`
    let bucket_idx := (x.1 % C, x.2 % C) in
    let l := match g.find bucket_idx with
      | none := []
      | some l' := l'
      end
    in
    g.insert bucket_idx (x :: l)

def test_points : list point :=
  [(0, 0), (2, 2)]

#check (grid_points 3 (by simp) test_points).entries
-- def grid_points : list (Σ (_ : point), list point)

def min_dist_point_aux (xs : list (point × ℝ)) (acc : point × ℝ) : point × ℝ :=
  match xs with
  | [] := acc
  | ((p, d) :: pds) :=
      let (p_acc, d_acc) := acc in
      let acc' :=
        if d < d_acc
        then (p, d)
        else acc
      in
      have pds.sizeof < xs.sizeof, by sorry,
      have acc'.sizeof < acc.sizeof, by sorry,
      min_dist_point_aux pds acc'
  end

def min_dist_point (pt_dist_pairs : list (point × ℝ)) : option point :=
  match pt_dist_pairs with
  | [] := none
  | ((p, d) :: pds) :=
      (min_dist_point_aux pt_dist_pairs (p, d)).fst

-- variable (a : option (point × ℝ))
-- #check a >>= (λ o, some o.fst)
  -- match o with
  -- | (some (p, _)) := p
  -- | none := none
  -- end)

def aux
  (C : ℕ)
  (C_nonzero : C ≠ 0)
  (g : grid_2D)
  (closest : point × point)
  (points : list point)
  : point × point :=
match points with
| [] := closest
| (p :: ps) :=
    let bucket_idx := (p.1 % C, p.2 % C) in
    let kernel : list (ℤ × ℤ) :=
      [
        (-1, 1), (0, 1), (1, 1),
        (-1, 0), (0, 0), (1, 0),
        (-1, -1), (0, -1), (1, -1)
      ]
    in
    -- `N` = neighbors
    let N := kernel.map (λ offs, g.find (bucket_idx + offs)) in
    let point_dist_pair_lists : list (list (point × ℝ)) := N.map (λ mq,
      match mq with
      | none := []
      | (some l) := l.map (λ q, (q, ∥ p - q ∥))
      end
    ) in
    let point_dist_pairs := point_dist_pair_lists.join in
    match min_dist_point point_dist_pairs with
    | some q := sorry
    | none := sorry
    end
end

/-
We can only get `none` if `C` wasn't actually a valid hint.
-/
noncomputable def find_closest_pair
  (C : ℕ)
  (C_nonzero : C ≠ 0)
  (points : list point)
  : option (point × point) :=
  match points with
  | [] := none
  | (_ :: []) := none
  | (p₁ :: p₂ :: _) :=
      let g := grid_points C C_nonzero points in
      let (p₁', p₂') := aux C C_nonzero g (p₁, p₂) points in
      -- TODO we need to use some norm that yeets out to ℚ, rather than ℝ, so it
      -- can recognize this as computable.
      if ∥ p₁' - p₂' ∥ > C
      then none
      else some (p₁', p₂')
  end


-- def hash_map_test : hash_map (ℚ × ℚ) (λ _, list point) :=
--   let res := mk_hash_map {point} {λ _, list point} point_hash 31 in
--   res


-- def close_pairs : list
