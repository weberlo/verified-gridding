import data.hash_map
import algebra.ring.basic
import data.int.basic
import data.nat.basic

import core.point

-- The definition happens to align with points here, but they're conceptually
-- different.
def grid_idx := ℤ × ℤ
instance : has_add grid_idx :=
  ⟨λ p₁ p₂, (p₁.1 + p₂.1, p₁.2 + p₂.2)⟩
instance : has_repr grid_idx :=
  ⟨λ p, "(" ++ (repr p.1) ++ ", " ++ (repr p.2) ++ ")"⟩


structure grid_2D :=
  (data : hash_map grid_idx (λ _, list point))
  (C : ℕ)
  (C_nonzero : C > 0)

-- def grid_2D := hash_map grid_idx (λ _, list point)

-- Lean won't let us define the overlapping instance here, since there's already
-- an instance for sigma types generally.
-- instance : has_repr (Σ (a : grid_idx), list point) :=
--  ⟨λ p, ""⟩
instance : has_repr grid_2D :=
  ⟨λ g, "[" ++ (g.data.entries.map
    (λ (p : Σ (a : grid_idx), list point),
      (" {" ++ repr p.1 ++ ": " ++ repr p.2 ++ "} ").to_list)).join.as_string ++ "]"⟩


def get_grid_idx (p : point) (C : ℕ) : grid_idx :=
  (p.1 / C, p.2 / C)

-- `C` is an upper bound on the closest pair distance.
def grid_points (C : ℕ) (C_nonzero : C > 0) : list point → grid_2D
-- TODO need to update this function to return a structure, rather than just the hash map for the grid.
| [] := ⟨mk_hash_map point_hash, C, C_nonzero⟩
| (x :: xs) :=
    let g := grid_points xs in
    -- TODO could just use `g.modify`
    let grid_idx := get_grid_idx x C in
    let l := match g.data.find grid_idx with
      | none := []
      | some l' := l'
      end
    in
    ⟨g.data.insert grid_idx (x :: l), C, C_nonzero⟩

def test_points : list point :=
  [(0, 0), (2, 2)]

#check (grid_points 3 (by simp) test_points).data.entries

def get_neighbs (p : point) (g : grid_2D) (bucket_idx : ℤ × ℤ) : list point :=
  let kernel : list (ℤ × ℤ) :=
    [
      (-1, 1), (0, 1), (1, 1),
      (-1, 0), (0, 0), (1, 0),
      (-1, -1), (0, -1), (1, -1)
    ]
  in
  (kernel.map (λ offs,
    match (g.data.find (bucket_idx + offs)) with
    | none := []
    | (some l) := l
    end)).join.filter (λ q, q ≠ p)

theorem close_in_grid_means_close_in_space :
  ∀ (p₁ p₂ : point) (a b : grid_idx) (G : grid_2D) (l₁ l₂ : list point),
  (a = get_grid_idx p₁ G.C) →
  (b = get_grid_idx p₂ G.C) →
  (a ∈ G.data.keys) →
  (b ∈ G.data.keys) →
  (G.data.find a = some l₁) →
  (G.data.find b = some l₂) →
  (p₁ ∈ l₁) →
  (p₂ ∈ l₂) →
  ∥ p₁ - p₂ ∥ ≤ G.C * G.C * (∥ a - b ∥ + ∥ (1, 1) ∥)
  := begin
    intros p₁ p₂ a b G l₁ l₂ a_p₁ b_p₂ a_in_G b_in_G a_has_elts b_has_elts p_in_a₁ b_in_a₂,
    unfold get_grid_idx at a_p₁,
    unfold get_grid_idx at b_p₂,
    rw [int.distrib_left (G.C * G.C) ∥a - b∥ ∥(1, 1)∥],
    have h : (↑(G.C * G.C) * ∥a - b∥ = ∥p₁ - p₂∥) :=
    begin
      rw [a_p₁, b_p₂],
      unfold point_norm,
      simp only [prod.fst, prod.snd],
      rw [int.distrib_left],
      have unfold_x_sub_y : ∀ (x y : ℤ), x - y = x + (-y) := begin
        intros x y,
        -- TODO wtf why doesn't this work?
        -- unfold int.sub,
        sorry
      end,
      have simpler_vars : ∀ (x y t : ℤ),
        t > 0 →
        (t*t) * ((x/t - y/t) * (x/t - y/t)) ≤ x*x - x*y - x*y + y*y + t*t := begin
          intros x y t t_nonzero,
          rw [unfold_x_sub_y],
          rw [int.distrib_left (x / t + -(y / t)) (x / t) (-(y / t))],
          rw [int.distrib_right (x / t) (-(y / t)) (x / t)],
          rw [int.distrib_right (x / t) (-(y / t)) (-(y / t))],
          rw [int.distrib_left (t*t) (x / t * (x / t) + -(y / t) * (x / t)) (x / t * -(y / t) + -(y / t) * -(y / t))],
          rw [int.distrib_left (t*t) (x / t * (x / t)) (-(y / t) * (x / t))],
          rw [int.distrib_left (t*t) (x / t * -(y / t)) (-(y / t) * -(y / t))],
          have reassoc : ∀ (x y z : ℤ), z * z * (x / z * (y / z)) = (z * x / z) * (z * (y / z)) := begin
            sorry
          end,
          have div_to_mod : ∀ (x y z : ℤ), z * z * (x / z * (y / z)) = (x - x % z) * (y - y % z) :=
          begin
            sorry
          end,
          simp [int.neg],
          simp [div_to_mod],
          rw [reassoc],
          rw [reassoc],
          rw [reassoc],
          rw [reassoc],
      end,
      rw [unfold_x_sub_y (p₁.fst / ↑(G.C)) ((p₂.fst / ↑(G.C)))],
      rw [int.distrib_left (p₁.fst / ↑(G.C) - p₂.fst / ↑(G.C)) (p₁.fst / ↑(G.C)) (-(p₂.fst / ↑(G.C)))],
      sorry
    end,
    rw h,
    simp [point_norm],
    apply (nonneg_iff_leq_zero (↑(G.C) * (1 + 1))).mp,
    apply a_nonneg_times_b_nonneq_means_a_times_b_nonneg,
    apply lift_nat_nonneg,
    simp [int.nonneg],
  end
