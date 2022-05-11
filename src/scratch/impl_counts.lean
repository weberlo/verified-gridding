def get_neighbs (p : point) (g : grid_2D) : list point :=
  let idxs : list (ℤ × ℤ) := get_idxs p g.c in
  let cells : list (option (list point)) := idxs.map (λ i, g.data.find i) in
  let cells' : list (list point) := cells.map lift_option_list in
  let flat_cells : list point := cells'.join in
  flat_cells.filter (λ q, q ≠ p)
def point := ℤ × ℤ
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
def point_norm (p : point) : ℤ :=
  p.1 * p.1 + p.2 * p.2
notation `∥` e `∥` := point_norm e
def point_le' (xy zw : option (point × point)) : bool :=
  match (xy, zw) with
  | (none, none) := true
  | (none, some _) := false
  | (some _, none) := true
  | (some (x, y), some (z, w)) := ∥ x - y ∥ ≤ ∥ z - w ∥
  end
def point_lt' (xy zw : option (point × point)) : bool :=
  match (xy, zw) with
  | (none, none) := false
  | (none, some _) := false
  | (some _, none) := true
  | (some (x, y), some (z, w)) := ∥ x - y ∥ < ∥ z - w ∥
  end
def get_hypercube (bound : ℕ) : list (ℤ × ℤ) :=
  (do
    j <- list.range (2 * bound + 1),
    return (do
      i <- list.range (2 * bound + 1),
      return (-(bound : ℤ) + i, -(bound : ℤ) + j))).join
def get_idxs (p : point) (c : ℕ⁺) :=
  let grid_idx := get_grid_idx p in
  let bound := nat.sqrt c + 1 in
  let hypercube := get_hypercube bound in
  hypercube.map (λ offs, grid_idx + offs)

def lift_option_list {α} : option (list α) → list α
| none := []
| (some l) := l
def get_grid_idx (p : point) : grid_idx :=
  (p.1, p.2)
def grid_points (c : ℕ⁺) : list point → grid_2D
| [] := ⟨mk_hash_map point_hash, c, []⟩
| (x :: xs) :=
    let g := grid_points xs in
    let grid_idx := get_grid_idx x in
    let l := match g.data.find grid_idx with
      | none := []
      | some l' := l'
      end
    in
    ⟨g.data.insert grid_idx (x :: l), c, x :: g.ps⟩
structure grid_2D :=
  (data : hash_map grid_idx (λ _, list point))
  (c : ℕ⁺)
  (ps : list point)
def grid_idx := ℤ × ℤ
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
def aux (g : grid_2D) : list point → option (point × point)
| [] := none
| (p :: ps) :=
    let rec_res := aux ps in
    let curr_res := mdp_with p g in
    -- TODO figure out why we can't get decidable to work on `point_le`.
    if point_lt' curr_res rec_res then curr_res else rec_res
lemma min_dist_pair_in_ball :
  ∀ (p q : point) (g : grid_2D),
    (mdp_with p g = some (p, q)) →
    pt_in_ball p q g.c g.ps := begin
  sorry
end
def mdp_with (p : point) (g : grid_2D) : option (point × point) :=
  let ps := get_neighbs p g in
  min_dist_pair p ps
def min_dist_pair (p : point) : list point → option (point × point)
| [] := none
| (q :: ps') :=
    let pq' := min_dist_pair ps' in
    if point_lt' (p, q) pq' then some (p, q) else pq'
def point_hash : point → ℕ
| (a, b) := a.nat_abs + b.nat_abs
structure pos_nat :=
  (val : ℕ)
  (val_nonzero : val > 0)
notation `ℕ⁺` := pos_nat
instance : has_coe ℕ⁺ ℕ :=
  ⟨λ pos_n, pos_n.val⟩
