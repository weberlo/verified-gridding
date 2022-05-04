structure pos_nat :=
  (val : ℕ)
  (val_nonzero : val > 0)
instance : has_mul ℕ⁺ := ⟨λ m n,
 ⟨m.val + n.val, by simp [add_nonzero_nonzero, m.val_nonzero, n.val_nonzero]⟩⟩
instance : has_one ℕ⁺ := ⟨⟨1, by simp⟩⟩
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
def get_min_dist_point_in_neighbs (p : point) (g : grid_2D) : option (point × point) :=
    let N := get_neighbs p g in
    let point_dist_pairs : list (point × ℚ) := N.map (λ q, (q, ∥ p - q ∥)) in
    match min_dist_point point_dist_pairs with
    | some q := some (p, q)
    | none := none
    end
notation `ℕ⁺` := pos_nat
instance : has_coe ℕ⁺ ℕ :=
  ⟨λ pos_n, pos_n.val⟩
def aux (g : grid_2D) : list point → option (point × point)
| [] := none
| (p :: ps) :=
    let rec_res := aux ps in
    let curr_res := get_min_dist_point_in_neighbs p g in
    match (curr_res, rec_res) with
    | (some _, none) := curr_res
    | (none, some _) := rec_res
    | (some (p', q'), some (p'', q'')) :=
        if ∥ p' - q' ∥ < ∥ p'' - q'' ∥
        then curr_res
        else rec_res
    | (none, none) := none
end
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
def point_hash : point → ℕ
| (a, b) := a.nat_abs + b.nat_abs
def grid_idx := ℤ × ℤ
instance : has_add grid_idx :=
  ⟨λ p₁ p₂, (p₁.1 + p₂.1, p₁.2 + p₂.2)⟩
instance : has_repr grid_idx :=
  ⟨λ p, "(" ++ (repr p.1) ++ ", " ++ (repr p.2) ++ ")"⟩
structure grid_2D :=
  (data : hash_map grid_idx (λ _, list point))
  (c : ℕ⁺)
  (ps : list point)
instance : has_repr grid_2D :=
  ⟨λ g, "[" ++ (g.data.entries.map
    (λ (p : Σ (a : grid_idx), list point),
      (" {" ++ repr p.1 ++ ": " ++ repr p.2 ++ "} ").to_list)).join.as_string ++ "]"⟩
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
def get_neighbs (p : point) (g : grid_2D) : list point :=
  let grid_idx := get_grid_idx p in
  let bound := nat.sqrt g.c in
  let kernel : list (ℤ × ℤ) :=
    (do
        j <- list.range (2 * bound + 1),
        return (do
          i <- list.range (2 * bound + 1),
          return (-(bound : ℤ) + i, -(bound : ℤ) + j))).join in
  (kernel.map (λ offs,
    match (g.data.find (grid_idx + offs)) with
    | none := []
    | (some l) := l
    end)).join.filter (λ q, q ≠ p)


lemma get_neighbs_gets_neighbs :
  ∀ (p : point) (g : grid_2D),
    ∀ (q : point),
      (q ∈ g.ps ∧ ∥ p - q ∥ ≤ g.c) → (q ∈ get_neighbs p g) :=
begin
  sorry
end
theorem close_in_grid_means_close_in_space :
  ∀ (p₁ p₂ : point) (a b : grid_idx) (G : grid_2D) (l₁ l₂ : list point),
  (a = get_grid_idx p₁) →
  (b = get_grid_idx p₂) →
  (a ∈ G.data.keys) →
  (b ∈ G.data.keys) →
  (G.data.find a = some l₁) →
  (G.data.find b = some l₂) →
  (p₁ ∈ l₁) →
  (p₂ ∈ l₂) →
  ∥ p₁ - p₂ ∥ ≤ G.c * G.c * (∥ a - b ∥ + ∥ (1, 1) ∥)
  := begin
    intros p₁ p₂ a b G l₁ l₂ a_p₁ b_p₂ a_in_G b_in_G a_has_elts b_has_elts p_in_a₁ b_in_a₂,
    unfold get_grid_idx at a_p₁,
    unfold get_grid_idx at b_p₂,
    rw [int.distrib_left (G.c * G.c) ∥a - b∥ ∥(1, 1)∥],
    have h : (↑(G.c * G.c) * ∥a - b∥ = ∥p₁ - p₂∥) :=
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
      rw [unfold_x_sub_y (p₁.fst / ↑(G.c)) ((p₂.fst / ↑(G.c)))],
      rw [int.distrib_left (p₁.fst / ↑(G.c) - p₂.fst / ↑(G.c)) (p₁.fst / ↑(G.c)) (-(p₂.fst / ↑(G.c)))],
      sorry
    end,
    rw h,
    simp [point_norm],
    apply (nonneg_iff_leq_zero (↑(G.c) * (1 + 1))).mp,
    apply a_nonneg_times_b_nonneq_means_a_times_b_nonneg,
    apply lift_nat_nonneg,
    simp [int.nonneg],
  end
lemma coe_to_ℕ_then_ℤ_eq_coe_to_ℤ :
  ∀ (n : ℕ⁺),
    (↑(↑n : ℕ) : ℤ) = (↑n : ℤ) := begin
  sorry
end
lemma add_nonzero_nonzero :
  ∀ (m n : ℕ),
    m > 0 →
    n > 0 →
    m + n > 0 := begin
  sorry
end
lemma get_neighbs_contains_all_within_ball :
  ∀ (c : ℕ⁺) (ps : list point) (p q : point) (g : grid_2D),
    (∥ p - q ∥ ≤ c) → (q ∈ get_neighbs p g) := begin
  sorry
end
lemma get_min_dist_point_in_neighbs_correct :
  ∀ (p q : point) (g : grid_2D),
    ∥ p - q ∥ ≤ g.c →
      ∃ (x : point),
        get_min_dist_point_in_neighbs p g = some (x, p) ∧
        ∥ p - x ∥ ≤ ∥ p - q ∥ := begin
  sorry
end
def closest_pair (p q : point) (ps : list point) : Prop :=
  (p ∈ ps) ∧
  (q ∈ ps) ∧
  (p ≠ q) ∧
  (∀ (r s : point),
      (((p = r ∧ q = s) ∨ (p = s ∧ q = r)) ↔ (∥ p - q ∥ = ∥ r - s ∥)) ∧
     (¬((p = r ∧ q = s) ∨ (p = s ∧ q = r)) ↔ (∥ p - q ∥ < ∥ r - s ∥)))
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
  exact false.elim ((not_x_lt_y_and_gt_y (∥ x - y ∥) (∥ z - w ∥)) ⟨xy_lt_zw, zw_lt_xy⟩),
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
inductive closest_pair_in_balls (c : ℕ⁺) (qs : list point) :
  option (point × point) → list point → Prop
| no_ball (xy : option (point × point)) : closest_pair_in_balls xy []
| succ_ball (xy : option (point × point)) (p : point) (ps' : list point) :
    ((∃ (q : point), q ∈ qs ∧ ∥ q - p ∥ ≤ c) → -- TODO should this be iff?
      ∃ (x y : point),
        xy = some (x, y) ∧
        (∀ (q : point),
            q ∈ qs →
            ∥ q - p ∥ ≤ c →
            ∥ x - y ∥ ≤ ∥ q - p ∥)) →
    closest_pair_in_balls xy ps' →
    closest_pair_in_balls xy (p :: ps')
lemma aux_monotonic_in_pt_list :
  ∀ (c : ℕ⁺) (qs : list point) (p : point) (ps : list point),
    ∃ (xy zw : option (point × point)),
      (xy = aux (grid_points c ps) ps) ∧
      (zw = aux (grid_points c ps) (p :: ps)) ∧
      match (xy, zw) with
      | (none, none) := true
      | (some xy', none) := false
      | (none, some zw') := true
      | (some xy', some zw') := ∥ zw'.1 - zw'.2 ∥ ≤ ∥ xy'.1 - xy'.2 ∥
      end := begin
  sorry,
end
lemma closest_pair_monotonic_in_pt_list :
  ∀ (c : ℕ⁺) (qs : list point) (p : point) (ps' : list point),
    (closest_pair_in_balls c qs (aux (grid_points c qs) ps') ps') →
    (closest_pair_in_balls c qs (aux (grid_points c qs) (p :: ps')) ps') := begin
  intros c qs p ps' cp_aux_ps'_for_ps',
  cases cp_aux_ps'_for_ps',
  apply closest_pair_in_balls.no_ball,
  rename [cp_aux_ps'_for_ps'_p → p', cp_aux_ps'_for_ps'_ps' → ps'],
  apply closest_pair_in_balls.succ_ball,
  sorry,
  sorry,
end
def eps_separated (ps : list point) (ε : ℕ⁺) : Prop :=
  (∀ (p q : point), p ∈ ps → q ∈ ps → ∥ p - q ∥ > ε)
lemma cp_with_help_implies_eps_separated :
  ∀ (p q : point) (ps : list point) (c : ℕ⁺),
    cp_with_help p q ps c → eps_separated ps 1 := begin
  sorry
end
lemma aux_finds_closest_pair_in_balls:
  ∀ (c : ℕ⁺) (qs : list point),
    (∃ (p q : point),
      cp_with_help p q qs 1) →
    (∀ (ps : list point),
      ps ⊆ qs →
      closest_pair_in_balls c qs (aux (grid_points c qs) ps) ps) := begin
  intros c qs exists_pair ps ps_subseteq_qs,
  induction ps,
  apply closest_pair_in_balls.no_ball,
  apply closest_pair_in_balls.succ_ball,
  intros exists_q_in_range_in_qs,
  apply exists_q_in_range_implies_aux_finds_it,
  assumption,
  apply closest_pair_monotonic_in_pt_list,
  sorry,
end
lemma cp_with_help_and_cp_in_balls_implies_closest_pair :
  ∀ (c : ℕ⁺) (ps : list point) (xy : option (point × point)),
    (∃ (p q : point),
      cp_with_help p q ps c) →
    (closest_pair_in_balls c ps xy ps) →
    ∃ (x y : point),
      xy = some (x, y) ∧ (closest_pair x y ps) := begin
  sorry,
end
lemma aux_gives_closest_pair:
  ∀ (c : ℕ⁺) (ps : list point),
    (∃ (p q : point),
      cp_with_help p q ps c) →
    (∃ (p q : point),
      aux (grid_points c ps) ps = some (p, q)
      ∧ closest_pair p q ps) := begin
  intros c ps cp_help,
  sorry,
end
theorem find_closest_pair_correct :
  ∀ (c : ℕ⁺) (ps : list point),
    (∃ (p q : point),
      cp_with_help p q ps c) →
      (∃ (p q : point),
        (find_closest_pair c ps) = some (p, q) ∧
        closest_pair p q ps) :=
begin
  intros c ps exists_pair,
  have aux_gives_closest :
    (∃ (p q : point),
        aux (grid_points c ps) ps = some (p, q)
        ∧ closest_pair p q ps) := begin
    apply aux_gives_closest_pair,
    assumption,
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
  rw [←coe_to_ℕ_then_ℤ_eq_coe_to_ℤ] at h,
  simp [h],
  fapply not_leq_and_gt,
  exact (aux_gives_closest_w - aux_gives_closest_h_w),
  exact c,
  apply and.intro,
  exact aux_closest_dist_leq_c,
  exact h,
  rw [←coe_to_ℕ_then_ℤ_eq_coe_to_ℤ] at h,
  simp [h],
  exact aux_gives_closest_h_h.right,
end
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
