def pt_in_ball (p q : point) (c : ℕ⁺) (qs : list point) : Prop :=
  q ∈ qs ∧
  q ≠ p ∧
  ∥q - p∥ ≤ c
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
def closest_pair (p q : point) (ps : list point) : Prop :=
  (p ∈ ps) ∧
  (q ∈ ps) ∧
  (p ≠ q) ∧
  (∀ (r s : point), r ≠ s → ∥p - q∥ ≤ ∥r - s∥)
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
lemma some_cp_in_balls_in_pt_list_and_neq :
  ∀ (c : ℕ⁺) (x y : point) (xy : option (point × point)) (ps : list point),
    xy = some (x, y) →
    closest_pair_in_ball_union c ps xy ps →
    x ∈ ps ∧ y ∈ ps ∧ x ≠ y := sorry
lemma grid_pts_dot_c_with_c_eq_c :
  ∀ (c : ℕ⁺) (ps : list point),
    (grid_points c ps).c = c := sorry
lemma grid_pts_dot_ps_with_ps_eq_ps :
  ∀ (c : ℕ⁺) (ps : list point),
    (grid_points c ps).ps = ps := sorry
def in_opt_list {α : Type} (x : α) : option (list α) → Prop
| none := false
| (some xs') := x ∈ xs'
def point_le (xy zw : option (point × point)) : Prop :=
  match (xy, zw) with
  | (none, none) := true
  | (none, some _) := false
  | (some _, none) := true
  | (some (x, y), some (z, w)) := ∥ x - y ∥ ≤ ∥ z - w ∥
  end
instance : has_le (option (point × point)) := ⟨point_le⟩
def point_lt (xy zw : option (point × point)) : Prop :=
  match (xy, zw) with
  | (none, none) := false
  | (none, some _) := false
  | (some _, none) := true
  | (some (x, y), some (z, w)) := ∥ x - y ∥ < ∥ z - w ∥
  end
instance : has_lt (option (point × point)) := ⟨point_lt⟩
lemma point_lt_iff_point_lt' :
  ∀ (xy zw : option (point × point)),
    point_lt xy zw ↔ ↥(point_lt' xy zw) := sorry
lemma point_norm_symm :
  ∀ (x y : point),
    ∥x - y∥ = ∥y - x∥ := begin
  sorry
end
lemma le_iff_neg_lt :
  ∀ (xy zw : option (point × point)),
    xy ≤ zw ↔ ¬(xy > zw) := sorry
lemma neg_le_iff_lt :
  ∀ (xy zw : option (point × point)),
    ¬(xy ≤ zw) ↔ zw < xy := sorry
lemma option_pt_lt_trans :
  ∀ (pq xy zw : option (point × point)),
    pq < xy →
    xy < zw →
    pq < zw := begin
  intros pq xy zw h1 h2,
  sorry,
end
lemma option_pt_le_trans :
  ∀ (pq xy zw : option (point × point)),
    pq ≤ xy →
    xy ≤ zw →
    pq ≤ zw := sorry
lemma option_pt_le_symm :
  ∀ (pq : option (point × point)) (x y : point),
    pq ≤ some (x, y) →
    pq ≤ some (y, x) := sorry
lemma option_pt_le_lt_trans :
  ∀ (pq xy zw : option (point × point)),
    pq ≤ xy →
    xy < zw →
    pq < zw := sorry
lemma option_pt_lt_le_trans :
  ∀ (pq xy zw : option (point × point)),
    pq < xy →
    xy ≤ zw →
    pq < zw := sorry
lemma option_pt_lt_to_le :
  ∀ (xy zw : option (point × point)),
    xy < zw →
    xy ≤ zw := sorry
lemma not_x_le_y_and_gt_y :
  ∀ (x y : option (point × point)),
    x ≤ y →
    y < x →
    false
    := begin
  sorry
end
lemma int_le_trans :
  ∀ (x y z : ℤ),
    x ≤ y →
    y ≤ z →
    x ≤ z := begin
  intros x y z h1 h2,
  linarith,
end
lemma point_lt'_iff_point_lt :
  ∀ (xy zw : option (point × point)),
    ↥(point_lt' xy zw) ↔ xy < zw := sorry
lemma option_pt_le_some_eq_some :
  ∀ (xy : option (point × point)) (z w : point),
    xy ≤ some (z, w) → ∃ (x y : point), xy = some (x, y) := sorry
lemma int_nonneg_add :
  ∀ (x y : ℤ), int.nonneg x → int.nonneg y → int.nonneg (x + y) := begin
  intros x y h1 h2,
  sorry
end
lemma int_x_times_x_nonneg :
  ∀ (x : ℤ), int.nonneg (x * x) := begin
    intros x,
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
lemma not_le_and_gt :
  ∀ (x y : ℤ),
    ¬(x ≤ y ∧ y < x) := begin
  sorry
end
lemma not_lt_and_not_gt_implies_eq :
  ∀ (x y : ℤ),
    ¬(x < y) →
    ¬(y < x) →
    x = y := begin
  sorry
end
lemma coe_to_ℕ_then_ℤ_eq_coe_to_ℤ :
  ∀ (n : ℕ⁺),
    (↑(↑n : ℕ) : ℤ) = (↑n : ℤ) := begin
  intros n,
  simp,
end
instance : has_one ℕ⁺ := ⟨⟨1, by simp⟩⟩
lemma add_nonzero_nonzero :
  ∀ (m n : ℕ),
    m > 0 →
    n > 0 →
    m + n > 0 := begin
  intros m n h1 h2,
  linarith,
end
instance : has_mul ℕ⁺ := ⟨λ m n,
 ⟨m.val + n.val, by simp [add_nonzero_nonzero, m.val_nonzero, n.val_nonzero]⟩⟩
