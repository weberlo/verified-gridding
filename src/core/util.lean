import data.nat.basic

structure pos_nat :=
  (n : ℕ)
  (n_nonzero : n > 0)
notation `ℕ⁺` := pos_nat
instance : has_coe ℕ⁺ ℕ :=
  ⟨λ pos_n, pos_n.n⟩

lemma coe_to_ℕ_then_ℤ_eq_coe_to_ℤ :
  ∀ (n : ℕ⁺),
    (↑(↑n : ℕ) : ℤ) = (↑n : ℤ) := begin
  sorry
end
