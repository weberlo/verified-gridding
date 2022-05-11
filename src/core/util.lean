import data.nat.basic
import data.rat.basic
import data.real.basic
import data.real.sqrt
import data.rat.sqrt
import analysis.normed.group.basic

structure pos_nat :=
  (val : ℕ)
  (val_nonzero : val > 0)
notation `ℕ⁺` := pos_nat
instance : has_coe ℕ⁺ ℕ :=
  ⟨λ pos_n, pos_n.val⟩

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
