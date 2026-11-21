import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.FieldDefs
open NumberField
open scoped TensorProduct NNReal

open scoped Pointwise in

private theorem val_nat_eq_one {R : Type} [CommRing R] (w : Valuation R ℝ≥0)
    (hw : ∀ x, w x ≤ 1) {p : ℕ} (hp : p.Prime) (hv : w (p : R) < 1) {m : ℕ} (hm : ¬ p ∣ m) :
    w (m : R) = 1 := by
  by_contra hne
  have hlt : w (m : R) < 1 := lt_of_le_of_ne (hw _) hne
  have hc : IsCoprime (p : R) (m : R) :=
    Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)
  obtain ⟨a, b, hab⟩ := hc
  have h1 : w (a * (p : R)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hw a)) hv
  have h2 : w (b * (m : R)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le (hw b)) hlt
  have := w.map_add_lt h1 h2
  rw [hab, map_one] at this
  exact lt_irrefl _ this

private theorem val_pow_le {R : Type} [CommRing R] (w : Valuation R ℝ≥0) (I : Ideal R) (c : ℝ≥0)
    (h : ∀ a ∈ I, w a ≤ c) (hw : ∀ x, w x ≤ 1) (n : ℕ) : ∀ x ∈ I ^ n, w x ≤ c ^ n := by
  induction n with
  | zero => intro x _; simpa using hw x
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [map_mul, pow_succ]
      exact mul_le_mul' (ih a ha) (h b hb)
    · intro a b ha hb
      exact w.map_add_le ha hb
