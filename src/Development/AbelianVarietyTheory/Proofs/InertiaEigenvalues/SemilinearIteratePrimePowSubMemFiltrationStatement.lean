module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Ideal.Operations

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXPowPrimePowSubOneMemSpan

section

@[expose] public section

namespace GlobalTheory

theorem sq_dvd_choose_prime_pow (l : ℕ) (hl : l.Prime) (b k : ℕ) (hb : 1 ≤ b) (hk0 : k ≠ 0)
    (hk : k < l ^ (b - 1)) : l ^ 2 ∣ (l ^ b).choose k := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨m, hm⟩ : ∃ m, l ^ b = m + 1 := Nat.exists_eq_succ_of_ne_zero (pow_pos hl.pos b).ne'
  have hkb : j + 1 ≤ l ^ b := le_trans hk.le (Nat.pow_le_pow_right hl.pos (Nat.sub_le b 1))
  have hC : (l ^ b).choose (j + 1) ≠ 0 := (Nat.choose_pos hkb).ne'

  have hid : l ^ b * m.choose j = (l ^ b).choose (j + 1) * (j + 1) := by
    rw [hm]; exact Nat.add_one_mul_choose_eq m j

  have hv : padicValNat l (j + 1) < b - 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : l ^ padicValNat l (j + 1) ≤ j + 1 :=
      Nat.le_of_dvd (Nat.succ_pos j) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    have h2 : l ^ (b - 1) ≤ l ^ padicValNat l (j + 1) := Nat.pow_le_pow_right hl.pos hcon
    omega
  have hdiv : l ^ b ∣ (l ^ b).choose (j + 1) * (j + 1) := by
    rw [← hid]; exact dvd_mul_right _ _
  have hne : (l ^ b).choose (j + 1) * (j + 1) ≠ 0 := mul_ne_zero hC (Nat.succ_ne_zero j)
  rw [(by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hne, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hC (by omega : j + 1 ≠ 0)] at hdiv
  exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hC).mpr (by omega)

theorem one_add_X_pow_prime_pow_sub_one_mem_span (l : ℕ) [Fact l.Prime] (b : ℕ) (hb : 1 ≤ b) :
    ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) ∈
      Ideal.span {((l : Polynomial ℤ)) ^ 2, Polynomial.X ^ (l ^ (b - 1))} := by

  have key : ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) =
      ∑ i ∈ Finset.range (l ^ b),
        Polynomial.X ^ (i + 1) * (((l ^ b).choose (i + 1) : ℕ) : Polynomial ℤ) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp
  rw [key]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  by_cases hi : i + 1 < l ^ (b - 1)
  ·
    obtain ⟨c, hc⟩ := sq_dvd_choose_prime_pow l (Fact.out) b (i + 1) hb (Nat.succ_ne_zero i) hi
    rw [hc, Nat.cast_mul, Nat.cast_pow, mul_left_comm]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  ·
    push_neg at hi
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    rw [hd, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearIteratePrimePowSubMemFiltration

section

@[expose] public section

namespace GlobalTheory

theorem semilinear_sub_mem_pow_succ_smul {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (n : Ideal A) (γ : A →+* A) (Y : N →+ N) (hY : ∀ a x, Y (a • x) = γ a • Y x)
    (hγ : ∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1))
    (h1 : ∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) (k : ℕ) (x : N)
    (hx : x ∈ n ^ k • (⊤ : Submodule A N)) :
    Y x - x ∈ n ^ (k + 1) • (⊤ : Submodule A N) := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro a ha y _
    have e : Y (a • y) - a • y = γ a • (Y y - y) + (γ a - a) • y := by
      rw [hY, smul_sub, sub_smul]; abel
    have hga : γ a ∈ n ^ k := by
      have h2 : γ a - a ∈ n ^ k := Ideal.pow_le_pow_right (Nat.le_succ k) (hγ k a ha)
      simpa using (n ^ k).add_mem h2 ha
    rw [e]
    refine Submodule.add_mem _ ?_ (Submodule.smul_mem_smul (hγ k a ha) trivial)
    rw [pow_succ, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hga (h1 y)
  · intro y z hy hz
    have e : Y (y + z) - (y + z) = (Y y - y) + (Y z - z) := by
      rw [map_add (f := _)]; abel
    rw [e]
    exact Submodule.add_mem _ hy hz

theorem semilinear_sub_one_pow_mem {A N : Type} [CommRing A] [AddCommGroup N] [Module A N]
    (n : Ideal A) (γ : A →+* A) (Y : N →+ N) (hY : ∀ a x, Y (a • x) = γ a • Y x)
    (hγ : ∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1))
    (h1 : ∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) (k : ℕ) (x : N) :
    ((Y.toIntLinearMap - 1 : Module.End ℤ N) ^ k) x ∈ n ^ k • (⊤ : Submodule A N) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' (Y.toIntLinearMap - 1 : Module.End ℤ N), Module.End.mul_apply]
    exact semilinear_sub_mem_pow_succ_smul n γ Y hY hγ h1 k _ ih

theorem semilinear_iterate_prime_pow_sub_mem :
    ∀ (l : ℕ) [Fact l.Prime] (A N : Type) [CommRing A] [AddCommGroup N] [Module A N] (n : Ideal A) (γ : A →+* A) (Y : N →+ N), (∀ a x, Y (a • x) = γ a • Y x) → (∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1)) → (∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) → ∀ b : ℕ, 1 ≤ b → ∀ x, Y^[l ^ b] x - x ∈ (Ideal.span {((l : A)) ^ 2} ⊔ n ^ (l ^ (b - 1))) • (⊤ : Submodule A N) := by
  intro l _ A N _ _ _ n γ Y hY hγ h1 b hb x
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (GlobalTheory.one_add_X_pow_prime_pow_sub_one_mem_span l b hb)
  set D : Module.End ℤ N := Y.toIntLinearMap - 1 with hD
  have h := congrArg (Polynomial.aeval D) huv
  rw [mul_comm u, mul_comm v] at h
  simp only [map_add (f := _), map_mul, map_pow, map_sub, map_one, map_natCast, Polynomial.aeval_X] at h
  have hYD : (1 + D) = Y.toIntLinearMap := by rw [hD]; abel
  rw [hYD] at h
  have h' := congrArg (fun f : Module.End ℤ N => f x) h
  simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
    Module.End.one_apply] at h'
  have e : (Y.toIntLinearMap ^ (l ^ b)) x = Y^[l ^ b] x := by
    rw [Module.End.pow_apply]; rfl
  rw [e] at h'
  rw [← h']
  refine Submodule.add_mem _ ?_ ?_
  · have e2 : ∀ y : N, (((l : Module.End ℤ N)) ^ 2) y = ((l : A) ^ 2) • y := by
      intro y
      rw [← Nat.cast_pow, ← Nat.cast_pow, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]
    rw [e2]
    exact Submodule.smul_mem_smul (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) trivial
  · exact Submodule.smul_mono_left le_sup_right
      (semilinear_sub_one_pow_mem n γ Y hY hγ h1 _ _)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearIteratePrimePowSubMemFiltrationStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.semilinear_iterate_prime_pow_sub_mem_filtration : ∀ (l : ℕ) [Fact l.Prime] (A N : Type) [CommRing A] [AddCommGroup N] [Module A N] (n : Ideal A) (γ : A →+* A) (Y : N →+ N), (∀ a x, Y (a • x) = γ a • Y x) → (∀ (k : ℕ), ∀ a ∈ n ^ k, γ a - a ∈ n ^ (k + 1)) → (∀ x, Y x - x ∈ n • (⊤ : Submodule A N)) → ∀ b : ℕ, 1 ≤ b → ∀ x, Y^[l ^ b] x - x ∈ (Ideal.span {((l : A)) ^ 2} ⊔ n ^ (l ^ (b - 1))) • (⊤ : Submodule A N) := by
  first | exact @GlobalTheory.semilinear_iterate_prime_pow_sub_mem | exact GlobalTheory.semilinear_iterate_prime_pow_sub_mem | (intros; apply GlobalTheory.semilinear_iterate_prime_pow_sub_mem <;> assumption)
end
end
