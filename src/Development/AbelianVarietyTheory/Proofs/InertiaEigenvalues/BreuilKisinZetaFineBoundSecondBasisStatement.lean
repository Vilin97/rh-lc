module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIntegralityComputationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulConnectionSeriesTermMemLatticeStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaSeriesHigherTermsMemLPowBreuilKisinStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XPowSmulMemPrimePowAddFiltrationPhiModule

section

@[expose] public section

noncomputable section

namespace GlobalTheory.BK

open PowerSeries

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]

theorem EIn_pow_eq_factorial_mul_Ediv (i : ℕ) :
    EIn l e (S O K e) ^ i = (i.factorial : S O K e) * ⟨Ediv K l e i, Ediv_mem_S l e i⟩ := by
  apply Subtype.ext
  have hf : (i.factorial : K) ≠ 0 := natCast_ne_zero' l i.factorial_ne_zero
  have hc : ((i.factorial : S O K e) : K⟦X⟧) = C (i.factorial : K) := by
    rw [map_natCast]; rfl
  simp only [SubmonoidClass.coe_pow, coe_EIn, Subalgebra.coe_mul, Ediv, hc]
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hf, map_one, one_mul]

theorem exists_uIn_pow_eq (j : ℕ) (hj : j ≤ l) : ∃ σ : S O K e, ∃ φ ∈ Fil O K l e j,
    uIn (S O K e) ^ (e * l) = (l : S O K e) ^ (l - j) * σ + φ := by
  have hu : uIn (S O K e) ^ e = EIn l e (S O K e) + -(l : S O K e) := by
    apply Subtype.ext
    simp [E]
  refine ⟨∑ i ∈ Finset.range j, EIn l e (S O K e) ^ i * (-1) ^ (l - i) * (l : S O K e) ^ (j - i) *
      (l.choose i : S O K e),
    ∑ i ∈ Finset.Ico j (l + 1), EIn l e (S O K e) ^ i * (-(l : S O K e)) ^ (l - i) *
      (l.choose i : S O K e), ?_, ?_⟩
  · refine Ideal.sum_mem _ fun i hi => ?_
    have hi' : j ≤ i := (Finset.mem_Ico.1 hi).1
    rw [EIn_pow_eq_factorial_mul_Ediv]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ediv_mem_Fil l e hi')))
  · rw [pow_mul, hu, add_pow, ← Finset.sum_range_add_sum_Ico _ (by omega : j ≤ l + 1),
      Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < j := Finset.mem_range.1 hi
    have h1 : l - i = (l - j) + (j - i) := by omega
    rw [neg_pow, h1, pow_add, pow_add]
    ring

theorem X_pow_smul_mem_l_pow_MM_add_FilMM (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι) (j : ℕ) (hj : j ≤ l)
    (w : Vec K a ι) (hw : w ∈ P.MM) : ∃ s ∈ P.MM, ∃ f ∈ P.FilMM j,
      (X : K⟦X⟧) ^ (e * l) • w = (l : K) ^ (l - j) • s + f := by
  obtain ⟨σ, φ, hφ, h⟩ := exists_uIn_pow_eq (O := O) (K := K) (l := l) (e := e) j hj
  refine ⟨σ • w, P.MM.smul_mem σ hw, φ • w, Submodule.smul_mem_smul hφ hw, ?_⟩
  have h2 : (X : K⟦X⟧) ^ (e * l) • w = (uIn (S O K e) ^ (e * l)) • w := by
    rw [Subalgebra.smul_def]
    simp
  have h3 : ((l : S O K e) ^ (l - j)) • (σ • w) = (l : K) ^ (l - j) • (σ • w) := by
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  rw [h2, h, add_smul, mul_smul, h3]

end GlobalTheory.BK
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XPowSmulMemPrimePowAddFiltrationPhiModuleStatement

section

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.X_pow_smul_mem_prime_pow_add_filtration_phiModule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (j : ℕ), j ≤ l → ∀ w ∈ P.MM, ∃ s ∈ P.MM, ∃ f ∈ P.FilMM j, (X : K⟦X⟧) ^ (e * l) • w = (l : K) ^ (l - j) • s + f := by
  first | exact @GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM | exact GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM | (intros; apply GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinZetaFineBoundSecondBasis

section

@[expose] public section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK

theorem zeta_Y'_fine_bound : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → ∀ y ∈ D.Y', ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta y = (l : K) ^ (l - 14 * H) • p + ((l : K) ^ (3 * H))⁻¹ • f := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hη hηH hl y hy
  obtain ⟨y₀, ⟨hy₀, -⟩, rfl⟩ := hy
  have hy₀' : E K l e ^ η • y₀ ∈ D.M := hy₀
  show ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta ((X : K⟦X⟧) ^ e • y₀) = _
  obtain ⟨r, hr, hT⟩ := GlobalTheory.T.zeta_series_higher_terms_mem_lPow_breuilKisin O K l e a ι η H D y₀ hη hηH hl hy₀'
  obtain ⟨w₁, hw₁, hB⟩ := GlobalTheory.T.prime_pow_smul_connection_series_term_mem_lattice O K l e a ι η H D y₀ hη hy₀' 0
  obtain ⟨s, hs, f, hf, hD⟩ := GlobalTheory.T.X_pow_smul_mem_prime_pow_add_filtration_phiModule O K l e a ι D.toPhiMod (10 * H) (by omega) w₁ hw₁
  have hIC := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D hηH (by omega)
  obtain ⟨p₁, hp₁, f₁, hf₁, rfl⟩ := hIC.1 s hs
  obtain ⟨p₂, hp₂, f₂, hf₂, rfl⟩ := hIC.1 r hr
  have hsm : ∀ {R : Type} [Semiring R] [Module R (Vec K a ι)] (W : Submodule R (Vec K a ι)) (k : ℕ)
      {v : Vec K a ι}, v ∈ W → (l : K) ^ k • v ∈ W := fun W k v hv => by
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; exact nsmul_mem hv _
  refine ⟨p₂ - (l : K) ^ (3 * H - 2 * η) • p₁, sub_mem hp₂ (hsm _ _ hp₁),
    (l : K) ^ (l - 11 * H) • f₂ - (l : K) ^ (2 * H - 2 * η) • ((l : K) ^ (l - 10 * H) • f₁ + f),
    sub_mem (hsm _ _ hf₂) (hsm _ _ (add_mem (hsm _ _ hf₁) hf)), ?_⟩
  simp only [zero_add, pow_one, zero_mul, add_zero, one_mul] at hB
  rw [hD] at hB
  have hl0 : (l : K) ≠ 0 := l_ne_zero l
  have e1 : l - 10 * H = (l - 14 * H) + (3 * H - 2 * η) + (H + 2 * η) := by omega
  have e2 : l - 11 * H = (l - 14 * H) + (2 * H - 2 * η) + (H + 2 * η) := by omega
  have e3 : (l : K) ^ (3 * H) = (l : K) ^ (2 * H - 2 * η) * (l : K) ^ (H + 2 * η) := by
    rw [← pow_add]; congr 1; omega
  rw [e1] at hB
  rw [e1, e2, e3]
  have hz := eq_sub_of_add_eq hT
  rw [hz]
  generalize l - 14 * H = A at *
  generalize 3 * H - 2 * η = B at *
  generalize 2 * H - 2 * η = Dd at *
  generalize H + 2 * η = Cc at *
  generalize (l : K) = x at *
  have hL : D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (x ^ Cc)⁻¹ • (x ^ (A + B + Cc) • (p₁ + f₁) + f) := by
    rw [← hB, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl0), one_smul]
  rw [hL]
  match_scalars <;> field_simp <;> ring

end GlobalTheory.BK
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinZetaFineBoundSecondBasisStatement

section

@[expose] public section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → ∀ y ∈ D.Y', ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), D.zeta y = (l : K) ^ (l - 14 * H) • p + ((l : K) ^ (3 * H))⁻¹ • f := by
  first | exact @GlobalTheory.BK.zeta_Y'_fine_bound | exact GlobalTheory.BK.zeta_Y'_fine_bound | (intros; apply GlobalTheory.BK.zeta_Y'_fine_bound <;> assumption)
end
end
