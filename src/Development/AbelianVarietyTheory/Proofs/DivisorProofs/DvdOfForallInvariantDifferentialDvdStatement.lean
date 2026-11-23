module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Mathlib.Algebra.Module.Projective
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
import Mathlib.RingTheory.MvPowerSeries.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveDvdOfForallDualDvd

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem projective_dvd_of_forall_dual_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Projective O M] (a : O) (b : M),
      (∀ φ : Module.Dual O M, a ∣ φ b) → ∃ z, b = a • z := by
  intro O M _ _ _ _ a b h
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective O M)
  have hc : ∀ i : M, a ∣ s b i := fun i => h ((Finsupp.lapply i).comp s)
  choose c hc using hc
  refine ⟨∑ i ∈ (s b).support, c i • i, ?_⟩
  have hb : Finsupp.linearCombination O id (s b) = b := by
    simpa using LinearMap.congr_fun hs b
  rw [Finset.smul_sum]
  conv_lhs => rw [← hb]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← hc i]
  rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveDvdOfForallDualDvdStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.exists_smul_eq_of_forall_dual_dvd : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Projective O M] (a : O) (b : M), (∀ φ : Module.Dual O M, a ∣ φ b) → ∃ z, b = a • z := by
  first | exact @GlobalTheory.projective_dvd_of_forall_dual_dvd | exact GlobalTheory.projective_dvd_of_forall_dual_dvd | (intros; apply GlobalTheory.projective_dvd_of_forall_dual_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvd

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem dvd_of_forall_omega_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ)
    (a : O) (b : G.A n),
    (∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n → a ∣ φ b) →
      (∃ z, b = a • z) ∧ ∀ w : G.dual.omega, ∃ φ : CartierDual O (G.A n), dUnit (R := O) φ = w.1 n := by
  intro p O _ G n a b h
  have hall : ∀ φ : CartierDual O (G.A n), a ∣ φ b := fun φ => by
    obtain ⟨w, hw⟩ := G.dual.omegaLevel_surjective n (dUnit (R := O) φ)
    exact h w φ hw.symm
  exact ⟨GlobalTheory.T.exists_smul_eq_of_forall_dual_dvd O (G.A n) a b (fun φ => hall (WithConv.toConv φ)),
    fun w => AugCot.d_surjective _ (w.1 n)⟩

end GlobalTheory.PDivGroup
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvdStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.dvd_of_forall_invariantDifferential_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ) (a : O) (b : G.A n), (∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n → a ∣ φ b) → (∃ z, b = a • z) ∧ ∀ w : G.dual.omega, ∃ φ : CartierDual O (G.A n), dUnit (R := O) φ = w.1 n := by
  first | exact @GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd | exact GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd | (intros; apply GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd <;> assumption)
end
end
