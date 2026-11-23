module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DvrOfNormIntegral

section

@[expose] public section

theorem UpperTheory.dvr_of_norm_integral :
    ∀ {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], (∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → IsIntegral ℤ_[l] x) → IsDiscreteValuationRing (integralClosure ℤ_[l] K) := by
  intro l _ K _ h
  have hded : IsDedekindDomain (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K _
  have hfr : IsFractionRing (integralClosure ℤ_[l] K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[l] ℚ_[l] K _
  have key : ∀ x : K, ‖(x : PadicAlgCl l)‖ ≤ 1 →
      IsLocalization.IsInteger (integralClosure ℤ_[l] K) x := by
    intro x hx
    have hi : IsIntegral ℤ_[l] x :=
      (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[l]) Subtype.val_injective).mp (h _ hx)
    exact ⟨⟨x, hi⟩, rfl⟩
  have hval : ValuationRing (integralClosure ℤ_[l] K) := by
    rw [ValuationRing.iff_isInteger_or_isInteger _ K]
    intro x
    rcases le_total ‖(x : PadicAlgCl l)‖ 1 with hx | hx
    · exact Or.inl (key x hx)
    · refine Or.inr (key _ ?_)
      rw [IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ hx
  have hinjK : Function.Injective (algebraMap ℤ_[l] K) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K, RingHom.coe_comp]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] K)) := by
    intro a b hab
    exact hinjK (congrArg Subtype.val hab)
  have hnf : ¬ IsField (integralClosure ℤ_[l] K) := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l]
      ((Algebra.IsIntegral.isField_iff_isField hinj).mpr hf)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[l] K) hnf).out 1 2).mpr hval
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsIntegralOfNormLeOne

section

@[expose] public section

theorem UpperTheory.padicAlgCl_isIntegral_of_norm_le_one :
    ∀ {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l), ‖x‖ ≤ 1 → IsIntegral ℤ_[l] x := by
  intro l _ x hx
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hint
  have hs : spectralValue (minpoly ℚ_[l] x) ≤ 1 := hx
  have hc : ∀ n : ℕ, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).1 hs
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq]
  exact minpoly.aeval _ _
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ReducedCoefficients

section

@[expose] public section

namespace UpperTheory.Reformulated.B.CoefficientRingContainingIntegers

theorem rc_coef {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K] :
    ∃ c : UpperTheory.V.HV.Coef l, ∀ x ∈ K, ‖x‖ ≤ 1 → x ∈ c.O := by
  have hD : IsDiscreteValuationRing (integralClosure ℤ_[l] K) := UpperTheory.dvr_of_norm_integral K (fun x hx => UpperTheory.padicAlgCl_isIntegral_of_norm_le_one x hx)
  have hF : Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f,
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x hx h1 => ?_⟩
  exact ⟨⟨x, hx⟩, (isIntegral_algHom_iff f hf).1 (UpperTheory.padicAlgCl_isIntegral_of_norm_le_one x h1), rfl⟩

end UpperTheory.Reformulated.B.CoefficientRingContainingIntegers
end
end
