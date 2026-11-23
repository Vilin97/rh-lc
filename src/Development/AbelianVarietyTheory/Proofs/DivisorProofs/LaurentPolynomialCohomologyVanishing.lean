module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomology
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

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeGroupCohomologyStrictlyHenselian

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem GlobalTheory.gm_cohomology_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧
      Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  first
  | exact @_root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology
  | exact _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology
  | (apply _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> assumption)
  | (intros; apply _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LaurentCohomologyVanishing.laurent_cohomology ..)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeGroupCohomologyStrictlyHenselianStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.multiplicativeGroup_cohomology_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ n i : ℤ, (2 ≤ n → Subsingleton (Ht q (sp (LaurentPolynomial A)) n i)) ∧ Nonempty (Ht q (sp (LaurentPolynomial A)) 1 i ≃+ ZMod q) := by
  first | (exact @GlobalTheory.gm_cohomology_strictlyHenselian) | (exact GlobalTheory.gm_cohomology_strictlyHenselian) | (intros; apply GlobalTheory.gm_cohomology_strictlyHenselian  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentPolynomialCohomologyVanishing

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem laurentPolynomial_cohomology_strictlyHenselian_vanishing : GlobalTheory.EtC.C5 := fun q _ A _ hA hq n i => GlobalTheory.T.multiplicativeGroup_cohomology_strictlyHenselian q A hA hq n i

end GlobalTheory.EtC
end
end
