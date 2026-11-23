module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionsNefPlusAmpleGeneratedGenericFibreStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedModelDominantCurveRestriction
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefShiftOfGeneratedAtCharZeroPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemipositiveNonnegCombination

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOnFiniteFieldFibresPowTens

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

open GlobalTheory.CechPic

namespace GlobalTheory.NefFibTens

theorem nefFib_pow_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → NefFib A → NefFib ((L.pow n).tens A) := by
  intro k _ X _ p D hX L A n hL hA Z i _ _ κ _ _ _ hd
  have : Module.Finite ℤ k := hX.finite
  have hp : IsProjOver p := hX.isProjOver
  rw [NefHodgeTateAt.topSelf_of_cls_eq_add hp ((L.pow n).tens A).isLB (L.pow n).isLB A.isLB
    (cls_tens (L.pow n).isLB A.isLB _) Z i κ hd, NefHodgeTateAt.topSelf_pow hp L n Z i κ hd]
  exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) (hL Z i κ hd)) (hA Z i κ hd)

end GlobalTheory.NefFibTens
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOnFiniteFieldFibresPowTensStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.nefOnFiniteFieldFibres_pow_tens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), NefFib L → NefFib A → NefFib ((L.pow n).tens A) := by
  first | exact @GlobalTheory.NefFibTens.nefFib_pow_tens | exact GlobalTheory.NefFibTens.nefFib_pow_tens | (intros; apply GlobalTheory.NefFibTens.nefFib_pow_tens <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMetricShiftIsNefPowTensAmple

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem exists_isNef_shift_pow_tens : GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), L.SemiPos D → NefFib L → IsAmpleLB A.B → A.IsNef D → ∃ t : ℝ, (((L.pow n).tens A).shift (fun _ => t) fun _ => rfl).IsNef D := by
  intro hC hN k _ X _ p D hX L A n hL hLf hA hAn
  obtain ⟨m, N, s, hm, hs⟩ := GlobalTheory.T.exists_sections_nefPlusAmple_generated_genericFibre hN k X p D hX L A n hLf hA
  obtain ⟨t, -, ht⟩ := GlobalTheory.NefOfGen.nef_of_gen hC k X p D hX ((L.pow n).tens A) m N s hm hs
    ((hL.pow n).tens hAn.semiPos) (GlobalTheory.T.nefOnFiniteFieldFibres_pow_tens k X p D hX L A n hLf (nefFib_of_isNef hAn))
  exact ⟨t, ht⟩

end GlobalTheory.VolBr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMetricShiftIsNefPowTensAmpleStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.exists_metricShift_isNef_pow_tens_ample : GlobalTheory.Published.ArCalc → GlobalTheory.Published.NefNumerics → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L A : HermLB p) (n : ℕ), L.SemiPos D → NefFib L → IsAmpleLB A.B → A.IsNef D → ∃ t : ℝ, (((L.pow n).tens A).shift (fun _ => t) fun _ => rfl).IsNef D := by
  first | exact @GlobalTheory.VolBr.exists_isNef_shift_pow_tens | exact GlobalTheory.VolBr.exists_isNef_shift_pow_tens | (intros; apply GlobalTheory.VolBr.exists_isNef_shift_pow_tens <;> assumption)
end
end
