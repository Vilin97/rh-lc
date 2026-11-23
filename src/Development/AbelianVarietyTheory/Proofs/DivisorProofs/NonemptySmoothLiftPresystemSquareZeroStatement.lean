module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftHomOfReductionSquareZeroSmooth
public import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Smooth.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLiftOfRetractSquareZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardSmoothRetractOfSmoothStatement
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSmoothLiftOverSqZeroThickening
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardSmoothLiftOverSqZeroThickeningStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.standardSmooth_lift_over_sqZero_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.IsStandardSmooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  first | exact @GlobalTheory.Obs.standardSmooth_lift_of_sqZero | exact GlobalTheory.Obs.standardSmooth_lift_of_sqZero | (intros; apply GlobalTheory.Obs.standardSmooth_lift_of_sqZero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLiftsOverSquareZeroThickening

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem smooth_lifts_over_sqZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  intro R R₀ _ _ I hI π hπ hk B₀ _ _ hsm
  obtain ⟨C₀, _, _, i, r, hstd, hri⟩ := GlobalTheory.T.exists_standardSmooth_retract_of_smooth R₀ B₀ hsm
  obtain ⟨C, _, _, p', hs', hp', hker', hC⟩ := GlobalTheory.T.standardSmooth_lift_over_sqZero_thickening R R₀ I hI π hπ hk C₀ hstd
  exact GlobalTheory.T.exists_smoothLift_of_retract_squareZero R R₀ I hI π hπ hk C C₀ p' hs' hp' hker' B₀ i r hri

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLiftsOverSquareZeroThickeningStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.smoothAlgebra_lifts_over_square_zero_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  first | exact @GlobalTheory.smooth_lifts_over_sqZero | exact GlobalTheory.smooth_lifts_over_sqZero | (intros; apply GlobalTheory.smooth_lifts_over_sqZero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftPresystemSquareZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem pre_nonempty : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀), (∀ T, Algebra.Smooth R₀ (F.obj T)) → Nonempty (Pre I π F) := by
  intro R R₀ _ _ I hI π hπ hk C _ F hF
  have h := fun T => GlobalTheory.T.smoothAlgebra_lifts_over_square_zero_thickening R R₀ I hI π hπ hk (F.obj T) (hF T)
  choose B iB aB p hs hp hker hsm using h
  letI := iB
  letI := aB
  have hl : ∀ {T T' : C} (a : T ⟶ T'), ∃ ρ : B T →ₐ[R] B T', ∀ b, p T' (ρ b) = mp F a (p T b) :=
    fun {T T'} a => homLift R R₀ I hI π hπ hk (B T) (F.obj T) (p T) (hs T) (hp T) (hker T)
      (B T') (F.obj T') (p T') (hs T') (hp T') (hker T') (mp F a)
  exact ⟨{ B := fun T => CommAlgCat.of R (B T)
           p := p
           semi := hs
           surj := hp
           ker := hker
           smooth := hsm
           ρ := fun a => (hl a).choose
           nat := fun a b => (hl a).choose_spec b }⟩

end GlobalTheory.Obs
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySmoothLiftPresystemSquareZeroStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonempty_smoothLiftPresystem_squareZero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀), (∀ T, Algebra.Smooth R₀ (F.obj T)) → Nonempty (Pre I π F) := by
  first | exact @GlobalTheory.Obs.pre_nonempty | exact GlobalTheory.Obs.pre_nonempty | (intros; apply GlobalTheory.Obs.pre_nonempty <;> assumption)
end
end
