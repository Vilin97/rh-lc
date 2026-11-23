module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPureTypePeriodOfSignatureSplit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfDefiniteStatement
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefinite

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsSplitPureTypePeriodOfSignatureSplitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_splitPureTypePeriod_of_signatureSplit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → SplitLat D → ∃ (P : D.La →+ (Fin g → ℂ)) (hP : IsPeriod D ty P), IsSplit hP := by
  first | exact @GlobalTheory.CompRat.exists_isSplit_of_splitLat | exact GlobalTheory.CompRat.exists_isSplit_of_splitLat | (intros; apply GlobalTheory.CompRat.exists_isSplit_of_splitLat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianLatticeSignatureSplitOfIndefiniteStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.hermitianLatticeSignatureSplit_of_indefinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0) → 3 ≤ D.p + D.q → 1 ≤ D.p → 1 ≤ D.q → SplitLat D := by
  first | exact @GlobalTheory.SplitGenus.splitLat_of_indefinite | exact GlobalTheory.SplitGenus.splitLat_of_indefinite | (intros; apply GlobalTheory.SplitGenus.splitLat_of_indefinite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsSplitPeriod

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompRat

theorem exists_isSplit_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → (D.p = 0 ∨ D.q = 0 ∨ (3 ≤ D.p + D.q ∧ (∃ D₁ : Datum H, D₁.p = 1 ∧ D₁.q = 0))) → ∀ i, ∃ (P : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P), IsSplit hP := by
  intro E _ _ _ H D l Xo σ g ty F _ _ hty _ hc i
  have hp : (F.Di i).p = D.p := (F.sig i).1
  have hq : (F.Di i).q = D.q := (F.sig i).2
  refine GlobalTheory.T.exists_splitPureTypePeriod_of_signatureSplit E H (F.Di i) g ty (by rw [hp, hq]; exact hty) ?_
  by_cases h0 : D.p = 0 ∨ D.q = 0
  · exact GlobalTheory.T.hermitianLatticeSignatureSplit_of_definite E H (F.Di i) (by rw [hp, hq]; exact h0)
  · have h1 : D.p ≠ 0 := fun h => h0 (Or.inl h)
    have h2 : D.q ≠ 0 := fun h => h0 (Or.inr h)
    rcases hc with h | h | ⟨h3, h4⟩
    · exact absurd h h1
    · exact absurd h h2
    · exact GlobalTheory.T.hermitianLatticeSignatureSplit_of_indefinite E H (F.Di i) h4 (by omega) (by omega) (by omega)

end GlobalTheory.CompRat
end
end
