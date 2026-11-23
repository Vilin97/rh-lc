module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInNormalAt
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TorusAlgebraicHolds
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
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
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsLieBasisIffIsUnitDet
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusConstMul
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.EllipsoidStA

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyInClassicalFrame

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.KeyOfPeriod

theorem exists_keyIn_classicalFrame :
    ∀ (g : ℕ) (τ₀ : Matrix (Fin g) (Fin g) ℂ) (a₀ b₀ : Fin g → ℂ), 1 ≤ g → τ₀.IsSymm → (τ₀.map Complex.im).PosDef → (∀ i, a₀ i = 0 ∨ a₀ i = 1 / 2) → (∀ i, b₀ i = 0 ∨ b₀ i = 1 / 2) → ∃ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L x.P.g) (τ : Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (a b : Fin x.P.g → ℂ), τ = τ₀.submatrix (Fin.cast h) (Fin.cast h) ∧ (a = fun i => a₀ (i.cast h)) ∧ (b = fun i => b₀ (i.cast h)) ∧ τ.IsSymm ∧ (τ.map Complex.im).PosDef ∧ (∀ i, a i = 0 ∨ a i = 1 / 2) ∧ (∀ i, b i = 0 ∨ b i = 1 / 2) ∧ (∀ z, z ∈ u.Λ ↔ ∃ m n : Fin x.P.g → ℤ, z = (fun i => (m i : ℂ)) + τ.mulVec (fun i => (n i : ℂ))) ∧ u.IsRig x.rig ∧ u.IsFn x.th (thetaChar τ a b) ∧ (∀ i, u.IsDiff (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (x.v i)) := by
  intro g τ₀ a₀ b₀ hg hs hp ha hb
  obtain ⟨x, h, hx⟩ := exists_keyIn_normalAt GlobalTheory.thetaUnifAV_all GlobalTheory.torusAlgebraic_holds g τ₀ a₀ b₀ hg hs hp
    ⟨ha, hb⟩
  obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (GlobalTheory.KeyPow.normalAt_one_iff x _ _ _).1 hx
  exact ⟨x, h, u, _, _, _, rfl, rfl, rfl, h₁, h₂, fun i => ha _, fun i => hb _, h₃, h₄, h₅, h₆⟩

end GlobalTheory.KeyOfPeriod
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyInNf

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

namespace GlobalTheory.MBLow.Cl

theorem exists_keyIn_nf :
    ∀ (g : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℂ) (c : ℂ) (Mx : Matrix (Fin g) (Fin g) ℂ), 1 ≤ g → τ.IsSymm → (τ.map Complex.im).PosDef → Half a → Half b → c ≠ 0 → Mx.det ≠ 0 → ∃ (x : KeyIn ℂ) (hg : x.P.g = g) (u : HolUnif x.P.A x.P.L g), NF x hg u τ a b c (fun j => (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx j) := by
  intro g τ a b c Mx hg hs hp ha hb hc hM
  obtain ⟨x, h, u, τ', a', b', e₁, e₂, e₃, -, -, -, -, h₃, h₄, h₅, h₆⟩ :=
    GlobalTheory.KeyOfPeriod.exists_keyIn_classicalFrame g τ a b hg hs hp ha hb
  subst h
  obtain rfl : τ' = τ := e₁
  obtain rfl : a' = a := e₂
  obtain rfl : b' = b := e₃
  have := x.P.isAb.comm
  obtain ⟨hex, -, -, -, hbas⟩ := LieComb.lieComb_algebra ℂ x.P.A x.P.g x.v x.basis.1
  choose v hv using fun i => (hex (Mx i)).exists
  refine ⟨⟨x.P, x.g_pos, x.rig, x.rig_gen, KeyNormalExists.constMul x.P.A.hom c x.th, fun s => ?_, v,
    (hbas Mx v x.basis hv).2 hM.isUnit⟩, rfl, u, hs, hp, ha, hb, hc, h₃, h₄,
    KeyNormalExists.isFn_constMul u c h₅, fun i => ?_⟩
  · obtain ⟨z, hz, hz'⟩ := x.th_ne s
    exact ⟨z, hz, KeyNormalExists.mem_nonzeroLocus_constMul _ hc.isUnit _ hz'⟩
  · have h1 := UnifDifferential.isDiff_of_isLieComb _ _ _ _ u _ x.v (Mx i) (v i) x.basis.1 h₆ (hv i)
    have e : ∑ j, Mx i j • (Pi.single j (2 * Real.pi * Complex.I : ℂ)⁻¹ : Fin x.P.g → ℂ) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • Mx i := by
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, MulZeroClass.mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    rw [e] at h1
    exact h1

end GlobalTheory.MBLow.Cl
end
end
