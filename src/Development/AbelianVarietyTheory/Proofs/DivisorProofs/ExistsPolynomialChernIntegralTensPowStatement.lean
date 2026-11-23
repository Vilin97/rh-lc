module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifoldStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegrableOnTargetOfTsupport
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMongeAmpereMassAddZsmul

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.MongeAmperePoly

variable {X : Type} [TopologicalSpace X]

theorem update_comp_swap {e : ℕ} (Φ : Fin (e + 1) → LocPot X) (i : Fin (e + 1)) (P : LocPot X) :
    Function.update Φ i P ∘ Equiv.swap 0 i =
      (Fin.cons P (fun k => Φ (Equiv.swap 0 i k.succ)) : Fin (e + 1) → LocPot X) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp
  · have h : Equiv.swap 0 i k.succ ≠ i := by
      intro h
      have h2 : Equiv.swap 0 i k.succ = Equiv.swap 0 i 0 := by rw [h, Equiv.swap_apply_left]
      exact Fin.succ_ne_zero k ((Equiv.swap 0 i).injective h2)
    simp [Function.update_of_ne h]

theorem mInt_update_add_zsmul [CompactSpace X] [T2Space X] {e : ℕ} (A : FinHolAtlas e X)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (i : Fin e) (P Q : LocPot X)
    (hP : IsPotential A P) (hQ : IsPotential A Q) (m : ℤ) :
    mInt A (Function.update Φ i (P + Q.zsmul m)) (fun _ => 1) =
      mInt A (Function.update Φ i P) (fun _ => 1) +
        m * mInt A (Function.update Φ i Q) (fun _ => 1) := by
  cases e with
  | zero => exact i.elim0
  | succ e =>
    have key : ∀ R : LocPot X, mInt A (Function.update Φ i R) (fun _ => 1) =
        mInt A (Fin.cons R (fun k => Φ (Equiv.swap 0 i k.succ))) (fun _ => 1) := by
      intro R
      rw [← update_comp_swap, mIntSymm]
    have hT : ∀ k : Fin e, IsPotential A (Φ (Equiv.swap 0 i k.succ)) := fun k => hΦ _
    have hI : ∀ R : LocPot X, IsPotential A R →
        MIntegrable A (Fin.cons R (fun k => Φ (Equiv.swap 0 i k.succ))) (fun _ => 1) := by
      intro R hR
      refine mIntegrableCont A _ (fun k => ?_) _ continuous_const
      refine Fin.cases ?_ (fun k => ?_) k
      · simpa using hR
      · simpa using hT k
    have hQm := isPotentialZsmul A m Q hQ
    rw [key, key, key, mIntAdd A P _ _ hP hQm hT _ (hI _ hP) (hI _ hQm),
      mIntZsmul A m Q _ hQ hT]

theorem exists_poly_finset [CompactSpace X] [T2Space X] {e : ℕ} (A : FinHolAtlas e X)
    (Ψ : Fin e → LocPot X) (hΨ : ∀ i, IsPotential A (Ψ i)) (S : Finset (Fin e)) :
    ∀ Φ : Fin e → LocPot X, (∀ i, IsPotential A (Φ i)) → ∃ P : Polynomial ℝ, ∀ m : ℤ,
      mInt A (fun i => if i ∈ S then Φ i + (Ψ i).zsmul m else Φ i) (fun _ => 1) =
        P.eval (m : ℝ) := by
  induction S using Finset.induction_on with
  | empty =>
    intro Φ _
    exact ⟨Polynomial.C (mInt A Φ (fun _ => 1)), fun m => by simp⟩
  | insert a S ha ih =>
    intro Φ hΦ
    have hΦ' : ∀ i, IsPotential A (Function.update Φ a (Ψ a) i) := by
      intro i
      by_cases h : i = a
      · subst h; simpa using hΨ i
      · simpa [Function.update_of_ne h] using hΦ i
    obtain ⟨P₁, h₁⟩ := ih Φ hΦ
    obtain ⟨P₂, h₂⟩ := ih _ hΦ'
    refine ⟨P₁ + Polynomial.X * P₂, fun m => ?_⟩
    set F : Fin e → LocPot X := fun i => if i ∈ S then Φ i + (Ψ i).zsmul m else Φ i with hF
    have hFp : ∀ i, IsPotential A (F i) := by
      intro i
      by_cases h : i ∈ S
      · simpa [hF, h] using isPotentialAdd A _ _ (hΦ i) (isPotentialZsmul A m _ (hΨ i))
      · simpa [hF, h] using hΦ i
    have e0 : (fun i => if i ∈ insert a S then Φ i + (Ψ i).zsmul m else Φ i) =
        Function.update F a (Φ a + (Ψ a).zsmul m) := by
      funext i
      by_cases h : i = a
      · subst h; simp
      · simp [hF, Function.update_of_ne h, h]
    have e1 : Function.update F a (Φ a) = F := by
      funext i
      by_cases h : i = a
      · subst h; simp [hF, ha]
      · simp [Function.update_of_ne h]
    have e2 : Function.update F a (Ψ a) = fun i => if i ∈ S then
        Function.update Φ a (Ψ a) i + (Ψ i).zsmul m else Function.update Φ a (Ψ a) i := by
      funext i
      by_cases h : i = a
      · subst h; simp [ha]
      · simp [hF, Function.update_of_ne h]
    rw [e0, mInt_update_add_zsmul A F hFp a _ _ (hΦ a) (hΨ a), e1, e2, h₂ m]
    have := h₁ m
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
    rw [← this]

theorem mInt_add_zsmul_poly : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X]
    [T2Space X] (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) →
    (∀ i, IsPotential A (Ψ i)) → ∃ P : Polynomial ℝ, ∀ m : ℤ,
      mInt A (fun i => Φ i + (Ψ i).zsmul m) (fun _ => 1) = P.eval (m : ℝ) := by
  intro e X _ _ _ A Φ Ψ hΦ hΨ
  obtain ⟨P, hP⟩ := exists_poly_finset A Ψ hΨ Finset.univ Φ hΦ
  exact ⟨P, fun m => by simpa using hP m⟩

end GlobalTheory.MongeAmperePoly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialMongeAmpereMassAddZsmulStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.exists_polynomial_mongeAmpereMass_add_zsmul : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X), (∀ i, IsPotential A (Φ i)) → (∀ i, IsPotential A (Ψ i)) → ∃ P : Polynomial ℝ, ∀ m : ℤ, mInt A (fun i => Φ i + (Ψ i).zsmul m) (fun _ => 1) = P.eval (m : ℝ) := by
  first | exact @GlobalTheory.MongeAmperePoly.mInt_add_zsmul_poly | exact GlobalTheory.MongeAmperePoly.mInt_add_zsmul_poly | (intros; apply GlobalTheory.MongeAmperePoly.mInt_add_zsmul_poly <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChernIntegralTensPow

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory.ChernPoly

theorem chernInt_tens_pow_poly : ∀ (Y : Var ℂ) (L H : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L)
    (ψ : Weight Y.str (RingHom.id ℂ) H), φ.IsCInf → ψ.IsCInf → ∃ P : Polynomial ℝ,
      P.eval 0 = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) ∧ ∀ m : ℕ,
        Weight.chernInt (φ.tens (ψ.pow m)) Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  intro Y L H φ ψ hφ hψ
  obtain ⟨hc, ht, _, A, hA⟩ := GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold Y
  have := hc
  have := ht

  have hφs : φ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hφ
  have hψs : ψ.IsSmooth (AnRead.all Y.str (RingHom.id ℂ) Y.dim) :=
    (Weight.isCInf_iff_isSmooth _).1 hψ
  have hΦ : IsPotential A φ.locPot := hφs.isPotential hA
  have hΨ : IsPotential A ψ.locPot := hψs.isPotential hA

  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_polynomial_mongeAmpereMass_add_zsmul Y.dim _ A (fun _ => φ.locPot) (fun _ => ψ.locPot)
    (fun _ => hΦ) (fun _ => hΨ)

  refine ⟨P, ?_, fun m => ?_⟩
  · rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y L φ hφ).2 A hA, ← (by simpa using hP 0 :
      mInt A (fun _ => φ.locPot + ψ.locPot.zsmul 0) (fun _ => 1) = P.eval 0)]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine (Weight.sameForm_of_eq φ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A 0 _ hΨ))
      (fun x => ⟨pick φ.isLB x, mem_pick φ.isLB x, fun z => ?_⟩)).symm
    show φ.φ (pick φ.isLB x) z / 2 = φ.locPot.φ x z + ((0 : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.locPot_φ]
    simp
  · have hT : (φ.tens (ψ.pow m)).IsCInf := hφ.tens (hψ.zpow m)
    rw [(GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral Y _ _ hT).2 A hA, show ((m : ℕ) : ℝ) = (((m : ℕ) : ℤ) : ℝ) by push_cast; rfl,
      ← hP m]
    refine SameForm.mInt_eq (fun _ => ?_) _
    refine Weight.sameForm_of_eq _ hA (isPotentialAdd A _ _ hΦ (isPotentialZsmul A m _ hΨ))
      (fun x => ⟨(pick φ.isLB x, fun _ => pick ψ.isLB x),
        mem_ptsIn_inf.2 ⟨mem_pick φ.isLB x, mem_pow_iff.2 (mem_pick ψ.isLB x)⟩, fun z => ?_⟩)
    show (φ.φ (pick φ.isLB x) z + (ψ.zpow m).φ (fun _ => pick ψ.isLB x) z) / 2 =
      φ.locPot.φ x z + ((m : ℤ) : ℝ) * ψ.locPot.φ x z
    rw [Weight.zpow_φ, Weight.locPot_φ, Weight.locPot_φ]
    ring

end GlobalTheory.ChernPoly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolynomialChernIntegralTensPowStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

theorem _root_.GlobalTheory.T.exists_polynomial_chernIntegral_tens_pow : ∀ (Y : Var ℂ) (L H : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L) (ψ : Weight Y.str (RingHom.id ℂ) H), φ.IsCInf → ψ.IsCInf → ∃ P : Polynomial ℝ, P.eval 0 = Weight.chernInt φ Y.dim Set.univ (fun _ => 1) ∧ ∀ m : ℕ, Weight.chernInt (φ.tens (ψ.pow m)) Y.dim Set.univ (fun _ => 1) = P.eval (m : ℝ) := by
  first | exact @GlobalTheory.ChernPoly.chernInt_tens_pow_poly | exact GlobalTheory.ChernPoly.chernInt_tens_pow_poly | (intros; apply GlobalTheory.ChernPoly.chernInt_tens_pow_poly <;> assumption)
end
end
