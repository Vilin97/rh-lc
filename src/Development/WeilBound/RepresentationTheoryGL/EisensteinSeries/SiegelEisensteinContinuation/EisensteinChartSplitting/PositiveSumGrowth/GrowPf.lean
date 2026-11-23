module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSumModerateGrowthConvergent

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.EisConvGrowth

theorem eis_modGrowth : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → (V.rank : ℝ) / 2 < s₁.re → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V φ) := by
  intro D V a ha hI μ s₁ φ hφ h
  haveI := t2Space_adeleRing' (F := D.host.F)
  obtain ⟨C₁, hC₁⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s₁.re + (V.rank : ℝ) / 2) :=
    hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  obtain ⟨C₂, hC₂, h₂⟩ := GlobalTheory.SWAbsGrowth.hgt_mul_le V a ha
  set τ : ℝ := s₁.re + (V.rank : ℝ) / 2 with hτ
  have hτ0 : 0 ≤ τ := by
    have : (0 : ℝ) ≤ (V.rank : ℝ) / 2 := by positivity
    linarith
  have hs := GlobalTheory.Eis.sphConv D V a hI s₁.re h
  set S := ∑' q : GlobalTheory.Eis.SiegelCosets V, (hgt V a (q.out : GQ (dblSp V)) : ℝ) ^ τ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set M : ℕ := ⌈τ⌉₊ with hM
  refine ⟨max C₁ 0 * (max C₂ 1) ^ M * S, 2 * V.rank * M, fun y => ?_⟩
  set H := GlobalTheory.Grow.height (dblSp V) y with hH
  have hH1 : 1 ≤ H := GlobalTheory.Grow.one_le_height _ y
  set K := max C₂ 1 * H ^ (2 * V.rank) with hK
  have hone : 1 ≤ K := one_le_mul_of_one_le_of_one_le (le_max_right _ _) (one_le_pow₀ hH1)
  set c := max C₁ 0 * K ^ M with hc
  have hq : ∀ x : GA D (dblSp V), ‖φ (x * y)‖ ≤ c * (hgt V a x : ℝ) ^ τ := by
    intro x
    refine (hC₁ _).trans ?_
    refine (mul_le_mul_of_nonneg_right (le_max_left C₁ 0) (by positivity)).trans ?_
    rw [hc, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
    have h3 : (hgt V a (x * y) : ℝ) ≤ hgt V a x * K :=
      (h₂ x y).trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (NNReal.coe_nonneg _))
    refine (Real.rpow_le_rpow (NNReal.coe_nonneg _) h3 hτ0).trans ?_
    rw [Real.mul_rpow (NNReal.coe_nonneg _) (by positivity), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [← Real.rpow_natCast _ M]
    exact Real.rpow_le_rpow_of_exponent_le hone (Nat.le_ceil τ)
  have hsum : HasSum (fun q : GlobalTheory.Eis.SiegelCosets V => c * (hgt V a (q.out : GQ (dblSp V)) : ℝ) ^ τ) (c * S) :=
    hs.hasSum.mul_left c
  have hb : ‖GlobalTheory.Eis.eis V φ y‖ ≤ c * S := tsum_of_norm_bounded hsum fun q => hq _
  refine hb.trans (le_of_eq ?_)
  rw [hc, hK, mul_pow, ← pow_mul]
  ring

end GlobalTheory.EisConvGrowth

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelEisensteinSumModerateGrowthConvergentStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.siegelEisensteinSum_moderateGrowth_convergent : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ (μ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : GA D (dblSp V) → ℂ), φ ∈ degPS V a μ s₁ → (V.rank : ℝ) / 2 < s₁.re → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V φ) := by
  first | exact @GlobalTheory.EisConvGrowth.eis_modGrowth | exact GlobalTheory.EisConvGrowth.eis_modGrowth | (intros; apply GlobalTheory.EisConvGrowth.eis_modGrowth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSiegelEisensteinModerateGrowthConvergen

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.SphGrowth

theorem spherical_eisenstein_modGrowth : ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (σ : ℂ))) :=
  fun D V _ a ha hI σ hσ => GlobalTheory.T.siegelEisensteinSum_moderateGrowth_convergent D V a ha hI 1 σ _ (GlobalTheory.Eis.sph_mem hI (σ : ℂ)) (by simpa using hσ)

end GlobalTheory.Core.Rk.SphGrowth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSiegelEisensteinModerateGrowthConvergenStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP


theorem _root_.GlobalTheory.T.sphericalSiegelEisenstein_moderate_growth_convergent : ∀ (D : D7) (V : HSp D), 0 < V.rank → ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) → ∀ σ : ℝ, (V.rank : ℝ) / 2 < σ → GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (σ : ℂ))) := by
  first | exact @GlobalTheory.Core.Rk.SphGrowth.spherical_eisenstein_modGrowth | exact GlobalTheory.Core.Rk.SphGrowth.spherical_eisenstein_modGrowth | (intros; apply GlobalTheory.Core.Rk.SphGrowth.spherical_eisenstein_modGrowth <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.EisensteinChartSplitting.PositiveSumGrowth.GrowPf

section

@[expose] public section

noncomputable section

open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.AutomorphicL2Unitary
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace ResidueKilled.Tr

theorem posSum_growth' (D : D7) (V : HSp D) (hV : 0 < V.rank) (a : GL (Fin V.rank) (AE D)) (ha : IsMaj V a)
    (hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a)) (p : GA D (dblSp V)) (c : ℝ≥0) (hc : 0 < c)
    (h : GA D (dblSp V) → ℝ) (hh : ∀ x, h x = Real.log (hgt V a (x * p⁻¹)) + Real.log c) (t : ℝ)
    (ht : (V.rank : ℝ) < t) : ∃ (C : ℝ) (N : ℕ), ∀ g,
      ‖GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V)) (fun x => (Real.exp (t * h x) : ℂ)) g‖ ≤
        C * GlobalTheory.Grow.height (dblSp V) g ^ N := by
  have hσ : (V.rank : ℝ) / 2 < t - (V.rank : ℝ) / 2 := by linarith
  obtain ⟨C₀, A, hC₀⟩ := GlobalTheory.T.sphericalSiegelEisenstein_moderate_growth_convergent D V hV a ha hI (t - (V.rank : ℝ) / 2) hσ
  have hpos : ∀ y, 0 < hgt V a y := fun y => hgtH_pos _
  have hf : (fun x => (Real.exp (t * h x) : ℂ)) = (Real.exp (t * Real.log c) : ℂ) •
      fun x => GlobalTheory.Eis.sph V a (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ) (x * p⁻¹) := by
    funext x
    have e : (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ) + (V.rank : ℂ) / 2 = (t : ℂ) := by push_cast; ring
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.Eis.sph]
    rw [npow_eq_exp (hpos _), e, hh x, ← Complex.ofReal_mul, ← Complex.ofReal_exp,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  refine ⟨Real.exp (t * Real.log c) * |C₀| * GlobalTheory.Grow.height (dblSp V) p⁻¹ ^ A, A, fun g => ?_⟩
  rw [hf, GlobalTheory.Eis.cosetSum_smul, GlobalTheory.Eis.cosetSum_mul_right, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have h1 := hC₀ (g * p⁻¹)
  have h2 : GlobalTheory.Grow.height (dblSp V) (g * p⁻¹) ^ A ≤
      (GlobalTheory.Grow.height (dblSp V) g * GlobalTheory.Grow.height (dblSp V) p⁻¹) ^ A :=
    pow_le_pow_left₀ (GlobalTheory.Grow.height_pos _ _).le (GlobalTheory.Grow.height_mul_le _ _ _) A
  have h3 : 0 ≤ GlobalTheory.Grow.height (dblSp V) (g * p⁻¹) ^ A := pow_nonneg (GlobalTheory.Grow.height_pos _ _).le A
  have h4 : ‖GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ)) (g * p⁻¹)‖ ≤
      |C₀| * (GlobalTheory.Grow.height (dblSp V) g * GlobalTheory.Grow.height (dblSp V) p⁻¹) ^ A :=
    h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self C₀) h3).trans (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)))
  calc Real.exp (t * Real.log c) * ‖GlobalTheory.Eis.cosetSum (siegel V) (GQ (dblSp V))
        (GlobalTheory.Eis.sph V a (((t - (V.rank : ℝ) / 2 : ℝ)) : ℂ)) (g * p⁻¹)‖
      ≤ Real.exp (t * Real.log c) * (|C₀| * (GlobalTheory.Grow.height (dblSp V) g * GlobalTheory.Grow.height (dblSp V) p⁻¹) ^ A) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = Real.exp (t * Real.log c) * |C₀| * GlobalTheory.Grow.height (dblSp V) p⁻¹ ^ A * GlobalTheory.Grow.height (dblSp V) g ^ A := by
        rw [mul_pow]; ring

end ResidueKilled.Tr
end
end
end
