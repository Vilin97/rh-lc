module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselCoreVertexLatticeSplitsAlongOrthDecompositStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselVertexLatticeSplitsAlongWitt
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsConjugateInverseStaircaseModulusIdealStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiVertexLatticeSplitsAlongWittAtPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeDepthLatticeOfPairStatement
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittCoreInclusionMemCompletedHomLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NsmulProjectionXColumnsMemSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualBesselCoreVertexLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualFractionalIdealSmulLatticeOfNormOneStatement
import Mathlib.Tactic.ReduceModChar
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsSelfDualCOfBase
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselVertexLatticeSplitsAlongWittStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.bessel_vertex_lattice_splits_along_witt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v := by
  first | exact @GlobalTheory.MonoBes.monoAt_bes | exact GlobalTheory.MonoBes.monoAt_bes | (intros; apply GlobalTheory.MonoBes.monoAt_bes <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiVertexLatticeSplitsAlongWittAtPlaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.fourierJacobiVertexLattice_splitsAlongWitt_at_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D), MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v := by
  first | exact @GlobalTheory.AscFin.MonoJac.monoAt_jac | exact GlobalTheory.AscFin.MonoJac.monoAt_jac | (intros; apply GlobalTheory.AscFin.MonoJac.monoAt_jac <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeLatOSelfDual

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem finLat_latO_selfDual : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → FinLat (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := fun S T ΛS ΛT hS hT => GlobalTheory.AscFinWit.finLat_latO (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hS) (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hT)

end GlobalTheory.AscFin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFiniteAdelicMatrixLatticeLatOSelfDualStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.isFiniteAdelicMatrixLattice_latO_selfDual : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → FinLat (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.AscFin.finLat_latO_selfDual | exact GlobalTheory.AscFin.finLat_latO_selfDual | (intros; apply GlobalTheory.AscFin.finLat_latO_selfDual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualBesselCoreVertexLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.isSelfDual_besselCoreVertexLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → ∀ (ρ : ℕ) (h : 2 * ρ + 2 ≤ D.R.m), IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) := by
  first | exact @GlobalTheory.AscFin.isSelfDualC_lat0 | exact GlobalTheory.AscFin.isSelfDualC_lat0 | (intros; apply GlobalTheory.AscFin.isSelfDualC_lat0 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualStandardFrameLineLattice

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin

theorem isSelfDualC_span_of_norm {D : D7} (S : HSp D) (hS : S.rank = 1) (ζ : Fin S.rank → D.host.E)
    (hζ : star ζ ⬝ᵥ (HSpace.gram S *ᵥ ζ) = -1) :
    IsSelfDualC S (Submodule.span (𝓞 D.host.E) {ζ}) := by
  have hform : ∀ x y : Fin S.rank → D.host.E,
      ∑ i, ∑ j, star (x i) * HSpace.gram S i j * y j = star x ⬝ᵥ (HSpace.gram S *ᵥ y) := by
    intro x y
    simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]
  have hne : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  haveI : Subsingleton (Fin S.rank) := by rw [hS]; infer_instance
  obtain ⟨i₀, hi₀⟩ : ∃ i, ζ i ≠ 0 := Function.ne_iff.mp hne
  have hall : ∀ y : Fin S.rank → D.host.E, ∃ c : D.host.E, y = c • ζ := by
    intro y
    refine ⟨y i₀ / ζ i₀, funext fun i => ?_⟩
    rw [Subsingleton.elim i i₀, Pi.smul_apply, smul_eq_mul, div_mul_cancel₀ _ hi₀]
  have hpair : ∀ a c : D.host.E, star (a • ζ) ⬝ᵥ (HSpace.gram S *ᵥ (c • ζ)) = -(star a * c) := by
    intro a c
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul, hζ, smul_eq_mul, smul_eq_mul]
    ring
  have hstar : ∀ a : 𝓞 D.host.E, IsIntegral ℤ (star (a : D.host.E)) := fun a =>
    (map_isIntegral_int (starRingEnd D.host.E) a.2 : )
  refine ⟨⟨Submodule.fg_span_singleton _, ?_⟩, fun y => ?_⟩
  · exact fun _ _ => (LinearIndependent.iff_fractionRing (𝓞 D.host.E) D.host.E).mp
  · obtain ⟨c, rfl⟩ := hall y
    constructor
    · intro hy x hx
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hy
      rw [← hb, hform]
      refine ⟨-(⟨_, hstar a⟩ * b), ?_⟩
      have := hpair a b
      simp only [← algebraMap_smul D.host.E a, ← algebraMap_smul D.host.E b]
      rw [this]
      rfl
    · intro h
      obtain ⟨b, hb⟩ := h ζ (Submodule.mem_span_singleton_self _)
      have h1 := hpair 1 c
      rw [one_smul, star_one, one_mul] at h1
      rw [hform, h1] at hb
      refine Submodule.mem_span_singleton.mpr ⟨-b, ?_⟩
      rw [← algebraMap_smul D.host.E (-b)]
      congr 1
      rw [map_neg]
      exact neg_eq_iff_eq_neg.mpr hb

theorem isSelfDualC_line : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → IsSelfDualC (negSp F.Lz) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
  intro D T L sc G F hF
  refine isSelfDualC_span_of_norm (negSp F.Lz) F.rk (F.ζ 0) ?_
  have h1 := congrFun (congrFun G.sp.dec0.gram 0) 0
  have h2 : star (fun i => G.sp.dec0.a i 0) ⬝ᵥ (HSpace.gram (G.V (Node.core 0)) *ᵥ (fun i => G.sp.dec0.a i 0)) = 1 := by
    have h3 : antiDiagonalSignGramMatrix 1 (1 : D.host.E) 0 0 = 1 := by simp [antiDiagonalSignGramMatrix]
    rw [h3, Matrix.mul_assoc] at h1
    exact h1
  rw [← hF.zB, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, F.oz.isoB] at h2
  rw [negSp_gram, neg_mulVec, dotProduct_neg]
  exact congrArg Neg.neg h2

end GlobalTheory.AscFin

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualStandardFrameLineLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.isSelfDual_standardFrame_lineLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (F : Frames G), Std F → IsSelfDualC (negSp F.Lz) (Submodule.span (𝓞 D.host.E) {F.ζ 0}) := by
  first | exact @GlobalTheory.AscFin.isSelfDualC_line | exact GlobalTheory.AscFin.isSelfDualC_line | (intros; apply GlobalTheory.AscFin.isSelfDualC_line <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplitting

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.GridLat

theorem lattices_grid : OnStd fun {D} _ _ {sc} {G} W F => (∀ i, i < D.R.m → FinLat (latRow G i) ∧ FinLat (latCore G i) ∧ FinLat (latBig G i) ∧ IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))) ∧ (∀ ρ h, IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) ∧ (∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v ∧ MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v) ∧ IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) ∧ ∀ v, OrthAt (F.oB ρ h) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) v) ∧ ∀ ρ, IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ ρ * (G.pl.stAbar sc ^ ρ)⁻¹ * shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  intro D hq T L μ0 hL sc G W M hM F hF
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := by
    intro i hi
    cases i with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).sd
  have sdP : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.core i)) (G.Λ (.core i)) := fun i hi => (G.sp.P_is i hi).sd
  have sdShift : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    intro i hi
    obtain ⟨I', h1, h2⟩ := GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal G.pl sc 0 1
    simp only [pow_zero, pow_one, inv_one, one_mul] at h1 h2
    exact GlobalTheory.T.isSelfDual_fractionalIdealSmulLattice_of_norm_one _ _ _ I' (sdG i hi) h1 h2
  have sdLine : ∀ a b : ℕ, IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ a * (G.pl.stAbar sc ^ a)⁻¹ *
      (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b *
        (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹))
      (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
    intro a b
    obtain ⟨I', h1, h2⟩ := GlobalTheory.T.exists_conjugate_inverse_staircase_modulus_ideal G.pl sc a b
    exact GlobalTheory.T.isSelfDual_fractionalIdealSmulLattice_of_norm_one _ _ _ I' (GlobalTheory.T.isSelfDual_standardFrame_lineLattice F hF) h1 h2
  refine ⟨fun i hi => ⟨GlobalTheory.T.isFiniteAdelicMatrixLattice_depthLatticeOfPair G (.chi i 0) (isSelfDualC_neg (sdG (i + 1) hi)) (sdG i hi.le),
    GlobalTheory.T.isFiniteAdelicMatrixLattice_depthLatticeOfPair G (.core i) (isSelfDualC_neg (sdP (i + 1) hi)) (sdP i hi.le),
    GlobalTheory.T.isFiniteAdelicMatrixLattice_latO_selfDual _ _ _ _ (sdG (i + 1) hi) (sdShift i hi.le), sdShift i hi.le⟩,
    fun ρ h => ⟨GlobalTheory.T.isSelfDual_besselCoreVertexLattice F hF ρ h, fun v => ⟨GlobalTheory.T.bessel_vertex_lattice_splits_along_witt F hF ρ h v, GlobalTheory.T.fourierJacobiVertexLattice_splitsAlongWitt_at_place F hF ρ h v⟩, ?_, fun v => GlobalTheory.T.orthAt_oB_lat0_of_std F hF ρ h v⟩,
    fun ρ => ?_⟩
  · have := sdLine (ρ + 1) 0
    simpa only [pow_zero, inv_one, mul_one] using this
  · have := sdLine ρ 1
    simp only [pow_one] at this
    exact this

end GlobalTheory.AscFin.GridLat

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.grid_lattices_compact_selfDual_splitting : OnStd fun {D} _ _ {sc} {G} W F => (∀ i, i < D.R.m → FinLat (latRow G i) ∧ FinLat (latCore G i) ∧ FinLat (latBig G i) ∧ IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))) ∧ (∀ ρ h, IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) ∧ (∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v ∧ MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v) ∧ IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) ∧ ∀ v, OrthAt (F.oB ρ h) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) v) ∧ ∀ ρ, IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ ρ * (G.pl.stAbar sc ^ ρ)⁻¹ * shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  first | exact @GlobalTheory.AscFin.GridLat.lattices_grid | exact GlobalTheory.AscFin.GridLat.lattices_grid | (intros; apply GlobalTheory.AscFin.GridLat.lattices_grid <;> assumption)
end
end
