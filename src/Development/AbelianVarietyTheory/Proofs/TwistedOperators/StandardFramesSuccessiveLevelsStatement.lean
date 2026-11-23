module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepBasePointColumnsPrimitiveStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplittingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralAdeleSmulDepthLatticeGridRowMemLatOStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InverseDifferentCompletionIffCharacterDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulFractionalIdealCompletionSubsetIffMemQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsLatticeDualZIdealMul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdVLeOfLoc
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LineLatAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualHomLatticeModulusShiftLocalEqLatO

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLatticeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.depthLatticeGridRow_local_eq_completed_homLattice : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0, ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (· = v) u → (u ∈ latRow G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  first | exact @GlobalTheory.RowLoc.latRow_at | exact GlobalTheory.RowLoc.latRow_at | (intros; apply GlobalTheory.RowLoc.latRow_at <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesFourierJacobiLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff Pointwise
open GlobalTheory.AscFin


open GlobalTheory.StairLine GlobalTheory.SeeSaw in
theorem GlobalTheory.AscFin.primAt_jac_std : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, PrimAt W.ψ (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  intro D hOff T L μ0 hL sc G W M hM F hF ρ h v hv
  obtain ⟨hc, he, -⟩ := hF.hJ ρ h
  have hlat := G.sp.colLat (2 * ρ + 1) (by omega) (by omega)
  let 𝔟 : Fin ρ → FI D := fun p => FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (p.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) p)
  have hline : ∀ p : Fin ρ, ∀ a, GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔
      a ∈ idV (𝔟 p) v := by
    intro p a
    have e1 : GlobalTheory.FinPl.colMul (F.dJ ρ h).jX p a = fun k => a * incA D ((-D.host.xi0) ^ (p.1 + 1) *
        (G.colDec (2 * ρ + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p)) := by
      funext k
      simp only [GlobalTheory.FinPl.colMul, HypDec.jX, rat, Matrix.map_apply, he, colsOf]
    rw [e1]
    have e2 : G.Λ (.grid (2 * ρ + 1) 0) = (G.colDec (2 * ρ + 1) (by omega) (by omega)).lat (G.Λ (.core (2 * ρ + 1)))
        (stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1)) := hlat
    rw [e2]
    exact line_mem_iff _ _ _ _ (by simp only [Fin.coe_castLE]; omega)
      (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)) v a
  intro i j hij s hs
  have hN : ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (G.pl.modul_ne_bot sc)
  have hN' : ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_ne_zero.2 ?_
    unfold Places.modulBar
    intro h0
    apply G.pl.modul_ne_bot sc
    have h1 := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using h1
  have hA : G.pl.stA sc ≠ 0 := mul_ne_zero (GlobalTheory.CuspCharLattice.host_AA_ne_zero _) (inv_ne_zero hN')
  have hB : G.pl.stAbar sc ≠ 0 := mul_ne_zero (GlobalTheory.Member.LatSelfDual.AAbar_ne_zero D) (inv_ne_zero hN)
  have hne : ∀ p, 𝔟 p ≠ 0 := fun p => mul_ne_zero
    (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact inv_ne_zero (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)))
    (by
      unfold stairId
      refine mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB)))
  have key : (∀ a : AE D, GlobalTheory.FinPl.colMul (F.dJ ρ h).jX j a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) →
      GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i (s * a) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v)) ↔
      ∀ a ∈ idV (𝔟 j) v, s * a ∈ idV (𝔟 i) v :=
    ⟨fun H a ha => (hline i _).1 (H a ((hline j a).2 ha)), fun H a hc => (hline i _).2 (H a ((hline j a).1 hc))⟩
  rw [key, GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient D v _ _ (hne j) (hne i) s hs, ← DiffDual.idV_dI_iff D W.ψ W.ψ_std v s hs]
  have hid : 𝔟 i * (𝔟 j)⁻¹ * (((G.pl.modul sc * G.pl.modulBar sc : Ideal (𝓞 D.host.E))) : FI D) = dI D := by
    have hst := stairId_succ (𝔞 := G.pl.stA sc) (c := 2 * ρ + 1 - 1) hB (Fin.castLE (by omega) i) (Fin.castLE (by omega) j)
      (by simp only [Fin.coe_castLE]; exact hij)
    have hSj : stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j) ≠ 0 := by
      unfold stairId
      exact mul_ne_zero (pow_ne_zero _ hA) (inv_ne_zero (pow_ne_zero _ hB))
    show FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (i.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) i) *
      (FractionalIdeal.spanSingleton _ (((-D.host.xi0) ^ (j.1 + 1))⁻¹) *
      stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j))⁻¹ * _ = _
    rw [hst]
    revert hSj
    generalize stairId (G.pl.stA sc) (G.pl.stAbar sc) (2 * ρ + 1 - 1) (Fin.castLE (by omega) j) = Sj
    intro hSj
    rw [FractionalIdeal.coeIdeal_mul, mul_inv, FractionalIdeal.spanSingleton_inv, inv_inv]
    unfold Places.stA Places.stAbar dI
    have hx : ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (-D.host.xi0) ^ (j.1 + 1) = -D.host.xi0 := by
      rw [hij, pow_succ (-D.host.xi0) (i.1 + 1), ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 cmHost_imaginaryGenerator_ne_zero)), one_mul]
    calc _ = FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ (((-D.host.xi0) ^ (i.1 + 1))⁻¹) *
          FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((-D.host.xi0) ^ (j.1 + 1)) * D.host.AA * D.host.AAbar *
          (Sj * Sj⁻¹) * (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) *
          (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D) * ((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FI D)⁻¹) := by ring
      _ = _ := by
        rw [mul_inv_cancel₀ hSj, mul_inv_cancel₀ hN, mul_inv_cancel₀ hN', FractionalIdeal.spanSingleton_mul_spanSingleton, hx,
          mul_one, mul_one, mul_one]
        congr 2
        rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
        exact ⟨-1, by simp⟩
  constructor
  · intro hs'
    refine idV_le_of_loc (fun z hz => ?_) hs'
    obtain ⟨t, ht, htm⟩ := exists_modul G.pl sc hv
    exact ⟨t, ht, by rw [← hid, mul_comm (algebraMap _ _ _)]; exact FractionalIdeal.mul_mem_mul hz htm⟩
  · intro hs'
    refine GlobalTheory.SeeSaw.idV_mono ?_ v hs'
    rw [← hid]
    calc _ ≤ 𝔟 i * (𝔟 j)⁻¹ * 1 := by first | exact FractionalIdeal.mul_left_mono _ FractionalIdeal.coeIdeal_le_one | exact mul_le_mul_right FractionalIdeal.coeIdeal_le_one _ | exact mul_le_mul_left FractionalIdeal.coeIdeal_le_one _ | exact mul_le_mul' le_rfl FractionalIdeal.coeIdeal_le_one
      _ = _ := mul_one _
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiPrimitiveStandardFramesFourierJacobiLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.psi_primitive_standardFrames_fourierJacobiLevel : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, PrimAt W.ψ (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) v := by
  first | exact @GlobalTheory.AscFin.primAt_jac_std | exact GlobalTheory.AscFin.primAt_jac_std | (intros; apply GlobalTheory.AscFin.primAt_jac_std <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualHomLatticeModulusShiftLocalEqLatOStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.selfDualHomLatticeModulusShift_local_eq_latO : All fun {D} _ _ _ {G} _ _ => ∀ i, i < D.R.m → ∀ v ∉ G.pl.S0, ∀ u : WO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)), MxAt (· = v) u → (u ∈ latBig G i ↔ u ∈ latO _ _ (G.Λ (.grid (i + 1) 0) : Set _) (G.Λ (.grid i 0) : Set _) (· = v)) := by
  first | exact @GlobalTheory.BigLoc.latBig_at | exact GlobalTheory.BigLoc.latBig_at | (intros; apply GlobalTheory.BigLoc.latBig_at <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFramesSuccessiveLevels

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.AscFin.GoodFB

theorem mxAt_mul {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {a : Mx D m n} (ha : MxAt P a) (b : Mx D n k) :
    MxAt P (a * b) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (ha i l)

theorem mxAt_mul_left {D : D7} {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (b : Mx D m n) {a : Mx D n k} (ha : MxAt P a) :
    MxAt P (b * a) := fun i j => by
  simp only [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (ha l j)

theorem goodAt_stdAt_fb : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.core (2 * σ + 3))) (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v ∧ StdAt (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  intro D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have I := GlobalTheory.T.grid_lattices_compact_selfDual_splitting D hQ T L μ0 hL sc G W M hM F hF
  have t1 := GlobalTheory.T.psi_primitive_standardFrames_fourierJacobiLevel D hQ T L μ0 hL sc G W M hM F hF (σ + 1) h v hv
  have t2 := GlobalTheory.T.fourierJacobiStep_basePoint_columns_primitive D hQ T L μ0 hL sc G W M hM F hF σ h h' v hv
  have r1 := GlobalTheory.T.depthLatticeGridRow_local_eq_completed_homLattice D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  have r2 := GlobalTheory.T.integralAdele_smul_depthLatticeGridRow_mem_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v
  have r3 := GlobalTheory.T.selfDualHomLatticeModulusShift_local_eq_latO D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) v hv
  obtain ⟨-, hb, -⟩ := I
  have hbσ := hb σ h'
  have hbσ1 := hb (σ + 1) h
  refine ⟨⟨?_, ?_, ?_, hbσ.1, (hbσ1.2.1 v).2, (hbσ.2.1 v).1, t1, t2⟩, ⟨?_, ?_, ?_⟩⟩
  · exact (G.sp.V_is (2 * σ + 3) 0 (by omega) (by omega) (by omega)).sd
  · exact (G.sp.P_is (2 * σ + 3) (by omega)).sd
  · exact (G.sp.V_is (2 * σ + 2) 0 (by omega) (by omega) (by omega)).sd
  · intro a ha
    exact r1 _ (mxAt_mul ha _)
  · intro a ha
    obtain ⟨⟨ε, hεε, -, hεi, -, hεoff⟩, -⟩ := GlobalTheory.FinPl.localComponents D (· = v)
    refine ⟨ε • a, fun i j => ?_, ?_⟩
    · rw [hεoff]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [mul_sub, ← mul_assoc, hεε, sub_self]
    · have := r2 ε hεi _ ha
      have e : (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (ε • a) =
          ε • (F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) a := by
        rw [HypDec.extX_apply, HypDec.extX_apply, Matrix.smul_mul]
      rw [e]
      exact this
  · intro ξ hξ
    exact r3 _ (mxAt_mul (mxAt_mul_left _ hξ) _)

end GlobalTheory.AscFin.GoodFB
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.StandardFramesSuccessiveLevelsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

theorem _root_.GlobalTheory.T.standard_frames_successive_levels : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ v ∉ G.pl.S0, GoodAt (F.dJ (σ + 1) h) (F.dB σ h') (xFB F σ h') W.ψ (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.core (2 * σ + 3))) (G.Λ (.grid (2 * σ + 2) 0)) (lat0 F σ h') v ∧ StdAt (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (G.Λ (.grid (2 * σ + 3) 0)) (G.Λ (.grid (2 * σ + 2) 0)) v := by
  first | exact @GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb | exact GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb | (intros; apply GlobalTheory.AscFin.GoodFB.goodAt_stdAt_fb <;> assumption)
end
end
