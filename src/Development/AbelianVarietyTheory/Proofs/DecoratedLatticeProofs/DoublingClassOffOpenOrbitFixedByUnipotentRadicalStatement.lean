module

public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjDoublingIsotropicUnipotentMemSiegelStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecPairVecDiag
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
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
import Mathlib.RingTheory.PicardGroup
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalIsometryNormalisesIsotropicUnipotentRadiStatement
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLagrangianTransverseInOpenOrbit

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

namespace GlobalTheory.Core.Rk.Dich

theorem exists_mem_siegel_of_diagSnd : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → x = 0) → ∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V := by
  intro D V γ hγ γi hγi hinj
  have hinc : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  obtain ⟨g, hg, hg1, hg2⟩ := exists_rat (dblSp V) hγ
  have hγi' : γi = (g⁻¹).1 := Matrix.map_injective hinc (hγi.symm.trans hg2)
  have hgγ : g.1 * γi = 1 := by rw [hγi']; exact Units.mul_inv g
  have hgi : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * dblGram finSumFinEquiv V.gram * γi =
      dblGram finSumFinEquiv V.gram := by
    have h := inv_mem hg
    change Formalism.UG.cT _ (g⁻¹).1 * (dblSp V).gram * (g⁻¹).1 = (dblSp V).gram at h
    rw [gram_hdbl] at h
    rw [hγi']; exact h
  have hiso := isotropic_diag hgi
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set P := leviMat finSumFinEquiv γi with hP
  set Q := diagSnd γi with hQ
  have hQu : IsUnit Q := Matrix.mulVec_injective_iff_isUnit.1 fun x y h =>
    sub_eq_zero.1 (hinj _ (by rw [Matrix.mulVec_sub, h, sub_self]))
  have hQ1 : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hQu)
  have hcT : ∀ M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E,
      Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
    intro M N; simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have hcT1 : Formalism.UG.cT σ Q⁻¹ * Formalism.UG.cT σ Q = 1 := by
    rw [← hcT, hQ1]; simp [Formalism.UG.cT]
  have hδ : Formalism.UG.cT σ (P * Q⁻¹) * V.gram * (P * Q⁻¹) = V.gram := by
    calc Formalism.UG.cT σ (P * Q⁻¹) * V.gram * (P * Q⁻¹)
        = Formalism.UG.cT σ Q⁻¹ * (Formalism.UG.cT σ P * V.gram * P) * Q⁻¹ := by simp only [hcT, Matrix.mul_assoc]
      _ = V.gram := by
        rw [hiso]; simp only [Matrix.mul_assoc]
        rw [hQ1, Matrix.mul_one, ← Matrix.mul_assoc, hcT1, Matrix.one_mul]
  have hdet : IsUnit (P * Q⁻¹).det := by
    have h := congrArg Matrix.det hδ
    rw [Matrix.det_mul, Matrix.det_mul] at h
    have hJ : IsUnit V.gram.det := GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit V
    rw [← h] at hJ
    exact isUnit_of_mul_isUnit_right hJ
  set d : GL (Fin V.rank) D.host.E := ((Matrix.isUnit_iff_isUnit_det (P * Q⁻¹)).2 hdet).unit with hd
  have hdv : d.1 = P * Q⁻¹ := rfl
  have hdU : d ∈ Formalism.UG.UJ σ V.gram := by
    change Formalism.UG.cT σ d.1 * V.gram * d.1 = V.gram
    rw [hdv]; exact hδ
  obtain ⟨δ', hδ'Q, hδ'⟩ := exists_of_rat V hdU
  refine ⟨δ'⁻¹, inv_mem hδ'Q, ?_⟩
  rw [show (io V (δ'⁻¹, 1))⁻¹ = io V (δ', 1) by rw [← map_inv, Prod.inv_mk, inv_inv, inv_one]]
  have hm : (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (δ', 1))).1 =
      (g.1 * blkMat finSumFinEquiv (P * Q⁻¹) 1).map (incA D) := by
    rw [map_mul, Units.val_mul, hg1, matHom_io, val_blkGL, hδ', map_one, Units.val_one, hdv]
    conv_rhs => rw [Matrix.map_mul, blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
  refine mem_siegelOf.2 ?_
  change KeepsDiag finSumFinEquiv (Formalism.L2.Theta.matHom (dblSp V) (γ * io V (δ', 1))).1
  rw [hm]
  refine KeepsDiag.map _ (keepsDiag_of_mulVec fun w hw => ?_) _
  obtain ⟨x, rfl⟩ := (mem_diagSub _).1 hw
  rw [← Matrix.mulVec_mulVec, blkMat_mulVec, Matrix.one_mulVec]
  have h2 : pairVec finSumFinEquiv ((P * Q⁻¹) *ᵥ x) x = γi *ᵥ pairVec finSumFinEquiv (Q⁻¹ *ᵥ x) (Q⁻¹ *ᵥ x) := by
    rw [mulVec_pairVec_diag, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQ1, Matrix.one_mulVec]
  rw [h2, Matrix.mulVec_mulVec, hgγ, Matrix.one_mulVec]
  exact (pairVec_mem_diagSub _).2 rfl

end GlobalTheory.Core.Rk.Dich
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLagrangianTransverseInOpenOrbitStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix


theorem _root_.GlobalTheory.T.doubled_lagrangian_transverse_in_open_orbit : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → x = 0) → ∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V := by
  first | exact @GlobalTheory.Core.Rk.Dich.exists_mem_siegel_of_diagSnd | exact GlobalTheory.Core.Rk.Dich.exists_mem_siegel_of_diagSnd | (intros; apply GlobalTheory.Core.Rk.Dich.exists_mem_siegel_of_diagSnd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalIsometryKeepsIsotropicFrameOfSiegel

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

namespace GlobalTheory.Core.Rk.Dich

theorem matHom_conj_io (D : D7) (V : HSp D) (γ : GA D (dblSp V)) (δ : GA D V) (g : GL (Fin (V.rank + V.rank)) D.host.E)
    (γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E) (δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (hg1 : (matHom (dblSp V) γ).1 = g.1.map (incA D)) (hγi : (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D))
    (hδ₀ : (matHom V δ).1 = δ₀.map (incA D)) :
    (matHom (dblSp V) (γ * io V (δ, 1) * γ⁻¹)).1 = (g.1 * blkMat finSumFinEquiv δ₀ 1 * γi).map (incA D) := by
  have h1 : (matHom (dblSp V) (io V (δ, 1))).1 = blkMat finSumFinEquiv (matHom V δ).1 1 := by
    rw [matHom_io, val_blkGL]
    simp
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, h1, hg1, hγi, hδ₀, Matrix.map_mul, Matrix.map_mul,
    blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]

theorem isoFrame_keep : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → ∃ y, x = K *ᵥ y) → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ δ ∈ GQ V, ∀ δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (matHom V δ).1 = δ₀.map (incA D) → γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∃ G : Matrix (Fin r) (Fin r) D.host.E, IsUnit G ∧ δ₀ * (leviMat finSumFinEquiv γi * K) = leviMat finSumFinEquiv γi * K * G := by
  intro D V γ hγ γi hγi r K hK hKsurj hC δ hδ δ₀ hδ₀ hsieg
  have inj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  obtain ⟨g, -, hg1, hg2⟩ := exists_rat (dblSp V) hγ
  obtain ⟨d, -, hd1, -⟩ := exists_rat V hδ
  have hγi' : γi = (g⁻¹).1 := Matrix.map_injective inj (hγi.symm.trans hg2)
  have hδ₀' : δ₀ = d.1 := Matrix.map_injective inj (hδ₀.symm.trans hd1)
  have hgi0 : γi * g.1 = 1 := by rw [hγi']; exact g.inv_mul
  obtain ⟨X, hX⟩ : ∃ X, X = g.1 * blkMat finSumFinEquiv δ₀ 1 * γi := ⟨_, rfl⟩
  have hXmap := matHom_conj_io D V γ δ g γi δ₀ hg1 hγi hδ₀
  rw [← hX] at hXmap
  have hKX : KeepsDiag finSumFinEquiv X := by
    have h : KeepsDiag finSumFinEquiv (matHom (dblSp V) (γ * io V (δ, 1) * γ⁻¹)).1 := mem_siegelOf.1 hsieg
    rw [hXmap] at h
    refine (keepsDiag_iff finSumFinEquiv).2 fun i j => inj ?_
    simpa using (keepsDiag_iff finSumFinEquiv).1 h i j
  obtain ⟨C, hCdef⟩ : ∃ C, C = leviMat finSumFinEquiv γi * K := ⟨_, rfl⟩
  rw [← hCdef] at hC ⊢
  have key : ∀ v : Fin r → D.host.E, ∃ w, δ₀ *ᵥ (C *ᵥ v) = C *ᵥ w := by
    intro v
    have h1 : γi *ᵥ pairVec finSumFinEquiv (K *ᵥ v) (K *ᵥ v) = pairVec finSumFinEquiv (C *ᵥ v) 0 := by
      rw [mulVec_pairVec_diag, mulVec_mulVec (M := diagSnd γi), hK, zero_mulVec, mulVec_mulVec, hCdef]
    have h2 : X *ᵥ pairVec finSumFinEquiv (K *ᵥ v) (K *ᵥ v) =
        g.1 *ᵥ pairVec finSumFinEquiv (δ₀ *ᵥ (C *ᵥ v)) 0 := by
      rw [hX, ← mulVec_mulVec, ← mulVec_mulVec, h1, blkMat_mulVec, mulVec_zero]
    have h3 : pairVec finSumFinEquiv (δ₀ *ᵥ (C *ᵥ v)) 0 =
        γi *ᵥ pairVec finSumFinEquiv (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) := by
      rw [← hKX.mulVec_diag, h2, mulVec_mulVec (M := γi), hgi0, one_mulVec]
    rw [mulVec_pairVec_diag] at h3
    have h4a : δ₀ *ᵥ (C *ᵥ v) = leviMat finSumFinEquiv γi *ᵥ (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) := by
      funext i
      have := congrFun h3 (finSumFinEquiv (.inl i))
      rw [pairVec_inl, pairVec_inl] at this
      exact this
    have h4b : diagSnd γi *ᵥ (leviMat finSumFinEquiv X *ᵥ (K *ᵥ v)) = 0 := by
      funext i
      have := congrFun h3 (finSumFinEquiv (.inr i))
      rw [pairVec_inr, pairVec_inr] at this
      exact this.symm
    obtain ⟨w, hw⟩ := hKsurj _ h4b
    exact ⟨w, by rw [h4a, hw, mulVec_mulVec, hCdef]⟩
  choose w hw using fun j => key (Pi.single j 1)
  have hCG : δ₀ * C = C * Matrix.of fun i j => w j i := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hw j) i
    rw [mulVec_mulVec, mulVec_single_one] at this
    simpa [Matrix.mul_apply, mulVec, dotProduct, transpose_apply] using this
  refine ⟨Matrix.of fun i j => w j i, ?_, hCG⟩
  rw [← mulVec_injective_iff_isUnit]
  intro a b hab
  have h0 : (Matrix.of fun i j => w j i) *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
  have h5 : C *ᵥ (a - b) = 0 := by
    have h6 : δ₀ *ᵥ (C *ᵥ (a - b)) = 0 := by rw [mulVec_mulVec, hCG, ← mulVec_mulVec, h0, mulVec_zero]
    have h7 := congrArg (fun x => (d⁻¹).1 *ᵥ x) h6
    simp only [hδ₀', mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, mulVec_zero] at h7
    exact h7
  obtain ⟨-, hli, -⟩ := hC
  have h8 := Fintype.linearIndependent_iff.1 hli (a - b) (by
    funext i
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using congrFun h5 i)
  exact sub_eq_zero.1 (funext h8)

end GlobalTheory.Core.Rk.Dich
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalIsometryKeepsIsotropicFrameOfSiegelStatement

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix


theorem _root_.GlobalTheory.T.rational_isometry_keeps_isotropic_frame_of_siegel : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → ∃ y, x = K *ᵥ y) → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ δ ∈ GQ V, ∀ δ₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, (matHom V δ).1 = δ₀.map (incA D) → γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∃ G : Matrix (Fin r) (Fin r) D.host.E, IsUnit G ∧ δ₀ * (leviMat finSumFinEquiv γi * K) = leviMat finSumFinEquiv γi * K * G := by
  first | exact @GlobalTheory.Core.Rk.Dich.isoFrame_keep | exact GlobalTheory.Core.Rk.Dich.isoFrame_keep | (intros; apply GlobalTheory.Core.Rk.Dich.isoFrame_keep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingClassOffOpenOrbitFixedByUnipotentRadical

section

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.Dich

theorem offOpen : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ¬ (∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V) → ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C ∧ (∀ n ∈ NI V C, ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1) ∧ ∀ δ ∈ GQ V, γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∀ n ∈ NI V C, δ * n * δ⁻¹ ∈ NI V C := by
  intro D V γ hγ hopen
  obtain ⟨g, hg, -, hγi⟩ := exists_rat (dblSp V) hγ
  have hgi : g⁻¹ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (dblSp V).gram := inv_mem hg
  set γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E := (g⁻¹).1 with hγidef
  have hU : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * dblGram finSumFinEquiv V.gram * γi =
      dblGram finSumFinEquiv V.gram := by
    have h : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) γi * (dblSp V).gram * γi = (dblSp V).gram := hgi
    rwa [gram_hdbl] at h
  set Qd := diagSnd γi with hQd
  set P := leviMat finSumFinEquiv γi with hP
  have hinj : ∀ x, P *ᵥ x = 0 → Qd *ᵥ x = 0 → x = 0 := by
    intro x h1 h2
    have h3 : γi *ᵥ pairVec finSumFinEquiv x x = 0 := by
      rw [mulVec_pairVec_diag, ← hP, ← hQd, h1, h2]
      funext j; simp [pairVec, Sum.elim_zero_zero]
    have h4 : (g.1 * γi) *ᵥ pairVec finSumFinEquiv x x = 0 := by rw [← mulVec_mulVec, h3, mulVec_zero]
    rw [hγidef, Units.mul_inv, one_mulVec] at h4
    funext i
    have := congrFun h4 (finSumFinEquiv (.inl i))
    rwa [pairVec_inl] at this
  by_cases hk : ∀ x, Qd *ᵥ x = 0 → x = 0
  · exact absurd (GlobalTheory.T.doubled_lagrangian_transverse_in_open_orbit D V γ hγ γi hγi hk) hopen
  push Not at hk
  obtain ⟨x0, hx0, hx0ne⟩ := hk
  let W := LinearMap.ker Qd.mulVecLin
  let b := Module.finBasis D.host.E W
  let K : Matrix (Fin V.rank) (Fin (Module.finrank D.host.E W)) D.host.E :=
    Matrix.of fun i j => (b j : Fin V.rank → D.host.E) i
  have hKv : ∀ y, K *ᵥ y = ((∑ j, y j • b j : W) : Fin V.rank → D.host.E) := by
    intro y; funext i
    simp [K, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]
  have hbQ : ∀ j, Qd *ᵥ (b j : Fin V.rank → D.host.E) = 0 := fun j => (b j).2
  have hQK : Qd * K = 0 := by
    refine Matrix.ext fun i j => ?_
    have := congrFun (hbQ j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, K, Matrix.of_apply, Matrix.zero_apply]
    exact this
  have hspan : ∀ x, Qd *ᵥ x = 0 → ∃ y, x = K *ᵥ y := by
    intro x hx
    refine ⟨b.repr ⟨x, hx⟩, ?_⟩
    rw [hKv, b.sum_repr]
  have hiso : IsIsoFrame V (P * K) := by
    refine ⟨?_, ?_, ?_⟩
    · exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x0, hx0⟩, fun h => hx0ne (congrArg Subtype.val h)⟩
    · refine (Matrix.mulVec_injective_iff (M := P * K)).1 ?_
      intro c c' hc
      rw [← sub_eq_zero] at hc ⊢
      rw [← mulVec_sub, ← mulVec_mulVec] at hc
      have h1 : K *ᵥ (c - c') = 0 := hinj _ hc (by rw [mulVec_mulVec, hQK, zero_mulVec])
      rw [hKv] at h1
      have h2 : (∑ j, (c - c') j • b j : W) = 0 := Subtype.ext h1
      funext j
      exact Fintype.linearIndependent_iff.1 b.linearIndependent _ h2 j
    · have hI := isotropic_diag hU
      rw [← hP, ← hQd] at hI
      rw [Formalism.UG.cT_mul]
      calc Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) K * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P *
            V.gram * (P * K)
          = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) K *
            (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) P * V.gram * P) * K := by
            simp only [Matrix.mul_assoc]
        _ = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (Qd * K) * V.gram * (Qd * K) := by
            rw [hI, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hQK]; simp [Formalism.UG.cT]
  refine ⟨_, P * K, hiso, GlobalTheory.T.conj_doubling_isotropic_unipotent_mem_siegel D V γ hγ γi hγi _ K hQK hiso, ?_⟩
  intro δ hδ hs n hn
  obtain ⟨d, -, hδm, -⟩ := exists_rat V hδ
  obtain ⟨G, hG, hGe⟩ := GlobalTheory.T.rational_isometry_keeps_isotropic_frame_of_siegel D V γ hγ γi hγi _ K hQK hspan hiso δ hδ d.1 hδm hs
  exact GlobalTheory.T.rational_isometry_normalises_isotropic_unipotent_radical D V _ (P * K) δ hδ d.1 hδm G hG hGe n hn

end GlobalTheory.Core.Rk.Dich

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingClassOffOpenOrbitFixedByUnipotentRadicalStatement

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


theorem _root_.GlobalTheory.T.doublingClass_offOpenOrbit_fixedByUnipotentRadical : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ¬ (∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V) → ∃ (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E), IsIsoFrame V C ∧ (∀ n ∈ NI V C, ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1) ∧ ∀ δ ∈ GQ V, γ * io V (δ, 1) * γ⁻¹ ∈ siegel V → ∀ n ∈ NI V C, δ * n * δ⁻¹ ∈ NI V C := by
  first | exact @GlobalTheory.Core.Rk.Dich.offOpen | exact GlobalTheory.Core.Rk.Dich.offOpen | (intros; apply GlobalTheory.Core.Rk.Dich.offOpen <;> assumption)
end
end
