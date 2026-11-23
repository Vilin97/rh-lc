module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormLeOfCuspidalVariationUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryGroupTwoModelsRationalRealUnipotentDictio
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicPointExistsIsotropicReductionOfSmallSStatement
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeastSizePowMulSqrtAbsNormLeProdNormsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LipschitzBoundRealUnipotentActionStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PrincipalCongruenceMemLatticeCongruenceLevelStatement
import Mathlib.Tactic.Linter.Style
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.SharpRestriction.CuspSpanNormBounds.BesselShellMomentBounds
import Mathlib.RingTheory.PicardGroup

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicPointRationalLatticeUnitaryModelIsoEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatDict
open Formalism.IndefR.Eqv.UI

theorem mem_hatL_iff (D : D7) (V : HSp D) (fr : Frames D V)
    (w : Fin V.rank → D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F) :
    w ∈ Formalism.L2.Herm.hatL (F := D.host.F) fr.Λ ↔ w ∈ (instV fr).Lf := by
  unfold Formalism.L2.Herm.hatL Formalism.UG.latS Formalism.MainNotions.S.AutInst.Lf Formalism.MainNotions.S.lamAf
  rw [Set.image_eq_range]
  rfl

theorem finE_brg (D : D7) (V : HSp D) (fr : Frames D V) (x : (instV fr).GA) :
    (Lev.finE V (brg fr x)).1 = (instV fr).fmat x.2 := by
  have hring : ∀ z : AF D.host.F ⊗[D.host.F] D.host.E,
      Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) =
        Formalism.L2.SG.AdBridge.tauF (instV fr) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ((Lev.swapAE D).congr_arg (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
    | tmul a b => exact (Formalism.L2.SG.AdBridge.tauF_tmul (instV fr) a b).symm
    | add a b ha hb =>
      have e1 := _root_.map_add (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) a b
      rw [e1, RingHom.map_add (f := _), ha, hb]
      exact (RingHom.map_add _ _ _).symm
  rw [((brg_isBridge fr) x).2]
  ext i j
  simp only [Lev.finE, finHom, matHom, Formalism.UG.bc, Formalism.L2.SG.AdBridge.hmat, Formalism.L2.SG.AdBridge.ofHAFin,
    MonoidHom.comp_apply, Units.coe_map, Matrix.map_apply]
  exact hring _

theorem latAt_brg : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (x : (Formalism.IndefR.Eqv.UI.instV fr).GA), latAt fr.Λ (Formalism.IndefR.Eqv.UI.brg fr x) = GlobalTheory.Count.lamX (Formalism.IndefR.Eqv.UI.instV fr) x := by
  intro D V fr x
  unfold GlobalTheory.SepPer.latAt GlobalTheory.Count.lamX
  congr 1
  ext y
  rw [← map_inv (brg fr) x, finE_brg D V fr x⁻¹]
  exact mem_hatL_iff D V fr _

end GlobalTheory.LatDict
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdelicPointRationalLatticeUnitaryModelIsoEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicPointRationalLattice_unitaryModelIso_eq : ∀ (D : D7) (V : HSp D) (fr : Formalism.IndefR.Eqv.UI.Frames D V) (x : (Formalism.IndefR.Eqv.UI.instV fr).GA), latAt fr.Λ (Formalism.IndefR.Eqv.UI.brg fr x) = GlobalTheory.Count.lamX (Formalism.IndefR.Eqv.UI.instV fr) x := by
  first | exact @GlobalTheory.LatDict.latAt_brg | exact GlobalTheory.LatDict.latAt_brg | (intros; apply GlobalTheory.LatDict.latAt_brg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInstanceFramesOfDiagonalFrameSelfDual

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem frames_of_diagonalising_frame : ∀ (D : D7) (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∃ fr : Formalism.IndefR.Eqv.UI.Frames D V, fr.Λ = Λ ∧ ∀ τ, fr.ε (Formalism.L2.Host.tauPl D τ) = A.ε τ ∧ fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := by
  intro D V A Λ h
  obtain ⟨hlat, hdual⟩ := h
  have hspan : Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) = ⊤ := by
    exact (Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ ⟨hlat, hdual⟩).span_eq_top
  have hf : ∀ v, IsUnit (A.fr ((Formalism.L2.Host.tauPl D).symm v)) := fun v => A.fr_unit _
  refine ⟨{ ε := fun v => A.ε ((Formalism.L2.Host.tauPl D).symm v)
            P := fun v => (A.fr ((Formalism.L2.Host.tauPl D).symm v))⁻¹
            unit := fun v => (Matrix.isUnit_nonsing_inv_iff).2 (hf v)
            spec := ?_
            Λ := Λ
            Λ_fg := hlat.fg
            Λ_span := hspan
            Λ_dual := ?_ }, rfl, fun τ => ?_⟩
  · intro v
    set τ := (Formalism.L2.Host.tauPl D).symm v
    have hg : V.gram.map (Formalism.IndefR.Eqv.UI.phiV D v) = (A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ := by
      rw [A.fr_gram τ]; rfl
    have hd : IsUnit (A.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hf v)
    have hdH : IsUnit ((A.fr τ)ᴴ).det := by
      rw [Matrix.det_conjTranspose]; exact hd.star
    rw [hg, Matrix.conjTranspose_nonsing_inv]
    calc ((A.fr τ)ᴴ)⁻¹ * ((A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ) * (A.fr τ)⁻¹
        = (((A.fr τ)ᴴ)⁻¹ * (A.fr τ)ᴴ) * Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (A.ε τ) := by
          rw [Matrix.nonsing_inv_mul _ hdH, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]
  · intro x
    rw [hdual x]
    refine forall₂_congr fun y _ => ?_
    unfold Formalism.UG.hform
    simp only [RingHom.mem_range, starRingEnd_apply]
  · simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInstanceFramesOfDiagonalFrameSelfDualStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_instanceFrames_of_diagonalFrame_selfDual : ∀ (D : D7) (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∃ fr : Formalism.IndefR.Eqv.UI.Frames D V, fr.Λ = Λ ∧ ∀ τ, fr.ε (Formalism.L2.Host.tauPl D τ) = A.ε τ ∧ fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := by
  first | exact @GlobalTheory.frames_of_diagonalising_frame | exact GlobalTheory.frames_of_diagonalising_frame | (intros; apply GlobalTheory.frames_of_diagonalising_frame <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalVectorNormAdelicPointTwoModelsEq

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem norm_dict : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (w : Fin V.rank → D.host.E), ∏ v, Real.sqrt (∑ i, ‖(Formalism.MainNotions.S.uMat (x.1 v)⁻¹ *ᵥ (((Formalism.IndefR.Eqv.UI.instV fr).P v)⁻¹ *ᵥ fun j => (Formalism.IndefR.Eqv.UI.instV fr).φ v (w j))) i‖ ^ 2) = ∏ τ, nrm θ A (Formalism.IndefR.Eqv.UI.brg fr x) τ w := by
  intro D θ hθ V A fr hP x w
  symm
  refine Fintype.prod_equiv (Formalism.L2.Host.tauPl D) _ _ fun τ => ?_
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  unfold nrm eu GlobalTheory.SepPer.cmp
  rw [← map_inv (Formalism.IndefR.Eqv.UI.brg fr) x, (GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr).2.1 x⁻¹ τ _ rfl, hP τ]
  have key : ∀ (U Q : Matrix (Fin V.rank) (Fin V.rank) ℂ) (y : Fin V.rank → ℂ),
      A.fr τ *ᵥ (((A.fr τ)⁻¹ * U * Q) *ᵥ y) = U *ᵥ (Q *ᵥ y) := fun U Q y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  erw [key]
  have hP' : (Formalism.IndefR.Eqv.UI.instV fr).P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := hP τ
  have hφ : (Formalism.IndefR.Eqv.UI.instV fr).φ (Formalism.L2.Host.tauPl D τ) = tauE D τ := by
    show Formalism.IndefR.Eqv.UI.phiV D _ = _
    simp only [Formalism.IndefR.Eqv.UI.phiV, Equiv.symm_apply_apply]
  erw [hP', hφ]
  rfl

end GlobalTheory.NormDict
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalVectorNormAdelicPointTwoModelsEqStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.rationalVectorNorm_adelicPoint_twoModels_eq : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (w : Fin V.rank → D.host.E), ∏ v, Real.sqrt (∑ i, ‖(Formalism.MainNotions.S.uMat (x.1 v)⁻¹ *ᵥ (((Formalism.IndefR.Eqv.UI.instV fr).P v)⁻¹ *ᵥ fun j => (Formalism.IndefR.Eqv.UI.instV fr).φ v (w j))) i‖ ^ 2) = ∏ τ, nrm θ A (Formalism.IndefR.Eqv.UI.brg fr x) τ w := by
  first | exact @GlobalTheory.NormDict.norm_dict | exact GlobalTheory.NormDict.norm_dict | (intros; apply GlobalTheory.NormDict.norm_dict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormCuspFormLeOfShortLine

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ShortLineCusp

theorem sum_sqrt_le (ι : Type) [Fintype ι] (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ∑ i, Real.sqrt (a i) ≤ Real.sqrt (Fintype.card ι) * Real.sqrt (∑ i, a i) := by
  have h1 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) (fun i => Real.sqrt (a i))
  simp only [one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, one_mul,
    Real.sq_sqrt (ha _)] at h1
  rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  simpa [Real.sq_sqrt (ha _)] using h1

theorem sum_sqrt_add_le : ∀ (ι : Type) [Fintype ι] (a b : ι → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) → ∑ i, (Real.sqrt (a i) + Real.sqrt (b i)) ≤ Real.sqrt (Fintype.card ι) * (Real.sqrt (∑ i, a i) + Real.sqrt (∑ i, b i)) := by
  intro ι _ a b ha hb
  rw [Finset.sum_add_distrib, mul_add]
  exact add_le_add (sum_sqrt_le ι a ha) (sum_sqrt_le ι b hb)

theorem finrank_eq_card_and_rd : ∀ D : D7, Module.finrank ℚ D.host.F = Fintype.card D.what₂.Tau ∧ |(discr D.host.E : ℝ)| ^ ((1 : ℝ) / (2 * (Module.finrank ℚ D.host.F : ℝ))) = rdisc D := by
  intro D
  haveI := D.sp.cm.totReal
  refine ⟨?_, ?_⟩
  · rw [Fintype.card_congr (Formalism.L2.Host.tauPl D), ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero,
      NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
  · unfold rdisc
    rw [← Module.finrank_mul_finrank ℚ D.host.F D.host.E, D.sp.cm.deg2]
    congr 1
    push_cast
    ring

theorem least_nonneg : ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.GA), 0 ≤ GlobalTheory.Count.least I x := by
  intro I x
  unfold GlobalTheory.Count.least Formalism.HN.leastSize
  apply Real.sInf_nonneg
  rintro t ⟨R, -, -, rfl⟩
  unfold Formalism.HN.size Formalism.HN.ht Formalism.F.covol
  apply Real.rpow_nonneg
  apply mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _))
  split_ifs <;> positivity

attribute [local instance] Formalism.BasicNotions.Host.cmStar



theorem norm_le_of_not_long : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (Λ : Lat V), IsSelfDualC V Λ → ∀ (g q : ℕ), 1 ≤ g → 1 ≤ q → 1 ≤ V.rank → (∀ τ, min (Finset.univ.filter fun a => A.ε τ a = true).card (Finset.univ.filter fun a => A.ε τ a = false).card ≤ q) → ∀ φ : GA D V → ℂ, IsAutFun V φ → IsCuspFun V φ → (∀ k ∈ Lev.levA V (congLev D.sp.cm V.gram Λ (Ideal.span {((g : ℕ) : 𝓞 D.host.E)})), ∀ x, φ (x * k) = φ x) → ∀ c : ℝ, 0 ≤ c → Lip θ A φ c → ∀ (x : GA D V) (s : ℝ), 0 < s → s ≤ 1 / 2 → ¬ Long θ A Λ x s → ‖φ x‖ ≤ c * ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q)) := by
  intro D θ hθ V A Λ hΛ g q hg hq hn hrk φ hφ hcusp hlev c hc hlip x s hs hs2 hlong
  obtain ⟨fr, hfrΛ, hfr⟩ := GlobalTheory.T.exists_instanceFrames_of_diagonalFrame_selfDual D V A Λ hΛ
  subst hfrΛ
  obtain ⟨hfF, hrdE⟩ := finrank_eq_card_and_rd D
  have hfI : (Formalism.IndefR.Eqv.UI.instV fr).f = Fintype.card D.what₂.Tau := hfF
  have hrdI : (Formalism.IndefR.Eqv.UI.instV fr).rd = rdisc D := hrdE
  set x0 := (Formalism.IndefR.Eqv.UI.brg fr).symm x with hx0
  have hbx : Formalism.IndefR.Eqv.UI.brg fr x0 = x := by simp [hx0]
  have hl0 : 0 ≤ GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0 := least_nonneg _ x0
  have hlt : GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0 < s := by
    by_contra hge
    push_neg at hge
    apply hlong
    intro 𝔪 h𝔪 w hw hw0
    have hL := GlobalTheory.T.adelicPointRationalLattice_unitaryModelIso_eq D V fr x0
    rw [hbx] at hL
    rw [hL] at hw
    have h1 := GlobalTheory.T.leastSize_pow_mul_sqrt_absNorm_le_prod_norms (Formalism.IndefR.Eqv.UI.instV fr) x0 𝔪 h𝔪 w hw hw0
    rw [GlobalTheory.T.rationalVectorNorm_adelicPoint_twoModels_eq D θ hθ V A fr (fun τ => (hfr τ).2) x0 w, hbx, hfI] at h1
    exact le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hs.le hge _) (Real.sqrt_nonneg _)) h1
  have hrkI : ∀ v, GlobalTheory.Count.rkR ((Formalism.IndefR.Eqv.UI.instV fr).ε v) ≤ q := by
    intro (v : InfinitePlace D.host.F)
    have h := (hfr ((Formalism.L2.Host.tauPl D).symm v)).1
    have e : (Formalism.L2.Host.tauPl D) ((Formalism.L2.Host.tauPl D).symm v) = v := Equiv.apply_symm_apply _ _
    rw [e] at h
    show GlobalTheory.Count.rkR (fr.ε v) ≤ q
    rw [h]
    exact hrk _
  obtain ⟨W, hW, hmv⟩ := GlobalTheory.T.automorphicPoint_exists_isotropic_reduction_of_small_size (Formalism.IndefR.Eqv.UI.instV fr) x0 g q hg hq hn hrkI (hlt.trans_le hs2)
  obtain ⟨hGQ, -, hN⟩ := GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr
  obtain ⟨r, C₀, hC₀, hNI⟩ := hN W hW
  apply GlobalTheory.CuspGeo.norm_le_of_unipRad_variation D V φ hφ hcusp r C₀ hC₀ x
  intro m hm
  have hm' : (Formalism.IndefR.Eqv.UI.brg fr).symm m ∈ (Formalism.IndefR.Eqv.UI.instV fr).NA W :=
    hNI _ (by simpa using hm)
  obtain ⟨γ, hγ, k, hk, u, Av, Z, hAZ, hu, heq, hbd⟩ := hmv _ hm'
  have hmx : m * x = Formalism.IndefR.Eqv.UI.brg fr γ * (x * Formalism.IndefR.Eqv.UI.brg fr (u, 1)) * Formalism.IndefR.Eqv.UI.brg fr (1, k) := by
    have h2 := congrArg (Formalism.IndefR.Eqv.UI.brg fr) heq
    have h3 : ((u, k) : (Formalism.IndefR.Eqv.UI.instV fr).GA) = (u, 1) * (1, k) := by simp
    rw [h3] at h2
    simp only [map_mul, hbx, ContinuousMulEquiv.apply_symm_apply] at h2
    rw [h2]; group
  rw [hmx, hlev _ (GlobalTheory.T.principalCongruence_mem_latticeCongruenceLevel D V fr g hg k hk), hφ.left _ ((hGQ γ).2 hγ)]
  have h6 := GlobalTheory.T.lipschitz_bound_real_unipotent_action D θ hθ V A fr (fun τ => (hfr τ).2) φ c hc hlip u Av Z hAZ hu x
  have h7 := sum_sqrt_add_le (InfinitePlace D.host.F) (fun v => Formalism.REAL.hs (Av v)) (fun v => Formalism.REAL.hs (Z v))
    (fun v => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
    (fun v => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hcard : Fintype.card (InfinitePlace D.host.F) = Fintype.card D.what₂.Tau :=
    Fintype.card_congr (Formalism.L2.Host.tauPl D).symm
  rw [hcard] at h7
  rw [hfI, hrdI] at hbd
  have hL : (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) ≤ (2 * s) ^ ((1 : ℝ) / q) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hL0 : 0 ≤ (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) := by positivity
  have hrd0 : 0 ≤ rdisc D := by unfold rdisc; positivity
  have hN : Real.sqrt (Fintype.card D.what₂.Tau) * Real.sqrt (Fintype.card D.what₂.Tau) = Fintype.card D.what₂.Tau :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hP : 0 ≤ (V.rank : ℝ) ^ 2 * (Fintype.card D.what₂.Tau : ℝ) * (g : ℝ) * rdisc D := by positivity
  have hbd' : Real.sqrt (Fintype.card D.what₂.Tau) *
      (Real.sqrt (∑ v, Formalism.REAL.hs (Av v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v))) ≤
      (V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D * (2 * s) ^ ((1 : ℝ) / q) := by
    calc _ ≤ Real.sqrt (Fintype.card D.what₂.Tau) * ((V.rank : ℝ) ^ 2 * Real.sqrt (Fintype.card D.what₂.Tau) * g * rdisc D *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) / 4) :=
          mul_le_mul_of_nonneg_left hbd (Real.sqrt_nonneg _)
      _ = (Real.sqrt (Fintype.card D.what₂.Tau) * Real.sqrt (Fintype.card D.what₂.Tau)) * ((V.rank : ℝ) ^ 2 * g * rdisc D *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q)) / 4 := by ring
      _ = ((V.rank : ℝ) ^ 2 * Fintype.card D.what₂.Tau * g * rdisc D) *
          (2 * GlobalTheory.Count.least (Formalism.IndefR.Eqv.UI.instV fr) x0) ^ ((1 : ℝ) / q) / 4 := by rw [hN]; ring
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hL hP, mul_nonneg hP hL0]
  calc _ ≤ _ := h6
    _ ≤ c * (Real.sqrt (Fintype.card D.what₂.Tau) *
      (Real.sqrt (∑ v, Formalism.REAL.hs (Av v)) + Real.sqrt (∑ v, Formalism.REAL.hs (Z v)))) := mul_le_mul_of_nonneg_left h7 hc
    _ ≤ _ := mul_le_mul_of_nonneg_left hbd' hc

end GlobalTheory.ShortLineCusp

end
end
end
