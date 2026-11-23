module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorThetaLiftOfBaseLevelLaw
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThFEqIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseOfOfPin
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumPrincipalLevelEqConstMulClassSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftEqMultiplePrincipalLevelClassSum

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorThetaLiftOfBaseLevelLawStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.goodProjector_thetaLift_of_baseLevelLaw : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ y' : (X.R.HV j t).H, (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y' (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y' h) ∧
      (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y) (X.geo.v₀ j _) = X.R.thF j t y' (X.geo.v₀ j _) := by
  first | exact @GlobalTheory.ProjLiftLaw.projLift_law | exact GlobalTheory.ProjLiftLaw.projLift_law | (intros; apply GlobalTheory.ProjLiftLaw.projLift_law <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumPrincipalLevelEqConstMulClassSumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField GlobalTheory.ExportSeries
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.classSum_principalLevel_eq_const_mul_classSum : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (ψ : Twist D Circle), ψ.Good → B.admitted ψ.Q →
    ∀ (ω : PairRep S T), B.IsWeil ψ.chi ω → ∀ (m : ℕ) (h₀ : Fin m → GA D S), IsClassSystem S ((GlobalTheory.FlatVecSum.princ B).levJ ψ) h₀ →
    ∀ (I : Type) [Fintype I] (h : I → GA D S), IsClassSystem S (B.levJ ψ) h →
    ∃ κ : ℂ, ∀ F ∈ B.formsC ψ, (GlobalTheory.FlatVecSum.princ B).classSum ω ψ h₀ F = κ • B.classSum ω ψ h F := by
  first | exact @GlobalTheory.ClassSumPrinc.classSum_princ_eq | exact GlobalTheory.ClassSumPrinc.classSum_princ_eq | (intros; apply GlobalTheory.ClassSumPrinc.classSum_princ_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockReadingTranslatedFormMemComplexForms

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockReadForms

theorem fockRead_mem_formsC : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∀ (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ),
      (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) = X.geo.v₀ j (sg0 D X.A3.A) →
    ∀ (z : Bridge.Gf (Vc D j)), z ∈ Subgroup.center (Bridge.Gf (Vc D j)) →
    (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1) := by
  intro D X E Y i j b t hxi hQ y hlaw u hu z hz
  have hC : GlobalTheory.Hk3.Core X.R.toRealDat X.F.lv2 :=
    ⟨X.char.lev, X.char.grp, X.char.fam, X.char.models, X.char.chain, X.char.thP⟩
  have hBo : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) :=
    GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have hG : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have htup : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Twist.triv Circle ∅) t := by
    classical
    exact ⟨by rw [hxi]; exact (mul_one _).symm, by rw [hQ]; exact (Finset.union_empty _).symm⟩
  have hact := (GlobalTheory.CoefActIo.act_ioP hC hG hBo (Twist.triv_good splitSet_empty) htup).2
  have hio : Formalism.IndefR.FWT.IoExt X.R.toRealDat :=
    GlobalTheory.IoExtremal.ioExt D _ _ _ _ _ X.R.toRealDat hC.lev hC.fam hC.models hC.thP
  have hval : ∀ w, X.R.ioP j (PiTensorProduct.tprod ℂ u) w ∈ (Y.Z.ρ.B i j b).valSpace := by
    intro w
    have hcV : (X.R.cV j).Is := hC.models.cV j
    obtain ⟨u', w₀, hu', -, hw⟩ := Formalism.IndefR.FWT.IsChosenExtremalVector.io _ (Y.Z.vec j) hio
    have huu : u' = u := funext fun ρ => Subtype.ext ((hu' ρ).trans (congrFun hu ρ).symm)
    rw [huu] at hw
    have hT := Scale.io_act hC.lev hC.thP hG hBo.ψ hBo.θ hBo.sT hBo.BS hBo.BT hBo.mu0 hBo.eta (PiTensorProduct.tprod ℂ u)
    have hΔ0 := GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) j
    rcases hcV.2.2.2.2 ((harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
        (X.R.ioP j (PiTensorProduct.tprod ℂ u))) (fun h => by
        obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
        rw [map_mul, hcV.1 k hk, mul_one]
        rintro _ ⟨w, hw', rfl⟩
        rw [Submodule.mem_comap, hT a ha]
        exact fockGL_mem_harm _ _ _ hw') with h | h
    · have h0 : w₀ ∈ (harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
          (X.R.ioP j (PiTensorProduct.tprod ℂ u)) := by
        rw [Submodule.mem_comap, hw, ← hBo.delta]
        exact delta_mem_harm _ _
      rw [h, Submodule.mem_bot] at h0
      rw [h0, map_zero] at hw
      exact absurd hw.symm hΔ0
    · exact (h ▸ Submodule.mem_top : w ∈ (harm (Wc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS).comap
        (X.R.ioP j (PiTensorProduct.tprod ℂ u)))

  have hx : (X.R.HV j t).e y ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
      (levEnv _ (X.R.βV j) (X.R.datVt j t)).J (levEnv _ (X.R.βV j) (X.R.datVt j t)).χ :=
    (hC.models.HV j t).2.1.le (LinearMap.mem_range_self _ y)
  rw [Base.mem_formsC]
  refine ⟨fun h => hval _, fun γ h k => ?_⟩
  have hzc := Subgroup.mem_center_iff.1 hz
  have e1 : Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j)) * z =
      Bridge.ratF (Vc D j) γ * (h * z) * (k : Bridge.Gf (Vc D j)) := by
    simp only [mul_assoc]
    rw [← hzc]
  have h2 : Bridge.ratF (Vc D j) γ * (h * z) * ((1 : (levEnv _ (X.R.βV j) (X.R.datVt j t)).J) : Bridge.Gf (Vc D j)) =
      Bridge.ratF (Vc D j) γ * (h * z) := by
    rw [OneMemClass.coe_one]
    exact mul_one _
  have e2 : (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z)) =
      (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
    calc (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))
        = (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z) *
            ((1 : (levEnv _ (X.R.βV j) (X.R.datVt j t)).J) : Bridge.Gf (Vc D j))) := congrArg _ h2.symm
      _ = (((levEnv _ (X.R.βV j) (X.R.datVt j t)).χ 1 : ℂˣ) : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
          hx γ (h * z) 1
      _ = (1 : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) :=
          congrArg (fun c : ℂ => c • (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)))
            (by rw [MonoidHom.map_one, Units.val_one])
      _ = (X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z)) := one_smul ℂ _
  calc X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j)) * z))
      = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z) * (k : Bridge.Gf (Vc D j)))) :=
        congrArg (fun g => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y g)) e1
    _ = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          (X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))) :=
        congrArg (X.R.ioP j (PiTensorProduct.tprod ℂ u)) (hlaw _ k)
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (Bridge.ratF (Vc D j) γ * (h * z))) :=
        map_smul _ _ _
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.cV j).ρ (γ : GA D (Vc D j)) ((X.R.HV j t).e y (h * z))) :=
        congrArg (fun v => (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • X.R.ioP j (PiTensorProduct.tprod ℂ u) v) e2
    _ = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) •
          (Y.Z.ρ.B i j b).act (γ : GA D (Vc D j)) (X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) :=
        congrArg (fun v => (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • v) (hact _ _ _).symm

end GlobalTheory.FockReadForms

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockReadingTranslatedFormMemComplexFormsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.fockReading_translatedForm_mem_complexForms : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∀ (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ),
      (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) = X.geo.v₀ j (sg0 D X.A3.A) →
    ∀ (z : Bridge.Gf (Vc D j)), z ∈ Subgroup.center (Bridge.Gf (Vc D j)) →
    (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1) := by
  first | exact @GlobalTheory.FockReadForms.fockRead_mem_formsC | exact GlobalTheory.FockReadForms.fockRead_mem_formsC | (intros; apply GlobalTheory.FockReadForms.fockRead_mem_formsC <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftEqMultiplePrincipalLevelClassSumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaLift_eq_multiple_principalLevel_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ (y : (X.R.HV j t).H) (u : ∀ ρ, lowT (X.R.MW j (sg0 D X.A3.A)) ρ),
    ∃ (m : ℕ) (h₀ : Fin m → GA D (Vc D j)) (c : ℂ) (z : Bridge.Gf (Vc D j)),
      IsClassSystem (Vc D j) ((GlobalTheory.FlatVecSum.princ (Y.Z.ρ.B i j b)).levJ (Y.Z.ρ.tw i b 0 ∅ 1)) h₀ ∧ z ∈ Subgroup.center (Bridge.Gf (Vc D j)) ∧
      X.R.thF j t y (fun ρ => (u ρ : ↥((X.R.MW j (sg0 D X.A3.A)).sm ρ))) =
        c • (GlobalTheory.FlatVecSum.princ (Y.Z.ρ.B i j b)).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) h₀
          (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))) := by
  first | exact @GlobalTheory.LiftClassSumPrinc.thF_eq_classSum_princ | exact GlobalTheory.LiftClassSumPrinc.thF_eq_classSum_princ | (intros; apply GlobalTheory.LiftClassSumPrinc.thF_eq_classSum_princ <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftExtremalVectorEqClassSum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.LiftClassSum

theorem exists_thetaLift_eq_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      X.R.thF j t y (X.geo.v₀ j _) = (Y.Z.ρ.B i j b).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) F := by
  classical
  intro D X E Y i j b t hxi hQ y hy
  obtain ⟨u, hu⟩ := GlobalTheory.LiftClassSum.exists_low D X E Y j
  obtain ⟨m, h₀, c, z, hh₀, hz, hP⟩ := GlobalTheory.T.thetaLift_eq_multiple_principalLevel_classSum D X E Y i j b t hxi hQ y u
  have hB : (Y.Z.ρ.B i j b).Good := Y.Z.good.base i j b
  have hq : (Y.Z.ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  have hc : (Y.Z.ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hgood : ∀ τ : Twist D Circle, τ.Q = ∅ → τ.chi = 1 → τ.Good := by
    rintro ⟨Q0, c0, r0⟩ hq0 hc0
    dsimp only at hq0 hc0
    subst hq0 hc0
    have h1 := Twist.triv_good (D := D) (A := Circle) (Q := ∅) splitSet_empty
    exact ⟨h1.isOpen, h1.rat, h1.real, h1.split, h1.unram, fun _ h => absurd h (Finset.notMem_empty _)⟩
  have hψ : (Y.Z.ρ.tw i b 0 ∅ 1).Good := hgood _ hq hc
  have hA : (Y.Z.ρ.B i j b).admitted (Y.Z.ρ.tw i b 0 ∅ 1).Q := by rw [hq]; exact Base.admissible_empty_of_good hB
  have hBase : GlobalTheory.ConjTwist.BaseOf X.R.toRealDat j (Y.Z.ρ.B i j b) :=
    GlobalTheory.PinBase.baseOf_of_pin D X Y.Z.ρ Y.Z.good Y.Z.pin i j b
  have htup : GlobalTheory.ConjTwist.IsTupOf X.R.toRealDat (Y.Z.ρ.B i j b) (Y.Z.ρ.tw i b 0 ∅ 1) t :=
    ⟨by rw [hxi, hc, mul_one], by rw [hQ, hq, Finset.union_empty]⟩
  have hW : (Y.Z.ρ.B i j b).IsWeil (Y.Z.ρ.tw i b 0 ∅ 1).chi (X.R.ωP j t) := hBase.isWeil X.char.thP.ωP htup
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.classSum_principalLevel_eq_const_mul_classSum D _ _ (Y.Z.ρ.B i j b) hB (D.sp.V_sig _) _ hψ hA _ hW m h₀ hh₀ _
    (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) (Y.Z.good.classes i j b _ hψ hA)
  have hF := GlobalTheory.T.fockReading_translatedForm_mem_complexForms D X E Y i j b t hxi hQ y hy u hu z hz
  refine ⟨(c * κ) • (fun h => X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j t).e y (h * z))), Submodule.smul_mem _ _ hF, ?_⟩
  refine (congrArg (fun v => X.R.thF j t y v) hu.symm).trans (hP.trans ?_)
  exact (congrArg (c • ·) (hκ _ hF)).trans ((smul_smul c κ _).trans (LinearMap.map_smul _ _ _).symm)

end GlobalTheory.LiftClassSum

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftExtremalVectorEqClassSumStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.thetaLift_extremalVector_eq_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      X.R.thF j t y (X.geo.v₀ j _) = (Y.Z.ρ.B i j b).classSum (X.R.ωP j t) (Y.Z.ρ.tw i b 0 ∅ 1) (Y.Z.ρ.rep i j b (Y.Z.ρ.tw i b 0 ∅ 1)) F := by
  first | exact @GlobalTheory.LiftClassSum.exists_thetaLift_eq_classSum | exact GlobalTheory.LiftClassSum.exists_thetaLift_eq_classSum | (intros; apply GlobalTheory.LiftClassSum.exists_thetaLift_eq_classSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectedThetaLiftExtremalVectorEqClassSum

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


noncomputable section

namespace GlobalTheory.LiftClassSum

theorem exists_projected_thetaLift_eq_sum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (t : X.T),
    X.R.xi t = (Y.Z.ρ.B i j b).de.chi → X.R.Q t = (Y.Z.ρ.B i j b).de.Q → ∀ y : (X.R.HV j t).H,
    (∀ (h : Bridge.Gf (Vc D j)) (k : (Y.Z.ρ.B i j b).levJ (Y.Z.ρ.tw i b 0 ∅ 1)),
        (X.R.HV j t).e y (h * (k : Bridge.Gf (Vc D j))) = (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) • (X.R.HV j t).e y h) →
    ∃ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      (X.R.HW j (sg0 D X.A3.A)).e (X.R.thG j t y) (X.geo.v₀ j _) = Y.Z.ρ.sum i j b 0 ∅ 1 F := by
  intro D X E Y i j b t hxi hQ y hy
  obtain ⟨y', hy', he⟩ := GlobalTheory.T.goodProjector_thetaLift_of_baseLevelLaw D X E Y i j b t hxi hQ y hy
  obtain ⟨F, hF, hs⟩ := GlobalTheory.T.thetaLift_extremalVector_eq_classSum D X E Y i j b t hxi hQ y' hy'
  exact ⟨F, hF, he.trans (hs.trans (LinearMap.congr_fun (sum_eq_classSum_ωP D X E Y i j b t hxi hQ) F).symm)⟩

end GlobalTheory.LiftClassSum

end
end
end
