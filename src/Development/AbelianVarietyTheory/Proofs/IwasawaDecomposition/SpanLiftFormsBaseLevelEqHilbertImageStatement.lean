module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassPresExtMemExtBijIsom
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqTie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanEigenformsAdelicFormsIffClassPresentationStatement
public import Development.AbelianVarietyTheory.Definitions.Foundations.ThetaSeriesTies

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelAdelicTypeImpliesLiftLaw

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.LevToQ
end GlobalTheory.LevToQ

namespace GlobalTheory.LevToQ
theorem units_map_inv_val {K : Type} [Field K] (σ : K →+* ℂ) (u : Kˣ) :
    (((Units.map σ.toMonoidHom u)⁻¹ : ℂˣ) : ℂ) = σ ((u⁻¹ : Kˣ) : K) := by
  simp
end GlobalTheory.LevToQ



theorem GlobalTheory.LevToQ.levtoq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) → ∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hcV hred i t Φ hΦ κ hu h
  have hl := GlobalTheory.DefiniteMult.exists_fin_lift (Vc D i) (κ : Bridge.Gf (Vc D i))
  obtain ⟨k, hkG, hk⟩ := hl
  have hl' := GlobalTheory.DefiniteMult.exists_fin_lift (Vc D i) h
  obtain ⟨g, hgG, hg⟩ := hl'
  have hfk : finE (Vc D i) k = Formalism.UG.bc (swapAE D) (((κ : Bridge.Gf (Vc D i)) : GL _ _)) := by
    rw [finE_eq, ← hk]
    rfl
  have hκQ := κ.2
  have hpar : finE (Vc D i) k ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := by
    rw [hfk]; exact hκQ.1
  have hrt : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) = R.eG ((R.B.L i t).act_tie.red κ) := by
    exact (congrArg (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t)) hfk).trans (hred i t κ).symm
  have hmem : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).conj.H := by
    rw [hrt]
    show R.eG.symm (R.eG ((R.B.L i t).act_tie.red κ)) ∈ F.P0
    simpa using hu
  have hkS : k ∈ levS (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) :=
    ⟨hkG, hpar, hmem⟩
  have hlaw := hΦ k hkS g
  have e1 : (R.cV i).ext Φ (g * k) = Φ (h * κ) := by
    show (R.cV i).ρ (g * k)⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict (g * k))) = _
    have hrr : (finHom (Vc D i)).rangeRestrict (g * k) = h * (κ : Bridge.Gf (Vc D i)) := by
      rw [map_mul, hg]
      exact congrArg (h * ·) hk
    exact (LinearMap.congr_fun ((hcV i).1 _ ((GfC _).inv_mem ((GfC _).mul_mem hgG hkG))) _).trans
      ((Module.End.one_apply _).trans (congrArg Φ hrr))
  have e2 : (R.cV i).ext Φ g = Φ h := by
    show (R.cV i).ρ g⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict g)) = _
    exact (LinearMap.congr_fun ((hcV i).1 _ ((GfC _).inv_mem hgG)) _).trans
      ((Module.End.one_apply _).trans (congrArg Φ hg))
  have hchi : levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) *
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    have hw : (⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hmem⟩ : F.P0) = ⟨_, hu⟩ :=
      Subtype.ext ((congrArg R.eG.symm hrt).trans (R.eG.symm_apply_apply _))
    have c1 : levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k =
        ((Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) : ℂˣ) : ℂ) := rfl
    have c2 := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.levR F false).conj (finE (Vc D i) k)
    have c3 := Formalism.L2.DIV.extendOne_of_mem (R.levR F false).conj.chi hmem
    have c4 : Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k) = (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ :=
      congrArg (Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t))) hfk
    have c5 : (((R.levR F false).conj.chi ⟨_, hmem⟩ : ℂˣ) : ℂ) =
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
      have d1 : (R.levR F false).conj.chi ⟨_, hmem⟩ = ((R.levR F false).chi ⟨_, hmem⟩)⁻¹ := rfl
      have d2 : (R.levR F false).chi ⟨_, hmem⟩ = Units.map D.what₂.embLL.toMonoidHom
          (F.ψ0 ⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hmem⟩) := rfl
      have d3 : (((Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨_, hu⟩))⁻¹ : ℂˣ) : ℂ) =
          D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) :=
        (GlobalTheory.LevToQ.units_map_inv_val D.what₂.embLL (F.ψ0 ⟨_, hu⟩)).trans
          (congrArg (fun u : D.what₂.LLˣ => D.what₂.embLL (u : D.what₂.LL)) (MonoidHom.inv_apply F.ψ0 _).symm)
      exact (congrArg (fun u : ℂˣ => (u : ℂ)) (d1.trans (congrArg (·⁻¹) (d2.trans (congrArg (Units.map D.what₂.embLL.toMonoidHom) (congrArg F.ψ0 hw)))))).trans d3
    have c6 := congrArg (fun u : ℂˣ => (u : ℂ)) (c2.trans (congrArg₂ (· * ·) c3 c4))
    refine c1.trans (c6.trans ?_)
    exact (Units.val_mul _ _).trans ((congrArg (· * (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ)) c5).trans (mul_comm _ _))
  calc Φ (h * κ) = (R.cV i).ext Φ (g * k) := e1.symm
    _ = levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k • (R.cV i).ext Φ g := hlaw
    _ = levChi (Vc D i) (R.βV i) (datVP R i t (R.levR F false)) k • Φ h := congrArg _ e2
    _ = ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) *
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL)) • Φ h := congrArg (· • Φ h) hchi
    _ = _ := mul_smul _ _ _
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseLevelAdelicTypeImpliesLiftLawStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.base_level_adelic_type_implies_lift_law : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) → ∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h := by
  first | exact @GlobalTheory.LevToQ.levtoq | exact GlobalTheory.LevToQ.levtoq | (intros; apply GlobalTheory.LevToQ.levtoq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLawImpliesAdelicExtensionBaseLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LiftSpan

theorem end_smul_smul {W : Type} [AddCommGroup W] [Module ℂ W] (L : Module.End ℂ W) (a b : ℂ) (x : W) :
    L (a • b • x) = (a * b) • L x := by
  rw [map_smul, map_smul, smul_smul]



theorem ext_mem_levSubV_of_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h) → (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hcV hred i t Φ hΦ
  intro k hk g
  have hkG : k ∈ GfC (Vc D i) := hk.1
  have hpar : finE (Vc D i) k ∈ Formalism.L2.DIV.parLev D.sp.cm (Vc D i).gram (R.βV i) (R.datVt i t) := hk.2.1
  have hH : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).H := hk.2.2
  have hq : (finHom (Vc D i)).rangeRestrict k ∈ (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := by
    show Formalism.UG.bc (swapAE D) (finHom (Vc D i) k) ∈
      Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (flagL (R.datVt i t))
    rw [← finE_eq]
    exact ⟨hpar, Subgroup.mem_top _⟩
  set κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q := ⟨_, hq⟩ with hκdef
  have hred' : R.eG ((R.B.L i t).act_tie.red κ) = Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) :=
    hred i t κ
  have hu : (R.B.L i t).act_tie.red κ ∈ F.P0 := by
    have h2 : R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)) ∈ F.P0 := hH
    rw [← hred', MulEquiv.symm_apply_apply] at h2
    exact h2
  have hlaw := hΦ κ hu ((finHom (Vc D i)).rangeRestrict g)
  have hchi : levChi _ (R.βV i) (datVP R i t (R.levR F false)) k =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) •
        D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
    have hH' : Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k) ∈ (R.levR F false).conj.H := hH
    have hP : (⟨R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)), hH⟩ : F.P0) =
        ⟨(R.B.L i t).act_tie.red κ, hu⟩ := Subtype.ext (by
          show R.eG.symm (Formalism.L2.DIV.rTup (R.βV i) (R.datVt i t) (finE (Vc D i) k)) = (R.B.L i t).act_tie.red κ
          rw [← hred', MulEquiv.symm_apply_apply])
    have hw := levFn_withP (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (R.levR F false).conj (finE (Vc D i) k)
    have he := Formalism.L2.DIV.extendOne_of_mem (R.levR F false).conj.chi hH'
    have hw2 : Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) =
        (R.levR F false).conj.chi ⟨_, hH'⟩ * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k) :=
      hw.trans (congrArg (fun u => u * Formalism.L2.DIV.levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) k)) he)
    show ((Formalism.L2.DIV.levFn (R.βV i) (withP (R.datVt i t) (R.levR F false).conj) (finE (Vc D i) k) : ℂˣ) : ℂ) = _
    rw [hw2, Units.val_mul, mul_comm, smul_eq_mul]
    congr 1
    · show (((Units.map D.what₂.embLL.toMonoidHom (F.ψ0 ⟨R.eG.symm _, hH⟩))⁻¹ : ℂˣ) : ℂ) = _
      rw [hP]
      rfl
  have e1 := Formalism.IndefR.Eqv.Act.coefExt_mul (R.cV i) (hcV i) Φ g k hkG
  have e3 : (R.cV i).ext Φ g = (R.cV i).ρ g⁻¹ (Φ ((finHom (Vc D i)).rangeRestrict g)) := rfl
  rewrite [e1, hchi, hlaw, e3, smul_eq_mul]
  exact @end_smul_smul _ _ _ _ _ _ _

end GlobalTheory.LiftSpan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLawImpliesAdelicExtensionBaseLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.lift_law_implies_adelic_extension_base_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.models_cV → R.grp_red_L → ∀ (i : Fin D.R.m) (t : T) (Φ : Bridge.Gf (Vc D i) → (R.cV i).W), (∀ (κ : (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q) (hu : (R.B.L i t).act_tie.red κ ∈ F.P0) (h : Bridge.Gf (Vc D i)), Φ (h * κ) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ : ℂˣ) : ℂ) • D.what₂.embLL ((F.ψ0⁻¹ ⟨_, hu⟩ : D.what₂.LLˣ) : D.what₂.LL) • Φ h) → (R.cV i).ext Φ ∈ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  first | exact @GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift | exact GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift | (intros; apply GlobalTheory.LiftSpan.ext_mem_levSubV_of_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanLiftFormsBaseLevelEqHilbertImage

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.LiftSpan



theorem span_liftForm_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → A.fam.Ok 1 → (∀ i t, Function.Injective (R.extV i t)) → ∀ (i : Fin D.R.m) (t : T), Submodule.span ℂ (Set.range fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) = LinearMap.range (R.extV i t) ⊓ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB _ _ i t
  classical
  have hHV := hB.models.HV i t
  have hjV := hB.models.jV
  have hExt : (R.B.L i t).pres.ExtBij :=
    (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.L i t).pres).2.1
  have key : (fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) =
      fun x => (R.cV i).ext ((R.B.L i t).pres.extL (GlobalTheory.OnTies.srcForm A i t F.P0 F.ψ0⁻¹ x)) := by
    funext x
    exact congrArg (R.cV i).ext (hjV i t _)
  have hR : Set.range (fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) =
      (R.cV i).ext '' ((R.B.L i t).pres.extL ''
        {f | ∀ u : F.P0, A.leftGroupActionLift i t (u : G) f = ((F.ψ0⁻¹ u : D.what₂.LLˣ) : D.what₂.LL) • f}) := by
    rw [key]
    ext Y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨_, (GlobalTheory.TraceIncl.mem_range_srcForm i t F.P0 F.ψ0⁻¹ _).1 ⟨x, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      obtain ⟨x, rfl⟩ := (GlobalTheory.TraceIncl.mem_range_srcForm i t F.P0 F.ψ0⁻¹ f).2 hf
      exact ⟨x, rfl⟩
  rw [hR, Submodule.span_image]
  ext Y
  simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_range]
  have hs1 := GlobalTheory.T.span_eigenforms_adelic_forms_iff_class_presentation (W := (R.cV i).W) (Bridge.ratF (Vc D i)) (A.MtCSD i t) D.what₂.embLL (R.cV i).coef.ρ
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ
    (levEnv (Vc D i) (R.βV i) (R.datVt i t)).Q (levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch (A.leftGroupActionLift i t)
    (R.B.L i t).pres (R.B.L i t).act_tie hExt F.P0 F.ψ0⁻¹
  have hs2a := GlobalTheory.T.base_level_adelic_type_implies_lift_law D G Pl0 T A Ks R F hB.models.cV hB.grp.red_L i t
  have hs2b := GlobalTheory.T.lift_law_implies_adelic_extension_base_level D G Pl0 T A Ks R F hB.models.cV hB.grp.red_L i t
  constructor
  · rintro ⟨Φ, hΦ, rfl⟩
    obtain ⟨hAd, hq⟩ := (hs1 Φ).1 hΦ
    refine ⟨?_, hs2b Φ hq⟩
    have h1 : Φ ∈ LinearMap.range (R.HV i t).e := by rw [hHV.2.1]; exact hAd
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, by rw [← hy]; rfl⟩
  · rintro ⟨⟨y, rfl⟩, hlev⟩
    have h1 : (R.HV i t).e y ∈ LinearMap.range (R.HV i t).e := LinearMap.mem_range_self _ y
    rw [hHV.2.1] at h1
    exact ⟨(R.HV i t).e y, (hs1 _).2 ⟨h1, hs2a _ hlev⟩, rfl⟩

end GlobalTheory.LiftSpan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanLiftFormsBaseLevelEqHilbertImageStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

theorem _root_.GlobalTheory.T.span_liftForms_baseLevel_eq_hilbertImage : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → A.fam.Ok 1 → (∀ i t, Function.Injective (R.extV i t)) → ∀ (i : Fin D.R.m) (t : T), Submodule.span ℂ (Set.range fun x => R.extV i t (R.jV i t (liftForm A F.P0 F.ψ0 i t x))) = LinearMap.range (R.extV i t) ⊓ levSubV (Vc D i) (R.cV i).W (levS _ (R.βV i) (datVP R i t (R.levR F false))) (levChi _ (R.βV i) (datVP R i t (R.levR F false))) := by
  first | exact @GlobalTheory.LiftSpan.span_liftForm_eq | exact GlobalTheory.LiftSpan.span_liftForm_eq | (intros; apply GlobalTheory.LiftSpan.span_liftForm_eq <;> assumption)
end
end
