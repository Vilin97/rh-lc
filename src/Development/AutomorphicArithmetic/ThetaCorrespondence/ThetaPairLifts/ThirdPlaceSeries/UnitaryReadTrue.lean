module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecT
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DivisibleGroupTowerCompatibility
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadS
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicWeightAgreesUnderModularFormDictionaryStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDictionaryCmFieldAutomorphic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsAgreeSplitPlaceDictionary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AlgWeightContragredientExistsUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ExistsCgTrueCharSide
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SphRead
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalIntegrality
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSplitPlaceOfSplitPlaceRealSubfieldHost
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDictionaryCmFieldAutomorphicStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.exists_dictionary_cm_field_automorphic : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n), ∃ U, Dict F π U := by
  first | exact @GlobalTheory.FormDictEx.exists_dict | exact GlobalTheory.FormDictEx.exists_dict | (intros; apply GlobalTheory.FormDictEx.exists_dict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComponentsAgreeSplitPlaceDictionaryStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.localComponents_agree_splitPlace_dictionary : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n) (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (s : SplitPlace L) (σ : SmIrr (GL (Fin n) (s.w.adicCompletion L))), IsCompAlong U (locU n s.w) ((cLoc s.w).comp (locU n s.w).subtype) σ.ρ → ∃ τ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion L)), IsLocS π.S s τ ∧ Nonempty (τ.ρ.Equiv σ.ρ) := by
  first | exact @GlobalTheory.SplitDict.locComp_agree | exact GlobalTheory.SplitDict.locComp_agree | (intros; apply GlobalTheory.SplitDict.locComp_agree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdeleIdentificationNonemptyPresenta

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open Matrix
open scoped TensorProduct

namespace GlobalTheory.FinIsoProof

open GlobalTheory.DefU.ClassFin GlobalTheory.AdeleBaseChange

theorem nonempty_finIso (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Nonempty (FinIso L n) := by
  obtain ⟨ι, hι⟩ := exists_toAd (maximalRealSubfield L) L
  let κ : AL L ≃+* FiniteAdeleRing (𝓞 L) L := RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩
  have hκ : ∀ x a, κ (x ⊗ₜ a) = algebraMap L _ x * adMap (maximalRealSubfield L) L a := hι
  have hc : ∀ y, κ (conjAL L y) = conjFin (cc L) (κ y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | tmul x a =>
      change κ ((IsCMField.complexConj L x) ⊗ₜ a) = _
      rw [hκ, hκ, map_mul, conjFin_adMap (cc L) (fun k => IsCMField.complexConj_apply_eq_self L k), conjFin_algebraMap]
      rfl
  have hc' : ∀ y, κ.symm (conjFin (cc L) y) = conjAL L (κ.symm y) := fun y => by
    rw [RingEquiv.symm_apply_eq, hc, RingEquiv.apply_symm_apply]
  let p : GAf L n →* GL (Fin n) (FiniteAdeleRing (𝓞 L) L) :=
    (GeneralLinearGroup.map κ.toRingHom).comp (ReciprocityTheory.Aut.GA L n).subtype
  have hp : ∀ x, Formalism.UG.cT (conjFin (cc L)) (p x).val * (p x).val = 1 := fun x =>
    unitary_map κ.toRingHom (conjAL L) (conjFin (cc L)) hc x.1.val (mul_eq_one_comm.mp x.2)
  let j : GAf L n →* UA L n := ((finGL L n).comp p).codRestrict (UA L n) fun x => finGL_mem_UA _ (hp x)
  refine ⟨⟨κ, map_tmul_one hι, ?_, j, fun x => MonoidHom.mem_ker.2 (pInf_finGL (p x)), ?_, ?_⟩⟩
  · intro w v h
    have hv : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext h
    subst hv
    refine ⟨locMap _ w, GlobalTheory.LFun.InertChart.continuous_complMap (rfl : w.under (𝓞 (maximalRealSubfield L)) = _), fun a => ?_⟩
    rw [hκ, map_one, one_mul]
    rfl
  · intro x w s t
    have h1 : (finGL L n (p x)).val.map (pFin L) = (p x).val := congrArg Units.val (pFin_finGL (p x))
    exact congrArg (pLoc L w) (congrFun₂ h1 s t)
  · intro y hy
    let z := GeneralLinearGroup.map (pFin L) y.1
    have hz : Formalism.UG.cT (conjFin (cc L)) z.val * z.val = 1 := cT_pFin y
    have hm : GeneralLinearGroup.map κ.symm.toRingHom z ∈ ReciprocityTheory.Aut.GA L n :=
      mul_eq_one_comm.mp (unitary_map κ.symm.toRingHom _ _ hc' z.val hz)
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    have e : p ⟨_, hm⟩ = z := Units.ext (Matrix.ext fun i k => κ.apply_symm_apply _)
    change finGL L n (p ⟨_, hm⟩) = _
    rw [e]
    exact finGL_pFin ⟨y, hy⟩

theorem finIso_nonempty : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), Nonempty (FinIso L n) :=
  fun L _ _ _ n => nonempty_finIso L n

end GlobalTheory.FinIsoProof
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdeleIdentificationNonemptyPresentaStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.unitaryFiniteAdeleIdentification_nonempty_presentations : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ), Nonempty (FinIso L n) := by
  first | exact @GlobalTheory.FinIsoProof.finIso_nonempty | exact GlobalTheory.FinIsoProof.finIso_nonempty | (intros; apply GlobalTheory.FinIsoProof.finIso_nonempty <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.UnitaryReadTrue

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC GlobalTheory.UnitaryReadTrue
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace UpperTheory.One.M

theorem noSplit (D : D7) (w : PlE D.host) (v) (hw : ¬ IsSplitPl D.host w) (hv : NG.OverPl w v) : NoSplit D.host.E v := by
  intro s hs
  by_cases e : s.w = w
  · exact hw (e ▸ GlobalTheory.SplitPlaceConj.isSplitPl_w D s)
  · refine not_isSplitAt D w hw ⟨s.w, e, HeightOneSpectrum.ext ?_⟩
    exact s.w_under.trans ((congrArg HeightOneSpectrum.asIdeal hs).trans hv.symm)

end UpperTheory.One.M
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitaryReadTrue

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC GlobalTheory.UnitaryReadTrue
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace UpperTheory.One.M
theorem unitaryRead_true_alt (sw : _root_.UpperTheory.One.M.TrivialCondition) : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (A : _root_.GlobalTheory.HeightCounting.AUSideAlt D),
    _root_.GlobalTheory.HeightCounting.AutomorphicSideRealised hL D T A → Ud.UnitaryReadS D.nbc (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro hL D T A hA j h1 h2 π
  obtain ⟨π₀, rfl⟩ := A.surj j h1 h2 π
  obtain ⟨F⟩ := GlobalTheory.T.unitaryFiniteAdeleIdentification_nonempty_presentations D.host.E D.R.nV
  obtain ⟨U, hU⟩ := GlobalTheory.T.exists_dictionary_cm_field_automorphic D.host.E D.R.nV F π₀
  refine ⟨U, hU.1, ?_, ?_, ?_⟩
  · intro w hw σ hσ
    obtain ⟨s, rfl⟩ := exists_splitPlace_w D w hw
    obtain ⟨τ, hτ, ⟨e⟩⟩ := GlobalTheory.T.localComponents_agree_splitPlace_dictionary _ _ F π₀ U hU s σ hσ
    have h := hA j h1 h2 π₀ s τ hτ
    show _ = (T.e s.w).symm _
    have hc : GlobalTheory.LocLanglands.cls τ = GlobalTheory.LocLanglands.cls (ParLaws.toRep σ) := by
      unfold GlobalTheory.LocLanglands.cls
      rw [(GlobalTheory.SmGL.IrrRep.cl_eq_iff (σ := τ) (τ := ParLaws.toRep σ)).2 ⟨e⟩]
    rw [Equiv.eq_symm_apply, h, hc]
  · intro w hw hsph
    let v := GlobalTheory.SplitConjPlace.belowE (D := D) w
    have hv : NG.OverPl w v := rfl
    have hsph0 := (A.sph j h1 h2 π₀ w v hw hv).1 hsph
    obtain ⟨s, ϖ, q, hs, hq⟩ :=
      GlobalTheory.InertPlaceConj.exists_conj_isUnramInv D.host.E w (host_unramified D.host w) (not_isSplitAt D w hw)
    obtain ⟨-, hI⟩ := _root_.UpperTheory.One.M.Sph.satAgree _ _ F π₀ U hU v w hv
    obtain ⟨⟨Dv, hDs, hDϖ⟩, hI2⟩ := hI s ϖ q hs hq
    obtain ⟨α, hα, hsat⟩ := A.sat j h1 h2 π₀ v w hv Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_dict _ _ F π₀ U hU v w hv hsph0 Dv)
    obtain ⟨α', hα', hS⟩ := hI2 Dv α hDs hDϖ hα
    refine ⟨fun w' hw' σ hσ => ?_, α', ⟨s, ϖ, q, hs, hq, hS⟩, ?_⟩
    · obtain ⟨t, rfl⟩ := exists_splitPlace_w D w' hw'
      obtain ⟨τ, hτ, ⟨e⟩⟩ := GlobalTheory.T.localComponents_agree_splitPlace_dictionary _ _ F π₀ U hU t σ hσ
      have hc : GlobalTheory.LocLanglands.cls τ = GlobalTheory.LocLanglands.cls (ParLaws.toRep σ) := by
        unfold GlobalTheory.LocLanglands.cls
        rw [(GlobalTheory.SmGL.IrrRep.cl_eq_iff (σ := τ) (τ := ParLaws.toRep σ)).2 ⟨e⟩]
      have := _root_.UpperTheory.One.M.New.sphGood sw hsph0 (noSplit D w v hw hv) t τ hτ
      rwa [hc] at this
    · rw [hsat]
      congr 1
      funext i
      exact (hα' i).symm
  · intro τ
    obtain ⟨b, hb, -⟩ := GlobalTheory.algWt_contragredient _ _ π₀.toAlgWt
    obtain ⟨lam, hl, hhw⟩ := GlobalTheory.T.algebraicWeight_agrees_under_modularForm_dictionary _ _ F π₀ U hU b hb τ
    refine ⟨lam, hl, ?_⟩
    rw [A.wt j h1 h2 π₀ b hb, A.infW j h1 h2 b τ lam.w hhw, infOf_eq_infOfWeight]
theorem cusp_read_rec_t : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
    _root_.GlobalTheory.HeightCounting.CGTrueT hL D T → CuspReadG (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro hL D T C a P ha hP hg
  haveI := host_isCMField D.host
  have hu : (CG.mk P).IsUnitary := CsdUnitary.isUnitary_of_isCsd _ a (CG.mk P) hP
  obtain ⟨π, hπ⟩ := _root_.UpperTheory.One.M.New.cgSurj C a ha ⟨CG.mk P, hu⟩ fun w => by
    obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL D.host.E a P w
    exact (ParLawsT.cls_loc_eq_of_isLocComp hσ).symm ▸ hg w σ hσ
  refine ⟨π, (C.csd a _).2 (by rw [hπ]; exact hP), fun w σ hσ => ?_, fun τ m hm => ?_⟩
  · apply (T.e w).injective
    rw [C.loc, hπ]
    simp only [_root_.GlobalTheory.FormDict.recT_alt, Equiv.apply_symm_apply]
    exact _root_.GlobalTheory.CuspRep.ParLaws.local_parameter_eq_reciprocity_of_is_local_component hL hσ _
  · rw [C.inf, hπ]
    exact CG.HasInfChar.infChar_eq (π := CG.mk P) hm
end UpperTheory.One.M
end
end
end
end
