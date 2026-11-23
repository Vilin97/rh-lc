module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPendingObjectsDepthZeroAdmissibleEigenSpanStatement
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcSymmAlgebraMapHost
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOpenSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisDepthZeroEntrywise
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockVectorJacquetNonzero
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.IsQgOfOver
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisFurtherStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTameMuPlGw
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MDzLoc
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisConjPlaceDual
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.RecLawsH

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RtMemIsoTyp

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CenKeepsType

theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W]
    [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) (S : Submodule ℂ (GAf L n → W)) (h : GAf L n)
    (f : GAf L n → W) (hf : f ∈ NG.isoTyp ρ S) : NG.rt L n h f ∈ NG.isoTyp ρ S := by
  have hle : NG.isoTyp ρ S ≤ (NG.isoTyp ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun U hU => ?_
    intro a ha
    have hU' : U ≤ NG.isoTyp ρ S := le_sSup hU
    exact hU' (hU.1.1.stable h a ha)
  exact hle hf

end GlobalTheory.CenKeepsType
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraCentreKeepsTypeSpacesAtLocalisations

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CenKeepsTypeLoc

theorem main : ∀ (D : D7) (M : MtFam D), AVTied D M → GlobalTheory.HeightCounting.Up.CenLoc D M → OnMtPreservesTypeV D := by
  intro D M A hC i PI z F hF
  by_cases hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
  · obtain ⟨L, -, hL⟩ := hC i
    rw [NTypes.onMt, dite_eq_left hz]
    rw [A.typeV, Submodule.mem_comap] at hF ⊢
    have e : (M.loc i).real (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) ⟨z, hz⟩ F) =
        actSum D L z ((M.loc i).real F) := hL ⟨z, hz⟩ F
    rw [e]
    unfold actSum Finsupp.sum
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (GlobalTheory.CenKeepsType.rt_mem_isoTyp _ _ _ _ hF)
  · rw [NTypes.onMt, dite_eq_right hz]
    exact Submodule.zero_mem _

end GlobalTheory.CenKeepsTypeLoc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraCentreKeepsTypeSpacesAtLocalisationsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.groupAlgebraCentre_keeps_typeSpaces_at_localisations : ∀ (D : D7) (M : MtFam D), AVTied D M → GlobalTheory.HeightCounting.Up.CenLoc D M → OnMtPreservesTypeV D := by
  first | exact @GlobalTheory.CenKeepsTypeLoc.main | exact GlobalTheory.CenKeepsTypeLoc.main | (intros; apply GlobalTheory.CenKeepsTypeLoc.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameGenAtTransport

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LabTies

section Galois

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

def conjHom (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) :
    G E Ω →* G E Ω where
  toFun := GlobalTheory.AntiRamConj.conjAut c hc
  map_one' := by
    ext x
    exact c.apply_symm_apply x
  map_mul' g h := by
    ext x
    change c (g (h (c.symm x))) = c (g (c.symm (c (h (c.symm x)))))
    rw [RingEquiv.symm_apply_apply]

theorem conjHom_apply (c : Ω ≃+* Ω) (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (g : G E Ω) (x : Ω) : conjHom c hc g x = c (g (c.symm x)) := rfl

theorem continuous_conjHom (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y) : Continuous (conjHom c hc) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro U hU
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).1 hU
  obtain ⟨S, hS⟩ := IntermediateField.fg_of_fg_toSubalgebra L (Subalgebra.fg_of_fg_toSubmodule
    ((Submodule.fg_iff_finiteDimensional L.toSubalgebra.toSubmodule).2 hL))
  classical
  let L' := IntermediateField.adjoin E ((S.image c.symm : Finset Ω) : Set Ω)
  have hL' : FiniteDimensional E L' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  refine Filter.mem_map.2 (Filter.mem_of_superset
    ((IntermediateField.fixingSubgroup_isOpen L').mem_nhds (Subgroup.one_mem _)) fun g hg => hLU ?_)
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hg
  have key : L ≤ IntermediateField.fixedField (Subgroup.zpowers (conjHom c hc g)) := by
    rw [← hS, IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    intro f hf
    have h1 : conjHom c hc g x = x := by
      rw [conjHom_apply, hg _ (IntermediateField.subset_adjoin _ _ (by simpa using hx)), RingEquiv.apply_symm_apply]
    exact (Subgroup.zpowers_le (H := MulAction.stabilizer (G E Ω) x)).2 h1 hf
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact (IntermediateField.mem_fixedField_iff _ _).1 (key hx) _ (Subgroup.mem_zpowers _)

theorem tameGenAt_transport (c : Ω ≃+* Ω)
    (hc : ∀ x : E, ∃ y : E, c.symm (algebraMap E Ω x) = algebraMap E Ω y)
    (hc' : ∀ x : E, ∃ y : E, c (algebraMap E Ω x) = algebraMap E Ω y)
    {B B' : ValuationSubring Ω} (hB : ∀ y, y ∈ B ↔ c y ∈ B') {γ γ' : G E Ω} (hγ : ∀ y, γ' (c y) = c (γ y))
    (h : TameGenAt B γ) : TameGenAt B' γ' := by
  have hc'' : ∀ x : E, ∃ y : E, c.symm.symm (algebraMap E Ω x) = algebraMap E Ω y := hc'
  have eB : B' = GlobalTheory.AntiRamConj.moveVal c B := by
    ext y
    rw [GlobalTheory.AntiRamConj.mem_moveVal, hB, RingEquiv.apply_symm_apply]
  have eγ : γ' = conjHom c hc γ := by
    ext y
    rw [conjHom_apply, ← hγ, RingEquiv.apply_symm_apply]
  subst eB eγ
  set f := conjHom c hc
  refine ⟨GlobalTheory.AntiRamConj.conjAut_mem_ine c hc h.1, fun σ hσ => ?_⟩
  have h1 := GlobalTheory.AntiRamConj.conjAut_mem_ine c.symm hc'' hσ
  have e2 : GlobalTheory.AntiRamConj.moveVal c.symm (GlobalTheory.AntiRamConj.moveVal c B) = B := by
    ext x
    simp [GlobalTheory.AntiRamConj.mem_moveVal]
  rw [e2] at h1
  have e3 : σ = f (GlobalTheory.AntiRamConj.conjAut c.symm hc'' σ) := by
    ext x
    rw [conjHom_apply, GlobalTheory.AntiRamConj.conjAut_apply]
    simp
  rw [e3]
  refine map_mem_closure (continuous_conjHom c hc) (h.2 h1) fun τ hτ => ?_
  have h2 := Subgroup.mem_map_of_mem f hτ
  rw [MonoidHom.map_closure] at h2
  refine Subgroup.closure_mono ?_ h2
  rintro _ ⟨a, ha | ha, rfl⟩
  · exact Or.inl (congrArg f ha)
  · refine Or.inr fun y hy => ?_
    rw [GlobalTheory.AntiRamConj.moveVal_lt_one, map_sub, map_div₀, map_one, conjHom_apply, RingEquiv.symm_apply_apply]
    exact ha _ ((map_ne_zero_iff _ c.symm.injective).2 hy)

end Galois

theorem main : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut),
    GlobalTheory.PendOf.LabAll D T → IneRep D ∧ LabDepth D ∧ LabGen D := by
  intro D T ⟨γ, h1, h2, h3⟩
  have hG : GenFam D γ := by
    refine ⟨h1, fun k w hw => ?_⟩
    obtain ⟨v, rfl | hv⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
    · rw [h1]
      exact D.ntypes.tg_gen k v
    · obtain ⟨c, hc1, hc2, hc3⟩ := h2 k v w hv
      refine tameGenAt_transport c (fun x => ⟨D.host.conj x, ?_⟩) (fun x => ⟨_, hc1 x⟩) hc2 hc3
        (D.ntypes.tg_gen k v)
      rw [RingEquiv.symm_apply_eq, hc1, GlobalTheory.AntiRamConj.host_conj_conj]
  have h3' : GlobalTheory.PendOf.Model.LabAll T γ := h3
  exact ⟨GlobalTheory.PendOf.Model.ineRep_of_tie T, GlobalTheory.PendOf.Model.labDepth_of_tie T hG h3',
    GlobalTheory.PendOf.Model.labGen_of_tie T hG h3'⟩

end GlobalTheory.LabTies

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTameAltAlt

section

@[expose] public section



section
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroTame
theorem depthZero_tame_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
    (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf →
    DepthZ D := by
  intro hP hS hL D P hrow hlab hchi
  obtain ⟨S, hT, hLaws, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hP.fin hL D P hrow
  have hfix : ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k),
      TameLP D (D.naut.locV i PI (D.naut.plGw k v)) := by
    intro i PI k v
    have hw := GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v
    have htame := _root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw hL D P S hT i k v hw
    have hTB := _root_.GlobalTheory.T.type_block_of_tame_at_split_place hL D P S hT i _ hw ⟨k, D.naut.plGw_over k v⟩ htame
    obtain ⟨x, hx0, hx⟩ := hTB.2 PI
    have hfixd : x ∈ GlobalTheory.PRep.fixed ((S i _ hw).rep PI).π
        (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin (D.R.r + D.R.t))) := by
      intro h
      have h' : ((S i _ hw).rep PI).π h x = x := GlobalTheory.JacBlock.KOne_le_stab htame hx h.2
      simpa using h'
    have hwild := _root_.GlobalTheory.DepthZeroLoc.main_m_alt hP.bz hS hL D _ _ ((S i _ hw).rep PI) ⟨x, hfixd, hx0⟩
      (UpperTheory.One.M.isQg_of_over D k _ (D.naut.plGw_over k v))
    intro σ hσI hσW
    have hd : D.naut.lpDim (D.naut.locV i PI (D.naut.plGw k v)) = D.R.r + D.R.t := by
      rw [← P.T.dim, (S i _ hw).locV PI, (hLaws i _ hw).dim]
    rw [P.T.inePol _ _ σ hσI, (S i _ hw).locV PI, hT.rc i _ hw, hwild σ hσW, hd]
  intro i PI k w hw
  obtain ⟨v, rfl | hc⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · exact hfix i PI k v
  · exact ((_root_.GlobalTheory.T.conjDual_of_labAll hP hL D P hlab) i PI k v w hc).2.1 (hfix i PI k v)
end GlobalTheory.DepthZeroTame
end
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisDepthZeroTame

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroTame
end GlobalTheory.DepthZeroTame
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.depthZ_of_rowMod_labAll_chiTOk : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf → DepthZ D := by
  first | exact @_root_.GlobalTheory.DepthZeroTame.depthZero_tame_alt | exact _root_.GlobalTheory.DepthZeroTame.depthZero_tame_alt | (intros; apply _root_.GlobalTheory.DepthZeroTame.depthZero_tame_alt <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerSide

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PinClose
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) →
    LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → SumRepresentations.tie0 D → SumRepresentations.adm5 D →
    ZLStable D → CenInt D → SerLL D → CoeffRingsHaveRootsOfUnity D → ∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  intro hPr hSu hL D P hRow hLab hCen hGr hChi ht0 ha5 hZL hCI hSer hZ
  obtain ⟨hIne, hDep, hGen⟩ := GlobalTheory.LabTies.main D P.T hLab
  have hCT : OnMtPreservesTypeV D := GlobalTheory.T.groupAlgebraCentre_keeps_typeSpaces_at_localisations D P.M P.H.av hCen
  have hDZ : DepthZ D := _root_.GlobalTheory.T.depthZ_of_rowMod_labAll_chiTOk hPr hSu hL D P hRow hLab hChi
  have hAdm : PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := _root_.GlobalTheory.T.admDepthZero_of_rowMod_labAll_greenLab hPr hL D P hRow hLab hCen hGr hChi
  have hPar : ∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par,
      ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w := by
    intro S
    refine ⟨P.ty.par.eP.symm ⟨S.1, S.2⟩, fun w => ?_⟩
    rw [P.ty.par.locPar_def]
    have e := P.ty.par.eP.apply_symm_apply (⟨S.1, S.2⟩ : HeightCounting.ParC D)
    rw [e]
  exact GlobalTheory.T.exists_pending_objects_depthZero_admissible_eigenSpan D P.M P.H.hecke P.H.rational P.H.av hPar ht0 ha5 hIne hDep hGen hZL hCI hCT hSer hZ hDZ hAdm
end GlobalTheory.PinClose
end
end
end
end
