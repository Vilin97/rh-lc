module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrimeStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.PairedCharacterCondition
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChiOneAwayFromType
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TotallyComplexHostE
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricCuspidalMultiplicityOneOfTwisted
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsobaricDiscreteSelfDualMultOneOfIsobaricSumMult
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsobaricRigidOfPin
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SClose
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.JumpDictionary
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AutomorphicGaloisAdmissible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReadingStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTameLabelMu
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SplitLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ConclusionFinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocParOfCharUnrIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.AbsCentralAlt
import Formalism.SharpRestriction.CuspSpanNormBounds.BlockEstimateWords
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlaceLabelOfConjugatePlace

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterTrivialAbovePlaceAdmissible

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChiOneAbove
theorem character_trivial_above_place_admissible_alt (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) :
    Formalism.MainNotions.SumRepresentations.adm5 D := by
  have hrig : IsobaricRigid D.nd D.naut := _root_.GlobalTheory.NPin.isobaricRigid_of_pin_alt hPr.fin hPr.js hL D P
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.cheb D
  exact (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
end GlobalTheory.ChiOneAbove
end
section
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltFurther

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChiOneAbove
theorem main_alt_alt_alt : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.IsdRW D.loc D.nbr i w hw (PairedCharacterCondition.chiGL (D := D) i) ∧
    D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (PairedCharacterCondition.chiGL (D := D) i)) w =
      D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)
        (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) := by
  intro hPr hL D P i w hw
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D := GlobalTheory.BlockCharInf.main D P.cf P.C P.tp P.chr
  have h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D := _root_.UpperTheory.GalS.galClose_alt hPr hL D P
  have h5 := _root_.GlobalTheory.ChiOneAbove.character_trivial_above_place_admissible_alt hPr hL D P
  obtain ⟨ρ, hρc, haway, habove⟩ :=
    (_root_.UpperTheory.GalS.weak' h2 i).2.2 (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (GlobalTheory.ChiOneNoPt.sOne D)
      (GlobalTheory.ChiOneNoPt.integral D hB i)
  have hρ := GlobalTheory.ChiOneNoPt.eq_chi D h5 i w hw ρ hρc haway
  obtain ⟨hdR, hwd, -⟩ := habove w hw
  subst hρ
  refine ⟨((D.loc_tie i w hw).2.1 1 _ (GlobalTheory.JumpDictionaryFoundation.continuous_chiGL D i 1)).2.1.1 hdR, hwd⟩
end GlobalTheory.ChiOneAbove
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAdmissibleCharacterTrivialAbove

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChiOneAbove
end GlobalTheory.ChiOneAbove
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isdRW_chiGL_at_places_over_l : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Br.IsdRW D.loc D.nbr i w hw (PairedCharacterCondition.chiGL (D := D) i) ∧ D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (PairedCharacterCondition.chiGL (D := D) i)) w = D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) := by
  first | exact @_root_.GlobalTheory.ChiOneAbove.main_alt_alt_alt | exact _root_.GlobalTheory.ChiOneAbove.main_alt_alt_alt | (intros; apply _root_.GlobalTheory.ChiOneAbove.main_alt_alt_alt <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MLabUnr

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabFixed
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
theorem lab_rcAt_ofDet_mul_eq (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (ξ η : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (hξ : IsSmoothChar ξ)
    (hη : IsSmoothChar η) (hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → η x = 1) (hξη : IsSmoothChar (ξ * η)) :
    WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 (ξ * η) hξη)) =
      WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ hξ)) := by
  unfold _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have e1 : LocLanglands.cls (Irr.ofDet 1 (ξ * η) hξη).toIrrRep = (GlobalTheory.LocGL.IrrGL.ofChar ξ hξ).tw η hη := by
    rw [GlobalTheory.LocGL.IrrGL.tw_ofChar]; rfl
  have e2 : LocLanglands.cls (Irr.ofDet 1 ξ hξ).toIrrRep = GlobalTheory.LocGL.IrrGL.ofChar ξ hξ := rfl
  rw [e1, e2, _root_.UpperTheory.One.M.LawsM.twist H _ _ _ (UpperTheory.One.M.good_ofChar ξ hξ), H.one η hη, lpChar_lpOfChar, WD.lab_lpTwist]
  intro σ
  have hd := ha.ord_eq (ineIncl _ σ)
  rw [deg_ineIncl, neg_zero] at hd
  apply hu
  have h0 : Valued.v ((a ((ineIncl _) σ) : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ) :
      HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v)) ≠ 0 := by simp
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at hd
  unfold Formalism.L2.Host.IsUnitAt
  rw [← WithZero.exp_log h0, hd, WithZero.exp_zero]
end GlobalTheory.LabFixed
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlaceLabelFixedByConjugation

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabFixed
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
theorem labLP_twist_eq_labAt_ofDet : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (s : ℝ), D.naut.items₂ k (D.naut.plGw k v) (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (D.naut.plGw k v)) s) = _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) := by
  intro hPr hL D P S hT i k v hw hχ s
  haveI := host_isCMField D.host
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, (j : ℕ) + 1 = D.nd.j i := by
    have := D.nd.j_range i
    exact ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  have hμ : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) (S i _ hw).mu := hT.mu i _ hw j hj
  have hψ : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹ := by
    rw [P.chr.tw, P.chr.muC i j hj, P.chr.etaTinv]
  have hc : IsComp (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 (D.naut.plGw k v)
      ((P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v)) := by
    rw [hψ]; exact ⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩
  rw [P.lab k v, P.T.tw, WD.lab_lpTw, _root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp hPr.fin hL D P _ _ _ hc, _root_.GlobalTheory.PendOf.localLabelPolynomial]
  have hηs : IsSmoothChar (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    have := ParLaws.isSmoothChar_loc (P.cf.eta⁻¹) (D.naut.plGw k v)
    convert this using 1
    exact MonoidHom.ext fun x => rfl
  have hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → (P.cf.eta.loc (D.naut.plGw k v))⁻¹ x = 1 := by
    intro x hx
    rw [MonoidHom.inv_apply, P.cf.isEta.unr _ x hx, inv_one]
  have e : (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v) =
      (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    rw [GlobalTheory.Published.ParamAboveModel.eq_loc hμ]
    rfl
  have key : ∀ (ξ' : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (h' : IsSmoothChar ξ'),
      ξ' = (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ →
      WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ' h')) =
        WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 (S i _ hw).mu hχ)) := by
    rintro _ h' rfl
    exact _root_.GlobalTheory.LabFixed.lab_rcAt_ofDet_mul_eq hL D k v _ _ hχ hηs hu h'
  exact key _ _ e
end GlobalTheory.LabFixed
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftSplitsLocally

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TieChiPin
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf → PairedCharacterCondition.tieChi (D := D) := by
  intro hPr hL D P hRow hLab hChi i k hl v
  obtain ⟨S, hS, -, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hPr.fin hL D P hRow
  have hsp : IsSplitPl D.host (D.naut.plGw k v) := GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  obtain ⟨htame, hχ, u, hu, hlab⟩ := _root_.GlobalTheory.T.nonGalois_tame_label_mu_alt hPr hL D P hChi S hS i k v hsp
  refine ⟨u, hu, fun w hw => ⟨fun hw0 => ?_, fun hc => ?_⟩⟩
  · obtain ⟨hdR, hwd⟩ := _root_.GlobalTheory.T.isdRW_chiGL_at_places_over_l hPr hL D P i w hw
    refine ⟨hdR, ?_⟩
    rw [hwd, hw0]
    rw [_root_.GlobalTheory.LabFixed.labLP_twist_eq_labAt_ofDet hPr hL D P S hS i k v hsp hχ, hlab]
  · obtain ⟨hdR, hwd⟩ := _root_.GlobalTheory.T.isdRW_chiGL_at_places_over_l hPr hL D P i w hw
    refine ⟨hdR, ?_⟩
    rw [hwd]
    exact _root_.GlobalTheory.T.placeLabel_of_conjugate_place_alt hPr hL D P hLab S hS i k v hsp hχ u htame hlab w hc _
end GlobalTheory.TieChiPin
end
end
end
end
