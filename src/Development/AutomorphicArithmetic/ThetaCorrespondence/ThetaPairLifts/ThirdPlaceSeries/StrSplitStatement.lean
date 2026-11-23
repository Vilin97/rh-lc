module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSum
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidalStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseChangeTwistedCuspParts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DictStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.Automorphisms.PlaceA
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceOverTypePrimeDividesOrConjugate
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffSQ

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPlaceIsSplit

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TieFrob

theorem xi_eq_of_heq {D : D7} {nch : NChoice D} {C C' : CharFrame D} (h : C = C') (Tp : TupTied D C nch)
    (Tp' : TupTied D C' nch) (e : HEq Tp Tp') : Tp.xi = Tp'.xi := by
  subst h; cases e; rfl

end GlobalTheory.TieFrob
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrobEigTwEqInvValV

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TieFrob
theorem frobEig_tw_eq_inv_valV_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {((GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂˣ) : ℂ)⁻¹} := by
  intro _ hL D P X _ _ i hμ j hj w hG _
  have hIs := X.recR.base.lev
  set t := X.tupT (D.nd.mu i) with ht
  have hV : GlobalTheory.DownLift.valV X.R j t w = (X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹).val w := by
    have e1 : GlobalTheory.DownLift.valV X.R j t w =
        GlobalTheory.LFun.val (X.R.toLevCh.mu0 (j.1 + 1)) w * GlobalTheory.LFun.val (X.R.toLevCh.xi t) w *
          (GlobalTheory.LFun.val X.R.toLevCh.eta w)⁻¹ := by
      show GlobalTheory.LFun.val (X.R.toLevCh.mu0 (j.1 + 1) * X.R.toLevCh.xi t * X.R.toLevCh.eta⁻¹) w = _
      rw [GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_mul, GlobalTheory.LFun.val_inv]
    rw [e1, GlobalTheory.LFun.val_eq_of_chrEq (hIs.mu0 j), GlobalTheory.LFun.val_eq_of_chrEq (hIs.xi t),
      GlobalTheory.LFun.val_eq_of_chrEq hIs.eta, HChar.val_mul, HChar.val_mul, HChar.val_inv]
  have hxi : X.R.xiH t = P.tp.xi (D.nd.mu i) := by
    rw [X.recR.tupXi _ hμ]
    exact congrFun (xi_eq_of_heq X.cfEq X.Tp P.tp X.tpEq) _
  have hE : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹ := by
    rw [P.chr.tw, P.chr.muC i j hj, P.chr.etaTinv, hxi, X.cfEq]
    rfl
  have hU : (X.R.C.mu0 j * X.R.xiH t * X.R.C.eta⁻¹).UnrAt w := by
    refine HChar.UnrAt.mul (HChar.UnrAt.mul ?_ ?_) (HChar.UnrAt.inv (X.R.C.isEta.unr w))
    · refine (X.R.C.isMu0 j).unr w fun k hk => ?_
      rcases GlobalTheory.StepLaw.div_or_isConjPl_div D X.R.C.P k w hk with hd | ⟨PP, hd, hc⟩
      · exact (hG w (Or.inl ((hIs.Pg w).2 ⟨k, hd⟩))).1 rfl
      · exact (hG PP (Or.inl ((hIs.Pg PP).2 ⟨k, hd⟩))).2 hc
    · by_contra hn
      rcases (hIs.Q_ram t w).1 hn with hq | ⟨PP, hq, hc⟩
      · exact (hG w (Or.inr hq)).1 rfl
      · exact (hG PP (Or.inr hq)).2 hc
  rw [P.chr.frob _ w (by rw [hE]; exact hU), hE, hV, Units.val_inv_eq_inv_val]
end GlobalTheory.TieFrob
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrobEigTwEqInvValVStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.isSplit_at_good_heightOne_place_of_used0 : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (w : HeightOneSpectrum (𝓞 D.host.E)), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → D.naut.frobEig (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) = {((GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂˣ) : ℂ)⁻¹} := by
  exact _root_.GlobalTheory.TieFrob.frobEig_tw_eq_inv_valV_alt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodOffSQStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.good_place_not_mem_S_and_Q_of_tieLab :
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
      (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
      (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep),
      _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D →
      Formalism.MainNotions.SumRepresentations.tieLab D →
      ∀ (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)),
        GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → w ∉ D.nd.S i ∧ w ∉ D.nd.Q i :=
  _root_.GlobalTheory.OffSQ.good_off_SQ_alt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StrSplit

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem GlobalTheory.EigStrSplit.str_split_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ B' : Multiset ℂ, (B w).map (fun a : ℂˣ => (a : ℂ)) = B' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) D.R.t ∧ ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  intro hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw hsp
  obtain ⟨Q, hQx, hu, hBQ⟩ := _root_.GlobalTheory.T.theta_eigen_compatibility_eighth_alt hAF hL D P X hA h41 h7 htl i hμ j hj x hx f hf y hy hy0 hh hops s B hs hB w hw hsp
  obtain ⟨-, Sig, ⟨P0, hP0, hbc⟩, hgood⟩ := hx
  have hcusp := GlobalTheory.T.goodLabels_rank_part_parameter_cuspidal D htl i x Sig ⟨P0, hP0, hbc⟩ hgood
  obtain ⟨hS, hQ⟩ := _root_.GlobalTheory.T.good_place_not_mem_S_and_Q_of_tieLab hL D P X hA h41 htl i w hw
  have hz := _root_.GlobalTheory.T.isSplit_at_good_heightOne_place_of_used0 hAF hL D P X hA htl i hμ j hj w hw hsp
  obtain ⟨B', e, hB'⟩ := _root_.GlobalTheory.T.isSplit_of_isBCV_twistIso_of_isCuspIso hAF hL D P h41 h7 htl i x Q P0 Sig hQx hP0 hcusp hbc w hsp hS hQ hu _ hz
  exact ⟨B', hBQ.trans e, hB'⟩
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StrSplitStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.theta_eigen_compatibility_fifth_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ x ∈ ZgoodN D.nd D.naut i, ∀ f : D.what₂.Mt (D.nd.mu i) (j.1 + 1), (hj ▸ f : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) ∈ eigC D.nd D.naut i x → ∀ y, X.R.extV j (X.tupT (D.nd.mu i)) y = X.fn hμ j f → y ≠ 0 → ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ (s : GlobalTheory.DownLift.Sys D) (B : GlobalTheory.LFun.Fam D.host.E), GlobalTheory.DownLift.IsEigV X.R j (X.tupT (D.nd.mu i)) h s y → GlobalTheory.LFun.IsSysParamD D (GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl X.R (X.tupT (D.nd.mu i))) (Formalism.IndefR.Links.Vc D j).rank s B → ∀ w : HeightOneSpectrum (𝓞 D.host.E), GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) w → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → ∃ B' : Multiset ℂ, (B w).map (fun a : ℂˣ => (a : ℂ)) = B' + GlobalTheory.DownLift.str (Ideal.absNorm w.asIdeal) (GlobalTheory.DownLift.valV X.R j (X.tupT (D.nd.mu i)) w : ℂ) D.R.t ∧ ∀ a ∈ B', ‖a‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ (((D.R.r : ℝ) - 1) / 2) := by
  first | exact @_root_.GlobalTheory.EigStrSplit.str_split_alt | exact _root_.GlobalTheory.EigStrSplit.str_split_alt | (intros; apply _root_.GlobalTheory.EigStrSplit.str_split_alt <;> assumption)
end
end
end
