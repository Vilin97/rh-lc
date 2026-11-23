module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigCLeStatement
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigStringAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointsOfTiedLattices
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SClose
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisLastStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisTailStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SParts
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeNZRecOfJoinStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftSpacesRankConstAndLocalisationScalars

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RankTw

open GlobalTheory.RowCopy GlobalTheory.NRows

theorem used_loc (D : D7) (i : D.nd.Loc) : D.nd.mu i = D.what₂.mu0 ∨ ∃ w, D.nd.mu i = D.what₂.muAt w :=
  Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩

theorem lamPos_of_used {D : D7} (h : LamUsed D) {μ} (hμ : μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : LamPos D μ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h μ hμ ⟨k, by omega⟩

theorem lamLoc {D : D7} (h : LamUsed D) (i : D.nd.Loc) : LamPos D (D.nd.mu i) (D.nd.j i) :=
  lamPos_of_used h (used_loc D i) (D.nd.j_range i).1 (D.nd.j_range i).2

theorem up_injective {D : D7} {μ} {j : ℕ} (h : LamPos D μ j) (hI : DirectSum.IsInternal (D.what₂.isot j)) :
    Function.Injective (D.what₂.thetaT μ j) := by
  have hs : Function.Surjective (D.what₂.thetaP μ j ∘ₗ D.what₂.thetaT μ j) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hI.submodule_iSup_eq_top, iSup_le_iff]
    intro σ f hf
    by_cases h0 : D.what₂.isot j σ = ⊥
    · rw [h0] at hf
      rw [(Submodule.mem_bot ℂ).1 hf]
      exact zero_mem _
    · have hl : ((D.what₂.lamP μ j σ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ((h σ).2 h0).ne'
      refine ⟨((D.what₂.lamP μ j σ : ℝ) : ℂ)⁻¹ • f, ?_⟩
      rw [map_smul, LinearMap.comp_apply, (h σ).1 f hf, smul_smul, inv_mul_cancel₀ hl, one_smul]
  have hi := LinearMap.injective_iff_surjective.2 hs
  rw [LinearMap.coe_comp] at hi
  exact hi.of_comp

theorem rank_of {D : D7} (hI : SumRepresentations.adm8 D) (h : LamUsed D) (L : SizeData₂ D) : TwistedPlaces.adm3 L := by
  intro j hj w hw
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
  have e : D.what₂.muTw w = D.what₂.muAt w := ((D.what₂.muAt_or w).resolve_left hw).symm
  have a := up_injective (lamPos_of_used h (Or.inr ⟨w, e⟩) h1 h2) (hI j h1 h2)
  have b := up_injective (lamPos_of_used h (Or.inl rfl) h1 h2) (hI j h1 h2)
  unfold SizeData₂.zeroSpaceRankAtPlace SizeData₂.dZ0 Rows.Data.Zj
  rw [LinearMap.finrank_range_of_inj a, LinearMap.finrank_range_of_inj b]

theorem main : ∀ D : D7, Formalism.MainNotions.SumRepresentations.adm8 D → GlobalTheory.NRows.LamUsed D →
    (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) ∧ ∀ L : SizeData₂ D, Formalism.MainNotions.TwistedPlaces.adm3 L :=
  fun _ hI h => ⟨GlobalTheory.RankTw.lamLoc h, GlobalTheory.RankTw.rank_of hI h⟩

end GlobalTheory.RankTw

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftSpacesRankConstAndLocalisationScalarsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.thetaLiftSpaces_rank_const_and_localisation_scalars : ∀ D : D7, Formalism.MainNotions.SumRepresentations.adm8 D → GlobalTheory.NRows.LamUsed D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) ∧ ∀ L : SizeData₂ D, Formalism.MainNotions.TwistedPlaces.adm3 L := by
  first | exact @GlobalTheory.RankTw.main | exact GlobalTheory.RankTw.main | (intros; apply GlobalTheory.RankTw.main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigStringAllStatement

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.eigString_of_agree_aux41_adm7_tieLab : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ i, GlobalTheory.NJoin.EigString X i := by
  first | exact @_root_.GlobalTheory.EigStr.eigString_all_of_aux41_adm7_tieLab | exact _root_.GlobalTheory.EigStr.eigString_all_of_aux41_adm7_tieLab | (intros; apply _root_.GlobalTheory.EigStr.eigString_all_of_aux41_adm7_tieLab <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepIsGeometricAtRamifiedPlaces

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsBClosing
end GlobalTheory.RowsBClosing
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.b_conditions_pairLift_splitBC_repOfLoc_of_a : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P → _root_.GlobalTheory.NRows.RowsAAlt D → Formalism.MainNotions.SumRepresentations.adm1 D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) → GlobalTheory.NRows.RowsB D ∧ ∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i := by
  first | exact @_root_.UpperTheory.One.M.latticesB_closing_alt | exact _root_.UpperTheory.One.M.latticesB_closing_alt | (intros; apply _root_.UpperTheory.One.M.latticesB_closing_alt <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepIsGeometricOfLocalConditions

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsAClose
end GlobalTheory.RowsAClose
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.thetaLocal_a_conditions_of_jumpsCard : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.RowsAAlt D := by
  first | exact @_root_.UpperTheory.GalS.a_close_main | exact _root_.UpperTheory.GalS.a_close_main | (intros; apply _root_.UpperTheory.GalS.a_close_main <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepIsGeometricAtAllPlaces

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsAll
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.PointConditions' D := by
  intro hP hHC hCusp hL D I hJ
  have a : _root_.GlobalTheory.NRows.RowsAAlt D := _root_.GlobalTheory.T.thetaLocal_a_conditions_of_jumpsCard hP hL D I.P hJ
  obtain ⟨J⟩ := _root_.GlobalTheory.T.nonempty_join_of_agree hHC hCusp hL D I.P I.X I.agree
  obtain ⟨lamLoc, rank⟩ := GlobalTheory.T.thetaLiftSpaces_rank_const_and_localisation_scalars D I.isot I.lam
  obtain ⟨b, trip⟩ := _root_.GlobalTheory.T.b_conditions_pairLift_splitBC_repOfLoc_of_a hP hL D I.P J a I.adm1 lamLoc
  have Conclusion1 : _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D := I.Conclusion1 (_root_.UpperTheory.GalS.Parts.main_alt_alt D) a b
  have c : GlobalTheory.NRows.RowsC D := _root_.GlobalTheory.T.c_statement_of_pair_lift_splitBC_repOfLoc hL D I.P J a b I.adm1 I.isot Conclusion1 trip
  refine ⟨a, b, c, fun i => ?_, rank⟩
  exact _root_.GlobalTheory.T.type_nonzero_recursion_of_eigen' hL D I.P I.X I.agree I.typeNZ i
    (_root_.GlobalTheory.T.eigString_of_agree_aux41_adm7_tieLab hP.fin hL D I.P I.X I.agree Conclusion1.1 a.temp a.tieLab i)
    (_root_.GlobalTheory.T.eigGood_of_archimedean_signature_adm5 hL D I.P I.X Conclusion1.1 a.tieLab I.mtPar I.adm1 a.tie0 b.a4 a.a5 I.e0loc I.e0read i)
end GlobalTheory.RowsAll
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.theta_conditions_of_inputs_of_jumpsCard : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7), _root_.GlobalTheory.NRows.LinkedInputs hL D → JumpsCard D.nd D.naut → _root_.GlobalTheory.NRows.PointConditions' D := by
  first | exact @_root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.RowsAll.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end
end
