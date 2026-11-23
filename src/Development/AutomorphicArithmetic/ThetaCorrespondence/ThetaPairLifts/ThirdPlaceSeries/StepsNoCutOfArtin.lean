module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCharactersTypePrimeProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDual1Dot
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
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
import Formalism.SharpRestriction.LevelLetterCocycles.LocalCongruenceBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftFMonoLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDirectLiftingProofStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCountDualLiftingProofStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceMemAdjoin
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedDualFamiliesContinuousStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocks
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeFamilyPotentiallyCrystallineCommonTameExtensStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixOfStabilizerTrivial
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreMoreStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SecondClosedOfFirstClosed
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ResidualIrreducibleRankR
import Mathlib.Tactic.Polynomial.Basic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepType

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualJumpRangeNegativeSignPlaceProof

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Pass.JumpDualStep

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Polynomial TensorProduct
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem jumpDual_main : StepJumpDual := by
  intro D hD hP i r hr eta s S sg U hs hJ Xs w hw n hsg hF
  obtain ⟨hc, hj, hU⟩ := hJ w hw
  refine ⟨insert 0 ((U w).image fun b => -b - 1), ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · constructor <;> push_cast <;> omega
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hu
      obtain ⟨h, -, -⟩ := hU b hb
      have hs' : ((eta : ℚ) + D.R.t + 1) < s := by exact_mod_cast hs
      have hS : (0 : ℚ) ≤ S := by positivity
      have ht : (1 : ℚ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
      have he : (0 : ℚ) ≤ eta := by positivity
      have key : (b : ℚ) ≤ (eta : ℚ) + D.R.t ∧ -((s : ℚ) + S) - 1 ≤ b := by
        rcases h with ⟨h1, h2⟩ | h | h
        · have h1' : (0 : ℚ) ≤ b := by exact_mod_cast h1
          have h2' : (b : ℚ) < D.R.t := by exact_mod_cast h2
          constructor <;> linarith
        · rw [abs_le] at h; unfold cen at h
          constructor <;> linarith [h.1, h.2]
        · unfold cloud cen at h; rw [hsg] at h
          simp only [Bool.false_eq_true, if_false] at h; push_cast at h
          constructor <;> linarith [h.1, h.2]
      have k1 : b ≤ (eta : ℤ) + D.R.t := by exact_mod_cast key.1
      have k2 : -((s : ℤ) + S) - 1 ≤ b := by exact_mod_cast key.2
      constructor <;> push_cast <;> omega
  · exact (Finset.card_insert_le _ _).trans (by have := Finset.card_image_le (s := U w) (f := fun b : ℤ => -b - 1); omega)
  · intro x τ a ha
    have h1 := (GlobalTheory.JumpDual.jump_dual D hD hP i r hr Xs w hw n hF x τ a).1 ha
    refine Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨-a - 1, hj x τ _ h1, by ring⟩))

end GlobalTheory.Pass.JumpDualStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualJumpRangeNegativeSignPlaceProofStatement

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.dualJumpRangeNegativeSignPlace_proof : StepJumpDual := by
  first | exact @GlobalTheory.Pass.JumpDualStep.jumpDual_main | exact GlobalTheory.Pass.JumpDualStep.jumpDual_main | (intros; apply GlobalTheory.Pass.JumpDualStep.jumpDual_main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpRangePositiveSignPlace

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules

theorem stepJumpDirect_holds : StepJumpDirect := by
  intro D i r eta s S sg U hs hJ Xs w hw hsg
  obtain ⟨hc, hj, hU⟩ := hJ w hw
  refine ⟨insert 0 (U w), ?_, Finset.mem_insert_self _ _, ?_, ?_⟩
  · intro u hu
    rcases Finset.mem_insert.1 hu with rfl | hu
    · constructor <;> push_cast <;> omega
    · obtain ⟨h, -, -⟩ := hU u hu
      have hs' : ((eta : ℚ) + D.R.t + 1) < s := by exact_mod_cast hs
      have hS : (0 : ℚ) ≤ S := by positivity
      have ht : (0 : ℚ) ≤ D.R.t := by positivity
      have he : (0 : ℚ) ≤ eta := by positivity
      have key : -((eta : ℚ) + D.R.t + 1) - 1 < u ∧ (u : ℚ) ≤ s + S := by
        rcases h with ⟨h1, h2⟩ | h | h
        · have h1' : (0 : ℚ) ≤ u := by exact_mod_cast h1
          have h2' : (u : ℚ) < D.R.t := by exact_mod_cast h2
          constructor <;> linarith
        · rw [abs_le] at h; unfold cen at h
          constructor <;> linarith [h.1, h.2]
        · unfold cloud cen at h; rw [hsg] at h; simp only [if_true] at h; push_cast at h
          constructor <;> linarith [h.1, h.2]
      have k1 : -((eta : ℤ) + D.R.t + 1) - 1 < u := by exact_mod_cast key.1
      have k2 : u ≤ (s : ℤ) + S := by exact_mod_cast key.2
      constructor <;> push_cast <;> omega
  · exact (Finset.card_insert_le _ _).trans (by omega)
  · intro x τ a ha
    exact Finset.mem_coe.2 (Finset.mem_insert_of_mem (hj x τ a ha))

end GlobalTheory.Pass

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpRangePositiveSignPlaceStatement

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.jump_range_positive_sign_place : StepJumpDirect := by
  first | exact @GlobalTheory.Pass.stepJumpDirect_holds | exact GlobalTheory.Pass.stepJumpDirect_holds | (intros; apply GlobalTheory.Pass.stepJumpDirect_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocksStatement

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.twisted_galois_rep_character_blocks : StepSub := by
  first | exact @GlobalTheory.Pass.stepSub_holds | exact GlobalTheory.Pass.stepSub_holds | (intros; apply GlobalTheory.Pass.stepSub_holds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProof

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Pass

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module

theorem stepDeg_main : StepDeg := fun D _ => GlobalTheory.TypeDegOne.degree_one D

end GlobalTheory.Pass
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePrimeCompletionDegreeOneCountProofStatement

section

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass

theorem _root_.GlobalTheory.T.typePrimeCompletionDegreeOneCount_proof : StepDeg := by
  first | exact @GlobalTheory.Pass.stepDeg_main | exact GlobalTheory.Pass.stepDeg_main | (intros; apply GlobalTheory.Pass.stepDeg_main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreTer

section

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
namespace GlobalTheory.Pass.ResidualSpan
theorem main_alt_alt : _root_.GlobalTheory.Pass.ResidueStatement := by
  intro D hRb _ i r ρ hr π hπ hd
  have hHG : HG D.nd D.naut i := ⟨π, (D.Zgood_tie i π).1 hπ⟩
  have hcont : Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :=
    GlobalTheory.BlockJumpsCompare.continuous_rho D.nd i r ρ π (hr π) hd
  have hrb : IsRhoBar D.nd i (redRep D.nd i (ρ π)) := by
    refine ⟨isOpen_ker_redRep D i (ρ π) hcont, ?_⟩
    intro x w hw B σ hB hσ
    have e2 := congrArg (Polynomial.map (IsLocalRing.residue (D.nd.O i)))
      (charpoly_of_decomp D i r ρ π hd σ)
    rw [Polynomial.map_mul, Polynomial.map_prod, ← Matrix.charpoly_map, ← Matrix.charpoly_map] at e2
    rw [heckePol_res D i x π w, ← (hr π).2.2 w hw B σ hB hσ, ← Matrix.charpoly_map]
    refine (e2.trans ?_).symm
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    simp
  have h := hRb.2 i hHG _ hrb
  unfold ResSpan
  convert h using 3
  funext g
  first
    | rfl
    | (ext a b; simp [mapM, rhoO, redRep, mapRep])
end GlobalTheory.Pass.ResidualSpan
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsNoCutOfArtin

section

@[expose] public section



section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.CongruenceModules
namespace GlobalTheory.Pass
theorem stepsNoCut_of_artin_alt : GlobalTheory.Published.GlobalArtinReciprocity → _root_.GlobalTheory.Pass.NoCutStatement := fun hA =>
  ⟨GlobalTheory.CentralIdem.centralIdemCoeff, GlobalTheory.T.central_elements_from_idempotent_coeffs, GlobalTheory.T.typePrimeCompletionDegreeOneCount_proof, _root_.UpperTheory.GalS.stepType_alt, GlobalTheory.T.typeFamily_potentiallyCrystalline_common_tame_extension,
    GlobalTheory.PotDual.stepPotDual, GlobalTheory.T.jump_range_positive_sign_place, GlobalTheory.T.dualJumpRangeNegativeSignPlace_proof, GlobalTheory.StepLiftPf.main, GlobalTheory.T.twisted_galois_rep_character_blocks, GlobalTheory.T.twisted_dual_families_continuous,
    GlobalTheory.T.localCountDirectLifting_proof, GlobalTheory.T.localCountDualLifting_proof, GlobalTheory.T.blochKatoCharactersTypePrime_proof, _root_.GlobalTheory.Pass.ResidualSpan.main_alt_alt, _root_.GlobalTheory.T.globalPass_of_globalArtinReciprocity hA⟩
end GlobalTheory.Pass
end
end
end
