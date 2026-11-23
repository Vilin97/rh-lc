module

public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TSelF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermRepUnram
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFam
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsFD
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
import Mathlib.Tactic.Linter.HaveILetI
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPlacesOverTypePrimesSplit
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIndicesColumnRowLevelsExact
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstTypePrimeLargeOfRecord
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardPrimesOverOfNorm
public import Formalism.LocalToGlobal.HermitianForms.BothSym
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RankConditionsOfLayerTwo
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DoubleCosetsMassLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll
public import Formalism.LocalToGlobal.BesselHermitianTheta.Lemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassNumberAll
public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TFrameOfRanksRowThree

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem tFrame_of_ranksRow_three : ∀ 𝒞 : FamClass,
    (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) →
      Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  intro 𝒞 h
  haveI : Fact Formalism.L2.SG.Pf.SzHypFD.DsigHC := Formalism.L2.SG.OwnFacts.FD.factDsigHC
  haveI : Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram := ⟨GlobalTheory.hermRepUnram⟩
  exact Formalism.L2.SG.Pf.SzHypFam.hTF_of_ranks 3 (𝒞 := 𝒞) h

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FinprodPlacesOverTypePrimesSplitStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.finprod_places_over_typePrimes_split : ∀ (D : D7) (φ : ℝ → ℝ), (∀ i, StandardLattice.SplitsF D (D.host.g i)) → (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, φ (Ideal.absNorm p.asIdeal : ℝ)) = φ (D.host.g 0) ^ D.R.f * φ (D.host.g 1) ^ D.R.f := by
  first | exact @GlobalTheory.TypedPlacesProduct.finprod_typed_places | exact GlobalTheory.TypedPlacesProduct.finprod_typed_places | (intros; apply GlobalTheory.TypedPlacesProduct.finprod_typed_places <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalIndicesColumnRowLevelsExactStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.localIndices_column_row_levels_exact : ∀ (D : D7) (i : Fin 2), StandardLattice.idxColLoc (D.host.g i) D.R.k = ∏ j ∈ Finset.Icc 1 D.R.k, ((D.host.g i : ℝ) ^ j - 1) ∧ StandardLattice.idxRowLoc (D.host.g i) D.R.k D.R.m = (∏ j ∈ Finset.range D.R.r, ((D.host.g i : ℝ) ^ D.R.r - (D.host.g i : ℝ) ^ j)) / ((D.host.g i : ℝ) ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * (D.host.g i : ℝ) ^ (D.R.k * (D.R.k - 1) / 2)) := by
  first | exact @GlobalTheory.idxColLoc_idxRowLoc_exact | exact GlobalTheory.idxColLoc_idxRowLoc_exact | (intros; apply GlobalTheory.idxColLoc_idxRowLoc_exact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExactRanksOfRecord

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain

namespace GlobalTheory

theorem exact_ranks_of_record : ∀ D : D7, (∀ i, StandardLattice.SplitsF D (D.host.g i)) → StandardLattice.volY0 D = StandardLattice.massI D D.R.r → StandardLattice.FactDstar D → (∀ u, (D.duS u : ℝ) = StandardLattice.duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) → letI := D.host.cmStar; ∀ (V : Type) [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V] [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E) (L : Submodule (𝓞 D.host.E) V), h.IsSymm → (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.k → ∀ u : D.what₂.Word, (D.duS u : ℝ) = Formalism.HermitianLatticesTheory.mass h L * (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, ∏ i ∈ Finset.Icc 1 D.R.k, ((Ideal.absNorm p.asIdeal : ℝ) ^ i - 1)) * (∏ τ, Formalism.MainNotions.S.vand (fun i : Fin D.R.k => (((D.hcW u τ).u i : ℚ) : ℝ)) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f) ∧ (Formalism.HermitianLatticesTheory.IsOrthoLattice h L D.R.r → D.what₂.Dstar = Formalism.HermitianLatticesTheory.mass h L * (∏ᶠ p ∈ {p : HeightOneSpectrum (𝓞 D.host.F) | ((D.host.g 0 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal ∨ ((D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal}, (∏ i ∈ Finset.range D.R.r, ((Ideal.absNorm p.asIdeal : ℝ) ^ D.R.r - (Ideal.absNorm p.asIdeal : ℝ) ^ i)) / ((Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * (Ideal.absNorm p.asIdeal : ℝ) ^ (D.R.k * (D.R.k - 1) / 2))) * ∏ τ, D.dsig τ) := by
  intro D hsp hvol hD hdu V _ _ _ _ h L hs
  letI := D.host.cmStar
  have hmass : ∀ n, Formalism.HermitianLatticesTheory.IsOrthoLattice h L n → Formalism.HermitianLatticesTheory.mass h L = StandardLattice.massI D n :=
    fun n ho => StandardLattice.mass_ortho D.host.E D.sp.cm.cmUnram n V h L ho
  have hcol := GlobalTheory.T.finprod_places_over_typePrimes_split D (fun x : ℝ => ∏ i ∈ Finset.Icc 1 D.R.k, (x ^ i - 1)) hsp
  have hrow := GlobalTheory.T.finprod_places_over_typePrimes_split D (fun x : ℝ => (∏ i ∈ Finset.range D.R.r, (x ^ D.R.r - x ^ i)) /
    (x ^ (D.R.rS * (2 * D.R.k + 2 * D.R.rS + 1)) * x ^ (D.R.k * (D.R.k - 1) / 2))) hsp
  beta_reduce at hcol hrow
  obtain ⟨hc0, hr0⟩ := GlobalTheory.T.localIndices_column_row_levels_exact D 0
  obtain ⟨hc1, hr1⟩ := GlobalTheory.T.localIndices_column_row_levels_exact D 1
  refine ⟨fun ho u => ?_, fun ho => ?_⟩
  · rw [hdu u, hmass _ ho, hcol]
    unfold StandardLattice.duStarU StandardLattice.duStarP StandardLattice.idxPi
    rw [hc0, hc1]
    rfl
  · rw [show D.what₂.Dstar = StandardLattice.DstarD D from hD, hmass _ ho, hrow]
    unfold StandardLattice.DstarD StandardLattice.DstarP StandardLattice.idxSig
    rw [hvol, hr0, hr1]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankConditionOfColumnsEqualSymmetricLevel

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem mu0Tie_of_colsTiedSym : ∀ (D : D7), Formalism.L2.Forms.ColsTiedSym D → ∀ u : D.what₂.Word, StandardLattice.Mu0Tie D u :=
  fun _ C u => Formalism.MainNotions.Ext.Lw.mu0Tie_of_sym C u

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankConditionOfColumnsEqualSymmetricLevelStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions

theorem _root_.GlobalTheory.T.rankCondition_of_columns_equal_symmetricLevel : ∀ (D : D7), Formalism.L2.Forms.ColsTiedSym D → ∀ u : D.what₂.Word, StandardLattice.Mu0Tie D u := by
  first | exact @GlobalTheory.mu0Tie_of_colsTiedSym | exact GlobalTheory.mu0Tie_of_colsTiedSym | (intros; apply GlobalTheory.mu0Tie_of_colsTiedSym <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeEqMassOfReal

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory.RankVolume

theorem definiteSpaceVolume_eq_mass_of_volumeComparison (hU : ∀ D : D7, StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D) :
    ∀ D : D7, Formalism.L2.Theta.RealTied D → StandardLattice.volY0 D = StandardLattice.massI D D.R.r := fun D h =>
  have hT : StandardLattice.VolTie D := Formalism.L2.Theta.VolTieG.volTie h.vol
  StandardLattice.volume_eq_mass_at_rank D (StandardLattice.volume_eq_mass_of_definite D (StandardLattice.volumeMass_of_unfolding D (hU D hT))
    (Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.mass_volume_identity_of_class_decomp D hT (GlobalTheory.genusMassStd_all D)
      (GlobalTheory.DefiniteDecompObj.doubleCosets_mass D)))

end GlobalTheory.RankVolume
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExactRanksAlongTiedFamily

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory
theorem exact_ranks_along_tied_family_alt : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (eps : ℝ) (Fm : FamP eps), _root_.Formalism.L2.TwistSelectionFunctions Fm →
    ∀ C0 Cg cb Cu cT CT : ℝ, PX.RanksF Fm C0 Cg cb Cu cT CT := by
  intro hU eps Fm s C0 Cg cb Cu cT CT
  refine ⟨max s.1 (Fm.x1 + 1), fun x hx i hh => ?_⟩
  have hx1 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_right _ _) hx)
  have R := s.2 x hx1 (le_trans (le_max_left _ _) hx) i
  have hr := R.T.theta.real
  have hm : ∀ u, StandardLattice.Mu0Tie (Fm.D x i) u := GlobalTheory.T.rankCondition_of_columns_equal_symmetricLevel _ R.T.cols
  have h4f : StandardLattice.Conclusion4f (Fm.D x i) (Fm.ex x hx1 i).lev :=
    StandardLattice.HarishChandraReduction.rankFormula_of_classNumber _ _ (ColClassNumber.classNumber_all _ _)
  obtain ⟨-, -, -, -, -, -, -, -, hT, -, h0, h1, -⟩ := hh.1
  have hS : ∀ j, StandardLattice.SplitsF (Fm.D x i) ((Fm.D x i).host.g j) :=
    Fin.forall_fin_two.2 ⟨RankSplit.splitsF_of_norm _ _ ((Fm.D x i).host.g_prime 0) h0,
      RankSplit.splitsF_of_norm _ _ ((Fm.D x i).host.g_prime 1) h1⟩
  exact exact_ranks_of_record (Fm.D x i) hS (RankVolume.definiteSpaceVolume_eq_mass_of_volumeComparison (fun D => hU D) _ hr)
    (StandardLattice.factDstar_fam Fm x hx1 i)
    (fun u => h4f (first_type_prime_large_of_record _) hS u
      (RankSplit.splitsF_of_norm _ _ ((Fm.D x i).mem u).A.T_prime (hT u).1) (hm u))
end GlobalTheory
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RanksAndFrameOfTiedClass

section

@[expose] public section



section
open Formalism.BasicNotions Formalism.MainNotions
namespace GlobalTheory
theorem ranks_and_frame_of_tied_class_alt : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), _root_.Formalism.L2.TwistSelection 𝒞 →
    (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧
      Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  intro hU 𝒞 sel
  have hR : Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu :=
    Formalism.MainNotions.Pk.Closed.of_class fun Fm _ hc =>
      _root_.GlobalTheory.exact_ranks_along_tied_family_alt hU _ Fm (sel Fm hc) _ _ _ _ _ _
  exact ⟨hR, GlobalTheory.tFrame_of_ranksRow_three 𝒞 hR⟩
end GlobalTheory
end
end
end
