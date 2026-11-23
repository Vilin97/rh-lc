module

public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesFinal
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusionsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterionStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineUniversalPartCaseAStatement
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcrisStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsiStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrExtensionClassFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatementsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHoldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedFormsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachRelayLemmaArcCoordinateHypothesesStatement
import Formalism.SharpRestriction.LevelLetterCocycles.DivisibilityInvariantMulLinear

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleArcDatumGivesArcProperty

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem admissibleArcDatum_gives_arcProperty : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → RamifiedCoefficientChains.adm11 D → UnusedSlot80.ArcLiftingCoordinates D HW F Cm :=
  fun D HW F Cm hA h1f h11 => UnusedSlot80.arc_coordinates_final D HW F Cm hA h1f h11

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleArcDatumGivesArcPropertyStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.arcCoordinatesCaseA_of_admArcA_of_P1free_of_adm11 : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → RamifiedCoefficientChains.adm11 D → UnusedSlot80.ArcLiftingCoordinates D HW F Cm := by
  first | exact @GlobalTheory.admissibleArcDatum_gives_arcProperty | exact GlobalTheory.admissibleArcDatum_gives_arcProperty | (intros; apply GlobalTheory.admissibleArcDatum_gives_arcProperty <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSplittingAlongArcsOfAdmissible

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem classSplitAlongArcs : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmSplitA D HW F Cm → UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → DeltaInvariantLattices.P6 D HW F → LiftingTheory.WachKillsQuotients D HW F → InvariantsGenerators.LitFont D HW F → LiftingTheory.adm23 D HW F → TruncatedSeriesCountingBounds.adm9 D → RamifiedCoefficientChains.adm11 D → UnusedSlot80.SplittingArcLifting D HW F Cm :=
  UnusedSlot80.split_case_A_final

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSplittingAlongArcsOfAdmissibleStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.classSplitting_along_arcs_of_admissible : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), UnusedSlot80.AdmSplitA D HW F Cm → UnusedSlot80.AdmArcA D HW F Cm → DeltaInvariantLattices.WachLatticeFreeGlobal D HW F → DeltaInvariantLattices.P6 D HW F → LiftingTheory.WachKillsQuotients D HW F → InvariantsGenerators.LitFont D HW F → LiftingTheory.adm23 D HW F → TruncatedSeriesCountingBounds.adm9 D → RamifiedCoefficientChains.adm11 D → UnusedSlot80.SplittingArcLifting D HW F Cm := by
  first | exact @GlobalTheory.classSplitAlongArcs | exact GlobalTheory.classSplitAlongArcs | (intros; apply GlobalTheory.classSplitAlongArcs <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DDeRhamEqDCrisOfUnramified

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.FontaineAdmissibility

theorem intersectionNumber_baseChange : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D :=
  fun D l _ K LL hb V _ _ _ _ _ ρ _ _ _ hc =>
    GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc

end GlobalTheory.FontaineAdmissibility
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DDeRhamEqDCrisOfUnramifiedStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.dDeRham_eq_dCris_of_unramified : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D := by
  first | exact @GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange | exact GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange | (intros; apply GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisExactStrictElementwiseCrystalline

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem dcris_exact_strict_elementwise : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  intro D l _ K LL
  have hA := (GlobalTheory.T.ramifiedCoefficientChains_adm11 D l K LL).1
  intro hbij V₀ V₁ V₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ₀ ρ₁ ρ₂ ι π _ _ _ _ _ _ _ _ _ hιe hπe hinj hsurj
    hker c₀ c₁ c₂
  obtain ⟨h1, h2, h3, h4⟩ :=
    hA hbij V₀ ρ₀ V₁ ρ₁ V₂ ρ₂ ι π hιe hπe hinj hsurj hker.symm c₀ c₁ c₂
  refine ⟨h1, ?_, h3, fun a => (h4 a).1, ?_⟩
  · intro x hx hπx
    exact Submodule.mem_map.mp (h2.ge ⟨hx, hπx⟩)
  · intro a y hy hyF
    exact (h4 a).2.ge ⟨hy, hyF⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisExactStrictElementwiseCrystallineStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.dcris_exact_strict_elementwise_crystalline : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D := by
  first | exact @GlobalTheory.dcris_exact_strict_elementwise | exact GlobalTheory.dcris_exact_strict_elementwise | (intros; apply GlobalTheory.dcris_exact_strict_elementwise <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBHypothesesAdmitted

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremBAdm

theorem admissible_ranks_of_CMDatum : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  intro hBK hTD hEC D HW F Cm
  have hN1 := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  obtain ⟨hP1, -, -, -, -, hP6, -, hP8, hP9, -⟩ := hN1
  have h54 := GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm
  obtain ⟨-, ⟨hWX, -⟩, hW1, -, -, hH, -, -⟩ := h54
  have hB := GlobalTheory.T.arcTheorem_tools_of_wachModuleConclusions D HW F Cm
  obtain ⟨hSat, -, hSatP, hPi0, hKL, hKill, -, hF1, -⟩ := hB
  obtain ⟨hRelay, hArcAdm⟩ := GlobalTheory.T.wachRelayLemma_arcCoordinateHypotheses hBK hTD hEC D HW F Cm
  have hA11 := GlobalTheory.T.ramifiedCoefficientChains_adm11 D
  have hArc := GlobalTheory.T.arcCoordinatesCaseA_of_admArcA_of_P1free_of_adm11 D HW F Cm hArcAdm hP1 hA11
  have hJ := (GlobalTheory.jumps_exact_adm D HW F).2
  have hExt := GlobalTheory.HerrExtClass.herr_extension_class_formula D HW F
  have hAdm9 := GlobalTheory.T.dcris_exact_strict_elementwise_crystalline D
  have hSplit := GlobalTheory.T.classSplitting_along_arcs_of_admissible D HW F Cm ⟨hP8, hP9, hW1, hJ, hExt, hF1, hRelay, hArc⟩ hArcAdm hP1 hP6 hWX
    (GlobalTheory.T.fontaine_fullFaithful_exact_psi D HW F) hJ hAdm9 hA11
  have hUniv := GlobalTheory.T.crystallineUniversalPart_caseA D HW F Cm ⟨hSat, hKL, hPi0, hArc⟩ hP9 hH (GlobalTheory.T.dDeRham_eq_dCris_of_unramified D)
  exact ⟨(GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm).1, GlobalTheory.T.localConstants_from_admitted_local_Galois_statements hBK hTD hEC D HW F Cm, hSat, hSatP, hKill,
    ArcLiftingSetup.content_divisibility_clause D, GlobalTheory.T.h1fGeneratorBoundAll_loc D, hRelay, hArc, hSplit, hUniv, hAdm9, GlobalTheory.T.blochKato_crystalline_extension_criterion D⟩

end GlobalTheory.TheoremBAdm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBHypothesesAdmittedStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

theorem _root_.GlobalTheory.T.localLifting_theoremB_hypotheses_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  first | exact @GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum | exact GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum | (intros; apply GlobalTheory.TheoremBAdm.admissible_ranks_of_CMDatum <;> assumption)
end
end
