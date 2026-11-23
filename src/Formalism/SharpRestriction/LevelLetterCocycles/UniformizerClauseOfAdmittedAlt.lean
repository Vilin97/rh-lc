module

public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
public import Formalism.SharpRestriction.LevelLetterCocycles.LatticeBoundsOfThreeParts
public import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
public import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
public import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
public import Formalism.SharpRestriction.LevelLetterCocycles.ExtDataExtTool
public import Formalism.SharpRestriction.LevelLetterCocycles.FirstLiftOfUniformizerClause
public import Formalism.SharpRestriction.LevelLetterCocycles.IsFracOL
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfFrobeniusHyps
import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FilDimOf
public import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
public import Formalism.SharpRestriction.LevelLetterCocycles.LemmasUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.AnnihilatorGeneralOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PtTransRec
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSZeroSplit
import Formalism.SharpRestriction.LevelLetterCocycles.WachFrobeniusLatticeUnramifiedFunctor
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
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsExpSmulA
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
public import Formalism.SharpRestriction.LevelLetterCocycles.CocyclesToWachVectorsBoundOfExtTool
public import Formalism.SharpRestriction.LevelLetterCocycles.IsTruncIff
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusDifferenceIdentity
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondLiftAtSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.TruncationClauseOfLatticeHypotheses
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.LemKD

section

@[expose] public section

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc


set_option maxHeartbeats 800000 in
theorem lemK_D (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (CR CA CB CK : ℝ) (hA : Formalism.MainNotions.RamifiedCoefficientChains.admitted D HW F Cm CR CA CB CK)
    (hL : Formalism.MainNotions.UnusedSlot80.LevCoeff D HW F) :
    Formalism.MainNotions.WachCoordinates.AtCaseA fun l _ K LL h => Formalism.MainNotions.RamifiedCoefficientChains.Sh.LemK ((HW l).W K 1 LL h.2.2) := by
  intro l _ K LL hA' h5
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  have h1 := hA.1 l K 1 LL hA'.2.2
  have h11 := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs := (HW l).W_s K 1 LL hA'.2.2
  have hp : ((D.loc l).PD K).p ≠ 2 := by rw [(D.loc l).PD_p]; exact hA'.2.1
  have hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F := fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hA'.2.2) :=
    (((h1.2.2.2.2.2.2.2.2.1 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hA'.2.2))) hs hp).2.2
      (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hA'.1)).1
  have tie := ((Cm l).C K 1 LL hA'.2.2).tie
  set_option synthInstance.maxHeartbeats 800000 in
   obtain ⟨hN, hAg⟩ := gam_of_tie _ hs tie
   exact lemK_of _ inferInstance (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL) h1.1 h1.2.2.1 (hL l K LL hA' h5)
    h1.2.2.2.2.1 h11.2.2 hring hN hAg (gamΔ_of_tie _ tie) (ptTrans_rec D HW F hP9 l K LL hA' h5)

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.SecondLiftOfHypotheses

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem second_lift_of_hypotheses [NeZero n] (W : LocWach PD LL O v n) (hZ : TTool2Z W)
    (hF : Formalism.MainNotions.CrystallineLiftingInputs.FTool W) (hB : Sh.BasTool W) (hK : Sh.LemK W) (hD : Sh.FilDim W)
    (hR : Sh.ExpRing W) (hE : Sh.ExpRules W)
    (h2a : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p2aK W T)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hEx : DcrisExactStrict PD LL)
    (hCs : CrysSubQuot PD LL) (hDq : DdREqDcris PD LL) : Step2 W := by
  intro d T₁ T₂ F b S η m hS
  obtain ⟨hDom, hDVR, hFr⟩ := hS.2.2.2.1
  refine ⟨2 * sigC PD.p (hpar n b S) η, Step2A.sigma_bound_le _ _ _ hS.2.1, ?_⟩
  intro s₁ FF _ _ _ _ g N y z μ ν hX F₁ ms hO
  exact second_lift_at_situation W hZ hF hB hK hD hR hE h2a h5 h9 hEx hCs hDq hS s₁ g N y z μ ν hX F₁ ms hO

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.UniformizerClauseOfAdmittedAlt

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
variable {CR CA CB CK : ℝ}

theorem caseA_loc' {l : ℕ} [Fact l.Prime] {K LL : Loc.FinExt l} (hg : Loc.Good K 1 LL)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg)) : Loc.CaseA K LL := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, hg⟩
  obtain ⟨y, hy⟩ := hCA.1.2 ⟨x, hx⟩
  have h2 := y.2.2
  have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
  rw [this] at h2
  exact h2

theorem laurent_clause_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.1

theorem uniformizer_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1

theorem level_tools_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm :=
  Formalism.MainNotions.UnusedSlot80.tools_unramified_statement D HW F Cm ⟨fun l _ K s LL h => (hA.1 l K s LL h).2.2.1, laurent_clause_of_admitted' D HW F Cm hA,
    uniformizer_clause_of_admitted D HW F Cm hA⟩



theorem local_lemmas_of_literature (hA : admitted D HW F Cm CR CA CB CK) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (hHerr : Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F)
    (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : cocyclesToWachVectorsBoundAtGoodExtensions D HW F := by
  intro l _ K LL hg _
  intro d T₁ T₂ F' b S η m hset
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := caseA_loc' D HW hg hCA
  have h5l : 5 ≤ l := by have := hset.2.1; rw [hpl] at this; omega
  set W := (HW l).W K 1 LL hg with hW
  have h1 := hA.1 l K 1 LL hg
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W := h1.2.2.2.2.2.2.2.2.1
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs : W.s = 1 := hCA.2.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hCAl.1)).1
  have C := ((Cm l).C K 1 LL hg).tie
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie W hs C
  have hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W := (level_tools_of_admitted' D HW F Cm hA l K LL hCAl h5l).2
  have hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of W hLev hG.1 hG.2
  have hRing : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of W hring
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F (uniformizer_clause_of_admitted D HW F Cm hA)
  have hL := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm (laurent_clause_of_admitted' D HW F Cm hA) hpt
  have hBas : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of W h9
  have hK : Formalism.MainNotions.RamifiedCoefficientChains.Sh.LemK W := Formalism.MainNotions.N.Pv.LocalLengthBound.lemK_D D HW F Cm CR CA CB CK hA hL l K LL hCAl h5l
  have hFD : Formalism.MainNotions.RamifiedCoefficientChains.Sh.FilDim W := Formalism.MainNotions.N.Pv.LocalLengthBound.filDim_of W hQ
  have hΔ : IsUnit ((W.DelF.card : ℕ) : ↥(OL LL)) := by
    have hcard : W.DelF.card = l - 1 :=
      Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F (uniformizer_clause_of_admitted D HW F Cm hA) l K LL hCAl
    by_contra hnu
    have hm : ((W.DelF.card : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := hnu
    have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
    have e : ((l : ℕ) : ↥(OL LL)) - ((W.DelF.card : ℕ) : ↥(OL LL)) = 1 := by
      rw [hcard, Nat.cast_sub (by omega)]; simp
    have h3 := Submodule.sub_mem _ hlm hm
    rw [e] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(OL LL)).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hP9π : Formalism.MainNotions.LiftingTheory.P9π₀ W := (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W h9 hCA _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W := fun hCA' =>
    Formalism.MainNotions.CrystallineLiftingInputs.RToolNum_holds (D.loc l) (HW l) K LL hg hCA'
  have hDss : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l K 1 LL hg
  have hS1 : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step1 W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.first_lift_of_uniformizer_clause W (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL) hP9π hRN h9 hDss hRu hRing hK hFD
      hBas hE hC hQ
  have hTZ' : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.TTool2Z W :=
    Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.tTool2Z_DU D HW F (uniformizer_clause_of_admitted D HW F Cm hA) hA.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.1 l K LL hg
  have hFT : Formalism.MainNotions.CrystallineLiftingInputs.FTool W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.local_clause_of_admitted_statements D HW F Cm hA l K LL hg
  have h2a : ∀ T : LocLat _ ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys _ T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p2aK W T :=
    fun T hT => ((hA.2.2.1 l K 1 LL hg).1 T hT).2
  have hS2 : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2 W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.second_lift_of_hypotheses W hTZ' hFT hBas hK hFD hRing hRu h2a h1.2.2.2.2.1 h9 hE hC hQ
  have hQT : Formalism.MainNotions.CrystallineLiftingInputs.QTool W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.level_clause_of_admitted_statements D HW F Cm hA h23 l K LL hg
  have hdex : W.DelF.card = ((D.loc l).PD K).p - 1 → ∃ dd : ↥(OL LL), dd * (W.DelF.card : ↥(OL LL)) = 1 :=
    fun _ => hΔ.exists_left_inv
  have hExt : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExtTool W :=
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.extData_extTool W (hHerr l K 1 LL hg).2.2.2 (Formalism.MainNotions.LiftingTheory.liftb_HExt_holds D HW F l K 1 LL hg)
      (Formalism.MainNotions.LiftingTheory.liftb_HOne_holds D HW F l K 1 LL hg) (Formalism.MainNotions.LiftingTheory.lker_HKer_D D HW F a22 l K 1 LL hg)
      (h23 l K LL) ((hFont l K LL hCAl).2.1) hdex h1.2.2.2.2.1 h1.2.2.2.2.2.1 h9 hQT
  exact Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.cocyclesToWachVectorsBound_of_extTool W hExt hS1 hS2 d T₁ T₂ F' b S η m hset

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature
end
end
end
