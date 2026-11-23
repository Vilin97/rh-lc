module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CorankOnePairsFamilyBoundsOfSiegelWeilStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DegenerateTermsAndCollisionBoundsUniformWidthsStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.GammaRangeOfSizeHypotheses
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.KerInclOn
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnDimensionWindowThreeOfColumnCount
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagAtScale
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalTheoremOfFourPointBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KernelExpansionAbsoluteConvergenceEqualWords
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WuDecayOfGap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowOfCovolumeOntoGrid
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremPublishedInputsVariant

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColumnDimensionWindowThreeOfColumnCountStatement

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.columnDimension_window_three_of_columnCount : ∀ D : D7, DataNW D → (∀ u, GlobalTheory.Core.Rk.RankMu D u) → StandingNumericalData D 3 := by
  first | exact @GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu | exact GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu | (intros; apply GlobalTheory.Core.Diag.standingNumericalData_three_of_dataNW_rankMu <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyConcreteRowDataOfFinitenessBundle

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Diag

theorem concK_of_finX : Formalism.L2.SG.Pf.WuDecayOfGap → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (S : Formalism.L2.SG.SpectralTiesReal.STies D), 29 ≤ C' → 29 ≤ Cl → FinX S.Y → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → Nonempty (Formalism.L2.SG.ThmSOwn.ConcK D) := by
  intro hWu D large₂ C' Cl Cg cb Cu cT CT S hC' hCl hFX hL hTF hH
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH (by linarith) hC'
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties S.X
  exact ⟨Formalism.L2.SG.ThmSOwn.concKOf S ⟨hFX, hK, fun u => Formalism.L2.SG.Pf.RegroupPf.neatKu_K2Level D S.X S.Y u hK,
    (hWu D hG S.X).1, (hWu D hG S.X).2, hL, hTF⟩⟩

end GlobalTheory.Core.Diag
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyConcreteRowDataOfFinitenessBundleStatement

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

theorem _root_.GlobalTheory.T.nonempty_concreteRowData_of_finitenessBundle : Formalism.L2.SG.Pf.WuDecayOfGap → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (S : Formalism.L2.SG.SpectralTiesReal.STies D), 29 ≤ C' → 29 ≤ Cl → FinX S.Y → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → Nonempty (Formalism.L2.SG.ThmSOwn.ConcK D) := by
  first | exact @GlobalTheory.Core.Diag.concK_of_finX | exact GlobalTheory.Core.Diag.concK_of_finX | (intros; apply GlobalTheory.Core.Diag.concK_of_finX <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowBoundFromWindowWidthThree

section

@[expose] public section

open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Rk

theorem exp_add_exp_le_exp_max_succ {C₁ C₂ y : ℝ} (hy : 1 ≤ y) :
    Real.exp (C₁ * y) + Real.exp (C₂ * y) ≤ Real.exp ((max C₁ C₂ + 1) * y) := by
  have hy0 : 0 ≤ y := by linarith
  have a1 : Real.exp (C₁ * y) ≤ Real.exp (max C₁ C₂ * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0)
  have a2 : Real.exp (C₂ * y) ≤ Real.exp (max C₁ C₂ * y) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (le_max_right _ _) hy0)
  have a3 : (2 : ℝ) ≤ Real.exp y := by
    have := Real.add_one_le_exp y
    linarith
  have e : Real.exp ((max C₁ C₂ + 1) * y) = Real.exp (max C₁ C₂ * y) * Real.exp y := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  have hp := Real.exp_pos (max C₁ C₂ * y)
  nlinarith

theorem diagonalRow_bound_from_windowWidthThree : Formalism.L2.SG.Pf.WuDecayOfGap → On {3} VanishingGramTermsBound → On {3} CollS → OneOn {3} true →
    OneOn {3} false →
    GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  intro hW hG hCo h1 h2 Cg cb Cu cT CT hcb hcT
  obtain ⟨C₁, hC₁, t₁, H₁⟩ := h1 Cg cb Cu cT CT hcb hcT
  obtain ⟨C₂, _, t₂, H₂⟩ := h2 Cg cb Cu cT CT hcb hcT
  obtain ⟨tG, HG⟩ := hG Cg cb Cu cT CT hcb hcT
  obtain ⟨tC, HC⟩ := hCo Cg cb Cu cT CT hcb hcT
  refine ⟨max C₁ C₂ + 1, max (max (max t₁ t₂) (max tG tC)) 29, max (max (max t₁ t₂) (max tG tC)) 29,
    by linarith [le_max_left C₁ C₂], ?_⟩
  intro C' Cl hC' hCl D L u hT hE hD
  obtain ⟨⟨large₂, hL, h8, h1G⟩, hR⟩ := hE
  obtain ⟨hTies, hAdm, hHL, hNW, hTF⟩ := hD
  subst hL
  have hS0 : StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT := ⟨h8, hHL.2⟩
  have hD0 : StandingNumericalData D 3 := GlobalTheory.T.columnDimension_window_three_of_columnCount D hNW hR
  have hH0 : Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT 3 := ⟨hS0, hD0, by norm_num⟩
  obtain ⟨S, hF, hLT⟩ := hT.trueD.sTies
  have m1 : ∀ {a b c d e : ℝ}, max (max (max a b) (max c d)) 29 ≤ e →
      a ≤ e ∧ b ≤ e ∧ c ≤ e ∧ d ≤ e ∧ 29 ≤ e := by
    intro a b c d e h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine le_trans ?_ h <;> simp
  obtain ⟨a1, a2, a3, a4, a5⟩ := m1 hC'
  obtain ⟨b1, b2, b3, b4, b5⟩ := m1 hCl
  obtain ⟨c⟩ := GlobalTheory.T.nonempty_concreteRowData_of_finitenessBundle hW D large₂ C' Cl Cg cb Cu cT CT S a5 b5 hF hLT hTF hS0
  have hAC : (c.Y.tO u u).AbsConv := kExp_absConv_tied.2 D c.X c.Y u u c.tie
  have g0 := HG 3 rfl C' Cl a3 b3 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC
  have gc := HC 3 rfl C' Cl a4 b4 D large₂ c.X c.Y c.hF c.hI u h1G hTies hAdm hH0 c.tie hAC
  have o1 := H₁ 3 rfl C' Cl a1 b1 D large₂ c.X c.Y u hTies hH0 c.tie hAC
  have o2 := H₂ 3 rfl C' Cl a2 b2 D large₂ c.X c.Y u hTies hH0 c.tie hAC
  simp only [if_true, Bool.false_eq_true, if_false] at o1 o2
  have hf : (1 : ℝ) ≤ D.R.f := by
    have h4 : D.R.m ^ 4 ≤ D.R.f := hHL.2.2.1
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by have := D.R.two_le_m; omega)
    exact_mod_cast le_trans this h4
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by have := D.R.two_le_m; omega : 1 ≤ D.R.m)
  have hL1 : 1 < large₂.sc.L := hHL.1
  have hy : 1 ≤ (D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L := by
    have : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 := one_le_pow₀ hm
    have h2' : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 5 * D.R.f := one_le_mul_of_one_le_of_one_le this hf
    exact one_le_mul_of_one_le_of_one_le h2' hL1.le
  have hg : ∀ C, gamL D large₂.sc.L C = Real.exp (C * ((D.R.m : ℝ) ^ 5 * D.R.f * large₂.sc.L)) := by
    intro C; unfold gamL; congr 1; ring
  have hsum : gamL D large₂.sc.L C₁ + gamL D large₂.sc.L C₂ ≤ gamL D large₂.sc.L (max C₁ C₂ + 1) := by
    rw [hg, hg, hg]; exact exp_add_exp_le_exp_max_succ hy
  have key := GlobalTheory.T.diagonalTheorem_of_fourPointBounds D c large₂ C' Cl Cg cb Cu cT CT 3 (gamL D large₂.sc.L C₁) (gamL D large₂.sc.L C₂)
    (gamL D large₂.sc.L (max C₁ C₂ + 1)) u a5 b5 hH0 (Real.exp_pos _).le (Real.exp_pos _).le hsum g0 gc o1 o2
  unfold SDiagAt at key
  show TwoTerm D u _ _
  unfold TwoTerm
  rw [d0_eq]
  have e1 : gamL D large₂.sc.L (max C₁ C₂ + 1) = Real.exp ((max C₁ C₂ + 1) * mfL D large₂.sc.L) := by
    rw [hg]; rfl
  have e2 : Real.exp (-((1 / 2 : ℝ) * D.R.k * D.R.f * Real.log D.R.k)) = Real.exp (-(kfk D / 2)) := by
    unfold kfk; congr 1; ring
  have e3 : Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k)) = Real.exp (-kfk D) := by
    unfold kfk; rfl
  rw [e1, e2, e3] at key
  refine le_trans key (le_of_eq ?_)
  ring

end GlobalTheory.Core.Rk
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowOfSiegelWeilUnitary

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Rk

theorem rowDiag_of_siegelWeilUnitary
    (hSW : HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent) :
    GlobalTheory.Core.Rk.RowDiag (fun D L C' => GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) := by
  have hDeg := GlobalTheory.T.degenerateTerms_and_collisionBounds_uniform_widths
  have hOne := GlobalTheory.T.corankOnePairsFamilyBounds_of_siegelWeil hSW 3
  exact GlobalTheory.Core.Rk.diagonalRow_bound_from_windowWidthThree GlobalTheory.wuDecayOfGap (hDeg.1 3) (hDeg.2 3) hOne.1 hOne.2

end GlobalTheory.Core.Rk
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiagonalRowOfSiegelWeilUnitaryStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.diagonalRow_of_siegelWeil_unitary :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent →
      GlobalTheory.Core.Rk.RowDiag (fun D L C' =>
        GlobalTheory.Core.Rk.IsScaleWithBoundedGamma D L C' ∧ ∀ u, GlobalTheory.Core.Rk.RankMu D u) :=
  GlobalTheory.Core.Rk.rowDiag_of_siegelWeilUnitary
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainTheoremPublishedInputsThird

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory
theorem miStarRow_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) ∧ _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition := by
  intro hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA hSWU hL N S Γ
  have hE := _root_.GlobalTheory.T.main_theorem_published_inputs_variant_alt_alt hHCF hCusp hDSC hHCM hCW hHowe hWeil hWSF hSWC hDbl hUDG hDSCl hSA
    (GlobalTheory.T.diagonalRow_of_siegelWeil_unitary hSWU) hL (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun _ q => ⟨q.x.rx⟩)
  have hr := RowE.row hE
  exact ⟨_root_.GlobalTheory.Fc.RL.LinkedAt.of_row hr,
    _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (hr.imp fun _ _ _ h => GlobalTheory.Fc.FourBoundsAtBundles.evW_of_atAll h)⟩
end GlobalTheory
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

theorem _root_.GlobalTheory.T.main_theorem_published_inputs_third_alt_alt : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.StrongApproxSU → HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L (AtAll fun _ _ _ (b : _root_.GlobalTheory.Fc.BundleCondition _ _ _) => (b.B.Q.Rl.toCx3 b.B.Q.F).MIstar2 (b.B.Q.F.eV (b.B.Q.Rl.toCx3 b.B.Q.F).zs) b.B.Q.sEE)) ∧ _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowMultiplicityCondition := by
  first | exact @_root_.GlobalTheory.miStarRow_alt_alt | exact _root_.GlobalTheory.miStarRow_alt_alt | (intros; apply _root_.GlobalTheory.miStarRow_alt_alt <;> assumption)
end
end
end
end
