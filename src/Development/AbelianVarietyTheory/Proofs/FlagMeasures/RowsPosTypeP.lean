module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsPos
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMultiplicityOneLargeGapAndWhittakerBesselStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HypOfUniqGap
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundAtTermsOfLocalDataStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GoodLoc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoefWeightedLocUncond
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ChoiceFinal
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IsLowUnitHBaseVector
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InstFactDecLow
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataTailBoundClosedFormLargeGapsStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MaximalHermitianLatticeMassRatio
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairCountBoundOfSiegelMassRatios

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocDatCOfBesselOfW

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.TypeAsm

theorem locDatC_of_besselOfW (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) : LocDatC := by
  haveI : Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc := ⟨GlobalTheory.Sloc.CoefWeighted.coefWeightedLoc_uncond⟩
  haveI : Fact Formalism.FourierDecayAlt.ThreeDimData.DecLow := ⟨GlobalTheory.DecTransport.decLow_main⟩
  intro D X hne hG hT
  obtain ⟨C⟩ := Formalism.L2.SG.Pf.choiceExists X 1 one_pos
  have hB : WuBessel C := Formalism.L2.SG.Pf.wuBesselOfLoc_all C hG hBW
    (Formalism.L2.SG.Pf.LocF.locFactor_holds hG C) (fun τ => Formalism.L2.SG.Pf.dsTr C τ)
    (fun τ => Formalism.L2.SG.Pf.haarTr C τ) (fun u τ => Formalism.L2.SG.Pf.colsTypeTr C u τ)
  refine ⟨C, hB, Formalism.L2.SG.Pf.LocF.locFactor_holds hG C, fun u τ => ⟨?_, ?_⟩⟩
  · exact goodW_of C u u τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u τ)
      (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.zTr C u τ) (Formalism.L2.SG.Pf.haarTr C τ)
  · exact goodS_of _ u u τ (Formalism.L2.SG.Pf.goodSRest_all hG hT _ u u τ)

end GlobalTheory.TypeAsm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermAmplitudeFactorNonneg

section

@[expose] public section

noncomputable section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints

namespace GlobalTheory.TypeAsm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem termAmplitudeFactor_nonneg {D : D7} (large₂ : SizeData₂ D) (CH Cs C : ℝ) (hC : 0 ≤ C) (j : ℕ) (δ : ℕ → D.host.E) :
    0 ≤ k2a large₂ CH Cs C j δ := by
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have hS : 0 ≤ k2S D (large₂.sc.b ^ (CH * (D.R.m : ℝ))) j δ := le_trans zero_le_one (one_le_sigma_product _ j δ)
  unfold k2a
  refine mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (div_nonneg hC (Nat.cast_nonneg _)) _)
    (Real.rpow_nonneg (minor_norm_nonneg j δ) _)) (Real.rpow_nonneg ?_ _)) (Real.rpow_nonneg hS _)
  unfold Formalism.MainNotions.S.Cnt.Hb
  exact Real.rpow_nonneg hb.le _

theorem typeBound_of_amplitude_pairs : AmpP → PairsP → TypeP := by
  intro hAmp hPairs Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨CH, hCH, hA⟩ := hAmp Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨Ch, Cp, hCh, hCp, C'₁, Cl₁, hP⟩ := hPairs Cg cb Cw cT CT C0 CH hCH
  refine ⟨CH, Ch, Cp, hCH, hCh, hCp, fun Cs hCs => ?_⟩
  obtain ⟨C₀, hC₀, hA2⟩ := hA Cs (by linarith)
  refine ⟨C₀, fun C hC => ?_⟩
  obtain ⟨C'₂, Cl₂, hA3⟩ := hA2 C hC
  refine ⟨max C'₁ C'₂, max Cl₁ Cl₂, fun C' Cl hC' hCl D large₂ X Y u hTies hK hConc => ?_⟩
  have amp := hA3 C' Cl (le_of_max_le_right hC') (le_of_max_le_right hCl) D large₂ X Y u hTies hK hConc
  have pairs := hP C' Cl (le_of_max_le_left hC') (le_of_max_le_left hCl) D large₂ X Y u hK hConc
  intro j' hj' j'' hj'' δ' δ'' S hS
  have hC0 : 0 ≤ C := le_trans hC₀ hC
  have hdpi : 0 ≤ dpiC X u := Nat.cast_nonneg _
  have hsq : Real.sqrt (dpiC X u) * Real.sqrt (dpiC X u) = dpiC X u := Real.mul_self_sqrt hdpi
  have ha' := termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j' δ'
  have ha'' := termAmplitudeFactor_nonneg large₂ CH Cs C hC0 j'' δ''
  have hK0 : 0 ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') :=
    mul_nonneg hdpi (mul_nonneg ha' ha'')
  have hterm : ∀ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖ ≤
      dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by
    intro p hp
    obtain ⟨hmem, hj1, hj2, hl1, hl2⟩ := hS p hp
    have h1 := amp p.1 hmem.1
    have h2 := amp p.2 hmem.2.1
    rw [hj1, hl1] at h1
    rw [hj2, hl2] at h2
    calc ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖
        ≤ (Formalism.L2.SG.TermOp.wt p.1 * Real.sqrt (dpiC X u) * (omT p.1 * k2a large₂ CH Cs C j' δ')) *
          (Formalism.L2.SG.TermOp.wt p.2 * Real.sqrt (dpiC X u) * (omT p.2 * k2a large₂ CH Cs C j'' δ'')) :=
          mul_le_mul h1 h2 (norm_nonneg _) (le_trans (norm_nonneg _) h1)
      _ = (Real.sqrt (dpiC X u) * Real.sqrt (dpiC X u)) * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
          ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by ring
      _ = _ := by rw [hsq]
  calc ∑ p ∈ S, ‖(Y.tO u u).vec p.1‖ * ‖(Y.tO u u).vec p.2‖
      ≤ ∑ p ∈ S, dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := Finset.sum_le_sum hterm
    _ = dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        ∑ p ∈ S, ((Formalism.L2.SG.TermOp.wt p.1 * Formalism.L2.SG.TermOp.wt p.2) * (omT p.1 * omT p.2)) := by
      rw [Finset.mul_sum]
    _ ≤ dpiC X u * (k2a large₂ CH Cs C j' δ' * k2a large₂ CH Cs C j'' δ'') *
        (massC Y u * (k2e large₂ CH Ch Cp j' δ' * k2e large₂ CH Ch Cp j'' δ'')) :=
      mul_le_mul_of_nonneg_left (pairs j' hj' j'' hj'' δ' δ'' S hS) hK0
    _ = _ := by ring

end GlobalTheory.TypeAsm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairCountBoundOfSiegelMassRatiosStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.termPairCountBound_of_siegelMassRatios : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.TypeAsm.PairsP := by
  first | exact @GlobalTheory.TypeAsm.pair_count_bound_of_siegel_mass | exact GlobalTheory.TypeAsm.pair_count_bound_of_siegel_mass | (intros; apply GlobalTheory.TypeAsm.pair_count_bound_of_siegel_mass <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TypePOfLargeGapDiscreteSeriesBessel

section

@[expose] public section

namespace GlobalTheory.TypeAsm.TopGap

theorem typeBound_of_gap :
    GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → Formalism.L2.SG.RowsPos.TypeP := by
  intro hH hBW

  have hAmp : GlobalTheory.TypeAsm.AmpP :=
    GlobalTheory.T.amplitudeBound_at_terms_of_localData (GlobalTheory.TypeAsm.locDatC_of_besselOfW hBW) (GlobalTheory.T.localDataTailBound_closedForm_largeGaps hH)

  have hPairs : GlobalTheory.TypeAsm.PairsP :=
    GlobalTheory.T.termPairCountBound_of_siegelMassRatios GlobalTheory.Mass.MaxFormula.main GlobalTheory.Mass.siegelMassRatio_holds
  exact GlobalTheory.TypeAsm.typeBound_of_amplitude_pairs hAmp hPairs

end GlobalTheory.TypeAsm.TopGap
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.TypePOfLargeGapDiscreteSeriesBesselStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.typeBound_of_largeGap_discreteSeries_bessel : GlobalTheory.GapIn.Hyp → Formalism.L2.SG.LocWSOf.BesselOfW → Formalism.L2.SG.RowsPos.TypeP := by
  first | exact @GlobalTheory.TypeAsm.TopGap.typeBound_of_gap | exact GlobalTheory.TypeAsm.TopGap.typeBound_of_gap | (intros; apply GlobalTheory.TypeAsm.TopGap.typeBound_of_gap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowsPosTypeP

section

@[expose] public section

namespace GlobalTheory

theorem rowsPos_typeP : Formalism.L2.SG.RowsPos.TypeP :=
  GlobalTheory.T.typeBound_of_largeGap_discreteSeries_bessel (GlobalTheory.GapIn.hyp_of_uniqGap GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.1) GlobalTheory.T.bessel_multiplicity_one_large_gap_and_whittaker_bessel.2

end GlobalTheory
end
end
