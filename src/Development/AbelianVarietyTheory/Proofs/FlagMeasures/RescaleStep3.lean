module

public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Volumes
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.SiegelWeilNarrowOfWide
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ArchPosHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabOrb
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensCnt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensHTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensIdxF
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensVolDone
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocPosV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoNuFin
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameStabilizerHaarNormalisedFibreMeasureStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMeasureUnipotentRadicalCovolumeOneStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsHaarMapProdEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ContinuousMeasureSplitting
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.HermitianMeasureSplitting
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.MapSplitEq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.ProductDecompositionHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedMeasureSplitting.T2SpaceGeneralLinearGroup
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.Style
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.FrameStd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentRatTupOfDetNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilVolumes
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.StdChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicTorusMeasureStabiliserHaar

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem omT_stab_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ a : ℕ, 1 ≤ a → 2 * a < n → ∀ (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 → ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)) (μ' : Measure (stabT (AF F) σ J X0)), Formalism.L2.SG.Volumes.IsOmT F E σ n J ψ (gramE σ J X0) hT νX ∧ μ'.IsHaarMeasure ∧ Formalism.L2.SG.Volumes.IsCompatT F E σ n J X0 μ μ' νX := by
  intro F E _ _ _ _ _ σ hE n J hJ ha hc ψ hψ a ha1 ha2 X0 hT hdet μ hμ
  obtain ⟨νX, hν⟩ := PI.VolStabS.Assembly.exOmT_holds F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ
  obtain ⟨μ', hμ'H, hμ'C⟩ := PI.VolStabS.exStab_of_nu PI.VolStabS.Assembly.nuInv_holds
    PI.VolStabS.nuFin_holds
    (PI.VolStabS.nuNeZero_of_dens PI.VolStabS.archPos_holds PI.VolStabS.locPos_holds
      (PI.VolStabS.densAA_of_open PI.VolStabS.volAA_holds PI.VolStabS.hensAA_holds
        PI.VolStabS.idxH_holds PI.VolStabS.cntAA_holds) PI.VolStabS.qvSum_holds)
    F E σ hE n J hJ ha hc a ha1 ha2 X0 hT hdet ψ hψ μ hμ νX hν
  exact ⟨νX, μ', hν, hμ'H, hμ'C⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicTorusMeasureStabiliserHaarStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → Formalism.MainNotions.UnusedSlot34.SWa1 F E σ n J → Formalism.L2.SG.Pf.NcWeil.StabilizerFirstChernCompatibility F E σ n J → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ a : ℕ, 1 ≤ a → 2 * a < n → ∀ (X0 : Fin a → Fin n → E) (hT : ∀ i j, σ (gramE σ J X0 j i) = gramE σ J X0 i j), (gramE σ J X0).det ≠ 0 → ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure → ∃ (νX : Measure (Fin a → Fin n → AF F ⊗[F] E)) (μ' : Measure (stabT (AF F) σ J X0)), Formalism.L2.SG.Volumes.IsOmT F E σ n J ψ (gramE σ J X0) hT νX ∧ μ'.IsHaarMeasure ∧ Formalism.L2.SG.Volumes.IsCompatT F E σ n J X0 μ μ' νX := by
  first | exact @GlobalTheory.omT_stab_exist | exact GlobalTheory.omT_stab_exist | (intros; apply GlobalTheory.omT_stab_exist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMeasWPrescribed

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.St.MeasWord

theorem exists_measW_prescribed :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
      IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (P : Frame E n r)
      (T : F), P.IsStd σ J T → ∀ (μNinf : Measure (Nsub (Ainf F) σ J P))
      (μHinf : Measure (Hsub (Ainf F) σ J P)) (μN : Measure (Nsub (AF F) σ J P))
      (μH : Measure (Hsub (AF F) σ J P))
      (μSv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Ssub (Fv F v) σ J P)),
      μNinf.IsHaarMeasure → μHinf.IsHaarMeasure → μN.IsHaarMeasure → μH.IsHaarMeasure →
      (∀ v, (μSv v).IsHaarMeasure) →
      ∃ W : MeasW σ J P, W.IsTextNorm ∧ W.μNinf = μNinf ∧ W.μHinf = μHinf ∧ W.μN = μN ∧ W.μH = μH ∧
        W.μSv = μSv := by
  intro F E _ _ _ _ _ σ hCM n J hJ r P T hP μNinf μHinf μN μH μSv hNinf hHinf hN hH hSv
  have : Module.Finite F E := PI.VolSemiDirect.W.Lc.finite_nf F E
  obtain ⟨eH, heH⟩ := PI.UnitaryGroupMassFormula.MeasWCore.hermitian_measure_splitting F E σ n J r P T hCM hJ hP
  obtain ⟨eN, heN⟩ := PI.UnitaryGroupMassFormula.MeasWCore.nilpotent_measure_splitting F E σ n J r P T hCM hJ hP
  have hsm : Measurable (splitA σ J) := (PI.UnitaryGroupMassFormula.MeasWCore.continuous_measure_splitting F E σ n J hCM).measurable
  have : SecondCountableTopology (Hsub (AF F) σ J P) :=
    eH.toHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (Nsub (AF F) σ J P) :=
    eN.toHomeomorph.symm.isEmbedding.secondCountableTopology
  obtain ⟨μHf, hHf, hHeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eH μHinf μH
  obtain ⟨μNf, hNf, hNeq⟩ := GlobalTheory.St.HaarSplit.exists_haar_map_prod_eq eN μNinf μN
  obtain ⟨μSf, hSH, hSeq⟩ := PI.UnitaryGroupMassFormula.MeasWCore.product_decomposition_holds F E σ n J r P T hCM hJ hP μNf μHf hNf hHf
  have : SigmaCompactSpace (Hsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Ainf F) σ J P) := inferInstance
  have : SigmaCompactSpace (Hsub (Af F) σ J P) := inferInstance
  have : SigmaCompactSpace (Nsub (Af F) σ J P) := inferInstance
  have : SigmaFinite μHinf := inferInstance
  have : SigmaFinite μNinf := inferInstance
  have : SigmaFinite μHf := inferInstance
  have : SigmaFinite μNf := inferInstance
  refine ⟨{ μH := μH, μHinf := μHinf, μHf := μHf, μN := μN, μNinf := μNinf, μNf := μNf, μSf := μSf,
            μSv := μSv }, ?_, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hH, hHinf, hHf, hN, hNinf, hNf, hSH, hSv, ?_, ?_, hSeq⟩
  · show (μH.map Subtype.val).map (splitA σ J) = _
    rw [← hHeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eH eH.continuous.measurable heH μHinf μHf
  · show (μN.map Subtype.val).map (splitA σ J) = _
    rw [← hNeq]
    exact PI.UnitaryGroupMassFormula.MeasWCore.map_split_eq (splitA σ J) hsm eN eN.continuous.measurable heN μNinf μNf

end GlobalTheory.St.MeasWord
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.FourMulAddFiveLeRank

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.CmHermitianRankFrames

theorem four_mul_add_five_le_rank (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) :
    4 * D.R.rS + 5 ≤ X.B.I.n := by

  rw [X.n_eq]
  have hk := D.R.m_add_three_le_k
  have h2 := D.R.two_le_m
  obtain ⟨j, hj⟩ := D.R.m_even
  simp only [Formalism.BasicNotions.Ranks.r, Formalism.BasicNotions.Ranks.rS]
  omega

theorem cm_herm_rank_frames : ∀ (D : Formalism.BasicNotions.D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), IsCMExt X.B.I.F X.B.I.E X.B.I.cm.sig ∧ IsHermND X.B.I.cm.sig X.B.I.J ∧ 4 * D.R.rS + 5 ≤ X.B.I.n ∧ ∀ u, ∃ T : X.B.I.F, (Formalism.L2.SG.TypedSets.frameOf X u).IsStd X.B.I.cm.sig X.B.I.J T :=
  fun D X => ⟨MassDataVolumesW.stepCM X, MassDataVolumesW.stepHerm X, four_mul_add_five_le_rank D X,
    fun u => MassDataLevelSSteps.frameStd_holds X u⟩

end GlobalTheory.CmHermitianRankFrames
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RescaleStep3

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

namespace GlobalTheory.St.Rescale

theorem rescaleStep3 :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, GlobalTheory.St.RescaleStep3 D := by
  intro hSW D X hb hM
  obtain ⟨hCM, hH, hsize, hfr⟩ := GlobalTheory.CmHermitianRankFrames.cm_herm_rank_frames D X
  obtain ⟨hA, hC⟩ := GlobalTheory.St.siegelWeil_volumes hSW X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH
  obtain ⟨ψ, hψ, hstd⟩ := Formalism.L2.SG.Pf.standard_character_exists X.B.I.F hCM.1
  have hstd' : Formalism.L2.SG.LocVol.IsStdChar ψ := hstd
  have hG := X.measG_norm
  have hμG : X.measG.μG.IsHaarMeasure := hG.1
  have hherm : ∀ {a : ℕ} (X0 : Fin a → Fin X.B.I.n → X.B.I.E) (i j : Fin a),
      X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) = gramE X.B.I.cm.sig X.B.I.J X0 i j :=
    fun X0 i j => GlobalTheory.FrameGram.hE_swap (GlobalTheory.FrameGram.conj_invol hCM) hH.1 _ _

  have hB : ∀ X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E,
      ∃ μ' : Measure (stabT (AF X.B.I.F) X.B.I.cm.sig X.B.I.J X0), μ'.IsHaarMeasure ∧
        ((gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0 →
          ∃ (hTB : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J X0 j i) =
              gramE X.B.I.cm.sig X.B.I.J X0 i j) (νB : Measure _),
            Formalism.L2.SG.Volumes.IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hTB νB ∧
            Formalism.L2.SG.Volumes.IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J X0 X.measG.μG μ' νB) := by
    intro X0
    by_cases hdet : (gramE X.B.I.cm.sig X.B.I.J X0).det ≠ 0
    · obtain ⟨νX, μ', h1, h2, h3⟩ := GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ
        (2 * D.R.rS + 2) (by omega) (by omega) X0 (hherm X0) hdet X.measG.μG hμG
      exact ⟨μ', h2, fun _ => ⟨hherm X0, νX, h1, h3⟩⟩
    · exact ⟨X.measG.μB X0, hG.2.2.2.2.1 X0, fun h => absurd h hdet⟩
  choose μB' hμB' hBc using hB

  have hW : ∀ u, ∃ W : MeasW X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.TypedSets.frameOf X u), W.IsTextNorm ∧
      W.μNinf = (X.measW u).μNinf ∧ W.μHinf = (X.measW u).μHinf ∧
      (∃ (hT1 : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) j i) =
            gramE X.B.I.cm.sig X.B.I.J (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) i j) (νH : Measure _),
        Formalism.L2.SG.Volumes.IsOmT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J ψ _ hT1 νH ∧
        Formalism.L2.SG.Volumes.IsCompatT X.B.I.F X.B.I.E X.B.I.cm.sig X.B.I.n X.B.I.J
          (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) X.measG.μG W.μH νH) ∧
      covol W.μN = 1 ∧
      ∀ v, Formalism.L2.SG.LocVol.LocTieW X.B.I.cm.sig X.B.I.J ψ v (Formalism.L2.SG.TypedSets.frameOf X u)
        (X.measG.μGv v) (W.μSv v) := by
    intro u
    obtain ⟨T, hP⟩ := hfr u
    obtain ⟨hdet, hT1, -⟩ := GlobalTheory.FrameGram.std_frame_gram X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH
      D.R.rS (Formalism.L2.SG.TypedSets.frameOf X u) T hP
    obtain ⟨νH, μH, h1, h2, h3⟩ := GlobalTheory.T.exists_adelicTorusMeasure_stabiliserHaar X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ
      (D.R.rS + 1 + D.R.rS) (by omega) (by omega) (tupH (Formalism.L2.SG.TypedSets.frameOf X u)) hT1 hdet
      X.measG.μG hμG
    obtain ⟨μN, hN, hN1⟩ := GlobalTheory.T.exists_haarMeasure_unipotentRadical_covolume_one X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH D.R.rS
      (Formalism.L2.SG.TypedSets.frameOf X u) T hP
    have hS : ∀ v : HeightOneSpectrum (𝓞 X.B.I.F),
        ∃ μS : Measure (Ssub (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (Formalism.L2.SG.TypedSets.frameOf X u)),
          μS.IsHaarMeasure ∧ Formalism.L2.SG.LocVol.LocTieW X.B.I.cm.sig X.B.I.J ψ v
            (Formalism.L2.SG.TypedSets.frameOf X u) (X.measG.μGv v) μS := fun v =>
      GlobalTheory.T.exists_frameStabilizerHaar_normalised_fibreMeasure X.B.I.F X.B.I.E X.B.I.cm.sig hCM X.B.I.n X.B.I.J hH hA hC ψ hψ hstd' v D.R.rS
        (Formalism.L2.SG.TypedSets.frameOf X u) T hP (by omega) (X.measG.μGv v) (hG.2.2.2.1 v)
    choose μSv hSv hSt using hS
    have hWn := X.measW_norm u
    obtain ⟨W, hWt, e1, e2, e3, e4, e5⟩ := GlobalTheory.St.MeasWord.exists_measW_prescribed X.B.I.F X.B.I.E X.B.I.cm.sig hCM
      X.B.I.n X.B.I.J hH D.R.rS (Formalism.L2.SG.TypedSets.frameOf X u) T hP
      (X.measW u).μNinf (X.measW u).μHinf μN μH μSv hWn.2.2.2.2.1 hWn.2.1 hN h2 hSv
    refine ⟨W, hWt, e1, e2, ⟨hT1, νH, h1, ?_⟩, ?_, ?_⟩
    · rw [e4]; exact h3
    · rw [e3]; exact hN1
    · intro v; rw [e5]; exact hSt v
  choose mw hw hNinf hHinf hOm hCov hLoc using hW
  let mg : MeasG X.B.I.cm.sig X.B.I.J D.R.rS := { X.measG with μB := μB' }
  have hg : mg.IsTextNorm := ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1, hμB', hG.2.2.2.2.2⟩
  refine ⟨mg, hg, mw, hw, ?_, ψ, hψ, hstd', ?_, ?_⟩
  · refine ⟨hM.1, hM.2.1, hM.2.2.1, fun u => ?_⟩
    have h := hM.2.2.2 u
    constructor
    · show amb (mw u).μNinf = _
      rw [hNinf u]; exact h.1
    · show amb (mw u).μHinf = _
      rw [hHinf u]; exact h.2
  · exact ⟨fun u => ⟨hOm u, hCov u⟩, hBc⟩
  · intro w v
    exact hLoc w v

end GlobalTheory.St.Rescale
end
end
