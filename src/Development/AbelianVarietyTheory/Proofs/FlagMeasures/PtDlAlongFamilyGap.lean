module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UniqGapOfUniq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
public import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
public import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
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
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndKFinDecayOfGapOfDecAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.KFinSmooth
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.BesselFunctionBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.DoubleCosetDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselIntegrability.IntegrableGNRpowOfLintegralLtTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FdegOfSchur
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.FlipOneTwo
public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.RStabInv
public import Formalism.SharpRestriction.CuspSpanNormBounds.KFinOfLowUnitH
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DegVand
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorLineUnitAmplitudesLargeGaps
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizesLargeOfPowerBounds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CompactCellConvergence.CellConvergence

-- Source module: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKFIff

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.NoPr

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.CellAmp

def AmpKF0 : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlaceKF L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → Integrable (pairMaj γ b) ν →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

end GlobalTheory.NoPr

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndDecInfAndKFinSmooth

section

@[expose] public section

namespace GlobalTheory.DecInputs

theorem decLow_and_decInf_and_kFinSmooth :
    Formalism.FourierDecayAlt.ThreeDimData.DecLow ∧ Formalism.FourierDecayAlt.ThreeDimData.DecInf ∧ PI.KFinSmooth :=
  ⟨GlobalTheory.DecTransport.decLow_holds, Formalism.L2.SG.BesselDiscreteSeries.decInf,
    Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.admitted.kFinSmooth'⟩

end GlobalTheory.DecInputs
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKF0IffGapIn

section

@[expose] public section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

noncomputable section

namespace GlobalTheory.NoPr.Model

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.FourierDecayAlt.ThreeDimData

theorem ampKF0_iff_gapIn : AmpKF0 ↔ GlobalTheory.GapIn.AmpKF0 := Iff.rfl


open Formalism.MainNotions.S.Pv.AmpDDPf in
theorem ampKF0_holds : AmpKF0 := by
  intro k r L h μG w0 l l' hOPKF γ μR νR ν hCD b hb hab' hpm v v' hv hv' ξ ξ'
  have hSchH := Formalism.FourierDecayAlt.P.schur_hermitian
  have hNI := Formalism.FourierDecayAlt.P.norm_inverse_bound
  have hGG := Formalism.FourierDecayAlt.P.growth_group_bound
  have hRS := Formalism.MainNotions.S.Pv.AmpDDPf.right_stabilizer_invariance
  have hIn := GlobalTheory.DecInputs.decLow_and_decInf_and_kFinSmooth
  obtain ⟨hOP, hK1, hK2⟩ := hOPKF
  obtain ⟨hgap, hOK, -, hw0, hμG, -, -⟩ := hOP
  obtain ⟨hγ, hGf, hmono, hrel, hμR, hOQ, hQ⟩ := hCD
  have hσ : PI.UpqRep.IsDSHpk k r L.ε L.lam L.σ := L.hσ
  obtain ⟨d, hd, hSch⟩ := hSchH k r L.ε L.lam L.Hs L.σ μG L.hlam hσ hμG
  have hw0K : PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ w0 := Formalism.MainNotions.KFiniteLowUnitary.kFin_of_lowUnitH' hw0
  have hw0s : w0 ∈ PI.UpqRep.smoothVecs (k := k) (r := r) L.σ :=
    hIn.2.2 k r L.ε L.lam L.Hs L.σ L.hlam hσ w0 hw0K
  obtain ⟨P, hP, hw⟩ := hw0
  have hnorm : ‖w0‖ = 1 := hw.1
  have hw0ne : w0 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hw1 : ⟪w0, w0⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]
    simp
  have hfd : PI.BesselPeriodGGP.fdegH μG L.σ w0 = d :=
    Formalism.FourierDecayAlt.P.S3dx6.fdeg_of_schur hw0ne hd (hSch w0 w0 w0 w0).2
  obtain ⟨C1, Ws1, -, hC1⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v hv
  obtain ⟨C2, Ws2, -, hC2⟩ := hIn.2.1 k r L.ε L.lam h L.Hs L.σ L.hlam hσ hgap hOK v' hv'
  have e1 : (1 : ℝ) - Formalism.FourierDecayAlt.ThreeDimData.aOf r h = -(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1) := by ring
  have hC1' : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤
      (C1 * (Ws1.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC1 w0 hw0s g hg
  have hC2' : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤
      (C2 * (Ws2.map fun W => ‖PI.UpqRep.dsigW (k := k) (r := r) L.σ W w0‖).sum) *
        Formalism.FourierDecayAlt.B.gN g ^ (-(Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1)) := fun g hg => by
    rw [← e1]; exact hC2 w0 hw0s g hg
  have hAG0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity
  have hab : b ≤ Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 := by linarith
  have hIG : Integrable (fun x : Mt k r =>
      Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1))) μG := by
    have h1 := hGG k r μG (Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b) hμG (by linarith)
    simpa only [neg_sub] using h1
  have hinv : MeasurePreserving (Formalism.FourierDecayAlt.P.B7.invM (k := k) (r := r)) μR μR :=
    ⟨Formalism.FourierDecayAlt.P.B7.measurable_invM, hRS k r L γ μR hOK.1 hγ hGf hrel hmono hμR⟩
  rw [hfd]
  exact amp_core' L hμG hd hSch hNI hw1 l l' hγ hrel hμR hOQ hQ hinv hb hab hIG hpm
    (fun t ht => hK1 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v hv)
    (fun t ht => hK2 _ (Formalism.FourierDecayAlt.P.S3dx6.mem_DD L.σ w0 ht) v' hv') hC1' hC2' ξ ξ'

end GlobalTheory.NoPr.Model

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadingMinorLineUnitAmplitudesLargeGapsStatement

section

@[expose] public section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.leadingMinor_line_unitAmplitudes_largeGaps : GlobalTheory.GapIn.Hyp → GlobalTheory.GapIn.AmpKF0 → CellConv → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C : ℝ, ∀ Cn : ℝ, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl : ℝ), 1000 ≤ Cl → Big D large₂ Cl m₀ → cdScaleTie D → HypZ D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ τ w w', HypTT D w w' → ∀ θ, normWin D large₂ C1 θ → ∀ W, GoodW D τ w w' θ W → ∀ lam', l1dist lam' (lamD D τ) ≤ Cn * D.R.k * (D.R.m : ℝ) ^ 3 → ∀ A₀ : LocS W, GoodS D lam' A₀ → ∀ l : ℕ, l ≤ D.R.rS + 1 → ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∀ AI : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → LocS W, (∀ I, I.card = l → (∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → GoodS D (lam' + s • epsI I) (AI I)) → ∃ a : Finset (Fin (2 * D.R.rS + D.R.k + 1)) → ℂ, (∀ I, I.card = l → (¬ ∃ A : LocS W, GoodS D (lam' + s • epsI I) A) → a I = 0) ∧ (∑ I ∈ univ.filter (fun I => I.card = l), ‖a I‖) ≤ large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2) ∧ ∀ μsec, IsSection D.R.k D.R.rS W.z W.z' μsec → ∀ γ p, RelPt D W.z W.z' γ p → ∀ θ', normWin D large₂ C1 θ' → ∀ νR, RMeas D W γ θ' νR → DminN W.z W.z' γ l • jhUnit D w w' A₀ μsec νR γ = ∑ I ∈ univ.filter (fun I => I.card = l), a I • jhUnit D w w' (AI I) μsec νR γ := by
  first | exact @GlobalTheory.CellMinorLineGap.minor_line | exact GlobalTheory.CellMinorLineGap.minor_line | (intros; apply GlobalTheory.CellMinorLineGap.minor_line <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PtDlAlongFamilyGap

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.FamDlGap

theorem ptDl_along_family_gap : Formalism.HermitianLatticesTheory.SiegelMassRatio → GlobalTheory.GapIn.Hyp → BpJoin.ThmBpDS → ∀ Cg cb Cu cT CT C0 C1 : ℝ, ∃ C thr : ℝ, ∀ (eps : ℝ) (Fm : FamP eps), thr ≤ sC' Fm → thr ≤ sCl Fm → PX.RanksF Fm C0 Cg cb Cu cT CT → ∀ Cn : ℝ, OwnEv Fm fun C' Cl x i => VanishingOnXAndXPlusBranching.adm2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Cn C1 C := by
  intro _ hH _ Cg cb Cu cT CT C0 C1
  have hA : GlobalTheory.GapIn.AmpKF0 := GlobalTheory.NoPr.Model.ampKF0_iff_gapIn.mp GlobalTheory.NoPr.Model.ampKF0_holds
  have hCC : GlobalTheory.CellAmp.CellConv := Formalism.MainNotions.S.Pv.AmpDDPf.cell_convergence
  obtain ⟨C, hC⟩ := GlobalTheory.T.leadingMinor_line_unitAmplitudes_largeGaps hH hA hCC Cg cb Cu cT CT C0 C1
  refine ⟨C, 1000, fun eps Fm _ hCl _ Cn => ?_⟩
  obtain ⟨m₀, hm⟩ := hC Cn
  obtain ⟨x0, hx0⟩ := GlobalTheory.family_sizes_eventually_large eps Fm (max m₀ 1)
  refine ⟨x0, fun x hx i => ?_⟩
  obtain ⟨-, hm1, -, -, hrd, -⟩ := hx0 x hx i
  have hmm : m₀ ≤ ((Fm.D x i).R.m : ℝ) := (le_max_left _ _).trans hm1
  have hm1' : (1 : ℝ) ≤ ((Fm.D x i).R.m : ℝ) := (le_max_right _ _).trans hm1
  have hbig : GlobalTheory.Amp.Big (Fm.D x i) (Fm.L x i) (sCl Fm) m₀ :=
    ⟨hrd, by nlinarith, hmm⟩
  intro hH0
  exact hm (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) hCl hbig (Fm.ties x i).cdScale_tie hH0

end GlobalTheory.FamDlGap
end
end
