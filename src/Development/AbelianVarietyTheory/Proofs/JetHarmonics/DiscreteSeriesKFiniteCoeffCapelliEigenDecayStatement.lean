module

public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
public import Formalism.PeriodIntegrals.CapelliEig
public import CompanionTheory.AutomorphicTheory.PieriRules.InfinitesimalCharacterDiscreteSeries
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselPeriodAdjointPairStatement
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.ZuckermanGapSmall
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Formalism.PeriodIntegrals.DSInfCharCap
public import Formalism.PeriodIntegrals.KFinSmooth
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliEigenvalueKFiniteDiscreteSeriesCoeff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
public import Formalism.HermitianCurvature.StatementQ
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CentredCapelliOperatorFormsAgree
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Admissible
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliKFiniteCoefficient

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliEigenvalueKFiniteDiscreteSeriesCoeffStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.capelli_eigenvalue_kFinite_discreteSeries_coeff : PI.KFinSmooth → PI.DSInfCharCap.DSInfCharCap → PI.CapelliEig.CapEig := by
  first | exact @GlobalTheory.CapelliEigenvalue.capEig | exact GlobalTheory.CapelliEigenvalue.capEig | (intros; apply GlobalTheory.CapelliEigenvalue.capEig <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.CentredCapelliOperatorFormsAgreeStatement

section

@[expose] public section

open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.centredCapelliOperator_forms_agree : ∀ (k r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Y : ℂ) (F : B.Mat k r → V), Q.CV k r Y F = PI.CapelliEig.capC (k := k) (r := r) Y F ∧ Q.CV k r Y F = Formalism.MainNotions.S.capC (k := k) (r := r) Y F := by
  first | exact @GlobalTheory.ThA.centredCapelli_forms_agree | exact GlobalTheory.ThA.centredCapelli_forms_agree | (intros; apply GlobalTheory.ThA.centredCapelli_forms_agree <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesKFiniteCoeffCapelliEigenDecay

section

@[expose] public section

open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CoefRegG

theorem eigDec_of_isKFinCoefT : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  intro k r ε mu h R Wp Wq _ _ _ _ _ _ f hDS hgap hok hf
  have H : BranchingSupport.HypsG := CompanionTheory.PieriExpansion.hypsG_of_zuck CompanionTheory.Zuck.zuckerman_gap
  have := FiniteDimensional.complete ℂ Wp
  have := FiniteDimensional.complete ℂ Wq
  have hsm : PI.KFinSmooth := H.1.2.2.1
  have hDG : R.IsDG ε mu := ⟨hDS.1, hDS.2, h, hgap, hok⟩
  obtain ⟨s, hs⟩ := (GlobalTheory.isCoef_of_translate_smul_exists hsm k r ε mu R Wp Wq (fun _ => 0) (fun _ => 0) hDS).1 f hf
  obtain ⟨h1, h2⟩ := Gp91.GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap H k r ε mu h R Wp Wq (fun _ => 0) (fun _ => 0) f s hDG hgap hok hs
  refine ⟨h1, h2, fun y g hg => ?_⟩
  have hE := GlobalTheory.T.capelli_eigenvalue_kFinite_discreteSeries_coeff hsm CompanionTheory.D.DSIC.discrete_series_infinitesimal_character k r ε mu R.H R.σ Wp Wq hDS.1 hDS.2 f hf (y : ℂ) g hg
  rw [(GlobalTheory.T.centredCapelliOperator_forms_agree k r _ (y : ℂ) f).1, hE]
  simp only [Formalism.QuantumDeterminants.capP, Complex.ofReal_prod, Complex.ofReal_add]

end GlobalTheory.CoefRegG

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesKFiniteCoeffCapelliEigenDecayStatement

section

@[expose] public section

open BranchingSupport BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.discreteSeries_KFinite_coeff_capelli_eigen_decay : ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (f : B.Mat k r → (Wq →L[ℂ] Wp)), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → (haveI := FiniteDimensional.complete ℂ Wp; PI.CapelliEig.IsKFinCoefT (k := k) (r := r) R.σ f) → EigDec f (aOf r h - 1) mu := by
  first | exact @GlobalTheory.CoefRegG.eigDec_of_isKFinCoefT | exact GlobalTheory.CoefRegG.eigDec_of_isKFinCoefT | (intros; apply GlobalTheory.CoefRegG.eigDec_of_isKFinCoefT <;> assumption)
end
end
