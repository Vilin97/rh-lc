module

public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSumSizeBoundLargeDataFromFactors
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSumDenominatorBoundOfFactorClaims
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaNormBoundHypothesesSatisfiedStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanClassCountBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanSumCountBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanSumSizeOppositeConjugate
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanTensorSizeBoundOfLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DepthOfSumBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePairBounds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteCoefficientBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteDataBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteInfiniteScalarBounds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteTopTermIntegralBoundOfLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FormValueFiniteInfiniteFactorization
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.GammaFactorLossAtFinitePlaces
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsCurveFieldAboveFiniteNonemptyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMeanLogAreaLogThetaNormLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteTopOfDictionaryDepth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEqualSignKernelsLargeConstantsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConjTopAtOfRankLeOfWeightLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RowSumOfHyp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeBoundFinitePlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDictionaryEventuallyLarge
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfinitePsiBounds
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSumSizeBoundLargeDataFromFactorsStatement

section

@[expose] public section

open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.archimedeanSumSizeBound_largeData_from_factors : SumOKK → DepthK → InfScalK → InfTensK → InfCountK → InfClassK → InfTopK → InfRowK → InfPairK → InfPsiK → InfFormK → InfK := by
  first | exact @GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors | exact GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors | (intros; apply GlobalTheory.Adopt.archimedeanSumSizeBound_largeData_from_factors <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FieldPairComparison

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.FPair
theorem lift_splits_locally : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPairK ∧ InfPairK := fun _ => ⟨finPair, infPair⟩
end GlobalTheory.FPair
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.field_pair_comparison : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPairK ∧ InfPairK := by
  first | exact @_root_.GlobalTheory.FPair.lift_splits_locally | exact _root_.GlobalTheory.FPair.lift_splits_locally | (intros; apply _root_.GlobalTheory.FPair.lift_splits_locally <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KernelConjugationMeanArchimedeanTopTerm

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
namespace GlobalTheory.KerConjMean
theorem archimedean_top_term_kernel_conj_mean : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfTopK := by
  intro hP hI hD hDp
  obtain ⟨C1, hC1, hmean⟩ := GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le
  obtain ⟨CF0, hCF⟩ := _root_.GlobalTheory.T.kernel_conjugation_average hP hI hD hDp C1 hC1
  obtain ⟨CF0', hCF'⟩ := GlobalTheory.T.rationalEqualSignKernels_largeConstants
  refine ⟨max CF0 CF0', fun CF hCF0 => ?_⟩
  obtain ⟨C0, hC0⟩ := hCF CF (le_trans (le_max_left _ _) hCF0)
  obtain ⟨C0', hC0'⟩ := hCF' CF (le_trans (le_max_right _ _) hCF0)
  refine ⟨max C0 C0', fun ε C hC => ?_⟩
  obtain ⟨x0, hx0⟩ := hC0 ε C (le_trans (le_max_left _ _) hC)
  obtain ⟨x0', hx0'⟩ := hC0' ε C (le_trans (le_max_right _ _) hC)
  refine ⟨max x0 x0', fun D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt hF => ?_⟩
  obtain ⟨a0, nD, Gd, ha0, hnD, hGd, hsum, hbound⟩ :=
    hx0 D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
  have hrat := hx0' D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hIs hAt hF
  obtain ⟨hL1, hLrd, hLd⟩ := sizes D large₂ Γ Pl0 T A Ks R F hS
  obtain ⟨hmA, hmT⟩ := hmean D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 _ hL1 hLrd hLd
  refine ⟨fun p => a0 + nD * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hArea D ch.S.Z.δ ch.S.Z.t0) +
    Gd * avg D ch.S.Z.δ ch.S.Z.t0 p.embedding (hTh D ch.S.Z.δ ch.S.Z.t0), ?_, ?_⟩
  · refine (meanInf_affine _ a0 nD Gd _ _ ha0).trans (le_trans ?_ hsum)
    have e1 := mul_le_mul_of_nonneg_left hmA hnD
    have e2 := mul_le_mul_of_nonneg_left hmT hGd
    nlinarith
  · intro p Φ β d hocc c j B v hv
    obtain ⟨f, hf⟩ := hrat Φ β d hocc c j
    obtain ⟨u, rfl, hu⟩ := hv
    refine ⟨f u, (hf u).symm, ?_⟩
    obtain ⟨hfin, hne⟩ := GlobalTheory.T.embeddingsCurveFieldAbove_finite_nonempty D (hI D) ch.S.Z.δ ch.S.Z.t0 ch.S.Z.crv ch.S.Z.pt0 p.embedding
    obtain ⟨⟨ρ₁, hρ₁, h₁⟩, ⟨ρ₂, hρ₂, h₂⟩⟩ := exists_avg _ hfin hne a0 nD Gd
      (hArea D ch.S.Z.δ ch.S.Z.t0) (hTh D ch.S.Z.δ ch.S.Z.t0)
    rcases le_or_gt 0 B with hB | hB
    · exact (hbound Φ β d hocc c j f hf p.embedding ρ₁ hρ₁ u B hu).trans
        (mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 h₁) hB)
    · exact (hbound Φ β d hocc c j f hf p.embedding ρ₂ hρ₂ u B hu).trans
        (mul_le_mul_of_nonpos_right (Real.exp_le_exp.2 h₂) hB.le)
end GlobalTheory.KerConjMean
end
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.kernel_conjugation_mean_archimedean_top_term : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → InfTopK := by
  first | exact @_root_.GlobalTheory.KerConjMean.archimedean_top_term_kernel_conj_mean | exact _root_.GlobalTheory.KerConjMean.archimedean_top_term_kernel_conj_mean | (intros; apply _root_.GlobalTheory.KerConjMean.archimedean_top_term_kernel_conj_mean <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeDictionaryOfLocalBounds

section

@[expose] public section

section
open GlobalTheory.SumSize GlobalTheory.RowClaim
namespace GlobalTheory.SumSize
theorem sum_size_dictionary_of_local_bounds (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) : DictK := by
  obtain ⟨CF0, h⟩ := _root_.GlobalTheory.T.twisted_dictionary_correspondence hP hI
  refine ⟨CF0, fun CF hCF => ⟨0, fun ε C _ => ?_⟩⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  exact ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt _ =>
    hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hIs hAt⟩
end GlobalTheory.SumSize
end

section
open GlobalTheory.SumSize GlobalTheory.RowClaim

theorem _root_.GlobalTheory.T.sum_size_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → DictK := by
  first | exact @_root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds | exact _root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds | (intros; apply _root_.GlobalTheory.SumSize.sum_size_dictionary_of_local_bounds <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TestVectorValueFactorization

section

@[expose] public section

section
namespace TestFunctionNorms
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.CoefModel
open Formalism.UG
open scoped ComplexOrder
namespace GlobalTheory.CompanionTheory.TestVal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section Lat
variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}
end Lat
section Cast
variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}
end Cast
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
theorem test_value_psi_finite_infinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPsiK ∧ InfPsiK := by
  intro _
  constructor
  · refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
    intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ w c u hu x
    exact pullback_fin_relation _ _ w c u hu x
  · refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, ?_⟩⟩⟩
    intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ σ c u x
    exact inf_aux _ _ σ c u x
end GlobalTheory.CompanionTheory.TestVal
end
end
end TestFunctionNorms
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.test_vector_value_factorization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → FinPsiK ∧ InfPsiK := by
  first | exact @_root_.TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.test_value_psi_finite_infinite | exact _root_.TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.test_value_psi_finite_infinite | (intros; apply _root_.TestFunctionNorms.GlobalTheory.CompanionTheory.TestVal.test_value_psi_finite_infinite <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedLocalFactorAwayFromLevel

section

@[expose] public section

section
namespace TwistAwayFromPlace
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.DivisionValues (vw lw)
open GlobalTheory.SumSize
namespace GlobalTheory.CompanionTheory.Twist
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Host in
theorem twist_trivial_away_from_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → AwayK := by
  intro _
  refine ⟨0, fun CF _ => ⟨0, fun ε C _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ w PP hP => ?_⟩⟩⟩
  have hr : ¬ (R.xiH (R.mu w)).UnrAt PP := (s.core.lev.Q_ram (R.mu w) PP).2 (Or.inl hP)
  by_cases hw : w ∈ R.twPl
  · obtain ⟨ψ, Q, hψ, e⟩ := s.mu_on w hw
    have e' : R.xiH (R.mu w) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    by_cases hd : (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt PP
    · refine Or.inr fun l hl h1 h2 => hr fun x hx => ?_
      have hp : Formalism.EigenvalueLevelCeiling.plc w = l := by
        exact ((Nat.prime_dvd_prime_iff_eq (Formalism.EigenvalueLevelCeiling.plc_prime w) hl).1
          ((ringChar.spec _ l).1 (by simpa using Ideal.Quotient.eq_zero_iff_mem.2 h2)))
      have a1 := hd x hx
      have a2 := hψ.atl PP (hp ▸ h1) x
      rw [e']
      change (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc PP x * ψ.loc PP x = 1
      rw [a1, a2, mul_one]
    · refine Or.inl (ch.G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_)))
      have key : ∀ p : ℕ, OverP D.host p PP → (p : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := fun p hp => by
        change algebraMap _ (𝓞 D.host.E) (p : 𝓞 D.host.F) ∈ PP.asIdeal
        rwa [map_natCast]
      unfold CharFrame.delAt at hd
      split_ifs at hd
      · exact Or.inr (Or.inr (Or.inr (key _ (by by_contra h; exact hd (R.C.isDel'.unr PP h)))))
      · exact Or.inr (Or.inr (Or.inl (key _ (by by_contra h; exact hd (R.C.isDel.unr PP h)))))
  · have e : R.mu w = A.μ0 := s.mu_off w hw
    refine absurd (fun x _ => ?_) hr
    rw [e, show R.xiH A.μ0 = 1 from s.core.lev.xi_base]
    rfl
end GlobalTheory.CompanionTheory.Twist
end
end
end TwistAwayFromPlace
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
theorem _root_.GlobalTheory.Adopt.twisted_local_factor_away_from_level : _root_.GlobalTheory.FunPr.ThetaLocalInputs → AwayK := by
  first | exact @_root_.TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.twist_trivial_away_from_level | exact _root_.TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.twist_trivial_away_from_level | (intros; apply _root_.TwistAwayFromPlace.GlobalTheory.CompanionTheory.Twist.twist_trivial_away_from_level <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SumSizeFiniteAwayArchimedeanCombined

section

@[expose] public section

section
namespace GlobalTheory.SumSize.Join
theorem sum_size_finite_away_archimedean_combined : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SumSize.FinK ∧ GlobalTheory.SumSize.AwayK ∧ GlobalTheory.SumSize.InfK := by
  intro P
  have hInp : ∀ D, GlobalTheory.NormSum.Inp D := GlobalTheory.T.cmThetaNormBoundHypotheses_satisfied
  have hOK : GlobalTheory.RowClaim.SumOKK := _root_.GlobalTheory.T.sumOKK_of_theta_local_inputs P
  have hDep : GlobalTheory.SumSize.DepthK := _root_.GlobalTheory.T.depthK_of_sumOKK P hOK
  have hDict : GlobalTheory.SumSize.DictK := _root_.GlobalTheory.T.sum_size_dictionary P hInp
  have hScal := _root_.GlobalTheory.T.finite_and_infinite_scalar_bounds P
  have hForm := _root_.GlobalTheory.T.form_value_finite_infinite_factorization P
  have hPair := _root_.GlobalTheory.T.field_pair_comparison P
  have hPsi := _root_.GlobalTheory.Adopt.test_vector_value_factorization P
  have hTopF := _root_.GlobalTheory.T.sum_size_finite_top_term_integral P hInp hDict hDep
  have hRowF := _root_.GlobalTheory.T.sum_size_bound_finite_places P hInp hDict hDep
  have hTopI := _root_.GlobalTheory.T.kernel_conjugation_mean_archimedean_top_term P hInp hDict hDep
  have hRowI := _root_.GlobalTheory.T.sum_size_bound_opposite_conjugation P hInp hDict hDep
  refine ⟨?_, _root_.GlobalTheory.Adopt.twisted_local_factor_away_from_level P, ?_⟩
  · exact GlobalTheory.Adopt.finiteSumDenominatorBound_of_factor_claims hOK hDep hScal.1 (_root_.GlobalTheory.Adopt.finCoefK_of_theta_inputs P) (_root_.GlobalTheory.T.finDatK_of_theta_inputs P) (_root_.GlobalTheory.T.gamma_factor_loss_at_finite_places P)
      hTopF hRowF hPair.1 hPsi.1 hForm.1
  · exact GlobalTheory.T.archimedeanSumSizeBound_largeData_from_factors hOK hDep hScal.2 (_root_.GlobalTheory.T.sum_size_archimedean_tensor_bound P) (_root_.GlobalTheory.T.sum_count_bound_archimedean P hDep) (_root_.GlobalTheory.T.class_count_bound_archimedean P)
      hTopI hRowI hPair.2 hPsi.2 hForm.2
end GlobalTheory.SumSize.Join
end

section

theorem _root_.GlobalTheory.T.sum_size_bound_all_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SumSize.FinK ∧ GlobalTheory.SumSize.AwayK ∧ GlobalTheory.SumSize.InfK := by
  first | exact @_root_.GlobalTheory.SumSize.Join.sum_size_finite_away_archimedean_combined | exact _root_.GlobalTheory.SumSize.Join.sum_size_finite_away_archimedean_combined | (intros; apply _root_.GlobalTheory.SumSize.Join.sum_size_finite_away_archimedean_combined <;> assumption)
end
end
end
