module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphicStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectors
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralUnfoldingLeOfTranslateCoverStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRealPlacesMatrixCoefficientProduct
import Mathlib.RingTheory.PiTensorProduct
import Formalism.LocalToGlobal.IndefiniteReal.SelfDualFullLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesUnitaryAbsolutelyConvergentModeratStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesSmoothModerateGrowthDerivStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldTsumAlongSubgroupStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsQuotHeightMulExpInfLe
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.FibreIntegralEqZero

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHaarEqZeroOfFibreIntegralsEqZero

section

@[expose] public section

open MeasureTheory

namespace GlobalTheory

theorem integral_haar_eq_zero_of_fibre_integrals_eq_zero :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ (P Q : Subgroup H), IsClosed (P : Set H) → IsClosed (Q : Set H) → (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) → (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) → (∀ h, h ∈ P → h ∈ Q → h = 1) → ∀ F : H → ℂ, (∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∫ p, F ((p : H) * q) ∂ν = 0) → ∫ h, F h ∂μ = 0 := by
  intro H _ _ _ _ _ _ _ _ μ hμ P Q hP hQ hcomm hgen hdisj F hF
  haveI : LocallyCompactSpace P := hP.locallyCompactSpace
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology (P : Set H)
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology (Q : Set H)
  haveI : BorelSpace P := Subtype.borelSpace (fun x => x ∈ (P : Set H))
  haveI : BorelSpace Q := Subtype.borelSpace (fun x => x ∈ (Q : Set H))
  let m : P × Q →* H :=
    { toFun := fun x => (x.1 : H) * x.2
      map_one' := by simp
      map_mul' := by
        rintro ⟨p, q⟩ ⟨p', q'⟩
        simp only [Prod.mk_mul_mk, Subgroup.coe_mul]
        have h := hcomm p' p'.2 q q.2
        calc (p : H) * p' * (q * q') = p * (p' * q) * q' := by simp only [mul_assoc]
          _ = p * (q * p') * q' := by rw [h]
          _ = p * q * (p' * q') := by simp only [mul_assoc] }
  have hm : ∀ x : P × Q, m x = (x.1 : H) * x.2 := fun _ => rfl
  have hcont : Continuous m :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hsurj : Function.Surjective m := by
    intro h
    obtain ⟨p, hp, q, hq, rfl⟩ := hgen h
    exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  have hinj : Function.Injective m := by
    rw [injective_iff_map_eq_one]
    rintro ⟨p, q⟩ h
    rw [hm] at h
    have h1 : (p : H) = (q : H)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hp1 : (p : H) = 1 := hdisj p p.2 (h1 ▸ Q.inv_mem q.2)
    have hq1 : (q : H) = 1 := by simpa [hp1] using h
    exact Prod.ext (Subtype.ext hp1) (Subtype.ext hq1)
  have hopen : IsOpenMap m := m.isOpenMap_of_sigmaCompact hsurj hcont
  let e : (P × Q) ≃* H := MulEquiv.ofBijective m ⟨hinj, hsurj⟩
  let φ : (P × Q) ≃ₜ H := e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen
  let νP : Measure P := Measure.haar
  let νQ : Measure Q := Measure.haar
  haveI : νP.IsHaarMeasure := inferInstance
  haveI : νQ.IsHaarMeasure := inferInstance
  haveI : (νP.prod νQ).IsHaarMeasure := inferInstance
  haveI : ((νP.prod νQ).map e).IsHaarMeasure :=
    e.isHaarMeasure_map (νP.prod νQ) φ.continuous φ.symm.continuous
  have hμeq := Measure.isMulLeftInvariant_eq_smul μ ((νP.prod νQ).map e)
  have hzero : ∫ h, F h ∂((νP.prod νQ).map e) = 0 := by
    have hemb : MeasurableEmbedding e := φ.measurableEmbedding
    rw [hemb.integral_map]
    by_cases hint : Integrable (fun x => F (e x)) (νP.prod νQ)
    · rw [integral_prod_symm _ hint]
      have : ∀ q : Q, ∫ p : P, F (e (p, q)) ∂νP = 0 := fun q => hF νP inferInstance q q.2
      simp [this]
    · exact integral_undef hint
  rw [hμeq, integral_smul_nnreal_measure, hzero, smul_zero]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralHaarEqZeroOfFibreIntegralsEqZeroStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.integral_haar_eq_zero_of_fibre_integrals_eq_zero_alt : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ (P Q : Subgroup H), IsClosed (P : Set H) → IsClosed (Q : Set H) → (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) → (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) → (∀ h, h ∈ P → h ∈ Q → h = 1) → ∀ F : H → ℂ, (∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∫ p, F ((p : H) * q) ∂ν = 0) → ∫ h, F h ∂μ = 0 := by
  first | exact @GlobalTheory.integral_haar_eq_zero_of_fibre_integrals_eq_zero | exact GlobalTheory.integral_haar_eq_zero_of_fibre_integrals_eq_zero | (intros; apply GlobalTheory.integral_haar_eq_zero_of_fibre_integrals_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunction

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.CoefMeas

theorem measurable_coef : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v a : ∀ τ, M.H τ), Measurable (coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v a) := by
  intro D θ hθ V S M Λ 𝔪 hΛ h𝔪 v a
  classical
  have h1 := GlobalTheory.SepPer.CoefCont.continuous_coefR D θ hθ V S M v a
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    exact Formalism.IndefR.Datum.IsSelfDualC.isFullLattice V Λ hΛ
  have h2 := (congLev_open_compact V hfull h𝔪).1
  unfold coef
  exact Measurable.ite h2.measurableSet h1.measurable measurable_const

end GlobalTheory.SepPer.CoefMeas
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurableLevelIndicatorCoefficientTestFunctionStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.measurable_level_indicator_coefficient_test_function : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v a : ∀ τ, M.H τ), Measurable (coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v a) := by
  first | exact @GlobalTheory.SepPer.CoefMeas.measurable_coef | exact GlobalTheory.SepPer.CoefMeas.measurable_coef | (intros; apply GlobalTheory.SepPer.CoefMeas.measurable_coef <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesPartialSumsBoundedCompact

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

theorem GlobalTheory.PoinAut.partialSum_bdd : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (v : ∀ τ, M.H τ), KDecay M v → Nonempty D.what₂.Tau → ∀ (c : GA D V) (a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (Kc : Set (GA D V)), IsCompact Kc → ∃ B : ℝ, ∀ x ∈ Kc, ∀ s : Finset (GQ V), ∑ γ ∈ s, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * x)‖ ≤ B := by
  intro D θ hθ V S M Λ 𝔪 hΛ v hv _ c a Kc hK
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hKdef
  set N := 2 * V.rank ^ 2 + 1 with hN
  obtain ⟨C₀, A₀, hI⟩ := GlobalTheory.T.poincareSeries_unitary_absolutelyConvergent_moderateGrowth D θ hθ V Λ hΛ c
  obtain ⟨C, hC, hCb⟩ := GlobalTheory.PoinAut.coefR_le_majorant D θ hθ V S M v (fun τ => (a τ : M.H τ)) N
    (fun τ => (hv τ).2 _ (a τ).2)
  obtain ⟨H, hH⟩ := hK.exists_bound_of_continuousOn (GlobalTheory.Grow.continuous_height V).continuousOn
  set P : ℝ := ∏ τ, (1 + hsn (cmp θ τ (1 : GA D V)⁻¹)) ^ N with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg fun τ _ =>
    pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) _
  have hKtop : ∀ y, y ∈ K → y ∈ congLev D.sp.cm V.gram Λ ⊤ := fun y hy => by
    rw [congLev_top]; exact ⟨hy.1, hy.2.1⟩
  refine ⟨C * P * (max C₀ 0 * H ^ A₀), fun x hx s => ?_⟩
  have hterm : ∀ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
      ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖ ≤
        C * P * ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := by
    intro γ hγ
    unfold coef
    rw [if_pos (Finset.mem_filter.1 hγ).2]
    have := hCb (c * (γ : GA D V) * x) 1
    rwa [mul_one] at this
  have hx0 : 0 ≤ height V x := (height_pos V x).le
  have hxH : height V x ≤ H := by
    have := hH x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg hx0] at this
  calc ∑ γ ∈ s, ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖
      = ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          ‖coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * x)‖ := by
        refine (Finset.sum_filter_of_ne fun γ _ h => ?_).symm
        by_contra hn
        exact h (by unfold coef; rw [if_neg hn, norm_zero])
    _ ≤ ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          C * P * ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := Finset.sum_le_sum hterm
    _ = C * P * ∑ γ ∈ s.filter (fun γ : GQ V => Lev.finE V (c * (γ : GA D V) * x) ∈ K),
          ∏ τ, ((1 + hsn (cmp θ τ (c * (γ : GA D V) * x))) ^ N)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ C * P * (C₀ * height V x ^ A₀) :=
        mul_le_mul_of_nonneg_left (hI x _ fun γ hγ => hKtop _ (Finset.mem_filter.1 hγ).2) (mul_nonneg hC hP)
    _ ≤ C * P * (max C₀ 0 * H ^ A₀) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC hP)
        exact mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ hx0 hxH _) (pow_nonneg hx0 _) (le_max_right _ _)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesPartialSumsBoundedCompactStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.poincareSeries_partialSums_bounded_compact : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → ∀ (v : ∀ τ, M.H τ), KDecay M v → Nonempty D.what₂.Tau → ∀ (c : GA D V) (a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M) (Kc : Set (GA D V)), IsCompact Kc → ∃ B : ℝ, ∀ x ∈ Kc, ∀ s : Finset (GQ V), ∑ γ ∈ s, ‖coef θ M (congLev D.sp.cm V.gram Λ 𝔪) v (fun τ => a τ) (c * (γ : GA D V) * x)‖ ≤ B := by
  first | exact @GlobalTheory.PoinAut.partialSum_bdd | exact GlobalTheory.PoinAut.partialSum_bdd | (intros; apply GlobalTheory.PoinAut.partialSum_bdd <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.ExistsMultTEqPoin

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace UpperTheory.Lit.Cusp

theorem poin_isCuspFun : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∀ a : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec M, IsCuspFun V (poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ) := by
  intro D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hT a
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  intro r C hC μ 𝓕 hμ h𝓕 g
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5; haveI := i7
  haveI : LocallyCompactSpace (NI V C) := (GlobalTheory.CuspDecay.Model.isClosed_NI V hC).locallyCompactSpace
  haveI : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI := hμ
  set K := congLev D.sp.cm V.gram Λ 𝔪 with hK
  have hm : Measurable (coef θ M K v fun τ => (a τ : M.H τ)) := GlobalTheory.T.measurable_level_indicator_coefficient_test_function D θ hθ V S M Λ 𝔪 hΛ h𝔪 v _
  set f : GA D V → ℂ := fun y => coef θ M K v (fun τ => (a τ : M.H τ)) (c * y * g) with hf
  have hfm : ∀ γ : GA D V, Measurable fun h : NI V C => f (γ * (NI V C).subtype h) := fun γ =>
    hm.comp ((continuous_const.mul (continuous_const.mul continuous_subtype_val)).mul continuous_const).measurable
  obtain ⟨-, Kc, hKc, hcov⟩ := GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V r C ⟨hC.2.1, hC.2.2⟩
  have hcov' : ∀ h : NI V C, ∃ δ ∈ (GQ V).comap (NI V C).subtype, δ * h ∈ Kc := fun h => by
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
    exact ⟨γ⁻¹, Subgroup.inv_mem _ hγ, by simpa using hk⟩
  obtain ⟨B, hB⟩ := GlobalTheory.T.poincareSeries_partialSums_bounded_compact D θ hθ V S M Λ 𝔪 hΛ v hv hT c a ((fun h : NI V C => (h : GA D V) * g) '' Kc)
    (hKc.image (continuous_subtype_val.mul continuous_const))
  have hpt : ∀ h ∈ Kc, ∑' γ : GQ V, ‖f (γ * (NI V C).subtype h) * 1‖ₑ ≤ ENNReal.ofReal B := by
    intro h hh
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le fun s => ?_
    have e : ∀ γ : GQ V, f (↑γ * (NI V C).subtype h) * 1 =
        coef θ M K v (fun τ => (a τ : M.H τ)) (c * (γ : GA D V) * ((h : GA D V) * g)) := fun γ => by
      simp only [hf, mul_one, Subgroup.coe_subtype, mul_assoc]
    simp only [e, ← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hB _ ⟨h, hh, rfl⟩ s)
  have hfin : (∑' q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫⁻ h, ‖f ((q.out : GQ V) * (NI V C).subtype h) * 1‖ₑ ∂μ) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (GlobalTheory.T.lintegral_unfolding_le_of_translate_cover (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) Kc hcov'
      (fun y => ‖f y * 1‖ₑ) (fun γ => ((hfm γ).mul_const 1).enorm))
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := B)) (hKc.measure_lt_top (μ := μ)).ne) ?_
    calc _ ≤ ∫⁻ _ in Kc, ENNReal.ofReal B ∂μ := setLIntegral_mono measurable_const hpt
      _ = ENNReal.ofReal B * μ Kc := setLIntegral_const _ _
  have hunf := GlobalTheory.T.integrableOn_and_hasSum_tsum_subgroup (GA D V) (NI V C) μ (NI V C).subtype Subtype.val_injective (GQ V) 𝓕 h𝓕 f (fun _ => 1)
    hfm measurable_const (fun _ _ _ => rfl) hfin
  have hzero : ∀ q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V),
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ = 0 := by
    intro q
    obtain ⟨τ⟩ := hT
    obtain ⟨P, Q, hPc, hQc, hcomm, hgen, htriv, hvan⟩ := fibre_integral_eq_zero D θ hθ V S M K v (fun τ => (a τ : M.H τ))
      (fun τ => (hv τ).2 _ (hv τ).1) (fun τ => (hv τ).2 _ (a τ).2) τ r C hC
    have := GlobalTheory.T.integral_haar_eq_zero_of_fibre_integrals_eq_zero_alt (NI V C) μ hμ P Q hPc hQc hcomm hgen htriv
      (fun n => coef θ M K v (fun τ => (a τ : M.H τ)) ((c * (q.out : GQ V)) * (n : GA D V) * g))
      (fun ν hν q' hq' => hvan ν hν q' hq' _ g)
    simpa [hf, mul_assoc] using this
  have hsum0 : HasSum (fun q : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) =>
      ∫ h, f ((q.out : GQ V) * (NI V C).subtype h) * 1 ∂μ) 0 := by
    simpa only [hzero] using (hasSum_zero : HasSum (fun _ : GQ V ⧸ (NI V C).subtype.range.subgroupOf (GQ V) => (0:ℂ)) 0)
  have h0 := hunf.2.unique hsum0
  rw [← h0]
  refine integral_congr_ae (.of_forall fun n => ?_)
  simp only [poin, hf, mul_one, Subgroup.coe_subtype, mul_assoc]

open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension


open Classical in
theorem exists_multT_eq_poin : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∃ y ∈ MultT θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1, ∀ a : M.Vec, (∀ τ, (a τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → y (PiTensorProduct.tprod ℂ a) = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ := by
  intro hHC hCW hRD D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨haut, ⟨T₀, hT₀⟩, hKeq⟩ := GlobalTheory.T.coefficientPoincareSeries_isAutomorphic D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hder := GlobalTheory.T.poincareSeries_smooth_moderateGrowth_deriv hHC D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hcusp := poin_isCuspFun D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨vol⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).1 V
  have hGK : IsGKMap θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1 vol.μ vol.𝓕 T₀ := by
    refine ⟨fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u k hk g => ?_, ?_, ?_⟩
    · rw [hT₀]; exact (haut u).1
    · rw [hT₀]; exact (hder u).1
    · rw [hT₀]; exact hcusp u
    · rw [hT₀]
      have hr := GlobalTheory.Grow.rapidDec_of_unifModGrowth hRD hθ (haut u).1 (hder u).1 (hder u).2.1 (hcusp u)
      exact GlobalTheory.CuspDecay.memLp_of_bounded hr.continuous hr.bounded _ _ vol.haar vol.fund 2
    · rw [hT₀]; exact (hder u).2.1
    · rw [hT₀, (haut u).2.2.2 k hk g]; simp
    · intro τ k hk u w hw
      rw [hT₀, hT₀]
      have e : (fun τ' => ((Function.update u τ w τ' : kFin M τ') : M.H τ')) =
          Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ k (u τ)) := by
        funext τ'
        by_cases h : τ' = τ
        · subst h; simp [hw]
        · simp [Function.update_of_ne h]
      rw [e]
      exact hKeq _ τ k (maxCpt_subset M τ hk)
    · intro τ X hX u w hw
      rw [hT₀, hT₀]
      exact (hder u).2.2 τ X hX w hw
  obtain ⟨T, ⟨hTm, hTe⟩, -⟩ := (GlobalTheory.GKExtensionToSmoothVectors.gkExtension hHC hCW D).1 θ hθ V S M _ 1 vol.μ vol.𝓕 vol.haar vol.fund T₀ hGK
  refine ⟨PiTensorProduct.lift T, ?_, fun a ha => ?_⟩
  · rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span hTm
  · rw [PiTensorProduct.lift.tprod, hTe a (fun τ => ⟨a τ, ha τ⟩) (fun τ => rfl), hT₀]

end UpperTheory.Lit.Cusp

end
end
end
