module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverageStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAndHasSumKAvg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStabEmpty
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimStableSpaceMaxCompactAverages
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFifth
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteCuspFormAverageApprox
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GEqBase
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteCuspAverageHasKType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KFiniteCuspFormAverageApprox
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsSmoothAutomorphicFunctionCompactFamilyAverage
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgTypeOtherPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodParOfSigOK
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AvgOverMaximalCompactWeightedSupNormBound

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFinCuspApprox

open MeasureTheory Matrix Formalism.REAL GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate

theorem avgN_weighted_bound : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau)
    (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ a : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (f : GA D N.V → ℂ) (B : ℝ), (∀ g, ‖f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ B) →
        ∀ g, ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ C * B := by
  intro D θ hθ N τ e he a
  set P := N.M.fr τ with hPdef
  have hU : ∀ k : KG (N.M.ε τ), P⁻¹ * toMK k * P ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := fun k =>
    GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ) (N.M.fr_gram τ) k
  have hκ : Continuous fun k : KG (N.M.ε τ) => P⁻¹ * toMK k * P :=
    (continuous_const.matrix_mul (GlobalTheory.TypeSum.continuous_toMK _)).matrix_mul continuous_const
  have hA : Continuous fun k : KG (N.M.ε τ) => atTau θ N.V τ (P⁻¹ * toMK k * P) :=
    (continuousOn_atTau hθ N.V τ).comp_continuous hκ hU
  obtain ⟨H, hH⟩ := isCompact_univ.exists_bound_of_continuousOn ((continuous_height N.V).comp hA).continuousOn
  have hHk : ∀ k, height N.V (atTau θ N.V τ (P⁻¹ * toMK k * P)) ≤ |H| := fun k => by
    have h := hH k (Set.mem_univ k)
    simp only [Function.comp_apply, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans (h.trans (le_abs_self _))
  have hne : Continuous fun k => ‖e k‖ := he.norm
  refine ⟨(∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * |H| ^ a,
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (pow_nonneg (abs_nonneg _) _), fun f B hf g => ?_⟩
  have hq := quotHeight_pos N.V g
  have hqa : 0 < quotHeight N.V g ^ a := pow_pos hq a
  have hpt : ∀ k, ‖e k * f (g * atTau θ N.V τ (P⁻¹ * toMK k * P))‖ ≤
      ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a) := by
    intro k
    set A := atTau θ N.V τ (P⁻¹ * toMK k * P)
    have h1 : quotHeight N.V g ≤ quotHeight N.V (g * A) * |H| := by
      have h := quotHeight_mul_le N.V (g * A) A⁻¹
      rw [mul_inv_cancel_right, height_inv] at h
      exact h.trans (mul_le_mul_of_nonneg_left (hHk k) (quotHeight_pos N.V _).le)
    have h2 : quotHeight N.V g ^ a ≤ quotHeight N.V (g * A) ^ a * |H| ^ a := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hq.le h1 a
    have h3 : ‖f (g * A)‖ * quotHeight N.V g ^ a ≤ B * |H| ^ a :=
      calc ‖f (g * A)‖ * quotHeight N.V g ^ a ≤ ‖f (g * A)‖ * (quotHeight N.V (g * A) ^ a * |H| ^ a) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = (‖f (g * A)‖ * quotHeight N.V (g * A) ^ a) * |H| ^ a := by ring
        _ ≤ B * |H| ^ a := mul_le_mul_of_nonneg_right (hf _) (by positivity)
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [le_div_iff₀ hqa]; exact h3
  have hint : ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ ≤
      ∫ k, ‖e k‖ * (B * |H| ^ a / quotHeight N.V g ^ a) ∂(muK (N.M.ε τ)) :=
    norm_integral_le_of_norm_le (GlobalTheory.ExpansionAverage.integrable_K (hne.mul continuous_const))
      (Filter.Eventually.of_forall hpt)
  rw [integral_mul_const] at hint
  calc ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * quotHeight N.V g ^ a
      ≤ ((∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * (B * |H| ^ a / quotHeight N.V g ^ a)) * quotHeight N.V g ^ a :=
        mul_le_mul_of_nonneg_right hint hqa.le
    _ = (∫ k, ‖e k‖ ∂(muK (N.M.ε τ))) * |H| ^ a * B := by field_simp

end GlobalTheory.KFinCuspApprox

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.AvgOverMaximalCompactWeightedSupNormBoundStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.avgOverMaximalCompact_weighted_supNorm_bound : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), Continuous e → ∀ a : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : GA D N.V → ℂ) (B : ℝ), (∀ g, ‖f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ B) → ∀ g, ‖GlobalTheory.KFinCuspApprox.avgN θ N τ e f g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ C * B := by
  first | exact @GlobalTheory.KFinCuspApprox.avgN_weighted_bound | exact GlobalTheory.KFinCuspApprox.avgN_weighted_bound | (intros; apply GlobalTheory.KFinCuspApprox.avgN_weighted_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimStableSpaceMaxCompactAveragesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_finiteDim_stable_space_maxCompactAverages : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ s : Set D.what₂.Tau, τ ∉ s → ∀ W' : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W' → (∀ f ∈ W', Continuous f) → GlobalTheory.KFinCuspApprox.KStab θ N s W' → ∃ W : Submodule ℂ (GA D N.V → ℂ), FiniteDimensional ℂ W ∧ (∀ f ∈ W, Continuous f) ∧ GlobalTheory.KFinCuspApprox.KStab θ N (insert τ s) W ∧ ∀ f ∈ W', GlobalTheory.KFinCuspApprox.avgN θ N τ e f ∈ W := by
  first | exact @GlobalTheory.KFinAvgSpan.exists_stab_insert | exact GlobalTheory.KFinAvgSpan.exists_stab_insert | (intros; apply GlobalTheory.KFinAvgSpan.exists_stab_insert <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormApproximationSinglePlace

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open MeasureTheory GlobalTheory.Grow GlobalTheory.Size
open scoped ENNReal
namespace GlobalTheory.KFinCuspApprox
theorem kFinite_cusp_approx_at_one_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (τ : D.what₂.Tau) (a : ℕ) (δ : ℝ), 0 < δ → ∃ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e ∧ GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e ∧ ∀ g, ‖φ g - GlobalTheory.KFinCuspApprox.avgN θ N τ e φ g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ δ := by
  intro hP D θ hθ N φ hφ τ a δ hδ
  obtain ⟨hA, hc, -⟩ := id hφ
  obtain ⟨U, hU, hlev⟩ := hA.level
  obtain ⟨d, C, hC⟩ := hP.cuspDecaySobolev D θ hθ N.V U hU 0 a
  have hr := rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hA hc
  have hη : 0 < δ / ((C : ℝ) + 1) := div_pos hδ (by positivity)
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.KAvgApprox.one_place D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) φ hr d _ hη
  have hec : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hav := GlobalTheory.KAvgApprox.avg_rapid D θ hθ N.V τ (N.M.ε τ) (N.M.fr τ) (N.M.fr_unit τ) (N.M.fr_gram τ) e hec φ hr
  set ψ : GA D N.V → ℂ := φ - avgN θ N τ e φ with hψ
  have hψr : RapidDecSm θ N.V ψ := by
    have := hr.add (hav.smul (-1))
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψc : IsCuspFun N.V ψ := by
    have h2 := _root_.GlobalTheory.T.kFinite_cuspForm_average_approx θ hθ hP N τ e hec φ hA hc
    have := GlobalTheory.MultMem.isCuspFun_add hr.toIsAutFun (hav.smul (-1)).toIsAutFun hc (GlobalTheory.MultMem.isCuspFun_smul (-1) h2)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψlev : ∀ k ∈ U, k ∈ GfC N.V → ∀ x, ψ (x * k) = ψ x := by
    intro k hk hk' x
    simp only [hψ, Pi.sub_apply, hlev k hk hk' x]
    congr 1
    show (∫ k', e k' * φ (x * k * _) ∂_) = ∫ k', e k' * φ (x * _) ∂_
    congr 1; funext k'
    rw [mul_assoc, ← Formalism.IndefR.Eqv.Act.comm_inf_fin (Formalism.IndefR.Eqv.Act.atTau_mem θ τ _) hk', ← mul_assoc, hlev k hk hk']
  refine ⟨e, hec, he, fun g => ?_⟩
  have h1 := hC ψ hψr.toIsAutFun hψlev hψr.smooth (GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hψr) hψc
  have h2 : decaySize N.V a ψ ≤ ENNReal.ofReal δ := by
    have h4 : (C : ℝ≥0∞) * growthSob θ N.V d 0 ψ ≤ C * ENNReal.ofReal (δ / ((C : ℝ) + 1)) := by gcongr
    refine h1.trans (h4.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [NNReal.coe_nonneg C]
  have h3 : ENNReal.ofReal (‖ψ g‖ * quotHeight N.V g ^ a) ≤ ENNReal.ofReal δ :=
    (le_iSup (fun x => ENNReal.ofReal (‖ψ x‖ * quotHeight N.V x ^ a)) g).trans h2
  rw [ENNReal.ofReal_le_ofReal_iff hδ.le] at h3
  simpa [hψ] using h3
end GlobalTheory.KFinCuspApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.cuspForm_approximation_single_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (τ : D.what₂.Tau) (a : ℕ) (δ : ℝ), 0 < δ → ∃ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e ∧ GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e ∧ ∀ g, ‖φ g - GlobalTheory.KFinCuspApprox.avgN θ N τ e φ g‖ * GlobalTheory.Grow.quotHeight N.V g ^ a ≤ δ := by
  first | exact @_root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place | exact _root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place | (intros; apply _root_.GlobalTheory.KFinCuspApprox.kFinite_cusp_approx_at_one_place <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KTypePreservedAverageOtherPlace

section

@[expose] public section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.AvgOtherPlace
open Formalism.MainNotions.S Formalism.REAL MeasureTheory Matrix GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom
open GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open scoped TensorProduct
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
section Avg
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}
end Avg
section Closure
variable {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K)
  [IsFiniteMeasure μ] {τ τ' : D.what₂.Tau} {κ : K → Matrix (Fin V.rank) (Fin V.rank) ℂ} {e : K → ℂ}
end Closure
theorem kFinite_average_isTypeAt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK →
    ∀ (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e →
    ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
    IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  intro hPr D θ hθ N hN τ τ' hne e he _ φ hφ
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hU : ∀ k, (N.M.fr τ)⁻¹ * toMK k * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
    fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hκ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := N.M.ε τ) (P := N.M.fr τ)
  have p1 := hPr.discreteSeriesUpqExists
  have p2 := GlobalTheory.Published.discreteSeriesHermitianUnique_iff.1 hPr.discreteSeriesHermitianUnique
  have p3 := hPr.harishChandraModules
  have p4 := hPr.casselmanWallach
  have hT := GlobalTheory.SeriesToClosure.hasTypeAt_of_isTypeAt θ N.V τ' (N.S τ') φ p1 p2 p3 p4 hθ hN
    (GlobalTheory.NodePar.goodPar_of_sigOK N hN τ') hφ.1 (hφ.2.2 τ')
  have hA := GlobalTheory.RealAverage.isAutFunSm_average D θ hθ N.V τ (KG (N.M.ε τ)) (muK (N.M.ε τ)) _ hκ hU e he φ hφ.1
  exact GlobalTheory.T.automorphicForm_uniformLimit_discreteSeries_series θ N.V τ' (N.S τ') _ p1 p2 p3 p4 hθ hN (GlobalTheory.NodePar.goodPar_of_sigOK N hN τ') hA
    (hasTypeAt_avgF (muK (N.M.ε τ)) hθ hne hκ hU he hφ.1.cont hT)
end GlobalTheory.AvgOtherPlace
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.kType_preserved_average_other_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ N : GlobalTheory.Grid.Node D, N.V.SigOK → ∀ (τ τ' : D.what₂.Tau), τ' ≠ τ → ∀ e : Formalism.REAL.KG (N.M.ε τ) → ℂ, Continuous e → GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → ∀ φ : GA D N.V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → IsTypeAt θ N.V τ' (N.S τ') (GlobalTheory.KFinCuspApprox.avgN θ N τ e φ) := by
  first | exact @_root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt | exact _root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt | (intros; apply _root_.GlobalTheory.AvgOtherPlace.kFinite_average_isTypeAt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsKFiniteApproxOfCuspForm

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.KFinCuspApprox
theorem exists_kFinite_approx_of_cusp_form : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ ψ : GA D (G.V i j).V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ ∧ (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) ∧ ∀ g, ‖φ g - ψ g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  intro hP D G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i j hi hj φ hφ a δ hδ
  have hθ : IsInfFam R.θ := hR.inf
  have hS : (G.V i j).V.SigOK := GlobalTheory.ThetaLiftTypeTh.sigOK_vert G hG hi hj
  have hA : ∀ τ (e : Formalism.REAL.KG ((G.V i j).M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun ((G.V i j).M.ε τ) e →
      ∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ →
        GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) (GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ) := by
    intro τ e he hK ψ hψ
    refine ⟨?_, _root_.GlobalTheory.T.kFinite_cuspForm_average_approx R.θ hθ hP (G.V i j) τ e he ψ hψ.1 hψ.2.1, fun τ' => ?_⟩
    · exact GlobalTheory.T.isSmoothAutomorphicFunction_compactFamily_average D R.θ hθ (G.V i j).V τ (Formalism.REAL.KG ((G.V i j).M.ε τ)) (Formalism.REAL.muK ((G.V i j).M.ε τ)) _
        GlobalTheory.SeriesToClosure.continuous_conjK
        (fun k => GlobalTheory.Published.AutFin.conj_mem_UH ((G.V i j).M.fr_unit τ) ((G.V i j).M.fr_gram τ) k) e he ψ hψ.1
    · by_cases h : τ' = τ
      · subst h
        exact _root_.GlobalTheory.T.kFinite_cusp_average_hasKType hP R.θ hθ (G.V i j) hS τ' e he hK ψ hψ
      · exact _root_.GlobalTheory.T.kType_preserved_average_other_place hP R.θ hθ (G.V i j) hS τ τ' h e he hK ψ hψ
  have hlin : ∀ τ (e : Formalism.REAL.KG ((G.V i j).M.ε τ) → ℂ), Continuous e → ∀ f f' : GA D (G.V i j).V → ℂ,
      Continuous f → Continuous f' → ∀ g, GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e f g -
        GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e f' g = GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e (f - f') g := by
    intro τ e he f f' hf hf' g
    have hk : Continuous fun k : Formalism.REAL.KG ((G.V i j).M.ε τ) =>
        atTau R.θ (G.V i j).V τ (((G.V i j).M.fr τ)⁻¹ * Formalism.REAL.toMK k * (G.V i j).M.fr τ) :=
      (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ (G.V i j).V τ).comp_continuous GlobalTheory.SeriesToClosure.continuous_conjK
        fun k => GlobalTheory.Published.AutFin.conj_mem_UH ((G.V i j).M.fr_unit τ) ((G.V i j).M.fr_gram τ) k
    have c1 : Continuous fun k : Formalism.REAL.KG ((G.V i j).M.ε τ) =>
        e k * f (g * atTau R.θ (G.V i j).V τ (((G.V i j).M.fr τ)⁻¹ * Formalism.REAL.toMK k * (G.V i j).M.fr τ)) :=
      he.mul (hf.comp (continuous_const.mul hk))
    have c2 : Continuous fun k : Formalism.REAL.KG ((G.V i j).M.ε τ) =>
        e k * f' (g * atTau R.θ (G.V i j).V τ (((G.V i j).M.fr τ)⁻¹ * Formalism.REAL.toMK k * (G.V i j).M.fr τ)) :=
      he.mul (hf'.comp (continuous_const.mul hk))
    have i1 := GlobalTheory.ExpansionAverage.integrable_K c1
    have i2 := GlobalTheory.ExpansionAverage.integrable_K c2
    simp only [GlobalTheory.KFinCuspApprox.avgN, GlobalTheory.SeriesToClosure.avg, Pi.sub_apply, mul_sub]
    exact (integral_sub i1 i2).symm
  have key : ∀ l : List D.what₂.Tau, l.Nodup → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ δ : ℝ, 0 < δ →
      ∃ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ ∧ ∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ),
        FiniteDimensional ℂ W ∧ ψ ∈ W ∧ (∀ f ∈ W, Continuous f) ∧ GlobalTheory.KFinCuspApprox.KStab R.θ (G.V i j) {τ | τ ∈ l} W ∧
        ∀ g, ‖φ g - ψ g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
    intro l
    induction l with
    | nil =>
      intro _ φ hφ δ hδ
      refine ⟨φ, hφ, Submodule.span ℂ {φ}, inferInstance, Submodule.mem_span_singleton_self φ, fun f hf => ?_,
        by simpa using GlobalTheory.KFinCuspApprox.kStab_empty R.θ (G.V i j) _, fun g => by simpa using hδ.le⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hf
      exact hφ.1.cont.const_smul c
    | cons τ l ih =>
      intro hnd φ hφ δ hδ
      rw [List.nodup_cons] at hnd
      obtain ⟨e, he, hK, happ⟩ := _root_.GlobalTheory.T.cuspForm_approximation_single_place hP R.θ hθ (G.V i j) φ hφ τ a (δ / 2) (by linarith)
      obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.avgOverMaximalCompact_weighted_supNorm_bound R.θ hθ (G.V i j) τ e he a
      obtain ⟨ψ', hψ', W', hW'f, hψW', hW'c, hW's, hb⟩ := ih hnd.2 φ hφ (δ / (2 * (C + 1))) (by positivity)
      obtain ⟨W, hWf, hWc, hWs, hWm⟩ :=
        GlobalTheory.T.exists_finiteDim_stable_space_maxCompactAverages R.θ hθ (G.V i j) τ e hK {τ | τ ∈ l} hnd.1 W' hW'f hW'c hW's
      refine ⟨_, hA τ e he hK ψ' hψ', W, hWf, hWm ψ' hψW', hWc, by simpa [Set.insert_def] using hWs, fun g => ?_⟩
      have h1 := happ g
      have h2 := hC (φ - ψ') _ hb g
      rw [← hlin τ e he φ ψ' hφ.1.cont hψ'.1.cont g] at h2
      have hq : 0 ≤ GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a := pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le a
      have e1 : φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g =
          (φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g) +
            (GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g) := by ring
      have h3 : C * (δ / (2 * (C + 1))) ≤ δ / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      calc ‖φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a
          ≤ (‖φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g‖ +
              ‖GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g‖) *
              GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a := by
            rw [e1]; exact mul_le_mul_of_nonneg_right (norm_add_le _ _) hq
        _ ≤ δ / 2 + δ / 2 := by rw [add_mul]; linarith
        _ = δ := by ring
  obtain ⟨ψ, hψ, W, hWf, hψW, -, hWs, hb⟩ := key Finset.univ.toList (Finset.nodup_toList _) φ hφ δ hδ
  refine ⟨ψ, hψ, ⟨W, hWf, hψW, fun τ g hg hk f hf => hWs τ (Finset.mem_toList.2 (Finset.mem_univ τ)) g hg hk f hf⟩, hb⟩
end GlobalTheory.KFinCuspApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.kFinite_cusp_forms_dense : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ ψ : GA D (G.V i j).V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ ∧ (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) ∧ ∀ g, ‖φ g - ψ g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  first | exact @_root_.GlobalTheory.KFinCuspApprox.exists_kFinite_approx_of_cusp_form | exact _root_.GlobalTheory.KFinCuspApprox.exists_kFinite_approx_of_cusp_form | (intros; apply _root_.GlobalTheory.KFinCuspApprox.exists_kFinite_approx_of_cusp_form <;> assumption)
end
end
end
