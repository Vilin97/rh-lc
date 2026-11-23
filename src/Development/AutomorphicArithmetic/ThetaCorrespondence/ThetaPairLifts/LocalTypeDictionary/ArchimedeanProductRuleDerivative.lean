module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalRingCardinality.DataHost
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanWeilRepresentationContinuous
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SchwartzFunctionSlopeEstimate

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzTendstoOperatorCurveOfPointwise

section

@[expose] public section

open Filter Topology
open scoped Uniformity

namespace GlobalTheory

theorem schwartz_tendsto_apply_of_tendsto_pointwise :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ f, Filter.Tendsto (fun t => S t f) (nhdsWithin 0 {0}ᶜ) (nhds f)) →
    ∀ (g : ℝ → SchwartzMap V ℂ) (g₀ : SchwartzMap V ℂ), Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds g₀) →
      Filter.Tendsto (fun t => S t (g t)) (nhdsWithin 0 {0}ᶜ) (nhds g₀) := by
  intro V _ _ _ S hS g g₀ hg
  haveI : BarrelledSpace ℂ (SchwartzMap V ℂ) := schwartzMap_barrelledSpace V
  rw [tendsto_iff_seq_tendsto]
  intro u hu
  have hq := schwartz_withSeminorms ℂ V ℂ
  have hUE : UniformEquicontinuous ((↑) ∘ fun n => S (u n)) := by
    refine hq.banach_steinhaus (𝓕 := fun n => S (u n)) ?_
    intro k f
    exact ((hq.continuous_seminorm k).tendsto f).comp ((hS f).comp hu) |>.bddAbove_range
  have hE := hUE.equicontinuous g₀
  have h1 : Tendsto (fun n => (S (u n) g₀, S (u n) (g (u n)))) atTop (𝓤 (SchwartzMap V ℂ)) := by
    intro U hU
    have := (hg.comp hu).eventually (hE U hU)
    rw [Filter.mem_map]
    exact this.mono fun n hn => hn n
  exact ((hS g₀).comp hu).congr_uniformity h1

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzTendstoOperatorCurveOfPointwiseStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.schwartz_tendsto_operatorCurve_of_pointwise : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ f, Filter.Tendsto (fun t => S t f) (nhdsWithin 0 {0}ᶜ) (nhds f)) →
    ∀ (g : ℝ → SchwartzMap V ℂ) (g₀ : SchwartzMap V ℂ), Filter.Tendsto g (nhdsWithin 0 {0}ᶜ) (nhds g₀) →
      Filter.Tendsto (fun t => S t (g t)) (nhdsWithin 0 {0}ᶜ) (nhds g₀) := by
  first | exact @GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise | exact GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise | (intros; apply GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompositionLines

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchProdRule

open Filter Topology

theorem slope_prod {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∀ (k : ℕ) (T : Fin k → ℝ → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ) (Q : Fin k → SchwartzMap V ℂ → SchwartzMap V ℂ),
    (∀ i t, Continuous (T i t)) → (∀ i f, T i 0 f = f) →
    (∀ i f, Tendsto (fun t : ℝ => t⁻¹ • (T i t f - f)) (𝓝[≠] 0) (𝓝 (Q i f))) →
    ∀ f, Tendsto (fun t : ℝ => t⁻¹ • ((List.ofFn fun i => T i t).prod f - f)) (𝓝[≠] 0) (𝓝 (∑ i, Q i f)) := by
  intro k
  induction k with
  | zero =>
    intro T Q _ _ _ f
    simpa using (tendsto_const_nhds (x := (0 : SchwartzMap V ℂ)) (f := 𝓝[≠] (0 : ℝ)))
  | succ k ih =>
    intro T Q hc h0 hQ f
    have ht := ih (fun i => T i.succ) (fun i => Q i.succ) (fun i => hc i.succ) (fun i => h0 i.succ)
      (fun i => hQ i.succ) f
    let S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ := fun t => ⟨T 0 t, hc 0 t⟩
    have hS1 : ∀ g, Tendsto (fun t => S t g) (𝓝[≠] 0) (𝓝 g) := by
      intro g
      have h2 : Tendsto (fun t : ℝ => t • (t⁻¹ • (T 0 t g - g)) + g) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • Q 0 g + g)) :=
        ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul (hQ 0 g)).add_const g
      rw [zero_smul, zero_add] at h2
      refine h2.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]
      rfl
    have h1 := GlobalTheory.T.schwartz_tendsto_operatorCurve_of_pointwise V S hS1 _ _ ht
    have h3 := h1.add (hQ 0 f)
    rw [Fin.sum_univ_succ, add_comm (Q 0 f)]
    refine h3.congr fun t => ?_
    have e : (List.ofFn fun i => T i t).prod f = T 0 t ((List.ofFn fun i : Fin k => T i.succ t).prod f) := by
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    rw [e]
    show T 0 t (t⁻¹ • ((List.ofFn fun i : Fin k => T i.succ t).prod f - f)) + _ = _
    rw [LinearMap.map_smul_of_tower, map_sub, ← smul_add, sub_add_sub_cancel]


end GlobalTheory.ArchProdRule
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ArchimedeanProductRuleDerivative

section

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.ArchProdRule
open Filter Topology
open scoped Classical in
theorem archimedean_hasDerivAt_prod : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)),
    (∀ i, γ i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W) →
    ∀ T : Fin k → ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ i t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ i (Multiplicative.ofAdd t))) ⇑f ⇑(T i t f)) →
    (∀ i s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i (s + t) f = T i s (T i t f)) →
    (∀ i (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i 0 f = f) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (y : Fin n × Fin d → mixedEmbedding.mixedSpace F) (c : Fin k → ℂ),
    (∀ i, HasDerivAt (fun t : ℝ => T i t f y) (c i) 0) →
    HasDerivAt (fun t : ℝ => (List.ofFn fun i => T i t).prod f y) (∑ i, c i) 0 := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW k γ hγ T hT hadd h0 f y c hc
  have hQ : ∀ i g, ∃ q, Tendsto (fun t : ℝ => t⁻¹ • (T i t g - g)) (𝓝[≠] 0) (𝓝 q) := fun i g =>
    _root_.GlobalTheory.T.schwartz_function_slope_estimate hP M ψ χX χW om hCM hψ hW (γ i) (hγ i) (T i) (hT i) (hadd i) (h0 i) g
  choose Q hQ using hQ
  have hcont : ∀ i t, Continuous (T i t) := fun i =>
    _root_.GlobalTheory.T.archimedean_weil_representation_continuous hP M ψ χX χW om hCM hψ hW (γ i) (hγ i) (T i) (hT i) (hadd i) (h0 i)
  have hprod := slope_prod k T Q hcont h0 hQ f
  let ev : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →L[ℂ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
  have hev : ∀ (s : ℝ) (g h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), ev (s • (g - h)) = s • (g y - h y) := by
    intro s g h
    rw [ContinuousLinearMap.map_smul_of_tower, map_sub]
    rfl
  have hevq : ∀ g : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d), ev g = g y := fun g => rfl
  have hci : ∀ i, c i = Q i f y := by
    intro i
    have h1 := hasDerivAt_iff_tendsto_slope_zero.1 (hc i)
    have h2 := (ev.continuous.tendsto _).comp (hQ i f)
    rw [hevq] at h2
    simp only [zero_add, h0] at h1
    refine tendsto_nhds_unique h1 (h2.congr fun t => ?_)
    exact hev _ _ _
  have hsum : (∑ i, c i) = ev (∑ i, Q i f) := by

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => (hci i).trans (hevq _).symm
  rw [hasDerivAt_iff_tendsto_slope_zero, hsum]
  have hp0 : (List.ofFn fun i => T i 0).prod = 1 := by
    have e : (fun i => T i 0) = fun _ => (1 : Module.End ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) :=
      funext fun i => LinearMap.ext (h0 i)
    rw [e, List.ofFn_const, List.prod_replicate, one_pow]
  have h1 := (ev.continuous.tendsto _).comp hprod
  refine h1.congr fun t => ?_
  simp only [Function.comp_apply, zero_add, hp0]
  exact hev _ _ _
end GlobalTheory.ArchProdRule
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem _root_.GlobalTheory.T.archimedean_product_rule_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W), IsCMExt F E σ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J)),
    (∀ i, γ i ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W) →
    ∀ T : Fin k → ℝ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
    (∀ i t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (1, γ i (Multiplicative.ofAdd t))) ⇑f ⇑(T i t f)) →
    (∀ i s t (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i (s + t) f = T i s (T i t f)) →
    (∀ i (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), T i 0 f = f) →
    ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (y : Fin n × Fin d → mixedEmbedding.mixedSpace F) (c : Fin k → ℂ),
    (∀ i, HasDerivAt (fun t : ℝ => T i t f y) (c i) 0) →
    HasDerivAt (fun t : ℝ => (List.ofFn fun i => T i t).prod f y) (∑ i, c i) 0 := by
  first | exact @_root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod | exact _root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod | (intros; apply _root_.GlobalTheory.ArchProdRule.archimedean_hasDerivAt_prod <;> assumption)
end
end
end
