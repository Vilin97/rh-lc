module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensTInner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationIntertwinesRealGroup
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
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationLevelProjectorFixedStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationMultilinearNormSqStatement
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesTestDataLargeGapsIntegrableStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.Normed.Operator.Extend
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerMapEqConstMulProdInnerStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNormStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjTranslatedRowEvaluationIntertwinesRealGroupStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.conjTranslatedRowEvaluation_intertwines_realGroup : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ S ∈ EP R F, ∀ (g : X.B.I.Ginf) (y : ∀ τ, ↥(GlobalTheory.RowEvalHH.Wsub R X c τ)), ∃ y' : ∀ τ, ↥(GlobalTheory.RowEvalHH.Wsub R X c τ), GlobalTheory.RowEvalHH.tensT X (fun τ => (y' τ : X.B.H (X.pl.symm τ))) = X.B.σs g (GlobalTheory.RowEvalHH.tensT X (fun τ => (y τ : X.B.H (X.pl.symm τ)))) ∧ GlobalTheory.RowEvalHH.evF R X h t c S y' = X.B.R (g, 1) (GlobalTheory.RowEvalHH.evF R X h t c S y) := by
  first | exact @GlobalTheory.RowEvalHH.evF_equiv | exact GlobalTheory.RowEvalHH.evF_equiv | (intros; apply GlobalTheory.RowEvalHH.evF_equiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseSpanTensorOfDenseSubspaces

section

@[expose] public section

open scoped InnerProductSpace
open Filter Topology

namespace GlobalTheory

theorem dense_span_tensor_of_dense_subspaces {ι : Type} [Fintype ι] {H : ι → Type}
    [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type}
    [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (u : (∀ i, H i) → Hs)
    (W : ∀ i, Submodule ℂ (H i)) (hu : ∀ x y, ⟪u x, u y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range u) : Set Hs))
    (hW : ∀ i, Dense (W i : Set (H i))) :
    Dense (Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i)))) :
      Set Hs) := by
  have hnorm : ∀ x y, ‖u y - u x‖ = Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
      - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ)) := by
    intro x y
    rw [← hu, ← hu, ← hu, inner_self_eq_norm_sq, inner_self_eq_norm_sq, ← norm_sub_sq,
      Real.sqrt_sq (norm_nonneg _)]
  have hcont : Continuous u := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hc : Continuous (fun y : (∀ i, H i) => Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
        - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ))) := by
      fun_prop
    have key : Tendsto (fun y => ‖u y - u x‖) (𝓝 x) (𝓝 ‖u x - u x‖) := by
      have e : (fun y => ‖u y - u x‖) = fun y => Real.sqrt (RCLike.re (∏ i, ⟪y i, y i⟫_ℂ)
          - 2 * RCLike.re (∏ i, ⟪y i, x i⟫_ℂ) + RCLike.re (∏ i, ⟪x i, x i⟫_ℂ)) :=
        funext fun y => hnorm x y
      rw [e, hnorm x x]
      exact hc.tendsto x
    simpa using key
  set S := Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i))))
    with hS
  have hpi : Dense (Set.pi Set.univ (fun i => (W i : Set (H i)))) :=
    dense_pi Set.univ (fun i _ => hW i)
  have hsub : Set.range u ⊆ closure (S : Set Hs) := by
    rintro _ ⟨x, rfl⟩
    refine map_mem_closure hcont (hpi x) ?_
    intro y hy
    apply Submodule.subset_span
    exact ⟨fun i => ⟨y i, hy i (Set.mem_univ i)⟩, rfl⟩
  have hle : Submodule.span ℂ (Set.range u) ≤ S.topologicalClosure := by
    rw [Submodule.span_le, Submodule.topologicalClosure_coe]
    exact hsub
  have h2 : Dense (S.topologicalClosure : Set Hs) := hd.mono hle
  rwa [Submodule.topologicalClosure_coe, dense_closure] at h2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DenseSpanTensorOfDenseSubspacesStatement

section

@[expose] public section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.dense_span_tensor_of_dense_subspaces' : ∀ {ι : Type} [Fintype ι] {H : ι → Type} [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace ℂ (H i)] {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] (u : (∀ i, H i) → Hs) (W : ∀ i, Submodule ℂ (H i)), (∀ x y, ⟪u x, u y⟫_ℂ = ∏ i, ⟪x i, y i⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → (∀ i, Dense (W i : Set (H i))) → Dense (Submodule.span ℂ (Set.range (fun x : (∀ i, W i) => u (fun i => (x i : H i)))) : Set Hs) := by
  first | exact @GlobalTheory.dense_span_tensor_of_dense_subspaces | exact GlobalTheory.dense_span_tensor_of_dense_subspaces | (intros; apply GlobalTheory.dense_span_tensor_of_dense_subspaces <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmOfGramEqSmul

section

@[expose] public section

open scoped InnerProductSpace

namespace GlobalTheory

theorem exists_clm_of_gram_eq_smul {α Hs E : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : α → Hs) (f : α → E)
    (K : ℝ) (hK : ∀ a b, ⟪f a, f b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ)
    (hd : Dense (Submodule.span ℂ (Set.range u) : Set Hs)) :
    ∃ A : Hs →L[ℂ] E, ∀ a, A (u a) = f a := by
  classical
  let Φ : (α →₀ ℂ) →ₗ[ℂ] Hs := Finsupp.linearCombination ℂ u
  let Ψ : (α →₀ ℂ) →ₗ[ℂ] E := Finsupp.linearCombination ℂ f
  have hinner : ∀ z w : α →₀ ℂ, ⟪Ψ z, Ψ w⟫_ℂ = (K : ℂ) * ⟪Φ z, Φ w⟫_ℂ := by
    intro z w
    induction z using Finsupp.induction_linear with
    | zero => simp
    | add z₁ z₂ h₁ h₂ => simp only [map_add (f := _), inner_add_left, h₁, h₂]; ring
    | single a c =>
      induction w using Finsupp.induction_linear with
      | zero => simp
      | add w₁ w₂ h₁ h₂ => simp only [map_add (f := _), inner_add_right, h₁, h₂]; ring
      | single b d =>
        simp only [Φ, Ψ, Finsupp.linearCombination_single, inner_smul_left, inner_smul_right, hK]
        ring
  have hnorm : ∀ z, ‖Ψ z‖ ^ 2 = K * ‖Φ z‖ ^ 2 := by
    intro z
    have h := hinner z z
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    apply Complex.ofReal_injective
    push_cast
    simpa using h
  have hbound : ∀ z, ‖Ψ z‖ ≤ Real.sqrt (max K 0) * ‖Φ z‖ := by
    intro z
    have hs : Real.sqrt (max K 0) ^ 2 = max K 0 := Real.sq_sqrt (le_max_right _ _)
    have h0 : 0 ≤ Real.sqrt (max K 0) := Real.sqrt_nonneg _
    have h1 : ‖Ψ z‖ ^ 2 ≤ (Real.sqrt (max K 0) * ‖Φ z‖) ^ 2 := by
      rw [mul_pow, hs, hnorm]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _)) two_ne_zero).1 h1
  have hdense : DenseRange Φ := by
    have hr : Set.range Φ = (Submodule.span ℂ (Set.range u) : Set Hs) := by
      rw [← LinearMap.coe_range]
      exact congrArg _ (Finsupp.range_linearCombination ℂ)
    rw [DenseRange, hr]
    exact hd
  refine ⟨Ψ.extendOfNorm Φ, fun a => ?_⟩
  have h := LinearMap.extendOfNorm_eq hdense ⟨_, hbound⟩ (Finsupp.single a 1)
  simpa [Φ, Ψ, Finsupp.linearCombination_single] using h
end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmOfGramEqSmulStatement

section

@[expose] public section

open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_clm_of_gram_eq_smul' : ∀ {α Hs E : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : α → Hs) (f : α → E) (K : ℝ), (∀ a b, ⟪f a, f b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → ∃ A : Hs →L[ℂ] E, ∀ a, A (u a) = f a := by
  first | exact @GlobalTheory.exists_clm_of_gram_eq_smul | exact GlobalTheory.exists_clm_of_gram_eq_smul | (intros; apply GlobalTheory.exists_clm_of_gram_eq_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEvaluationTranslateMemRowSpace

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.RowEvalHH in
theorem GlobalTheory.RowEvalHH.conj_eval_mem_HH : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ EP R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → star φ ∈ HHX X := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod hHost hιE t c v₀ ht hLM hc hv S hS φ hφ
  classical
  obtain ⟨hDS, -, -, -, -, hloc⟩ := GlobalTheory.T.discreteSeries_testData_large_gaps_integrable X hHost
  obtain ⟨hinj, hran⟩ := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec
    X.B.e X.B.Re X.B.Re_spec X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1) (fun v => (X.ds v).2.2.2.1)
    (fun v => (hDS v).2.2.2) (fun v => (X.low v).1) hloc X.Rph X.Rph_spec X.B.Hs X.B.σs X.B.tens X.B.tens_spec

  let u : (∀ τ, ↥(Wsub R X c τ)) → X.B.Hs := fun y => tensT X (fun τ => (y τ : X.B.H (X.pl.symm τ)))
  obtain ⟨f, K, hfe, hfn⟩ := GlobalTheory.T.conjTranslatedRowEvaluation_multilinear_norm_sq R F X h hLev hGrp hMod t c ht S hS
  have hfi := GlobalTheory.T.inner_multilinearMap_eq_mul_prod_inner f K hfn
  have hgram : ∀ a b, ⟪evF R X h t c S a, evF R X h t c S b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ := by
    intro a b
    rw [← hfe a, ← hfe b, hfi a b, tensT_inner]
    rfl
  have hdense : Dense (Submodule.span ℂ (Set.range u) : Set X.B.Hs) :=
    GlobalTheory.T.dense_span_tensor_of_dense_subspaces' (tensT X) (Wsub R X c) (tensT_inner X) (tensT_dense X) (Wsub_dense R X c)
  obtain ⟨Aop, hA⟩ := GlobalTheory.T.exists_clm_of_gram_eq_smul' u (evF R X h t c S) K hgram hdense
  have hHom : Aop ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    intro g
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨y, rfl⟩
    obtain ⟨y', hy1, hy2⟩ := GlobalTheory.T.conjTranslatedRowEvaluation_intertwines_realGroup R F X h hLev hGrp hMod hHost hιE t c ht hc S hS g y
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    change Aop (X.B.σs g (u y)) = X.B.R (g, 1) (Aop (u y))
    rw [← hy1]
    change Aop (u y') = _
    rw [hA, hA, hy2]
  have hRe : X.B.Re.comp Aop = Aop := by
    apply ContinuousLinearMap.ext_on hdense
    rintro _ ⟨y, rfl⟩
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [hA]
    exact GlobalTheory.T.conj_translatedRowEvaluation_levelProjector_fixed R F X h hLev hGrp hMod hHost hιE t c ht hLM S hS y
  have heHom : Aop ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re :=
    Submodule.mem_map.2 ⟨Aop, hHom, hRe⟩

  let y₀ : ∀ τ, ↥(Wsub R X c τ) := fun τ => ⟨c τ (v₀ τ), Submodule.mem_map_of_mem (v₀ τ).2⟩
  have hu0 : u y₀ = X.B.tens X.B.w := by
    have : (fun τ => ((y₀ τ : ↥(Wsub R X c τ)) : X.B.H (X.pl.symm τ))) = fun τ => X.B.w (X.pl.symm τ) := by
      funext τ
      exact hv τ
    change tensT X _ = _
    rw [this, tensT_w]
  have hvec : vecOf R X c y₀ = v₀ := by
    funext τ
    apply Subtype.ext
    exact (c τ).symm_apply_apply (v₀ τ)
  obtain ⟨c', -, hnorm⟩ := GlobalTheory.T.translatedRowEvaluation_squareIntegrable_norm R F X h hLev hGrp hMod t ht
  have hunit : ∀ τ, ‖((v₀ τ : (MP R).H τ))‖ = 1 := by
    intro τ
    rw [← (c τ).norm_map, hv τ]
    exact (X.low _).1
  obtain ⟨hmem, -, -⟩ := hnorm v₀ hunit S hS
  have hval : Aop (X.B.tens X.B.w) = star φ := by
    rw [← hu0, hA]
    delta evF
    rw [hvec, dite_eq_left hmem]
    congr 1
    exact (Lp.ext (hφ.trans hmem.coeFn_toLp.symm)).symm
  have hmemHH : star φ ∈ Formalism.L2.SG.RowsDef.HH X.B.I X.B.μf X.B.fund X.B.Re X.Rph := by
    rw [← hran]
    exact ⟨⟨Aop, heHom⟩, hval⟩
  exact hmemHH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjRowEvaluationTranslateMemRowSpaceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.conj_rowEvaluation_translate_mem_rowSpace : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (v₀ : (MP R).Vec), t ∈ GfC (Yc D 0) → LevelMatchA R F X h t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → (∀ τ, c τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ)) → ∀ S ∈ EP R F, ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → star φ ∈ HHX X := by
  exact @GlobalTheory.RowEvalHH.conj_eval_mem_HH
end
end
