module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenvalueAdjointFactsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelActionFormulaStatement
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowLeftInvariantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowMatrixStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowSupportStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateSobolevStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PhiResolventIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RapidFactorizationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveIntegralIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveRepresentationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveUniquenessStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointSmooth

section

@[expose] public section

noncomputable section

open scoped ContDiff InnerProductSpace

namespace GlobalTheory.CompanionTheory.KerFc

def innerSmulRightR {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (e : V) :
    V →L[ℝ] (V →L[ℂ] V) :=
  LinearMap.mkContinuous
    { toFun := fun x => (innerSL ℂ x).smulRight e
      map_add' := fun x y => by
        ext w
        simp [inner_add_left, add_smul]
      map_smul' := fun r x => by
        ext w
        change ⟪r • x, w⟫_ℂ • e = r • (⟪x, w⟫_ℂ • e)
        rw [← Complex.coe_smul r x, inner_smul_left, Complex.conj_ofReal, mul_smul, Complex.coe_smul] }
    ‖e‖
    (fun x => by
      refine (ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_)
      have h1 : ‖⟪x, w⟫_ℂ‖ ≤ ‖x‖ * ‖w‖ := norm_inner_le_norm x w
      simp only [LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, norm_smul]
      calc ‖⟪x, w⟫_ℂ‖ * ‖e‖ ≤ (‖x‖ * ‖w‖) * ‖e‖ := by gcongr
        _ = ‖e‖ * ‖x‖ * ‖w‖ := by ring)

theorem innerSmulRightR_apply {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (e x : V) :
    innerSmulRightR e x = (innerSL ℂ x).smulRight e := rfl

theorem adjoint_eq_sum {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [CompleteSpace V] (B : V →L[ℂ] V) :
    ContinuousLinearMap.adjoint B =
      ∑ i, innerSmulRightR (stdOrthonormalBasis ℂ V i) (B (stdOrthonormalBasis ℂ V i)) := by
  ext w
  rw [ContinuousLinearMap.sum_apply]
  simp only [innerSmulRightR_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  rw [← (stdOrthonormalBasis ℂ V).sum_repr' (ContinuousLinearMap.adjoint B w)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.adjoint_inner_right]

theorem adjSmooth : AdjSmooth := by
  intro W V _ _ _ _ _ _ A s hA
  have hEq : (fun y => ContinuousLinearMap.adjoint (A y)) = fun y =>
      ∑ i, innerSmulRightR (stdOrthonormalBasis ℂ V i) (A y (stdOrthonormalBasis ℂ V i)) := by
    funext y
    exact adjoint_eq_sum (A y)
  rw [hEq]
  refine ContDiffOn.sum fun i _ => ?_
  exact (innerSmulRightR (stdOrthonormalBasis ℂ V i)).contDiff.comp_contDiffOn (hA _)

end GlobalTheory.CompanionTheory.KerFc
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelAdjointSmoothStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.kernel_adjoint_smooth : GlobalTheory.CompanionTheory.KerFc.AdjSmooth := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.adjSmooth | exact GlobalTheory.CompanionTheory.KerFc.adjSmooth | (intros; apply GlobalTheory.CompanionTheory.KerFc.adjSmooth <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowExists

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rowExists_of_factor (hFac : FactorRapid) (hEv : EvAdj) : RowExists := by
  intro n _ _ μ _ E _ Ω T F c hS h hh v
  have hS' := hS
  obtain ⟨hLg, hUn, hRC, hSG, hAE, -, -, hCS, hSO, -, -, -, -, -, hOm, -⟩ := hS'
  obtain ⟨h₁, h₂, r₁, r₂, r₂s, rfl⟩ := hFac h hh
  obtain ⟨κ, hκ, hrow⟩ := hEv n μ E Ω T F c hS h₁ r₁ v
  obtain ⟨C₁, hC₁⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (star h₂) r₂s
  obtain ⟨C₂, hC₂⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm h₂ r₂
  obtain ⟨f, hfS, hfE, hfc, -⟩ := hC₁ κ hκ
  refine ⟨f, hfS, hfE, ?_⟩
  intro φ f' hφS hφE hf'S hf'E hf'
  obtain ⟨φ₂, hφ₂S, hφ₂E, hφ₂c, -⟩ := hC₂ (cls μ φ) (subset_closure ⟨φ, hφS, hφE, rfl⟩)
  have hmul : cls μ f' = F.Φ h₁ (cls μ φ₂) := by
    rw [hf', F.map_mul, hφ₂c]
    rfl
  rw [hfc, F.map_star, ContinuousLinearMap.adjoint_inner_left, ← hφ₂c]
  exact hrow φ₂ f' hφ₂S hφ₂E hf'S hf'E hmul

end GlobalTheory.CompanionTheory.KerFc
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRowExistsStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.kernel_row_exists : GlobalTheory.CompanionTheory.KerFc.FactorRapid → GlobalTheory.CompanionTheory.KerFc.EvAdj → GlobalTheory.CompanionTheory.KerFc.RowExists := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.rowExists_of_factor | exact GlobalTheory.CompanionTheory.KerFc.rowExists_of_factor | (intros; apply GlobalTheory.CompanionTheory.KerFc.rowExists_of_factor <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateCommutes

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def lTrL {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) : Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun y : G n => x * y) (measurePreserving_mul_left μ x)).toContinuousLinearMap

theorem memLp_lTr {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) : MemLp (fun y : G n => lTr x f y.val) 2 μ :=
  hf.comp_measurePreserving (measurePreserving_mul_left μ x)

theorem lTrL_cls {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : G n) {f : Mat n → V}
    (hf : MemLp (fun y : G n => f y.val) 2 μ) : lTrL μ V x (cls μ f) = cls μ (lTr x f) := by
  unfold cls
  rw [dite_eq_left hf, dite_eq_left (memLp_lTr μ x hf)]
  exact Lp.toLp_compMeasurePreserving hf (measurePreserving_mul_left μ x)

theorem ltComm_of_ltSob : LtSob → LtComm := by
  intro hL n _ _ μ _ E _ Ω T F c hS h x f f' hf hf' hff'
  obtain ⟨hLg, hU, hR, -, -, -, -, hCS, -, -, hM, -, -, -, hO, -⟩ := hS
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  have hcomm : lTrL μ E.V x * F.Φ h = F.Φ h * lTrL μ E.V x := by
    refine F.comm _ (fun m => ?_) h
    obtain ⟨f₀, hf₀, hc⟩ := hM m.1 m.2
    have hL₀ := hL n μ E.V hLg hU hR x f₀ hf₀
    have hmem : cls μ (lTr x f₀) ∈ Msob μ E.V := Submodule.subset_span ⟨_, hL₀.1, rfl⟩
    have hm₀ : cls μ f₀ ∈ Msob μ E.V := hc ▸ m.2
    have hm : m = ⟨cls μ f₀, hm₀⟩ := Subtype.ext hc.symm
    have hO₀ : Sob μ (Om f₀) := (hOps n μ E.V hLg hU hR f₀ hf₀).1
    have hf₀m : MemLp (fun y : G n => f₀ y.val) 2 μ := hf₀.2 []
    have hO₀m : MemLp (fun y : G n => Om f₀ y.val) 2 μ := hO₀.2 []
    refine ⟨⟨_, hmem⟩, ?_, ?_⟩
    · change cls μ (lTr x f₀) = lTrL μ E.V x m.1
      rw [← hc, lTrL_cls μ x hf₀m]
    · rw [hO _ hmem hL₀.1, hm, hO _ hm₀ hf₀, lTrL_cls μ x hO₀m]
      exact (hCl n μ E.V hU).2.2.1 _ _ hL₀.2
  have hfm : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []
  have hfm' : MemLp (fun y : G n => f' y.val) 2 μ := hf'.2 []
  rw [← lTrL_cls μ x hfm', hff', ← lTrL_cls μ x hfm]
  exact DFunLike.congr_fun hcomm (cls μ f)

end GlobalTheory.CompanionTheory.KerFc
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftTranslateCommutesStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.left_translate_commutes : GlobalTheory.CompanionTheory.KerFc.LtSob → GlobalTheory.CompanionTheory.KerFc.LtComm := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob | exact GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob | (intros; apply GlobalTheory.CompanionTheory.KerFc.ltComm_of_ltSob <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularity

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem coe_toC0 {f : ℝ → ℂ} (h₁ : Continuous f) (h₂ : Tendsto f (cocompact ℝ) (𝓝 0)) (y : ℝ) : toC0 f y = f y := by
  have : Continuous f ∧ Tendsto f (cocompact ℝ) (𝓝 0) := ⟨h₁, h₂⟩
  simp only [toC0]
  rw [dite_eq_left this]
  rfl

theorem adj_rho {n : ℕ} (E : KMod n) [CompleteSpace E.V] (k : Matrix.unitaryGroup (Fin n) ℂ) :
    ContinuousLinearMap.adjoint (E.ρ k⁻¹) = E.ρ k := by
  have hmul : ∀ v, E.ρ k (E.ρ k⁻¹ v) = v := fun v => by
    have := congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k k⁻¹)
    simpa using this.symm
  have hmul' : ∀ v, E.ρ k⁻¹ (E.ρ k v) = v := fun v => by
    have := congrArg (fun L : E.V →L[ℂ] E.V => L v) (E.ρ.map_mul k⁻¹ k)
    simpa using this.symm
  let I : E.V →ₗᵢ[ℂ] E.V := ⟨(E.ρ k).toLinearMap, fun v => E.iso k v⟩
  ext v
  refine ext_inner_right ℂ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  have := I.inner_map_map v (E.ρ k⁻¹ w)
  have e : ∀ z, I z = E.ρ k z := fun _ => rfl
  rw [e, e, hmul] at this
  exact this.symm

theorem kerCore_of (hFR : RowExists) (hRM : RowMatrix) (hAS : AdjSmooth) (hRL : RowLeft) (hAF : ActFormula)
    (hWR : WaveRep) (hWU : WaveUniq) (hPR : PhiRes) (hWI : WaveInt) (hSR : SupportRow) : KerCore := by
  intro n _ _ μ _ E g T₀ hb hLg hUn hRC hSG hAE hWS hWC hCS hSO hPW
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  obtain ⟨hAbsFC, hAbsCut, hFc, hWv, hCls, hSobOps, hCptSob, hSB, hPres, hConc, hCJ, hFr, hOmF, hIbp, hDD⟩ := id hCS
  obtain ⟨hMrep, Ω, T, hDense, hSym, hEx, hLeft, hOm⟩ :=
    hConc n μ E.V hLg hUn hRC hSG hPres hFr hCls hSobOps hCptSob hOmF hIbp hDD
  obtain ⟨F⟩ := hAbsFC _ _ Ω T hDense hSym hEx hLeft
  obtain ⟨c, hc⟩ := hSB n μ E hLg hUn hRC
  have hStd : Std μ E F c :=
    ⟨hLg, hUn, hRC, hSG, hAE, hWS, hWC, hCS, hSO, hPW, hMrep, hSym, hEx, hLeft, hOm, hc⟩
  have hPW1 := (hPW c g T₀ hb).1
  have hPW2 := (hPW c g T₀ hb).2
  have hC0 : ∀ y, toC0 (hg c g) y = hg c g y := fun y => by
    have := hPW1 0
    simp only [pow_zero, one_mul] at this
    exact coe_toC0 this.1 (by simpa using this.2) y
  have hR : Rapid (toC0 (hg c g)) := fun m =>
    ⟨toC0 (fun y : ℝ => (y : ℂ) ^ m * hg c g y), fun y => by
      rw [coe_toC0 (hPW1 m).1 (hPW1 m).2, hC0]⟩
  obtain ⟨A, hA⟩ := hRM n μ E Ω T F c hStd _ (hFR n μ E Ω T F c hStd _ hR)
  have hWV : ∀ f ∈ CE E, Cpt f → ∀ u, IsWave E u → (∀ x ∈ GLs n, u 0 x = f x) → ∀ f', Sob μ f' → IsSec E f' →
      cls μ f' = F.Φ (toC0 (hg c g)) (cls μ f) → ∀ x ∈ GLs n, ∫ t, (g t : ℂ) • u t x = f' x := by
    intro f hf hcpt u hu h0 f' hs _ hcl x hx
    obtain ⟨N, b, U, hN, hT, hUw, hU0, hUt⟩ := hWR n μ E Ω T F c hStd f hf hcpt
    have huU : ∀ t, u t x = U t x := fun t =>
      hWU hWS hCS hRC n E u U hu hUw (fun y hy => by rw [h0 y hy, hU0 y hy]) t x hx
    have hcl' : cls μ f' = F.Φ (toC0 (fun y => ((((1 + y ^ 2) ^ N)⁻¹ : ℝ) : ℂ) * hg c g y)) b := by
      rw [hPR n μ E Ω T F c hStd g T₀ hb N hN, hcl, ← hT]
      rfl
    have := hWI n μ E Ω T F c hStd g T₀ hb N b U hN hUw hUt f' hs hcl' x hx
    simpa only [huU] using this
  obtain ⟨R, hRsup⟩ := hSR n μ E Ω T F c hStd g T₀ _ hb hR hWV
  have hKdef : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, A (y * k.1) = E.ρ k⁻¹ * A y := by
    intro k y hy
    ext v
    exact (hA v).2.1 y hy k
  have hkG : ∀ k : Matrix.unitaryGroup (Fin n) ℂ, ∀ y ∈ GLs n, k.1 * y ∈ GLs n := by
    intro k y hy
    have hk : (k.1 : Mat n).det ≠ 0 :=
      (Matrix.isUnit_det_of_right_inverse (Matrix.mem_unitaryGroup_iff.1 k.2)).ne_zero
    simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at hy ⊢
    exact mul_ne_zero hk hy
  refine ⟨fun y => ContinuousLinearMap.adjoint (A y), hAS _ _ A _ fun v => (hA v).1.1, ⟨R, ?_⟩, ?_, ?_⟩
  · intro y hy hl
    have : A y = 0 := by
      ext v
      exact hRsup v _ (hA v) y hy hl
    simp [this]
  · intro y hy k₁ k₂
    have e1 : A (k₁.1 * y * k₂.1) = E.ρ k₂⁻¹ * A (k₁.1 * y) := hKdef k₂ _ (hkG k₁ y hy)
    have e2 : A (k₁.1 * y) = A y * E.ρ k₁⁻¹ := by
      ext v
      exact hRL n μ E Ω T F c hStd _ A hR hA k₁ y hy v
    show ContinuousLinearMap.adjoint (A (k₁.1 * y * k₂.1)) = _
    rw [e1, e2]
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.mul_def, adj_rho]
  · intro f hf hcpt u hu h0 x hx
    have hSf : Sob μ f := (hCptSob n μ E.V hLg hRC f hf.1 hcpt).1
    obtain ⟨C, hC⟩ := hSO n μ E Ω T F hLg hUn hRC hSG hAE hCS hOm (toC0 (hg c g)) hR
    obtain ⟨f', hf's, hf'e, hf'c, -⟩ := hC (cls μ f) (subset_closure ⟨f, hSf, hf.2, rfl⟩)
    rw [hAF n μ E Ω T F c hStd _ A hA f hf hcpt f' hf's hf'e hf'c x hx,
      hWV f hf hcpt u hu h0 f' hf's hf'e hf'c x hx]

theorem kerCore : KerCore :=
  have hLC := GlobalTheory.T.left_translate_commutes GlobalTheory.T.left_translate_sobolev
  kerCore_of (GlobalTheory.T.kernel_row_exists GlobalTheory.T.rapid_factorization GlobalTheory.T.eigenvalue_adjoint_facts) GlobalTheory.T.kernel_row_matrix GlobalTheory.T.kernel_adjoint_smooth
    (GlobalTheory.T.kernel_row_left_invariant GlobalTheory.T.left_translate_sobolev hLC) (GlobalTheory.T.kernel_action_formula GlobalTheory.T.left_translate_sobolev hLC) GlobalTheory.T.wave_representation GlobalTheory.T.wave_uniqueness GlobalTheory.T.phi_resolvent_identity
    GlobalTheory.T.wave_integral_identity GlobalTheory.T.kernel_row_support

end GlobalTheory.CompanionTheory.KerFc
end
end
end
