module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.EventuallyDifferentiableAtOfContDiffAtTwo
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Separation.CompletelyRegular
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralReTopDegreeDensityDbarEqZero
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.IntegralFderivApplyEqZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet
import Development.AbelianVarietyTheory.Definitions.Divisors.LeTwoMulOfForallScale
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Set

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiolaIdentityWirtingerAntiholomorphic

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

noncomputable section

namespace GlobalTheory.GoodTop.Piola

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem hasFDerivAt_dbar_apply {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z) (u : E) :
    HasFDerivAt (fun x => dbar f x u)
      ((1 / 2 : ℂ) • ((ContinuousLinearMap.apply ℝ ℂ u).comp (fderiv ℝ (fderiv ℝ f) z) +
        Complex.I • (ContinuousLinearMap.apply ℝ ℂ (Complex.I • u)).comp (fderiv ℝ (fderiv ℝ f) z))) z := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h : ∀ a : E, HasFDerivAt (fun x => fderiv ℝ f x a)
      ((ContinuousLinearMap.apply ℝ ℂ a).comp (fderiv ℝ (fderiv ℝ f) z)) z :=
    fun a => (ContinuousLinearMap.apply ℝ ℂ a).hasFDerivAt.comp z hD.hasFDerivAt
  exact ((h u).add ((h (Complex.I • u)).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

theorem dbar_dbar_symm {f : E → ℂ} {z : E} (hf : ContDiffAt ℝ 2 f z) (v w : E) :
    dbar (fun x => dbar f x w) z v = dbar (fun x => dbar f x v) z w := by
  have hs : IsSymmSndFDerivAt ℝ f z := hf.isSymmSndFDerivAt (by simp)
  rw [dbar_eq_of_hasFDerivAt (hasFDerivAt_dbar_apply hf w),
    dbar_eq_of_hasFDerivAt (hasFDerivAt_dbar_apply hf v)]
  simp only [antilinPart_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hs v w, hs v (Complex.I • w), hs (Complex.I • v) w, hs (Complex.I • v) (Complex.I • w)]
  ring_nf

theorem dbar_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {g : ι → E → ℂ} {z : E}
    (hg : ∀ i ∈ s, DifferentiableAt ℝ (g i) z) (u : E) :
    dbar (fun x => ∏ i ∈ s, g i x) z u = ∑ k ∈ s, dbar (g k) z u * ∏ i ∈ s.erase k, g i z := by
  have h := HasFDerivAt.finsetProd (fun i hi => (hg i hi).hasFDerivAt)
  rw [dbar_eq_of_hasFDerivAt h]
  simp only [antilinPart_apply, dbar_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

end GlobalTheory.GoodTop.Piola

namespace GlobalTheory.GoodTop

theorem piola_dbar {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n)
    (hf : ∀ i, i ≠ j → ContDiffAt ℝ 2 (f i) v) :
    ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
      dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) = 0 := by
  have e : ∀ w : Equiv.Perm (Fin n),
      dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) =
      ∑ k ∈ Finset.univ.erase j, dbar (fun x => dbar (f k) x (coordVec (w k))) v (coordVec (w j)) *
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i)) := fun w =>
    Piola.dbar_finset_prod (g := fun i x => dbar (f i) x (coordVec (w i))) _
      (fun i hi => (Piola.hasFDerivAt_dbar_apply (hf i (Finset.ne_of_mem_erase hi)) _).differentiableAt) _
  simp only [e, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hkj : k ≠ j := Finset.ne_of_mem_erase hk
  set T : Equiv.Perm (Fin n) → ℂ := fun w => ((Equiv.Perm.sign w : ℤ) : ℂ) *
    (dbar (fun x => dbar (f k) x (coordVec (w k))) v (coordVec (w j)) *
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i))) with hT
  have h1 : ∀ w, T (w * Equiv.swap j k) = -T w := by
    intro w
    have hp : ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec ((w * Equiv.swap j k) i)) =
        ∏ i ∈ (Finset.univ.erase j).erase k, dbar (f i) v (coordVec (w i)) := by
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne
        (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)) (Finset.ne_of_mem_erase hi)]
    simp only [hT]
    rw [hp, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_right,
      Piola.dbar_dbar_symm (hf k hkj) (coordVec (w k)) (coordVec (w j)), Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hkj.symm]
    simp
  have h2 : ∑ w, T w = -∑ w, T w := by
    rw [← Finset.sum_neg_distrib, ← Equiv.sum_comp (Equiv.mulRight (Equiv.swap j k)) T]
    exact Finset.sum_congr rfl fun w _ => h1 w
  show ∑ w, T w = 0
  linear_combination (1 / 2 : ℂ) * h2

end GlobalTheory.GoodTop
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiolaIdentityWirtingerAntiholomorphicStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.piola_identity_wirtingerAntiholomorphic : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, i ≠ j → ContDiffAt ℝ 2 (f i) v) → ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) = 0 := by
  first | exact @GlobalTheory.GoodTop.piola_dbar | exact GlobalTheory.GoodTop.piola_dbar | (intros; apply GlobalTheory.GoodTop.piola_dbar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetWirtingerAntiholomorphicDerivEqSum

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem det_dbar_eq_sum_dbar : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, ContDiffAt ℝ 2 (f i) v) → (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) := by
  intro n f j v hf
  have hP := GlobalTheory.T.piola_identity_wirtingerAntiholomorphic f j v (fun i _ => hf i)
  have hd : ∀ w : Equiv.Perm (Fin n), DifferentiableAt ℝ
      (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v := fun w =>
    (HasFDerivAt.finsetProd (u := Finset.univ.erase j) (g := fun i x => dbar (f i) x (coordVec (w i)))
      (fun i _ => (differentiableAt_dbar_apply (hf i) _).hasFDerivAt)).differentiableAt
  have hj : DifferentiableAt ℝ (f j) v := (hf j).differentiableAt (by norm_num)
  have key : ∀ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
      dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) =
      ((Equiv.Perm.sign w : ℤ) : ℂ) * ∏ i, dbar (f i) v (coordVec (w i)) +
      f j v * (((Equiv.Perm.sign w : ℤ) : ℂ) *
        dbar (fun x => ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j))) := by
    intro w
    rw [dbar_mul hj (hd w), ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    ring
  rw [Finset.sum_congr rfl (fun w _ => key w), Finset.sum_add_distrib, ← Finset.mul_sum, hP, mul_zero, add_zero,
    ← Matrix.det_transpose, Matrix.det_apply']
  rfl

end GlobalTheory.GoodTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetWirtingerAntiholomorphicDerivEqSumStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.det_wirtingerAntiholomorphicDeriv_eq_sum : ∀ {n : ℕ} (f : Fin n → V n → ℂ) (j : Fin n) (v : V n), (∀ i, ContDiffAt ℝ 2 (f i) v) → (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) * dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v (coordVec (w j)) := by
  first | exact @GlobalTheory.GoodTop.det_dbar_eq_sum_dbar | exact GlobalTheory.GoodTop.det_dbar_eq_sum_dbar | (intros; apply GlobalTheory.GoodTop.det_dbar_eq_sum_dbar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAntiholomorphicDerivCompactSupportEqZero

section

@[expose] public section

set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

noncomputable section

namespace GlobalTheory.GoodTop

theorem integral_dbar_eq_zero_of_hasCompactSupport {n : ℕ} {G : V n → ℂ} (hG : ContDiff ℝ 1 G)
    (hc : HasCompactSupport G) (u : V n) :
    Integrable (fun v => dbar G v u) ∧ ∫ v, dbar G v u = 0 := by
  apply _root_.GlobalTheory.CxForm.integrable_dbar_integral_eq_zero <;> assumption

theorem setIntegral_dbar_eq_zero {n : ℕ} (U K : Set (V n)) (g : V n → ℂ) (ξ : V n)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hg : ContDiffOn ℝ 1 g U)
    (h0 : ∀ v ∈ U, v ∉ K → g v = 0) :
    IntegrableOn (fun v => dbar g v ξ) U ∧ ∫ v in U, dbar g v ξ = 0 := by
  classical
  set G : V n → ℂ := U.indicator g with hGdef
  have hin : ∀ v ∈ U, G =ᶠ[𝓝 v] g := fun v hv => by
    filter_upwards [hU.mem_nhds hv] with x hx
    exact Set.indicator_of_mem hx g
  have hz : ∀ x, x ∉ K → G x = 0 := fun x hx => by
    by_cases hxU : x ∈ U
    · rw [hGdef, Set.indicator_of_mem hxU, h0 x hxU hx]
    · rw [hGdef, Set.indicator_of_notMem hxU]
  have hout : ∀ v, v ∉ K → G =ᶠ[𝓝 v] fun _ => 0 := fun v hv => by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hv] with x hx
    exact hz x hx
  have hG : ContDiff ℝ 1 G := by
    rw [contDiff_iff_contDiffAt]
    intro v
    by_cases hv : v ∈ U
    · exact (hg.contDiffAt (hU.mem_nhds hv)).congr_of_eventuallyEq (hin v hv)
    · exact contDiffAt_const.congr_of_eventuallyEq (hout v fun h => hv (hKU h))
  have hc : HasCompactSupport G := HasCompactSupport.intro hK hz
  obtain ⟨hI, hE⟩ := integral_dbar_eq_zero_of_hasCompactSupport hG hc ξ
  have heq : Set.EqOn (fun v => dbar G v ξ) (fun v => dbar g v ξ) U := fun v hv => by
    simp only [dbar_congr (hin v hv)]
  refine ⟨hI.integrableOn.congr_fun heq hU.measurableSet, ?_⟩
  rw [← setIntegral_congr_fun hU.measurableSet heq,
    setIntegral_eq_integral_of_forall_compl_eq_zero, hE]
  intro v hv
  rw [dbar_congr (hout v fun h => hv (hKU h))]
  simp [dbar_apply]

end GlobalTheory.GoodTop
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAntiholomorphicDerivCompactSupportEqZeroStatement

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

theorem _root_.GlobalTheory.T.integral_antiholomorphicDeriv_compactSupport_eq_zero : ∀ {n : ℕ} (U K : Set (V n)) (g : V n → ℂ) (ξ : V n), IsOpen U → IsCompact K → K ⊆ U → ContDiffOn ℝ 1 g U → (∀ v ∈ U, v ∉ K → g v = 0) → IntegrableOn (fun v => dbar g v ξ) U ∧ ∫ v in U, dbar g v ξ = 0 := by
  first | exact @GlobalTheory.GoodTop.setIntegral_dbar_eq_zero | exact GlobalTheory.GoodTop.setIntegral_dbar_eq_zero | (intros; apply GlobalTheory.GoodTop.setIntegral_dbar_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarJacobianDetEqZeroOfCompactSupport

section

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem contDiffOn_dbar_apply {n : ℕ} {U : Set (V n)} {f : V n → ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (ξ : V n) : ContDiffOn ℝ 1 (fun x => dbar f x ξ) U := by
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y) U := hf.fderiv_of_isOpen hU (by norm_num)
  have ha : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y ξ) U := h1.clm_apply contDiffOn_const
  have hb : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y (Complex.I • ξ)) U :=
    h1.clm_apply contDiffOn_const
  have : (fun x => dbar f x ξ) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ f x ξ + Complex.I • fderiv ℝ f x (Complex.I • ξ)) := by
    funext x; exact dbar_apply f x ξ
  rw [this]
  exact (ha.add (hb.const_smul Complex.I)).const_smul _

theorem integral_dbarJacobian_eq_zero : ∀ {n : ℕ} (U K : Set (V n)) (f : Fin n → V n → ℂ) (j : Fin n),
    IsOpen U → IsCompact K → K ⊆ U → (∀ i, ContDiffOn ℝ 2 (f i) U) →
    (∀ v ∈ U, v ∉ K → f j v = 0) →
    ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  intro n U K f j hU hK hKU hf hz
  have hgC : ∀ w : Equiv.Perm (Fin n), ContDiffOn ℝ 1
      (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) U := fun w =>
    ((hf j).of_le (by norm_num)).mul
      (contDiffOn_prod fun i _ => contDiffOn_dbar_apply hU (hf i) _)
  have hg0 : ∀ w : Equiv.Perm (Fin n), ∀ v ∈ U, v ∉ K →
      (f j v * ∏ i ∈ Finset.univ.erase j, dbar (f i) v (coordVec (w i))) = 0 :=
    fun w v hv hvK => by rw [hz v hv hvK, zero_mul]
  have hT := fun w : Equiv.Perm (Fin n) =>
    GlobalTheory.T.integral_antiholomorphicDeriv_compactSupport_eq_zero U K _ (coordVec (w j)) hU hK hKU (hgC w) (hg0 w)
  have hcongr : ∫ v in U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det =
      ∫ v in U, ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤ) : ℂ) *
        dbar (fun x => f j x * ∏ i ∈ Finset.univ.erase j, dbar (f i) x (coordVec (w i))) v
          (coordVec (w j)) :=
    setIntegral_congr_fun hU.measurableSet fun v hv =>
      GlobalTheory.T.det_wirtingerAntiholomorphicDeriv_eq_sum f j v fun i => (hf i).contDiffAt (hU.mem_nhds hv)
  rw [hcongr, integral_finsetSum _ fun w _ => (hT w).1.const_mul _]
  refine Finset.sum_eq_zero fun w _ => ?_
  rw [integral_const_mul, (hT w).2, mul_zero]

end GlobalTheory.GoodTop
end
end
