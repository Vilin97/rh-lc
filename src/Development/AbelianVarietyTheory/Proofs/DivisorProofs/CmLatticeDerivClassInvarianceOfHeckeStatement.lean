module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedProductDerivativeTermNormLeUniform
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivFormulaOfSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnWirtWordMulExpCompStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DTermOrigin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFormExistsUnique
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsElementPosImUnderCmType
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivCmTypeRealEmbeddingsMaxRealSubfieldStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFDerivAtWeightTwoDerivativeEisensteinTermStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDeformedLatticeEisensteinSummandWeightTwoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomothetyLatSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedComplexPartialDerivativeEqWirtingerWordStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePrincMulUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegersOfMemHatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderLatticeEqSteinitzFormCmStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannClEqSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesDifferentiable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightTwoDerivativeEisensteinTermUniformBoundStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFormBaseOfValue

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DualBase

theorem dualFormBase_of_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → DualFormValue φ → DualFormBase φ := by
  intro E _ _ _ I _ _ φ hcm hval d δ hd hδ hφ η
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    have : (d : E) = 0 := by simpa using hδ.symm
    have : d = 0 := by exact_mod_cast this
    omega
  obtain ⟨i0, -⟩ := hcm (Classical.choice (inferInstance : Nonempty (E →+* ℂ)))
  have hconj : IsCMField.complexConj E δ = -δ := by
    apply (φ i0).injective
    rw [IsCMField.complexEmbedding_complexConj, hφ, map_neg, hφ]
    simp [Complex.conj_ofReal]
  have hξ0 : ((η : ℤ) : E) * δ⁻¹ ≠ 0 := mul_ne_zero (by simp) (inv_ne_zero hδ0)
  have hξc : IsCMField.complexConj E (((η : ℤ) : E) * δ⁻¹) = -(((η : ℤ) : E) * δ⁻¹) := by
    rw [map_mul, map_inv₀, hconj, map_intCast, inv_neg, mul_neg]
  obtain ⟨h1, h2⟩ := hval _ hξ0 hξc
  refine ⟨h1, fun B hB ε => ?_⟩
  obtain ⟨h3, h4⟩ := h2 B hB ε
  refine ⟨h3, fun i => ?_⟩
  rw [h4 i, map_mul, map_inv₀, map_intCast, hφ]
  have hs : (Real.sqrt d : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rcases Int.units_eq_one_or η with rfl | rfl <;> rcases Int.units_eq_one_or ε with rfl | rfl <;>
    · push_cast
      field_simp

end GlobalTheory.DualBase
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualFormValueOfValues

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum

namespace GlobalTheory.DualFormOrtho

theorem bilin_eq_zero_of_span {V : Type} [AddCommGroup V] [Module ℂ V] (B : LinearMap.BilinForm ℂ V) {s t : Set V}
    (h : ∀ u ∈ s, ∀ v ∈ t, B u v = 0) {a b : V} (ha : a ∈ Submodule.span ℂ s) (hb : b ∈ Submodule.span ℂ t) : B a b = 0 := by
  induction ha using Submodule.span_induction with
  | mem u hu =>
    induction hb using Submodule.span_induction with
    | mem v hv => exact h u hu v hv
    | zero => simp
    | add x y _ _ hx hy => simp [hx, hy]
    | smul c x _ hx => simp [hx]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul c x _ hx => simp [hx]

theorem dualFormValue_of_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ), IsCMType φ → (∀ ξ : E, ξ ≠ 0 → ∃! B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B) →
    (∀ ξ : E, ξ ≠ 0 → IsCMField.complexConj E ξ = -ξ → ∀ B : LinearMap.BilinForm ℂ (Coh E), IsDualForm ξ B →
      ∀ ρ ρ' : E →+* ℂ, (ρ' = ComplexEmbedding.conjugate ρ → B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = (ρ ξ)⁻¹) ∧
        (ρ' ≠ ComplexEmbedding.conjugate ρ → B ρ.toRatAlgHom.toLinearMap ρ'.toRatAlgHom.toLinearMap = 0)) →
    DualFormValue φ := by
  intro E _ _ _ I _ _ φ hφ hex hval ξ hξ hc
  refine ⟨hex ξ hξ, fun B hB ε => ?_⟩
  have hv := hval ξ hξ hc B hB
  have key : ∀ i j, i ≠ j → ∀ σ : E →+* ℂ, (σ = φ i ∨ σ = ComplexEmbedding.conjugate (φ i)) →
      (σ = φ j ∨ σ = ComplexEmbedding.conjugate (φ j)) → False :=
    fun i j hij σ h1 h2 => hij ((hφ σ).unique h1 h2)
  have gen : ∀ i j, i ≠ j → ∀ u ∈ ({eCl φ i, fCl φ i} : Set (Coh E)), ∀ v ∈ ({eCl φ j, fCl φ j} : Set (Coh E)), B u v = 0 := by
    rintro i j hij u (rfl | rfl) v (rfl | rfl)
    · exact (hv (φ i) (φ j)).2 fun h => key i j hij (φ j) (Or.inr h) (Or.inl rfl)
    · exact (hv (φ i) (ComplexEmbedding.conjugate (φ j))).2 fun h =>
        key i j hij (ComplexEmbedding.conjugate (φ j)) (Or.inr h) (Or.inr rfl)
    · refine (hv (ComplexEmbedding.conjugate (φ i)) (φ j)).2 fun h => ?_
      rw [ComplexEmbedding.involutive_conjugate E (φ i)] at h
      exact key i j hij (φ j) (Or.inl h) (Or.inl rfl)
    · refine (hv (ComplexEmbedding.conjugate (φ i)) (ComplexEmbedding.conjugate (φ j))).2 fun h => ?_
      rw [ComplexEmbedding.involutive_conjugate E (φ i)] at h
      exact key i j hij (ComplexEmbedding.conjugate (φ j)) (Or.inl h) (Or.inr rfl)
  refine ⟨fun i j hij a ha b hb => ?_, fun i => ?_⟩
  · have h0 : B a b = 0 := bilin_eq_zero_of_span B (gen i j hij) ha hb
    rw [pairing, h0, mul_zero]
  · have h1 : B (eCl φ i) (fCl φ i) = (φ i ξ)⁻¹ := (hv (φ i) (ComplexEmbedding.conjugate (φ i))).1 rfl
    rw [pairing, h1, div_eq_mul_inv]
    ring

end GlobalTheory.DualFormOrtho
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsElementPosImUnderCmTypeStatement

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_element_pos_im_under_cmType : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ θ : E, ∀ i, 0 < (φ i θ).im := by
  first | exact @GlobalTheory.CMTypeImPos.exists_im_pos | exact GlobalTheory.CMTypeImPos.exists_im_pos | (intros; apply GlobalTheory.CMTypeImPos.exists_im_pos <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHecke

section

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum GlobalTheory.DeformedSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.DerivAtOrigin

theorem series_weightTwo : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] [DecidableEq I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (σ : ℂ), 0 < σ.re → ∀ (m : I → ℕ) (z : I → ℂ), z ∈ polydisc I → DifferentiableAt ℝ (fun w : I → ℂ => ∑' q : modUnits (lattice c y), eTerm φ m σ w q.1.out) z ∧ ∀ i : I, wirt i false (fun w : I → ℂ => ∑' q : modUnits (lattice c y), eTerm φ m σ w q.1.out) z = ∑' q : modUnits (lattice c y), eTerm φ (m + Pi.single i 1) σ z q.1.out := by
  intro E _ _ _ I _ _ φ hφ c y hc σ hσ m z hz
  have hz1 : ‖z‖ < 1 := (pi_norm_lt_iff one_pos).2 hz
  set r : ℝ := (‖z‖ + 1) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hzr : ‖z‖ < r := by rw [hr]; linarith
  set U : Set (I → ℂ) := Metric.ball 0 r with hU
  have hUo : IsOpen U := Metric.isOpen_ball
  have hUc : IsPreconnected U := (convex_ball (0 : I → ℂ) r).isPreconnected
  have hzU : z ∈ U := by simpa [hU] using hzr
  have hUle : ∀ w ∈ U, ∀ i, ‖w i‖ ≤ r := fun w hw i =>
    (norm_le_pi_norm w i).trans (show ‖w‖ < r by simpa [hU] using hw).le
  have hUpd : ∀ w ∈ U, w ∈ polydisc I := fun w hw i => lt_of_le_of_lt (hUle w hw i) hr1
  set N : modUnits (lattice c y) → ℝ := fun q => |(Algebra.norm ℚ (q.1.out : E) : ℝ)| ^ (-(1 + σ.re)) with hN
  have hNs : Summable N := GlobalTheory.CMVal.Conv.summable_norm_rpow E c y (1 + σ.re) hc (by linarith)
  have hne : ∀ q : modUnits (lattice c y), q.1.out ≠ 0 := fun q => (out_mem_lattice q).2
  choose C hC using fun m : I → ℕ => GlobalTheory.T.weightTwoDerivativeEisensteinTerm_uniform_bound E I φ hφ m σ r hσ.le hr1
  have hsum : ∀ m, ∀ w ∈ U, Summable (fun q : modUnits (lattice c y) => eTerm φ m σ w q.1.out) := fun m w hw =>
    Summable.of_norm_bounded (hNs.mul_left (C m)) fun q => hC m w (hUle w hw) _ (hne q)
  set f' : modUnits (lattice c y) → (I → ℂ) → ((I → ℂ) →L[ℝ] ℂ) := fun q w =>
    ∑ j, (eTerm φ (m + Pi.single j 1) σ w q.1.out • dz j +
      (eTerm φ m σ w q.1.out * (-σ * φ j q.1.out / starRingEnd ℂ (defCoord φ w q.1.out j))) • dzbar j) with hf'
  set u : modUnits (lattice c y) → ℝ := fun q => ∑ j : I, (C (m + Pi.single j 1) * N q * ‖(dz j : (I → ℂ) →L[ℝ] ℂ)‖ +
    C m * N q * (‖σ‖ / (1 - r)) * ‖(dzbar j : (I → ℂ) →L[ℝ] ℂ)‖) with hu
  have hus : Summable u := summable_sum fun j _ =>
    ((hNs.mul_left _).mul_right _).add (((hNs.mul_left _).mul_right _).mul_right _)
  have hder : ∀ q w, w ∈ U → HasFDerivAt (fun w : I → ℂ => eTerm φ m σ w q.1.out) (f' q w) w :=
    fun q w hw => GlobalTheory.T.hasFDerivAt_weightTwoDerivativeEisensteinTerm E I φ m σ q.1.out (hne q) w (hUpd w hw)
  have hrat : ∀ (q : modUnits (lattice c y)) w, w ∈ U → ∀ j,
      ‖-σ * φ j q.1.out / starRingEnd ℂ (defCoord φ w q.1.out j)‖ ≤ ‖σ‖ / (1 - r) := by
    intro q w hw j
    have hl := GlobalTheory.DeformedSum.Bound.defCoord_lower φ w q.1.out j (hUle w hw j)
    have hp : 0 < ‖φ j q.1.out‖ := by simpa using hne q
    have hr' : 0 < 1 - r := by linarith
    have hd : 0 < ‖defCoord φ w q.1.out j‖ := lt_of_lt_of_le (mul_pos hr' hp) hl
    rw [norm_div, norm_mul, norm_neg, Complex.norm_conj, div_le_div_iff₀ hd hr']
    nlinarith [norm_nonneg σ]
  have hbd : ∀ q w, w ∈ U → ‖f' q w‖ ≤ u q := by
    intro q w hw
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_add_le _ _).trans (add_le_add ?_ ?_))
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hC _ w (hUle w hw) _ (hne q)) (norm_nonneg _)
    · rw [norm_smul, norm_mul]
      have h1 := hC m w (hUle w hw) _ (hne q)
      exact mul_le_mul_of_nonneg_right (mul_le_mul h1 (hrat q w hw j) (norm_nonneg _) ((norm_nonneg _).trans h1))
        (norm_nonneg _)
  have hF : HasFDerivAt (fun w : I → ℂ => ∑' q : modUnits (lattice c y), eTerm φ m σ w q.1.out)
      (∑' q, f' q z) z :=
    hasFDerivAt_tsum_of_isPreconnected hus hUo hUc hder hbd hzU (hsum m z hzU) hzU
  refine ⟨hF.differentiableAt, fun i => ?_⟩
  have hcs : Summable (fun q => f' q z) := Summable.of_norm_bounded hus fun q => hbd q z hzU
  have hap : ∀ v : I → ℂ, HasSum (fun q => f' q z v) ((∑' q, f' q z) v) := fun v =>
    (ContinuousLinearMap.apply ℝ ℂ v).hasSum hcs.hasSum
  unfold wirt
  rw [hF.fderiv]
  refine (HasSum.tsum_eq ?_).symm
  refine (((hap _).add ((hap _).mul_left _)).div_const 2).congr_fun ?_
  intro q
  simp only [hf', ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dz_apply,
    dzbar_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp),
    Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj]) (by simp)]
  simp only [Pi.single_eq_same, map_one, Complex.conj_I, Bool.false_eq_true, if_false]
  linear_combination (eTerm φ (m + Pi.single i 1) σ z q.1.out / 2 -
    eTerm φ m σ z q.1.out * (-σ * φ i q.1.out / starRingEnd ℂ (defCoord φ z q.1.out i)) / 2) * Complex.I_mul_I

theorem wirtWord_congr {I : Type} [Fintype I] {U : Set (I → ℂ)} (hU : IsOpen U) {f g : (I → ℂ) → ℂ}
    (h : ∀ z ∈ U, f z = g z) (w : List (I × Bool)) : ∀ z ∈ U, wirtWord w f z = wirtWord w g z := by
  induction w with
  | nil => exact h
  | cons a w ih =>
    intro z hz
    have hev : wirtWord w f =ᶠ[nhds z] wirtWord w g := by
      filter_upwards [hU.mem_nhds hz] with u hu using ih u hu
    simp only [wirtWord_cons, wirt, hev.fderiv_eq]

theorem wirt_const_mul {I : Type} [Fintype I] (i : I) (bar : Bool) (a : ℂ) {f : (I → ℂ) → ℂ} {z : I → ℂ}
    (hf : DifferentiableAt ℝ f z) : wirt i bar (fun w => a * f w) z = a * wirt i bar f z := by
  simp only [wirt, fderiv_const_mul hf, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem eq_at_zero {f g : ℂ → ℂ} (hf : DifferentiableOn ℂ f halfPlane) (hg : DifferentiableOn ℂ g halfPlane)
    (h : ∀ σ : ℂ, 0 < σ.re → f σ = g σ) : f 0 = g 0 := by
  have ho : IsOpen halfPlane := isOpen_lt continuous_const Complex.continuous_re
  have hc : IsPreconnected halfPlane := (convex_halfSpace_re_gt _).isPreconnected
  have h1 : (1 : ℂ) ∈ halfPlane := by simp [halfPlane]; norm_num
  have h0 : (0 : ℂ) ∈ halfPlane := by simp [halfPlane]; norm_num
  have ho' : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  refine (hf.analyticOnNhd ho).eqOn_of_preconnected_of_eventuallyEq (hg.analyticOnNhd ho) hc h1 ?_ h0
  filter_upwards [ho'.mem_nhds (show (1 : ℂ) ∈ {s : ℂ | 0 < s.re} by simp)] with s hs using h s hs

theorem isOpen_upperHalf (F : Type) [Field F] [NumberField F] : IsOpen (upperHalf F) := by
  have : upperHalf F = ⋂ τ : Emb F, {z : Emb F → ℂ | 0 < (z τ).im} := by
    ext z; simp [upperHalf]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply i))

theorem derivFormula_two (hH : HeckeWeightTwo) (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I]
    [DecidableEq I] (φ : I → E →+* ℂ) (hF : 2 ≤ Module.finrank ℚ (maximalRealSubfield E)) (hφ : IsCMType φ)
    (c : Ideal (OF E)) (y : (Af E)ˣ) (hc : c ≠ ⊥) : DerivFormula φ 2 (lattice c y) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_cmType_realEmbeddings_maxRealSubfield E I φ hφ
  obtain ⟨θ₀, hθ₀⟩ := GlobalTheory.T.exists_element_pos_im_under_cmType E I φ hφ
  have hne : Nonempty I := by
    obtain ⟨i, -⟩ := hφ (Classical.arbitrary (E →+* ℂ))
    exact ⟨i⟩
  have hnot : ∀ θ : E, (∀ i, 0 < (φ i θ).im) → θ ∉ maximalRealSubfield E := fun θ h hθ => by
    obtain ⟨i⟩ := hne
    have h1 := h i
    rw [show θ = ((⟨θ, hθ⟩ : maximalRealSubfield E) : E) from rfl, he] at h1
    simp at h1
  obtain ⟨𝔞, 𝔟, a₀, hL⟩ := GlobalTheory.T.orderLattice_eq_steinitzForm_cm E c y hc θ₀ (hnot θ₀ hθ₀)
  set θ : E := θ₀ + a₀ with hθdef
  have hθ : ∀ i, 0 < (φ i θ).im := fun i => by
    rw [hθdef, map_add (f := _), he]; simpa using hθ₀ i
  obtain ⟨G, ⟨hG1, hG2, hG3⟩, hG0, -⟩ := hH (maximalRealSubfield E) hF 𝔞 𝔟
  have hP := GlobalTheory.WeightTwoSum.isOpen_polydisc I
  have hmaps : Set.MapsTo (modPt φ e θ) (polydisc I) (upperHalf _) := fun z hz τ => modPt_im_pos φ e θ hθ hz τ
  set cw : ℂ := (cWt E 2 : ℂ) with hcw
  set b : (I → ℂ) → ℂ := fun z => (homFac z)⁻¹ ^ 2 with hb
  have hbC : ContDiffOn ℂ ∞ b (polydisc I) :=
    (contDiff_homFac.contDiffOn.inv fun z hz => homFac_ne_zero hz).pow 2
  set K : ℂ → (I → ℂ) → ℂ := fun σ z => b z * Complex.exp (-σ * logFac z) * G σ (modPt φ e θ z) with hK
  have hchain : ∀ (a : ℂ) (w : List (I × Bool)), ∀ z ∈ polydisc I,
      DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => a * K σ z') z) halfPlane := fun a w z hz => by
    have h := GlobalTheory.T.differentiableOn_wirtWord_mul_exp_comp' _ I (polydisc I) (upperHalf _) halfPlane G (modPt φ e θ) (fun z => a * b z) logFac hP
      (isOpen_upperHalf _) hmaps ((contDiffOn_modPt φ e θ).restrict_scalars ℝ)
      ((contDiffOn_const.mul hbC).restrict_scalars ℝ) contDiffOn_logFac hG2 hG3 w z hz
    simpa only [hK, mul_assoc] using h
  have hKd : ∀ z ∈ polydisc I, DifferentiableOn ℂ (fun σ => K σ z) halfPlane := fun z hz => by
    simpa [wirtWord_nil] using hchain 1 [] z hz
  have hKs : ∀ z ∈ polydisc I, ∀ σ : ℂ, 0 < σ.re →
      HasSum (fun q : modUnits (lattice c y) => defTerm φ 2 z σ q.1.out) (K σ z) := fun z hz σ hσ => by
    obtain ⟨h1, h2⟩ := hG1 σ hσ _ (hmaps hz)
    refine GlobalTheory.T.hasSum_deformedLatticeEisensteinSummand_weight_two E I φ e he 𝔞 𝔟 θ _ (hnot θ hθ) hL z hz σ _ ?_
    rw [h2]
    exact h1.hasSum
  have hagree : ∀ g, IsDefSum φ 2 (lattice c y) g → ∀ z ∈ polydisc I, g z = cw * K 0 z := by
    intro g hg z hz
    obtain ⟨G', hG', hgz⟩ := hg z hz
    obtain ⟨H, hH1, hH2, rfl⟩ := hG'.2 rfl
    rw [hgz, eq_at_zero hH1 (hKd z hz) fun σ hσ => (hH2 σ hσ).unique (hKs z hz σ hσ)]
  have hK0 : DifferentiableOn ℂ (fun z => cw * K 0 z) (polydisc I) := by
    simp only [hK, neg_zero, zero_mul, Complex.exp_zero, mul_one]
    refine (((hbC.differentiableOn (by simp)).mul (hG0.comp ((contDiffOn_modPt φ e θ).differentiableOn (by simp)) hmaps))).const_mul _
  refine ⟨⟨fun z => cw * K 0 z, fun z hz => ⟨K 0 z, ⟨fun h => absurd rfl h,
    fun _ => ⟨fun σ => K σ z, hKd z hz, hKs z hz, rfl⟩⟩, rfl⟩⟩, fun g hg => ?_⟩
  have hgd : DifferentiableOn ℂ g (polydisc I) := hK0.congr (hagree g hg)
  refine ⟨hgd, fun κ l hl => ⟨fun S hS => ?_, fun h => absurd h (by norm_num)⟩⟩
  have h0 : (0 : I → ℂ) ∈ polydisc I := GlobalTheory.DerivAtOrigin.zero_mem_polydisc I
  have hκ : (fun j => l.count j) = κ := funext hl

  have hser : ∀ σ : ℂ, 0 < σ.re → ∀ l : List I, ∀ z ∈ polydisc I,
      wirtWord (l.map fun i => (i, false)) (fun z' => cw * K σ z') z =
        cw * ∑' q : modUnits (lattice c y), eTerm φ (fun j => l.count j) σ z q.1.out := by
    intro σ hσ l
    induction l with
    | nil =>
      intro z hz
      have : (fun j : I => ([] : List I).count j) = 0 := by funext j; simp
      rw [this]
      simp only [List.map_nil, wirtWord_nil, eTerm_zero]
      rw [(hKs z hz σ hσ).tsum_eq]
    | cons i l ih =>
      intro z hz
      obtain ⟨h1, h2⟩ := series_weightTwo E I φ hφ c y hc σ hσ (fun j => l.count j) z hz
      have h3 := wirtWord_congr hP ih [(i, false)] z hz
      rw [List.map_cons, wirtWord_cons, count_cons_eq, ← h2 i, ← wirt_const_mul i false cw h1]
      exact h3
  rw [GlobalTheory.T.iteratedComplexPartialDerivative_eq_wirtingerWord I _ g hP hgd l 0 h0, wirtWord_congr hP (hagree g hg) _ 0 h0, ← risingS_zero]
  refine eq_at_zero (f := fun σ => wirtWord (l.map fun i => (i, false)) (fun z' => cw * K σ z') 0)
    (g := fun σ => cw * risingS σ κ * S σ) (hchain cw _ 0 h0)
    ((((differentiable_risingS κ).const_mul cw).mul hS.1).differentiableOn) fun σ hσ => ?_
  have h4 := hS.2 σ (by push_cast; linarith)
  simp only [hser σ hσ l 0 h0, hκ, eTerm_origin]
  rw [tsum_mul_left, h4.tsum_eq, mul_assoc]

theorem statement (hH : HeckeWeightTwo) : GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement := by
  intro E _ _ _ I _ _ φ hF hφ
  have hV := GlobalTheory.DualFormOrtho.dualFormValue_of_values E I φ hφ (GlobalTheory.DualFormExists.dualForm_existsUnique E)
    (GlobalTheory.DualFormValues.dualForm_values E)
  refine ⟨fun s hs => ⟨fun c y hc => ⟨?_, GlobalTheory.HomothetyLatSum.homothety E I φ hφ s _⟩,
    GlobalTheory.ClassInv.classInvariance E I φ hφ (GlobalTheory.HomothetyLatSum.homothety E I φ hφ) s⟩, hV,
    GlobalTheory.DualBase.dualFormBase_of_value E I φ hφ hV⟩
  rcases Nat.lt_or_ge s 2 with h | h
  · obtain rfl : s = 1 := by omega
    exact derivFormula_two hH E I φ hF hφ c y hc
  · exact derivFormula_of_series E I φ (2 * s) _ (by omega)
      (fun m z hz => GlobalTheory.DeformedSum.Series.series_differentiable E I φ hφ s h c y hc m z hz)

end GlobalTheory.DerivAtOrigin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDerivClassInvarianceOfHeckeStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement := by
  first | exact @GlobalTheory.DerivAtOrigin.statement | exact GlobalTheory.DerivAtOrigin.statement | (intros; apply GlobalTheory.DerivAtOrigin.statement <;> assumption)
end
end
