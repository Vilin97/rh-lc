module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.Matrix.Order

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.Laplace

section

@[expose] public section

open MeasureTheory Complex Filter Topology Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Laplace

theorem gauss_diag {d : ℕ} (b : Fin d → ℂ) (hb : ∀ i, 0 < (b i).re) :
    ∫ v : Fin d → ℝ, cexp (-∑ i, b i * (v i : ℂ) ^ 2) ≠ 0 := by
  have hb0 : ∀ i, b i ≠ 0 := fun i h => by
    have h' := hb i
    rw [h] at h'
    simp at h'
  have h := GaussianFourier.integral_cexp_neg_sum_mul_add hb (fun _ => (0 : ℂ))
  simp only [zero_mul, Finset.sum_const_zero, add_zero] at h
  rw [h, Finset.prod_ne_zero_iff]
  intro i _
  refine mul_ne_zero ?_ (Complex.exp_ne_zero _)
  rw [Ne, Complex.cpow_eq_zero_iff]
  rintro ⟨h1, -⟩
  exact div_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) (hb0 i) h1

open scoped MatrixOrder in
theorem simdiag {d : ℕ} (A C : Matrix (Fin d) (Fin d) ℝ) (hA : A.PosDef) (hC : C.IsHermitian) :
    ∃ P : Matrix (Fin d) (Fin d) ℝ, IsUnit P ∧ ∃ c : Fin d → ℝ,
      Pᵀ * A * P = 1 ∧ Pᵀ * C * P = diagonal c := by
  have spec : ∀ (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.IsHermitian),
      ∃ U : Matrix (Fin d) (Fin d) ℝ, Uᵀ * U = 1 ∧ Uᵀ * M * U = diagonal hM.eigenvalues := by
    intro M hM
    have hst : star (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) =
        (hM.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)ᵀ := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    have h1 := Matrix.mem_unitaryGroup_iff'.1 hM.eigenvectorUnitary.2
    have h2 := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp] at h2
    rw [hst] at h1 h2
    obtain ⟨U, hU1, hU2⟩ : ∃ U : Matrix (Fin d) (Fin d) ℝ,
        Uᵀ * U = 1 ∧ M = U * diagonal hM.eigenvalues * Uᵀ := ⟨_, h1, h2⟩
    refine ⟨U, hU1, ?_⟩
    calc Uᵀ * M * U = Uᵀ * (U * diagonal hM.eigenvalues * Uᵀ) * U :=
          congrArg (fun X => Uᵀ * X * U) hU2
      _ = (Uᵀ * U) * diagonal hM.eigenvalues * (Uᵀ * U) := by simp only [Matrix.mul_assoc]
      _ = diagonal hM.eigenvalues := by rw [hU1, Matrix.one_mul, Matrix.mul_one]
  have hCt : Cᵀ = C := by
    have h := hC
    unfold Matrix.IsHermitian at h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  obtain ⟨U, hU1, hU2⟩ := spec A hA.1
  obtain ⟨s, hs⟩ : ∃ s : Fin d → ℝ, ∀ i, s i * hA.1.eigenvalues i * s i = 1 := by
    refine ⟨fun i => (Real.sqrt (hA.1.eigenvalues i))⁻¹, fun i => ?_⟩
    have h0 := hA.eigenvalues_pos i
    rw [show (Real.sqrt (hA.1.eigenvalues i))⁻¹ * hA.1.eigenvalues i *
        (Real.sqrt (hA.1.eigenvalues i))⁻¹ =
        hA.1.eigenvalues i / (Real.sqrt (hA.1.eigenvalues i) * Real.sqrt (hA.1.eigenvalues i)) by ring,
      Real.mul_self_sqrt h0.le, div_self h0.ne']
  have hQ' : (U * diagonal s)ᵀ * A * (U * diagonal s) = 1 := by
    have e1 : (U * diagonal s)ᵀ * A * (U * diagonal s) = diagonal s * (Uᵀ * A * U) * diagonal s := by
      simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [e1, hU2, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hs i
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin d) (Fin d) ℝ, Qᵀ * A * Q = 1 := ⟨_, hQ'⟩
  have hC' : (Qᵀ * C * Q).IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hCt, Matrix.mul_assoc]
  obtain ⟨V, hV1, hV2⟩ := spec _ hC'
  have hPA : (Q * V)ᵀ * A * (Q * V) = 1 := by
    have e : (Q * V)ᵀ * A * (Q * V) = Vᵀ * (Qᵀ * A * Q) * V := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, hQ, Matrix.mul_one, hV1]
  have hPC : (Q * V)ᵀ * C * (Q * V) = diagonal hC'.eigenvalues := by
    have e : (Q * V)ᵀ * C * (Q * V) = Vᵀ * (Qᵀ * C * Q) * V := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    rw [e, hV2]
  have hdet := congrArg Matrix.det hPA
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at hdet
  have hP : IsUnit (Q * V) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Matrix.det_mul]
    intro h0
    rw [h0] at hdet
    simp at hdet
  exact ⟨Q * V, hP, hC'.eigenvalues, hPA, hPC⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_diag (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ) (hB : ∀ v, v ≠ 0 → 0 < (B v v).re) :
    ∃ (L : (Fin (Module.finrank ℝ E) → ℝ) ≃ₗ[ℝ] E) (b : Fin (Module.finrank ℝ E) → ℂ),
      (∀ i, 0 < (b i).re) ∧ ∀ w, B (L w) (L w) = ∑ i, b i * (w i : ℂ) ^ 2 := by
  let e := Module.finBasis ℝ E
  let A : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => ((B (e i) (e j)).re + (B (e j) (e i)).re) / 2
  let C : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun i j => ((B (e i) (e j)).im + (B (e j) (e i)).im) / 2
  have hexp : ∀ x : Fin (Module.finrank ℝ E) → ℝ, B (e.equivFun.symm x) (e.equivFun.symm x) =
      ∑ i, ∑ j, ((x i * x j : ℝ) : ℂ) * B (e i) (e j) := by
    intro x

    simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, Complex.real_smul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  have hsymm : ∀ (x : Fin (Module.finrank ℝ E) → ℝ) (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      ∑ i, x i * ∑ j, ((f i j + f j i) / 2) * x j = ∑ i, ∑ j, x i * x j * f i j := by
    intro x f
    have h1 : ∑ i, ∑ j, x i * x j * f j i = ∑ i, ∑ j, x i * x j * f i j := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have h2 : ∑ i, x i * ∑ j, ((f i j + f j i) / 2) * x j =
        (∑ i, ∑ j, x i * x j * f i j + ∑ i, ∑ j, x i * x j * f j i) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h2, h1]
    ring
  have hre : ∀ x, (B (e.equivFun.symm x) (e.equivFun.symm x)).re = x ⬝ᵥ (A *ᵥ x) := by
    intro x
    show _ = ∑ i, x i * ∑ j, ((B (e i) (e j)).re + (B (e j) (e i)).re) / 2 * x j
    rw [hsymm x (fun i j => (B (e i) (e j)).re), hexp]
    simp only [Complex.re_sum, Complex.re_ofReal_mul]
  have him : ∀ x, (B (e.equivFun.symm x) (e.equivFun.symm x)).im = x ⬝ᵥ (C *ᵥ x) := by
    intro x
    show _ = ∑ i, x i * ∑ j, ((B (e i) (e j)).im + (B (e j) (e i)).im) / 2 * x j
    rw [hsymm x (fun i j => (B (e i) (e j)).im), hexp]
    simp only [Complex.im_sum, Complex.im_ofReal_mul]
  have hAh : A.IsHermitian := Matrix.IsHermitian.ext fun i j => by
    show star (((B (e j) (e i)).re + (B (e i) (e j)).re) / 2) =
      ((B (e i) (e j)).re + (B (e j) (e i)).re) / 2
    rw [star_trivial, add_comm]
  have hCh : C.IsHermitian := Matrix.IsHermitian.ext fun i j => by
    show star (((B (e j) (e i)).im + (B (e i) (e j)).im) / 2) =
      ((B (e i) (e j)).im + (B (e j) (e i)).im) / 2
    rw [star_trivial, add_comm]
  have hApd : A.PosDef := by
    refine ⟨hAh, fun x hx => ?_⟩
    have key : (x.sum fun i xi => x.sum fun j xj => star xi * A i j * xj) = (⇑x) ⬝ᵥ (A *ᵥ ⇑x) := by
      rw [Finsupp.sum_fintype]
      · show ∑ i, (x.sum fun j xj => star (x i) * A i j * xj) = ∑ i, x i * ∑ j, A i j * x j
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finsupp.sum_fintype]
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [star_trivial]; ring
        · intro j; simp
      · intro i; simp
    rw [key, ← hre]
    refine hB _ ((LinearEquiv.map_ne_zero_iff _).2 ?_)
    intro h0
    exact hx (Finsupp.ext fun i => by simpa using congrFun h0 i)
  obtain ⟨P, hP, c, hPA, hPC⟩ := simdiag A C hApd hCh
  have hcong : ∀ (M : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
      (w : Fin (Module.finrank ℝ E) → ℝ),
      (P *ᵥ w) ⬝ᵥ (M *ᵥ (P *ᵥ w)) = w ⬝ᵥ ((Pᵀ * M * P) *ᵥ w) := by
    intro M w
    rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose P w, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mul_assoc]
  refine ⟨(Matrix.toLinearEquiv' P hP.invertible).trans e.equivFun.symm,
    fun i => 1 + (c i : ℂ) * I, fun i => by simp, fun w => ?_⟩
  have hd : diagonal c *ᵥ w = fun i => c i * w i := funext (Matrix.mulVec_diagonal c w)
  show B (e.equivFun.symm (P *ᵥ w)) (e.equivFun.symm (P *ᵥ w)) = _
  rw [← Complex.re_add_im (B (e.equivFun.symm (P *ᵥ w)) (e.equivFun.symm (P *ᵥ w))), hre, him,
    hcong, hcong, hPA, hPC, Matrix.one_mulVec, hd]
  show ((∑ i, w i * w i : ℝ) : ℂ) + ((∑ i, w i * (c i * w i) : ℝ) : ℂ) * I = _
  push_cast
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

variable [MeasurableSpace E] [BorelSpace E]

theorem gauss_ne_zero (μ : Measure E) [μ.IsAddHaarMeasure] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ)
    (hB : ∀ v, v ≠ 0 → 0 < (B v v).re) : ∫ v, cexp (-(B v v)) ∂μ ≠ 0 := by
  obtain ⟨L, b, hb, hL⟩ := exists_diag B hB
  have hemb : MeasurableEmbedding
      (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) :=
    L.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hμ : μ = Measure.addHaarScalarFactor μ
      (Measure.map (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) volume) •
      Measure.map (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) volume := by
    apply Measure.isAddLeftInvariant_eq_smul
  have hc : 0 < Measure.addHaarScalarFactor μ
      (Measure.map (L.toContinuousLinearEquiv : (Fin (Module.finrank ℝ E) → ℝ) → E) volume) := by
    apply Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
  have h2 : ∀ w : Fin (Module.finrank ℝ E) → ℝ,
      cexp (-(B (L.toContinuousLinearEquiv w) (L.toContinuousLinearEquiv w))) =
        cexp (-∑ i, b i * (w i : ℂ) ^ 2) := by
    intro w
    rw [show L.toContinuousLinearEquiv w = L w from rfl, hL]
  rw [hμ, integral_smul_nnreal_measure, hemb.integral_map]
  simp_rw [h2]
  rw [NNReal.smul_def, Complex.real_smul]
  exact mul_ne_zero (Complex.ofReal_ne_zero.2 (NNReal.coe_pos.2 hc).ne') (gauss_diag b hb)

theorem mono_pow {x s t : ℝ} (hx : 0 ≤ x) (hs : 0 < s) (hst : s ≤ t) :
    (1 + x / s) ^ s ≤ (1 + x / t) ^ t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have hs' : s ≠ 0 := hs.ne'
  have ht' : t ≠ 0 := ht.ne'
  have hp0 : 0 ≤ s / t := div_nonneg hs.le ht.le
  have hp1 : s / t ≤ 1 := (div_le_one ht).2 hst
  have hb : 0 ≤ 1 + x / s := add_nonneg zero_le_one (div_nonneg hx hs.le)
  have key : (1 + x / s) ^ (s / t) ≤ 1 + x / t := by
    have h := Real.geom_mean_le_arith_mean2_weighted hp0 (sub_nonneg.2 hp1) hb zero_le_one
      (by ring : s / t + (1 - s / t) = 1)
    rw [Real.one_rpow, mul_one] at h
    calc (1 + x / s) ^ (s / t) ≤ s / t * (1 + x / s) + (1 - s / t) * 1 := h
      _ = 1 + x / t := by field_simp <;> ring
  calc (1 + x / s) ^ s = ((1 + x / s) ^ (s / t)) ^ t := by
        rw [← Real.rpow_mul hb]
        congr 1
        field_simp
    _ ≤ (1 + x / t) ^ t := Real.rpow_le_rpow (Real.rpow_nonneg hb _) key ht.le

end ReciprocityTheory.ChartRestriction.DS.Lap.Laplace
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.B6

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

private theorem integrable_one_add_mul_norm_sq_rpow_neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] {a s : ℝ} (ha : 0 < a) (hs : (Module.finrank ℝ E : ℝ) < 2 * s) :
    MeasureTheory.Integrable (fun v : E => (1 + a * ‖v‖ ^ 2) ^ (-s)) μ := by
  open MeasureTheory Filter Topology in
  have h := (integrable_rpow_neg_one_add_norm_sq (μ := μ) hs).comp_smul (Real.sqrt_pos.2 ha).ne'
  refine h.congr (Filter.Eventually.of_forall fun v => ?_)
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.2 ha), mul_pow,
    Real.sq_sqrt ha.le]
  congr 1
  ring

private theorem main_lemma_2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E)
    [μ.IsAddHaarMeasure] (f : ℕ → E → ℂ)
    (hm : ∀ᶠ t : ℕ in Filter.atTop, MeasureTheory.AEStronglyMeasurable (f t) μ) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℂ)
    (hlim : ∀ v, Filter.Tendsto (fun t : ℕ => f t ((Real.sqrt t)⁻¹ • v)) Filter.atTop
      (nhds (Complex.exp (-(B v v)))))
    {c γ : ℝ} (hc : 0 < c) (hγ : 0 < γ)
    (hbd : ∀ᶠ t : ℕ in Filter.atTop, ∀ v, ‖f t v‖ ≤ (1 + c * ‖v‖ ^ 2) ^ (-(γ * t))) :
    ∀ᶠ t : ℕ in Filter.atTop, MeasureTheory.Integrable (f t) μ ∧ ∫ v, f t v ∂μ ≠ 0 := by
  open MeasureTheory Filter Topology in
  have hbig : ∀ᶠ t : ℕ in atTop, (Module.finrank ℝ E : ℝ) < 2 * (γ * t) ∧ (1 : ℝ) ≤ t := by
    have h1 : Tendsto (fun t : ℕ => 2 * (γ * (t : ℝ))) atTop atTop :=
      Tendsto.const_mul_atTop two_pos (Tendsto.const_mul_atTop hγ tendsto_natCast_atTop_atTop)
    filter_upwards [h1.eventually_gt_atTop (Module.finrank ℝ E : ℝ), eventually_ge_atTop 1]
      with t ht ht1
    exact ⟨ht, by exact_mod_cast ht1⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((hbd.and hm).and hbig)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos (hN N le_rfl).2.2

  have hmaj : ∀ t : ℕ, N ≤ t → ∀ w : E,
      ‖f t ((Real.sqrt t)⁻¹ • w)‖ ≤ (1 + c / N * ‖w‖ ^ 2) ^ (-(γ * N)) := by
    intro t ht w
    have ht' : (N : ℝ) ≤ t := by exact_mod_cast ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hNpos ht'
    have h1 := (hN t ht).1.1 ((Real.sqrt t)⁻¹ • w)
    have hn : ‖(Real.sqrt t)⁻¹ • w‖ ^ 2 = ‖w‖ ^ 2 / t := by
      rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        inv_pow, Real.sq_sqrt htpos.le]
      ring
    rw [hn] at h1
    refine h1.trans ?_
    have hx : 0 ≤ c * ‖w‖ ^ 2 := by positivity
    have hmono := ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.mono_pow hx hNpos ht'
    have hA : 0 < 1 + c * ‖w‖ ^ 2 / N := by positivity
    have hB : 0 < 1 + c * ‖w‖ ^ 2 / t := by positivity
    have key : (1 + c * ‖w‖ ^ 2 / N) ^ (γ * N) ≤ (1 + c * ‖w‖ ^ 2 / t) ^ (γ * t) := by
      rw [mul_comm γ (N : ℝ), mul_comm γ (t : ℝ), Real.rpow_mul hA.le, Real.rpow_mul hB.le]
      exact Real.rpow_le_rpow (Real.rpow_nonneg hA.le _) hmono hγ.le
    have e1 : c * (‖w‖ ^ 2 / t) = c * ‖w‖ ^ 2 / t := by ring
    have e2 : c / N * ‖w‖ ^ 2 = c * ‖w‖ ^ 2 / N := by ring
    rw [e1, e2, Real.rpow_neg hB.le, Real.rpow_neg hA.le]
    exact inv_anti₀ (Real.rpow_pos_of_pos hA _) key
  have hbint : Integrable (fun w : E => (1 + c / N * ‖w‖ ^ 2) ^ (-(γ * N))) μ :=
    integrable_one_add_mul_norm_sq_rpow_neg μ (div_pos hc hNpos) (hN N le_rfl).2.1
  have hgm : ∀ t : ℕ, N ≤ t → AEStronglyMeasurable (fun w => f t ((Real.sqrt t)⁻¹ • w)) μ := by
    intro t ht
    have htpos : (0 : ℝ) < t := lt_of_lt_of_le hNpos (by exact_mod_cast ht)
    have hr : (Real.sqrt t)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 htpos).ne'
    exact (hN t ht).1.2.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_smul μ hr)
  have hT : Tendsto (fun t : ℕ => ∫ w, f t ((Real.sqrt t)⁻¹ • w) ∂μ) atTop
      (𝓝 (∫ w, Complex.exp (-(B w w)) ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence _
      ((eventually_ge_atTop N).mono hgm)
      ((eventually_ge_atTop N).mono fun t ht => Eventually.of_forall (hmaj t ht))
      hbint (Eventually.of_forall hlim)

  have hpos : ∀ v : E, v ≠ 0 → 0 < (B v v).re := by
    intro v hv
    have hle : ‖Complex.exp (-(B v v))‖ ≤ (1 + c / N * ‖v‖ ^ 2) ^ (-(γ * N)) :=
      le_of_tendsto (hlim v).norm (eventually_atTop.2 ⟨N, fun t ht => hmaj t ht v⟩)
    have hlt : (1 + c / N * ‖v‖ ^ 2) ^ (-(γ * N)) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg
      · have hv' := norm_pos_iff.2 hv
        have : 0 < c / N * ‖v‖ ^ 2 := by positivity
        linarith
      · have := mul_pos hγ hNpos
        linarith
    rw [Complex.norm_exp] at hle
    have h3 : Real.exp (-(B v v)).re < 1 := hle.trans_lt hlt
    have h4 := Real.exp_lt_exp.1 (h3.trans_eq Real.exp_zero.symm)
    rw [Complex.neg_re] at h4
    linarith
  have hev : ∀ᶠ t : ℕ in atTop, ∫ w, f t ((Real.sqrt t)⁻¹ • w) ∂μ ≠ 0 :=
    hT.eventually_ne (ReciprocityTheory.ChartRestriction.DS.Lap.Laplace.gauss_ne_zero μ B hpos)
  filter_upwards [eventually_ge_atTop N, hev] with t ht hgt
  refine ⟨?_, ?_⟩
  · exact Integrable.mono' (integrable_one_add_mul_norm_sq_rpow_neg μ hc (hN t ht).2.1) (hN t ht).1.2
      (Eventually.of_forall (hN t ht).1.1)
  · intro h0
    apply hgt
    rw [Measure.integral_comp_smul μ (f t) (Real.sqrt t)⁻¹, h0, smul_zero]

theorem b6 : GaussianLimitHaar := by
  intro E _ _ _ _ _ μ _ f hm B hlim c γ hc hγ hbd
  exact main_lemma_2 μ f hm B hlim hc hγ hbd

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
end
end
end
