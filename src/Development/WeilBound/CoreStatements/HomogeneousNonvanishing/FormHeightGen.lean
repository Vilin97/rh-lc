module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSphereMeanEqOfFrameNormEq
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.SemistableReduction.DetGramEqProdGramSchmidt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousRenameCastLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinSubstLinSubst
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.UniformSpace.Uniformizable
import ReciprocityTheory.SemistableReduction.LagrangeIdealLiftsFact

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianFirstCoordsMeasurePreserving

section

@[expose] public section

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

noncomputable section

namespace GlobalTheory.GaussMarginal

open Real

theorem lintegral_pi_fin {E : Type*} [MeasurableSpace E] (n : ℕ) (μ : Measure E) [SigmaFinite μ]
    (f : Fin n → E → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), Fin.prod_univ_succ,
      ← ih (fun i => f i.succ) (fun i => hf _), ← lintegral_prod_mul (hf 0).aemeasurable
        (Finset.measurable_prod _ fun i _ => (hf i.succ).comp (measurable_pi_apply i)).aemeasurable]
    refine lintegral_congr fun q => ?_
    simp [Fin.prod_univ_succ, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

theorem lintegral_pi_prod {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E) [SigmaFinite μ]
    (f : ι → E → ENNReal) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : ι → E, ∏ i, f i (x i) ∂(Measure.pi fun _ => μ) = ∏ i, ∫⁻ t, f i t ∂μ := by
  let e := (Fintype.equivFin ι).symm
  have h := measurePreserving_piCongrLeft (fun _ : ι => μ) e
  rw [← h.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _), ← e.prod_comp,
    ← lintegral_pi_fin _ μ (fun i => f (e i)) (fun i => hf _)]
  refine lintegral_congr fun q => ?_
  rw [← e.prod_comp]
  simp [MeasurableEquiv.coe_piCongrLeft]

theorem pi_withDensity_const {ι E : Type*} [Fintype ι] [MeasurableSpace E] (μ : Measure E)
    [SigmaFinite μ] (f : E → ENNReal) (hf : Measurable f) [SigmaFinite (μ.withDensity f)] :
    (Measure.pi fun _ : ι => μ.withDensity f) =
      (Measure.pi fun _ : ι => μ).withDensity fun x => ∏ i, f (x i) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [withDensity_apply _ (hs _), ← lintegral_indicator (hs _)]
  rw [← lintegral_pi_prod μ (fun i => (s i).indicator f) (fun i => hf.indicator (hs i))]
  refine lintegral_congr fun x => ?_
  by_cases hx : x ∈ Set.univ.pi s
  · rw [Set.indicator_of_mem hx]
    exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hx i trivial) _).symm
  · rw [Set.indicator_of_notMem hx]
    obtain ⟨i, hi⟩ : ∃ i, x i ∉ s i := by simpa [Set.mem_pi] using hx
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm

theorem isProbabilityMeasure_complexGaussian_one :
    IsProbabilityMeasure (GlobalTheory.complexGaussian ℂ 1) :=
  GlobalTheory.isProbabilityMeasure_complexGaussian (by simp [Complex.finrank_real_complex])

theorem gaussProb_eq_complexGaussian (k : ℕ) :
    gaussProb k = GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k := by
  have hP := GlobalTheory.isProbabilityMeasure_complexGaussian (E := EuclideanSpace ℂ (Fin k)) (g := k)
    (by rw [GlobalTheory.finrank_real_euclideanSpace_complex, Fintype.card_fin])
  set ν := (volume : Measure (EuclideanSpace ℂ (Fin k))).withDensity
    fun x => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) with hν
  have hm : Measurable fun x : EuclideanSpace ℂ (Fin k) => ENNReal.ofReal (Real.exp (-‖x‖ ^ 2)) := by
    fun_prop
  have hc : GlobalTheory.complexGaussian (EuclideanSpace ℂ (Fin k)) k = ENNReal.ofReal ((π ^ k)⁻¹) • ν := by
    ext s hs
    rw [Measure.smul_apply, GlobalTheory.complexGaussian, withDensity_apply _ hs, hν, withDensity_apply _ hs,
      smul_eq_mul, ← lintegral_const_mul _ hm]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (by positivity)]
  have h1 := hP.measure_univ
  rw [hc, Measure.smul_apply, smul_eq_mul] at h1
  rw [gaussProb, ProbabilityTheory.cond, Measure.restrict_univ, hc, ← hν,
    ← ENNReal.eq_inv_of_mul_eq_one_left h1]

theorem map_ofLp_gaussProb (k : ℕ) :
    (gaussProb k).map (WithLp.ofLp (p := 2) (V := Fin k → ℂ)) =
      Measure.pi fun _ : Fin k => GlobalTheory.complexGaussian ℂ 1 := by
  haveI := isProbabilityMeasure_complexGaussian_one
  have hmp := GlobalTheory.volume_preserving_ofLp_complex (Fin k)
  set f1 : ℂ → ENNReal := fun z => ENNReal.ofReal ((π ^ 1)⁻¹ * Real.exp (-‖z‖ ^ 2)) with hf1
  have hf1m : Measurable f1 := by fun_prop
  haveI : SigmaFinite ((volume : Measure ℂ).withDensity f1) :=
    inferInstanceAs (SigmaFinite (GlobalTheory.complexGaussian ℂ 1))
  have hG : Measurable fun y : Fin k → ℂ => ∏ i, f1 (y i) := by fun_prop
  ext s hs
  rw [Measure.map_apply hmp.measurable hs, gaussProb_eq_complexGaussian, GlobalTheory.complexGaussian,
    withDensity_apply _ (hmp.measurable hs), show GlobalTheory.complexGaussian ℂ 1 = (volume : Measure ℂ).withDensity f1 from rfl,
    pi_withDensity_const _ f1 hf1m, ← volume_pi, withDensity_apply _ hs,
    ← hmp.setLIntegral_comp_preimage hs hG]
  refine lintegral_congr fun x => ?_
  simp only [hf1]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity), Finset.prod_mul_distrib,
    ← Real.exp_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin, EuclideanSpace.norm_sq_eq,
    ← Finset.sum_neg_distrib, pow_one, inv_pow]

theorem measurePreserving_restrict_castLE {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {N n : ℕ} (h : N ≤ n) :
    MeasurePreserving (fun (y : Fin n → α) (j : Fin N) => y (Fin.castLE h j))
      (Measure.pi fun _ => μ) (Measure.pi fun _ => μ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  have hr : Measurable fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j) :=
    Measurable.of_eval fun j => measurable_pi_apply _
  refine ⟨hr, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply hr (MeasurableSet.univ_pi hs)]
  have hpre : (fun (y : Fin (N + m) → α) (j : Fin N) => y (Fin.castLE h j)) ⁻¹' univ.pi s =
      univ.pi (Fin.append s fun _ : Fin m => (univ : Set α)) := by
    ext y
    simp only [mem_preimage, mem_univ_pi]
    constructor
    · intro hy i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.append_left]; exact hy j
      · rw [Fin.append_right]; exact mem_univ _
    · intro hy j
      have := hy (Fin.castAdd m j)
      rwa [Fin.append_left] at this
  rw [hpre, Measure.pi_pi, Fin.prod_univ_add]
  simp [Fin.append_left, Fin.append_right]

theorem measurePreserving_firstCoords_gaussProb :
    ∀ (N n : ℕ) (h : N ≤ n), MeasurePreserving (firstCoords h) (gaussProb n) (gaussProb N) := by
  intro N n h
  haveI := isProbabilityMeasure_complexGaussian_one
  have hofn : Measurable (WithLp.ofLp (p := 2) (V := Fin n → ℂ)) :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin n)).measurable
  have hofN : Measurable (WithLp.ofLp (p := 2) (V := Fin N → ℂ)) :=
    (GlobalTheory.volume_preserving_ofLp_complex (Fin N)).measurable
  have htoN : Measurable (WithLp.toLp 2 : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N)) := by fun_prop
  have e1 : MeasurePreserving (WithLp.ofLp (p := 2) (V := Fin n → ℂ)) (gaussProb n)
      (Measure.pi fun _ : Fin n => GlobalTheory.complexGaussian ℂ 1) := ⟨hofn, map_ofLp_gaussProb n⟩
  have e3 : MeasurePreserving (WithLp.toLp 2 : (Fin N → ℂ) → EuclideanSpace ℂ (Fin N))
      (Measure.pi fun _ : Fin N => GlobalTheory.complexGaussian ℂ 1) (gaussProb N) := by
    refine ⟨htoN, ?_⟩
    rw [← map_ofLp_gaussProb N, Measure.map_map htoN hofN]
    convert Measure.map_id
    funext x
    rfl
  exact e3.comp ((measurePreserving_restrict_castLE _ h).comp e1)

end GlobalTheory.GaussMarginal
end
end
end

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.FormHeightGen

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.UnitProductCombination.XB

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop GlobalTheory.ChowHt

theorem mean_incl (B N n δ : ℕ) (f : MvPolynomial (Fin B × Fin N) ℂ) (hN : 0 < N)
    (hNn : N ≤ n) (hf : f ≠ 0) (hm : IsMultiHomogeneous (fun _ => δ) f) :
    blockSphereMean B n (linSubst (Matrix.of fun (j : Fin N) (k : Fin n) =>
        if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) f) =
      blockSphereMean B N f + (B : ℝ) * δ * ((harmonic (N - 1) : ℝ) - (harmonic (n - 1) : ℝ)) / 2 := by
  have hn : 0 < n := lt_of_lt_of_le hN hNn
  rw [linSubst_incl hNn]
  set e : Fin B × Fin N → Fin B × Fin n := fun p => (p.1, Fin.castLE hNn p.2) with he
  have heinj : Function.Injective e := by
    intro p q hpq
    simp only [he, Prod.mk.injEq] at hpq
    exact Prod.ext hpq.1 (Fin.castLE_injective hNn hpq.2)
  set g := rename e f with hgdef
  have hg : g ≠ 0 := fun h0 => hf (rename_injective e heinj (by rw [← hgdef, h0, map_zero]))
  have hgm : IsMultiHomogeneous (fun _ => δ) g := isMultiHomogeneous_rename_castLE hNn _ f hm
  have hIn := (gauss_blockMean hn δ g hg hgm).2
  have hIN := (gauss_blockMean hN δ f hf hm).2
  have : IsProbabilityMeasure (gaussProb N) := isProbabilityMeasure_gaussProb hN
  have hproj : MeasurePreserving (fun (x : Fin B → EuclideanSpace ℂ (Fin n)) b => firstCoords hNn (x b))
      (Measure.pi fun _ => gaussProb n) (Measure.pi fun _ => gaussProb N) :=
    measurePreserving_pi _ _ fun _ => GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb N n hNn
  have hev : ∀ x : Fin B → EuclideanSpace ℂ (Fin n),
      eval (fun p => WithLp.ofLp (x p.1) p.2) g =
        eval (fun p => WithLp.ofLp (firstCoords hNn (x p.1)) p.2) f := by
    intro x
    rw [hgdef, eval_rename]
    rfl
  have hmeas : Measurable fun y : Fin B → EuclideanSpace ℂ (Fin N) =>
      Real.log ‖eval (fun p => WithLp.ofLp (y p.1) p.2) f‖ := by
    refine Real.measurable_log.comp (Continuous.measurable ?_)
    exact continuous_norm.comp ((continuous_eval f).comp (by fun_prop))
  have hchange : ∫ x, Real.log ‖eval (fun p => WithLp.ofLp (x p.1) p.2) g‖
        ∂(Measure.pi fun _ => gaussProb n) =
      ∫ y, Real.log ‖eval (fun p => WithLp.ofLp (y p.1) p.2) f‖
        ∂(Measure.pi fun _ => gaussProb N) := by
    simp_rw [hev]
    rw [← hproj.map_eq, integral_map hproj.measurable.aemeasurable hmeas.aestronglyMeasurable]
  rw [hchange, hIN] at hIn
  have hr := radRatio_sub hN hn
  linear_combination hIn.symm + (B : ℝ) * δ * hr

theorem exists_unitary {N m : ℕ} (Q : Matrix (Fin N) (Fin m) ℂ)
    (hQ : ∀ z : Fin N → ℂ, ∑ a, ‖∑ i, Q i a * z i‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) :
    N ≤ m ∧ ∃ U : Matrix (Fin m) (Fin m) ℂ,
      (∀ x : EuclideanSpace ℂ (Fin m), ‖Matrix.toEuclideanLin U x‖ = ‖x‖) ∧
      Q = (Matrix.of fun (j : Fin N) (k : Fin m) => if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) * U := by
  let T : EuclideanSpace ℂ (Fin N) →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin m) :=
    ⟨Matrix.toEuclideanLin Q.transpose, fun z => by
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      exact congrArg _ (hQ z.ofLp)⟩
  have hle : N ≤ m := by
    have := LinearMap.finrank_le_finrank_of_injective (f := T.toLinearMap) T.injective
    simpa using this
  refine ⟨hle, ?_⟩
  have ho : Orthonormal ℂ (T ∘ EuclideanSpace.basisFun (Fin N) ℂ) :=
    (EuclideanSpace.basisFun (Fin N) ℂ).orthonormal.comp_linearIsometry T
  let v : Fin m → EuclideanSpace ℂ (Fin m) := fun k =>
    if h : (k : ℕ) < N then T (EuclideanSpace.basisFun (Fin N) ℂ ⟨k, h⟩) else 0
  have hv : Orthonormal ℂ (({k : Fin m | (k : ℕ) < N}).restrict v) := by
    have h1 := ho.comp (fun k : {k : Fin m | (k : ℕ) < N} => (⟨k.1, k.2⟩ : Fin N))
      fun a b h => Subtype.ext (Fin.ext (congrArg Fin.val h :))
    convert h1 using 1
    funext k
    exact dif_pos k.2
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq (by simp)
  refine ⟨Matrix.of fun k a => b k a, fun x => ?_, ?_⟩
  · let x' : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 fun a => starRingEnd ℂ (x a)
    have h1 := b.sum_sq_norm_inner_right x'
    have h2 : ‖x'‖ = ‖x‖ := by
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      simp [x']
    rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq (norm_nonneg x), ← h2, ← h1]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [← Complex.norm_conj]
    congr 1
    change starRingEnd ℂ (∑ a, b k a * x a) = _

    simp only [PiLp.inner_apply, RCLike.inner_apply, map_sum, map_mul, x']
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  · ext j a
    rw [Matrix.mul_apply, Fintype.sum_eq_single (Fin.castLE hle j)]
    · have hj : ((Fin.castLE hle j : Fin m) : ℕ) < N := j.2
      simp only [Matrix.of_apply, Fin.val_castLE, if_true, one_mul]
      rw [hb _ hj]
      simp only [v]
      rw [dif_pos hj]
      change Q j a = ∑ i, Q i a * (EuclideanSpace.basisFun (Fin N) ℂ j) i
      simp [EuclideanSpace.basisFun_apply, Pi.single_apply]
    · intro k hk
      have hne : (j : ℕ) ≠ (k : ℕ) := fun he => hk (Fin.ext he.symm)
      simp [hne]

theorem mean_gen {B N m δ : ℕ} (hN : 0 < N) (G : Matrix (Fin N) (Fin m) ℂ) {A : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.det ≠ 0) (M : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ x : Fin N → ℂ, ∑ a, ‖∑ k, M k a * ∑ j, G j k * x j‖ ^ 2 = GlobalTheory.Adelic.archSize A x ^ 2)
    {f : MvPolynomial (Fin B × Fin N) ℂ} (hf : f ≠ 0) (hm : IsMultiHomogeneous (fun _ => δ) f) :
    blockSphereMean B m (linSubst M (linSubst G f)) + (B : ℝ) * δ * (harmonic (m - 1) : ℝ) / 2 =
      blockSphereMean B N (linSubst A f) + (B : ℝ) * δ * (harmonic (N - 1) : ℝ) / 2 := by
  obtain ⟨hle, U, hU, hQ⟩ := exists_unitary (A⁻¹ * (G * M)) fun z => by
    have h1 := h (Matrix.vecMul z A⁻¹)
    rw [GlobalTheory.Adelic.archSize, Real.sq_sqrt (by positivity)] at h1
    have e1 : ∀ a, ∑ k, M k a * ∑ j, G j k * Matrix.vecMul z A⁻¹ j = ∑ i, (A⁻¹ * (G * M)) i a * z i := fun a => by
      have := congrFun (Matrix.vecMul_vecMul z A⁻¹ (G * M)) a
      rw [← Matrix.vecMul_vecMul] at this
      simp only [Matrix.vecMul, dotProduct] at this ⊢
      simp only [mul_comm (M _ a), mul_comm (G _ _), mul_comm _ (z _)]
      exact this
    have e2 : ∀ i, ∑ j, A j i * Matrix.vecMul z A⁻¹ j = z i := fun i => by
      have := congrFun (Matrix.vecMul_vecMul z A⁻¹ A) i
      rw [Matrix.nonsing_inv_mul _ hA.isUnit, Matrix.vecMul_one] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    simpa only [e1, e2] using h1
  have e : G * M = A * (Matrix.of fun (j : Fin N) (k : Fin m) => if (j : ℕ) = (k : ℕ) then (1 : ℂ) else 0) * U := by
    rw [Matrix.mul_assoc, ← hQ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA.isUnit, Matrix.one_mul]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  rw [GlobalTheory.HeightUnique.linSubst_linSubst, e, ← GlobalTheory.HeightUnique.linSubst_linSubst,
    GlobalTheory.SphereMeanFrame.blockSphereMean_linSubst U hU, ← GlobalTheory.HeightUnique.linSubst_linSubst,
    mean_incl B N (n + 1) δ _ hN hle (GlobalTheory.HeightUnique.linSubst_ne_zero (A.mul_nonsing_inv hA.isUnit) hf)
      (GlobalTheory.HeightUnique.linSubst_homog _ hm)]
  ring

end PositivityTheory.UnitarySelfGeneration.UnitProductCombination.XB

end

open MvPolynomial NumberField GlobalTheory.ChowHt GlobalTheory.CompHt

theorem PositivityTheory.UnitarySelfGeneration.UnitProductCombination.formHeight_gen {K : Type} [Field K] [NumberField K] {B N m δ : ℕ} (hN : 0 < N)
    (g : Matrix (Fin N) (Fin m) K) (hg : Submodule.span K (Set.range g.col) = ⊤)
    (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hA : ∀ σ, (A σ).det ≠ 0)
    (Mt : (K →+* ℂ) → Matrix (Fin m) (Fin m) ℂ)
    (hMt : ∀ (σ : K →+* ℂ) (x : Fin N → ℂ), ∑ a, ‖∑ k, Mt σ k a * ∑ j, σ (g j k) * x j‖ ^ 2 =
      GlobalTheory.Adelic.archSize (A σ) x ^ 2)
    {Φ : MvPolynomial (Fin B × Fin N) K} (h0 : Φ ≠ 0) (hΦ : ReciprocityTheory.MultiplicativeHeights.IsMultiHomogeneous (fun _ => δ) Φ) :
    formHeight δ (1 : Matrix (Fin m) (Fin m) K) Mt (linSubst g Φ) = formHeight δ g A Φ := by
  unfold formHeight
  rw [GlobalTheory.HeightUnique.linSubst_one]
  congr 2
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [GlobalTheory.ImageHeightUnique.map_linSubst]
  exact PositivityTheory.UnitarySelfGeneration.UnitProductCombination.XB.mean_gen hN (g.map σ) (hA σ) (Mt σ) (hMt σ)
    (fun h => h0 (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero])))
    (ReciprocityTheory.MultiplicativeHeights.isMultiHomogeneous_map_ring _ Φ hΦ σ)
end
end
