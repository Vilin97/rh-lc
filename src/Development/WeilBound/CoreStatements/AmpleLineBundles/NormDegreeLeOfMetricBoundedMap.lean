module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
public import GroundTheory.HeightsAndTheta.Heights.ArithDegree
public import Development.WeilBound.CoreStatements.AmpleLineBundles.SpanLeOfMem
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PNormComparison

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights
open scoped ComplexOrder MatrixOrder

noncomputable section

theorem re_det_le_of_posSemidef_smul_sub {n : Type*} [Fintype n] [DecidableEq n]
    {G G' : Matrix n n ℂ} (hG : G.PosDef) (hG' : G'.PosSemidef) (c : ℝ)
    (hc : (c • G - G').PosSemidef) : (det G').re ≤ c ^ Fintype.card n * (det G).re := by
  obtain ⟨P, hP⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg
  rw [star_eq_conjTranspose] at hP
  have hdetG : det G = star (det P) * det P := by
    rw [hP, det_mul, det_conjTranspose]
  have hPne : det P ≠ 0 := by
    intro h0
    have := hG.det_pos.ne'
    rw [hdetG, h0, mul_zero] at this
    exact this rfl
  have hU : IsUnit (det P) := isUnit_iff_ne_zero.mpr hPne
  set Q := P⁻¹ with hQ
  have hQP : Q * P = 1 := nonsing_inv_mul P hU
  have hPQ : P * Q = 1 := mul_nonsing_inv P hU
  set B := Qᴴ * G' * Q with hB
  have hBpsd : B.PosSemidef := hG'.conjTranspose_mul_mul_same Q
  have hG'eq : G' = Pᴴ * B * P := by
    calc G' = (Q * P)ᴴ * G' * (Q * P) := by rw [hQP, conjTranspose_one, one_mul, mul_one]
      _ = Pᴴ * B * P := by rw [conjTranspose_mul, hB]; simp only [Matrix.mul_assoc]
  have hQGQ : Qᴴ * G * Q = 1 := by
    calc Qᴴ * G * Q = (P * Q)ᴴ * (P * Q) := by
          rw [hP, conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPQ, conjTranspose_one, one_mul]
  have hCB : (c • (1 : Matrix n n ℂ) - B).PosSemidef := by
    have := hc.conjTranspose_mul_mul_same Q
    rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, hQGQ] at this
  have heig : ∀ i, hBpsd.1.eigenvalues i ≤ c := by
    intro i
    set u : n → ℂ := ⇑(hBpsd.1.eigenvectorBasis i)
    have h1 := hCB.re_dotProduct_nonneg u
    have hu : star u ⬝ᵥ u = 1 := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hBpsd.1.eigenvectorBasis.orthonormal.1 i]
      simp
    rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul, hu, map_sub,
      ← hBpsd.1.eigenvalues_eq i] at h1
    simpa using h1
  have hdetB : (det B).re ≤ c ^ Fintype.card n := by
    rw [hBpsd.1.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
    change (((∏ i, hBpsd.1.eigenvalues i : ℝ) : ℂ)).re ≤ _
    rw [Complex.ofReal_re]
    calc ∏ i, hBpsd.1.eigenvalues i ≤ ∏ _i : n, c :=
          Finset.prod_le_prod₀ (fun i _ ↦ hBpsd.eigenvalues_nonneg i) (fun i _ ↦ heig i)
      _ = c ^ Fintype.card n := by rw [Finset.prod_const, Finset.card_univ]
  have hstar : star (det P) * det P = ((Complex.normSq (det P) : ℝ) : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj (det P)
  have hdetG' : det G' = det B * ((Complex.normSq (det P) : ℝ) : ℂ) := by
    rw [hG'eq, det_mul, det_mul, det_conjTranspose, ← hstar]; ring
  rw [hdetG', hdetG, hstar, Complex.re_mul_ofReal, Complex.ofReal_re]
  exact mul_le_mul_of_nonneg_right hdetB (Complex.normSq_nonneg _)

variable {K : Type*} [Field K] [NumberField K]

theorem gramDet_le_of_norm_le {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h h' : HermitianMetric K E) (σ : K →+* ℂ) (A : ℝ)
    (hA : ∀ x : Fibre σ E, ‖FibreSpace.equiv h' σ x‖ ≤ A * ‖FibreSpace.equiv h σ x‖)
    {r : ℕ} {s : Fin r → E} (hs : LinearIndependent (𝓞 K) s) :
    gramDet h' σ s ≤ (max A 0 ^ 2) ^ r * gramDet h σ s := by
  let L : FibreSpace h σ →ₗ[ℂ] FibreSpace h' σ :=
    (FibreSpace.equiv h' σ).toLinearMap ∘ₗ (FibreSpace.equiv h σ).symm.toLinearMap
  have hL : ∀ y, ‖L y‖ ≤ A * ‖y‖ := by
    intro y
    have := hA ((FibreSpace.equiv h σ).symm y)
    rwa [LinearEquiv.apply_symm_apply] at this
  let f := L.mkContinuous A hL
  have hf : ‖f‖ ≤ max A 0 := LinearMap.mkContinuous_norm_le' L hL
  set v : Fin r → FibreSpace h σ := fun i ↦ fibreVec h σ (s i)
  have hfv : (⇑f ∘ v) = fun i ↦ fibreVec h' σ (s i) := rfl
  have hpsd := posSemidef_opNorm_smul_gram_sub_gram v f
  rw [hfv] at hpsd
  have hmain := re_det_le_of_posSemidef_smul_sub
    (posDef_gram_of_linearIndependent (linearIndependent_fibreVec h σ hs))
    (posSemidef_gram ℂ _) _ hpsd
  rw [Fintype.card_fin] at hmain
  have hg : 0 < gramDet h σ s := gramDet_pos h σ hs
  calc gramDet h' σ s ≤ (‖f‖ ^ 2) ^ r * gramDet h σ s := hmain
    _ ≤ (max A 0 ^ 2) ^ r * gramDet h σ s := by
      gcongr

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
end
end

-- Source module: Development.WeilBound.CoreStatements.AmpleLineBundles.NormDegreeLeOfMetricBoundedMap

section

@[expose] public section

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

variable {K : Type} [Field K] [NumberField K]

theorem norm_sq_eq_sqAt (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (x : Fibre σ E.carrier) :
    ‖FibreSpace.equiv E.metric σ x‖ ^ 2 = sqAt E σ x := by
  rw [@norm_sq_eq_re_inner ℂ]
  rfl

theorem gram_map_le (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ)
    (hφ : Function.Injective φ) (hc : 0 < c) (σ : K →+* ℂ)
    (h : ∀ x : Fibre σ E.carrier, sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x)
    {r : ℕ} {s : Fin r → E.carrier} (hs : LinearIndependent (𝓞 K) s) :
    gramDet E'.metric σ (fun i => φ (s i)) ≤ c ^ r * gramDet E.metric σ s := by
  have hnorm : ∀ x : Fibre σ E.carrier,
      ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ≤ Real.sqrt c * ‖FibreSpace.equiv E.metric σ x‖ := by
    intro x
    have h1 : ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ^ 2 = sqAt E' σ (φ.lTensor (ComplexAt σ) x) := by
      rw [← CoverDenseAlt.norm_sq_eq_sqAt, @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, FibreSpace.inner_equiv,
        FibreSpace.inner_equiv, HermitianMetric.comap_inner E'.metric φ hφ σ]
      rfl
    have h2 := h x
    rw [← h1, ← CoverDenseAlt.norm_sq_eq_sqAt] at h2
    have h3 : ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ^ 2 ≤
        (Real.sqrt c * ‖FibreSpace.equiv E.metric σ x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]
      exact h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) two_ne_zero).mp h3
  have key := LatticeLemmas.gramDet_le_of_norm_le E.metric (E'.metric.comap φ hφ) σ (Real.sqrt c) hnorm hs
  rw [gramDet_comap] at key
  rwa [max_eq_left (Real.sqrt_nonneg c), Real.sq_sqrt hc.le] at key

theorem normDeg_map (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ)
    (hφ : Function.Injective φ) (hc : 0 < c)
    (h : ∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier),
      sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) (F : Submodule (𝓞 K) E.carrier) :
    E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c := by
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := F) (n := E.rank F) le_rfl
  have hv : LinearIndependent (𝓞 K) (fun i => (s i : E.carrier)) := hs.map' F.subtype F.ker_subtype
  have hw : LinearIndependent (𝓞 K) (fun i => φ (s i : E.carrier)) :=
    hv.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  let e := Submodule.equivMapOfInjective φ hφ F
  let t : Fin (E.rank F) → F.map φ := fun i => e (s i)
  have ht : LinearIndependent (𝓞 K) t := hs.map' e.toLinearMap e.ker
  have hrank : E'.rank (F.map φ) = E.rank F := (LinearEquiv.finrank_eq e).symm
  have hdF := E.degree_eq_of_linearIndependent F hs (Fintype.card_fin _)
  have hdG : E'.degree (F.map φ) = Real.log (Nat.card (F.map φ ⧸ Submodule.span (𝓞 K) (Set.range t))) -
      1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet E'.metric σ fun i => φ (s i : E.carrier)) :=
    E'.degree_eq_of_linearIndependent (F.map φ) ht (by rw [Fintype.card_fin, hrank])
  have hcard : Nat.card (F.map φ ⧸ Submodule.span (𝓞 K) (Set.range t)) =
      Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    refine (Nat.card_congr (Submodule.Quotient.equiv _ _ e ?_).toEquiv).symm
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hgram : ∀ σ : K →+* ℂ, Real.log (gramDet E'.metric σ fun i => φ (s i : E.carrier)) ≤
      E.rank F * Real.log c + Real.log (gramDet E.metric σ fun i => (s i : E.carrier)) := by
    intro σ
    have hle := gram_map_le E E' φ c hφ hc σ (h σ) hv
    have hpos' := gramDet_pos E'.metric σ hw
    have hpos := gramDet_pos E.metric σ hv
    calc _ ≤ Real.log (c ^ E.rank F * gramDet E.metric σ fun i => (s i : E.carrier)) :=
          Real.log_le_log hpos' hle
      _ = _ := by rw [Real.log_mul (pow_pos hc _).ne' hpos.ne', Real.log_pow]
  have hsum := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hgram σ
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card K ℂ,
    nsmul_eq_mul] at hsum
  have hq : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold HermitianBundle.normDegree
  rw [div_add' _ _ _ hq.ne', div_le_div_iff_of_pos_right hq, hdF, hdG, hcard]
  linarith

theorem normDegree_le_of_metric_bounded_map : ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ), Function.Injective φ → 0 < c → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) → (∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c) ∧ E.slopeMax ≤ E'.slopeMax + ((Real.log c / 2 : ℝ) : EReal) := by
  intro K _ _ E E' φ c hφ hc h
  refine ⟨normDeg_map E E' φ c hφ hc h, iSup₂_le fun F hF => ?_⟩
  have hne : F.map φ ≠ ⊥ := by
    intro h0
    have := rank_map E E' φ hφ F
    rw [h0] at this
    have h1 := rank_pos E hF
    rw [← this] at h1
    simp [HermitianBundle.rank] at h1
  have hle : ((E'.slope (F.map φ) : ℝ) : EReal) ≤ E'.slopeMax := le_iSup₂_of_le (F.map φ) hne le_rfl
  refine le_trans ?_ (add_le_add_left hle _)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hr : (0 : ℝ) < E.rank F := by exact_mod_cast rank_pos E hF
  have hd := normDeg_map E E' φ c hφ hc h F
  unfold HermitianBundle.slope
  rw [rank_map E E' φ hφ, div_add' _ _ _ hr.ne']
  refine div_le_div_of_nonneg_right ?_ hr.le
  linarith

end CoverDenseAlt
end
end
