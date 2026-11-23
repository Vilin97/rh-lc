module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.DensOn
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExpB
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.ConjTransposeEqOfInG
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExpC

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def sg (ε : Fin n → Bool) (a : Fin n) : ℂ := if ε a then 1 else -1

theorem inG_iff_entry {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ} :
    inG ε X ↔ ∀ i j, star (X j i) * sg ε j + sg ε i * X i j = 0 := by
  unfold inG Jm sg
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    rwa [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply] at this
  · intro h
    ext i j
    rw [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
      Matrix.zero_apply]
    exact h i j

theorem gMat_inG {ε : Fin n → Bool} (s : GCo ε) : inG ε (gMat s) := by
  rw [inG_iff_entry]
  intro i j
  simp only [gMat, Matrix.add_apply, kMat, pmat, sg]
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : ¬ j < i := lt_asymm h
    have h2 : i ≠ j := ne_of_lt h
    by_cases he : ε i = ε j
    · simp [h, h1, h2, h2.symm, he]
    · have he' : ε j ≠ ε i := Ne.symm he
      simp [h, h1, h2, h2.symm, he, he']
      rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>
        rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢
  · apply Complex.ext <;> simp <;> split_ifs <;> simp
  · have h1 : ¬ i < j := lt_asymm h
    have h2 : j ≠ i := ne_of_lt h
    by_cases he : ε i = ε j
    · simp [h, h1, h2, h2.symm, he]
      split_ifs <;> ring
    · have he' : ε j ≠ ε i := Ne.symm he
      simp [h, h1, h2, h2.symm, he, he']
      rcases Bool.eq_false_or_eq_true (ε i) with hi | hi <;>
        rcases Bool.eq_false_or_eq_true (ε j) with hj | hj <;> simp [hi, hj] at he ⊢

def gCo (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) : GCo ε :=
  ((fun a => (Z a a).im, fun p => Z p.1.1 p.1.2), fun p => Z p.1.1 p.1.2)

theorem gCo_gMat {ε : Fin n → Bool} (s : GCo ε) : gCo ε (gMat s) = s := by
  obtain ⟨⟨w, x⟩, z⟩ := s
  refine Prod.ext (Prod.ext ?_ ?_) ?_
  · funext a
    simp [gCo, gMat, kMat, pmat]
  · funext p
    obtain ⟨⟨a, b⟩, hab, he⟩ := p
    have h1 : a ≠ b := (ne_of_lt hab).symm
    have h2 : ¬ a < b := lt_asymm hab
    simp [gCo, gMat, kMat, pmat, h1, hab, he, h2]
  · funext p
    obtain ⟨⟨a, b⟩, hab, he⟩ := p
    have h1 : a ≠ b := (ne_of_lt hab).symm
    have h2 : ¬ a < b := lt_asymm hab
    simp [gCo, gMat, kMat, pmat, h1, hab, he, h2]

theorem gMat_gCo {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) :
    gMat (gCo ε Z) = Z := by
  rw [inG_iff_entry] at hZ
  ext i j
  have hij := hZ i j
  simp only [gMat, Matrix.add_apply, kMat, pmat, gCo, sg] at hij ⊢
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : ¬ j < i := lt_asymm h
    have h2 : i ≠ j := ne_of_lt h
    cases hi : ε i <;> cases hj : ε j <;> simp [h, h1, h2, hi, hj] at hij ⊢ <;>
      first | linear_combination hij | linear_combination -hij
  · apply Complex.ext <;> simp
    · have := congrArg Complex.re hij
      cases hi : ε i <;> simp [hi] at this <;> linarith
  · have h1 : ¬ i < j := lt_asymm h
    have h2 : j ≠ i := ne_of_lt h
    simp [h, h1, h2.symm]
    split_ifs <;> simp

end ReciprocityTheory.ChartRestriction.DS.HExp
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExpD

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.HExp

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem gMat_add {ε : Fin n → Bool} (s t : GCo ε) : gMat (s + t) = gMat s + gMat t := by
  ext a b
  simp only [gMat, Matrix.add_apply]
  simp only [kMat, pmat, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  split_ifs <;> (try simp only [Complex.ofReal_add, star_add, mul_add, neg_add, add_zero]) <;>
    (try ring)

theorem gMat_smul {ε : Fin n → Bool} (c : ℝ) (s : GCo ε) : gMat (c • s) = (RingHom.id ℝ c) • gMat s := by
  ext a b
  simp only [gMat, RingHom.id_apply, Matrix.add_apply, Matrix.smul_apply]
  simp only [kMat, pmat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
  split_ifs <;> (try simp only [Complex.real_smul, Complex.ofReal_mul, star_mul', Complex.star_def,
    Complex.conj_ofReal, smul_add, smul_zero, smul_neg, add_zero, mul_neg]) <;>
    (try simp only [smul_eq_mul, Complex.ofReal_mul]) <;> (try ring_nf)

def gL (ε : Fin n → Bool) : GCo ε →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := gMat
  map_add' := gMat_add
  map_smul' := gMat_smul

theorem gL_injective (ε : Fin n → Bool) : Function.Injective (gL ε) := by
  intro s t h
  have h' : gMat s = gMat t := h
  rw [← gCo_gMat s, ← gCo_gMat t, h']

abbrev gV (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) := LinearMap.range (gL ε)

def gE (ε : Fin n → Bool) : GCo ε ≃ₗ[ℝ] gV ε := LinearEquiv.ofInjective (gL ε) (gL_injective ε)

def ujMat (ε : Fin n → Bool) : UJ ε →* Matrix (Fin n) (Fin n) ℂ :=
  (Units.coeHom _).comp (UJ ε).subtype

theorem ujMat_apply (ε : Fin n → Bool) (g : UJ ε) : ujMat ε g = toM g := rfl

section Normed

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_inUJ_small (ε : Fin n → Bool) : ∀ᶠ Z in 𝓝 (0 : Matrix (Fin n) (Fin n) ℂ),
    inUJ ε (NormedSpace.exp Z) → inG ε Z := by
  unfold inG
  have hd : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ) 0 := hasStrictFDerivAt_exp_zero
  obtain ⟨s, hs, hap⟩ := hd.approximates_deriv_on_nhds (c := 1 / 2) (Or.inr (by norm_num))

  have hinj : ∀ x ∈ s, ∀ y ∈ s, NormedSpace.exp x = NormedSpace.exp y → x = y := by
    intro x hx y hy hxy
    have h := hap x hx y hy
    rw [hxy, sub_self] at h
    change ‖0 - (x - y)‖ ≤ ((1 / 2 : NNReal) : ℝ) * ‖x - y‖ at h
    rw [zero_sub, norm_neg, NNReal.coe_div, NNReal.coe_one, NNReal.coe_two] at h
    have h0 : ‖x - y‖ = 0 := le_antisymm (by linarith [norm_nonneg (x - y)]) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have hJJ : Jm ε * Jm ε = 1 := by
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := ⟨⟨Jm ε, Jm ε, hJJ, hJJ⟩, rfl⟩
  have hc1 : Tendsto (fun Z : Matrix (Fin n) (Fin n) ℂ => Jm ε * Zᴴ * Jm ε) (𝓝 0) (𝓝 0) := by
    have hcont : Continuous (fun Z : Matrix (Fin n) (Fin n) ℂ => Jm ε * Zᴴ * Jm ε) :=
      (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
    simpa using hcont.tendsto 0
  have hc2 : Tendsto (fun Z : Matrix (Fin n) (Fin n) ℂ => -Z) (𝓝 0) (𝓝 0) := by
    simpa using (continuous_neg.tendsto (0 : Matrix (Fin n) (Fin n) ℂ))
  filter_upwards [hc1.eventually hs, hc2.eventually hs] with Z h1 h2 hU
  unfold inUJ at hU
  have hE : NormedSpace.exp (Jm ε * Zᴴ * Jm ε) = NormedSpace.exp (-Z) := by
    have hL : Jm ε * (NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z = 1 := by
      calc Jm ε * (NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z
          = Jm ε * ((NormedSpace.exp Z)ᴴ * Jm ε * NormedSpace.exp Z) := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hU, hJJ]
    rw [show Jm ε * Zᴴ * Jm ε = Jm ε * Zᴴ * (Jm ε)⁻¹ by rw [hJi], Matrix.exp_conj _ _ hJu, hJi,
      Matrix.exp_conjTranspose, Matrix.exp_neg]
    exact (Matrix.inv_eq_left_inv hL).symm
  have hZ := hinj _ h1 _ h2 hE
  calc Zᴴ * Jm ε + Jm ε * Z = Jm ε * (Jm ε * Zᴴ * Jm ε) + Jm ε * Z := by
        simp only [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
    _ = 0 := by rw [hZ, Matrix.mul_neg, neg_add_cancel]

def ujChart (ε : Fin n → Bool) : Chart (gV ε) (UJ ε) where
  mat := ujMat ε
  emb := (isClosedEmbedding_toM ε).isEmbedding
  H1 := fun X => by
    obtain ⟨s, hs⟩ := X.2
    have h : NormedSpace.exp (gMat s) ∈ Set.range (fun g : UJ ε => toM g) := by
      rw [range_toM]
      have := exp_smul_mem_UJset (gMat_inG s) 1
      simp only [Complex.ofReal_one, one_smul] at this
      exact this
    obtain ⟨g, hg⟩ := h
    refine ⟨g, ?_⟩
    rw [ujMat_apply, ← hs]
    exact hg
  H2 := by
    filter_upwards [exp_inUJ_small ε] with Z hZ hg
    obtain ⟨g, hg⟩ := hg
    have h1 : inUJ ε (ujMat ε g) := g.2
    rw [hg] at h1
    exact ⟨gCo ε Z, gMat_gCo (hZ h1)⟩

end Normed

end ReciprocityTheory.ChartRestriction.DS.HExp
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.HaarExp

section

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HExp

variable {n : ℕ}

section Normed

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem haar_exp_density {ε : Fin n → Bool} (μ : Measure (UJ ε)) [μ.IsHaarMeasure] :
    ∃ d : ℝ, 0 < d ∧ DensOn (fun S => μ (expSet S)) d := by
  letI mV : MeasurableSpace (gV ε) := borel _
  haveI : BorelSpace (gV ε) := ⟨rfl⟩
  let eC : GCo ε ≃L[ℝ] gV ε := (gE ε).toContinuousLinearEquiv
  let lam : Measure (gV ε) := Measure.map eC volume
  haveI : (volume : Measure (KCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  haveI : (volume : Measure (GCo ε)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  have hlamH : lam.IsAddHaarMeasure := eC.isAddHaarMeasure_map volume
  obtain ⟨c, hc0, hct, hup, hdown⟩ := (ujChart ε).exists_density_unif' inferInstance mV ⟨rfl⟩ _
    inferInstance inferInstance μ inferInstance lam (by exact hlamH)
  have himg : ∀ S : Set (GCo ε), (ujChart ε).img (eC '' S) = expSet S := by
    intro S
    ext g
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, h⟩
      exact ⟨s, hs, h⟩
    · rintro ⟨s, hs, h⟩
      exact ⟨eC s, ⟨s, hs, rfl⟩, h⟩
  have hmeas : ∀ S : Set (GCo ε), MeasurableSet S → MeasurableSet (eC '' S) := fun S hS =>
    eC.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hS
  have hlam : ∀ S : Set (GCo ε), MeasurableSet S → lam (eC '' S) = volume S := by
    intro S hS
    rw [Measure.map_apply eC.continuous.measurable (hmeas S hS), Set.preimage_image_eq S eC.injective]
  have hsmall : ∀ δ > 0, ∃ δ' > 0, ∀ S : Set (GCo ε), (∀ s ∈ S, ‖s‖ < δ') →
      eC '' S ⊆ ball (0 : gV ε) δ := by
    intro δ hδ
    obtain ⟨δ', hδ', h⟩ := Metric.continuousAt_iff.mp (eC.continuous.continuousAt (x := 0)) δ hδ
    refine ⟨δ', hδ', fun S hS => ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    have := h (x := s) (by simpa using hS s hs)
    simpa using this
  set d := c.toReal with hd
  have hdpos : 0 < d := ENNReal.toReal_pos hc0 hct
  have hc : c = ENNReal.ofReal d := (ENNReal.ofReal_toReal hct).symm
  refine ⟨d, hdpos, fun η hη => ?_⟩
  have hU : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      μ (expSet S) ≤ ENNReal.ofReal ((1 + η) * d) * volume S := by
    obtain ⟨δ, hδ, h⟩ := hup (Real.toNNReal ((1 + η) * d)) (by
      rw [hc]
      show ENNReal.ofReal d < ENNReal.ofReal ((1 + η) * d)
      rw [ENNReal.ofReal_lt_ofReal_iff (by positivity)]
      nlinarith)
    obtain ⟨δ', hδ', h'⟩ := hsmall δ hδ
    refine ⟨δ', hδ', fun S hS hSδ => ?_⟩
    have := h (eC '' S) (hmeas S hS) (h' S hSδ)
    rw [himg, hlam S hS] at this
    exact this
  have hL : ∃ δ > 0, ∀ S : Set (GCo ε), MeasurableSet S → (∀ s ∈ S, ‖s‖ < δ) →
      ENNReal.ofReal ((1 - η) * d) * volume S ≤ μ (expSet S) := by
    by_cases hη1 : (1 - η) * d ≤ 0
    · refine ⟨1, one_pos, fun S _ _ => ?_⟩
      rw [ENNReal.ofReal_of_nonpos hη1, zero_mul]
      exact bot_le
    · have hη1' : 0 < (1 - η) * d := not_le.mp hη1
      obtain ⟨δ, hδ, h⟩ := hdown (Real.toNNReal ((1 - η) * d)) (by
        rw [hc]
        show ENNReal.ofReal ((1 - η) * d) < ENNReal.ofReal d
        rw [ENNReal.ofReal_lt_ofReal_iff hdpos]
        nlinarith)
      obtain ⟨δ', hδ', h'⟩ := hsmall δ hδ
      refine ⟨δ', hδ', fun S hS hSδ => ?_⟩
      have := h (eC '' S) (hmeas S hS) (h' S hSδ)
      rw [himg, hlam S hS] at this
      exact this
  obtain ⟨δ1, hδ1, h1⟩ := hU
  obtain ⟨δ2, hδ2, h2⟩ := hL
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun S hS hSδ => ⟨?_, ?_⟩⟩
  · exact h1 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_left _ _)
  · exact h2 S hS fun s hs => lt_of_lt_of_le (hSδ s hs) (min_le_right _ _)

end Normed

end ReciprocityTheory.ChartRestriction.DS
end
end
end
