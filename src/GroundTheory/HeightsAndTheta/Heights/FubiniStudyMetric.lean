module

public import GroundTheory.HeightsAndTheta.Heights.ComplexProjective
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Projectivization.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Geometry.Manifold.StructureGroupoid
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

-- Source module: GroundTheory.HeightsAndTheta.Heights.ProjTopology

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]

instance : TopologicalSpace (ℙ K V) :=
  TopologicalSpace.coinduced (Projectivization.mk' K) inferInstance

namespace ProjTopology

lemma continuous_mk' : Continuous (Projectivization.mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  continuous_coinduced_rng

lemma isOpen_iff {s : Set (ℙ K V)} :
    IsOpen s ↔ IsOpen ((Projectivization.mk' K) ⁻¹' s : Set {v : V // v ≠ 0}) :=
  isOpen_coinduced

lemma continuous_iff {Y : Type*} [TopologicalSpace Y] {g : ℙ K V → Y} :
    Continuous g ↔ Continuous (g ∘ Projectivization.mk' K) :=
  continuous_coinduced_dom

end ProjTopology

instance compactSpace_projectivization_complex (N : ℕ) : CompactSpace (ℙ ℂ (Fin (N + 1) → ℂ)) := by
  have hS : IsCompact (Metric.sphere (0 : Fin (N + 1) → ℂ) 1) := isCompact_sphere 0 1
  have : CompactSpace (Metric.sphere (0 : Fin (N + 1) → ℂ) 1) := isCompact_iff_compactSpace.mp hS
  have hne : ∀ w : Metric.sphere (0 : Fin (N + 1) → ℂ) 1, (w : Fin (N + 1) → ℂ) ≠ 0 := by
    intro w h
    have := w.2
    rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at this
    exact zero_ne_one this
  let g : Metric.sphere (0 : Fin (N + 1) → ℂ) 1 → ℙ ℂ (Fin (N + 1) → ℂ) := fun w =>
    Projectivization.mk' ℂ ⟨w.1, hne w⟩
  have hg : Continuous g :=
    ProjTopology.continuous_mk'.comp (Continuous.subtype_mk continuous_subtype_val _)
  have hsurj : Function.Surjective g := by
    intro v
    induction v using Projectivization.ind with
    | h w hw =>
      have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      refine ⟨⟨(‖w‖⁻¹ : ℂ) • w, ?_⟩, ?_⟩
      · rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, Complex.norm_real, norm_norm,
          inv_mul_cancel₀ hn]
      · change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ w hw
        rw [Projectivization.mk_eq_mk_iff]
        exact ⟨Units.mk0 (‖w‖⁻¹ : ℂ) (inv_ne_zero (by exact_mod_cast hn)), rfl⟩
  refine ⟨?_⟩
  rw [← hsurj.range_eq]
  exact isCompact_range hg

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.FubiniStudyCharts

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ContDiff Manifold
open Topology Set

noncomputable section

variable {N : ℕ}

namespace CP

def chartVec (i : Fin (N + 1)) (z : Fin N → ℂ) : Fin (N + 1) → ℂ := Fin.insertNth i 1 z

@[simp] lemma chartVec_self (i : Fin (N + 1)) (z : Fin N → ℂ) : chartVec i z i = 1 := by
  simp [chartVec]

@[simp] lemma chartVec_succAbove (i : Fin (N + 1)) (z : Fin N → ℂ) (j : Fin N) :
    chartVec i z (i.succAbove j) = z j := by
  simp [chartVec]

lemma chartVec_ne_zero (i : Fin (N + 1)) (z : Fin N → ℂ) : chartVec i z ≠ 0 := by
  intro h
  have := congr_fun h i
  simp at this

lemma contDiff_chartVec_apply (𝕜 : Type*) [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ]
    (i m : Fin (N + 1)) : ContDiff 𝕜 ∞ (fun z : Fin N → ℂ => chartVec i z m) := by
  obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m
  · simp only [chartVec_self]; exact contDiff_const
  · simp only [chartVec_succAbove]
    exact (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : Fin N => ℂ) k).contDiff

lemma continuous_chartVec (i : Fin (N + 1)) : Continuous (chartVec (N := N) i) :=
  continuous_pi fun m => (contDiff_chartVec_apply ℂ i m).continuous

def chartInv (i : Fin (N + 1)) (z : Fin N → ℂ) : CP N :=
  Projectivization.mk ℂ (chartVec i z) (chartVec_ne_zero i z)

lemma continuous_chartInv (i : Fin (N + 1)) : Continuous (chartInv (N := N) i) :=
  ProjTopology.continuous_mk'.comp
    ((continuous_chartVec i).subtype_mk fun z => chartVec_ne_zero i z)

def chartCoord (i : Fin (N + 1)) : CP N → (Fin N → ℂ) :=
  Projectivization.lift (fun v => fun j => v.1 (i.succAbove j) / v.1 i) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ t rfl
    funext j
    have ht : t ≠ 0 := by rintro rfl; simp at ha
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hbi : b i = 0
    · simp [hbi]
    · field_simp)

@[simp] lemma chartCoord_mk (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    chartCoord i (Projectivization.mk ℂ v hv) = fun j => v (i.succAbove j) / v i := rfl

def chartDomain (i : Fin (N + 1)) : Set (CP N) :=
  {x | Projectivization.lift (fun v : {v : Fin (N + 1) → ℂ // v ≠ 0} => v.1 i ≠ 0) (by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ t rfl
    have ht : t ≠ 0 := by rintro rfl; simp at ha
    simp [ht]) x}

@[simp] lemma mk_mem_chartDomain (i : Fin (N + 1)) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ chartDomain i ↔ v i ≠ 0 := Iff.rfl

lemma chartInv_mem (i : Fin (N + 1)) (z : Fin N → ℂ) : chartInv i z ∈ chartDomain i := by
  simp [chartInv]

lemma chartCoord_chartInv (i : Fin (N + 1)) (z : Fin N → ℂ) : chartCoord i (chartInv i z) = z := by
  funext j; simp [chartInv]

lemma chartInv_chartCoord (i : Fin (N + 1)) {x : CP N} (hx : x ∈ chartDomain i) :
    chartInv i (chartCoord i x) = x := by
  induction x using Projectivization.ind with
  | h v hv =>
    rw [mk_mem_chartDomain] at hx
    simp only [chartInv, chartCoord_mk]
    rw [Projectivization.mk_eq_mk_iff]
    refine ⟨Units.mk0 (v i)⁻¹ (inv_ne_zero hx), ?_⟩
    funext m
    obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove i m
    · simp [hx]
    · simp [div_eq_inv_mul]

lemma isQuotientMap_mk' : IsQuotientMap (Projectivization.mk' ℂ : {v : Fin (N + 1) → ℂ // v ≠ 0} → CP N) := by
  refine ⟨⟨rfl⟩, fun x => ?_⟩
  induction x using Projectivization.ind with
  | h v hv => exact ⟨⟨v, hv⟩, rfl⟩

lemma isOpen_chartDomain (i : Fin (N + 1)) : IsOpen (chartDomain (N := N) i) := by
  rw [ProjTopology.isOpen_iff]
  have : (Projectivization.mk' ℂ) ⁻¹' (chartDomain (N := N) i) =
      {v : {v : Fin (N + 1) → ℂ // v ≠ 0} | v.1 i ≠ 0} := by
    ext ⟨v, hv⟩; exact Iff.rfl
  rw [this]
  exact isOpen_ne_fun ((continuous_apply i).comp continuous_subtype_val) continuous_const

lemma continuousOn_chartCoord (i : Fin (N + 1)) :
    ContinuousOn (chartCoord (N := N) i) (chartDomain i) := by
  rw [isQuotientMap_mk'.continuousOn_isOpen_iff (isOpen_chartDomain i)]
  refine continuousOn_pi.mpr fun j => ?_
  intro v hv
  have hvi : v.1 i ≠ 0 := hv
  have hc : ContinuousAt (fun w : {v : Fin (N + 1) → ℂ // v ≠ 0} => w.1 (i.succAbove j) / w.1 i) v :=
    (((continuous_apply _).comp continuous_subtype_val).continuousAt).div
      (((continuous_apply _).comp continuous_subtype_val).continuousAt) hvi
  exact hc.continuousWithinAt

def chart (i : Fin (N + 1)) : OpenPartialHomeomorph (CP N) (Fin N → ℂ) where
  toFun := chartCoord i
  invFun := chartInv i
  source := chartDomain i
  target := univ
  map_source' _ _ := mem_univ _
  map_target' z _ := chartInv_mem i z
  left_inv' _ hx := chartInv_chartCoord i hx
  right_inv' z _ := chartCoord_chartInv i z
  open_source := isOpen_chartDomain i
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_chartCoord i
  continuousOn_invFun := (continuous_chartInv i).continuousOn

lemma exists_mem_chartDomain (x : CP N) : ∃ i, x ∈ chartDomain i := by
  induction x using Projectivization.ind with
  | h v hv =>
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    exact ⟨i, hi⟩

def chartIndex (x : CP N) : Fin (N + 1) := (exists_mem_chartDomain x).choose

lemma mem_chartDomain_chartIndex (x : CP N) : x ∈ chartDomain (chartIndex x) :=
  (exists_mem_chartDomain x).choose_spec

end CP

end

end GroundTheory.Heights₂.Heights
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.FubiniStudyMetric

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped LinearAlgebra.Projectivization ContDiff
open Topology Set

noncomputable section

variable {N : ℕ}

def normSq2 {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

def norm2 {ι : Type*} [Fintype ι] (v : ι → ℂ) : ℝ := √(normSq2 v)

section Norm2

variable {ι : Type*} [Fintype ι]

lemma normSq2_nonneg (v : ι → ℂ) : 0 ≤ normSq2 v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma normSq2_pos {v : ι → ℂ} (hv : v ≠ 0) : 0 < normSq2 v := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
    ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩

lemma euclideanNorm_pos {v : ι → ℂ} (hv : v ≠ 0) : 0 < norm2 v := Real.sqrt_pos.mpr (normSq2_pos hv)

lemma euclideanNorm_sq (v : ι → ℂ) : norm2 v ^ 2 = normSq2 v := Real.sq_sqrt (normSq2_nonneg v)

lemma normSq2_smul (t : ℂ) (v : ι → ℂ) : normSq2 (t • v) = ‖t‖ ^ 2 * normSq2 v := by
  simp [normSq2, mul_pow, Finset.mul_sum]

lemma euclideanNorm_smul (t : ℂ) (v : ι → ℂ) : norm2 (t • v) = ‖t‖ * norm2 v := by
  rw [norm2, normSq2_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]; rfl

end Norm2

namespace CP

lemma normSq2_chartVec (i : Fin (N + 1)) (z : Fin N → ℂ) :
    normSq2 (chartVec i z) = 1 + ∑ j, ‖z j‖ ^ 2 := by
  rw [normSq2, Fin.sum_univ_succAbove _ i]
  simp

def tautLine (x : CP N) : Submodule ℂ (Fin (N + 1) → ℂ) := x.submodule

lemma rep_mem_tautLine (x : CP N) : x.rep ∈ tautLine x := by
  rw [tautLine, Projectivization.submodule_eq]; exact Submodule.mem_span_singleton_self _

lemma mem_tautLine_mk (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) : v ∈ tautLine (Projectivization.mk ℂ v hv) := by
  rw [tautLine, Projectivization.submodule_mk]; exact Submodule.mem_span_singleton_self _

abbrev O1 (x : CP N) : Type := Module.Dual ℂ (tautLine x)

def fsNorm (x : CP N) (φ : O1 x) : ℝ := ‖φ ⟨x.rep, rep_mem_tautLine x⟩‖ / norm2 x.rep

theorem fsNorm_eq (x : CP N) (φ : O1 x) (v : Fin (N + 1) → ℂ) (hv : v ∈ tautLine x) (hv0 : v ≠ 0) :
    fsNorm x φ = ‖φ ⟨v, hv⟩‖ / norm2 v := by
  have hv' := hv
  rw [tautLine, Projectivization.submodule_eq, Submodule.mem_span_singleton] at hv'
  obtain ⟨t, rfl⟩ := hv'
  have ht : t ≠ 0 := by rintro rfl; simp at hv0
  have : (⟨t • x.rep, hv⟩ : tautLine x) = t • ⟨x.rep, rep_mem_tautLine x⟩ := rfl
  rw [this, map_smul, smul_eq_mul, norm_mul, euclideanNorm_smul, fsNorm]
  have hn : 0 < norm2 x.rep := euclideanNorm_pos x.rep_nonzero
  have ht' : 0 < ‖t‖ := norm_pos_iff.mpr ht
  field_simp

lemma tautologicalDual_ext (x : CP N) {φ ψ : O1 x} (h : φ ⟨x.rep, rep_mem_tautLine x⟩ = ψ ⟨x.rep, rep_mem_tautLine x⟩) :
    φ = ψ := by
  ext ⟨w, hw⟩
  have hw' := hw
  rw [tautLine, Projectivization.submodule_eq, Submodule.mem_span_singleton] at hw'
  obtain ⟨t, rfl⟩ := hw'
  have : (⟨t • x.rep, hw⟩ : tautLine x) = t • ⟨x.rep, rep_mem_tautLine x⟩ := rfl
  rw [this, map_smul, map_smul, h]

theorem fsNorm_eq_zero_iff (x : CP N) (φ : O1 x) : fsNorm x φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    have hn : 0 < norm2 x.rep := euclideanNorm_pos x.rep_nonzero
    rw [fsNorm, div_eq_zero_iff, norm_eq_zero] at h
    rcases h with h | h
    · exact tautologicalDual_ext x (by simpa using h)
    · exact absurd h hn.ne'
  · rintro rfl; simp [fsNorm]

def restrictForm (ℓ : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ) (x : CP N) : O1 x := ℓ.domRestrict (tautLine x)

theorem fsNorm_restrictForm_mk (ℓ : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ) (v : Fin (N + 1) → ℂ) (hv : v ≠ 0) :
    fsNorm (Projectivization.mk ℂ v hv) (restrictForm ℓ _) = ‖ℓ v‖ / norm2 v :=
  fsNorm_eq _ _ v (mem_tautLine_mk v hv) hv

def coordForm (i : Fin (N + 1)) : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj i

theorem restrictForm_coordForm_ne_zero (i : Fin (N + 1)) {x : CP N} (hx : x ∈ chartDomain i) :
    restrictForm (coordForm i) x ≠ 0 := by
  induction x using Projectivization.ind with
  | h v hv =>
    intro h
    have := (fsNorm_eq_zero_iff _ _).mpr h
    rw [fsNorm_restrictForm_mk, div_eq_zero_iff, norm_eq_zero] at this
    rcases this with h1 | h1
    · exact hx h1
    · exact (euclideanNorm_pos hv).ne' h1

theorem fsNorm_sq_chartInv (ℓ : (Fin (N + 1) → ℂ) →ₗ[ℂ] ℂ) (i : Fin (N + 1)) (z : Fin N → ℂ) :
    fsNorm (chartInv i z) (restrictForm ℓ _) ^ 2 = ‖ℓ (chartVec i z)‖ ^ 2 / (1 + ∑ j, ‖z j‖ ^ 2) := by
  rw [chartInv, fsNorm_restrictForm_mk, div_pow, euclideanNorm_sq, normSq2_chartVec]

theorem fsNorm_sq_frame (i : Fin (N + 1)) (z : Fin N → ℂ) :
    fsNorm (chartInv i z) (restrictForm (coordForm i) _) ^ 2 = 1 / (1 + ∑ j, ‖z j‖ ^ 2) := by
  rw [fsNorm_sq_chartInv]
  simp [coordForm]

lemma contDiff_normSqSum : ContDiff ℝ ∞ (fun z : Fin N → ℂ => ∑ j, ‖z j‖ ^ 2) :=
  ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) j)

end CP

end

end GroundTheory.Heights₂.Heights
end
end
