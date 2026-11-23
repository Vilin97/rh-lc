module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Mathlib.LinearAlgebra.Matrix.PosDef
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeEqLintegral
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Matrix.Order
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.Order.Star.Real

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntNearOfClosureShort

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem span_intCast_image_eq_top {ι : Type} [Fintype ι] [DecidableEq ι] (T : Set (ι → ℤ))
    (hT : AddSubgroup.closure T = ⊤) :
    Submodule.span ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T) = ⊤ := by
  have h : ∀ z : ι → ℤ, (fun i => (z i : ℝ)) ∈
      Submodule.span ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T) := by
    intro z
    have hz : z ∈ AddSubgroup.closure T := by rw [hT]; trivial
    induction hz using AddSubgroup.closure_induction with
    | mem z hz => exact Submodule.subset_span ⟨z, hz, rfl⟩
    | zero =>
      have : (fun i => (((0 : ι → ℤ) i : ℤ) : ℝ)) = 0 := by ext i; simp
      rw [this]; exact Submodule.zero_mem _
    | add u v _ _ hu hv =>
      have : (fun i => (((u + v) i : ℤ) : ℝ)) = (fun i => (u i : ℝ)) + fun i => (v i : ℝ) := by
        ext i; simp
      rw [this]; exact Submodule.add_mem _ hu hv
    | neg u _ hu =>
      have : (fun i => (((-u) i : ℤ) : ℝ)) = -(fun i => (u i : ℝ)) := by
        ext i; simp
      rw [this]; exact Submodule.neg_mem _ hu
  rw [eq_top_iff]
  intro x _
  rw [pi_eq_sum_univ x]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  have := h (fun j => if i = j then 1 else 0)
  convert this using 2 with j
  split_ifs <;> simp

theorem exists_int_near_of_closure_short :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ (T : Set (ι → ℤ)) (ρ : ℝ), 0 ≤ ρ → AddSubgroup.closure T = ⊤ → (∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) → ∀ x : ι → ℝ, ∃ z : ι → ℤ, ∑ i, ∑ j, A i j * (x i - z i) * (x j - z j) ≤ (Fintype.card ι * ρ) ^ 2 := by
  intro ι _ _ A hA T ρ hρ hT hz x
  classical
  set B : LinearMap.BilinForm ℝ (ι → ℝ) := Matrix.toBilin' A with hB
  have hBq : ∀ v : ι → ℝ, ∑ i, ∑ j, A i j * v i * v j = B v v := by
    intro v
    rw [hB, Matrix.toBilin'_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hpos : ∀ v : ι → ℝ, 0 ≤ B v v := by
    intro v
    rw [hB, Matrix.toBilin'_apply']
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg v
  have hsymm : ∀ u v : ι → ℝ, B u v = B v u := by
    intro u v
    rw [hB, Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : A j i = A i j := by simpa using hA.isHermitian.apply i j
    rw [this]; ring
  obtain ⟨b, hbS, hspan, hli⟩ :=
    exists_linearIndependent ℝ ((fun z : ι → ℤ => fun i => (z i : ℝ)) '' T)
  rw [span_intCast_image_eq_top T hT] at hspan
  have hfin : b.Finite := hli.setFinite
  haveI : Fintype b := hfin.fintype
  have hcard : Fintype.card b ≤ Fintype.card ι := by
    simpa using hli.fintype_card_le_finrank
  have hx : x ∈ Submodule.span ℝ (Set.range ((↑) : b → ι → ℝ)) := by
    rw [Subtype.range_coe, hspan]; trivial
  obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hx
  choose w hwT hw using fun a : b => hbS a.2
  have hq : ∀ a : b, B a a ≤ ρ ^ 2 := by
    intro a
    rw [← hBq, ← hw a]
    exact hz _ (hwT a)
  have hq2 : ∀ a c : b, B a c ≤ ρ ^ 2 := by
    intro a c
    have h1 := hpos ((a : ι → ℝ) - c)
    simp only [map_sub, LinearMap.sub_apply] at h1
    have := hsymm c a
    have := hq a
    have := hq c
    linarith
  refine ⟨∑ a : b, ⌊t a⌋ • w a, ?_⟩
  have hy : (fun i => x i - ((∑ a : b, ⌊t a⌋ • w a) i : ℤ)) =
      ∑ a : b, Int.fract (t a) • (a : ι → ℝ) := by
    ext i
    rw [← ht]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sum, Int.cast_mul,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have : (w a i : ℝ) = (a : ι → ℝ) i := congrFun (hw a) i
    rw [this, Int.fract]; ring
  have := hBq (fun i => x i - ((∑ a : b, ⌊t a⌋ • w a) i : ℤ))
  rw [this, hy]

  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  calc _ ≤ ∑ _a : b, ∑ _c : b, ρ ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        try rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun c _ => ?_
        have h1 := Int.fract_nonneg (t a)
        have h2 := (Int.fract_lt_one (t a)).le
        have h3 := Int.fract_nonneg (t c)
        have h4 := (Int.fract_lt_one (t c)).le
        have h5 := hq2 a c
        have h6 := hq2 c a
        have h7 : 0 ≤ ρ ^ 2 := by positivity
        have h8 := mul_nonneg h1 h3
        have h9 : Int.fract (t a) * Int.fract (t c) ≤ 1 := mul_le_one₀ h2 h3 h4
        nlinarith [mul_le_mul_of_nonneg_left h5 h8, mul_le_mul_of_nonneg_left h6 h8,
          mul_le_mul_of_nonneg_right h9 h7]
    _ = (Fintype.card b * ρ) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := by
        gcongr

end GlobalTheory.HSAmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeSumSqBallPosLtTop

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix MatrixOrder

namespace GlobalTheory.HSAmp

theorem sumSq_ball_eq_smul (ι : Type) [Fintype ι] (R : ℝ) (hR : 0 ≤ R) :
    {x : ι → ℝ | ∑ i, x i ^ 2 ≤ R ^ 2} = (fun x => R • x) '' {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · intro hx
    rcases hR.eq_or_lt with h0 | h0
    · subst h0
      refine ⟨0, by simp, ?_⟩
      have h1 : ∑ i, x i ^ 2 = 0 :=
        le_antisymm (by simpa using hx) (Finset.sum_nonneg fun i _ => sq_nonneg _)
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)] at h1
      funext i
      have := h1 i (Finset.mem_univ _)
      simp [pow_eq_zero_iff] at this
      simp [this]
    · refine ⟨R⁻¹ • x, ?_, by simp [smul_smul, h0.ne']⟩
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, inv_pow]
      rw [inv_mul_le_iff₀ (by positivity)]
      simpa using hx
  · rintro ⟨y, hy, rfl⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    nlinarith [sq_nonneg R]

theorem volume_sumSq_ball_pos_lt_top (ι : Type) [Fintype ι] :
    0 < volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} ∧ volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} < ⊤ := by
  constructor
  · have ho : IsOpen {x : ι → ℝ | ∑ i, x i ^ 2 < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    refine lt_of_lt_of_le (ho.measure_pos volume ⟨0, by simp⟩) (measure_mono ?_)
    intro x hx
    exact le_of_lt (a := ∑ i, x i ^ 2) hx
  · refine lt_of_le_of_lt (measure_mono ?_) (isCompact_closedBall (0 : ι → ℝ) 1).measure_lt_top
    intro x hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : x i ^ 2 ≤ ∑ i, x i ^ 2 :=
      Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : x i ^ 2 ≤ 1 := h1.trans hx
    rw [Real.norm_eq_abs]
    exact (sq_le_one_iff_abs_le_one _).1 h2

theorem volume_ellipsoid : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ R : ℝ, 0 ≤ R → volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ R ^ 2} = ENNReal.ofReal (R ^ Fintype.card ι / Real.sqrt A.det) * volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} ∧ 0 < volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} ∧ volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} < ⊤ := by
  intro ι _ _ A hA R hR
  refine ⟨?_, volume_sumSq_ball_pos_lt_top ι⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix ι ι ℝ, A = Bᵀ * B := by
    obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.posSemidef.nonneg
    exact ⟨B, by simpa [Matrix.star_eq_conjTranspose] using hB⟩
  have hdet : A.det = B.det ^ 2 := by
    rw [hB, Matrix.det_mul, Matrix.det_transpose, sq]
  have hpos : 0 < A.det := hA.det_pos
  have hB0 : B.det ≠ 0 := by
    intro h; rw [hdet, h] at hpos; simp at hpos
  have hset : {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ R ^ 2}
      = (Matrix.toLin' B) ⁻¹' {x : ι → ℝ | ∑ i, x i ^ 2 ≤ R ^ 2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Matrix.toLin'_apply]
    have : ∑ i, ∑ j, A i j * x i * x j = ∑ i, (B *ᵥ x) i ^ 2 := by
      simp only [hB, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, sq,
        Finset.sum_mul, Finset.mul_sum]
      symm
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this]
  have hl : LinearMap.det (Matrix.toLin' B) ≠ 0 := by simpa using hB0
  rw [hset, Measure.addHaar_preimage_linearMap _ hl, sumSq_ball_eq_smul ι R hR, Set.image_smul,
    Measure.addHaar_smul_of_nonneg _ hR, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 2
  rw [hdet, Real.sqrt_sq_eq_abs, LinearMap.det_toLin', abs_inv, Module.finrank_fintype_fun_eq_card]
  ring

end GlobalTheory.HSAmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLatticePointsQuadraticBallEstimate

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

theorem log_ellCount_near : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ (T : Set (ι → ℤ)) (ρ R : ℝ), 0 ≤ ρ → 0 < R → AddSubgroup.closure T = ⊤ → (∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) → 2 * Fintype.card ι * ρ ≤ R → {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.Finite ∧ |Real.log (ellCount A R) - (Fintype.card ι * Real.log R - Real.log A.det / 2 + Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ Fintype.card ι * Real.log 2 := by
  intro ι _ _ A hA T ρ R hρ hR hT hTz hRρ
  set n : ℕ := Fintype.card ι with hn
  set s : ℝ := n * ρ with hs
  have hs0 : 0 ≤ s := by positivity
  have hsR : s ≤ R / 2 := by rw [hs]; linarith
  have hnear := exists_int_near_of_closure_short ι A hA T ρ hρ hT hTz
  have hup := ellCount_volume ι A hA s R hs0 hR.le hnear
  have hlo := (ellCount_volume ι A hA s (R - s) hs0 (by linarith) hnear).2.1
  rw [sub_add_cancel] at hlo
  refine ⟨hup.1, ?_⟩
  obtain ⟨-, hω0, hωt⟩ := volume_ellipsoid ι A hA 0 le_rfl
  set ω : ENNReal := volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1} with hω
  have hVr : ∀ r : ℝ, 0 ≤ r → (volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r ^ 2}).toReal
      = r ^ n / Real.sqrt A.det * ω.toReal := by
    intro r hr
    rw [(volume_ellipsoid ι A hA r hr).1, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  have hVfin : ∀ r : ℝ, 0 ≤ r → volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r ^ 2} ≠ ⊤ := by
    intro r hr
    rw [(volume_ellipsoid ι A hA r hr).1]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωt.ne
  have hmono : ∀ r r' : ℝ, 0 ≤ r → r ≤ r' → volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r ^ 2}
      ≤ volume {x : ι → ℝ | ∑ i, ∑ j, A i j * x i * x j ≤ r' ^ 2} := by
    intro r r' hr hrr
    apply measure_mono
    intro x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    nlinarith
  have hlo' := (hmono (R / 2) (R - s) (by positivity) (by linarith)).trans hlo
  have hup' := hup.2.2.trans (hmono (R + s) (2 * R) (by linarith) (by linarith))
  have hloR : (R / 2) ^ n / Real.sqrt A.det * ω.toReal ≤ (ellCount A R : ℝ) := by
    rw [← hVr _ (by positivity)]
    have := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hlo'
    simpa using this
  have hupR : (ellCount A R : ℝ) ≤ (2 * R) ^ n / Real.sqrt A.det * ω.toReal := by
    rw [← hVr _ (by positivity)]
    have := ENNReal.toReal_mono (hVfin _ (by positivity)) hup'
    simpa using this
  have hdet := hA.det_pos
  have hωr : 0 < ω.toReal := ENNReal.toReal_pos hω0.ne' hωt.ne
  set K : ℝ := ω.toReal / Real.sqrt A.det with hK
  have hK0 : 0 < K := by positivity
  have hlogK : Real.log K = Real.log ω.toReal - Real.log A.det / 2 := by
    rw [hK, Real.log_div hωr.ne' (Real.sqrt_pos.2 hdet).ne', Real.log_sqrt hdet.le]
  have e1 : (R / 2) ^ n / Real.sqrt A.det * ω.toReal = (R / 2) ^ n * K := by rw [hK]; ring
  have e2 : (2 * R) ^ n / Real.sqrt A.det * ω.toReal = (2 * R) ^ n * K := by rw [hK]; ring
  rw [e1] at hloR
  rw [e2] at hupR
  have hp1 : 0 < (R / 2) ^ n * K := by positivity
  have hc : 0 < (ellCount A R : ℝ) := hp1.trans_le hloR
  have l1 := Real.log_le_log hp1 hloR
  have l2 := Real.log_le_log hc hupR
  rw [Real.log_mul (by positivity) hK0.ne', Real.log_pow, Real.log_div hR.ne' two_ne_zero] at l1
  rw [Real.log_mul (by positivity) hK0.ne', Real.log_pow, Real.log_mul two_ne_zero hR.ne'] at l2
  rw [mul_sub] at l1
  rw [mul_add] at l2
  rw [abs_le]
  constructor <;> linarith

end GlobalTheory.HSAmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLatticePointsQuadraticBallEstimateStatement

section

@[expose] public section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

theorem _root_.GlobalTheory.T.log_lattice_points_quadratic_ball_estimate : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ), A.PosDef → ∀ (T : Set (ι → ℤ)) (ρ R : ℝ), 0 ≤ ρ → 0 < R → AddSubgroup.closure T = ⊤ → (∀ z ∈ T, ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ ρ ^ 2) → 2 * Fintype.card ι * ρ ≤ R → {z : ι → ℤ | ∑ i, ∑ j, A i j * (z i : ℝ) * (z j : ℝ) ≤ R ^ 2}.Finite ∧ |Real.log (ellCount A R) - (Fintype.card ι * Real.log R - Real.log A.det / 2 + Real.log (volume {x : ι → ℝ | ∑ i, x i ^ 2 ≤ 1}).toReal)| ≤ Fintype.card ι * Real.log 2 := by
  first | exact @GlobalTheory.HSAmp.log_ellCount_near | exact GlobalTheory.HSAmp.log_ellCount_near | (intros; apply GlobalTheory.HSAmp.log_ellCount_near <;> assumption)
end
end
