module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirEigenNonnegRealUnitaryStatement
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCasimirEigenvalueDropsOffBlock

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR
variable {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]

theorem casDrop_term (F : ι → ι → Module.End ℂ M) (hF : IsGl F) (a b j k : ι) :
    F a b * F b a * F j k = F j k * (F a b * F b a) + (F a b * (if a = j then F b k else 0) - F a b * (if k = b then F j a else 0))
      + ((if b = j then F a k else 0) * F b a - (if k = a then F j b else 0) * F b a) := by
  have h1 := hF b a j k
  have h2 := hF a b j k
  have e1 : F b a * F j k = F j k * F b a + ((if a = j then F b k else 0) - (if k = b then F j a else 0)) := by
    rw [← h1]; abel
  have e2 : F a b * F j k = F j k * F a b + ((if b = j then F a k else 0) - (if k = a then F j b else 0)) := by
    rw [← h2]; abel
  calc F a b * F b a * F j k = F a b * (F b a * F j k) := mul_assoc _ _ _
    _ = F a b * F j k * F b a + F a b * ((if a = j then F b k else 0) - (if k = b then F j a else 0)) := by
        rw [e1, mul_add, mul_assoc]
    _ = _ := by rw [e2]; simp only [add_mul, sub_mul, mul_sub, mul_assoc]; abel

theorem cas_mul_off (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (hF : IsGl F) (j k : ι) (hj : s j = false)
    (hk : s k = true) :
    cas s F * F j k = F j k * cas s F + (2 : ℂ) • (∑ b, if s b = false then F j b * F b k else 0)
      - (2 : ℂ) • (∑ b, if s b = true then F j b * F b k else 0)
      + (((Finset.univ.filter fun a => s a = true).card : ℂ) - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • F j k := by
  have hjk : j ≠ k := by intro h; rw [h, hk] at hj; exact Bool.noConfusion hj
  have sw : ∀ a, F a k * F j a = F j a * F a k - F j k := by
    intro a
    have h := hF a k j a
    rw [if_neg (Ne.symm hjk), if_pos rfl] at h
    calc F a k * F j a = (F a k * F j a - F j a * F a k) + F j a * F a k := by abel
      _ = _ := by rw [h]; abel
  have cnt : ∀ c : Bool, (∑ a, if s a = c then F a k * F j a else 0)
      = (∑ a, if s a = c then F j a * F a k else 0) - ((Finset.univ.filter fun a => s a = c).card : ℂ) • F j k := by
    intro c
    have : (∑ a, if s a = c then F a k * F j a else 0)
        = ∑ a, ((if s a = c then F j a * F a k else 0) - (if s a = c then F j k else 0)) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases h : s a = c
      · simp only [if_pos h, sw]
      · simp [h]
    rw [this, Finset.sum_sub_distrib]
    congr 1
    rw [← Finset.sum_filter, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have S1 : ∑ a, ∑ b, (if s a = s b then F a b * (if a = j then F b k else 0) else 0)
      = ∑ b, if s b = false then F j b * F b k else 0 := by
    rw [Finset.sum_eq_single j]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hj]; by_cases h : s b <;> simp [h]
    · intro a _ ha; simp [ha]
    · simp
  have S2 : ∑ a, ∑ b, (if s a = s b then F a b * (if k = b then F j a else 0) else 0)
      = ∑ a, if s a = true then F a k * F j a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single k]
    · rw [hk]; simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have S3 : ∑ a, ∑ b, (if s a = s b then (if b = j then F a k else 0) * F b a else 0)
      = ∑ a, if s a = false then F a k * F j a else 0 := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single j]
    · rw [hj]; simp
    · intro b _ hb; simp [hb]
    · simp
  have S4 : ∑ a, ∑ b, (if s a = s b then (if k = a then F j b else 0) * F b a else 0)
      = ∑ b, if s b = true then F j b * F b k else 0 := by
    rw [Finset.sum_eq_single k]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [hk]; by_cases h : s b <;> simp [h]
    · intro a _ ha; simp [Ne.symm ha]
    · simp
  have expand : ∀ a b, (if s a = s b then F a b * F b a else 0) * F j k
      = (if s a = s b then F j k * (F a b * F b a) else 0)
        + ((if s a = s b then F a b * (if a = j then F b k else 0) else 0)
          - (if s a = s b then F a b * (if k = b then F j a else 0) else 0))
        + ((if s a = s b then (if b = j then F a k else 0) * F b a else 0)
          - (if s a = s b then (if k = a then F j b else 0) * F b a else 0)) := by
    intro a b
    by_cases h : s a = s b
    · simp only [if_pos h]; exact casDrop_term F hF a b j k
    · simp [h]
  unfold cas
  simp only [Finset.sum_mul, expand, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [S1, S2, S3, S4, cnt, cnt]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  simp only [two_smul, sub_smul]
  abel

end GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_drop : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ (α β x ω : ℂ) (y : ι → M), IsGl F → (∀ a b, qop F α β a b = 0) →
    (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ a, cas s F (y a) = ω • y a) →
    ∀ j, s j = false → cas s F (∑ b, F j b (y b)) = (ω - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ)
      - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • ∑ b, F j b (y b) := by
  intro ι M _ _ _ _ s F α β x ω y hF hq hy0 hyA hω j hj
  set r : ℂ := ((Finset.univ.filter fun a => s a = true).card : ℂ)
  set r' : ℂ := ((Finset.univ.filter fun a => s a = false).card : ℂ)
  set T : ι → Module.End ℂ M := fun b => ∑ c, if s c = true then F j c * F c b else 0 with hT

  have quad : ∀ b, s b = true → (∑ c, if s c = false then F j c * F c b else 0) = α • F j b - T b := by
    intro b hb
    have hjb : j ≠ b := by intro h; rw [h, hb] at hj; exact Bool.noConfusion hj
    have h := hq j b
    simp only [qop, if_neg hjb, sub_zero] at h
    have split : (∑ c, F j c * F c b) = (∑ c, if s c = false then F j c * F c b else 0) + T b := by
      rw [hT, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      cases s c <;> simp
    rw [split] at h
    calc (∑ c, if s c = false then F j c * F c b else 0) = ((∑ c, if s c = false then F j c * F c b else 0) + T b - α • F j b)
          + α • F j b - T b := by abel
      _ = α • F j b - T b := by rw [h]; abel

  have term : ∀ b, cas s F (F j b (y b)) = (ω + 2 * α + r - r') • F j b (y b) - (4 : ℂ) • T b (y b) := by
    intro b
    cases hb : s b
    · simp [hT, hy0 b hb]
    · have h := cas_mul_off s F hF j b hj hb
      rw [quad b hb] at h
      have h' := congrArg (fun L : Module.End ℂ M => L (y b)) h
      simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply] at h'
      rw [h', hω b, map_smul]
      module
  have sumT : (∑ b, T b (y b)) = x • ∑ b, F j b (y b) := by
    have : ∀ b, T b (y b) = ∑ c, if s c = true then F j c (F c b (y b)) else 0 := by
      intro b
      simp only [hT, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      split_ifs <;> rfl
    simp only [this]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    cases hc : s c
    · simp [hy0 c hc]
    · simp only [if_true]

      rw [← map_sum, hyA c hc, map_smul]

  rw [map_sum]
  simp only [term]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum, ← Finset.smul_sum, sumT, smul_smul, ← sub_smul]
  congr 1
  ring

end GlobalTheory.HoweR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockCasimirEigenvalueDropsOffBlockStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.blockCasimir_eigenvalue_drops_offBlock : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x ω : ℂ) (y : ι → M), IsGl F → (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ a, cas s F (y a) = ω • y a) → ∀ j, s j = false → cas s F (∑ b, F j b (y b)) = (ω - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ) - ((Finset.univ.filter fun a => s a = false).card : ℂ)) • ∑ b, F j b (y b) := by
  first | exact @GlobalTheory.HoweR.cas_drop | exact GlobalTheory.HoweR.cas_drop | (intros; apply GlobalTheory.HoweR.cas_drop <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticOperatorEigenvectorDiagonalBlockIdentit

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem qop_quadratic_on_eigenvector : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x : ℂ) (y : ι → M), (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ j, s j = false → ∑ b, F j b (y b) = 0) → ∀ a, (x ^ 2 - α * x - β) • y a = 0 := by
  intro ι M _ _ _ _ s F α β x y hq hs ht hf a
  have hall : ∀ c, ∑ b, F c b (y b) = x • y c := by
    intro c
    cases hc : s c
    · rw [hf c hc, hs c hc, smul_zero]
    · exact ht c hc
  cases ha : s a
  · rw [hs a ha, smul_zero]
  · have key : ∑ b, qop F α β a b (y b) = 0 := by simp [hq]
    have pt : ∀ b, qop F α β a b (y b)
        = ∑ c, F a c (F c b (y b)) - α • F a b (y b) - (if a = b then β • y b else 0) := by
      intro b
      simp only [qop, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.sum_apply, Module.End.mul_apply]
      split_ifs <;> simp
    have expand : ∑ b, qop F α β a b (y b)
        = ∑ c, F a c (∑ b, F c b (y b)) - α • ∑ b, F a b (y b) - β • y a := by
      rw [Finset.sum_congr rfl (fun b _ => pt b), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_comm, Finset.sum_ite_eq, ← Finset.smul_sum]

      simp [map_sum]
    rw [expand, ht a ha] at key
    simp only [hall, map_smul] at key
    rw [← Finset.smul_sum, ht a ha] at key
    rw [sub_smul, sub_smul, pow_two, mul_smul, mul_smul]
    exact key

end GlobalTheory.HoweR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticOperatorEigenvectorDiagonalBlockIdentitStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.quadraticOperator_eigenvector_diagonalBlock_identity : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (α β x : ℂ) (y : ι → M), (∀ a b, qop F α β a b = 0) → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = x • y a) → (∀ j, s j = false → ∑ b, F j b (y b) = 0) → ∀ a, (x ^ 2 - α * x - β) • y a = 0 := by
  first | exact @GlobalTheory.HoweR.qop_quadratic_on_eigenvector | exact GlobalTheory.HoweR.qop_quadratic_on_eigenvector | (intros; apply GlobalTheory.HoweR.qop_quadratic_on_eigenvector <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalEigenvalueLeOfCasimirNearMin

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem real_root_quad_le {x : ℝ} {α β : ℂ} (h : (x : ℂ) ^ 2 - α * x - β = 0) : x ≤ ‖α‖ + ‖β‖ + 1 := by
  have h1 : (x : ℂ) ^ 2 = α * x + β := by linear_combination h
  have h2 : ‖(x : ℂ)‖ ^ 2 ≤ ‖α‖ * ‖(x : ℂ)‖ + ‖β‖ := by
    calc ‖(x : ℂ)‖ ^ 2 = ‖(x : ℂ) ^ 2‖ := (norm_pow _ _).symm
    _ = ‖α * x + β‖ := by rw [h1]
    _ ≤ ‖α * x‖ + ‖β‖ := norm_add_le _ _
    _ = ‖α‖ * ‖(x : ℂ)‖ + ‖β‖ := by rw [norm_mul]
  have hx : ‖(x : ℂ)‖ = |x| := by rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hx] at h2
  have ha := norm_nonneg α
  have hb := norm_nonneg β
  by_contra hc
  push_neg at hc
  have ht : ‖α‖ + ‖β‖ + 1 < |x| := lt_of_lt_of_le hc (le_abs_self x)
  nlinarith [mul_nonneg hb (by linarith : (0:ℝ) ≤ |x| - 1),
    mul_pos (by linarith : (0:ℝ) < |x| - (‖α‖ + ‖β‖ + 1)) (by linarith : (0:ℝ) < |x|)]

theorem diag_eig_le_of_cas_min : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F → (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ, (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) → ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R := by
  intro ι _ _ s α β
  refine ⟨max (‖α‖ + ‖β‖ + 1) ((2 * ‖α‖ + Fintype.card ι + 1) / 4), ?_⟩
  intro M _ _ F hGl hq hLoc ω hω x y hy hfalse htrue hcas
  by_cases hz : ∀ j, s j = false → ∑ b, F j b (y b) = 0
  · have hbc := GlobalTheory.T.quadraticOperator_eigenvector_diagonalBlock_identity ι M s F α β x y hq hfalse htrue hz
    obtain ⟨a, ha⟩ : ∃ a, y a ≠ 0 := by
      by_contra h
      push_neg at h
      exact hy (funext h)
    have h0 : (x : ℂ) ^ 2 - α * x - β = 0 := by
      by_contra hne
      exact ha ((smul_eq_zero.mp (hbc a)).resolve_left hne)
    exact le_max_of_le_left (real_root_quad_le h0)
  · push_neg at hz
    obtain ⟨j, hj, hzj⟩ := hz
    have hd := GlobalTheory.T.blockCasimir_eigenvalue_drops_offBlock ι M s F α β x ω y hGl hq hfalse htrue hcas j hj
    obtain ⟨U, hU, hUU⟩ := hLoc {∑ b, F j b (y b)}
    have hzU : ∑ b, F j b (y b) ∈ U := hU _ (Finset.mem_singleton_self _)
    have him := ((GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hUU).1 _ _ hzU hzj hd).1
    set c : ℂ := (ω : ℂ) - 4 * x + 2 * α + ((Finset.univ.filter fun a => s a = true).card : ℂ)
      - ((Finset.univ.filter fun a => s a = false).card : ℂ) with hc
    have hcre : c = ((c.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
    have hlt := hω c.re _ hzj (by rw [← hcre]; exact hd)
    have hre : c.re = ω - 4 * x + 2 * α.re + ((Finset.univ.filter fun a => s a = true).card : ℝ)
      - ((Finset.univ.filter fun a => s a = false).card : ℝ) := by simp [hc]
    have hr : ((Finset.univ.filter fun a => s a = true).card : ℝ) ≤ Fintype.card ι := by
      have := Finset.card_filter_le (Finset.univ : Finset ι) (fun a => s a = true)
      rw [Finset.card_univ] at this
      exact_mod_cast this
    have hαre : α.re ≤ ‖α‖ := Complex.re_le_norm α
    have hr'0 : (0:ℝ) ≤ ((Finset.univ.filter fun a => s a = false).card : ℝ) := Nat.cast_nonneg _
    refine le_max_of_le_right ?_
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    linarith

end GlobalTheory.HoweR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalEigenvalueLeOfCasimirNearMinStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F → (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ, (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) → ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) → (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R := by
  first | exact @GlobalTheory.HoweR.diag_eig_le_of_cas_min | exact GlobalTheory.HoweR.diag_eig_le_of_cas_min | (intros; apply GlobalTheory.HoweR.diag_eig_le_of_cas_min <;> assumption)
end
end
