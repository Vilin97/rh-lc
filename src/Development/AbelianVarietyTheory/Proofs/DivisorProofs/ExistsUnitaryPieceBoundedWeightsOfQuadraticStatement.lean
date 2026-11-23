module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalEigenvalueLeOfCasimirNearMinStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirEigenNonnegRealUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUnitaryDiagonalLeOfEigenvalueBoundStatement
import Std.Tactic.BVDecide.Normalize.Bool

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirCommuteSameBlockUnit

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_mul_comm_of_block : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), IsGl F → ∀ a b, s a = s b → cas s F * F a b = F a b * cas s F := by
  intro ι M _ _ _ _ s F hF a b hab
  rw [← sub_eq_zero]
  have key : ∀ c d, F c d * F d c * F a b - F a b * (F c d * F d c) =
      ((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0)) := by
    intro c d
    have e : F c d * F d c * F a b - F a b * (F c d * F d c) =
        F c d * (F d c * F a b - F a b * F d c) + (F c d * F a b - F a b * F c d) * F d c := by noncomm_ring
    rw [e, hF d c a b, hF c d a b]
    simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  have h0 : cas s F * F a b - F a b * cas s F = ∑ c, ∑ d, if s c = s d then
      (((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0))) else 0 := by
    simp only [cas, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : s c = s d
    · simp only [h, if_true]; exact key c d
    · simp only [h, if_false, zero_mul, mul_zero, sub_self]
  have h1 : (∑ c, ∑ d, if s c = s d then (if c = a then F c d * F d b else 0) else 0) =
      ∑ d, if s a = s d then F a d * F d b else 0 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [hc]
    · simp
  have h4 : (∑ c, ∑ d, if s c = s d then (if b = c then F a d * F d c else 0) else 0) =
      ∑ d, if s a = s d then F a d * F d b else 0 := by
    rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  have h2 : (∑ c, ∑ d, if s c = s d then (if b = d then F c d * F a c else 0) else 0) =
      ∑ c, if s c = s a then F c b * F a c else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro d _ hd; simp [Ne.symm hd]
    · simp
  have h3 : (∑ c, ∑ d, if s c = s d then (if d = a then F c b * F d c else 0) else 0) =
      ∑ c, if s c = s a then F c b * F a c else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro d _ hd; simp [hd]
    · simp
  rw [h0]
  have split : (∑ c, ∑ d, if s c = s d then
      (((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0))) else 0) =
      ((∑ c, ∑ d, if s c = s d then (if c = a then F c d * F d b else 0) else 0) -
        (∑ c, ∑ d, if s c = s d then (if b = d then F c d * F a c else 0) else 0)) +
      ((∑ c, ∑ d, if s c = s d then (if d = a then F c b * F d c else 0) else 0) -
        (∑ c, ∑ d, if s c = s d then (if b = c then F a d * F d c else 0) else 0)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [split, h1, h2, h3, h4]
  abel

end GlobalTheory.HoweR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockDiagonalFibreCasimirCommuteSameBlockUnitStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.blockDiagonalFibreCasimir_commute_sameBlock_unit : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), IsGl F → ∀ a b, s a = s b → cas s F * F a b = F a b * cas s F := by
  first | exact @GlobalTheory.HoweR.cas_mul_comm_of_block | exact GlobalTheory.HoweR.cas_mul_comm_of_block | (intros; apply GlobalTheory.HoweR.cas_mul_comm_of_block <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceOfLeStable

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem unitOn_of_le : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ U U' : Submodule ℂ M, UnitOn s F U → U' ≤ U →
    (∀ a b, s a = s b → ∀ u ∈ U', F a b u ∈ U') → UnitOn s F U' := by
  intro ι M _ _ _ _ s F U U' hU hle hst
  obtain ⟨hfin, -, ip, hsym, hpos, hadj⟩ := hU
  refine ⟨Submodule.finiteDimensional_of_le hle, hst, ip, ?_, ?_, ?_⟩
  · intro x hx y hy; exact hsym x (hle hx) y (hle hy)
  · intro x hx h0; exact hpos x (hle hx) h0
  · intro a b hab x hx y hy; exact hadj a b hab x (hle hx) y (hle hy)

end GlobalTheory.HoweR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceOfLeStableStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_of_le_stable : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ U U' : Submodule ℂ M, UnitOn s F U → U' ≤ U → (∀ a b, s a = s b → ∀ u ∈ U', F a b u ∈ U') → UnitOn s F U' := by
  first | exact @GlobalTheory.HoweR.unitOn_of_le | exact GlobalTheory.HoweR.unitOn_of_le | (intros; apply GlobalTheory.HoweR.unitOn_of_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymNegTSwap

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem isGl_negT {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (F : ι → ι → Module.End ℂ M) (h : IsGl F) : IsGl (negT F) := by
  intro a b c d
  have h1 := h d c b a
  simp only [negT, neg_mul_neg]
  have e1 : F b a * F d c - F d c * F b a = -(F d c * F b a - F b a * F d c) := by abel
  rw [e1, h1]
  simp only [@eq_comm _ c b, @eq_comm _ a d]
  split_ifs <;> abel

theorem unitOn_negT {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (h : UnitOn s F U) :
    UnitOn s (negT F) U := by
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := h
  refine ⟨hfd, fun a b hab u hu => ?_, ip, hsym, hpos, fun a b hab x hx y hy => ?_⟩
  · simp only [negT, LinearMap.neg_apply]
    exact U.neg_mem (hst b a hab.symm u hu)
  · simp only [negT, LinearMap.neg_apply, map_neg, LinearMap.neg_apply]
    rw [hadj b a hab.symm x hx y hy]

theorem unitOn_not {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (h : UnitOn s F U) :
    UnitOn (fun a => !s a) F U := by
  obtain ⟨hfd, hst, ip, hsym, hpos, hadj⟩ := h
  refine ⟨hfd, fun a b hab u hu => hst a b (by simpa using hab) u hu, ip, hsym, hpos,
    fun a b hab x hx y hy => hadj a b (by simpa using hab) x hx y hy⟩

theorem sym_negT_swap : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), (IsGl F → IsGl (negT F)) ∧ cas s (negT F) = cas s F ∧ cas (fun a => !s a) F = cas s F ∧ (∀ U, UnitOn s F U → UnitOn s (negT F) U ∧ UnitOn (fun a => !s a) F U) ∧ (LocU s F → LocU s (negT F) ∧ LocU (fun a => !s a) F) := by
  intro ι M _ _ _ _ s F
  refine ⟨isGl_negT F, ?_, ?_, fun U hU => ⟨unitOn_negT s F U hU, unitOn_not s F U hU⟩, fun h => ⟨?_, ?_⟩⟩
  · unfold cas negT
    simp only [neg_mul_neg]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [eq_comm]
  · unfold cas
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Bool.not_inj_iff]
  · intro t
    obtain ⟨U, hU, hUn⟩ := h t
    exact ⟨U, hU, unitOn_negT s F U hUn⟩
  · intro t
    obtain ⟨U, hU, hUn⟩ := h t
    exact ⟨U, hU, unitOn_not s F U hUn⟩

end GlobalTheory.HoweR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPieceBoundedWeightsOfQuadratic

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem diag_re_le_of_near_min {ι M : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (s : ι → Bool) (G : ι → ι → Module.End ℂ M) (α β : ℂ) (R : ℝ)
    (hR : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), IsGl F →
      (∀ a b, qop F α β a b = 0) → LocU s F → ∀ ω : ℝ,
      (∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s F v = (ω' : ℂ) • v → ω < ω' + 1) →
      ∀ (x : ℝ) (y : ι → M), y ≠ 0 → (∀ a, s a = false → y a = 0) →
      (∀ a, s a = true → ∑ b, F a b (y b) = (x : ℂ) • y a) → (∀ a, cas s F (y a) = (ω : ℂ) • y a) → x ≤ R)
    (hG : IsGl G) (hq : ∀ a b, qop G α β a b = 0) (hL : LocU s G) (U : Submodule ℂ M) (hU : UnitOn s G U) (ω : ℝ)
    (hω : ∀ (ω' : ℝ) (v : M), v ≠ 0 → cas s G v = (ω' : ℂ) • v → ω < ω' + 1)
    (hUe : ∀ u ∈ U, cas s G u = (ω : ℂ) • u) :
    ∀ a, s a = true → ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, G a a u = m • u → m.re ≤ R :=
  GlobalTheory.T.blockUnitary_diagonal_le_of_eigenvalue_bound ι M s G U R hU (fun x y hy hyU hf hs => hR M G hG hq hL ω hω x y hy hf hs (fun a => hUe _ (hyU a)))

theorem exists_unitOn_diag_bounded : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β α' β' : ℂ), ∃ R : ℝ,
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), Nontrivial M → IsGl F →
    (∀ a b, qop F α β a b = 0) → (∀ a b, qop (negT F) α' β' a b = 0) → LocU s F →
    ∃ U : Submodule ℂ M, U ≠ ⊥ ∧ UnitOn s F U ∧ ∀ a, ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → |m.re| ≤ R := by
  intro ι _ _ s α β α' β'
  obtain ⟨R1, h1⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι s α β
  obtain ⟨R2, h2⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι (fun a => !s a) α β
  obtain ⟨R3, h3⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι s α' β'
  obtain ⟨R4, h4⟩ := GlobalTheory.T.blockDiagonal_eigenvalue_le_of_casimir_nearMin ι (fun a => !s a) α' β'
  refine ⟨max (max R1 R2) (max R3 R4), ?_⟩
  intro M _ _ F hnt hG hq hq' hL
  obtain ⟨hGn, hcn, hcs, hUs, hLs⟩ := sym_negT_swap ι M s F
  obtain ⟨-, hcn', hcs', hUs', hLs'⟩ := sym_negT_swap ι M s (negT F)
  let S : Set ℝ := {ω' | ∃ v : M, v ≠ 0 ∧ cas s F v = (ω' : ℂ) • v}
  have hSne : S.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : M)
    obtain ⟨U, hxU, hU⟩ := hL {x}
    have hne : U ≠ ⊥ := by
      intro h
      have := hxU x (Finset.mem_singleton_self x)
      rw [h, Submodule.mem_bot] at this
      exact hx this
    obtain ⟨ω, v, -, hv, hcv⟩ := (GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hU).2 hne
    exact ⟨ω, v, hv, hcv⟩
  have hSbdd : BddBelow S := by
    refine ⟨0, fun ω' hω' => ?_⟩
    obtain ⟨v, hv, hcv⟩ := hω'
    obtain ⟨U, hvU, hU⟩ := hL {v}
    have := (GlobalTheory.T.blockDiagonalFibreCasimir_eigen_nonneg_real_unitary ι M s F U hU).1 (ω' : ℂ) v (hvU v (Finset.mem_singleton_self v)) hv hcv
    simpa using this.2
  obtain ⟨ω, ⟨v, hv, hcv⟩, hωlt⟩ := exists_lt_of_csInf_lt hSne (lt_add_one (sInf S))
  have hω : ∀ (ω' : ℝ) (w : M), w ≠ 0 → cas s F w = (ω' : ℂ) • w → ω < ω' + 1 := fun ω' w hw hcw => by
    have := csInf_le hSbdd ⟨w, hw, hcw⟩
    linarith
  obtain ⟨U0, hvU0, hU0⟩ := hL {v}
  let U : Submodule ℂ M := U0 ⊓ LinearMap.ker (cas s F - (ω : ℂ) • (1 : Module.End ℂ M))
  have hUe : ∀ u ∈ U, cas s F u = (ω : ℂ) • u := fun u hu => by
    have h2 := hu.2
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h2
    simpa using h2
  have hvU : v ∈ U := ⟨hvU0 v (Finset.mem_singleton_self v), by
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]; simpa using hcv⟩
  have hUst : ∀ a b, s a = s b → ∀ u ∈ U, F a b u ∈ U := by
    intro a b hab u hu
    refine ⟨hU0.2.1 a b hab u hu.1, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    have hc := congrArg (fun T : Module.End ℂ M => T u) (GlobalTheory.T.blockDiagonalFibreCasimir_commute_sameBlock_unit ι M s F hG a b hab)
    simp only [Module.End.mul_apply] at hc
    rw [hc, hUe u hu]
    simp
  have hU : UnitOn s F U := GlobalTheory.T.isBlockUnitaryFiniteSubspace_of_le_stable ι M s F U0 U hU0 inf_le_left hUst
  refine ⟨U, fun h => hv (by rw [h, Submodule.mem_bot] at hvU; exact hvU), hU, ?_⟩
  intro a u hu hu0 m hm
  have b1 := diag_re_le_of_near_min s F α β R1 h1 hG hq hL U hU ω hω hUe
  have b2 := diag_re_le_of_near_min (fun a => !s a) F α β R2 h2 hG hq (hLs hL).2 U (hUs U hU).2 ω
    (by rw [hcs]; exact hω) (by rw [hcs]; exact hUe)
  have b3 := diag_re_le_of_near_min s (negT F) α' β' R3 h3 (hGn hG) hq' (hLs hL).1 U (hUs U hU).1 ω
    (by rw [hcn]; exact hω) (by rw [hcn]; exact hUe)
  have b4 := diag_re_le_of_near_min (fun a => !s a) (negT F) α' β' R4 h4 (hGn hG) hq' (hLs' (hLs hL).1).2 U
    (hUs' U (hUs U hU).1).2 ω (by rw [hcs', hcn]; exact hω) (by rw [hcs', hcn]; exact hUe)
  have hmn : negT F a a u = (-m) • u := by simp [negT, hm]
  have l1 : R1 ≤ max (max R1 R2) (max R3 R4) := (le_max_left _ _).trans (le_max_left _ _)
  have l2 : R2 ≤ max (max R1 R2) (max R3 R4) := (le_max_right _ _).trans (le_max_left _ _)
  have l3 : R3 ≤ max (max R1 R2) (max R3 R4) := (le_max_left _ _).trans (le_max_right _ _)
  have l4 : R4 ≤ max (max R1 R2) (max R3 R4) := (le_max_right _ _).trans (le_max_right _ _)
  rw [abs_le]
  cases hsa : s a
  · have e1 := b2 a (by simp [hsa]) u hu hu0 m hm
    have e2 := b4 a (by simp [hsa]) u hu hu0 (-m) hmn
    rw [Complex.neg_re] at e2
    constructor <;> linarith
  · have e1 := b1 a hsa u hu hu0 m hm
    have e2 := b3 a hsa u hu hu0 (-m) hmn
    rw [Complex.neg_re] at e2
    constructor <;> linarith

end GlobalTheory.HoweR
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPieceBoundedWeightsOfQuadraticStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.exists_unitary_piece_bounded_weights_of_quadratic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β α' β' : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), Nontrivial M → IsGl F → (∀ a b, qop F α β a b = 0) → (∀ a b, qop (negT F) α' β' a b = 0) → LocU s F → ∃ U : Submodule ℂ M, U ≠ ⊥ ∧ UnitOn s F U ∧ ∀ a, ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → |m.re| ≤ R := by
  first | exact @GlobalTheory.HoweR.exists_unitOn_diag_bounded | exact GlobalTheory.HoweR.exists_unitOn_diag_bounded | (intros; apply GlobalTheory.HoweR.exists_unitOn_diag_bounded <;> assumption)
end
end
