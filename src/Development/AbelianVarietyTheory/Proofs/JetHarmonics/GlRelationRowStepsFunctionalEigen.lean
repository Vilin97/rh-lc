module

public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowExp
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorEqUnitSmulOfRangeEq

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_perm_of_range_eq {t : ℕ} {β : Type} (a a₂ : Fin t → β)
    (ha : Function.Injective a) (ha₂ : Function.Injective a₂) (h : Set.range a = Set.range a₂) :
    ∃ τ : Equiv.Perm (Fin t), a = a₂ ∘ τ := by
  refine ⟨(Equiv.ofInjective a ha).trans ((Set.equivOfEq h).trans (Equiv.ofInjective a₂ ha₂).symm), ?_⟩
  funext i
  simp [Equiv.apply_ofInjective_symm]

theorem qminor_eq_smul_of_range_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a a₂ b b₂ : Fin t → Fin n), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective a₂ → Function.Injective b → Function.Injective b₂ → Set.range a = Set.range a₂ → Set.range b = Set.range b₂ → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u, Formalism.REAL.qminor E a b u = e • Formalism.REAL.qminor E a₂ b₂ u := by
  intro A _ _ n t E a a₂ b b₂ hE ha ha₂ hb hb₂ hra hrb
  obtain ⟨σ, rfl⟩ := exists_perm_of_range_eq a a₂ ha ha₂ hra
  obtain ⟨τ, rfl⟩ := exists_perm_of_range_eq b b₂ hb hb₂ hrb
  refine ⟨(((Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign τ : ℤ) : ℤ) : ℂ), ?_, fun u => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h' | h' <;> simp [h, h']
  · rw [Formalism.REAL.quantumMinorRowSkew_holds A n t E a₂ (b₂ ∘ τ) σ u, Formalism.REAL.quantumMinorColSkew_holds A n t E hE a₂ b₂ τ u,
      Int.cast_smul_eq_zsmul, zsmul_eq_mul, ← mul_assoc, Int.cast_mul]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorEqUnitSmulOfRangeEqStatement

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.quantumMinor_eq_unit_smul_of_range_eq : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a a₂ b b₂ : Fin t → Fin n), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective a₂ → Function.Injective b → Function.Injective b₂ → Set.range a = Set.range a₂ → Set.range b = Set.range b₂ → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u, Formalism.REAL.qminor E a b u = e • Formalism.REAL.qminor E a₂ b₂ u := by
  first | exact @GlobalTheory.qminor_eq_smul_of_range_eq | exact GlobalTheory.qminor_eq_smul_of_range_eq | (intros; apply GlobalTheory.qminor_eq_smul_of_range_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorRowExpansionEigenFunctional

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem qminor_row_step_under_functional : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → a0 ∉ Set.range b → (∀ j v, l (E a0 (b j) v) = (if b j = b0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' u v) := by
  intro M Wp _ _ _ _ n t E l a b a' b' a0 b0 p hE ha hb ha' hb' hra ha0 hrb hb0 hab hl
  have hA : Function.Injective (Fin.cons a0 a' : Fin (t + 1) → Fin n) :=
    Fin.cons_injective_iff.2 ⟨ha0, ha'⟩
  have hB : Function.Injective (Fin.cons b0 b' : Fin (t + 1) → Fin n) :=
    Fin.cons_injective_iff.2 ⟨hb0, hb'⟩
  have hrB : Set.range b = Set.range (Fin.cons b0 b' : Fin (t + 1) → Fin n) := by
    rw [Fin.range_cons]; exact hrb
  obtain ⟨e, he, hq⟩ := GlobalTheory.T.quantumMinor_eq_unit_smul_of_range_eq (Module.End ℂ M) n (t + 1) E a (Fin.cons a0 a') b (Fin.cons b0 b') hE
    ha hA hb hB (by rw [Fin.range_cons]; exact hra) hrB
  refine ⟨e, he, fun u v => ?_⟩
  have key : ∀ (j : Fin (t + 1)) (w : ℂ) (x : M),
      l (Formalism.REAL.Tm E w a0 ((Fin.cons b0 b' : Fin (t + 1) → Fin n) j) x) = (if j = 0 then p else 0) • l x := by
    intro j w x
    have hmem : (Fin.cons b0 b' : Fin (t + 1) → Fin n) j ∈ Set.range b := by
      rw [hrB]; exact ⟨j, rfl⟩
    have hne : a0 ≠ (Fin.cons b0 b' : Fin (t + 1) → Fin n) j := fun h => hab (h ▸ hmem)
    obtain ⟨k, hk⟩ := hmem
    have hiff : b k = b0 ↔ j = 0 := by
      rw [hk]
      exact ⟨fun h => hB (by simpa using h), fun h => by subst h; rfl⟩
    unfold Formalism.REAL.Tm
    rw [if_neg hne, zero_add, ← hk, hl k x]
    simp only [hiff]

  rw [hq u, quantum_minor_row_expansion.1 (Module.End ℂ M) n t E hE, LinearMap.smul_apply, map_smul, LinearMap.sum_apply,
  map_sum, Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero, mul_smul]
  · congr 1
    have h0 := key 0
    simp only [Fin.cons_zero, if_true] at h0
    simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Module.End.mul_apply, Fin.cons_zero, h0,
      Fin.succAbove_zero]
    rfl
  · intro j _
    rw [← zsmul_eq_mul, LinearMap.smul_apply, map_zsmul, Module.End.mul_apply, Fin.cons_zero, key,
      if_neg (Fin.succ_ne_zero j), zero_smul, smul_zero]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorRowExpansionEigenFunctionalStatement

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.quantumMinor_rowExpansion_eigenFunctional : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → a0 ∉ Set.range b → (∀ j v, l (E a0 (b j) v) = (if b j = b0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' u v) := by
  first | exact @GlobalTheory.qminor_row_step_under_functional | exact GlobalTheory.qminor_row_step_under_functional | (intros; apply GlobalTheory.qminor_row_step_under_functional <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelationRowStepsFunctionalEigen

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RowChain

theorem quantumMinor_row_removal_chain (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp]
    (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp)
    (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ) (hE : Formalism.REAL.GlRel E)
    (h : ∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) →
      (∀ v, l (E a b v) = p a b • l v) ∧
      ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ)
        else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ
        else 0)) (d : ℕ) :
    ∀ (i t : ℕ) (a b : Fin (t + 1) → Fin (2 * r + k + 1)), i + d + 1 = r → t + 1 + i = 2 * r + k →
      (∀ j, (a j).val = i + j.val) → (∀ j, (b j).val = i + 1 + j.val) →
      ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) =
        c • l (Formalism.REAL.qminor E
          (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
          (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
  induction d with
  | zero =>
    intro i t a b hi ht ha hb
    obtain rfl : t = r + k := by omega
    have hai : Function.Injective a := fun x y hxy => by
      have h1 := ha x; have h2 := ha y; rw [hxy] at h1; exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y hxy => by
      have h1 := hb x; have h2 := hb y; rw [hxy] at h1; exact Fin.ext (by omega)
    obtain ⟨e, he, hl⟩ := GlobalTheory.T.quantumMinor_rowExpansion_eigenFunctional M Wp _ _ E l a b
      (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1)))
      ⟨i, by omega⟩ ⟨r + k, by omega⟩ (p ⟨i, by omega⟩ ⟨r + k, by omega⟩) hE hai hbi
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by split_ifs at hxy <;> omega))
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, ha]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, hb]
        constructor
        · rintro ⟨j, hj⟩
          rcases lt_trichotomy j.val k with h0 | h0 | h0
          · right; exact ⟨⟨j.val, by omega⟩, by simp only; split_ifs <;> omega⟩
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; split_ifs <;> omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨k, by omega⟩, by simp only; omega⟩
          · split_ifs at hj
            · exact ⟨⟨j.val, by omega⟩, by simp only; omega⟩
            · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; split_ifs at hj <;> omega)
      (by
        simp only [Set.mem_range, Fin.ext_iff, hb]
        rintro ⟨j, hj⟩; omega)
      (by
        intro j v
        have hj := hb j
        obtain ⟨h1, h2⟩ := h ⟨i, by omega⟩ (b j) (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
        rw [h1]
        by_cases hc : b j = ⟨r + k, by omega⟩
        · rw [if_pos hc, hc]
        · rw [if_neg hc]
          have hc' : (b j).val ≠ r + k := fun h' => hc (Fin.ext h')
          rw [if_neg (by simp only; omega), if_neg (by simp only; omega)] at h2
          rw [norm_eq_zero.mp h2])
    refine ⟨_, ?_, hl⟩
    obtain ⟨-, h2⟩ := h ⟨i, by omega⟩ ⟨r + k, by omega⟩ (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
    rw [if_neg (by simp only; omega), if_pos (Or.inl ⟨by simp only; omega, rfl⟩)] at h2
    rw [norm_mul, he, h2, one_mul]
  | succ d ih =>
    intro i t a b hi ht ha hb
    obtain ⟨t, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hai : Function.Injective a := fun x y hxy => by
      have h1 := ha x; have h2 := ha y; rw [hxy] at h1; exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y hxy => by
      have h1 := hb x; have h2 := hb y; rw [hxy] at h1; exact Fin.ext (by omega)
    obtain ⟨c, hc, hcl⟩ := ih (i + 1) t
      (fun j : Fin (t + 1) => (⟨i + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (t + 1) => (⟨i + 1 + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (by omega) (by omega) (fun _ => rfl) (fun _ => rfl)
    obtain ⟨e, he, hl⟩ := GlobalTheory.T.quantumMinor_rowExpansion_eigenFunctional M Wp _ _ E l a b
      (fun j : Fin (t + 1) => (⟨i + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (t + 1) => (⟨i + 1 + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (p ⟨i, by omega⟩ ⟨i + 1, by omega⟩) hE hai hbi
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, ha]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, hb]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        simp only [Set.mem_range, Fin.ext_iff, hb]
        rintro ⟨j, hj⟩; omega)
      (by
        intro j v
        have hj := hb j
        obtain ⟨h1, h2⟩ := h ⟨i, by omega⟩ (b j) (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
        rw [h1]
        by_cases hc : b j = ⟨i + 1, by omega⟩
        · rw [if_pos hc, hc]
        · rw [if_neg hc]
          have hc' : (b j).val ≠ i + 1 := fun h' => hc (Fin.ext h')
          rw [if_neg (by simp only; omega), if_neg (by simp only; omega)] at h2
          rw [norm_eq_zero.mp h2])
    obtain ⟨-, h2⟩ := h ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
    rw [if_pos (by simp only; exact ⟨trivial, by omega⟩)] at h2
    refine ⟨e * p ⟨i, by omega⟩ ⟨i + 1, by omega⟩ * c, ?_, fun u v => ?_⟩
    · rw [norm_mul, norm_mul, he, h2, hc, one_mul, one_mul]
    · rw [hl, hcl, smul_smul]

theorem chain_rows : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → 1 ≤ r → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * r + k))) (Fin.succAbove 0) u v) = c • l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
  intro M Wp _ _ _ _ k r E l p τ _ hE h hr
  have gen : ∀ (n : ℕ) (a b : Fin n → Fin (2 * r + k + 1)), n = 2 * r + k →
      (∀ j, (a j).val = 0 + j.val) → (∀ j, (b j).val = 0 + 1 + j.val) →
      ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) =
        c • l (Formalism.REAL.qminor E
          (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
          (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
    intro n a b hn ha hb
    cases n with
    | zero => omega
    | succ t =>
      exact quantumMinor_row_removal_chain M Wp k r E l p τ hE h (r - 1) 0 t a b (by omega) (by omega) ha hb
  exact gen _ _ _ rfl (fun j => by simp) (fun j => by simp; omega)

end GlobalTheory.RowChain
end
end
