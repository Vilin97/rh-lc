module

public import Formalism.RealPlaceAnalysis.StatementE
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialFirstColumn.FirstColumnSplitBijective
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorColumnExpansionUnderLinearMap

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapStepCol

theorem exists_perm_of_range_eq {n t : ℕ} (a a₂ : Fin t → Fin n) (ha : Function.Injective a)
    (h : Set.range a = Set.range a₂) : ∃ τ : Equiv.Perm (Fin t), a = a₂ ∘ τ := by
  have h1 : ∀ i, ∃ j, a₂ j = a i := fun i => by
    have : a i ∈ Set.range a₂ := h ▸ Set.mem_range_self i
    exact this
  choose f hf using h1
  have hinj : Function.Injective f := fun i j hij => ha (by rw [← hf i, ← hf j, hij])
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_⟩
  funext i
  simp [hf]

theorem norm_sign {t : ℕ} (τ : Equiv.Perm (Fin t)) :
    ‖(((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

theorem cap_step_col : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → b0 ∉ Set.range a → (∀ j v, l (E (a j) b0 v) = (if a j = a0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' (u - 1) v) := by
  intro M Wp _ _ _ _ n t E l a b a' b' a0 b0 p hE ha hb ha' hb' hra ha0 hrb hb0 hba hl
  obtain ⟨σ, hσ⟩ := exists_perm_of_range_eq a (Fin.cons a0 a' : Fin (t + 1) → Fin n) ha
    (by rw [hra, Fin.range_cons])
  obtain ⟨τ, hτ⟩ := exists_perm_of_range_eq b (Fin.cons b0 b' : Fin (t + 1) → Fin n) hb
    (by rw [hrb, Fin.range_cons])
  refine ⟨(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) * (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℂ), ?_, ?_⟩
  · rw [norm_mul, norm_sign, norm_sign, one_mul]
  intro u v
  have hT : ∀ (j : Fin (t + 1)) (w : M),
      l (Formalism.REAL.Tm E u ((Fin.cons a0 a' : Fin (t + 1) → Fin n) j) b0 w) =
        (if j = 0 then p else 0) • l w := by
    intro j w
    have hmem : (Fin.cons a0 a' : Fin (t + 1) → Fin n) j ∈ Set.range a := by
      rw [hra, ← Fin.range_cons]; exact Set.mem_range_self j
    obtain ⟨i, hi⟩ := hmem
    have hne : a i ≠ b0 := fun h => hba ⟨i, h⟩
    have hiff : a i = a0 ↔ j = 0 := by
      rw [hi]
      refine Fin.cases ?_ (fun k => ?_) j
      · simp
      · simp only [Fin.cons_succ, Fin.succ_ne_zero, iff_false]
        exact fun h => ha0 ⟨k, h⟩
    rw [← hi, Formalism.REAL.Tm, if_neg hne, zero_add, hl]
    simp only [hiff]
  have key : l (Formalism.REAL.qminor E (Fin.cons a0 a' : Fin (t + 1) → Fin n)
      (Fin.cons b0 b' : Fin (t + 1) → Fin n) u v) = p • l (Formalism.REAL.qminor E a' b' (u - 1) v) := by

    rw [PI.QmColExpWork.expFirst, LinearMap.sum_apply, map_sum, Finset.sum_eq_single 0]
    · have e1 : (Fin.cons a0 a' : Fin (t + 1) → Fin n) ∘ (0 : Fin (t + 1)).succAbove = a' := by
        funext k; simp
      have e2 : (Fin.cons b0 b' : Fin (t + 1) → Fin n) ∘ Fin.succ = b' := by
        funext k; simp
      rw [e1, e2]
      simp only [Fin.val_zero, pow_zero, Int.cast_one, one_mul, Module.End.mul_apply]
      have := hT 0 (Formalism.REAL.qminor E a' b' (u - 1) v)
      simpa using this
    · intro j _ hj
      rw [Module.End.mul_apply, Module.End.intCast_apply, map_zsmul, Module.End.mul_apply,
        Fin.cons_zero, hT, if_neg hj, zero_smul, smul_zero]
    · simp
  rw [hσ, hτ, Formalism.REAL.quantumMinorRowSkew_holds, Formalism.REAL.quantumMinorColSkew_holds _ _ _ E hE,
    Module.End.mul_apply, Module.End.mul_apply, Module.End.intCast_apply,
    Module.End.intCast_apply, map_zsmul, map_zsmul, key, mul_smul, mul_smul,
    Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]

end GlobalTheory.CapStepCol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorColumnExpansionUnderLinearMapStatement

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.quantumMinor_column_expansion_under_linearMap : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n t : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (a b : Fin (t + 1) → Fin n) (a' b' : Fin t → Fin n) (a0 b0 : Fin n) (p : ℂ), Formalism.REAL.GlRel E → Function.Injective a → Function.Injective b → Function.Injective a' → Function.Injective b' → Set.range a = insert a0 (Set.range a') → a0 ∉ Set.range a' → Set.range b = insert b0 (Set.range b') → b0 ∉ Set.range b' → b0 ∉ Set.range a → (∀ j v, l (E (a j) b0 v) = (if a j = a0 then p else 0) • l v) → ∃ e : ℂ, ‖e‖ = 1 ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) = (e * p) • l (Formalism.REAL.qminor E a' b' (u - 1) v) := by
  first | exact @GlobalTheory.CapStepCol.cap_step_col | exact GlobalTheory.CapStepCol.cap_step_col | (intros; apply GlobalTheory.CapStepCol.cap_step_col <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselColumnStepsFunctionalEigen

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quantumMinor_columnSteps_partial (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp]
    [Module ℂ Wp] (k r : ℕ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp)
    (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ) (hE : Formalism.REAL.GlRel E)
    (hp : ∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) →
      (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ =
        (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ)
          else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ
          else 0))
    (w : Fin k → Fin (2 * r + k + 1)) (hw : ∀ i, (w i).val = r + i.val) (j : ℕ) :
    j ≤ r → ∀ (t : ℕ) (a b : Fin t → Fin (2 * r + k + 1)), t = k + j →
      (∀ i, (a i).val = r + i.val) →
      (∀ i, (b i).val = if i.val < k then r + i.val else r + i.val + 1) →
      ∃ c : ℂ, ‖c‖ = (if j = 0 then 1 else τ) ∧ ∀ u v,
        l (Formalism.REAL.qminor E a b u v) = c • l (Formalism.REAL.qminor E w w (u - (j : ℂ)) v) := by
  induction j with
  | zero =>
    intro _ t a b ht ha hb
    obtain rfl : t = k := ht
    have h1 : a = w := funext fun i => Fin.ext (by rw [ha, hw])
    have h2 : b = w := funext fun i => Fin.ext (by rw [hb, hw, if_pos i.isLt])
    refine ⟨1, by simp, fun u v => ?_⟩
    simp [h1, h2]
  | succ j ih =>
    intro hj t a b ht ha hb
    obtain rfl : t = (k + j) + 1 := ht
    obtain ⟨c, hc, hcu⟩ := ih (by omega) (k + j) (fun i => a i.castSucc) (fun i => b i.castSucc) rfl
      (fun i => by simpa using ha i.castSucc) (fun i => by simpa using hb i.castSucc)
    have hai : Function.Injective a := fun x y h => by
      have h' := congrArg Fin.val h
      rw [ha, ha] at h'
      exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y h => by
      have h' := congrArg Fin.val h
      rw [hb, hb] at h'
      exact Fin.ext (by split_ifs at h' <;> omega)
    have hr : ∀ f : Fin (k + j + 1) → Fin (2 * r + k + 1),
        Set.range f = insert (f (Fin.last _)) (Set.range fun i : Fin (k + j) => f i.castSucc) := by
      intro f
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Fin.exists_fin_succ', eq_comm, or_comm]
    have hn : ∀ f : Fin (k + j + 1) → Fin (2 * r + k + 1), Function.Injective f →
        f (Fin.last _) ∉ Set.range fun i : Fin (k + j) => f i.castSucc := by
      rintro f hf ⟨i, hi⟩
      exact (Fin.castSucc_lt_last i).ne (hf hi)
    have hal : (a (Fin.last _)).val = r + (k + j) := by rw [ha]; simp
    have hbl : (b (Fin.last _)).val = r + (k + j) + 1 := by rw [hb]; simp
    have hlt : ∀ i, a i < b (Fin.last _) := fun i => by
      have := i.isLt
      rw [Fin.lt_def, ha, hbl]; omega
    have hq := fun i => hp (a i) (b (Fin.last _)) (hlt i) (by rw [hbl]; omega)
    obtain ⟨e, he, heu⟩ := GlobalTheory.T.quantumMinor_column_expansion_under_linearMap M Wp _ (k + j) E l a b (fun i => a i.castSucc)
      (fun i => b i.castSucc) (a (Fin.last _)) (b (Fin.last _))
      (p (a (Fin.last _)) (b (Fin.last _))) hE hai hbi
      (hai.comp (Fin.castSucc_injective _)) (hbi.comp (Fin.castSucc_injective _))
      (hr a) (hn a hai) (hr b) (hn b hbi)
      (by rintro ⟨i, hi⟩; exact (hlt i).ne hi)
      (by
        intro i v
        rw [(hq i).1 v]
        split_ifs with h
        · rw [h]
        · have h0 := (hq i).2
          have hi : (a i).val ≠ r + (k + j) := fun h' => h (Fin.ext (by rw [h', hal]))
          have hi2 := ha i
          rw [hbl, if_neg (by omega), if_neg (by omega)] at h0
          rw [norm_eq_zero.1 h0])
    refine ⟨e * p (a (Fin.last _)) (b (Fin.last _)) * c, ?_, fun u v => ?_⟩
    · have h0 := (hq (Fin.last _)).2
      rw [hal, hbl] at h0
      rw [norm_mul, norm_mul, he, hc, h0]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
        intro h; omega
      · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
        simp
    · rw [heu, hcu, smul_smul]
      congr 4
      push_cast
      ring

theorem qminor_column_chain : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → 1 ≤ r → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) = c • l (Formalism.REAL.qminor E (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (u - (r : ℂ)) v) := by
  intro M Wp _ _ _ _ k r E l p τ _ hE hp hr
  have h := quantumMinor_columnSteps_partial M Wp k r E l p τ hE hp
    (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (fun _ => rfl) r le_rfl (r + k)
    (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
    (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
      by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) (Nat.add_comm _ _) (fun _ => rfl) (fun _ => rfl)
  rw [if_neg (by omega)] at h
  exact h

end GlobalTheory
end
end
