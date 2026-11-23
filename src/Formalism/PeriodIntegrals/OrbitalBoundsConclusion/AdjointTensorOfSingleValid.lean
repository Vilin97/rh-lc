module

public import Formalism.PeriodIntegrals.FockRBlock
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.FilterConcatWLength
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.Development
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
import Mathlib.Tactic.ENatToNat
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.FockLin

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.MultidegSingle

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace PI.TOW.DegW

open PI.TO PI.TOW

variable {K : Type} [Field K] {n' k : ℕ}

theorem multideg_add (a b : Fin n' × Fin k →₀ ℕ) (i : Fin n') :
    multideg (a + b) i = multideg a i + multideg b i := by
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]

theorem multideg_single (j : Fin n' × Fin k) (i : Fin n') :
    multideg (Finsupp.single j 1) i = if j.1 = i then 1 else 0 := by
  obtain ⟨j₁, j₂⟩ := j
  by_cases h : j₁ = i <;> simp [multideg, Finsupp.single_apply, Prod.ext_iff, h]

theorem step_mem (t : Fin n') (a b : Fin k) (d : Fin n' → ℕ) (G : MvPolynomial (Fin n' × Fin k) K)
    (hG : G ∈ Pol K (ι := Fin n') k d) :
    X (t, a) * pderiv (t, b) G ∈ Pol K (ι := Fin n') k d := by
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hG

  rw [G.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hdm : ∀ i, multideg m i = d i := hG hm
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul]
  by_cases hmb : m (t, b) = 0
  · simp [hmb]
  have hle : Finsupp.single (t, b) 1 ≤ m := by
    rw [Finsupp.single_le_iff]; omega
  have hsplit : m = (m - Finsupp.single (t, b) 1) + Finsupp.single (t, b) 1 :=
    (tsub_add_cancel_of_le hle).symm
  have hexp : ∀ i, multideg (Finsupp.single (t, a) 1 + (m - Finsupp.single (t, b) 1)) i = d i := by
    intro i
    have h1 := multideg_add (m - Finsupp.single (t, b) 1) (Finsupp.single (t, b) 1) i
    rw [← hsplit, hdm i, multideg_single] at h1
    rw [multideg_add, multideg_single]
    simp only at h1 ⊢
    split_ifs at h1 ⊢ <;> omega
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro x hx
  have hx' := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hx)
  rw [Finset.mem_singleton] at hx'
  subst hx'
  exact hexp

theorem stepDeg : StepDeg := by
  intro K _ n' k d l G hG
  induction l with
  | nil => exact hG
  | cons y l ih =>
    simp only [opWord, List.foldr_cons] at ih ⊢
    exact step_mem y.1 y.2.1 y.2.2 d _ ih

end PI.TOW.DegW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.NotMemVarsEmbS

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace PI.TOW.LiftW

open PI.TO PI.TOW

variable {K : Type} [CommRing K] {n' k : ℕ}

theorem inj (t : Fin n') : Function.Injective (fun c : Fin k => (t, c)) := by
  intro a c h
  exact (Prod.mk.inj h).2

theorem pderiv_embS (t : Fin n') (b : Fin k) (W : MvPolynomial (Fin k) K) :
    pderiv (t, b) (embS K t W) = embS K t (pderiv b W) := by
  simpa [embS] using pderiv_rename (inj (k := k) t) b W

theorem notMem_vars_embS {t a : Fin n'} (h : a ≠ t) (b : Fin k) (W : MvPolynomial (Fin k) K) :
    (t, b) ∉ (embS K a W).vars := by
  intro hm
  have h2 : (t, b) ∈ W.vars.image (fun c : Fin k => (a, c)) :=
    vars_rename (fun c : Fin k => (a, c)) W hm
  rw [Finset.mem_image] at h2
  obtain ⟨c, -, hc⟩ := h2
  exact h (congrArg Prod.fst hc)

theorem pderiv_prod_ne (t : Fin n') (b : Fin k) (T : Finset (Fin n')) (ht : t ∉ T)
    (H : Fin n' → MvPolynomial (Fin k) K) : pderiv (t, b) (∏ s ∈ T, embS K s (H s)) = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert s T hs ih =>
    rw [Finset.prod_insert hs, Derivation.leibniz]
    have hst : s ≠ t := fun e => ht (e ▸ Finset.mem_insert_self s T)
    rw [ih (fun h => ht (Finset.mem_insert_of_mem h)),
      pderiv_eq_zero_of_notMem_vars (notMem_vars_embS hst b (H s))]
    simp

theorem opWord_liftW (t : Fin n') (l : List (Fin k × Fin k)) (F : MvPolynomial (Fin k) K)
    (R : MvPolynomial (Fin n' × Fin k) K) (hR : ∀ b, pderiv (t, b) R = 0) :
    opWord (liftW t l) (embS K t F * R) = embS K t (word1 l F) * R := by
  induction l with
  | nil => simp [opWord, liftW, word1]
  | cons y l ih =>
    have e1 : opWord (liftW t (y :: l)) (embS K t F * R)
        = X (t, y.1) * pderiv (t, y.2) (opWord (liftW t l) (embS K t F * R)) := by
      simp [opWord, liftW]
    have e2 : word1 (y :: l) F = X y.1 * pderiv y.2 (word1 l F) := by
      simp [word1]
    rw [e1, ih, e2, Derivation.leibniz, hR, pderiv_embS]
    simp [embS, map_mul, rename_X]
    ring

theorem opWord_append (l₁ l₂ : List (Fin n' × (Fin k × Fin k))) (f : MvPolynomial (Fin n' × Fin k) K) :
    opWord (l₁ ++ l₂) f = opWord l₁ (opWord l₂ f) := by
  simp [opWord, List.foldr_append]

theorem main_list (w : Fin n' → List (Fin k × Fin k)) (G : Fin n' → MvPolynomial (Fin k) K)
    (ts : List (Fin n')) (hts : ts.Nodup) :
    opWord (ts.flatMap fun t => liftW t (w t)) (∏ s, embS K s (G s)) =
      ∏ s, embS K s (if s ∈ ts then word1 (w s) (G s) else G s) := by
  classical
  induction ts with
  | nil => simp [opWord]
  | cons t ts ih =>
    rw [List.nodup_cons] at hts
    rw [List.flatMap_cons, opWord_append, ih hts.2]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t),
      ← Finset.mul_prod_erase Finset.univ
        (fun s => embS K s (if s ∈ t :: ts then word1 (w s) (G s) else G s)) (Finset.mem_univ t)]
    simp only [if_neg hts.1, List.mem_cons, true_or, if_true]
    rw [opWord_liftW t (w t) (G t) _ (fun b' => pderiv_prod_ne t b' _ (Finset.notMem_erase t _) _)]
    congr 1
    refine Finset.prod_congr rfl fun s hs => ?_
    have hne : s ≠ t := Finset.ne_of_mem_erase hs
    simp [hne]

theorem stepLift : StepLift := by
  intro K _ n' k w F
  have h := main_list w F (List.finRange n') (List.nodup_finRange n')
  simpa [concatW, List.mem_finRange] using h

end PI.TOW.LiftW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.OkSmulRight

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace PI.TOW

open PI.TO

variable {K : Type} [Field K] {n' m : ℕ} {vec : Fin n' → Bool} {TT : Finset (Fin n')} {d : Fin n' → ℕ} {c : ℕ}

theorem ok_zero_left (s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K) :
    Ok K n' m vec TT d c 0 s := by
  refine ⟨0, by simp, fun G _ H _ => ?_⟩
  rw [mul_zero, fockR_zero_right, combo_zero, map_zero, fockR_zero_left]

theorem ok_zero_right (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K) :
    Ok K n' m vec TT d c β 0 := by
  refine ⟨0, by simp, fun G _ H _ => ?_⟩
  rw [mul_zero, fockR_zero_left, combo_zero, map_zero, fockR_zero_left]

theorem ok_add_left {β₁ β₂ s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h₁ : Ok K n' m vec TT d c β₁ s) (h₂ : Ok K n' m vec TT d c β₂ s) : Ok K n' m vec TT d c (β₁ + β₂) s := by
  obtain ⟨f₁, hf₁, e₁⟩ := h₁
  obtain ⟨f₂, hf₂, e₂⟩ := h₂
  refine ⟨f₁ + f₂, fun l hl => ?_, fun G hG H hH => ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hl) with h | h
    exacts [hf₁ l h, hf₂ l h]
  · rw [mul_add, fockR_add_right, e₁ G hG H hH, e₂ G hG H hH, combo_add, map_add (f := _),
      fockR_add_left]

theorem ok_add_right {β s₁ s₂ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h₁ : Ok K n' m vec TT d c β s₁) (h₂ : Ok K n' m vec TT d c β s₂) : Ok K n' m vec TT d c β (s₁ + s₂) := by
  obtain ⟨f₁, hf₁, e₁⟩ := h₁
  obtain ⟨f₂, hf₂, e₂⟩ := h₂
  refine ⟨f₁ + f₂, fun l hl => ?_, fun G hG H hH => ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hl) with h | h
    exacts [hf₁ l h, hf₂ l h]
  · rw [mul_add, fockR_add_left, e₁ G hG H hH, e₂ G hG H hH, combo_add, map_add (f := _),
      fockR_add_left]

theorem ok_smul_left (a : K) {β s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h : Ok K n' m vec TT d c β s) : Ok K n' m vec TT d c (a • β) s := by
  obtain ⟨f, hf, e⟩ := h
  refine ⟨a • f, fun l hl => hf l (Finsupp.support_smul hl), fun G hG H hH => ?_⟩
  rw [mul_smul_comm, fockR_smul_right, e G hG H hH, combo_smul, map_smul,
    fockR_smul_left]

theorem ok_smul_right (a : K) {β s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h : Ok K n' m vec TT d c β s) : Ok K n' m vec TT d c β (a • s) := by
  obtain ⟨f, hf, e⟩ := h
  refine ⟨a • f, fun l hl => hf l (Finsupp.support_smul hl), fun G hG H hH => ?_⟩
  rw [mul_smul_comm, fockR_smul_left, e G hG H hH, combo_smul, map_smul,
    fockR_smul_left]

theorem stepSpan : StepSpan := by
  intro K _ n' m vec TT d c M hM β hβ s hs
  unfold PI.TO.tensorLat at hβ hs
  have key : ∀ F : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K, (∀ t, F t ∈ M t) →
      Ok K n' m vec TT d c (∏ t, PI.TO.blockEmb K t (F t)) s := by
    intro F hF
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, hS, rfl⟩ := hx
      exact hM F S hF hS
    | zero => exact ok_zero_right _
    | add x y _ _ hx hy => exact ok_add_right hx hy
    | smul a x _ hx => exact ok_smul_right a hx
  induction hβ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact key F hF
  | zero => exact ok_zero_left _
  | add x y _ _ hx hy => exact ok_add_left hx hy
  | smul a x _ hx => exact ok_smul_left a hx

end PI.TOW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.StepMonoFactor

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace PI.TOW.MonoW

open PI.TO PI.TOW

theorem stepMonoFactor : StepMonoFactor := by
  intro K _ n' k μ
  simp only [embS, rename_monomial]
  suffices hμ : μ = ∑ t, Finsupp.mapDomain (fun c => (t, c)) (partS μ t) by
    rw [← MvPolynomial.monomial_sum_one, ← hμ]
  ext ⟨t, c⟩
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · rw [Finsupp.mapDomain_apply_of_injective (fun a b h => by simpa using h)]
    simp [partS]
  · intro t' _ ht'
    rw [Finsupp.mapDomain_notin_range]
    rintro ⟨c', hc'⟩
    exact ht' (congrArg Prod.fst hc')
  · simp

end PI.TOW.MonoW
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdjointTensorOfSingleValid

section

@[expose] public section

theorem adjointTensorOfSingle_valid : PI.TenOp :=
  PI.TOW.tenOp_of_steps PI.TOW.DegW.stepDeg
    (PI.TOW.stepPure_of PI.TOW.LiftW.stepLift PI.TOW.MonoW.stepMonoFactor) PI.TOW.stepSpan
end
end
