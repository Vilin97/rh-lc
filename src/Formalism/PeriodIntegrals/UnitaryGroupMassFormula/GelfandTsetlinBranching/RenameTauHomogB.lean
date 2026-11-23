module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.RowActDiagMonomial
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.FockFEqSumOfSubsetB
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.DetPowUnitriB

section

@[expose] public section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

def FiltB {σ : Type*} (ψ : σ → ℕ) (d : ℕ) : Submodule ℂ (MvPolynomial σ ℂ) where
  carrier := {g | ∀ e ∈ g.support, d ≤ Finsupp.weight ψ e}
  add_mem' := by
    intro a b ha hb e he
    classical
    rcases Finset.mem_union.mp (support_add he) with h1 | h1
    exacts [ha e h1, hb e h1]
  zero_mem' := by
    intro e he
    simp at he
  smul_mem' := by
    intro c a ha e he
    exact ha e (support_smul he)

theorem FiltB_mono {σ : Type*} (ψ : σ → ℕ) {d d' : ℕ} (h : d' ≤ d) : FiltB ψ d ≤ FiltB ψ d' :=
  fun _ hp e he => le_trans h (hp e he)

theorem FiltB_mul {σ : Type*} (ψ : σ → ℕ) {d d' : ℕ} {p q : MvPolynomial σ ℂ} (hp : p ∈ FiltB ψ d)
    (hq : q ∈ FiltB ψ d') : p * q ∈ FiltB ψ (d + d') := by
  classical
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (support_mul p q he)
  rw [map_add (f := _)]
  exact Nat.add_le_add (hp a ha) (hq b hb)

theorem X_mem_FiltB {σ : Type*} (ψ : σ → ℕ) (v : σ) : (X v : MvPolynomial σ ℂ) ∈ FiltB ψ (ψ v) := by
  intro e he
  rw [support_X, Finset.mem_singleton] at he
  subst he
  rw [Finsupp.weight_single, one_smul]

def GoodB {σ : Type*} (R : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (ψ : σ → ℕ) (p : MvPolynomial σ ℂ) (d : ℕ) :
    Prop :=
  p ∈ FiltB ψ d ∧ R p - p ∈ FiltB ψ (d + 1)

section Good

variable {σ : Type*} (R : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ) (ψ : σ → ℕ)

theorem GoodB_mul {p q : MvPolynomial σ ℂ} {d d' : ℕ} (hp : GoodB R ψ p d) (hq : GoodB R ψ q d') :
    GoodB R ψ (p * q) (d + d') := by
  refine ⟨FiltB_mul ψ hp.1 hq.1, ?_⟩
  have hRq : R q ∈ FiltB ψ d' := by
    have e : R q = (R q - q) + q := by ring
    rw [e]
    exact Submodule.add_mem _ (FiltB_mono ψ (Nat.le_succ d') hq.2) hq.1
  have e : R (p * q) - p * q = (R p - p) * R q + p * (R q - q) := by
    rw [map_mul]; ring
  rw [e]
  refine Submodule.add_mem _ ?_ ?_
  · have := FiltB_mul ψ hp.2 hRq
    rwa [show d + 1 + d' = d + d' + 1 by ring] at this
  · have := FiltB_mul ψ hp.1 hq.2
    rwa [show d + (d' + 1) = d + d' + 1 by ring] at this

theorem GoodB_one : GoodB R ψ 1 0 :=
  ⟨fun _ _ => Nat.zero_le _, by rw [map_one, sub_self]; exact Submodule.zero_mem _⟩

theorem GoodB_pow {p : MvPolynomial σ ℂ} {d : ℕ} (hp : GoodB R ψ p d) : ∀ k : ℕ, GoodB R ψ (p ^ k) (k * d)
  | 0 => by simpa using GoodB_one R ψ
  | k + 1 => by
    rw [pow_succ, Nat.succ_mul]
    exact GoodB_mul R ψ (GoodB_pow hp k) hp

theorem GoodB_prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℂ) (d : ι → ℕ)
    (h : ∀ i ∈ s, GoodB R ψ (f i) (d i)) : GoodB R ψ (∏ i ∈ s, f i) (∑ i ∈ s, d i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GoodB_one R ψ
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact GoodB_mul R ψ (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem GoodB_smul (c : ℂ) {p : MvPolynomial σ ℂ} {d : ℕ} (hp : GoodB R ψ p d) : GoodB R ψ (c • p) d := by
  refine ⟨Submodule.smul_mem _ c hp.1, ?_⟩
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_mem _ c hp.2

theorem GoodB_monomial (hX : ∀ v, GoodB R ψ (X v) (ψ v)) (e : σ →₀ ℕ) (c : ℂ) :
    GoodB R ψ (monomial e c) (Finsupp.weight ψ e) := by
  have he : Finsupp.weight ψ e = ∑ v ∈ e.support, e v * ψ v := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    simp [smul_eq_mul]
  rw [monomial_eq, ← smul_eq_C_mul, Finsupp.prod, he]
  exact GoodB_smul R ψ c (GoodB_prod R ψ _ _ _ fun v _ => GoodB_pow R ψ (hX v) (e v))

theorem GoodB_homog (hX : ∀ v, GoodB R ψ (X v) (ψ v)) (g : MvPolynomial σ ℂ) (d : ℕ)
    (hg : IsWeightedHomogeneous ψ g d) : R g - g ∈ FiltB ψ (d + 1) := by
  have e0 : R g - g = ∑ e ∈ g.support, (R (monomial e (AddMonoidAlgebra.coeff g e)) - monomial e (AddMonoidAlgebra.coeff g e)) := by
    conv_lhs => rw [g.as_sum]

    rw [map_sum, ← Finset.sum_sub_distrib]
  rw [e0]
  refine Submodule.sum_mem _ fun e he => ?_
  have := (GoodB_monomial R ψ hX e (AddMonoidAlgebra.coeff g e)).2
  rwa [hg (mem_support_iff.mp he)] at this

end Good

theorem rowAct_X_B {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (v : Fin N × Fin N) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) M (X v) = ∑ b, C (M v.1 b) * X (b, v.2) := by
  simp [Formalism.GradedWeylDivisibility.rowAct]

theorem GoodB_X_tri {n N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (hd : ∀ a, M a a = 1)
    (ho : ∀ a b, a ≠ b → M a b ≠ 0 → prowB n N a < prowB n N b) (v : Fin N × Fin N) :
    GoodB (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) M) (psiB n N) (X v) (psiB n N v) := by
  refine ⟨X_mem_FiltB _ v, ?_⟩
  rw [rowAct_X_B, ← Finset.add_sum_erase _ _ (Finset.mem_univ v.1), hd, map_one, one_mul, Prod.mk.eta,
    add_sub_cancel_left]
  refine Submodule.sum_mem _ fun b hb => ?_
  have hb' : b ≠ v.1 := Finset.ne_of_mem_erase hb
  by_cases h0 : M v.1 b = 0
  · rw [h0, map_zero, zero_mul]
    exact Submodule.zero_mem _
  · rw [← smul_eq_C_mul]
    refine Submodule.smul_mem _ _ (FiltB_mono _ ?_ (X_mem_FiltB _ (b, v.2)))
    exact ho v.1 b (Ne.symm hb') h0

theorem homog_psi_B {n N : ℕ} (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ)
    (hg : IsWeightedHomogeneous (wnB n N) g m) : IsWeightedHomogeneous (psiB n N) g (PsiB n m) := by
  intro e he
  rw [weight_psiB, hg he]

theorem high_zero_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (k : ℕ)
    (hmax : ∀ g ∈ W, g ≠ 0 → ∀ m, IsWeightedHomogeneous (wnB n N) g m → PsiB n m ≤ k)
    (x : MvPolynomial (Fin N × Fin N) ℂ) (hxW : x ∈ W) (hxF : x ∈ FiltB (psiB n N) (k + 1)) : x = 0 := by
  classical
  rw [← comp_sum_B (wnB n N) x (x.support.image (Finsupp.weight (wnB n N)))
    (fun e he => Finset.mem_image_of_mem _ he)]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_contra hne
  have hle := hmax _ (graded_B h lam W hW x hxW m) hne m (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  obtain ⟨e, hc⟩ := MvPolynomial.ne_zero_iff.mp hne
  rw [coeff_weightedHomogeneousComponent] at hc
  split_ifs at hc with hw
  · have h1 := hxF e (mem_support_iff.mpr hc)
    rw [weight_psiB, hw] at h1
    omega
  · exact hc rfl

theorem psi_le_B {n N : ℕ} (e : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (psiB n N) e ≤ n * Finsupp.weight (1 : Fin N × Fin N → ℕ) e := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  simp only [smul_eq_mul, Pi.one_apply, mul_one]
  have : psiB n N v ≤ n := by
    unfold psiB prowB
    split_ifs <;> omega
  calc e v * psiB n N v ≤ e v * n := Nat.mul_le_mul_left _ this
    _ = n * e v := mul_comm _ _

theorem bound_B {n N : ℕ} (lam : DomWeight N) (g : MvPolynomial (Fin N × Fin N) ℂ) (hg : g ∈ nablaSq ℂ N lam)
    (hg0 : g ≠ 0) (m : Fin n → ℕ) (hm : IsWeightedHomogeneous (wnB n N) g m) :
    PsiB n m ≤ n * ∑ s, lam.natW s := by
  obtain ⟨e, he⟩ := MvPolynomial.ne_zero_iff.mp hg0
  have hhom := dualWeyl_le_homog_B N N lam.natW hg
  rw [mem_homogeneousSubmodule] at hhom
  have h1 : Finsupp.weight (1 : Fin N × Fin N → ℕ) e = ∑ s, lam.natW s := hhom he
  rw [← hm he, ← weight_psiB, ← h1]
  exact psi_le_B e

theorem embGL_unitri_B {n N : ℕ} (h : n + 1 = N) (u : GL (Fin n) ℂ) (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) :
    (∀ a, ((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) a a = 1) ∧
    (∀ a b, a ≠ b → ((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) b a ≠ 0 →
      prowB n N a < prowB n N b) ∧
    (∀ a b, a < b → ((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) b a = 0) := by
  refine ⟨fun a => ?_, fun a b hab hne => ?_, fun a b hab => ?_⟩
  · rw [embGL_apply_B]
    by_cases ha : a.1 < n
    · rw [dite_eq_left ha, dite_eq_left ha]; exact hd _
    · rw [dite_eq_right ha, if_neg ha]
  · have ha2 := a.2
    have hb2 := b.2
    rw [embGL_apply_B] at hne
    by_cases hb : b.1 < n <;> by_cases ha : a.1 < n
    · rw [dite_eq_left hb, dite_eq_left ha] at hne
      have hba : ¬ (a.1 < b.1) := fun hlt => hne (hl _ _ (Fin.mk_lt_mk.mpr hlt))
      have hne' : a.1 ≠ b.1 := fun e => hab (Fin.ext e)
      unfold prowB
      rw [if_pos ha, if_pos hb]
      omega
    · rw [dite_eq_left hb, dite_eq_right ha] at hne; exact absurd rfl hne
    · rw [dite_eq_right hb, if_pos ha] at hne; exact absurd rfl hne
    · exact absurd (Fin.ext (by omega)) hab
  · have ha2 := a.2
    have hb2 := b.2
    rw [embGL_apply_B]
    by_cases hb : b.1 < n <;> by_cases ha : a.1 < n
    · rw [dite_eq_left hb, dite_eq_left ha]
      exact hl _ _ (Fin.mk_lt_mk.mpr (Fin.lt_def.mp hab))
    · exact absurd (lt_trans (Fin.lt_def.mp hab) hb) ha
    · rw [dite_eq_right hb, if_pos ha]
    · have := Fin.lt_def.mp hab
      omega

theorem detPow_unitri_B {n N : ℕ} (h : n + 1 = N) (u : GL (Fin n) ℂ) (hl : ∀ i j, j < i → u i j = 0)
    (hd : ∀ i, u i i = 1) (c : ℤ) : detPow ℂ N (embGL ℂ n N h u) c = 1 := by
  obtain ⟨h1, _, h3⟩ := embGL_unitri_B h u hl hd
  have hdet : (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => h3 j i hij)]
    simp [h1]
  have hu : Matrix.GeneralLinearGroup.det (embGL ℂ n N h u) = 1 := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hdet]
    rfl
  unfold detPow
  rw [hu, one_zpow, Units.val_one]

end PI.WGB
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.RenameTauHomogB

section

@[expose] public section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions MvPolynomial

def swapM {n : ℕ} (σ : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if σ i = j then 1 else 0

theorem swapM_sq {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) : swapM σ * swapM σ = 1 := by
  ext i j
  simp only [swapM, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (σ i)]
  · simp [hσ]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_mul]
  · simp

def swapGL {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) : GL (Fin n) ℂ :=
  ⟨swapM σ, swapM σ, swapM_sq σ hσ, swapM_sq σ hσ⟩

def tauB {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (a : Fin N) : Fin N :=
  if ha : a.1 < n then ⟨(σ ⟨a.1, ha⟩).1, by have := (σ ⟨a.1, ha⟩).isLt; omega⟩ else a

theorem tauB_val {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (a : Fin N) (ha : a.1 < n) :
    (tauB h σ a).1 = (σ ⟨a.1, ha⟩).1 := by
  unfold tauB; rw [dif_pos ha]

theorem tauB_of_not {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (a : Fin N) (ha : ¬ a.1 < n) :
    tauB h σ a = a := by
  unfold tauB; rw [dif_neg ha]

theorem tauB_invol {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) (a : Fin N) :
    tauB h σ (tauB h σ a) = a := by
  by_cases ha : a.1 < n
  · have h2 : (tauB h σ a).1 < n := by rw [tauB_val h σ a ha]; exact (σ _).isLt
    apply Fin.ext
    rw [tauB_val h σ _ h2]
    have e : (⟨(tauB h σ a).1, h2⟩ : Fin n) = σ ⟨a.1, ha⟩ := Fin.ext (tauB_val h σ a ha)
    rw [e, hσ]
  · rw [tauB_of_not h σ a ha, tauB_of_not h σ a ha]

theorem swap_entry_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) (a b : Fin N) :
    ((embGL ℂ n N h (swapGL σ hσ) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) b a =
      if b = tauB h σ a then 1 else 0 := by
  have ha2 := a.2
  have hb2 := b.2
  rw [embGL_apply_B]
  by_cases hb : b.1 < n <;> by_cases ha : a.1 < n
  · rw [dif_pos hb, dif_pos ha]
    show swapM σ ⟨b.1, hb⟩ ⟨a.1, ha⟩ = _
    simp only [swapM, Matrix.of_apply]
    have key : σ ⟨b.1, hb⟩ = ⟨a.1, ha⟩ ↔ b = tauB h σ a := by
      constructor
      · intro e
        apply Fin.ext
        rw [tauB_val h σ a ha, ← e, hσ]
      · intro e
        have e2 : (⟨b.1, hb⟩ : Fin n) = σ ⟨a.1, ha⟩ := Fin.ext (by
          show b.1 = (σ ⟨a.1, ha⟩).1
          rw [← tauB_val h σ a ha, e])
        rw [e2, hσ]
    by_cases hk : b = tauB h σ a
    · rw [if_pos hk, if_pos (key.mpr hk)]
    · rw [if_neg hk, if_neg (fun e => hk (key.mp e))]
  · rw [dif_pos hb, dif_neg ha, tauB_of_not h σ a ha, if_neg (fun e : b = a => ha (e ▸ hb))]
  · have hne : b ≠ tauB h σ a := by
      intro e
      apply hb
      rw [e, tauB_val h σ a ha]
      exact (σ _).isLt
    rw [dif_neg hb, if_pos ha, if_neg hne]
  · have hab : b = a := Fin.ext (by omega)
    rw [dif_neg hb, if_neg ha, tauB_of_not h σ a ha, if_pos hab]

theorem rowAct_swap_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) :
    Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
              (((embGL ℂ n N h (swapGL σ hσ) : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) =
      rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [rowAct_X_B, rename_X]
  rw [Finset.sum_eq_single (tauB h σ v.1)]
  · rw [Matrix.transpose_apply, swap_entry_B, if_pos rfl, map_one, one_mul]
  · intro b _ hb
    rw [Matrix.transpose_apply, swap_entry_B, if_neg hb, map_zero, zero_mul]
  · simp

theorem wnB_tau {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (v : Fin N × Fin N) : wnB n N (tauB h σ v.1, v.2) = fun j => wnB n N v (σ j) := by
  funext j
  by_cases ha : v.1.1 < n
  · have h2 : (tauB h σ v.1).1 < n := by rw [tauB_val h σ _ ha]; exact (σ _).isLt
    dsimp only [wnB]
    rw [dif_pos h2, dif_pos ha]
    have e : (⟨(tauB h σ v.1).1, h2⟩ : Fin n) = σ ⟨v.1.1, ha⟩ := Fin.ext (tauB_val h σ _ ha)
    rw [e, Pi.single_apply, Pi.single_apply]
    by_cases hj : σ j = ⟨v.1.1, ha⟩
    · rw [if_pos hj, if_pos (by rw [← hj, hσ])]
    · rw [if_neg hj, if_neg (fun e => hj (by rw [e, hσ]))]
  · have h2 : ¬ (tauB h σ v.1).1 < n := by rw [tauB_of_not h σ _ ha]; exact ha
    dsimp only [wnB]
    rw [dif_neg h2, dif_neg ha]
    rfl

theorem weight_tau_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (u : Fin N × Fin N →₀ ℕ) :
    Finsupp.weight (wnB n N) (Finsupp.mapDomain (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) u) =
      fun j => Finsupp.weight (wnB n N) u (σ j) := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • wnB n N i) (fun _ => zero_smul _ _)
    (fun _ _ _ => add_smul _ _ _)]
  funext j
  rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Pi.smul_apply, wnB_tau h σ hσ]

theorem rename_tau_homog_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j)
    (g : MvPolynomial (Fin N × Fin N) ℂ) (m : Fin n → ℕ) (hg : IsWeightedHomogeneous (wnB n N) g m) :
    IsWeightedHomogeneous (wnB n N) (rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) g)
      (fun j => m (σ j)) := by
  intro d hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ _ _ hd
  rw [weight_tau_B h σ hσ, hg hu]

theorem rename_tau_inj_B {n N : ℕ} (h : n + 1 = N) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) :
    Function.Injective (rename (R := ℂ) (fun v : Fin N × Fin N => (tauB h σ v.1, v.2))) := by
  apply rename_injective
  intro v w e
  have e1 := congrArg Prod.fst e
  have e2 := congrArg Prod.snd e
  simp only at e1 e2
  have e3 : v.1 = w.1 := by
    rw [← tauB_invol h σ hσ v.1, e1, tauB_invol h σ hσ w.1]
  exact Prod.ext e3 e2

theorem swap_mem_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (W : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hW : IsStable h lam W) (σ : Equiv.Perm (Fin n)) (hσ : ∀ j, σ (σ j) = j) (g : MvPolynomial (Fin N × Fin N) ℂ)
    (hg : g ∈ W) : rename (fun v : Fin N × Fin N => (tauB h σ v.1, v.2)) g ∈ W := by
  have h1 := hW (swapGL σ hσ) g hg
  unfold sqAct at h1
  rw [rowAct_swap_B] at h1
  have hu : detPow ℂ N (embGL ℂ n N h (swapGL σ hσ)) lam.detShift ≠ 0 := Units.ne_zero _
  have := W.smul_mem (detPow ℂ N (embGL ℂ n N h (swapGL σ hσ)) lam.detShift)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ hu, one_smul] at this

theorem PsiB_swap_B {n : ℕ} (m : Fin n → ℕ) (i : ℕ) (hi : i + 1 < n)
    (hlt : m ⟨i, by omega⟩ < m ⟨i + 1, hi⟩) :
    PsiB n m < PsiB n (fun j => m (Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩ j)) := by
  set a : Fin n := ⟨i, by omega⟩ with ha
  set b : Fin n := ⟨i + 1, hi⟩ with hb
  have hab : a ≠ b := by
    intro e
    have := congrArg Fin.val e
    simp [ha, hb] at this
  have split : ∀ f : Fin n → ℕ, ∑ j, f j = f a + f b + ∑ j ∈ (Finset.univ.erase a).erase b, f j := by
    intro f
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩)]
    ring
  rw [PsiB_apply, PsiB_apply, split, split]
  have hrest : ∑ j ∈ (Finset.univ.erase a).erase b, (n - j.1) * m (Equiv.swap a b j) =
      ∑ j ∈ (Finset.univ.erase a).erase b, (n - j.1) * m j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjb := Finset.ne_of_mem_erase hj
    have hja := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj)
    rw [Equiv.swap_apply_of_ne_of_ne hja hjb]
  rw [hrest, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have e1 : n - a.1 = (n - b.1) + 1 := by simp only [ha, hb]; omega
  rw [e1]
  nlinarith

theorem antitone_of_succ_B {n : ℕ} (m : Fin n → ℕ)
    (hdom : ∀ (i : ℕ) (hi : i + 1 < n), m ⟨i + 1, hi⟩ ≤ m ⟨i, by omega⟩) : Antitone m := by
  let M : ℕ → ℕ := fun k => if hk : k < n then m ⟨k, hk⟩ else 0
  have hM : Antitone M := by
    refine antitone_nat_of_succ_le fun k => ?_
    by_cases hk1 : k + 1 < n
    · simp only [M, dif_pos hk1, dif_pos (show k < n by omega)]
      exact hdom k hk1
    · simp only [M, dif_neg hk1]
      exact Nat.zero_le _
  intro a b hab
  have := hM (Fin.le_def.mp hab)
  simp only [M, dif_pos a.2, dif_pos b.2] at this
  exact this

theorem torus_fix_B {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (g : MvPolynomial (Fin N × Fin N) ℂ)
    (m : Fin n → ℕ) (hm : IsWeightedHomogeneous (wnB n N) g m) (t : Fin n → ℂˣ) :
    sqAct ℂ N lam (embGL ℂ n N h (diagGL ℂ n t)) g =
      ((∏ j, t j ^ ((m j : ℤ) + lam.detShift) : ℂˣ) : ℂ) • g := by
  unfold sqAct
  rw [embGL_diag_B, Matrix.diagonal_transpose, rowAct_diag_homog _ _ _ hm, smul_smul]
  congr 1
  have hdet : Matrix.GeneralLinearGroup.det (embGL ℂ n N h (diagGL ℂ n t)) = ∏ j, t j := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, embGL_diag_B, Matrix.det_diagonal, Units.coe_prod]
    subst h
    rw [Fin.prod_univ_castSucc]
    simp [dB]
  unfold detPow
  rw [hdet]
  have hchi : chiB (fun j => ((t j : ℂˣ) : ℂ)) m = ((∏ j, t j ^ (m j) : ℂˣ) : ℂ) := by
    simp [chiB, Units.coe_prod]
  rw [hchi, ← Units.val_mul]
  congr 1
  simp only [zpow_add, Finset.prod_mul_distrib, zpow_natCast, Finset.prod_zpow]
  rw [mul_comm]

theorem highestVec_B : HighestVec := by
  classical
  intro n N h lam W hWle hW hne
  let Pk : ℕ → Prop := fun k =>
    ∃ g ∈ W, g ≠ 0 ∧ ∃ m, IsWeightedHomogeneous (wnB n N) g m ∧ PsiB n m = k
  have hex : ∃ k, Pk k := by
    obtain ⟨f, hfW, hf0⟩ := (Submodule.ne_bot_iff W).mp hne
    by_contra hno
    push_neg at hno
    apply hf0
    rw [← comp_sum_B (wnB n N) f (f.support.image (Finsupp.weight (wnB n N)))
      (fun e he => Finset.mem_image_of_mem _ he)]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_contra hc
    exact hno _ ⟨_, graded_B h lam W hW f hfW m, hc, m, weightedHomogeneousComponent_isWeightedHomogeneous _ _, rfl⟩
  obtain ⟨k0, hk0⟩ := hex
  have hPb : ∀ k, Pk k → k ≤ n * ∑ s, lam.natW s := by
    rintro k ⟨g, hgW, hg0, m, hm, rfl⟩
    exact bound_B lam g (hWle hgW) hg0 m hm
  have hK : Pk (Nat.findGreatest Pk (n * ∑ s, lam.natW s)) := Nat.findGreatest_spec (hPb k0 hk0) hk0
  have hmax : ∀ g ∈ W, g ≠ 0 → ∀ m, IsWeightedHomogeneous (wnB n N) g m →
      PsiB n m ≤ Nat.findGreatest Pk (n * ∑ s, lam.natW s) := by
    intro g hgW hg0 m hm
    exact Nat.le_findGreatest (hPb _ ⟨g, hgW, hg0, m, hm, rfl⟩) ⟨g, hgW, hg0, m, hm, rfl⟩
  obtain ⟨g, hgW, hg0, m, hm, hmK⟩ := hK
  have hfix : ∀ u : GL (Fin n) ℂ, (∀ i j, j < i → u i j = 0) → (∀ i, u i i = 1) →
      sqAct ℂ N lam (embGL ℂ n N h u) g = g := by
    intro u hl hd
    obtain ⟨h1, h2, _⟩ := embGL_unitri_B h u hl hd
    have hs : sqAct ℂ N lam (embGL ℂ n N h u) g = Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
        (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) g := by
      unfold sqAct
      rw [detPow_unitri_B h u hl hd, one_smul]
    rw [hs]
    have hR : Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
        (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose) g - g = 0 := by
      refine high_zero_B h lam W hW _ hmax _ ?_ ?_
      · refine W.sub_mem ?_ hgW
        rw [← hs]
        exact hW u g hgW
      · have := GoodB_homog (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
          (((embGL ℂ n N h u : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ).transpose)) (psiB n N)
          (fun v => GoodB_X_tri _ (fun a => by rw [Matrix.transpose_apply]; exact h1 a)
            (fun a b hab hne => h2 a b hab (by rwa [Matrix.transpose_apply] at hne)) v) g (PsiB n m)
          (homog_psi_B g m hm)
        rwa [hmK] at this
    exact sub_eq_zero.mp hR
  have hdom : ∀ (i : ℕ) (hi : i + 1 < n), m ⟨i + 1, hi⟩ ≤ m ⟨i, by omega⟩ := by
    intro i hi
    by_contra hlt
    push_neg at hlt
    let σ := Equiv.swap (⟨i, by omega⟩ : Fin n) ⟨i + 1, hi⟩
    have hσ : ∀ j, σ (σ j) = j := fun j => Equiv.swap_apply_self _ _ j
    have hgt := PsiB_swap_B m i hi hlt
    have hle := hmax _ (swap_mem_B h lam W hW σ hσ g hgW)
      (fun e => hg0 (rename_tau_inj_B h σ hσ (by rw [e, map_zero])))
      _ (rename_tau_homog_B h σ hσ g m hm)
    rw [← hmK] at hle
    exact absurd hle (not_le.mpr hgt)
  have hanti : Antitone m := antitone_of_succ_B m hdom
  let mu : DomWeight n := ⟨fun j => (m j : ℤ) + lam.detShift, fun a b hab => by
    have := hanti hab
    simp only
    omega⟩
  exact ⟨g, hgW, hg0, mu, hfix, fun t => torus_fix_B h lam g m hm t⟩

end PI.WGB
end
end
end
