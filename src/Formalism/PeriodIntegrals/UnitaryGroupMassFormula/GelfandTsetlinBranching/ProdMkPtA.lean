module

public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ExtremalFacts
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LSatLemmas
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.CoeffRowActDiagA
import Mathlib.Tactic.Polynomial.Basic
import Formalism.LocalRingCardinality.Params

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.StepACleared

section

@[expose] public section

noncomputable section

namespace PI.WGB

open Formalism.GradedWeylDivisibility MvPolynomial

variable {n : ℕ}

def RInvA (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) : Prop :=
  ∀ (x : Fin (n + 1) × Fin (n + 1) → ℂ) (a b : Fin (n + 1)) (t : ℂ), a < b → b.val < n →
    φ (lhwline_rowOp a b t x) = φ x

theorem mrow_invA (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) (hφ : RInvA φ) (p : Fin (n + 1))
    (t : Fin (n + 1) → ℂ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) (S : Finset (Fin (n + 1)))
    (hS : ∀ b ∈ S, p < b ∧ b.val < n) :
    φ (lhwline_mrow p S t x) = φ x := by
  induction S using Finset.induction_on with
  | empty =>
    congr 1
  | insert b S hb ih =>
    have hpS : p ∉ S := fun h => lt_irrefl p (hS p (Finset.mem_insert_of_mem h)).1
    have hpb := hS b (Finset.mem_insert_self b S)
    have heq : lhwline_mrow p (insert b S) t x = lhwline_rowOp p b (t b) (lhwline_mrow p S t x) := by
      funext v
      simp only [lhwline_mrow, lhwline_rowOp, Finset.mem_insert]
      by_cases hv : v.1 = b
      · simp [hv, hb, hpS]
      · simp [hv]
    rw [heq, hφ _ p b _ hpb.1 hpb.2, ih fun b' hb' => hS b' (Finset.mem_insert_of_mem hb')]

def stepA (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Fin (n + 1) × Fin (n + 1) → ℂ :=
  let y := lhwline_mrow p (Finset.univ.filter fun b => p < b ∧ b.val < n) (fun b => -(x (b, q) / x (p, q))) x
  lhwline_mcol q (Finset.univ.filter fun j => q < j) (fun j => -(y (p, j) / y (p, q))) y

theorem stepA_inv (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) (hR : RInvA φ) (hC : lhwline_CInv φ)
    (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : φ (stepA p q x) = φ x := by
  unfold stepA
  simp only
  rw [lhwline_mcol_inv φ hC _ _ _ _ (fun j hj => (Finset.mem_filter.mp hj).2),
    mrow_invA φ hR _ _ _ _ (fun b hb => (Finset.mem_filter.mp hb).2)]

def elimA : ℕ → (Fin (n + 1) × Fin (n + 1) → ℂ) → (Fin (n + 1) × Fin (n + 1) → ℂ)
  | 0, x => x
  | k + 1, x =>
    if h : k < n then stepA ⟨k, by omega⟩ ⟨k, by omega⟩ (elimA k x) else elimA k x

theorem elimA_inv (φ : (Fin (n + 1) × Fin (n + 1) → ℂ) → ℂ) (hR : RInvA φ) (hC : lhwline_CInv φ)
    (k : ℕ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : φ (elimA k x) = φ x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [elimA]
    split_ifs
    · rw [stepA_inv φ hR hC, ih]
    · exact ih

def clearedA (k : ℕ) (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Prop :=
  ∀ (a j : Fin (n + 1)), a.val < n → a.val ≠ j.val → (a.val < k ∨ j.val < k) → x (a, j) = 0

theorem stepA_apply (p q : Fin (n + 1)) (x : Fin (n + 1) × Fin (n + 1) → ℂ) (a j : Fin (n + 1)) :
    stepA p q x (a, j) =
      (if p < a ∧ a.val < n then x (a, j) + -(x (a, q) / x (p, q)) * x (p, j) else x (a, j)) +
      (if q < j then -(x (p, j) / x (p, q)) *
        (if p < a ∧ a.val < n then x (a, q) + -(x (a, q) / x (p, q)) * x (p, q) else x (a, q)) else 0) := by
  simp only [stepA, lhwline_mcol, lhwline_mrow, Finset.mem_filter, Finset.mem_univ, true_and,
    lt_irrefl, false_and, if_false]
  split_ifs <;> ring

theorem stepA_cleared (k : ℕ) (hk : k < n) (y : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hy : clearedA k y) (hp : y (⟨k, by omega⟩, ⟨k, by omega⟩) ≠ 0) :
    clearedA (k + 1) (stepA ⟨k, by omega⟩ ⟨k, by omega⟩ y) := by
  intro a j ha hne hlt
  rw [stepA_apply]
  simp only [Fin.lt_def]
  rcases lt_trichotomy j.val k with hj | hj | hj
  · have h1 : y (⟨k, by omega⟩, j) = 0 := hy _ _ (by show k < n; omega) (by show k ≠ j.val; omega) (Or.inr hj)
    have h2 : y (a, j) = 0 := hy _ _ ha hne (Or.inr hj)
    rw [if_neg (show ¬ k < j.val by omega)]
    split_ifs <;> simp [h1, h2]
  · have hjq : j = ⟨k, by omega⟩ := Fin.ext hj
    rw [hjq]
    simp only [Fin.val_mk, lt_irrefl, if_false, add_zero]
    split_ifs with ha'
    · rw [neg_mul, div_mul_cancel₀ _ hp, add_neg_cancel]
    · rw [← hjq]
      exact hy _ _ ha hne (Or.inl (by omega))
  · have ha2 : a.val ≤ k := by omega
    have hka : ¬ (k < a.val ∧ a.val < n) := by omega
    simp only [if_neg hka, if_pos hj]
    rcases lt_or_eq_of_le ha2 with ha2 | ha2
    · have h1 : y (a, j) = 0 := hy _ _ ha hne (Or.inl ha2)
      have h2 : y (a, ⟨k, by omega⟩) = 0 := hy _ _ ha (by show a.val ≠ k; omega) (Or.inl ha2)
      simp [h1, h2]
    · have hap : a = ⟨k, by omega⟩ := Fin.ext ha2
      rw [hap, neg_mul, div_mul_cancel₀ _ hp, add_neg_cancel]

theorem pivotA_ne (k : ℕ) (hk : k < n) (y : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hy : clearedA k y) (hd : eval y (lpMinor ℂ (k + 1) (by omega) (by omega) :
      MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0) :
    y (⟨k, by omega⟩, ⟨k, by omega⟩) ≠ 0 := by
  unfold lpMinor at hd
  rw [RingHom.map_det] at hd
  have hM : (eval y).mapMatrix (Matrix.of fun p q : Fin (k + 1) =>
      (X (Fin.castLE (show k + 1 ≤ n + 1 by omega) p, Fin.castLE (show k + 1 ≤ n + 1 by omega) q) :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) =
      Matrix.diagonal (fun p => y (Fin.castLE (show k + 1 ≤ n + 1 by omega) p,
        Fin.castLE (show k + 1 ≤ n + 1 by omega) p)) := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_X,
      Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · have hpq : p.val ≠ q.val := fun e => h (Fin.ext e)
      have := p.isLt
      have := q.isLt
      apply hy
      · simp only [Fin.val_castLE]; omega
      · simpa using hpq
      · simp only [Fin.val_castLE]; omega
  rw [hM, Matrix.det_diagonal] at hd
  have := Finset.prod_ne_zero_iff.mp hd (Fin.last k) (Finset.mem_univ _)
  convert this using 3 <;> ext <;> simp

theorem minorA_RInv (s : ℕ) (hr : s ≤ n + 1) :
    RInvA (fun x : Fin (n + 1) × Fin (n + 1) → ℂ => eval x (lpMinor ℂ s hr hr)) :=
  fun x a b t hab _ => lhwline_minor_RInv s hr hr x a b t hab

theorem elimA_cleared (x : Fin (n + 1) × Fin (n + 1) → ℂ)
    (hx : ∀ (s : ℕ) (hs : s + 1 ≤ n), eval x (lpMinor ℂ (s + 1) (by omega) (by omega) :
      MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0) :
    ∀ k, k ≤ n → clearedA k (elimA k x) := by
  intro k
  induction k with
  | zero =>
    intro _ a j _ _ h
    omega
  | succ k ih =>
    intro hk
    have hkn : k < n := by omega
    have hc := ih (by omega)
    simp only [elimA, dif_pos hkn]
    apply stepA_cleared k hkn _ hc
    apply pivotA_ne k hkn _ hc
    have hk1 : k + 1 ≤ n + 1 := by omega
    rw [elimA_inv (fun y => eval y (lpMinor ℂ (k + 1) hk1 hk1 :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ))
      (minorA_RInv _ _) (lhwline_minor_CInv _ _ _)]
    exact hx k hkn

theorem vanishA (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hR : RInvA (fun x => eval x g)) (hC : lhwline_CInv (fun x => eval x g))
    (hD : ∀ D : Fin (n + 1) × Fin (n + 1) → ℂ,
      (∀ a j : Fin (n + 1), a.val < n → a ≠ j → D (a, j) = 0) → eval D g = 0) :
    g = 0 := by
  set P : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ := ∏ s : Fin n,
    lpMinor ℂ (s.val + 1) (by have := s.isLt; omega) (by have := s.isLt; omega) with hPdef
  have hP : P ≠ 0 := by
    intro h
    have := congrArg (eval (idPoint ℂ (n + 1) (n + 1))) h
    simp only [hPdef, map_prod, eval_idPoint_lpMinor, Finset.prod_const_one, map_zero] at this
    exact one_ne_zero this
  have hgP : g * P = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, map_zero]
    by_cases hx : ∀ (s : ℕ) (hs : s + 1 ≤ n), eval x (lpMinor ℂ (s + 1) (by omega) (by omega) :
        MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) ≠ 0
    · have h1 : eval x g = eval (elimA n x) g :=
        (elimA_inv (fun y => eval y g) hR hC n x).symm
      rw [h1, hD _ (fun a j ha h => elimA_cleared x hx n le_rfl a j ha
        (fun e => h (Fin.ext e)) (Or.inl ha)), zero_mul]
    · push Not at hx
      obtain ⟨s, hs, hs0⟩ := hx
      have : eval x P = 0 := by
        rw [hPdef, map_prod]
        exact Finset.prod_eq_zero (i := ⟨s, by omega⟩) (Finset.mem_univ _) hs0
      rw [this, mul_zero]
  rcases mul_eq_zero.mp hgP with h | h
  · exact h
  · exact absurd h hP

end PI.WGB
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.ProdMkPtA

section

@[expose] public section

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

variable {n : ℕ}

def mStarA (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) : Fin (n + 1) × Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v =>
    Fin.lastCases (Fin.lastCases (ν (Fin.last n)) (fun k => ν (Fin.castSucc k) - kap k) v.2)
      (fun a => Fin.lastCases 0 (fun k => if k = a then kap a else 0) v.2) v.1

@[simp] theorem mStarA_cc (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (a k : Fin n) :
    mStarA kap ν (Fin.castSucc a, Fin.castSucc k) = if k = a then kap a else 0 := by
  simp [mStarA]

@[simp] theorem mStarA_cl (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (a : Fin n) :
    mStarA kap ν (Fin.castSucc a, Fin.last n) = 0 := by
  simp [mStarA]

@[simp] theorem mStarA_lc (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (k : Fin n) :
    mStarA kap ν (Fin.last n, Fin.castSucc k) = ν (Fin.castSucc k) - kap k := by
  simp [mStarA]

@[simp] theorem mStarA_ll (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) :
    mStarA kap ν (Fin.last n, Fin.last n) = ν (Fin.last n) := by
  simp [mStarA]

def IsDPtA (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Prop :=
  ∀ a j : Fin (n + 1), a.val < n → a ≠ j → x (a, j) = 0

theorem mono_eq_A (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hcol : IsWeightedHomogeneous (colW (n + 1) (n + 1)) g ν)
    (hrow : ∀ m ∈ g.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kap a)
    (x : Fin (n + 1) × Fin (n + 1) → ℂ) (hx : IsDPtA x) (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ)
    (hm : m ∈ g.support) (hne : ∏ v, x v ^ m v ≠ 0) : m = mStarA kap ν := by
  have hz : ∀ v, x v = 0 → m v = 0 := by
    intro v hv
    by_contra h
    exact hne (Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, zero_pow h]))
  have htop : ∀ (a : Fin n) (s : Fin (n + 1)), s ≠ Fin.castSucc a → m (Fin.castSucc a, s) = 0 :=
    fun a s hs => hz _ (hx _ _ (by simp) (Ne.symm hs))
  have hdiag : ∀ a : Fin n, m (Fin.castSucc a, Fin.castSucc a) = kap a := by
    intro a
    rw [← hrow m hm a, Finset.sum_eq_single (Fin.castSucc a)]
    · intro s _ hs
      exact htop a s hs
    · simp
  have hcolsum : ∀ j, ∑ ρ, m (ρ, j) = ν j := by
    intro j
    rw [← lhwline_weight_col, hcol (mem_support_iff.mp hm)]
  ext ⟨ρ, s⟩
  induction ρ using Fin.lastCases with
  | last =>
    induction s using Fin.lastCases with
    | last =>
      have h := hcolsum (Fin.last n)
      rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (fun a _ => htop a _ (Fin.castSucc_lt_last a).ne'),
        zero_add] at h
      rw [mStarA_ll, h]
    | cast k =>
      have h := hcolsum (Fin.castSucc k)
      rw [Fin.sum_univ_castSucc, Finset.sum_eq_single k] at h
      · rw [hdiag] at h
        rw [mStarA_lc]
        omega
      · intro b _ hb
        exact htop b _ (fun e => hb (Fin.castSucc_injective _ e).symm)
      · simp
  | cast a =>
    induction s using Fin.lastCases with
    | last =>
      rw [mStarA_cl]
      exact htop a _ (Fin.castSucc_lt_last a).ne'
    | cast k =>
      rw [mStarA_cc]
      split_ifs with hka
      · subst hka
        exact hdiag k
      · exact htop a _ (fun e => hka (Fin.castSucc_injective _ e))

theorem eval_D_A (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hcol : IsWeightedHomogeneous (colW (n + 1) (n + 1)) g ν)
    (hrow : ∀ m ∈ g.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kap a)
    (x : Fin (n + 1) × Fin (n + 1) → ℂ) (hx : IsDPtA x) :
    eval x g = AddMonoidAlgebra.coeff g (mStarA kap ν) * ∏ v, x v ^ (mStarA kap ν) v := by
  rw [MvPolynomial.eval_eq']
  by_cases hs : mStarA kap ν ∈ g.support
  · rw [Finset.sum_eq_single (mStarA kap ν)]
    · intro m hm hne
      by_contra hz
      have hprod : ∏ v, x v ^ m v ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
      exact hne (mono_eq_A kap ν g hcol hrow x hx m hm hprod)
    · intro h
      exact absurd hs h
  · have hc : AddMonoidAlgebra.coeff g (mStarA kap ν) = 0 := by
      by_contra h
      exact hs (MvPolynomial.mem_support_iff.mpr h)
    rw [hc, zero_mul]
    refine Finset.sum_eq_zero fun m hm => ?_
    by_contra hz
    have hprod : ∏ v, x v ^ m v ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
    exact hs (mono_eq_A kap ν g hcol hrow x hx m hm hprod ▸ hm)

def kapA (lam : DomWeight (n + 1)) (mu : DomWeight n) (a : Fin n) : ℕ := (mu.w a - lam.detShift).toNat

theorem props_A (lam : DomWeight (n + 1)) (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hf : f ∈ nablaSq ℂ (n + 1) lam) (hfix : IsFixedW rfl lam mu f) :
    IsWeightedHomogeneous (colW (n + 1) (n + 1)) f lam.natW ∧ RInvA (fun x => eval x f) ∧
      lhwline_CInv (fun x => eval x f) ∧
      ∀ m ∈ f.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kapA lam mu a := by
  refine ⟨(lsat_mem_dualWeyl.mp hf).1, ?_, ?_, ?_⟩
  · intro x a b t hab hb
    have ha : a.val < n := lt_trans hab hb
    have h1 : a = Fin.castSucc ⟨a.val, ha⟩ := Fin.ext rfl
    have h2 : b = Fin.castSucc ⟨b.val, hb⟩ := Fin.ext rfl
    simp only
    rw [h1, h2]
    exact fixed_rowOp_A lam mu f hfix _ _ (by rw [Fin.lt_def] at hab ⊢; exact hab) t x
  · exact lhwline_CInv_of f (fun l j hlj c => ((dualWeylPoint ℂ (n + 1) (n + 1) lam.natW f).mp hf).2 l j hlj c)
  · intro m hm a
    have := fixed_rowDeg_A lam mu f hfix m hm a
    unfold kapA
    omega

def mkPtA (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) : Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun v => Fin.lastCases (z v.2) (fun a => Fin.lastCases 0 (fun k => if k = a then dv a else 0) v.2) v.1

theorem mkPtA_D (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) : IsDPtA (mkPtA dv z) := by
  intro a j ha hne
  obtain ⟨a', rfl⟩ : ∃ a' : Fin n, a = Fin.castSucc a' := ⟨⟨a.val, ha⟩, Fin.ext rfl⟩
  induction j using Fin.lastCases with
  | last => simp [mkPtA]
  | cast k =>
    simp only [mkPtA, Fin.lastCases_castSucc]
    rw [if_neg]
    rintro rfl
    exact hne rfl

theorem prod_mkPtA (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) :
    ∏ v, mkPtA dv z v ^ (mStarA kap ν) v =
      (∏ a, dv a ^ kap a) * (∏ k : Fin n, z (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k)) *
        z (Fin.last n) ^ ν (Fin.last n) := by
  have hpw : ∀ a' k : Fin n, (if k = a' then dv a' else 0) ^ (if k = a' then kap a' else 0) =
      if k = a' then dv a' ^ kap a' else 1 := by
    intro a' k
    split_ifs <;> simp
  rw [Fintype.prod_prod_type]
  simp [Fin.prod_univ_castSucc, mkPtA, hpw, mul_assoc]

end PI.WGB
end
end
end
