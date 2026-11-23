module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaRight
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.IsWeightedHomogeneousPairingLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.KappaMain
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.PolarizationBihomogeneous
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.PolarizationBihomogeneous

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.DivideAll

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace PI.OpWords

theorem wtLe_span (K : Type) [Field K] (k : ℕ) (c : ℤ) (s : Set (Pol K k))
    (hs : ∀ f ∈ s, WtLe K k c f) : ∀ f ∈ Submodule.span K s, WtLe K k c f := by
  intro f hf
  induction hf using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero =>
    intro m hm
    simp at hm
  | add x y _ _ hx hy =>
    intro m hm a
    rcases Finset.mem_union.1 (support_add hm) with h | h
    · exact hx m h a
    · exact hy m h a
  | smul r x _ hx =>
    intro m hm a
    exact hx m (support_smul hm) a

theorem kappa_ad (hL : KappaLeft) (hR : KappaRight) (K : Type) [Field K] [CharZero K] (k d : ℕ)
    (a b : Fin k) (A : Module.End K ↥(homogeneousSubmodule (Fin k) K d)) :
    kappa K k d (Formalism.MainNotions.TestSideCounting.Ed K k d a b * A - A * Formalism.MainNotions.TestSideCounting.Ed K k d a b) =
      Rop K k a b (kappa K k d A) := by
  rw [map_sub, hL K k d a b A, hR K k d a b A]
  rfl

theorem divide_all (hV : Vanish) (hD : DivT) (hRB : RBihom) (hRT : RTT) (hTW : TTWt)
    (K : Type) [Field K] [CharZero K] (k c : ℕ) : ∀ n : ℕ, ∀ (W : Submodule K (Pol K k)),
    W ≤ Bihom K k (c + n) → (∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W) → (∀ f ∈ W, WtLe K k c f) →
    ∀ f ∈ W, ∃ g ∈ Bihom K k c, f = tt K k ^ n * g := by
  intro n
  induction n with
  | zero =>
    intro W hW _ _ f hf
    exact ⟨f, by simpa using hW hf, by simp⟩
  | succ n ih =>
    intro W hW hst hwt f hf
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hf' : f ∈ weightedHomogeneousSubmodule K (wx 0) (c + (n + 1)) ⊓
          weightedHomogeneousSubmodule K (wxi 0) (c + (n + 1)) := hW hf
      have h1 := (Submodule.mem_inf.1 hf').1
      rw [mem_weightedHomogeneousSubmodule] at h1
      rw [mul_zero]
      ext m
      simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
      by_contra h
      have h2 := h1 h
      have h3 : m = 0 := by
        ext v
        rcases v with i | i <;> exact i.elim0
      rw [h3, map_zero] at h2
      omega
    · have htt : tt K k ≠ 0 := by
        intro h
        have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
        simp [tt] at h1
        omega
      have hdiv : ∀ f ∈ W, ∃ g ∈ Bihom K k (c + n), f = tt K k * g := by
        intro f hf
        have hv := hV K k (c + (n + 1)) c W hW hst hwt (by omega) f hf
        obtain ⟨g, hg, rfl⟩ := hD K k (c + (n + 1)) (by omega) f (hW hf) hv
        exact ⟨g, by simpa using hg, rfl⟩
      let W' : Submodule K (Pol K k) := W.comap (LinearMap.mulLeft K (tt K k))
      have hmem : ∀ g, g ∈ W' ↔ tt K k * g ∈ W := fun g => Iff.rfl
      have hW' : W' ≤ Bihom K k (c + n) := by
        intro g hg
        obtain ⟨g', hg', he⟩ := hdiv _ ((hmem g).1 hg)
        rw [mul_left_cancel₀ htt he]
        exact hg'
      have hst' : ∀ f ∈ W', ∀ a b, Rop K k a b f ∈ W' := by
        intro g hg a b
        rw [hmem, ← hRT K k a b g]
        exact hst _ ((hmem g).1 hg) a b
      have hwt' : ∀ f ∈ W', WtLe K k c f := by
        intro g hg
        exact hTW K k c g (hwt _ ((hmem g).1 hg))
      obtain ⟨g, hg, rfl⟩ := hdiv f hf
      obtain ⟨g'', hg'', rfl⟩ := ih W' hW' hst' hwt' g ((hmem g).2 hf)
      exact ⟨g'', hg'', by ring⟩

theorem opWords_of (hI : KappaInj) (hL : KappaLeft) (hR : KappaRight) (hB : KappaBihom)
    (hE : WtOfEig) (hRB : RBihom) (hRT : RTT) (hTW : TTWt) (hD : DivT) (hV : Vanish)
    (hS : Surj) : Formalism.MainNotions.TestSideCounting.OpBound := by
  intro K _ _ k d c WW Sg hst hspan heig A hA
  have key : ∃ c' : ℕ, c' ≤ c ∧ c' ≤ d ∧ ∃ g ∈ Bihom K k c', kappa K k d A = tt K k ^ (d - c') * g := by
    rcases Nat.lt_or_ge c d with hcd | hdc
    · let W : Submodule K (Pol K k) := WW.map (kappa K k d)
      have hW : W ≤ Bihom K k (c + (d - c)) := by
        have e : c + (d - c) = d := by omega
        rw [e]
        rintro f ⟨A', _, rfl⟩
        exact hB K k d A'
      have hWst : ∀ f ∈ W, ∀ a b, Rop K k a b f ∈ W := by
        rintro f ⟨A', hA', rfl⟩ a b
        rw [← kappa_ad hL hR K k d a b A']
        exact Submodule.mem_map_of_mem (hst A' hA' a b)
      have hWwt : ∀ f ∈ W, WtLe K k c f := by
        have hWeq : W = Submodule.span K (kappa K k d '' Sg) := by
          show WW.map (kappa K k d) = _
          rw [hspan, Submodule.map_span]
        rw [hWeq]
        apply wtLe_span
        rintro f ⟨A', hA', rfl⟩ m hm a
        obtain ⟨ω, hω, hωc⟩ := heig A' hA'
        have h1 : Rop K k a a (kappa K k d A') = (ω a : K) • kappa K k d A' := by
          rw [← kappa_ad hL hR K k d a a A', hω a, map_smul]
        have h2 := hE K k a (ω a) (kappa K k d A') h1 m hm
        rw [h2]
        exact_mod_cast hωc a
      obtain ⟨g, hg, he⟩ := divide_all hV hD hRB hRT hTW K k c (d - c) W hW hWst hWwt _
        (Submodule.mem_map_of_mem hA)
      exact ⟨c, le_rfl, hcd.le, g, hg, he⟩
    · exact ⟨d, hdc, le_rfl, kappa K k d A, hB K k d A, by simp⟩
  obtain ⟨c', hc'c, hc'd, g, hg, he⟩ := key
  have hsurj := hS K k d c' hc'd g hg
  rw [← he] at hsurj
  obtain ⟨B, hB', hBe⟩ := Submodule.mem_map.1 hsurj
  have hAB : B = A := hI K k d hBe
  subst hAB
  have hmono : Wc K k d c' ≤ Wc K k d c := by
    unfold Wc
    apply Submodule.span_mono
    rintro Bx ⟨l, hl, rfl⟩
    exact ⟨l, le_trans hl hc'c, rfl⟩
  exact hmono hB'

end PI.OpWords
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.PairingPowMemSymbolRange

section

@[expose] public section

open MvPolynomial Finsupp

noncomputable section

namespace PI.OpWords

variable (K : Type) [Field K] [CharZero K] (k d : ℕ)

def Sc (c : ℕ) : Submodule K (Pol K k) :=
  ((Wc K k d c).map (kappa K k d)).comap (LinearMap.mulLeft K (tt K k ^ (d - c)))

theorem mem_Sc (c : ℕ) (g : Pol K k) :
    g ∈ Sc K k d c ↔ tt K k ^ (d - c) * g ∈ (Wc K k d c).map (kappa K k d) := Iff.rfl

theorem Wc_mono {c c' : ℕ} (h : c ≤ c') : Wc K k d c ≤ Wc K k d c' := by
  unfold Wc
  apply Submodule.span_mono
  rintro Bx ⟨l, hl, rfl⟩
  exact ⟨l, le_trans hl h, rfl⟩

theorem Ed_mul_Wc (c : ℕ) (a b : Fin k) {B : Module.End K ↥(homogeneousSubmodule (Fin k) K d)}
    (hB : B ∈ Wc K k d c) : Formalism.MainNotions.TestSideCounting.Ed K k d a b * B ∈ Wc K k d (c + 1) := by
  unfold Wc at hB ⊢
  induction hB using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    apply Submodule.subset_span
    exact ⟨(a, b) :: l, by simpa using hl, by simp [Formalism.MainNotions.TestSideCounting.EdWord]⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ r hx

theorem wtXSum (m : Fin k ⊕ Fin k →₀ ℕ) : weight (wx k) m = ∑ i, m (Sum.inl i) := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wx, Fintype.sum_sum_type]

theorem wtXiSum (m : Fin k ⊕ Fin k →₀ ℕ) : weight (wxi k) m = ∑ i, m (Sum.inr i) := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, wxi, Fintype.sum_sum_type]

theorem bihom_zero_const (g : Pol K k) (hg : g ∈ Bihom K k 0) : ∃ r : K, g = C r := by
  have hg' : g ∈ weightedHomogeneousSubmodule K (wx k) 0 ⊓ weightedHomogeneousSubmodule K (wxi k) 0 := hg
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hg'
  rw [mem_weightedHomogeneousSubmodule] at h1 h2
  refine ⟨AddMonoidAlgebra.coeff g 0, ?_⟩
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [← hm]
  · by_contra hne
    apply hm
    have e1 := h1 hne
    have e2 := h2 hne
    rw [wtXSum] at e1
    rw [wtXiSum] at e2
    ext v
    rcases v with i | i
    · have h3 := (Finset.sum_eq_zero_iff.1 e1) i (Finset.mem_univ i)
      simp [h3]
    · have h3 := (Finset.sum_eq_zero_iff.1 e2) i (Finset.mem_univ i)
      simp [h3]

theorem bihom_le_Sc : ∀ c, c ≤ d → Bihom K k c ≤ Sc K k d c := by
  intro c
  induction c with
  | zero =>
    intro _ g hg
    obtain ⟨r, rfl⟩ := bihom_zero_const K k g hg
    rw [mem_Sc]
    refine ⟨(r * (d.factorial : K)) • 1, Submodule.smul_mem _ _
      (Submodule.subset_span ⟨[], by simp, by simp [Formalism.MainNotions.TestSideCounting.EdWord]⟩), ?_⟩
    rw [map_smul, symbolMapOne, smul_smul, mul_assoc,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero d)), mul_one, Nat.sub_zero,
      smul_eq_C_mul, mul_comm]
  | succ c ih =>
    intro hc
    have IH := ih (by omega)
    obtain ⟨n, hn⟩ : ∃ n, d - c = n + 1 := ⟨d - c - 1, by omega⟩
    have hn2 : d - (c + 1) = n := by omega
    intro g hg
    have hg' := hg
    rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
      mem_weightedHomogeneousSubmodule] at hg'
    rw [as_sum g]
    apply Submodule.sum_mem
    intro m hmS
    have hne : AddMonoidAlgebra.coeff g m ≠ 0 := MvPolynomial.mem_support_iff.1 hmS
    have hw1 := hg'.1 hne
    have hw2 := hg'.2 hne
    rw [show monomial m (AddMonoidAlgebra.coeff g m) = AddMonoidAlgebra.coeff g m • monomial m (1 : K) by rw [smul_monomial, smul_eq_mul, mul_one]]
    apply Submodule.smul_mem

    rw [wtXSum] at hw1
    rw [wtXiSum] at hw2
    obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw1]; omega)
    obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hw2]; omega)
    obtain ⟨m', rfl⟩ : ∃ m' : Fin k ⊕ Fin k →₀ ℕ,
        m = m' + single (Sum.inl a) 1 + single (Sum.inr b) 1 := by
      refine ⟨m - single (Sum.inl a) 1 - single (Sum.inr b) 1, ?_⟩
      ext i
      rcases i with i | i
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, single_apply,
          Sum.inl.injEq, reduceCtorEq, if_false]
        split_ifs with h
        · subst h; omega
        · omega
      · simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, single_apply,
          Sum.inr.injEq, reduceCtorEq, if_false]
        split_ifs with h
        · subst h; omega
        · omega
    have hmono : X (Sum.inl a) * X (Sum.inr b) * monomial m' (1 : K) =
        monomial (m' + single (Sum.inl a) 1 + single (Sum.inr b) 1) 1 := by
      simp only [X, monomial_mul, one_mul]
      congr 1
      abel
    have hw1' : weight (wx k) m' = c := by
      have := hw1
      rw [← wtXSum, map_add (f := _), map_add (f := _), weight_single, weight_single] at this
      have e1 : wx k (Sum.inl a) = 1 := rfl
      have e2 : wx k (Sum.inr b) = 0 := rfl
      rw [e1, e2, smul_eq_mul, smul_eq_mul] at this
      omega
    have hw2' : weight (wxi k) m' = c := by
      have := hw2
      rw [← wtXiSum, map_add (f := _), map_add (f := _), weight_single, weight_single] at this
      have e1 : wxi k (Sum.inl a) = 0 := rfl
      have e2 : wxi k (Sum.inr b) = 1 := rfl
      rw [e1, e2, smul_eq_mul, smul_eq_mul] at this
      omega
    have hh : monomial m' (1 : K) ∈ Bihom K k c := by
      rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
        mem_weightedHomogeneousSubmodule]
      exact ⟨isWeightedHomogeneous_monomial _ _ _ hw1', isWeightedHomogeneous_monomial _ _ _ hw2'⟩
    have hh' : X (Sum.inl a) * pderiv (Sum.inl b) (monomial m' (1 : K)) ∈ Bihom K k c := by
      rw [Bihom, Submodule.mem_inf, mem_weightedHomogeneousSubmodule,
        mem_weightedHomogeneousSubmodule] at hh ⊢
      exact ⟨iwh_X_pderiv _ _ _ (by simp [wx]) hh.1, iwh_X_pderiv _ _ _ (by simp [wxi]) hh.2⟩
    obtain ⟨B, hB, hBk⟩ := (mem_Sc K k d c _).1 (IH hh)
    obtain ⟨B', hB', hB'k⟩ := (mem_Sc K k d c _).1 (IH hh')
    rw [hn] at hBk hB'k
    rw [mem_Sc, hn2, ← hmono]
    refine ⟨(((n + 1 : ℕ) : K)⁻¹) • (Formalism.MainNotions.TestSideCounting.Ed K k d a b * B - B'),
      Submodule.smul_mem _ _ (Submodule.sub_mem _ (Ed_mul_Wc K k d c a b hB)
        (Wc_mono K k d (Nat.le_succ c) hB')), ?_⟩
    rw [map_smul, map_sub, symbolMapMulLeft, hBk, hB'k, Derivation.leibniz, Derivation.leibniz_pow,
      pderiv_inl_tt, Nat.add_sub_cancel, smul_eq_C_mul]
    simp only [smul_eq_mul, nsmul_eq_mul]
    have hC : (C (((n + 1 : ℕ) : K)⁻¹) : Pol K k) * ((n + 1 : ℕ) : Pol K k) = 1 := by
      rw [← map_natCast (C : K →+* Pol K k), ← map_mul,
        inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)), map_one]
    linear_combination (tt K k ^ n * (X (Sum.inl a) * X (Sum.inr b) * monomial m' (1 : K))) * hC

theorem pairingPowMemSymbolRange : Surj := by
  intro K _ _ k d c hc g hg
  exact (mem_Sc K k d c g).1 (bihom_le_Sc K k d c hc hg)

end PI.OpWords
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialDifferentialWords.Assemble

section

@[expose] public section

namespace PI.OpWords

theorem opBound_of_vanish (hV : Vanish) : Formalism.MainNotions.TestSideCounting.OpBound :=
  opWords_of symbolMapInjective symbolMapMulLeft symbolMapMulRight symbolMapBihomogeneous weightOfEigenvector
    polarizationBihomogeneous rttRelation pairingWeightCancel pairingDivisibility hV pairingPowMemSymbolRange

end PI.OpWords
end
end
