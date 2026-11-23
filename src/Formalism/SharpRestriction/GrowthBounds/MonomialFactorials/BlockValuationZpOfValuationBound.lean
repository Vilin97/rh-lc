module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfLatticeInclusion
public import Formalism.MahlerMeasure.GoodCount
public import Formalism.PolynomialDimension.MultinomialDepth.PartnerM
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
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.DegSubSingle

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M

section Comm

variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem pderiv_glAct (LL : M.Letters N) (J : ℕ) (a : Fin N) (c c' d' : Fin r)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    pderiv (a, c) (M.glAct p LL J c' d' x) = M.glAct p LL J c' d' (pderiv (a, c) x) +
      (if (a : ℕ) < J then
        (if LL.vec a then (if c = c' then pderiv (a, d') x else 0) else (if c = d' then -pderiv (a, c') x else 0))
       else 0) := by
  classical
  have hcomm : ∀ (u v : Fin N × Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
      pderiv u (pderiv v y) = pderiv v (pderiv u y) := by
    intro u v y
    refine MvPolynomial.induction_on' y (fun s b => ?_) (fun q q' hq hq' => ?_)
    · simp only [pderiv_monomial]
      by_cases huv : u = v
      · subst huv
        rfl
      · have h1 : (s - Finsupp.single v 1 : Fin N × Fin r →₀ ℕ) u = s u := by
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (Ne.symm huv), Nat.sub_zero]
        have h2 : (s - Finsupp.single u 1 : Fin N × Fin r →₀ ℕ) v = s v := by
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg huv, Nat.sub_zero]
        rw [h1, h2, tsub_right_comm, mul_assoc, mul_assoc, mul_comm ((s u : ℚ_[p]))]
    · simp only [map_add (f := _), hq, hq']
  have hg : ∀ y, M.glAct p LL J c' d' y = ∑ i : Fin N, (if (i : ℕ) < J then
      (if LL.vec i then X (i, c') * pderiv (i, d') y else -(X (i, d') * pderiv (i, c') y)) else 0) := by
    intro y
    simp only [M.glAct, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  have key : ∀ i : Fin N, pderiv (a, c) (if (i : ℕ) < J then
      (if LL.vec i then X (i, c') * pderiv (i, d') x else -(X (i, d') * pderiv (i, c') x)) else 0) =
      (if (i : ℕ) < J then (if LL.vec i then X (i, c') * pderiv (i, d') (pderiv (a, c) x)
        else -(X (i, d') * pderiv (i, c') (pderiv (a, c) x))) else 0) +
      (if a = i then (if (i : ℕ) < J then (if LL.vec i then (if c = c' then pderiv (i, d') x else 0)
        else (if c = d' then -pderiv (i, c') x else 0)) else 0) else 0) := by
    intro i
    by_cases hi : (i : ℕ) < J
    · by_cases hv : LL.vec i
      · simp only [hi, hv, if_true, pderiv_mul, pderiv_X, Pi.single_apply]
        rw [hcomm (a, c) (i, d') x]
        by_cases hai : a = i
        · subst hai
          by_cases hcc : c = c'
          · subst hcc
            simp
            try abel
          · simp [hcc, Ne.symm hcc]
        · have hne : (i, c') ≠ (a, c) := fun h' => hai (congrArg Prod.fst h').symm
          simp [hai, hne]
      · simp only [hi, hv, if_true, Bool.false_eq_true, if_false, map_neg, pderiv_mul, pderiv_X,
          Pi.single_apply]
        rw [hcomm (a, c) (i, c') x]
        by_cases hai : a = i
        · subst hai
          by_cases hcd : c = d'
          · subst hcd
            simp
            try abel
          · simp [hcd, Ne.symm hcd]
        · have hne : (i, d') ≠ (a, c) := fun h' => hai (congrArg Prod.fst h').symm
          simp [hai, hne]
    · simp [hi]

  rw [hg, hg, map_sum, Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib,
  Finset.sum_ite_eq]
  simp

theorem pderiv_keep {σ : Type} (v : σ) (Q Q' : Set (σ →₀ ℕ))
    (h : ∀ m ∈ Q, 1 ≤ m v → m - Finsupp.single v 1 ∈ Q') :
    ∀ x ∈ restrictSupport ℚ_[p] Q, pderiv v x ∈ restrictSupport ℚ_[p] Q' := by
  intro x hx
  have hx' := (mem_restrictSupport_iff ℚ_[p]).mp hx

  rw [x.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [pderiv_monomial]
  by_cases hmv : m v = 0
  · simp [hmv]
  · rw [mem_restrictSupport_iff]
    intro m' hm'
    have h1 := support_monomial_subset hm'
    rw [Finset.mem_singleton] at h1
    rw [h1]
    exact h m (hx' hm) (Nat.one_le_iff_ne_zero.mpr hmv)

theorem wt_sub_single (LL : M.Letters N) (J : ℕ) (a : Fin N) (c c0 : Fin r) (m : Fin N × Fin r →₀ ℕ)
    (h : 1 ≤ m (a, c)) :
    M.wt LL J c0 (m - Finsupp.single (a, c) 1) =
      M.wt LL J c0 m - (if (a : ℕ) < J ∧ c = c0 then (if LL.vec a then 1 else -1) else 0) := by
  have key : ∀ i, (((m - Finsupp.single (a, c) 1 : Fin N × Fin r →₀ ℕ)) (i, c0) : ℤ) =
      (m (i, c0) : ℤ) - (if i = a ∧ c = c0 then 1 else 0) := by
    intro i
    rw [Finsupp.tsub_apply, Finsupp.single_apply]
    by_cases hh : i = a ∧ c = c0
    · obtain ⟨rfl, rfl⟩ := hh
      rw [if_pos rfl, if_pos ⟨rfl, rfl⟩, Nat.cast_sub h]
      simp
    · rw [if_neg, if_neg hh]
      · simp
      · intro h'
        apply hh
        simp only [Prod.mk.injEq] at h'
        exact ⟨h'.1.symm, h'.2⟩
  unfold M.wt
  simp only [key]
  rw [show (if (a : ℕ) < J ∧ c = c0 then (if LL.vec a then (1 : ℤ) else -1) else 0) =
      ∑ i : Fin N, (if (i : ℕ) < J then (if LL.vec i then (if i = a ∧ c = c0 then (1 : ℤ) else 0)
        else -(if i = a ∧ c = c0 then 1 else 0)) else 0) from ?_]
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> ring
  · rw [Finset.sum_eq_single a]
    · by_cases h1 : (a : ℕ) < J <;> by_cases h2 : c = c0 <;> by_cases h3 : LL.vec a <;> simp [h1, h2, h3]
    · intro b _ hb
      simp [hb]
    · simp

variable [NeZero r]

theorem ycond_vec (LL LL' : M.Letters N) (h : LL.vec = LL'.vec) (J : ℕ) (Mt : WithTop ℤ) :
    M.YCond p (r := r) LL J Mt = M.YCond p (r := r) LL' J Mt := by
  obtain ⟨v, d⟩ := LL
  obtain ⟨v', d'⟩ := LL'
  simp only at h
  subst h
  rfl

theorem pderiv_ycond (LL : M.Letters N) (J : ℕ) (Mt : WithTop ℤ) (a : Fin N) (hva : (a : ℕ) < J → LL.vec a = true)
    (c : Fin r) (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ M.YCond p (r := r) LL J Mt) :
    pderiv (a, c) x ∈ M.YCond p (r := r) LL J Mt := by
  classical
  obtain ⟨S', hS'⟩ : ∃ S' : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]),
      S' = Submodule.span ℚ_[p] {z | ∃ (c'' : Fin r) (y : MvPolynomial (Fin N × Fin r) ℚ_[p]),
        y ∈ M.YCond p (r := r) LL J Mt ∧ z = pderiv (a, c'') y} := ⟨_, rfl⟩
  have hgen : ∀ (c'' : Fin r) y, y ∈ M.YCond p (r := r) LL J Mt → pderiv (a, c'') y ∈ S' := by
    intro c'' y hy
    rw [hS']
    exact Submodule.subset_span ⟨c'', y, hy, rfl⟩
  have hsupp : S' ≤ MvPolynomial.restrictSupport ℚ_[p]
      {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [hS', Submodule.span_le]
    rintro _ ⟨c'', y, hy, rfl⟩
    refine pderiv_keep (a, c'') _ _ ?_ y (Formalism.CountingSumsFrames.ycond_le_supp LL J Mt hy)
    intro m hm h1
    simp only [Set.mem_setOf_eq] at hm ⊢
    rw [wt_sub_single LL J a c'' 0 m h1]
    refine le_trans (WithTop.coe_le_coe.mpr ?_) hm
    by_cases ha : (a : ℕ) < J
    · have hv := hva ha
      by_cases hc : c'' = 0 <;> simp [ha, hv, hc]
    · simp [ha]
  have hstab : M.GlStable p LL J S' := by
    intro c d z hz
    rw [hS'] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c'', y, hy, rfl⟩ := hz
      have e := pderiv_glAct LL J a c'' c d y
      have hy' : M.glAct p LL J c d y ∈ M.YCond p (r := r) LL J Mt :=
        Formalism.CountingSumsFrames.ycond_glStable LL J Mt c d y hy
      have hext : (if (a : ℕ) < J then
          (if LL.vec a then (if c'' = c then pderiv (a, d) y else 0)
            else (if c'' = d then -pderiv (a, c) y else 0)) else 0) ∈ S' := by
        split_ifs
        · exact hgen d y hy
        · exact S'.zero_mem
        · exact S'.neg_mem (hgen c y hy)
        · exact S'.zero_mem
        · exact S'.zero_mem
      rw [show M.glAct p LL J c d (pderiv (a, c'') y) = pderiv (a, c'') (M.glAct p LL J c d y) -
        (if (a : ℕ) < J then (if LL.vec a then (if c'' = c then pderiv (a, d) y else 0)
            else (if c'' = d then -pderiv (a, c) y else 0)) else 0) by rw [e]; abel]
      exact S'.sub_mem (hgen c'' _ hy') hext
    | zero => simp
    | add z z' _ _ hz hz' =>
      rw [map_add (f := _)]
      exact S'.add_mem hz hz'
    | smul t z _ hz =>
      rw [map_smul]
      exact S'.smul_mem t hz
  have hle : S' ≤ M.YCond p (r := r) LL J Mt := by
    unfold M.YCond
    exact le_sSup ⟨hsupp, hstab⟩
  exact hle (hgen c x hx)

theorem tieF_ycond (LL : M.Letters N) (J : ℕ) (Mt : WithTop ℤ) (W E : Fin N) (hW : (W : ℕ) < J) (hE : (E : ℕ) < J)
    (hvW : LL.vec W = true) (hvE : LL.vec E = false)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) (hx : x ∈ M.YCond p (r := r) LL J Mt) :
    tieF (fun c => (W, c)) (fun c => (E, c)) x ∈ M.YCond p (r := r) LL J Mt := by
  classical
  have ht : ∀ y : MvPolynomial (Fin N × Fin r) ℚ_[p], tieF (fun c => (W, c)) (fun c => (E, c)) y =
      ∑ c0 : Fin r, pderiv (W, c0) (pderiv (E, c0) y) := by
    intro y
    simp [tieF, LinearMap.sum_apply]
  refine Formalism.CountingSumsFrames.ycond_keep LL J Mt (tieF (fun c => (W, c)) (fun c => (E, c))) ?_ ?_ x hx
  · intro c d y
    have step : ∀ c0, pderiv (W, c0) (pderiv (E, c0) (M.glAct p LL J c d y)) =
        M.glAct p LL J c d (pderiv (W, c0) (pderiv (E, c0) y)) +
        (if c0 = c then pderiv (W, d) (pderiv (E, c0) y) else 0) +
        (if c0 = d then -pderiv (W, c0) (pderiv (E, c) y) else 0) := by
      intro c0
      rw [pderiv_glAct LL J E c0 c d y, map_add (f := _), pderiv_glAct LL J W c0 c d (pderiv (E, c0) y)]
      simp only [hE, hW, hvW, hvE, if_true, Bool.false_eq_true, if_false]
      split_ifs <;> simp [map_neg]

    rw [ht, ht, map_sum, Finset.sum_congr rfl (fun c0 _ => step c0), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true, add_assoc, add_neg_cancel, add_zero]
  · intro z hz
    rw [ht]
    refine Submodule.sum_mem _ fun c0 _ => ?_
    have hQ1 : pderiv (E, c0) z ∈ MvPolynomial.restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ |
        (((M.wt LL J 0 m - (if c0 = 0 then 1 else 0) : ℤ)) : WithTop ℤ) ≤ Mt} := by
      refine pderiv_keep (E, c0) {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} _ ?_ z hz
      intro m hm h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [wt_sub_single LL J E c0 0 m h1]
      by_cases hc : c0 = 0 <;> simpa [hE, hvE, hc] using hm
    refine pderiv_keep (W, c0) _ {m : Fin N × Fin r →₀ ℕ | ((M.wt LL J 0 m : ℤ) : WithTop ℤ) ≤ Mt} ?_ _ hQ1
    · intro m hm h1
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [wt_sub_single LL J W c0 0 m h1]
      by_cases hc : c0 = 0 <;> simpa [hW, hvW, hc] using hm

end Comm

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfValuationBound

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM Formalism.GM.M

section Hyp

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

theorem hypU_proved (hB : G.BlockOK) : Formalism.InvariantFactorPaths.KP.LL.HypU p (r := r) G := by
  have hpol : ∀ (LL LL' : M.Letters N) (a : Fin N) (c : Fin r), LL'.deg a = LL.deg a - 1 →
      (∀ i, i ≠ a → LL'.deg i = LL.deg i) →
      ∀ y ∈ M.Pol p r LL, pderiv (a, c) y ∈ M.Pol p r LL' := by
    intro LL LL' a c hda hdo y hy
    unfold M.Pol at hy ⊢
    rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported] at hy

    rw [y.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [MvPolynomial.pderiv_monomial]
    by_cases h0 : m (a, c) = 0
    · rw [h0, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
      exact zero_mem _
    · have hmd : M.MultiDeg LL m := hy (Finset.mem_coe.mpr hm)
      rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported]
      refine (Finset.coe_subset.mpr MvPolynomial.support_monomial_subset).trans ?_
      rw [Finset.coe_singleton, Set.singleton_subset_iff]
      show M.MultiDeg LL' (m - Finsupp.single (a, c) 1)
      intro i
      by_cases hi : i = a
      · subst hi
        have key : ∀ c', ((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0) =
            m (i, c') := by
          intro c'
          rw [Finsupp.tsub_apply, Finsupp.single_apply]
          by_cases hc : c' = c
          · subst hc
            rw [if_pos rfl, if_pos rfl]
            omega
          · have hne : ¬ (i, c) = (i, c') := fun h => hc (congrArg Prod.snd h).symm
            rw [if_neg hne, if_neg hc]
            simp
        have hs : ∑ c', (((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0)) =
            ∑ c', m (i, c') := Finset.sum_congr rfl fun c' _ => key c'
        have h1 : ∑ c' : Fin r, (if c' = c then 1 else 0 : ℕ) = 1 := by simp
        rw [Finset.sum_add_distrib, h1] at hs
        rw [hda, ← hmd i]
        omega
      · rw [hdo i hi, ← hmd i]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finsupp.tsub_apply, Finsupp.single_apply,
          if_neg (fun h => hi (congrArg Prod.fst h).symm), Nat.sub_zero]
  intro j jp c y hy
  simp only [M.Y, Submodule.mem_inf, Submodule.mem_iInf] at hy ⊢
  refine ⟨hpol _ _ G.uPos c ?_ ?_ y hy.1, fun k => ?_⟩
  · simp only [M.BlockData.lettersAt, eq_self_iff_true, if_true]
    omega
  · intro i hi
    simp only [M.BlockData.lettersAt, if_neg hi]
  · rw [ycond_vec (p := p) (r := r) (G.lettersAt j (jp + 1)) (G.lettersAt j jp) rfl]
    exact pderiv_ycond (p := p) _ _ _ G.uPos (fun _ => hB.2.2.1) c y (hy.2 k)

theorem sum_update_ite {t : ℕ} (P : Fin t → Prop) [DecidablePred P] (j : Fin t → ℕ) (i : Fin t) :
    ∑ i', (if P i' then Function.update j i (j i + 1) i' else 0) =
      ∑ i', (if P i' then j i' else 0) + (if P i then 1 else 0) := by
  have h : ∀ i', (if P i' then Function.update j i (j i + 1) i' else 0) =
      (if P i' then j i' else 0) + (if i' = i then (if P i then 1 else 0) else 0) := by
    intro i'
    by_cases hi : i' = i
    · subst hi
      rw [Function.update_self]
      split_ifs <;> simp_all
    · rw [Function.update_of_ne hi, if_neg hi, add_zero]
  rw [Finset.sum_congr rfl fun i' _ => h i', Finset.sum_add_distrib]
  simp

theorem hypTie_proved (hB : G.BlockOK) : Formalism.InvariantFactorPaths.KP.LL.HypJoin p (r := r) G := by
  have hpol : ∀ (LL LL' : M.Letters N) (a : Fin N) (c : Fin r), LL'.deg a = LL.deg a - 1 →
      (∀ i, i ≠ a → LL'.deg i = LL.deg i) →
      ∀ y ∈ M.Pol p r LL, pderiv (a, c) y ∈ M.Pol p r LL' := by
    intro LL LL' a c hda hdo y hy
    unfold M.Pol at hy ⊢
    rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported] at hy

    rw [y.as_sum, map_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    rw [MvPolynomial.pderiv_monomial]
    by_cases h0 : m (a, c) = 0
    · rw [h0, Nat.cast_zero, mul_zero, MvPolynomial.monomial_zero]
      exact zero_mem _
    · have hmd : M.MultiDeg LL m := hy (Finset.mem_coe.mpr hm)
      rw [MvPolynomial.restrictSupport, AddMonoidAlgebra.supported, Submodule.mem_comap, Finsupp.mem_supported]
      refine (Finset.coe_subset.mpr MvPolynomial.support_monomial_subset).trans ?_
      rw [Finset.coe_singleton, Set.singleton_subset_iff]
      show M.MultiDeg LL' (m - Finsupp.single (a, c) 1)
      intro i
      by_cases hi : i = a
      · subst hi
        have key : ∀ c', ((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0) =
            m (i, c') := by
          intro c'
          rw [Finsupp.tsub_apply, Finsupp.single_apply]
          by_cases hc : c' = c
          · subst hc
            rw [if_pos rfl, if_pos rfl]
            omega
          · have hne : ¬ (i, c) = (i, c') := fun h => hc (congrArg Prod.snd h).symm
            rw [if_neg hne, if_neg hc]
            simp
        have hs : ∑ c', (((m - Finsupp.single (i, c) 1 : (Fin N × Fin r) →₀ ℕ) (i, c')) + (if c' = c then 1 else 0)) =
            ∑ c', m (i, c') := Finset.sum_congr rfl fun c' _ => key c'
        have h1 : ∑ c' : Fin r, (if c' = c then 1 else 0 : ℕ) = 1 := by simp
        rw [Finset.sum_add_distrib, h1] at hs
        rw [hda, ← hmd i]
        omega
      · rw [hdo i hi, ← hmd i]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [Finsupp.tsub_apply, Finsupp.single_apply,
          if_neg (fun h => hi (congrArg Prod.fst h).symm), Nat.sub_zero]
  intro j jp i y hy
  obtain ⟨hlt, hvW, hvE⟩ := hB.1.2.1 i
  set W := G.letterAt (G.T.pos i) with hWdef
  set E := G.letterAt (G.T.pos i + 1) with hEdef
  have hWv : (W : ℕ) = G.T.pos i := by
    simp only [hWdef, M.BlockData.letterAt]
    omega
  have hEv : (E : ℕ) = G.T.pos i + 1 := by
    simp only [hEdef, M.BlockData.letterAt]
    omega
  have hWE : W ≠ E := fun h => by
    have := congrArg Fin.val h
    omega
  have hvW' : G.LL.vec W = true := by
    rwa [show W = ⟨G.T.pos i, by omega⟩ from Fin.ext hWv]
  have hvE' : G.LL.vec E = false := by
    rwa [show E = ⟨G.T.pos i + 1, hlt⟩ from Fin.ext hEv]

  have hdeg : ∀ x : Fin N, (G.lettersAt (Function.update j i (j i + 1)) jp).deg x =
      (G.lettersAt j jp).deg x -
        (if ((x : ℕ) = G.T.pos i ∨ (x : ℕ) = G.T.pos i + 1) then 1 else 0) := by
    intro x
    simp only [M.BlockData.lettersAt]
    change G.LL.deg x - (∑ k : Fin G.T.t, if (x : ℕ) = G.T.pos k ∨
      (x : ℕ) = G.T.pos k + 1 then Function.update j i (j i + 1) k else 0) -
      (if x = G.uPos then jp else 0) =
      (G.LL.deg x - (∑ k : Fin G.T.t, if (x : ℕ) = G.T.pos k ∨
        (x : ℕ) = G.T.pos k + 1 then j k else 0) -
        (if x = G.uPos then jp else 0)) - _
    rw [sum_update_ite]
    omega
  have htie : ∀ x : MvPolynomial (Fin N × Fin r) ℚ_[p],
      Formalism.GM.tieF (fun c => (W, c)) (fun c => (E, c)) x =
      ∑ c, pderiv (W, c) (pderiv (E, c) x) := by
    intro x
    simp [Formalism.GM.tieF]
  simp only [M.Y, Submodule.mem_inf, Submodule.mem_iInf] at hy ⊢
  refine ⟨?_, fun k => ?_⟩
  · rw [htie]
    refine Submodule.sum_mem _ fun c _ => ?_
    let L1 : M.Letters N := ⟨G.LL.vec, fun x =>
      if x = E then (G.lettersAt j jp).deg x - 1 else (G.lettersAt j jp).deg x⟩
    have h1 := hpol (G.lettersAt j jp) L1 E c (by show (if E = E then _ else _) = _; rw [if_pos rfl])
      (fun x hx => by show (if x = E then _ else _) = _; rw [if_neg hx]) y hy.1
    refine hpol L1 _ W c ?_ ?_ _ h1
    · rw [hdeg W, if_pos (Or.inl hWv)]
      show _ = (if W = E then _ else _) - 1
      rw [if_neg hWE]
    · intro x hx
      rw [hdeg x]
      show _ = (if x = E then _ else _)
      by_cases hxE : x = E
      · have hxv : (x : ℕ) = G.T.pos i + 1 := by rw [hxE]; exact hEv
        rw [if_pos hxE, if_pos (Or.inr hxv)]
      · rw [if_neg hxE, if_neg, Nat.sub_zero]
        rintro (h | h)
        · exact hx (Fin.ext (h.trans hWv.symm))
        · exact hxE (Fin.ext (h.trans hEv.symm))
  · rw [ycond_vec (p := p) (r := r) (G.lettersAt (Function.update j i (j i + 1)) jp)
      (G.lettersAt j jp) rfl]
    have hx := hy.2 k
    by_cases hE : (E : ℕ) < G.T.J k
    · exact tieF_ycond (p := p) (G.lettersAt j jp) (G.T.J k) (G.T.thr k) W E (by omega) hE hvW' hvE' y hx
    · rw [htie]
      exact Submodule.sum_mem _ fun c _ => pderiv_ycond (p := p) _ _ _ W (fun _ => hvW') c _
        (pderiv_ycond (p := p) _ _ _ E (fun h => absurd h hE) c y hx)

end Hyp

section Inst

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem restLL_proved {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) : RestLL C0 CE1 CE2 X :=
  restLL_of C0 CE1 CE2 X hCYb hCE1 hCE2 hH fun aTop aPlus b =>
    ⟨hypTie_proved X.p _ (gB_blockOK C0 CE1 CE2 X aTop aPlus b),
      hypU_proved X.p _ (gB_blockOK C0 CE1 CE2 X aTop aPlus b)⟩

theorem block_valuation_Zp_of_valuation_bound {CYb Cde Ck CD Cb Cc : ℝ} (hCYb : 1 ≤ CYb) (hCE1 : 0 ≤ CE1) (hCE2 : 0 ≤ CE2)
    (hH : flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X) (hV : RestVal C0 CE1 CE2 X) : BlockBoundIntegers C0 CE1 CE2 X :=
  block_valuation_Zp_of_lattice_inclusion C0 CE1 CE2 X (Nat.one_le_iff_ne_zero.mpr X.hm)
    (restLL_proved C0 CE1 CE2 X hCYb hCE1 hCE2 hH) hV

end Inst

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
end
