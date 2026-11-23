module

public import ReciprocityTheory.SemistableReduction.LatSemiSt
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
public import ReciprocityTheory.SemistableReduction.LatAll
public import ReciprocityTheory.SemistableReduction.SemiContract
public import ReciprocityTheory.SemistableReduction.SemiDegSt
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.Tactic.Basify
public import ReciprocityTheory.SemistableReduction.SemiDegAA
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.SemistableReduction.SemiDegB
public import ReciprocityTheory.SemistableReduction.SemiDegC
public import ReciprocityTheory.SemistableReduction.SemiDegD
public import ReciprocityTheory.SemistableReduction.SemiDegZA

-- Source module: ReciprocityTheory.SemistableReduction.SemiDegAB

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

theorem wa_cases3 {n : ℕ} (i : Fin (n + 2)) :
    i = 0 ∨ i = Fin.last (n + 1) ∨ ∃ j : Fin n, i = (Fin.castSucc j).succ := by
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · exact Or.inl h
  · right
    induction j using Fin.lastCases with
    | last => left; simp
    | cast j => right; exact ⟨j, rfl⟩

def waExt {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) : Fin (n + 2) → α :=
  Fin.cons x (Fin.snoc f y : Fin (n + 1) → α)

@[simp] theorem waExt_zero {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) :
    waExt x y f 0 = x := by
  simp [waExt]

@[simp] theorem waExt_last {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) :
    waExt x y f (Fin.last (n + 1)) = y := by
  rw [waExt, ← Fin.succ_last, Fin.cons_succ, Fin.snoc_last]

@[simp] theorem waExt_mid {α : Type} {n : ℕ} (x y : α) (f : Fin n → α) (j : Fin n) :
    waExt x y f (Fin.castSucc j).succ = f j := by
  rw [waExt, Fin.cons_succ, Fin.snoc_castSucc]

theorem wa_witt_apply {K : Type} [Field K] (r m : ℕ) (g : Fin r → K) (i j : Fin r) :
    wittMat r m g i j = if (i : ℕ) + j + 1 = r ∧ ((i : ℕ) < m ∨ (j : ℕ) < m) then 1
      else if (i : ℕ) = j ∧ m ≤ (i : ℕ) ∧ (i : ℕ) + m < r then g i else 0 := by
  unfold wittMat
  simp only [Matrix.of_apply, Fin.val_inj]

theorem wa_main {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r) :
    ∀ (n : ℕ) (W : Submodule K (Fin r → K)), finrank K W = n →
      (∀ x ∈ W, (∀ y ∈ W, S.h x y = 0) → x = 0) →
      ∃ (m : ℕ) (b : Fin n → Fin r → K) (g : Fin n → K), (∀ i, b i ∈ W) ∧ 2 * m ≤ n ∧
        (∀ i j, S.h (b i) (b j) = wittMat n m g i j) ∧
        ∀ t : Fin n → K, (∀ i : Fin n, (i : ℕ) < m ∨ n ≤ (i : ℕ) + m → t i = 0) →
          ∑ i, S.c (t i) * g i * t i = 0 → t = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hW hnd
  by_cases hiso : ∃ x ∈ W, x ≠ 0 ∧ S.h x x = 0
  · obtain ⟨x, hxW, hx0, hxx⟩ := hiso
    obtain ⟨y, hyW, hxy, hyy⟩ := wa_hyp S W hnd x hxW hx0 hxx
    have hyx : S.h y x = 1 := by rw [wa_symm, hxy, map_one]
    have hf1 := wa_finrank_inf_ker W (waR S x) y hyW
      (by rw [waR_apply, hxy]; exact one_ne_zero)
    have hf2 := wa_finrank_inf_ker (W ⊓ LinearMap.ker (waR S x)) (waR S y) x
      (Submodule.mem_inf.mpr ⟨hxW, by rw [LinearMap.mem_ker, waR_apply, hxx]⟩)
      (by rw [waR_apply, hyx]; exact one_ne_zero)
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 :=
      ⟨finrank K ↥(W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)), by omega⟩
    obtain ⟨m', b', g', hb'W, hm', hgram', hani'⟩ := ih n' (by omega)
      (W ⊓ LinearMap.ker (waR S x) ⊓ LinearMap.ker (waR S y)) (by omega)
      (wa_perp_nondeg S W hnd x y hxW hyW hxx hxy hyy)
    have hmem : ∀ j, b' j ∈ W ∧ S.h x (b' j) = 0 ∧ S.h y (b' j) = 0 := fun j => by
      have h := hb'W j
      rw [Submodule.mem_inf, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, waR_apply,
        waR_apply] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    have hbx : ∀ j, S.h (b' j) x = 0 := fun j => by rw [wa_symm, (hmem j).2.1, map_zero]
    have hby : ∀ j, S.h (b' j) y = 0 := fun j => by rw [wa_symm, (hmem j).2.2, map_zero]
    refine ⟨m' + 1, waExt x y b', waExt 0 0 g', fun i => ?_, by omega, fun i j => ?_,
      fun t ht hsum => ?_⟩
    · rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · simpa using hxW
      · simpa using hyW
      · simpa using (hmem j).1
    · rw [wa_witt_apply]
      rcases wa_cases3 i with rfl | rfl | ⟨i, rfl⟩ <;>
        rcases wa_cases3 j with rfl | rfl | ⟨j, rfl⟩ <;>
        simp only [waExt_zero, waExt_last, waExt_mid, Fin.val_zero, Fin.val_last, Fin.val_succ,
          Fin.val_castSucc] <;>
        try simp only [true_and]
      · rw [hxx, if_neg (by omega), if_neg (by omega)]
      · rw [hxy, if_pos (by omega)]
      · have := j.2
        rw [(hmem j).2.1, if_neg (by omega), if_neg (by omega)]
      · rw [hyx, if_pos (by omega)]
      · rw [hyy, if_neg (by omega), if_neg (by omega)]
      · have := j.2
        rw [(hmem j).2.2, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hbx, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        rw [hby, if_neg (by omega), if_neg (by omega)]
      · have := i.2
        have := j.2
        rw [hgram', wa_witt_apply]
        split_ifs <;> first | rfl | (exfalso; omega)
    · have ht0 : t 0 = 0 := ht 0 (Or.inl (by simp))
      have htl : t (Fin.last (n' + 1)) = 0 := ht _ (Or.inr (by simp only [Fin.val_last]; omega))
      have ht' : (fun j : Fin n' => t (Fin.castSucc j).succ) = 0 := by
        refine hani' _ (fun j hj => ht _ ?_) ?_
        · simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        · rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc] at hsum
          simpa [ht0, htl, Fin.succ_last] using hsum
      funext i
      rcases wa_cases3 i with rfl | rfl | ⟨j, rfl⟩
      · exact ht0
      · exact htl
      · exact congrFun ht' j
  · have han : ∀ x ∈ W, S.h x x = 0 → x = 0 := fun x hx hxx => by
      by_contra h0
      exact hiso ⟨x, hx, h0, hxx⟩
    obtain ⟨b, hbW, hb0, hbo⟩ := wa_diag S n W hW han
    have hg : ∀ k, S.h (b k) (b k) ≠ 0 := fun k h => hb0 k (han _ (hbW k) h)
    refine ⟨0, b, fun k => S.h (b k) (b k), hbW, by omega, fun i j => ?_, fun t _ hsum => ?_⟩
    · rw [wa_witt_apply]
      have := i.2
      by_cases hij : i = j
      · subst hij
        rw [if_neg (by omega), if_pos ⟨rfl, by omega, by omega⟩]
      · rw [hbo i j hij, if_neg (by omega), if_neg (fun h => hij (Fin.ext h.1))]
    · have hz : ∀ k, S.h (b k) (∑ i, t i • b i) = t k * S.h (b k) (b k) := fun k => by
        rw [wa_sum_right, Finset.sum_eq_single k
          (fun i _ hik => by rw [hbo k i (Ne.symm hik), mul_zero]) (by simp)]
      have hzz : S.h (∑ i, t i • b i) (∑ i, t i • b i) = 0 := by
        rw [wa_sum_left]
        simp only [hz]
        refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
        beta_reduce
        ring
      have hz0 := han _ (W.sum_mem fun i _ => W.smul_mem _ (hbW i)) hzz
      funext k
      have h := hz k
      rw [hz0, wa_zero_right] at h
      exact (mul_eq_zero.mp h.symm).resolve_right (hg k)

end ReciprocityTheory.MultiplicativeHeights
end
end
end

-- Source module: ReciprocityTheory.SemistableReduction.SemiDegA

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Module

theorem wa_witt_ker {K : Type} [Field K] (r m : ℕ) (g : Fin r → K)
    (hg : ∀ k : Fin r, m ≤ (k : ℕ) → (k : ℕ) + m < r → g k ≠ 0) (v : Fin r → K)
    (hv : ∀ p : Fin r, ∑ i, v i * wittMat r m g p i = 0) : v = 0 := by
  funext j
  have hj := j.isLt
  by_cases hmid : m ≤ (j : ℕ) ∧ (j : ℕ) + m < r
  · have h := hv j
    rw [Finset.sum_eq_single j] at h
    · simp only [wittMat, Matrix.of_apply] at h
      rw [if_neg (by omega), if_pos ⟨trivial, hmid.1, hmid.2⟩] at h
      exact (mul_eq_zero.1 h).resolve_right (hg j hmid.1 hmid.2)
    · intro i _ hij
      have hi := i.isLt
      simp only [wittMat, Matrix.of_apply]
      rw [if_neg, if_neg, mul_zero]
      · rintro ⟨h1, -⟩
        exact hij h1.symm
      · rintro ⟨h1, h2⟩
        rcases h2 with h2 | h2 <;> omega
    · intro h
      exact absurd (Finset.mem_univ j) h
  · set p : Fin r := ⟨r - 1 - j, by omega⟩ with hp
    have hpv : (p : ℕ) = r - 1 - j := rfl
    have h := hv p
    rw [Finset.sum_eq_single j] at h
    · simp only [wittMat, Matrix.of_apply] at h
      have hc : (p : ℕ) + j + 1 = r ∧ ((p : ℕ) < m ∨ (j : ℕ) < m) := by
        rw [hpv]
        omega
      rw [if_pos hc, mul_one] at h
      exact h
    · intro i _ hij
      have hi := i.isLt
      simp only [wittMat, Matrix.of_apply]
      rw [if_neg, if_neg, mul_zero]
      · rintro ⟨-, h2, h3⟩
        rw [hpv] at h2 h3
        omega
      · rintro ⟨h1, -⟩
        apply hij
        ext
        rw [hpv] at h1
        omega
    · intro h
      exact absurd (Finset.mem_univ j) h

theorem wittBasis_holds : WittBasisStatement := by
  intro K _ _ r S hdet
  have hnd : ∀ x ∈ (⊤ : Submodule K (Fin r → K)),
      (∀ y ∈ (⊤ : Submodule K (Fin r → K)), S.h x y = 0) → x = 0 := by
    intro x _ hx
    have hrow : Matrix.vecMul (fun a => S.c (x a)) S.G = 0 := by
      funext b'
      have h1 := hx (Pi.single b' 1) Submodule.mem_top
      simpa [HermForm.h, Pi.single_apply, Matrix.vecMul, dotProduct] using h1
    have h2 : (fun a => S.c (x a)) = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hrow
    funext a
    have h3 := congrFun h2 a
    simp only [Pi.zero_apply, map_eq_zero] at h3
    exact h3
  obtain ⟨m, bb, g, -, hm, hW, hg⟩ := wa_main S r ⊤ (by rw [finrank_top, Module.finrank_fin_fun]) hnd
  have hgmid : ∀ k : Fin r, m ≤ (k : ℕ) → (k : ℕ) + m < r → g k ≠ 0 := by
    intro k hk1 hk2 hgk
    have ht := hg (Pi.single k 1) (fun i hi => by
      rw [Pi.single_apply, if_neg]
      rintro rfl
      omega) (by
      rw [Finset.sum_eq_single k]
      · simp [hgk]
      · intro i _ hik
        simp [Pi.single_eq_of_ne hik]
      · intro h
        exact absurd (Finset.mem_univ k) h)
    have := congrFun ht k
    simp at this
  have hlin : ∀ (x v : Fin r → K), S.h x (fun a => ∑ i, bb i a * v i) = ∑ i, v i * S.h x (bb i) := by
    intro x v
    simp only [HermForm.h, Finset.mul_sum]
    calc ∑ a, ∑ b', ∑ i, S.c (x a) * S.G a b' * (bb i b' * v i)
        = ∑ a, ∑ i, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', S.c (x a) * S.G a b' * (bb i b' * v i) := Finset.sum_comm
      _ = ∑ i, ∑ a, ∑ b', v i * (S.c (x a) * S.G a b' * bb i b') :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
            Finset.sum_congr rfl fun b' _ => by ring
  refine ⟨Matrix.of fun a i => bb i a, m, g, ?_, hm, ?_, hg⟩
  · intro hd
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hd
    apply hv0
    have hPv : Matrix.mulVec (Matrix.of fun a i => bb i a) v = fun a => ∑ i, bb i a * v i := by
      funext a
      simp [Matrix.mulVec, dotProduct]
    refine wa_witt_ker r m g hgmid v fun p => ?_
    have h1 : S.h (bb p) (fun a => ∑ i, bb i a * v i) = 0 := by
      rw [← hPv, hv]
      simp [HermForm.h]
    rw [hlin] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => by rw [hW p i]
  · ext i j
    rw [← hW i j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply, HermForm.h,
      Finset.sum_mul]
    exact Finset.sum_comm

end ReciprocityTheory.MultiplicativeHeights
end
end
end

-- Source module: ReciprocityTheory.SemistableReduction.SemiDeg

section

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

theorem semiDeg_holds (hD : DegAddStatement) : SemiPointStatement :=
  SemiPt.semiPoint_of wittBasis_holds latDegBasis_holds integralIndex_holds selfDualIndex_holds
    (gradedExt_holds latDegBasis_holds hD) absDet_holds

end ReciprocityTheory.MultiplicativeHeights
end
end

-- Source module: ReciprocityTheory.SemistableReduction.SemiAll

section

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights.Closed

open ReciprocityTheory.MultiplicativeHeights

theorem semiPoint : SemiPointStatement := semiDeg_holds degAdd

theorem semistable : SemistableStatement := semiContract_holds semiPoint degAdd

end ReciprocityTheory.MultiplicativeHeights.Closed
end
end
