module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.MvPowerSeries.Basic
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
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Ideal.Operations

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetUpdateRowAlternatingMulVecMem

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

theorem det_updateRow_single_mul_sub_mem {T : Type} [CommRing T] {g : ℕ} (x : Fin g → T)
    (I : Ideal T) (m : Matrix (Fin g) (Fin g) T) (p : Fin g)
    (hm : ∀ q, q ≠ p → m.mulVec x q ∈ I) (i j : Fin g) :
    x j * (m.updateRow p (Pi.single i 1)).det - x i * (m.updateRow p (Pi.single j 1)).det ∈ I := by
  set m' := m.updateRow p (Pi.single i 1) with hm'
  have h1 : m'.adjugate.mulVec (m'.mulVec x) = m'.det • x := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : ∑ q, m'.adjugate j q * m'.mulVec x q = m'.det * x j := by
    have := congrFun h1 j
    simpa [Matrix.mulVec, dotProduct] using this
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ p)] at h2
  have h3 : m'.adjugate j p = (m.updateRow p (Pi.single j 1)).det := by
    rw [Matrix.adjugate_apply, hm', Matrix.updateRow_idem]
  have h4 : m'.mulVec x p = x i := by
    simp [hm', Matrix.mulVec]
  rw [h3, h4] at h2
  have h5 : ∑ q ∈ Finset.univ.erase p, m'.adjugate j q * m'.mulVec x q ∈ I := by
    refine I.sum_mem fun q hq => I.mul_mem_left _ ?_
    have hq' : q ≠ p := Finset.ne_of_mem_erase hq
    have : m'.mulVec x q = m.mulVec x q := by
      simp [hm', Matrix.mulVec, Matrix.updateRow_ne hq']
    rw [this]
    exact hm q hq'
  convert h5 using 1
  linear_combination -h2

theorem det_updateRow_alternating_mulVec_mem {T : Type} [CommRing T] {g : ℕ} (x : Fin g → T)
    (I : Ideal T) (m : Matrix (Fin g) (Fin g) T) (p : Fin g)
    (hm : ∀ q, q ≠ p → m.mulVec x q ∈ I) (s : Matrix (Fin g) (Fin g) T)
    (hs : s.transpose = -s) (hd : ∀ i, s i i = 0) :
    (m.updateRow p (s.mulVec x)).det ∈ I := by
  have h1 : (m.updateRow p (s.mulVec x)).det
      = ∑ ij : Fin g × Fin g,
          s ij.1 ij.2 * (x ij.2 * (m.updateRow p (Pi.single ij.1 1)).det) := by
    have e : ∀ v : Fin g → T, (m.updateRow p v).det
        = ∑ i, v i * (m.updateRow p (Pi.single i 1)).det := by
      intro v
      have := Matrix.cramer_transpose_apply m v p
      rw [← this, Matrix.cramer_eq_adjugate_mulVec]
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Matrix.adjugate_transpose, Matrix.transpose_apply, Matrix.adjugate_apply, mul_comm]
    rw [e, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

  rw [h1, ← Ideal.Quotient.eq_zero_iff_mem, map_sum]
  refine Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _) Prod.swap_swap
  · rintro ⟨i, j⟩
    rw [← map_add (f := _), Ideal.Quotient.eq_zero_iff_mem]
    have hji : s j i = - s i j := by
      have := congrFun (congrFun hs i) j
      simpa using this
    have := I.mul_mem_left (s i j) (det_updateRow_single_mul_sub_mem x I m p hm i j)
    convert this using 1
    simp only [Prod.fst_swap, Prod.snd_swap, hji]
    ring
  · rintro ⟨i, j⟩ h e
    apply h
    have : j = i := congrArg Prod.fst e
    subst this
    simp [hd]

theorem det_sub_det_mem_span_of_mulVec_eq :
    ∀ (T : Type) [CommRing T] (g : ℕ) (x : Fin g → T), (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) → ∀ c c' : Matrix (Fin g) (Fin g) T, c.mulVec x = c'.mulVec x → c.det - c'.det ∈ Ideal.span (Set.range (c.mulVec x)) := by
  intro T _ g x hx c c' hc
  set I := Ideal.span (Set.range (c.mulVec x)) with hI
  let M : Finset (Fin g) → Matrix (Fin g) (Fin g) T :=
    fun S => Matrix.of fun i => if i ∈ S then c' i else c i
  have hM : ∀ S q, (M S).mulVec x q = c.mulVec x q := by
    intro S q
    by_cases h : q ∈ S
    · rw [hc]; simp [M, Matrix.mulVec, h]
    · simp [M, Matrix.mulVec, h]
  have key : ∀ S : Finset (Fin g), c.det - (M S).det ∈ I := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have : M ∅ = c := by ext i j; simp [M]
      simp [this]
    | insert p S hp ih =>
      obtain ⟨s, hs, hd, hr⟩ := hx (c p - c' p) (by
        have := congrFun hc p
        simp only [Matrix.mulVec, dotProduct] at this
        simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr this)
      have h1 := det_updateRow_alternating_mulVec_mem x I (M S) p
        (fun q _ => by rw [hM]; exact Ideal.subset_span ⟨q, rfl⟩) s hs hd
      rw [← hr] at h1
      have e1 : (M S).updateRow p (c' p) = M (insert p S) := by
        ext i j
        by_cases h : i = p
        · subst h; simp [M]
        · simp [M, Matrix.updateRow_ne h, h]
      have e2 : (M S).updateRow p (c p) = M S := by
        ext i j
        by_cases h : i = p
        · subst h; simp [M, hp]
        · simp [Matrix.updateRow_ne h]
      have e3 := Matrix.det_updateRow_add (M S) p (c p - c' p) (c' p)
      rw [sub_add_cancel, e1, e2] at e3
      have := I.add_mem ih h1
      convert this using 1
      linear_combination e3
  have := key Finset.univ
  have e : M Finset.univ = c' := by ext i j; simp [M]
  rwa [e] at this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.MvPowerSeriesVariablesSyzygySocle

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

open MvPowerSeries Finsupp in
theorem coeff_mul_X_ite {k : Type} [CommRing k] {g : ℕ} (f : MvPowerSeries (Fin g) k)
    (j : Fin g) (m : Fin g →₀ ℕ) :
    coeff m (f * X j) = if m j ≠ 0 then coeff (m - single j 1) f else 0 := by
  classical
  rw [X_def, coeff_mul_monomial, mul_one]
  congr 1
  simp [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

open MvPowerSeries Finsupp in
theorem mvPowerSeries_X_syzygy {k : Type} [CommRing k] {g : ℕ}
    (r : Fin g → MvPowerSeries (Fin g) k) (hr : ∑ i, r i * X i = 0) :
    ∃ s : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k), s.transpose = -s ∧ (∀ i, s i i = 0) ∧
      r = s.mulVec (fun i => X i) := by
  classical
  let t : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k) := fun i j n =>
    if j < i ∧ ∀ l < j, n l = 0 then coeff (n + single j 1) (r i) else 0
  have ht : ∀ i j n, coeff n (t i j) =
      if j < i ∧ ∀ l < j, n l = 0 then coeff (n + single j 1) (r i) else 0 := fun _ _ _ => rfl
  refine ⟨t - t.transpose, by simp [Matrix.transpose_sub], fun i => by simp, ?_⟩
  funext i
  ext m
  have h1 : ∀ j, coeff m (t i j * X j) =
      if m j ≠ 0 ∧ j < i ∧ ∀ l < j, m l = 0 then coeff m (r i) else 0 := by
    intro j
    rw [coeff_mul_X_ite, ht]
    by_cases hj : m j = 0
    · simp [hj]
    · have e : m - single j 1 + single j 1 = m :=
        tsub_add_cancel_of_le (by simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hj)
      have e2 : (∀ l < j, (m - single j 1 : Fin g →₀ ℕ) l = 0) ↔ ∀ l < j, m l = 0 := by
        refine forall_congr' fun l => forall_congr' fun hl => ?_
        simp [Finsupp.single_apply, hl.ne']
      simp only [e, e2, hj, ne_eq, not_false_eq_true, if_true, true_and]
  have h2 : ∀ j, coeff m (t j i * X j) =
      if (∀ l < i, m l = 0) ∧ j ≠ i then coeff (m + single i 1) (r j * X j) else 0 := by
    intro j
    rw [coeff_mul_X_ite, ht, coeff_mul_X_ite]
    by_cases hji : j = i
    · simp [hji]
    have e0 : (m + single i 1 : Fin g →₀ ℕ) j = m j := by
      simp [Finsupp.single_apply, Ne.symm hji]
    rw [e0]
    by_cases hj : m j = 0
    · simp [hj]
    have e : m - single j 1 + single i 1 = m + single i 1 - single j 1 :=
      tsub_add_eq_add_tsub (by simpa [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero] using hj)
    rw [e]
    rcases lt_or_gt_of_ne hji with h | h
    · have : ¬ ∀ l < i, m l = 0 := fun H => hj (H j h)
      simp [this, h.not_gt]
    · have e2 : (∀ l < i, (m - single j 1 : Fin g →₀ ℕ) l = 0) ↔ ∀ l < i, m l = 0 := by
        refine forall_congr' fun l => forall_congr' fun hl => ?_
        simp [Finsupp.single_apply, (hl.trans h).ne']
      simp only [e2, hj, h, hji, ne_eq, not_false_eq_true, if_true, true_and, and_true]

  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.transpose_apply, sub_mul,
  map_sum, map_sub, h1, h2, Finset.sum_sub_distrib]
  by_cases hi : ∀ l < i, m l = 0
  · rw [Finset.sum_eq_zero (fun j _ => if_neg (fun H => H.1 (hi j H.2.1)))]
    have h3 := congrArg (coeff (m + single i 1)) hr

    rw [map_sum, map_zero, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), coeff_mul_X_ite] at h3
    simp only [iff_true_intro hi, true_and]
    rw [← Finset.sum_filter, Finset.filter_ne']
    simp only [Finsupp.add_apply, single_eq_same, add_tsub_cancel_right] at h3
    rw [if_pos (by omega)] at h3
    linear_combination h3
  · simp only [hi, false_and, if_false, Finset.sum_const_zero, sub_zero]
    push_neg at hi
    obtain ⟨l, hl, hml⟩ := hi
    obtain ⟨j, hj, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Fin g)) {j | m j ≠ 0} ⟨l, hml⟩
    have hj0 : ∀ a < j, m a = 0 := fun a ha => by
      by_contra h; exact hmin a h ha
    rw [Finset.sum_eq_single j]
    · rw [if_pos ⟨hj, lt_of_le_of_lt (not_lt.1 (hmin l hml)) hl, hj0⟩]
    · intro b _ hb
      refine if_neg fun H => ?_
      rcases lt_or_gt_of_ne hb with h | h
      · exact H.1 (hj0 b h)
      · exact hj (H.2.2 j h)
    · simp

open MvPowerSeries Finsupp in
theorem mvPowerSeries_prod_X_pow_notMem {k : Type} [CommRing k] [Nontrivial k] {g : ℕ} (N : ℕ) :
    ∏ i, (X i : MvPowerSeries (Fin g) k) ^ N ∉
      Ideal.span (Set.range fun i => (X i : MvPowerSeries (Fin g) k) ^ (N + 1)) := by
  classical
  intro h
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.1 h
  have hp : ∀ s : Finset (Fin g), ∏ i ∈ s, (X i : MvPowerSeries (Fin g) k) ^ N =
      monomial (∑ i ∈ s, single i N) 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  have := congrArg (coeff (∑ i : Fin g, single i N)) hc

  rw [hp, coeff_monomial_same, map_sum, Finset.sum_eq_zero] at this
  · exact zero_ne_one this
  · intro i _
    refine X_pow_dvd_iff.1 (dvd_mul_left _ _) _ ?_
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem mvPowerSeries_variables_syzygy_socle :
    ∀ (k : Type) [Field k] (g : ℕ) (x : Fin g → MvPowerSeries (Fin g) k), (∀ i, x i = MvPowerSeries.X i) → (∀ r : Fin g → _, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) _, s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x) ∧ ∀ N : ℕ, ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)) := by
  intro k _ g x hx
  obtain rfl : x = fun i => MvPowerSeries.X i := funext hx
  exact ⟨fun r hr => mvPowerSeries_X_syzygy r hr, fun N => mvPowerSeries_prod_X_pow_notMem N⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetNotMemSpanMulVecOfSocle

section

@[expose] public section

open scoped TensorProduct

namespace GlobalTheory

theorem det_notMem_span_mulVec_of_socle {T : Type} [CommRing T] {g N : ℕ} (x : Fin g → T)
    (hsyz : ∀ r : Fin g → T, ∑ i, r i * x i = 0 → ∃ s : Matrix (Fin g) (Fin g) T,
      s.transpose = -s ∧ (∀ i, s i i = 0) ∧ r = s.mulVec x)
    (hsoc : ∏ i, x i ^ N ∉ Ideal.span (Set.range fun i => x i ^ (N + 1)))
    (a : Matrix (Fin g) (Fin g) T)
    (h : ∀ i, x i ^ (N + 1) ∈ Ideal.span (Set.range (a.mulVec x))) :
    a.det ∉ Ideal.span (Set.range (a.mulVec x)) := by
  intro hdet
  have h' : ∀ i, ∃ c : Fin g → T, ∑ j, c j * a.mulVec x j = x i ^ (N + 1) := fun i =>
    Ideal.mem_span_range_iff_exists_fun.mp (h i)
  choose b hb using h'
  let B : Matrix (Fin g) (Fin g) T := Matrix.of b
  have hB : B.mulVec (a.mulVec x) = fun i => x i ^ (N + 1) := by
    funext i
    exact hb i
  set J : Ideal T := Ideal.span (Set.range fun i => x i ^ (N + 1)) with hJ
  have hf : ∀ i, B.det * a.mulVec x i ∈ J := by
    intro i
    have e : B.adjugate.mulVec (B.mulVec (a.mulVec x)) = B.det • a.mulVec x := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have e' := congrFun e i
    rw [hB, Pi.smul_apply, smul_eq_mul] at e'
    rw [← e']
    exact Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun j => B.adjugate i j, rfl⟩
  have hBa : (B * a).det ∈ J := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hdet
    rw [Matrix.det_mul, ← hc, Finset.mul_sum]
    refine Ideal.sum_mem _ fun j _ => ?_
    rw [mul_left_comm]
    exact Ideal.mul_mem_left _ _ (hf j)
  have hBx : (B * a).mulVec x = fun i => x i ^ (N + 1) := by
    rw [← Matrix.mulVec_mulVec, hB]
  have hD : (Matrix.diagonal fun i => x i ^ N).mulVec x = fun i => x i ^ (N + 1) := by
    funext i
    rw [Matrix.mulVec_diagonal, pow_succ]
  have key := GlobalTheory.det_sub_det_mem_span_of_mulVec_eq T g x hsyz (B * a)
    (Matrix.diagonal fun i => x i ^ N) (hBx.trans hD.symm)
  rw [hBx, Matrix.det_diagonal] at key
  have := J.sub_mem hBa key
  rw [sub_sub_cancel] at this
  exact hsoc this

theorem det_notMem_span_mulVec_X : ∀ (k : Type) [Field k] (g N : ℕ) (a : Matrix (Fin g) (Fin g) (MvPowerSeries (Fin g) k)), (∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin g) k) ^ N ∈ Ideal.span (Set.range (a.mulVec MvPowerSeries.X))) → a.det ∉ Ideal.span (Set.range (a.mulVec MvPowerSeries.X)) := by
  intro k _ g N a h
  obtain ⟨hsyz, hsoc⟩ := GlobalTheory.mvPowerSeries_variables_syzygy_socle k g MvPowerSeries.X (fun _ => rfl)
  refine det_notMem_span_mulVec_of_socle MvPowerSeries.X hsyz (hsoc N) a fun i => ?_
  rw [pow_succ]
  exact Ideal.mul_mem_right _ _ (h i)

end GlobalTheory
end
end
