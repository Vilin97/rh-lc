module

public import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLie
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDelta
public import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFB
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
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallCv
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLie
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyRes2
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePSplitDef
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyGlue

section

@[expose] public section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie

section Glue

variable {C : Type} [Field C] {V : VF C}

theorem tends_pow_zero {a : C} (ha : V.MM a) : Tends V (fun n => a ^ V.l ^ n) 0 := by
  unfold Tends VF.MM at *
  intro w
  by_cases ha0 : a = 0
  · refine ⟨0, fun n _ => ?_⟩
    unfold VF.Ge
    show (w : WithTop ℝ) ≤ V.v (0 - a ^ V.l ^ n)
    rw [ha0, zero_pow (pow_pos V.l_prime.pos n).ne', sub_zero, AddValuation.map_zero]
    exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff V.v).mpr ha0)
    have hr0 : 0 < r := by
      rw [← hr] at ha
      exact WithTop.coe_pos.mp ha
    refine ⟨⌈w / r⌉₊, fun n hn => ?_⟩
    unfold VF.Ge
    show (w : WithTop ℝ) ≤ V.v (0 - a ^ V.l ^ n)
    rw [zero_sub, AddValuation.map_neg, AddValuation.map_pow, ← hr, ← WithTop.coe_nsmul,
      WithTop.coe_le_coe, nsmul_eq_mul]
    have h1 : (n : ℝ) ≤ ((V.l ^ n : ℕ) : ℝ) := by
      first
        | exact_mod_cast (Nat.lt_pow_self V.l_prime.one_lt n).le
        | exact_mod_cast (Nat.lt_pow_self V.l_prime.one_lt).le
    have h2 : w / r ≤ n := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    exact (div_mul_cancel₀ w hr0.ne').ge.trans (mul_le_mul_of_nonneg_right (h2.trans h1) hr0.le)

variable [CharZero C] {O : Type} [CommRing O] {n d : ℕ}

theorem chi_kill (K : KeyData C V O n d) (w : Fin n → C) (hw : w ≠ 0) (hP : Matrix.mulVec K.P w = w)
    (χ : O →+* C) (hχ : ∀ x, Matrix.mulVec (K.ρ x) w = χ x • w) :
    (∀ y, V.Ge 0 (χ y)) ∧ ∀ z, (∀ a, V.MM (K.em a z)) → V.MM (χ z) := by
  have hint : ∀ y, V.Ge 0 (χ y) := fun y => eig_int (K.ρ y) (K.ρ_int y) w hw (χ y) (hχ y)
  refine ⟨hint, ?_⟩
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)

  have hT : Tends V (fun m => χ K.ε ^ V.l ^ m * w i) (w i) := by
    have h1 : Tends V (fun m => Matrix.mulVec (K.ρ (K.ε ^ V.l ^ m)) w i) (Matrix.mulVec K.P w i) := by
      simp only [Matrix.mulVec, dotProduct]
      refine Tends.sum _ fun j _ => Tends.mul ?_ (tends_const _)
      exact RowTiePProj.tends_of_nat fun N => K.P_lim N i j
    have e : (fun m => Matrix.mulVec (K.ρ (K.ε ^ V.l ^ m)) w i) = fun m => χ K.ε ^ V.l ^ m * w i := by
      funext m
      rw [hχ, map_pow]; rfl
    rw [e, hP] at h1
    exact h1
  have hunit : ¬ V.MM (χ K.ε) := by
    intro hm
    have h0 := (tends_pow_zero hm).mul (tends_const (V := V) (w i))
    rw [zero_mul] at h0
    exact hi (hT.unique h0)
  intro z hz
  obtain ⟨y, hy⟩ := K.ε_ann z hz
  have h1 := congrArg (fun t => V.v (χ t)) hy
  simp only [map_mul, map_natCast, AddValuation.map_mul, V.v_l] at h1
  unfold VF.MM at hunit ⊢
  push_neg at hunit
  have he0 : V.v (χ K.ε) = 0 := le_antisymm hunit (hint K.ε)
  rw [he0, zero_add] at h1
  rw [h1]
  have := hint y
  unfold VF.Ge at this
  calc (0 : WithTop ℝ) < 1 := by exact_mod_cast one_pos
    _ = 1 + 0 := (add_zero _).symm
    _ ≤ 1 + V.v (χ y) := add_le_add le_rfl (by exact_mod_cast this)

end Glue

section Top

theorem keyLA_of (hE : KeyEigSt) (hR : KeyResSt) (hD : KeyDeltaSt) (C : Type) [Field C] [CharZero C] (V : VF C)
    (hac : IsAlgClosed C)
    (hcpl : ∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n))
    (O : Type) [CommRing O] (n d : ℕ) [NeZero d] (K : KeyData C V O n d) (x : O) :
    Polynomial.aeval (K.ρ x) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (K.em c x))) * K.P = 0 := by
  have hv : ∀ v : Fin n → C,
      Matrix.mulVec (Polynomial.aeval (K.ρ x) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (K.em c x))) * K.P) v = 0 := by
    intro v
    obtain ⟨m, w, χ, hPv, hw⟩ := hE C V hac hcpl O n d K v
    rw [← Matrix.mulVec_mulVec, hPv, Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases h0 : w j = 0
    · rw [h0, Matrix.mulVec_zero]
    obtain ⟨hPw, hχ⟩ := hw j
    obtain ⟨hint, hkill⟩ := chi_kill K (w j) h0 hPw (χ j) hχ
    obtain ⟨c, hc⟩ := hR C V O n d K (χ j) hint hkill
    have heq := hD C V O n d K (χ j) c hint hc
    rw [aeval_mulVec _ _ _ (hχ x), Polynomial.eval_prod]
    have : ∏ c' : ZMod d, Polynomial.eval (χ j x) (Polynomial.X - Polynomial.C (K.em c' x)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ c) (by rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
        heq, sub_self])
    rw [this, zero_smul]
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

end Top

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePSplitLA

section

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePSplit

open Polynomial Matrix

section Sep

variable {K : Type} [Field K] [CharZero K]

theorem aff_sub (α β : K) (h : α ≠ 0 ∨ β ≠ 0) : {t : ℕ | α + (t : K) * β = 0}.Subsingleton := by
  intro t1 h1 t2 h2
  simp only [Set.mem_setOf_eq] at h1 h2
  by_cases hb : β = 0
  · rw [hb, mul_zero, add_zero] at h1
    exact absurd h1 (h.resolve_right (not_not.mpr hb))
  · have h3 : ((t1 : K) - t2) * β = 0 := by linear_combination h1 - h2
    have h4 : (t1 : K) = t2 := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hb)
    exact_mod_cast h4

theorem exists_sep {O : Type} [CommRing O] {ι : Type} [Fintype ι] (em : ι → (O →+* K))
    (hem : Function.Injective em) : ∃ x0 : O, ∀ c c', c ≠ c' → em c x0 ≠ em c' x0 := by
  classical
  have key : ∀ F : Finset (ι × ι), (∀ q ∈ F, q.1 ≠ q.2) → ∃ x0 : O, ∀ q ∈ F, em q.1 x0 ≠ em q.2 x0 := by
    intro F
    induction F using Finset.induction_on with
    | empty => intro _; exact ⟨0, by simp⟩
    | insert p F _ ih =>
      intro hF
      obtain ⟨x, hx⟩ := ih fun q hq => hF q (Finset.mem_insert_of_mem hq)
      obtain ⟨z, hz⟩ : ∃ z, em p.1 z ≠ em p.2 z := by
        by_contra h
        push Not at h
        exact hF p (Finset.mem_insert_self p F) (hem (RingHom.ext h))
      have hfin : (⋃ q ∈ ((↑(insert p F) : Set (ι × ι))),
          {t : ℕ | (em q.1 x - em q.2 x) + (t : K) * (em q.1 z - em q.2 z) = 0}).Finite := by
        refine Set.Finite.biUnion (Finset.finite_toSet _) fun q hq => (aff_sub _ _ ?_).finite
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hq) with rfl | hq'
        · exact Or.inr (sub_ne_zero.2 hz)
        · exact Or.inl (sub_ne_zero.2 (hx q hq'))
      obtain ⟨t, ht⟩ := hfin.infinite_compl.nonempty
      refine ⟨x + (t : O) * z, fun q hq h => ht (Set.mem_biUnion (Finset.mem_coe.2 hq) ?_)⟩
      simp only [Set.mem_ofPred_eq]
      simp only [map_add (f := _), map_mul, map_natCast] at h
      linear_combination h
  obtain ⟨x0, hx0⟩ := key (Finset.univ.filter fun q : ι × ι => q.1 ≠ q.2)
    (fun q hq => (Finset.mem_filter.1 hq).2)
  exact ⟨x0, fun c c' hcc' => hx0 (c, c') (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcc'⟩)⟩

end Sep

section Mat

variable {K : Type} [Field K] {n : ℕ}

theorem alg_mulVec (a : K) (A : Matrix (Fin n) (Fin n) K) (w : Fin n → K) :
    (algebraMap K (Matrix (Fin n) (Fin n) K) a * A) *ᵥ w = a • (A *ᵥ w) := by
  rw [← Algebra.smul_def, Matrix.smul_mulVec]

theorem alg_mulVec1 (a : K) (w : Fin n → K) :
    algebraMap K (Matrix (Fin n) (Fin n) K) a *ᵥ w = a • w := by
  rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem commute_aeval {A B : Matrix (Fin n) (Fin n) K} (h : Commute A B) (f : K[X]) : Commute A (aeval B f) := by
  induction f using Polynomial.induction_on with
  | C a =>
    rw [aeval_C]
    exact (Algebra.commutes a A).symm
  | add p q hp hq =>
    rw [map_add (f := _)]
    exact hp.add_right hq
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
    exact ih.mul_right h

theorem pow_shift (N B : Matrix (Fin n) (Fin n) K) (hNB : Commute N B) (lam : K) (w : Fin n → K)
    (hw : N *ᵥ w = lam • w) (k : ℕ) :
    (N + B) ^ k *ᵥ w = (algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) ^ k *ᵥ w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ih,
      Matrix.add_mulVec, Matrix.add_mulVec]
    congr 1
    have hc : Commute N ((algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) ^ k) :=
      ((show Commute (algebraMap K (Matrix (Fin n) (Fin n) K) lam) N from Algebra.commutes lam N).symm.add_right
        hNB).pow_right k
    rw [Matrix.mulVec_mulVec, hc.eq, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_smul, alg_mulVec1]

theorem aeval_shift (N B : Matrix (Fin n) (Fin n) K) (hNB : Commute N B) (lam : K) (w : Fin n → K)
    (hw : N *ᵥ w = lam • w) (f : K[X]) :
    aeval (N + B) f *ᵥ w = aeval (algebraMap K (Matrix (Fin n) (Fin n) K) lam + B) f *ᵥ w := by
  induction f using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mulVec, Matrix.add_mulVec, hp, hq]
  | monomial k a _ =>
    rw [map_mul, map_mul, aeval_C, aeval_C, map_pow, map_pow, aeval_X, aeval_X, alg_mulVec, alg_mulVec,
      pow_shift N B hNB lam w hw (k + 1)]

theorem X_sub_mul_basis {ι : Type} [DecidableEq ι] {s : Finset ι} {v : ι → K} {i : ι} (hi : i ∈ s) :
    (X - Polynomial.C (v i)) * Lagrange.basis s v i =
      Polynomial.C (Lagrange.nodalWeight s v i) * Lagrange.nodal s v := by
  rw [Lagrange.nodal_eq_mul_nodal_erase hi]
  simp only [Lagrange.basis, Lagrange.basisDivisor, Finset.prod_mul_distrib, Lagrange.nodalWeight, Lagrange.nodal,
    map_prod]
  ring

theorem coeff_extract [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι] (B : Matrix (Fin n) (Fin n) K)
    (w : Fin n → K) (a μ : ι → K) (c : ι) (hac : a c = 0) (ha : ∀ c', c' ≠ c → a c' ≠ 0)
    (h : ∀ t : ℕ, aeval B (∏ c', (Polynomial.C (a c') + Polynomial.C (t : K) * (X - Polynomial.C (μ c')))) *ᵥ w = 0) :
    B *ᵥ w = μ c • w := by
  set R : K[X][X] := ∏ c', (Polynomial.C (Polynomial.C (a c')) + X * Polynomial.C (X - Polynomial.C (μ c'))) with hR
  have hev : ∀ t : ℕ, R.eval (Polynomial.C (t : K)) =
      ∏ c', (Polynomial.C (a c') + Polynomial.C (t : K) * (X - Polynomial.C (μ c'))) := by
    intro t
    rw [hR, eval_prod]
    refine Finset.prod_congr rfl fun c' _ => ?_
    rw [eval_add, eval_C, eval_mul, eval_X, eval_C]
  have hcoord : ∀ i, (aeval B (R.coeff 1) *ᵥ w) i = 0 := by
    intro i
    set q : K[X] := ∑ k ∈ Finset.range (R.natDegree + 2), monomial k ((aeval B (R.coeff k) *ᵥ w) i) with hq
    have hroot : ∀ t : ℕ, q.eval (t : K) = 0 := by
      intro t
      have h1 := congrFun (h t) i

      rw [← hev t, eval_eq_sum_range' (n := R.natDegree + 2) (by omega), map_sum, Matrix.sum_mulVec,
      Finset.sum_apply, Pi.zero_apply] at h1
      rw [hq, eval_finsetSum]
      refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) h1
      rw [eval_monomial, ← map_pow, map_mul, aeval_C, ← Algebra.commutes, alg_mulVec, Pi.smul_apply, smul_eq_mul,
        mul_comm]
    have hq0 : q = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Nat.cast_injective (R := K)))
      rintro _ ⟨t, rfl⟩
      exact hroot t
    have hc1 := congrArg (fun p : K[X] => p.coeff 1) hq0
    simp only [hq, finsetSum_coeff, coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range, coeff_zero] at hc1
    rw [if_pos (by omega)] at hc1
    exact hc1
  have hR1 : R.coeff 1 = (X - Polynomial.C (μ c)) * Polynomial.C (∏ c' ∈ Finset.univ.erase c, a c') := by
    rw [hR, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c), hac, map_zero, map_zero, zero_add, mul_assoc]
    refine (coeff_X_mul _ 0).trans ?_
    rw [coeff_C_mul, coeff_zero_eq_eval_zero, eval_prod, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun c' _ => ?_
    rw [eval_add, eval_C, eval_mul, eval_X, zero_mul, add_zero]
  have hπ : ∏ c' ∈ Finset.univ.erase c, a c' ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun c' hc' => ha c' (Finset.ne_of_mem_erase hc')
  have hv : aeval B (R.coeff 1) *ᵥ w = 0 := funext hcoord
  rw [hR1, map_mul, aeval_C, ← Algebra.commutes, alg_mulVec, map_sub, aeval_X, aeval_C, Matrix.sub_mulVec,
    alg_mulVec1] at hv
  have h2 := (smul_eq_zero.1 hv).resolve_left hπ
  rwa [sub_eq_zero] at h2

end Mat

theorem split_holds : SplitSt := by
  intro K _ _ O _ n ι _ _ M P em hPP hPM hinj hann v
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hP : P = 0 := by
      have h := hann 0
      rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, one_mul] at h
      exact h
    refine ⟨fun c => (hι.false c).elim, ?_, fun c => (hι.false c).elim⟩
    rw [hP, Matrix.zero_mulVec, Finset.univ_eq_empty, Finset.sum_empty]
  obtain ⟨x0, hx0⟩ := exists_sep em hinj
  have hinjl : Set.InjOn (fun c => em c x0) (Finset.univ : Finset ι) := fun c _ c' _ h => by
    by_contra hne
    exact hx0 c c' hne h
  refine ⟨fun c => P *ᵥ (aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c) *ᵥ v), ?_, ?_⟩

  · rw [← Matrix.mulVec_sum, ← Matrix.sum_mulVec, ← map_sum, Lagrange.sum_basis hinjl Finset.univ_nonempty, map_one,
    Matrix.one_mulVec]
  intro c x
  set u := aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c) *ᵥ v with hu
  have hP0 : Commute P (M x0) := hPM x0

  have hXL : (X - Polynomial.C (em c x0)) * Lagrange.basis Finset.univ (fun c => em c x0) c =
      Polynomial.C (Lagrange.nodalWeight Finset.univ (fun c => em c x0) c) * ∏ c', (X - Polynomial.C (em c' x0)) :=
    by
      simpa only [Lagrange.nodal_eq] using
        (X_sub_mul_basis (v := fun c' => em c' x0) (Finset.mem_univ c))
  have hE0 : (M x0 - algebraMap K _ (em c x0)) *
      (P * aeval (M x0) (Lagrange.basis Finset.univ (fun c => em c x0) c)) = 0 := by
    have e1 : M x0 - algebraMap K (Matrix (Fin n) (Fin n) K) (em c x0) = aeval (M x0) (X - Polynomial.C (em c x0)) := by
      rw [map_sub, aeval_X, aeval_C]
    rw [e1, ← mul_assoc, ← (commute_aeval hP0 _).eq, mul_assoc, ← map_mul, hXL, map_mul, aeval_C, ← mul_assoc,
      ← Algebra.commutes, mul_assoc, (commute_aeval hP0 _).eq, hann x0, mul_zero]
  have hw0 : M x0 *ᵥ (P *ᵥ u) = em c x0 • (P *ᵥ u) := by
    have h1 := congrArg (fun A => A *ᵥ v) hE0
    simp only [Matrix.zero_mulVec] at h1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, alg_mulVec1, sub_eq_zero] at h1
    exact h1

  refine coeff_extract (M x) (P *ᵥ u) (fun c' => em c x0 - em c' x0) (fun c' => em c' x) c (sub_self _)
    (fun c' hc' => sub_ne_zero.2 (hx0 c c' (Ne.symm hc'))) fun t => ?_
  have hcx : Commute (M x0) ((t : Matrix (Fin n) (Fin n) K) * M x) := by
    refine ((Nat.cast_commute t (M x0)).symm).mul_right ?_
    show M x0 * M x = M x * M x0
    rw [← map_mul, ← map_mul, mul_comm]
  have h1 := congrArg (fun A => A *ᵥ u) (hann (x0 + (t : O) * x))
  simp only [Matrix.zero_mulVec] at h1
  rw [← Matrix.mulVec_mulVec, map_add (f := _), map_mul, map_natCast, aeval_shift _ _ hcx (em c x0) _ hw0] at h1
  have e2 : algebraMap K (Matrix (Fin n) (Fin n) K) (em c x0) + (t : Matrix (Fin n) (Fin n) K) * M x =
      aeval (M x) (Polynomial.C (em c x0) + Polynomial.C (t : K) * X) := by
    rw [map_add (f := _), map_mul, aeval_C, aeval_C, aeval_X, map_natCast]
  rw [e2, ← aeval_comp, prod_comp] at h1
  refine Eq.trans ?_ h1
  congr 2
  refine Finset.prod_congr rfl fun c' _ => ?_
  rw [sub_comp, X_comp, C_comp]
  simp only [map_add (f := _), map_mul, map_natCast, map_sub]
  ring

end RowTiePSplit

end Formalism.L2.FormalSeriesBounds
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLieSelf

section

@[expose] public section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace ProjLieSelf

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie RowTiePSplit RowTiePKey

theorem keySelf (hE : KeyEigSt) {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
    {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ} [NeZero d] {I0 : Type} [Fintype I0] (p : SelfData Y d I0) (ε : O)
    (hε : ∃ y, ε * ε - ε = (V.l : O) * y) (hε1 : ∀ a, V.MM (p.em a ε - 1))
    (hεx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, ε * x = (V.l : O) * y) (e : Pt C 1 dd)
    (he : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i))) (x : O) :
    Polynomial.aeval (linM (Y.B.A.act x)) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (p.em c x))) * linM e = 0 := by
  let K : KeyData C V O dd d :=
    { ρ := linHom Y
      ρ_int := fun x i j => Y.intAct x i _
      P := linM e
      em := p.em
      em_int := p.em_int
      em_frob := p.em_frob
      ε := ε
      ε_idem := hε
      ε_one := hε1
      ε_ann := hεx
      P_lim := fun N i j => he N i _ }
  exact keyLA_of hE RowTiePKeyRes.keyRes_holds keyDelta_holds C V Y.algClosed Y.cpl O dd d K x

end ProjLieSelf


open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie RowTiePSplit RowTiePKey in
theorem projLieSelf_of (hE : KeyEigSt) : ProjLieSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p ε hε hε1 hεx e he v
  obtain ⟨e0, hidem, hcomm⟩ := proj_core Y ε hε e he
  have hinj : Function.Injective (fun c : ZMod d => p.em c) := by
    intro c c' h
    by_contra hne
    obtain ⟨x, hx⟩ := p.em_sep c c' hne
    have h2 : p.em c = p.em c' := h
    rw [h2, sub_self, AddValuation.map_zero] at hx
    simp at hx
  have hPP : linM e * linM e = linM e := by rw [← lin_comp1 e0, hidem]
  have hPM : ∀ x, linM e * linHom Y x = linHom Y x * linM e := fun x => by
    show linM e * linM (Y.B.A.act x) = linM (Y.B.A.act x) * linM e
    rw [← lin_comp1 (Y.B.A.const x), ← lin_comp1 e0, hcomm x]
  obtain ⟨w, hw, hwe⟩ := split_holds C O dd (ZMod d) (linHom Y) (linM e) (fun c => p.em c) hPP hPM hinj
    (fun x => ProjLieSelf.keySelf hE Y p ε hε hε1 hεx e he x) v
  have hb : ∀ c, ∃ b : I0 → C, (∀ c', p.ty0 c' ≠ c → b c' = 0) ∧ w c = ∑ c', b c' • p.e c' := fun c =>
    p.e_full c (w c) fun x => by rw [linAct_eq]; exact hwe c x
  choose b _ hbw using hb
  refine ⟨fun c' => ∑ c, b c c', ?_⟩
  rw [linAct_eq, hw]
  simp_rw [hbw, Finset.sum_smul]
  exact Finset.sum_comm

theorem allStartSelf_of_eig (hE : RowTiePKey.KeyEigSt) : AllStartSelfSt := allStartSelf_of (projLieSelf_of hE)

end Formalism.L2.FormalSeriesBounds
end
end
end
