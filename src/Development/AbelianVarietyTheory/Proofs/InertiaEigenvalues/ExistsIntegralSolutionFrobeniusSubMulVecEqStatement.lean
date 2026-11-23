module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.Analysis.Normed.Group.Ultra

-- Source module: GroundTheory.PAdicHodge.SemilinearResidue

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Polynomial Module Finset

namespace SemilinearResidue

section Poly

variable {k : Type*} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]


omit [CharP k p] in
include hp in
theorem two_le_pow {e : ℕ} (he : 0 < e) : 2 ≤ p ^ e :=
  calc 2 ≤ p := hp.out.two_le
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ e := Nat.pow_le_pow_right hp.out.pos he

variable {e : ℕ}

end Poly

section Vec

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

theorem linearIndependent_of_notMem_span (v : ℕ → V) : ∀ m : ℕ,
    (∀ j < m, v j ∉ Submodule.span k (Set.range (fun i : Fin j => v i))) →
      LinearIndependent k (fun i : Fin m => v i) := by
  intro m
  induction m with
  | zero => exact fun _ => linearIndependent_empty_type
  | succ m ih =>
    intro h
    exact linearIndependent_finSucc'.mpr
      ⟨ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h m (Nat.lt_succ_self m)⟩


variable (k) in
theorem exists_rel [FiniteDimensional k V] (v : ℕ → V) :
    ∃ m, (∃ c : ℕ → k, v m = ∑ i ∈ range m, c i • v i) ∧
      LinearIndependent k (fun i : Fin m => v i) := by
  classical
  let P : ℕ → Prop := fun j => v j ∈ Submodule.span k (Set.range (fun i : Fin j => v i))
  have hex : ∃ j, P j := by
    by_contra hcon
    push Not at hcon
    have li := linearIndependent_of_notMem_span v (finrank k V + 1) (fun j _ => hcon j)
    have := li.fintype_card_le_finrank
    simp at this
  refine ⟨Nat.find hex, ?_, linearIndependent_of_notMem_span v _ (fun j hj => Nat.find_min hex hj)⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp (Nat.find_spec hex)
  refine ⟨fun i => if h : i < Nat.find hex then c ⟨i, h⟩ else 0, ?_⟩
  rw [← hc, Finset.sum_range]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [i.2]

variable {p : ℕ} [hp : Fact p.Prime] [CharP k p] {e : ℕ} {φ : V →+ V}


end Vec

end SemilinearResidue

end GroundTheory.PAdicHodge
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralSolutionFrobeniusSubMulVecEq

section

@[expose] public section

noncomputable section

namespace GlobalTheory.PMonE.LangOnto

open Polynomial Finset GlobalTheory.PMonE

def backPoly {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) (j : ℕ) : k[X] :=
  Nat.rec X (fun j P => P ^ q - C (c (n - j)) * X) j

theorem backPoly_zero {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) : backPoly q n c 0 = X := rfl

theorem backPoly_succ {k : Type*} [Field k] (q n : ℕ) (c : ℕ → k) (j : ℕ) :
    backPoly q n c (j + 1) = backPoly q n c j ^ q - C (c (n - j)) * X := rfl

theorem backPoly_natDegree {k : Type*} [Field k] {q : ℕ} (hq : 2 ≤ q) (n : ℕ) (c : ℕ → k) :
    ∀ j, 1 ≤ (backPoly q n c j).natDegree := by
  intro j
  induction j with
  | zero => simp [backPoly_zero]
  | succ j ih =>
    have h1 : (C (c (n - j)) * X : k[X]).natDegree ≤ 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_
      simp
    have h2 : 2 ≤ (backPoly q n c j ^ q).natDegree := by
      rw [natDegree_pow]; nlinarith
    rw [backPoly_succ, natDegree_sub_eq_left_of_natDegree_lt (by omega)]
    omega

theorem exists_sub_eq_inv {k : Type*} [Field k] [IsAlgClosed k] {V : Type*} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] {q : ℕ} (hq : 2 ≤ q) (ψ : V →+ V)
    (hψ : ∀ (c : k) (x : V), ψ (c ^ q • x) = c • ψ x) (z : V) : ∃ y, y - ψ y = z := by
  obtain ⟨m, ⟨c, hrel⟩, -⟩ := GroundTheory.PAdicHodge.SemilinearResidue.exists_rel (k := k) (fun i => (⇑ψ)^[i] z)
  cases m with
  | zero => exact ⟨0, by simpa using hrel.symm⟩
  | succ n =>
    have hdeg : (backPoly q n c (n + 1) - C 1).degree ≠ 0 := by
      rw [degree_sub_C (natDegree_pos_iff_degree_pos.mp (backPoly_natDegree hq n c (n + 1)))]
      exact (natDegree_pos_iff_degree_pos.mp (backPoly_natDegree hq n c (n + 1))).ne'
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_root _ hdeg
    set u : ℕ → k := fun i => (backPoly q n c (n - i)).eval t with hu
    have h0 : u 0 ^ q = 1 + c 0 * t := by
      have := ht.eq_zero
      simp only [backPoly_succ, eval_sub, eval_pow, eval_mul, eval_C, eval_X, Nat.sub_self] at this
      simp only [hu, Nat.sub_zero]
      linear_combination this
    have hn : u n = t := by simp [hu, backPoly_zero]
    have hs : ∀ i ∈ range n, u (i + 1) ^ q = u i + c (i + 1) * t := by
      intro i hi
      have hi' : i < n := mem_range.mp hi
      have e1 : n - i = (n - (i + 1)) + 1 := by omega
      have e2 : n - (n - (i + 1)) = i + 1 := by omega
      simp only [hu]
      rw [e1]
      simp only [backPoly_succ, eval_sub, eval_pow, eval_mul, eval_C, eval_X, e2]
      ring
    have hit : ∀ i, ψ ((⇑ψ)^[i] z) = (⇑ψ)^[i + 1] z := fun i =>
      (Function.iterate_succ_apply' _ _ _).symm
    refine ⟨∑ i ∈ range (n + 1), u i ^ q • (⇑ψ)^[i] z, ?_⟩

    rw [map_sum]
    simp_rw [hψ, hit]
    have hA : ∑ i ∈ range n, u (i + 1) ^ q • (⇑ψ)^[i + 1] z
        = ∑ i ∈ range n, (u i + c (i + 1) * t) • (⇑ψ)^[i + 1] z :=
      sum_congr rfl (fun i hi => by rw [hs i hi])
    rw [sum_range_succ (fun i => u i • (⇑ψ)^[i + 1] z), hn, hrel, smul_sum, sum_range_succ' _ n,
      sum_range_succ' (fun i => t • c i • (⇑ψ)^[i] z) n, hA, h0]
    simp only [Function.iterate_zero, id, smul_smul, add_smul, sum_add_distrib, one_smul, mul_comm t]
    abel

theorem exists_sol {F : Type*} [Field F] [IsAlgClosed F] (p : ℕ) [hp : Fact p.Prime] [CharP F p] {m : Type*}
    [Fintype m] {e : ℕ} (he : 0 < e) (A : Matrix m m F) (b : m → F) :
    ∃ x : m → F, ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  have : ExpChar F p := ExpChar.prime hp.out
  have hq : 2 ≤ p ^ e := GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow he
  let r : F ≃+* F := (iterateFrobeniusEquiv F p e).symm
  have hr : ∀ a : F, r a ^ p ^ e = a := fun a => by
    rw [← iterateFrobeniusEquiv_def]
    exact (iterateFrobeniusEquiv F p e).apply_symm_apply a
  have hr' : ∀ a : F, r (a ^ p ^ e) = a := fun a => by
    rw [← iterateFrobeniusEquiv_def]
    exact (iterateFrobeniusEquiv F p e).symm_apply_apply a
  let ψ : (m → F) →+ (m → F) := AddMonoidHom.mk' (fun y => A.mulVec (fun i => r (y i))) (fun y y' => by
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp)
  have hψ : ∀ (c : F) (x : m → F), ψ (c ^ p ^ e • x) = c • ψ x := by
    intro c x
    change A.mulVec _ = c • A.mulVec _
    rw [← Matrix.mulVec_smul]
    congr 1
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, hr']
  obtain ⟨y, hy⟩ := exists_sub_eq_inv hq ψ hψ b
  refine ⟨fun i => r (y i), fun i => ?_⟩
  rw [hr, ← hy]
  rfl

theorem lang_onto : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ)
    [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F,
    (∀ i j, ‖A i j‖ ≤ 1) → ∀ b : m → F, Integral b →
      ∃ x : m → F, Integral x ∧ ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  intro F _ _ _ p _ _ m _ _ e he A hA b hb
  obtain ⟨x, hx⟩ := exists_sol p he A b
  refine ⟨x, ?_, hx⟩
  have hq : 2 ≤ p ^ e := GroundTheory.PAdicHodge.SemilinearResidue.two_le_pow he
  intro i₀
  by_contra hlt
  push Not at hlt
  obtain ⟨i, -, hi⟩ := exists_max_image univ (fun j => ‖x j‖) ⟨i₀, mem_univ _⟩
  have hR : 1 < ‖x i‖ := hlt.trans_le (hi i₀ (mem_univ _))
  have h1 : ‖A.mulVec x i‖ ≤ ‖x i‖ := by
    simp only [Matrix.mulVec, dotProduct]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun j _ => ?_)
    rw [norm_mul]
    calc ‖A i j‖ * ‖x j‖ ≤ 1 * ‖x j‖ := mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)
      _ ≤ ‖x i‖ := by rw [one_mul]; exact hi j (mem_univ _)
  have h2 : x i ^ p ^ e = b i + A.mulVec x i := by rw [← hx i]; ring
  have h3 : ‖x i‖ ^ p ^ e ≤ ‖x i‖ := by
    rw [← norm_pow, h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hb i).trans hR.le) h1)
  have h4 : ‖x i‖ ^ 1 < ‖x i‖ ^ p ^ e := pow_lt_pow_right₀ hR (by omega)
  rw [pow_one] at h4
  linarith

end GlobalTheory.PMonE.LangOnto

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralSolutionFrobeniusSubMulVecEqStatement

section

@[expose] public section

open GlobalTheory.PMonE

theorem _root_.GlobalTheory.T.exists_integral_solution_frobenius_sub_mulVec_eq : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → ∀ b : m → F, Integral b → ∃ x : m → F, Integral x ∧ ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  first | exact @GlobalTheory.PMonE.LangOnto.lang_onto | exact GlobalTheory.PMonE.LangOnto.lang_onto | (intros; apply GlobalTheory.PMonE.LangOnto.lang_onto <;> assumption)
end
end
