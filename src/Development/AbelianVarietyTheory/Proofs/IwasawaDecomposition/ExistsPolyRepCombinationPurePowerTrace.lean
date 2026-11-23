module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AevalDualModel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieTensorProductStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieExteriorSquare

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.PolyRep

theorem snd_wedge2_dual {M : ℕ} {R : Type} [CommRing R] (L : Matrix (Fin M) (Fin M) R) (p q : Fin (pairCard M)) :
    TrivSqZeroExt.snd (ChernSpan.wedge2 (Matrix.of fun a b =>
        (TrivSqZeroExt.inl ((1 : Matrix (Fin M) (Fin M) R) a b) + TrivSqZeroExt.inr (L a b) : DualNumber R)) p q)
      = wedge2Lie L p q := by
  simp only [ChernSpan.wedge2, wedge2Lie, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
    wedgeRaw, wedgeLieRaw, Matrix.of_apply]
  simp only [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.fst_add,
    TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
    smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, add_zero, zero_add]
  ring

theorem lie_wedge2 {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) :
    ρ.wedge2.lie A = wedge2Lie (ρ.lie A) := by
  ext p q
  have h := ev_dual_model ρ.wedge2 A p q
  have e : ∀ D : Mat m (DualNumber R), ρ.wedge2.ev D = ChernSpan.wedge2 (ρ.ev D) :=
    fun D => evEnt_wedge2 ρ.ent D
  have e2 : ρ.ev (R := DualNumber R) (fun τ => Matrix.of fun a b =>
        TrivSqZeroExt.inl ((1 : Mat m R) τ a b) + TrivSqZeroExt.inr (A τ a b))
      = Matrix.of fun a b => (TrivSqZeroExt.inl ((1 : Matrix (Fin ρ.M) (Fin ρ.M) R) a b)
        + TrivSqZeroExt.inr (ρ.lie A a b) : DualNumber R) := by
    ext a b : 1
    exact ev_dual_model ρ A a b
  rw [e, e2] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at h2
  exact h2.symm.trans (snd_wedge2_dual (ρ.lie A) p q)

end GlobalTheory.GoodMetric.PolyRep

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialMatrixFamilyRepLieExteriorSquareStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.polynomialMatrixFamilyRep_lie_exteriorSquare : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R), ρ.wedge2.lie A = wedge2Lie (ρ.lie A) := by
  first | exact @GlobalTheory.GoodMetric.PolyRep.lie_wedge2 | exact GlobalTheory.GoodMetric.PolyRep.lie_wedge2 | (intros; apply GlobalTheory.GoodMetric.PolyRep.lie_wedge2 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulTraceExteriorSquareDerivationPow

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped Matrix
open Finset

namespace GlobalTheory.GoodMetric.ChernSpan.TraceWedgeSq

variable {R : Type} [CommRing R] {M : ℕ}

theorem trace_reindex_self {m n : Type} [Fintype m] [Fintype n] (e : m ≃ n) (A : Matrix m m R) :
    (Matrix.reindex e e A).trace = A.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diag]
  exact e.symm.sum_comp (fun x => A x x)

theorem reindex_pow_self {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m R) (k : ℕ) :
    (Matrix.reindex e e A) ^ k = Matrix.reindex e e (A ^ k) := by
  induction k with
  | zero => simp [Matrix.submatrix_one_equiv]
  | succ k ih =>
    rw [pow_succ, pow_succ, ih]
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

def embF (x : Fin M × Fin M) (a b : Fin M) : R :=
  (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 b -
    (1 : Matrix (Fin M) (Fin M) R) x.1 b * (1 : Matrix (Fin M) (Fin M) R) x.2 a

def emb (R : Type) [CommRing R] (M : ℕ) : Matrix (Fin M × Fin M) (Pair M) R :=
  Matrix.of fun x r => embF x r.1.1 r.1.2

theorem sum_mul_embF (A : Fin M × Fin M → R) (a b : Fin M) :
    ∑ y, A y * embF y a b = A (a, b) - A (b, a) := by
  simp [embF, Fintype.sum_prod_type, Matrix.one_apply, mul_sub, Finset.sum_sub_distrib, mul_ite]

theorem sum_emb_mul (x : Fin M × Fin M) (G : Fin M → Fin M → R) (hG : ∀ a b, G b a = - G a b)
    (hG0 : ∀ a, G a a = 0) :
    ∑ q : Pair M, emb R M x q * G q.1.1 q.1.2 = G x.1 x.2 := by
  have h := sum_sum_eq_sum_pair (fun a b =>
    (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 b * G a b)
  have hl : ∑ a, ∑ b, (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 b * G a b
      = G x.1 x.2 := by
    simp [Matrix.one_apply]
  have hd : ∑ a, (1 : Matrix (Fin M) (Fin M) R) x.1 a * (1 : Matrix (Fin M) (Fin M) R) x.2 a * G a a = 0 :=
    Finset.sum_eq_zero fun a _ => by rw [hG0, mul_zero]
  rw [hl, hd, add_zero] at h
  rw [h]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [emb, embF, Matrix.of_apply, hG q.1.1 q.1.2]
  ring

theorem mul_emb_apply {n : Type} (A : Matrix n (Fin M × Fin M) R) (x : n) (r : Pair M) :
    (A * emb R M) x r = A x (r.1.1, r.1.2) - A x (r.1.2, r.1.1) := by
  rw [Matrix.mul_apply]
  exact sum_mul_embF (fun y => A x y) r.1.1 r.1.2

def wedgeLieExt (L : Matrix (Fin M) (Fin M) R) (a b : Fin M) (r : Pair M) : R :=
  L a r.1.1 * (1 : Matrix (Fin M) (Fin M) R) b r.1.2 + (1 : Matrix (Fin M) (Fin M) R) a r.1.1 * L b r.1.2 -
    L b r.1.1 * (1 : Matrix (Fin M) (Fin M) R) a r.1.2 - (1 : Matrix (Fin M) (Fin M) R) b r.1.1 * L a r.1.2

def tensorLie (L : Matrix (Fin M) (Fin M) R) : Matrix (Fin M × Fin M) (Fin M × Fin M) R :=
  Matrix.kroneckerMap (· * ·) L 1 + Matrix.kroneckerMap (· * ·) 1 L

theorem tensorLie_mul_emb (L : Matrix (Fin M) (Fin M) R) :
    tensorLie L * emb R M = emb R M * wedgeLieRaw L := by
  ext x r
  rw [mul_emb_apply, Matrix.mul_apply]
  have h := sum_emb_mul x (fun a b => wedgeLieExt L a b r)
    (fun a b => by simp only [wedgeLieExt]; ring) (fun a => by simp only [wedgeLieExt]; ring)
  rw [show (∑ q : Pair M, emb R M x q * wedgeLieRaw L q r) =
      ∑ q : Pair M, emb R M x q * wedgeLieExt L q.1.1 q.1.2 r from rfl, h]
  simp only [tensorLie, wedgeLieExt, Matrix.add_apply, Matrix.kroneckerMap_apply]
  ring

theorem tensorLie_pow_mul_emb (L : Matrix (Fin M) (Fin M) R) (n : ℕ) :
    tensorLie L ^ n * emb R M = emb R M * wedgeLieRaw L ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, Matrix.one_mul, Matrix.mul_one]
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_assoc, tensorLie_mul_emb, ← Matrix.mul_assoc, ih, Matrix.mul_assoc]

theorem emb_transpose_mul_emb :
    (emb R M)ᵀ * emb R M = (2 : R) • (1 : Matrix (Pair M) (Pair M) R) := by
  ext ⟨⟨i, j⟩, hij⟩ ⟨⟨k, l⟩, hkl⟩
  rw [mul_emb_apply]
  simp only [Matrix.transpose_apply, emb, embF, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply,
    Subtype.mk.injEq, Prod.mk.injEq, smul_eq_mul]
  simp only at hij hkl
  have h0 : ¬ (k = j ∧ l = i) := fun h => by
    rcases h with ⟨rfl, rfl⟩; exact absurd (hij.trans hkl) (lt_irrefl _)
  by_cases h1 : k = i <;> by_cases h2 : l = j
  · subst h1; subst h2; simp [hkl.ne, hkl.ne']; ring
  · have : ¬ (i = k ∧ j = l) := fun h => h2 h.2.symm
    by_cases h3 : k = j <;> by_cases h4 : l = i <;> simp_all
  · have : ¬ (i = k ∧ j = l) := fun h => h1 h.1.symm
    by_cases h3 : k = j <;> by_cases h4 : l = i <;> simp_all
  · have : ¬ (i = k ∧ j = l) := fun h => h1 h.1.symm
    by_cases h3 : k = j <;> by_cases h4 : l = i <;> simp_all

theorem emb_mul_transpose_apply (x y : Fin M × Fin M) :
    (emb R M * (emb R M)ᵀ) x y = embF x y.1 y.2 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  simp only [mul_comm (emb R M x _)]
  exact sum_emb_mul y (fun a b => embF x a b) (fun a b => by simp only [embF]; ring)
    (fun a => by simp only [embF]; ring)

theorem trace_mul_emb_mul_transpose (A : Matrix (Fin M × Fin M) (Fin M × Fin M) R) :
    (A * (emb R M * (emb R M)ᵀ)).trace = A.trace - ∑ x : Fin M × Fin M, A x (x.2, x.1) := by
  simp only [Matrix.trace, Matrix.diag]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Matrix.mul_apply]
  simp only [emb_mul_transpose_apply]
  exact sum_mul_embF (fun y => A x y) x.1 x.2

theorem sum_kron_swap (P Q : Matrix (Fin M) (Fin M) R) :
    ∑ x : Fin M × Fin M, Matrix.kroneckerMap (· * ·) P Q x (x.2, x.1) = (P * Q).trace := by
  simp [Fintype.sum_prod_type, Matrix.trace, Matrix.mul_apply]

theorem kron_left_pow (L : Matrix (Fin M) (Fin M) R) (m : ℕ) :
    (Matrix.kroneckerMap (· * ·) L (1 : Matrix (Fin M) (Fin M) R)) ^ m =
      Matrix.kroneckerMap (· * ·) (L ^ m) (1 : Matrix (Fin M) (Fin M) R) := by
  induction m with
  | zero => simp [Matrix.one_kronecker_one]
  | succ m ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul, Matrix.mul_one, pow_succ]

theorem kron_right_pow (L : Matrix (Fin M) (Fin M) R) (m : ℕ) :
    (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) L) ^ m =
      Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) (L ^ m) := by
  induction m with
  | zero => simp [Matrix.one_kronecker_one]
  | succ m ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul, Matrix.mul_one, pow_succ]

theorem sum_tensorLie_pow_swap (L : Matrix (Fin M) (Fin M) R) (n : ℕ) :
    ∑ x : Fin M × Fin M, (tensorLie L ^ n) x (x.2, x.1) = 2 ^ n * (L ^ n).trace := by
  have hc : Commute (Matrix.kroneckerMap (· * ·) L (1 : Matrix (Fin M) (Fin M) R))
      (Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) L) := by
    show _ * _ = _ * _
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  have hterm : ∀ m ∈ Finset.range (n + 1), ∀ x : Fin M × Fin M,
      (Matrix.kroneckerMap (· * ·) L (1 : Matrix (Fin M) (Fin M) R) ^ m *
        Matrix.kroneckerMap (· * ·) (1 : Matrix (Fin M) (Fin M) R) L ^ (n - m) *
        ((n.choose m : ℕ) : Matrix (Fin M × Fin M) (Fin M × Fin M) R)) x (x.2, x.1) =
      (n.choose m : R) * Matrix.kroneckerMap (· * ·) (L ^ m) (L ^ (n - m)) x (x.2, x.1) := by
    intro m _ x
    rw [kron_left_pow, kron_right_pow, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      ← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul]
  have htr : ∀ m ∈ Finset.range (n + 1), (L ^ m * L ^ (n - m)).trace = (L ^ n).trace := by
    intro m hm
    rw [← pow_add, Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm))]
  rw [tensorLie, hc.add_pow]
  simp only [Matrix.sum_apply]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun m hm => (Finset.sum_congr rfl fun x _ => hterm m hm x)]
  simp only [← Finset.mul_sum, sum_kron_swap]
  rw [Finset.sum_congr rfl fun m hm => by rw [htr m hm], ← Finset.sum_mul]
  rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

end GlobalTheory.GoodMetric.ChernSpan.TraceWedgeSq

namespace GlobalTheory.GoodMetric.ChernSpan

open TraceWedgeSq

theorem two_mul_trace_wedge2Lie_pow {R : Type} [CommRing R] {M : ℕ} (L : Matrix (Fin M) (Fin M) R) (i : ℕ) :
    2 * ((wedge2Lie L) ^ i).trace = ((kron L 1 + kron 1 L) ^ i).trace - 2 ^ i * (L ^ i).trace := by
  have hW : ((wedge2Lie L) ^ i).trace = ((wedgeLieRaw L) ^ i).trace := by
    rw [wedge2Lie, reindex_pow_self, trace_reindex_self]
  have hK : kron L 1 + kron 1 L = Matrix.reindex finProdFinEquiv finProdFinEquiv (tensorLie L) := by
    ext a b
    simp [kron, tensorLie]
  rw [hW, hK, reindex_pow_self, trace_reindex_self]
  have key : (2 : R) • (wedgeLieRaw L ^ i) = (emb R M)ᵀ * (tensorLie L ^ i * emb R M) := by
    rw [tensorLie_pow_mul_emb, ← Matrix.mul_assoc, emb_transpose_mul_emb, Matrix.smul_mul, Matrix.one_mul]
  calc 2 * (wedgeLieRaw L ^ i).trace = ((2 : R) • (wedgeLieRaw L ^ i)).trace := by
        rw [Matrix.trace_smul, smul_eq_mul]
    _ = (tensorLie L ^ i * emb R M * (emb R M)ᵀ).trace := by rw [key, Matrix.trace_mul_comm]
    _ = _ := by rw [Matrix.mul_assoc, trace_mul_emb_mul_transpose, sum_tensorLie_pow_swap]

end GlobalTheory.GoodMetric.ChernSpan
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMulTraceExteriorSquareDerivationPowStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.two_mul_trace_exteriorSquareDerivation_pow : ∀ {R : Type} [CommRing R] {M : ℕ} (L : Matrix (Fin M) (Fin M) R) (i : ℕ), 2 * ((wedge2Lie L) ^ i).trace = ((kron L 1 + kron 1 L) ^ i).trace - 2 ^ i * (L ^ i).trace := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow | exact GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow | (intros; apply GlobalTheory.GoodMetric.ChernSpan.two_mul_trace_wedge2Lie_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolyRepCombinationPurePowerTrace

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.PureVirt

variable {ι : Type} [Fintype ι] {m : ι → ℕ} {S : Type} [CommRing S] [Algebra ℝ S]

def Virt (m : ι → ℕ) (g : ℕ → Mat m S → S) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ),
    ∀ (A : Mat m S) (b : ℕ), ∑ j, c j • (ρ j).ptr b A = g b A

theorem virt_smul (r : ℝ) {g : ℕ → Mat m S → S} (hg : Virt m g) : Virt m (fun b A => r • g b A) := by
  obtain ⟨J, _, ρ, c, hc⟩ := hg
  refine ⟨J, inferInstance, ρ, fun j => r * c j, fun A b => ?_⟩
  simp only [← hc, Finset.smul_sum, smul_smul]

theorem virt_fsum {α : Type} [Fintype α] (g : α → ℕ → Mat m S → S) (hg : ∀ a, Virt m (g a)) :
    Virt m (fun b A => ∑ a, g a b A) := by
  choose J hJ ρ c hc using hg
  refine ⟨Σ a, J a, inferInstance, fun x => ρ x.1 x.2, fun x => c x.1 x.2, fun A b => ?_⟩
  rw [Fintype.sum_sigma]
  simp only [hc]

theorem ptr_tensor_sub_wedge2 (ρ : PolyRep m) (A : Mat m S) (b : ℕ) :
    (ρ.tensor ρ).ptr b A - 2 * ρ.wedge2.ptr b A = 2 ^ b * ρ.ptr b A := by
  have h := GlobalTheory.T.two_mul_trace_exteriorSquareDerivation_pow (ρ.lie A) b
  have e1 : (ρ.tensor ρ).ptr b A = ((kron (ρ.lie A) 1 + kron 1 (ρ.lie A)) ^ b).trace :=
    congrArg (fun L => (L ^ b).trace) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_tensorProduct ρ ρ A)
  have e2 : ρ.wedge2.ptr b A = ((wedge2Lie (ρ.lie A)) ^ b).trace :=
    congrArg (fun L => (L ^ b).trace) (GlobalTheory.T.polynomialMatrixFamilyRep_lie_exteriorSquare ρ A)
  have e3 : ρ.ptr b A = ((ρ.lie A) ^ b).trace := rfl
  linear_combination e1 - 2 * e2 - h - 2 ^ b * e3

theorem virt_double {g : ℕ → Mat m S → S} (hg : Virt m g) :
    Virt m (fun b A => (2 : ℝ) ^ b • g b A) := by
  obtain ⟨J, _, ρ, c, hc⟩ := hg
  refine ⟨J ⊕ J, inferInstance, Sum.elim (fun j => (ρ j).tensor (ρ j)) (fun j => (ρ j).wedge2),
    Sum.elim c (fun j => -2 * c j), fun A b => ?_⟩
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [← hc, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h := ptr_tensor_sub_wedge2 (ρ j) A b
  simp only [Algebra.smul_def, map_mul, map_neg, map_pow, map_ofNat]
  linear_combination (algebraMap ℝ S (c j)) * h

theorem virt_proj (τ : ι) : Virt m (fun b (A : Mat m S) => ((A τ) ^ b).trace) := by
  refine ⟨Unit, inferInstance, fun _ => proj m τ, fun _ => 1, fun A b => ?_⟩
  simp only [PolyRep.ptr, lie_proj_model, one_smul, Finset.univ_unique, Finset.sum_singleton]
  rfl

theorem virt_pow (τ : ι) (a : ℕ) :
    Virt m (fun b (A : Mat m S) => ((2 : ℝ) ^ a) ^ b • ((A τ) ^ b).trace) := by
  induction a with
  | zero => simpa using virt_proj (m := m) (S := S) τ
  | succ a ih =>
    have e : (fun b (A : Mat m S) => ((2 : ℝ) ^ (a + 1)) ^ b • ((A τ) ^ b).trace)
        = fun b A => (2 : ℝ) ^ b • (((2 : ℝ) ^ a) ^ b • ((A τ) ^ b).trace) := by
      funext b A
      rw [smul_smul, pow_succ, mul_pow, mul_comm]
    rw [e]
    exact virt_double ih

theorem exists_vandermonde_solution (n i : ℕ) : ∃ x : Fin (n + 1) → ℝ, ∀ b : Fin (n + 1),
    ∑ a, x a * ((2 : ℝ) ^ (a : ℕ)) ^ (b : ℕ) = if (b : ℕ) = i then 1 else 0 := by
  set V := Matrix.vandermonde (fun a : Fin (n + 1) => (2 : ℝ) ^ (a : ℕ)) with hV
  have hinj : Function.Injective (fun a : Fin (n + 1) => (2 : ℝ) ^ (a : ℕ)) := by
    intro a a' h
    exact Fin.ext ((pow_right_strictMono₀ one_lt_two).injective h)
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)
  set δ : Fin (n + 1) → ℝ := fun b => if (b : ℕ) = i then 1 else 0 with hδ
  refine ⟨δ ᵥ* V⁻¹, fun b => ?_⟩
  have h : (δ ᵥ* V⁻¹) ᵥ* V = δ := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  exact congrFun h b

theorem exists_pure_power_trace {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S]
    [Algebra ℝ S] (τ : ι) (i : ℕ) (_hi : 1 ≤ i) :
    ∃ (J : Type) (_ : Fintype J) (ρ : J → PolyRep m) (c : J → ℝ), ∀ (A : Mat m S) (b : ℕ), b ≤ n →
      ∑ j, c j • (ρ j).ptr b A = if b = i then ((A τ) ^ i).trace else 0 := by
  obtain ⟨x, hx⟩ := exists_vandermonde_solution n i
  obtain ⟨J, hJ, ρ, c, hc⟩ := virt_fsum (m := m) (S := S)
    (fun a : Fin (n + 1) => fun b A => x a • (((2 : ℝ) ^ (a : ℕ)) ^ b • ((A τ) ^ b).trace))
    (fun a => virt_smul (x a) (virt_pow τ a))
  refine ⟨J, hJ, ρ, c, fun A b hb => ?_⟩
  rw [hc]
  have h := hx ⟨b, Nat.lt_succ_of_le hb⟩
  simp only [smul_smul, ← Finset.sum_smul] at h ⊢
  rw [h]
  split_ifs with hbi
  · subst hbi; exact one_smul ℝ _
  · exact zero_smul ℝ _

end GlobalTheory.GoodMetric.PureVirt

end
end
end
