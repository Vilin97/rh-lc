module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicConjInvariantEqSumInducedDerivativesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionBlockDiagEqHarishChandraGelfan
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClassFunctionBernsteinZelevinskyDerivative

section

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

noncomputable section

namespace GlobalTheory.GLm.DerClass

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

def blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g)) (D : Mt g b) :
    Mt g (a + b) :=
  (Matrix.fromBlocks A B C D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem exists_blocks (M : Mt g (a + b)) : ∃ A B C D, M = blocks A B C D := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁, (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [blocks, Matrix.fromBlocks_toBlocks]
  ext i j
  simp

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {a b : ℕ} in
theorem _root_.GlobalTheory.GLm.DerClass.blocks_mul (A A' : _root_.GlobalTheory.GLq.Mt g a)
    (B B' : Matrix (Fin a) (Fin b) (ZMod g)) (C C' : Matrix (Fin b) (Fin a) (ZMod g))
    (D D' : _root_.GlobalTheory.GLq.Mt g b) :
    _root_.GlobalTheory.GLm.DerClass.blocks A B C D * _root_.GlobalTheory.GLm.DerClass.blocks A' B' C' D' =
      _root_.GlobalTheory.GLm.DerClass.blocks (A * A' + B * C') (A * B' + B * D') (C * A' + D * C')
        (C * B' + D * D') := by
  unfold _root_.GlobalTheory.GLm.DerClass.blocks
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

open Polynomial in
open scoped Classical in
variable {g : ℕ} [Fact g.Prime] {a b : ℕ} in
theorem _root_.GlobalTheory.GLm.DerClass.blocks_one :
    _root_.GlobalTheory.GLm.DerClass.blocks (1 : _root_.GlobalTheory.GLq.Mt g a) 0 0 (1 : _root_.GlobalTheory.GLq.Mt g b) = 1 := by
  unfold _root_.GlobalTheory.GLm.DerClass.blocks
  rw [Matrix.fromBlocks_one]
  exact Matrix.submatrix_one_equiv _

theorem tl_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : tl a (blocks A B C D) = A := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [tl, entN, dite_eq_left ⟨by omega, by omega⟩]
  change blocks A B C D (Fin.castAdd b i) (Fin.castAdd b j) = _
  simp [blocks]

theorem br_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : br a b (blocks A B C D) = D := by
  ext i j
  have hi := i.2
  have hj := j.2
  rw [br, entN, dite_eq_left ⟨by omega, by omega⟩]
  change blocks A B C D (Fin.natAdd a i) (Fin.natAdd a j) = _
  simp [blocks]

theorem inPar_blocks (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (C : Matrix (Fin b) (Fin a) (ZMod g))
    (D : Mt g b) : InPar a (blocks A B C D) ↔ C = 0 := by
  constructor
  · intro h
    ext i j
    have := h (Fin.natAdd a i) (Fin.castAdd b j) (by simp) (by simp)
    simpa [blocks] using this
  · rintro rfl i j hj hi
    induction i using Fin.addCases with
    | left i => have := i.2; simp at hi; omega
    | right i =>
      induction j using Fin.addCases with
      | left j => simp [blocks]
      | right j => simp at hj

theorem inMir_blocks (hb : 0 < b) (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) {D : Mt g b} (hD : IsUniUp D) :
    InMir (blocks A B 0 D) := by
  intro i j hi
  rw [← blocks_one]
  induction i using Fin.addCases with
  | left i => have := i.2; simp at hi; omega
  | right i =>
    induction j using Fin.addCases with
    | left j => simp [blocks]
    | right j =>
      have hj := j.2
      simp only [Fin.val_natAdd] at hi
      simp only [blocks, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₂₂]
      by_cases h : i = j
      · rw [(hD i j).2 h, h, Matrix.one_apply_eq]
      · rw [Matrix.one_apply_ne h]
        refine (hD i j).1 ?_
        have : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
        rw [Fin.lt_def]
        omega

theorem isUniUp_one : IsUniUp (1 : Mt g b) := fun i j =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => by rw [h, Matrix.one_apply_eq]⟩

def dg (b : ℕ) (y : Gn g a) : Gn g (a + b) where
  val := blocks y.val 0 0 1
  inv := blocks (y⁻¹).val 0 0 1
  val_inv := by rw [blocks_mul]; simpa using blocks_one
  inv_val := by rw [blocks_mul]; simpa using blocks_one

theorem conj_val (y : Gn g a) (x : Gn g (a + b)) {A : Mt g a} {B : Matrix (Fin a) (Fin b) (ZMod g)}
    {C : Matrix (Fin b) (Fin a) (ZMod g)} {D : Mt g b} (hx : x.val = blocks A B C D) :
    (dg b y * x * (dg b y)⁻¹).val = blocks (y.val * A * (y⁻¹).val) (y.val * B) (C * (y⁻¹).val) D := by
  change blocks y.val 0 0 1 * x.val * blocks (y⁻¹).val 0 0 1 = _
  rw [hx, blocks_mul, blocks_mul]
  simp

theorem res_conj (hb : 0 < b) {F : Gn g (a + b) → ℂ} (hF : IsMirClass F) (h y : Gn g a) (u : Gn g b)
    (hu : IsUniUp (u : Mt g b)) : res a b F (y * h * y⁻¹) u = res a b F h u := by
  unfold res
  congr 1
  symm
  refine Fintype.sum_equiv (MulAut.conj (dg b y)).toEquiv _ _ fun x => ?_
  obtain ⟨A, B, C, D, hx⟩ := exists_blocks x.val
  have e := conj_val y x hx
  change _ = if InPar a (dg b y * x * (dg b y)⁻¹).val ∧ tl a (dg b y * x * (dg b y)⁻¹).val = (y * h * y⁻¹).val ∧
    br a b (dg b y * x * (dg b y)⁻¹).val = u.val then F (dg b y * x * (dg b y)⁻¹) else 0
  rw [e, hx, inPar_blocks, inPar_blocks, tl_blocks, tl_blocks, br_blocks, br_blocks]
  have h1 : C * (y⁻¹).val = 0 ↔ C = 0 := by
    constructor
    · intro hc
      have := congrArg (· * y.val) hc
      simpa [Matrix.mul_assoc] using this
    · rintro rfl
      simp
  have h2 : y.val * A * (y⁻¹).val = (y * h * y⁻¹).val ↔ A = h.val := by
    rw [Units.val_mul, Units.val_mul, Units.mul_left_inj, Units.mul_right_inj]
  simp only [h1, h2]
  split_ifs with hc
  · obtain ⟨rfl, -, rfl⟩ := hc
    refine (hF _ _ ?_ ?_).symm
    · exact inMir_blocks hb _ _ isUniUp_one
    · rw [hx]
      exact inMir_blocks hb _ _ hu
  · rfl

theorem wh_congr (ψ : AddChar (ZMod g) ℂ) {α β : Gn g b → ℂ} (h : ∀ u : Gn g b, IsUniUp (u : Mt g b) → α u = β u) :
    wh ψ α = wh ψ β := by
  unfold wh tr
  refine Finset.sum_congr rfl fun u _ => ?_
  by_cases hu : IsUniUp (u : Mt g b)
  · rw [h u hu]
  · have : (eU g b ψ).coeff u = 0 := by
      simp only [eU, eDat, MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_sum, MonoidAlgebra.coeff_single,
        Finsupp.smul_apply, Finsupp.finsetSum_apply]
      rw [Finset.sum_eq_zero, smul_zero]
      intro v hv
      rw [Finsupp.single_apply, if_neg]
      rintro rfl
      exact hu (Finset.mem_filter.1 hv).2
    rw [this, zero_mul, zero_mul]

theorem isClass_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ), i < n →
    IsMirClass F → IsClass (der ψ i F) := by
  intro g _ ψ i n F hin hF h y
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hin.le
  unfold der
  rw [Nat.add_sub_cancel_left]
  exact wh_congr ψ fun u hu => res_conj (by omega) hF h y u hu

end GlobalTheory.GLm.DerClass
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClassFunctionBernsteinZelevinskyDerivativeStatement

section

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.isClassFunction_bernsteinZelevinskyDerivative : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ), i < n → IsMirClass F → IsClass (der ψ i F) := by
  first | exact @GlobalTheory.GLm.DerClass.isClass_der | exact GlobalTheory.GLm.DerClass.isClass_der | (intros; apply GlobalTheory.GLm.DerClass.isClass_der <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionBlockDiagEqHarishChandraGelfanStatement

section

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

theorem _root_.GlobalTheory.T.mirabolicInduction_blockDiag_eq_harishChandra_gelfandGraev : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i k : ℕ) (ρ : Gn g i → ℂ), i ≤ k → IsClass ρ → ∀ h : Gn g k, indR ψ i (k + 1) ρ (diag1 h (k + 1)) = hc i (k - i) ρ (gg ψ (k - i)) k h := by
  first | exact @GlobalTheory.GLm.indR_diag1_eq_hc_gg | exact GlobalTheory.GLm.indR_diag1_eq_hc_gg | (intros; apply GlobalTheory.GLm.indR_diag1_eq_hc_gg <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicClassFunBlockDiagonalEqSumDerivatives

section

@[expose] public section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem inMir_diag1_succ {g : ℕ} [Fact g.Prime] {k : ℕ} (h : Gn g k) :
    InMir ((diag1 h (k + 1) : Gn g (k + 1)) : Mt g (k + 1)) := by
  unfold InMir diag1 toG
  intro i j hi
  split_ifs with hu
  · have hk : ¬ ((i : ℕ) < k) := by omega
    refine (congrFun (congrFun hu.unit_spec i) j).trans ?_
    simp [hk]
  · rfl

theorem mirClass_diag1_eq_sum : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (k : ℕ) (F : Gn g (k + 1) → ℂ), IsMirClass F → ∀ h : Gn g k, F (diag1 h (k + 1)) = ∑ i ∈ Finset.range (k + 1), hc i (k - i) (der ψ i F) (gg ψ (k - i)) k h := by
  intro g inst ψ hψ k F hF h
  rw [GlobalTheory.T.mirabolicConjInvariant_eq_sum_induced_derivatives g ψ hψ (k + 1) F (by omega) hF (diag1 h (k + 1)) (inMir_diag1_succ h)]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  exact GlobalTheory.T.mirabolicInduction_blockDiag_eq_harishChandra_gelfandGraev g ψ i k (der ψ i F) hik (GlobalTheory.T.isClassFunction_bernsteinZelevinskyDerivative g ψ i (k + 1) F (by omega) hF) h

end GlobalTheory.GLm
end
end
