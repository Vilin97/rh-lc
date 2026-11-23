module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph
public import ReciprocityTheory.DualLattices.FischerAdjointStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.DualLattices.FischerAdjointStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockGraph
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffRenameCayleyBlockSymbolEmbeddiStatement
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyOperatorPowEqSignedSumPartialDerivs

section

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

set_option autoImplicit false

namespace GlobalTheory.CayleyBlock

theorem dList_append' {σ : Type} [DecidableEq σ] (l₁ l₂ : List σ) :
    dList (l₁ ++ l₂) = dList l₁ * dList l₂ := by
  simp [dList, List.map_append, List.prod_append]

theorem smallList_cons' {p q : ℕ} (σ : Equiv.Perm (Fin p)) (τ : Fin q → Equiv.Perm (Fin p)) :
    smallList (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) =
      (List.finRange p).map (fun j => (σ j, j)) ++ smallList τ := by
  simp [smallList, List.finRange_succ, List.flatMap_cons, List.flatMap_map]

theorem sgnProd_cons' {p q : ℕ} (σ : Equiv.Perm (Fin p)) (τ : Fin q → Equiv.Perm (Fin p)) :
    sgnProd (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) =
      (Equiv.Perm.sign σ : ℤ) * sgnProd τ := by
  simp [sgnProd, Fin.prod_univ_succ]

theorem cayMono_eq_dList' {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    cayMono p ℂ σ = dList ((List.finRange p).map fun j => (σ j, j)) := by
  simp [cayMono, dList, List.map_map]
  rfl

theorem cayOp_pow_eq_sum (p q : ℕ) :
    cayOp p ℂ ^ q = ∑ τ : Fin q → Equiv.Perm (Fin p), sgnProd τ • dList (smallList τ) := by
  induction q with
  | zero => simp [smallList, sgnProd, dList]
  | succ q ih =>
    rw [pow_succ', ih, cayOp, Finset.sum_mul_sum,
      ← (Fin.consEquiv (fun _ => Equiv.Perm (Fin p))).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun τ _ => ?_
    change _ = sgnProd (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)) •
      dList (smallList (Fin.cons σ τ : Fin (q + 1) → Equiv.Perm (Fin p)))
    rw [smallList_cons', sgnProd_cons', dList_append', cayMono_eq_dList', smul_mul_smul, mul_smul]

end GlobalTheory.CayleyBlock
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CayleyOperatorPowEqSignedSumPartialDerivsStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

theorem _root_.GlobalTheory.T.cayleyOperator_pow_eq_signed_sum_partialDerivs : ∀ (p q : ℕ), cayOp p ℂ ^ q = ∑ τ : Fin q → Equiv.Perm (Fin p), sgnProd τ • dList (smallList τ) := by
  first | exact @GlobalTheory.CayleyBlock.cayOp_pow_eq_sum | exact GlobalTheory.CayleyBlock.cayOp_pow_eq_sum | (intros; apply GlobalTheory.CayleyBlock.cayOp_pow_eq_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffComposedPartialDerivListOfNodup

section

@[expose] public section

set_option autoImplicit false

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory.CayleyBlock

theorem coeff_dList_of_nodup {σ : Type} [DecidableEq σ] (l : List σ) (hl : l.Nodup) (m : σ →₀ ℕ)
    (hm : ∀ v ∈ l, m v = 0) (G : MvPolynomial σ ℂ) :
    AddMonoidAlgebra.coeff (dList l G) m = AddMonoidAlgebra.coeff G (m + (l.map fun v => Finsupp.single v 1).sum) := by
  induction l generalizing m with
  | nil => simp [dList]
  | cons v l ih =>
    have hc : dList (v :: l) G = pderiv v (dList l G) := by
      simp [dList]
    rw [List.nodup_cons] at hl
    have h0 : m v = 0 := hm v (List.mem_cons_self ..)
    have h1 : ∀ w ∈ l, (m + Finsupp.single v 1 : σ →₀ ℕ) w = 0 := by
      intro w hw
      have hne : w ≠ v := fun h => hl.1 (h ▸ hw)
      rw [Finsupp.add_apply, hm w (List.mem_cons_of_mem _ hw), Finsupp.single_eq_of_ne hne, add_zero]
    rw [hc, MvPolynomial.coeff_pderiv, ih hl.2 _ h1, h0, List.map_cons, List.sum_cons, add_assoc]
    simp

end GlobalTheory.CayleyBlock
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffComposedPartialDerivListOfNodupStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

theorem _root_.GlobalTheory.T.coeff_composedPartialDerivList_of_nodup : ∀ {σ : Type} [DecidableEq σ] (l : List σ), l.Nodup → ∀ (m : σ →₀ ℕ), (∀ v ∈ l, m v = 0) → ∀ (G : MvPolynomial σ ℂ), AddMonoidAlgebra.coeff (dList l G) m = AddMonoidAlgebra.coeff G (m + (l.map fun v => Finsupp.single v 1).sum) := by
  first | exact @GlobalTheory.CayleyBlock.coeff_dList_of_nodup | exact GlobalTheory.CayleyBlock.coeff_dList_of_nodup | (intros; apply GlobalTheory.CayleyBlock.coeff_dList_of_nodup <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantCoeffCayleyOperatorPowDeterminantPow

section

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

namespace GlobalTheory

theorem cayOp_pow_cayDet_pow (p s k : ℕ) :
    (cayOp p ℂ ^ k) (cayDet p ℂ ^ (s + k)) =
      (∏ t ∈ Finset.range k, ∏ j ∈ Finset.range p, (s + 1 + t + j)) • cayDet p ℂ ^ s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ← add_assoc, cayley p ℂ (s + k + 1), Nat.add_sub_cancel,
      map_nsmul, ih, smul_smul, Finset.prod_range_succ]
    congr 1
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    ring

theorem prod_succ_mul_factorial (j q : ℕ) :
    (∏ t ∈ Finset.range q, (1 + t + j)) * j.factorial = (q + j).factorial := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.prod_range_succ, mul_right_comm, ih, show q + 1 + j = (q + j) + 1 by ring,
      Nat.factorial_succ]
    ring

theorem constantCoeff_cayOp_pow_cayDet_pow : ∀ (p q : ℕ),
    constantCoeff ((cayOp p ℂ ^ q) (cayDet p ℂ ^ q)) =
      ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  intro p q
  have h := cayOp_pow_cayDet_pow p 0 q
  rw [zero_add] at h
  rw [h, pow_zero, map_nsmul, map_one, nsmul_eq_mul, mul_one, Finset.prod_comm]
  push_cast
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [eq_div_iff (by exact_mod_cast (Nat.factorial_pos j).ne')]
  have := prod_succ_mul_factorial j q
  simp only [zero_add] at *
  exact_mod_cast this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConstantCoeffCayleyOperatorPowDeterminantPowStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.PGsh GlobalTheory.CayleyBlock

theorem _root_.GlobalTheory.T.constantCoeff_cayleyOperator_pow_determinant_pow : ∀ (p q : ℕ), constantCoeff ((cayOp p ℂ ^ q) (cayDet p ℂ ^ q)) = ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  first | exact @GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow | exact GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow | (intros; apply GlobalTheory.constantCoeff_cayOp_pow_cayDet_pow <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffBlockSymbolDetPowCayley

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.PGsh

namespace GlobalTheory.CayleyBlock

theorem det_pow_eq {p q : ℕ} (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q) :
    (GlobalTheory.DomainDens.blockSym h1 ()).det ^ q = rename (blockEmb h1) (sumMap p q (cayDet p ℂ ^ q)) := by
  rw [map_pow, map_pow, cayDet, AlgHom.map_det, AlgHom.map_det]
  congr 2
  ext i j
  simp [GlobalTheory.DomainDens.blockSym_apply, sumMap, blockEmb, Matrix.mvPolynomialX]

theorem bigList_nodup {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : (bigList τ).Nodup := by
  rw [bigList, List.nodup_flatMap]
  refine ⟨fun b _ => (List.nodup_finRange p).map fun j k h => by simpa using congrArg (fun x => x.2.2) h, ?_⟩
  refine (List.nodup_finRange q).imp fun {a b} hab => ?_
  show List.Disjoint _ _
  rw [List.disjoint_left]
  intro x hx hy
  simp only [List.mem_map, List.mem_finRange, true_and] at hx hy
  obtain ⟨j, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hy
  exact hab (congrArg Prod.fst hk).symm

theorem bigList_sum {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) :
    ((bigList τ).map fun v => Finsupp.single v 1).sum = blockGraph τ := by
  simp [bigList, blockGraph, List.map_flatMap, Fin.sum_univ_def, List.map_map, Function.comp_def]
  simp [List.flatMap, List.sum_flatten, List.map_map, Function.comp_def]

theorem pderiv_sumMap {p q : ℕ} (v : Fin q × Fin p × Fin p) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    pderiv v (sumMap p q P) = sumMap p q (pderiv v.2 P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sumMap]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | mul_X f w hf =>
    simp only [map_mul, Derivation.leibniz, hf, smul_eq_mul, map_add (f := _)]
    congr 1
    simp [sumMap, pderiv_X, Pi.single_apply, Prod.ext_iff]
    by_cases h : w.1 = v.2.1 ∧ w.2 = v.2.2 <;> simp [h, Finset.filter_eq']

theorem dList_sumMap {p q : ℕ} (l : List (Fin q × Fin p × Fin p)) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    dList l (sumMap p q P) = sumMap p q (dList (l.map fun v => v.2) P) := by
  induction l with
  | nil => simp [dList]
  | cons v l ih =>
    simp only [dList, List.map_cons, List.prod_cons, Module.End.mul_apply] at ih ⊢
    rw [ih]
    exact pderiv_sumMap v _

theorem bigList_map {p q : ℕ} (τ : Fin q → Equiv.Perm (Fin p)) : (bigList τ).map (fun v => v.2) = smallList τ := by
  simp [bigList, smallList, List.map_flatMap, List.map_map, Function.comp_def]

theorem constantCoeff_sumMap (p q : ℕ) (P : MvPolynomial (Fin p × Fin p) ℂ) :
    constantCoeff (sumMap p q P) = constantCoeff P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [sumMap]
  | add f g hf hg => simp only [map_add (f := _), hf, hg]
  | mul_X f w hf => simp [sumMap, constantCoeff_X]

end GlobalTheory.CayleyBlock


open GlobalTheory.CayleyBlock ReciprocityTheory.PGsh MvPolynomial in
theorem GlobalTheory.topCoeff_blockSym_det_pow : ∀ (p q : ℕ) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q),
    GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) =
      ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  intro p q h1
  rw [det_pow_eq, GlobalTheory.T.topDegreeFormCoeff_rename_cayleyBlockSymbolEmbedding, ← GlobalTheory.T.constantCoeff_cayleyOperator_pow_determinant_pow, GlobalTheory.T.cayleyOperator_pow_eq_signed_sum_partialDerivs, LinearMap.sum_apply]
  have key : ∀ τ : Fin q → Equiv.Perm (Fin p), (sgnProd τ : ℂ) * AddMonoidAlgebra.coeff (sumMap p q (cayDet p ℂ ^ q)) (blockGraph τ) =
      constantCoeff (sgnProd τ • dList (smallList τ) (cayDet p ℂ ^ q)) := by
    intro τ
    rw [← bigList_sum, ← zero_add ((bigList τ).map _).sum, ← GlobalTheory.T.coeff_composedPartialDerivList_of_nodup _ (bigList_nodup τ) 0 (fun _ _ => rfl),
      dList_sumMap, bigList_map, ← constantCoeff_sumMap p q, map_zsmul, zsmul_eq_mul,
      ← map_intCast (C : ℂ →+* MvPolynomial (Fin q × Fin p × Fin p) ℂ), map_mul, constantCoeff_C, constantCoeff_eq]

  simp_rw [LinearMap.smul_apply, key, map_sum]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffBlockSymbolDetPowCayleyStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.topDegreeFormCoeff_blockSymbolDet_pow_cayley : ∀ (p q : ℕ) (h1 : Fintype.card (Unit × Fin p × Fin q) = p * q), GlobalTheory.GoodMetric.topCoeff ((GlobalTheory.DomainDens.blockSym h1 ()).det ^ q) = ∏ i ∈ Finset.range p, (((q + i).factorial : ℂ) / i.factorial) := by
  first | exact @GlobalTheory.topCoeff_blockSym_det_pow | exact GlobalTheory.topCoeff_blockSym_det_pow | (intros; apply GlobalTheory.topCoeff_blockSym_det_pow <;> assumption)
end
end
