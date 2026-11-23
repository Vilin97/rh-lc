module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumEqMassMulOrbitalIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsWeightEqFinrankMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceVectorValuedEqFiniteKernelSumStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWsp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelSumEqFinsumRegularRationalClassesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceDualWeylModuleInvRationalPointEqConjCharAtStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.trace_dualWeylModule_inv_rationalPoint_eq_conj_charAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : DomWeight n) (γ : UE E n) (v : InfinitePlace E), LinearMap.trace ℂ _ (GlobalTheory.Branching.sqRep ℂ n lam (GeneralLinearGroup.map v.embedding (γ⁻¹).1)) = starRingEnd ℂ (chAt lam (γ.1.val.charpoly.map v.embedding)) := by
  first | exact @GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt | exact GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt | (intros; apply GlobalTheory.ContraChar.trace_sqRep_inv_eq_conj_chAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsEqDimMulKernelSum

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_forms_hop_eq_kernSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = dimW lam * kernSum S lam K' f := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf
  rw [GlobalTheory.T.heckeTrace_forms_weight_eq_finrank_mul E hU n hn S hS lam K' hK f hf, GlobalTheory.T.heckeTrace_vectorValued_eq_finite_kernelSum E hU n hn S hS lam K' hK f hf, TrKer.finrank_wsp]
  unfold kernSum
  congr 2
  refine finsum_congr fun q => ?_
  congr 1
  refine finsum_congr fun γ => ?_
  congr 1
  unfold TrKer.wAt chW
  rw [TrKer.trace_piMap]
  exact Finset.prod_congr rfl fun v _ => GlobalTheory.T.trace_dualWeylModule_inv_rationalPoint_eq_conj_charAt E n (lam v) γ v

end GlobalTheory.BCT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceFormsEqDimMulKernelSumStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.heckeTrace_forms_eq_dim_mul_kernelSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → trOn (forms S lam K') (hop S K' f) = dimW lam * kernSum S lam K' f := by
  first | exact @GlobalTheory.BCT.trOn_forms_hop_eq_kernSum | exact GlobalTheory.BCT.trOn_forms_hop_eq_kernSum | (intros; apply GlobalTheory.BCT.trOn_forms_hop_eq_kernSum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceWeightFormsEqDimMulRationalClasses

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_forms_hop_eq_geom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → trOn (forms S lam K') (hop S K' f) = dimW lam * geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) := by
  intro E _ _ _ hU n hn S hS lam K' hK f hf hreg
  rw [GlobalTheory.T.heckeTrace_forms_eq_dim_mul_kernelSum E hU n hn S hS lam K' hK f hf, GlobalTheory.T.kernelSum_eq_finsum_regular_rationalClasses E hU n hn S hS lam K' hK f hf hreg]
  congr 1
  unfold geomURat
  refine finsum_congr fun c => ?_
  split_ifs with h
  · rw [GlobalTheory.T.classSum_eq_mass_mul_orbitalIntegral E hU n hn S hS lam K' hK f hf c.rep h]; ring
  · rfl

end GlobalTheory.BCT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTraceWeightFormsEqDimMulRationalClassesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.heckeTrace_weightForms_eq_dim_mul_rationalClasses : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) → trOn (forms S lam K') (hop S K' f) = dimW lam * geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) := by
  first | exact @GlobalTheory.BCT.trOn_forms_hop_eq_geom | exact GlobalTheory.BCT.trOn_forms_hop_eq_geom | (intros; apply GlobalTheory.BCT.trOn_forms_hop_eq_geom <;> assumption)
end
end
