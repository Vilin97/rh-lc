module

public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousGaloisRepRankTwoTateDualOfOrdinaryNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivisibleOrdinarySelmerChainExistsIntegralRepresStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleLocalConditionsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDivisibleChainPrimaryTorsionGroupStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowMulMemAdd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteLTorsionSelmerRankTwoAdjoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQ
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCommutatorDetNonzeroStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualMatrixMemCoefRingOfNorma
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonzeroOrdinaryClassOfCompatibleCocyclesModPowStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousGaloisRepRankTwoTateDualOfOrdinaryNormStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix


theorem _root_.GlobalTheory.T.continuous_galoisRepRankTwoTateDual_of_ordinaryNormalForm : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → Continuous (dual1 W) := by
  first | exact @GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual | exact GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual | (intros; apply GlobalTheory.Ord2.DualCont.continuous_galoisRepRankTwoTateDual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteLTorsionSelmerRankTwoAdjointStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix


theorem _root_.GlobalTheory.T.finite_lTorsion_selmer_rank_two_adjoint : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), ContainsAbove S l → Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1) → Finite {x : DivSel c W S A // l • x = 0} := by
  first | exact @GlobalTheory.Ord2.finite_lTorsion_divSel | exact GlobalTheory.Ord2.finite_lTorsion_divSel | (intros; apply GlobalTheory.Ord2.finite_lTorsion_divSel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualEqOneOfMemKerUnramifiedQStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix


theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramifiedQuotient : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ a ∈ (toGS Ω (S : Set Pl)).ker, dual1 W a = 1 := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramified <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualExistsNoEigenvalueOne

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ g, (mat (dual1 W) g - 1).det ≠ 0 := by
  intro l _ Ω _ _ _ e S A W h
  obtain ⟨φ, hφ, hd⟩ := GlobalTheory.T.exists_commutator_det_nonzero l Ω e S A W h
  have hφ' : φ ∈ H0g W := (Subgroup.commutator_le.2 (fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))) hφ
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hφ'
  rw [MonoidHom.mem_ker] at h1 h2
  have hχ : (cycBar ℚ Ω l * (dt W)⁻¹) φ = 1 := by
    simp [h1, h2]
  refine ⟨φ, ?_⟩
  have : mat (dual1 W) φ = mat W φ := by
    unfold dual1
    generalize (cycBar ℚ Ω l * (dt W)⁻¹) = χ at hχ
    simp [mat, tw, hχ]
  rw [this]; exact hd

end GlobalTheory.Ord2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualExistsNoEigenvalueOneStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix


theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_exists_no_eigenvalue_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ g, (mat (dual1 W) g - 1).det ≠ 0 := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualMatrixMemCoefRingOfNormaStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix


theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualUpperTriangularDecomposi

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_upperTriangular_decompGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 1 0 = 0 := by
  intro l _ Ω _ _ _ e S A W hW s hs
  have h := hW.upper s hs
  simp only [mat, dual1, tw_val, Matrix.smul_apply, smul_eq_mul] at h ⊢
  rw [h, mul_zero]

end GlobalTheory.Ord2
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualUpperTriangularDecomposiStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix


theorem _root_.GlobalTheory.T.galoisRepRankTwoTateDual_upperTriangular_decompositionGroup : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ s ∈ Dec (F := ℚ) A, mat (dual1 W) s 1 0 = 0 := by
  first | exact @GlobalTheory.Ord2.galoisRepRankTwoTateDual_upperTriangular_decompGroup | exact GlobalTheory.Ord2.galoisRepRankTwoTateDual_upperTriangular_decompGroup | (intros; apply GlobalTheory.Ord2.galoisRepRankTwoTateDual_upperTriangular_decompGroup <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerUnboundedOrderNonzeroOrdinaryClass

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem gw_limit : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ¬ GrZero (dual1 W) A := by
  intro hL l _ Ω _ _ _ e S A W hW c hc H hGr
  have h1 := GlobalTheory.T.continuous_galoisRepRankTwoTateDual_of_ordinaryNormalForm l Ω e S A W hW
  have h2 := GlobalTheory.T.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm_alt l Ω e S A W hW c hc
  have h3 := GlobalTheory.T.galoisRepRankTwoTateDual_exists_no_eigenvalue_one l Ω e S A W hW
  have h4 := GlobalTheory.T.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramifiedQuotient l Ω e S A W hW
  have h5 := GlobalTheory.T.galoisRepRankTwoTateDual_upperTriangular_decompositionGroup l Ω e S A W hW
  have hunb := GlobalTheory.T.exists_cocycle_local_conditions l Ω S A (dual1 W) c h2 h3 H
  have hfin := GlobalTheory.T.finite_lTorsion_selmer_rank_two_adjoint hL l Ω S A (dual1 W) c hW.above h1 h2 h4
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.exists_divisible_chain_primary_torsion_group l (DivSel c (dual1 W) S A) (divSel_torsion c (dual1 W) S A) hfin hunb
  obtain ⟨a, N, p1, p2, p3, p4, p5, p6, p7, p8⟩ := GlobalTheory.T.divisibleOrdinarySelmerChain_exists_integral_representatives l Ω S A (dual1 W) c h1 h2 h4 h5 x hx0 hx
  exact GlobalTheory.T.nonzero_ordinary_class_of_compatible_cocycles_mod_pow l Ω S A (dual1 W) c h1 h2 h3 a N p1 p2 p3 p4 p5 p6 p7 p8 hGr

end GlobalTheory.Ord2

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerUnboundedOrderNonzeroOrdinaryClassStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

theorem _root_.GlobalTheory.T.dualSelmer_unbounded_order_nonzero_ordinaryClass : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ¬ GrZero (dual1 W) A := by
  first | exact @GlobalTheory.Ord2.gw_limit | exact GlobalTheory.Ord2.gw_limit | (intros; apply GlobalTheory.Ord2.gw_limit <;> assumption)
end
end
