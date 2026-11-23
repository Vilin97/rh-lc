module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemIntMat
public import Formalism.SatakeDualWeyl.StatementF
public import Formalism.LocalRingCardinality.DataHost
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyNormFinLeOne
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerProductFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.Divisibility.CoefMod
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SatakeDualWeyl.StatementE
public import Formalism.SatakeDualWeyl.StatementG
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.LocalRingCardinality.DataHost
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesDiagonalUniformizerPowStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexUniformizerPowMulIntegersEqSqPowStatement
import Mathlib.Algebra.Order.Star.Int

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalUnitaryAntidiagonalFormExponentBalance

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem diag_unitary_exp_sym {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ)
    (hU : IsUnramInv ϖ c q) (r : ℕ) (d : Fin r → ℤ) (t : GU c r)
    (ht : t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i)) :
    ∑ i, max (-d i) 0 = ∑ i, max (d i) 0 := by
  obtain ⟨_, _, hcϖ, hv, _⟩ := hU
  have hmem := t.2
  change Formalism.UG.cT c (t.1.1) * Formalism.UG.antiJ L r * t.1.1 = Formalism.UG.antiJ L r at hmem
  rw [ht] at hmem
  have hcT : Formalism.UG.cT c (Matrix.diagonal (fun i => ϖ ^ d i)) = Matrix.diagonal (fun i => ϖ ^ d i) := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp [map_zpow₀, hcϖ]
    · simp [h, Ne.symm h]
  rw [hcT] at hmem
  have hϖ : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.zero_ne_coe hv
  have key : ∀ i : Fin r, d (Fin.rev i) = -d i := by
    intro i
    have e := congrArg (fun M => M i (Fin.rev i)) hmem
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal] at e
    have hJ : Formalism.UG.antiJ L r i (Fin.rev i) = 1 := by
      simp only [Formalism.UG.antiJ, Fin.val_rev]; rw [if_pos]; omega
    rw [hJ, mul_one] at e
    rw [← zpow_add₀ hϖ] at e
    have e2 := congrArg (fun x => Valued.v x) e
    simp only [map_zpow₀, map_one, hv] at e2
    rw [← WithZero.coe_zpow, ← ofAdd_zsmul] at e2
    have e3 : (d i + d (Fin.rev i)) • (-1 : ℤ) = 0 := by
      have := WithZero.coe_injective e2
      exact Multiplicative.ofAdd.injective (this.trans ofAdd_zero.symm)
    simp at e3
    omega
  calc ∑ i, max (-d i) 0 = ∑ i, max (d (Fin.rev i)) 0 := by simp [key]
    _ = ∑ i, max (d i) 0 := Equiv.sum_comp Fin.revPerm (fun i => max (d i) 0)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalUnitaryAntidiagonalFormExponentBalanceStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.diagonal_unitary_antidiagonalForm_exponent_balance : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q → ∀ (r : ℕ) (d : Fin r → ℤ) (t : GU c r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∑ i, max (-d i) 0 = ∑ i, max (d i) 0 := by
  first | exact @GlobalTheory.diag_unitary_exp_sym | exact GlobalTheory.diag_unitary_exp_sym | (intros; apply GlobalTheory.diag_unitary_exp_sym <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesLeftMulUnitaryKUInvarian

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.InertHomIdx


open Formalism.UG in
theorem intMat_map_lmul_of_mem_range {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    {r n : ℕ} {g : GL (Fin r) L} (hg : g ∈ (Formalism.UG.bc (n := Fin r) (intL L).subtype).range) :
    (intMat L r n).map (lmul (n := n) (g : Matrix (Fin r) (Fin r) L)) = intMat L r n := by
  obtain ⟨h, rfl⟩ := hg
  have hint : ∀ (a : GL (Fin r) (intL L)) (X : Matrix (Fin r) (Fin n) L), X ∈ intMat L r n →
      lmul (n := n) ((Formalism.UG.bc (n := Fin r) (intL L).subtype a : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) X
        ∈ intMat L r n := by
    intro a X hX i j
    rw [lmul_apply, Matrix.mul_apply]
    refine Subring.sum_mem _ fun k _ => Subring.mul_mem _ ?_ (hX k j)
    exact ((a : Matrix (Fin r) (Fin r) (intL L)) i k).2
  apply le_antisymm
  · rintro _ ⟨X, hX, rfl⟩
    exact hint h X hX
  · intro X hX
    refine ⟨lmul (n := n) ((Formalism.UG.bc (n := Fin r) (intL L).subtype h⁻¹ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) X,
      hint h⁻¹ X hX, ?_⟩
    simp only [lmul_apply]
    rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem relIndex_intMat_lmul_KU {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
    (c : L →+* L) (r n : ℕ) (t k₁ k₂ : GU c r) (hk₁ : k₁ ∈ KU c r) (hk₂ : k₂ ∈ KU c r) :
    (intMat L r n).relIndex ((intMat L r n).map (lmul (k₁ * t * k₂).1.1)) =
      (intMat L r n).relIndex ((intMat L r n).map (lmul t.1.1)) := by
  have h₁ := intMat_map_lmul_of_mem_range (n := n) ((Subgroup.mem_subgroupOf.mp hk₁)).2
  have h₂ := intMat_map_lmul_of_mem_range (n := n) ((Subgroup.mem_subgroupOf.mp hk₂)).2
  have hcomp : (lmul (n := n) (k₁ * t * k₂).1.1) =
      (lmul (n := n) k₁.1.1).comp ((lmul (n := n) t.1.1).comp (lmul (n := n) k₂.1.1)) := by
    ext X : 1
    simp only [lmul_apply, AddMonoidHom.comp_apply, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  have hinj : Function.Injective (lmul (n := n) k₁.1.1) := by
    intro X Y hXY
    have := congrArg (fun Z => ((k₁.1⁻¹ : GL (Fin r) L) : Matrix (Fin r) (Fin r) L) * Z) hXY
    simpa only [lmul_apply, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mul] using this
  rw [hcomp, ← AddSubgroup.map_map, ← AddSubgroup.map_map, h₂]
  calc _ = ((intMat L r n).map (lmul (n := n) k₁.1.1)).relIndex
        (((intMat L r n).map (lmul (n := n) t.1.1)).map (lmul (n := n) k₁.1.1)) := by rw [h₁]
    _ = _ := AddSubgroup.relIndex_map_map_of_injective _ _ hinj

end GlobalTheory.InertHomIdx
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesLeftMulUnitaryKUInvarianStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.relIndex_integralMatrices_leftMul_unitary_KU_invariant : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (c : L →+* L) (r n : ℕ) (t k₁ k₂ : GU c r), k₁ ∈ KU c r → k₂ ∈ KU c r → (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (k₁ * t * k₂).1.1)) = (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul t.1.1)) := by
  first | exact @GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU | exact GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU | (intros; apply GlobalTheory.InertHomIdx.relIndex_intMat_lmul_KU <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexIntegralMatricesUnitaryDiagonalTranslate

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.LatIdx

theorem relIndex_intMat_translate : ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (c : L →+* L) (q : ℕ), IsUnramInv ϖ c q → ∀ (r n : ℕ) (d : Fin r → ℤ) (t : GU c r), t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KU c r, ∀ k₂ ∈ KU c r, (GlobalTheory.InertHomIdx.intMat L r n).relIndex ((GlobalTheory.InertHomIdx.intMat L r n).map (GlobalTheory.InertHomIdx.lmul (k₁ * t * k₂).1.1)) = (q ^ 2) ^ (n * (∑ i, max (d i) 0).toNat) := by
  intro L _ _ ϖ c q hq r n d t ht k₁ hk₁ k₂ hk₂

  have hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) :=
    hq.2.2.2.1
  have h0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hv
    exact WithZero.zero_ne_coe hv
  have h1 : Valued.v ϖ ≤ 1 := by
    rw [hv, ← WithZero.coe_one, WithZero.coe_le_coe, ← ofAdd_zero, Multiplicative.ofAdd_le]
    norm_num

  rw [GlobalTheory.T.relIndex_integralMatrices_leftMul_unitary_KU_invariant c r n t k₁ k₂ hk₁ hk₂, ht,
    GlobalTheory.T.relIndex_integralMatrices_diagonal_uniformizer_pow ϖ (q ^ 2) h0 h1 (GlobalTheory.T.relIndex_uniformizer_pow_mul_integers_eq_sq_pow ϖ c q hq) r n d,
    GlobalTheory.T.diagonal_unitary_antidiagonalForm_exponent_balance ϖ c q hq r d t ht]

end GlobalTheory.LatIdx
end
end
end
