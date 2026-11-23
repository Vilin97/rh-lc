module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumMulGaussSumInvOfIsPrimitive
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.GaussSum
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
public import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumMulGaussSumInvPrim

section

@[expose] public section

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

theorem gaussSum_mul_gaussSum_inv_prim {K : Type} [Field K] {n : ℕ} [NeZero n]
    {χ : DirichletCharacter K n} {e : AddChar (ZMod n) K} (hχ : χ.IsPrimitive)
    (he : e.IsPrimitive) : gaussSum χ e * gaussSum χ⁻¹ e⁻¹ = (n : K) := by
  apply GlobalTheory.GaussInt.gaussSum_mul_gaussSum_inv_of_isPrimitive <;> assumption

end GlobalTheory.KummerEisensteinGalois
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumModPrimePowerMulInvEqPrimePow

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

noncomputable section

namespace GlobalTheory.KZ.Cmp

theorem sum_mulChar_eq_sum_units {K : Type} [CommRing K] {n : ℕ} (ψ : MulChar (ZMod n) K)
    (f : ZMod n → K) [Fintype (ZMod n)] :
    ∑ a : ZMod n, ψ a * f a = ∑ b : (ZMod n)ˣ, ψ b * f b := by
  classical
  rw [← Finset.sum_filter_of_ne (p := IsUnit) (fun a _ h => by
    by_contra hu; exact h (by rw [MulChar.map_nonunit ψ hu, zero_mul]))]
  refine (Finset.sum_nbij' (fun b : (ZMod n)ˣ => (b : ZMod n)) (fun a => if h : IsUnit a then h.unit else 1)
    ?_ ?_ ?_ ?_ ?_).symm
  · intro b _; simp
  · intro a _; simp
  · intro b _; simp
  · intro a ha
    have hu : IsUnit a := (Finset.mem_filter.1 ha).2
    simp [hu]
  · intro b _; rfl

theorem gSum_mul_gSum_inv_prim : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l)
    (ψ : DirichletCharacter (Qbar l) (l ^ m)), IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive →
    gSum m z ψ * gSum m z⁻¹ ψ⁻¹ = (l : Qbar l) ^ m := by
  intro l _ m z ψ hz hψ
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let e : AddChar (ZMod (l ^ m)) (Qbar l) := AddChar.zmodChar (l ^ m) hz.pow_eq_one
  have he : e.IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root (l ^ m) hz
  have h1 : gSum m z ψ = gaussSum ψ e := by
    unfold gSum gaussSum
    rw [sum_mulChar_eq_sum_units]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.zmodChar_apply]
  have h2 : gSum m z⁻¹ ψ⁻¹ = gaussSum ψ⁻¹ e⁻¹ := by
    unfold gSum gaussSum
    rw [sum_mulChar_eq_sum_units]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [AddChar.inv_apply', AddChar.zmodChar_apply, inv_pow]
  rw [h1, h2, GlobalTheory.KummerEisensteinGalois.gaussSum_mul_gaussSum_inv_prim hψ he]
  push_cast
  rfl

end GlobalTheory.KZ.Cmp
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaussSumModPrimePowerMulInvEqPrimePowStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

theorem _root_.GlobalTheory.T.gaussSumModPrimePower_mul_inv_eq_prime_pow : ∀ (l : ℕ) [Fact l.Prime] (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → gSum m z ψ * gSum m z⁻¹ ψ⁻¹ = (l : Qbar l) ^ m := by
  first | exact @GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim | exact GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim | (intros; apply GlobalTheory.KZ.Cmp.gSum_mul_gSum_inv_prim; all_goals assumption)
end
end
