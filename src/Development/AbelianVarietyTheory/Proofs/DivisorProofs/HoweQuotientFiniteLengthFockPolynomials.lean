module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionsLieRationalWeightsCommuteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantKernelStableAndAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantsHighestWeightCyclicMultiplicityOne
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirFockAct1SubCasimirFockAct2
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantsHighestWeightCyclicMultiplicityOStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.fockCoinvariants_highestWeightCyclic_multiplicityOne : ∀ (P Q R S : ℕ) (x : ℂ), CycMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  first | exact @GlobalTheory.HoweR.coinv_cycMod | exact GlobalTheory.HoweR.coinv_cycMod | (intros; apply GlobalTheory.HoweR.coinv_cycMod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariants

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.SecondQuad

section Ring

variable {A : Type} [Ring A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (u l : I × J → A)

theorem left_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) =
      ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  have h1 : ∀ d a b, u (a, c) * l (a, d) * (u (b, d) * l (b, e)) =
      u (a, c) * u (b, d) * (l (a, d) * l (b, e)) + if a = b then u (a, c) * l (a, e) else 0 := by
    intro d a b
    have h := hlu (a, d) (b, d)
    simp only [Prod.mk.injEq, and_true] at h
    have : u (a, c) * l (a, d) * (u (b, d) * l (b, e)) = u (a, c) * (l (a, d) * u (b, d)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hab : a = b
    · subst hab; simp [mul_add, add_mul, mul_assoc]
    · simp [hab, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul_sum, h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem right_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) +
        Fintype.card I • ∑ b, u (b, c) * l (b, e) := by
  have h1 : ∀ a b d, u (b, d) * l (a, d) * (u (a, c) * l (b, e)) =
      u (b, d) * u (a, c) * (l (a, d) * l (b, e)) + if d = c then u (b, c) * l (b, e) else 0 := by
    intro a b d
    have h := hlu (a, d) (a, c)
    simp only [Prod.mk.injEq, true_and] at h
    have : u (b, d) * l (a, d) * (u (a, c) * l (b, e)) = u (b, d) * (l (a, d) * u (a, c)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hdc : d = c
    · subst hdc; simp [mul_add, add_mul, mul_assoc]
    · simp [hdc, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul, h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem key (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0)
    (huu : ∀ i j, u i * u j = u j * u i) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) + Fintype.card I • ∑ a, u (a, c) * l (a, e) =
      ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  rw [left_expand u l hlu, right_expand u l hlu]
  have hT : ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by rw [huu]
  rw [hT]
  abel

end Ring

variable {P Q R S : ℕ}

theorem raiB_comm (l m : Ln P Q R S) : raiB l * raiB m = raiB m * raiB l := by
  by_cases hlm : l = m
  · rw [hlm]
  refine LinearMap.ext fun f => ?_
  cases hl : linePos l <;> cases hm : linePos m <;>
    simp [raiB, hl, hm, MvPolynomial.pderiv_X, Pi.single_apply, hlm, Ne.symm hlm,
      GlobalTheory.FockCasimir.pderiv_pderiv_comm l m, mul_left_comm]

theorem fockSecondAction_matrixUnit_eq (c d : Ix R S) :
    fockAct2 P Q R S (Eab c d) = ∑ a, raiB (a, c) * lowB (a, d) +
      if c = d then ((Fintype.card (Ix P Q) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct2_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, true_and]
  by_cases hcd : c = d
  · simp [hcd, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hcd]

theorem fockFirstAction_matrixUnit_eq (b a : Ix P Q) :
    fockAct1 P Q R S (Eab b a) = ∑ d, raiB (b, d) * lowB (a, d) +
      if b = a then ((Fintype.card (Ix R S) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct1_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, and_true]
  by_cases hba : b = a
  · simp [hba, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hba]

theorem trace_Eab (b a : Ix P Q) : (Eab b a).trace = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h; simp [Eab, Matrix.trace, Matrix.single_apply]
  · simp [Eab, Matrix.trace, Matrix.single_apply, h]

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem sq_shift (X : J → J → A) (k : ℂ) (c e : J) :
    ∑ d, (X c d + if c = d then k • (1 : A) else 0) * (X d e + if d = e then k • (1 : A) else 0) =
      ∑ d, X c d * X d e + (2 * k) • X c e + if c = e then (k * k) • (1 : A) else 0 := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero,
    smul_mul_assoc, one_mul, mul_smul_comm, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, smul_smul]
  by_cases hce : c = e
  · subst hce; simp only [if_true]; module
  · simp only [hce, if_false]; module

theorem rhs_shift (E : I → I → A) (Y : I → I → A) (m x : ℂ) :
    ∑ a, ∑ b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      ∑ a, ∑ b, E b a * Y a b + (m - x) • ∑ a, Y a a := by
  have : ∀ a b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      E b a * Y a b + if b = a then (m - x) • Y a b else 0 := by
    intro a b
    by_cases h : b = a
    · simp only [h, if_true, mul_one, sub_mul, add_mul, smul_mul_assoc, one_mul, sub_smul]; abel
    · simp [h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.smul_sum]

end Alg

variable {P Q R S : ℕ}

theorem qop_eq (x : ℂ) (c e : Ix R S) :
    qop (units (fockAct2 P Q R S)) (x + (Fintype.card (Ix R S) : ℂ) / 2)
        ((Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2)) c e =
      ∑ a, ∑ b, (fockAct1 P Q R S (Eab b a) - (x * (Eab b a).trace) • (1 : Module.End ℂ (Pol P Q R S))) *
        (raiB (a, c) * lowB (b, e)) := by
  have hk := key (fun i : Ln P Q R S => raiB i) (fun i => lowB i) GlobalTheory.FockCasimir.lowB_mul_raiB raiB_comm c e
  simp only [← Nat.cast_smul_eq_nsmul ℂ] at hk
  simp only [qop, units, fockSecondAction_matrixUnit_eq, fockFirstAction_matrixUnit_eq, trace_Eab]
  have hs := sq_shift (A := Module.End ℂ (Pol P Q R S)) (fun c d => ∑ a, raiB (a, c) * lowB (a, d))
    ((Fintype.card (Ix P Q) : ℂ) / 2) c e
  have hr := rhs_shift (A := Module.End ℂ (Pol P Q R S)) (fun b a => ∑ d, raiB (b, d) * lowB (a, d))
    (fun a b => raiB (a, c) * lowB (b, e)) ((Fintype.card (Ix R S) : ℂ) / 2) x
  rw [hs, hr]
  by_cases hce : c = e
  · subst hce; simp only [if_true]
    linear_combination (norm := module) hk
  · simp only [hce, if_false]
    linear_combination (norm := module) hk

theorem qop_mem_coinv (P Q R S : ℕ) (x : ℂ) :
    ∃ α β : ℂ, ∀ a b f, qop (units (fockAct2 P Q R S)) α β a b f ∈ coinv P Q R S x := by
  refine ⟨x + (Fintype.card (Ix R S) : ℂ) / 2,
    (Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2),
    fun c e f => ?_⟩
  rw [qop_eq x c e, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  refine Submodule.subset_span ⟨Eab b a, (raiB (a, c) * lowB (b, e)) f, ?_⟩
  simp [Module.End.mul_apply, LinearMap.sub_apply]

end GlobalTheory.HoweR.SecondQuad

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariantsStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.fockSecondAction_quadraticIdentity_mod_coinvariants : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f, qop (units (fockAct2 P Q R S)) α β a b f ∈ coinv P Q R S x := by
  first | exact @GlobalTheory.HoweR.SecondQuad.qop_mem_coinv | exact GlobalTheory.HoweR.SecondQuad.qop_mem_coinv | (intros; apply GlobalTheory.HoweR.SecondQuad.qop_mem_coinv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvari

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.QuadT

section Abstract

variable {A ι κ : Type} [Ring A] [Algebra ℂ A] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  (u l : ι → κ → A)

theorem core_term (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c) (a b : ι) (i j k : κ) :
    u a k * l a i * (u b j * l b k) =
      u a k * l b k * (l a i * u b j) - if k = j then u a k * l a i else 0 := by
  have e1 : u b j * l b k = l b k * u b j - if k = j then 1 else 0 := by
    rw [h b k j]; abel
  have e2 : u a k * l a i * (l b k * u b j) = u a k * l b k * (l a i * u b j) := by
    calc _ = u a k * (l a i * l b k) * u b j := by simp only [mul_assoc]
      _ = u a k * (l b k * l a i) * u b j := by rw [hll]
      _ = _ := by simp only [mul_assoc]
  rw [e1, mul_sub, e2]
  split_ifs <;> simp

theorem core1 (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c) (i j : κ) :
    ∑ k, (∑ a, u a k * l a i) * (∑ b, u b j * l b k) =
      (∑ a, ∑ b, (∑ k, u a k * l b k) * (l a i * u b j)) -
        (Fintype.card ι : ℂ) • ∑ a, u a j * l a i := by
  simp only [Finset.sum_mul, Finset.mul_sum, core_term u l h hll, Finset.sum_sub_distrib]
  congr 1
  · calc (∑ k, ∑ b, ∑ a, u a k * l b k * (l a i * u b j))
          = ∑ b, ∑ k, ∑ a, u a k * l b k * (l a i * u b j) := Finset.sum_comm
        _ = ∑ b, ∑ a, ∑ k, u a k * l b k * (l a i * u b j) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := Finset.sum_comm
  · rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp)]
    simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, Finset.smul_sum]

theorem core2 (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0) (i j : κ) :
    ∑ a, l a i * u a j = ∑ a, u a j * l a i + if i = j then (Fintype.card ι : ℂ) • (1 : A) else 0 := by
  simp only [h, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

end Abstract

end GlobalTheory.HoweR.QuadT

namespace GlobalTheory.HoweR.QuadT

section Main

variable {V ι κ : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ] (u l : ι → κ → Module.End ℂ V) (E : ι → ι → Module.End ℂ V) (G : κ → κ → Module.End ℂ V)

theorem quad_main (h : ∀ b c e, l b c * u b e = u b e * l b c + if c = e then 1 else 0)
    (hll : ∀ a c b e, l a c * l b e = l b e * l a c)
    (hE : ∀ a b, E a b = ∑ c, u a c * l b c + (if a = b then (Fintype.card κ : ℂ) / 2 else 0) • 1)
    (hG : ∀ c d, G c d = ∑ a, u a c * l a d + (if c = d then (Fintype.card ι : ℂ) / 2 else 0) • 1)
    (x : ℂ) (i j : κ) :
    qop (fun c d => -G d c) ((Fintype.card κ : ℂ) / 2 - x)
        ((Fintype.card ι : ℂ) ^ 2 / 4 + (x - (Fintype.card κ : ℂ) / 2) * (Fintype.card ι : ℂ) / 2) i j =
      ∑ a, ∑ b, (E a b - (if a = b then x else 0) • 1) * (l a i * u b j) := by
  have hR : ∀ a b, (E a b - (if a = b then x else 0) • 1) * (l a i * u b j) =
      (∑ c, u a c * l b c) * (l a i * u b j) +
        (if a = b then (Fintype.card κ : ℂ) / 2 - x else 0) • (l a i * u b j) := by
    intro a b
    rw [hE]
    split_ifs <;> simp [add_mul, sub_mul, sub_smul, smul_mul_assoc, add_sub_assoc]
  simp only [hR, Finset.sum_add_distrib]
  have hD : ∑ a, ∑ b, (if a = b then (Fintype.card κ : ℂ) / 2 - x else 0) • (l a i * u b j) =
      ((Fintype.card κ : ℂ) / 2 - x) • ∑ a, l a i * u a j := by
    simp [ite_smul, Finset.sum_ite_eq, Finset.smul_sum]
  have h1 := core1 u l h hll i j
  rw [eq_sub_iff_add_eq] at h1
  rw [hD, core2 u l h, ← h1]
  simp only [qop, hG]
  simp only [neg_mul_neg, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
    smul_smul, Finset.sum_add_distrib, ite_smul, zero_smul, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    module
  · simp only [hij, Ne.symm hij, if_false]
    module

end Main

end GlobalTheory.HoweR.QuadT

namespace GlobalTheory.HoweR.QuadT

theorem fockAct1_Eab_eq {P Q R S : ℕ} (a b : Ix P Q) :
    fockAct1 P Q R S (Eab a b) =
      ∑ c, raiB (a, c) * lowB (b, c) + (if a = b then (Fintype.card (Ix R S) : ℂ) / 2 else 0) • 1 := by
  rw [fockAct1_Eab]
  simp only [omE, Prod.mk.injEq, and_true, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv]

theorem fockAct2_Eab_eq {P Q R S : ℕ} (c d : Ix R S) :
    fockAct2 P Q R S (Eab c d) =
      ∑ a, raiB (a, c) * lowB (a, d) + (if c = d then (Fintype.card (Ix P Q) : ℂ) / 2 else 0) • 1 := by
  rw [fockAct2_Eab]
  simp only [omE, Prod.mk.injEq, true_and, Finset.sum_add_distrib]
  congr 1
  split_ifs <;> simp [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv]

theorem negT_fockAct2_quad : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f,
    qop (negT (units (fockAct2 P Q R S))) α β a b f ∈ coinv P Q R S x := by
  intro P Q R S x
  refine ⟨(Fintype.card (Ix R S) : ℂ) / 2 - x,
    (Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 + (x - (Fintype.card (Ix R S) : ℂ) / 2) * (Fintype.card (Ix P Q) : ℂ) / 2,
    fun i j f => ?_⟩
  have key : qop (negT (units (fockAct2 P Q R S))) ((Fintype.card (Ix R S) : ℂ) / 2 - x)
      ((Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 +
        (x - (Fintype.card (Ix R S) : ℂ) / 2) * (Fintype.card (Ix P Q) : ℂ) / 2) i j =
      ∑ a, ∑ b, (fockAct1 P Q R S (Eab a b) - (if a = b then x else 0) • 1) *
        (lowB (a, i) * raiB (b, j)) :=
    quad_main (fun (a : Ix P Q) (c : Ix R S) => raiB (a, c)) (fun a c => lowB (a, c))
      (fun a b => fockAct1 P Q R S (Eab a b)) (fun c d => fockAct2 P Q R S (Eab c d))
      (fun b c e => by simp [GlobalTheory.FockCasimir.lowB_mul_raiB])
      (fun a c b e => GlobalTheory.FockCasimir.lowB_comm _ _) fockAct1_Eab_eq fockAct2_Eab_eq x i j
  rw [key, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [Module.End.mul_apply]
  apply Submodule.subset_span
  refine ⟨Eab a b, (lowB (a, i) * raiB (b, j)) f, ?_⟩
  by_cases hab : a = b
  · subst hab
    simp [Eab, Matrix.trace_single_eq_same]
  · simp [hab, Eab, Matrix.trace_single_eq_of_ne _ _ _ hab]

end GlobalTheory.HoweR.QuadT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvariStatement

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

theorem _root_.GlobalTheory.T.negTranspose_fockSecondAction_quadratic_mod_coinvariants : ∀ (P Q R S : ℕ) (x : ℂ), ∃ α β : ℂ, ∀ a b f, qop (negT (units (fockAct2 P Q R S))) α β a b f ∈ coinv P Q R S x := by
  first | exact @GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | exact GlobalTheory.HoweR.QuadT.negT_fockAct2_quad | (intros; apply GlobalTheory.HoweR.QuadT.negT_fockAct2_quad <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweQuotientFiniteLengthFockPolynomials

section

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_pack : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  obtain ⟨-, hLie, -, hWt, -⟩ := GlobalTheory.T.fockActions_lie_rationalWeights_commute P Q R S
  obtain ⟨hStab, hAdm⟩ := GlobalTheory.T.fockCoinvariantKernel_stable_and_admissible P Q R S x
  obtain ⟨α, β, hq⟩ := GlobalTheory.T.fockSecondAction_quadraticIdentity_mod_coinvariants P Q R S x
  obtain ⟨α', β', hqt⟩ := GlobalTheory.T.negTranspose_fockSecondAction_quadratic_mod_coinvariants P Q R S x
  refine ⟨⟨hLie, hWt, GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩, hStab, ⟨α, β, α', β', fun a b v _ => ⟨hq a b v, hqt a b v⟩⟩, hAdm, GlobalTheory.T.fockCoinvariants_highestWeightCyclic_multiplicityOne P Q R S x⟩

end GlobalTheory.HoweR
end
end
