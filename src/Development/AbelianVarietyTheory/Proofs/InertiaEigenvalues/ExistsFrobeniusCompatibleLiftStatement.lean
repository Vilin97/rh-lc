module

public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Basic
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
public import Mathlib.NumberTheory.Basic
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
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorGhostEqFrobeniusIterate

section

@[expose] public section

open scoped NNReal
open Finset

namespace GlobalTheory.DworkGhost


open scoped Classical in
open Classical in
noncomputable def coeff {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) : ℕ → A
  | n => if h : ((l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i))
      then h.choose else 0
decreasing_by exact i.isLt

theorem coeff_spec {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A) (a : A) (n : ℕ)
    (h : (l : A) ^ n ∣ φ^[n] a - ∑ i ∈ range n, (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  have h' : (l : A) ^ n ∣ φ^[n] a - ∑ i : Fin n, (l : A) ^ (i : ℕ) * coeff l φ a i ^ l ^ (n - i) := by
    rwa [Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n]
  have e : coeff l φ a n = h'.choose := by
    rw [coeff, dite_eq_left h']
  have hc := h'.choose_spec
  rw [← e, Fin.sum_univ_eq_sum_range (fun i => (l : A) ^ i * coeff l φ a i ^ l ^ (n - i)) n] at hc
  rw [sum_range_succ, Nat.sub_self, pow_zero, pow_one, ← hc]
  ring

theorem ghost_eq {A : Type} [CommRing A] (l : ℕ) (φ : A →+* A)
    (hφ : ∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) (a : A) (n : ℕ) :
    φ^[n] a = ∑ i ∈ range (n + 1), (l : A) ^ i * coeff l φ a i ^ l ^ (n - i) := by
  induction n with
  | zero => exact coeff_spec l φ a 0 (by simp)
  | succ n ih =>
    apply coeff_spec

    rw [Function.iterate_succ_apply', ih, map_sum, ← sum_sub_distrib]
    apply dvd_sum
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hi)
    rw [map_mul, map_pow, map_pow, map_natCast, ← mul_sub]
    have e1 : n + 1 = i + (n - i + 1) := by omega
    have e2 : n + 1 - i = n - i + 1 := by omega
    have e3 : coeff l φ a i ^ l ^ (n - i + 1) = (coeff l φ a i ^ l) ^ l ^ (n - i) := by
      rw [pow_succ', pow_mul]
    rw [e2, e3, e1, pow_add]
    exact mul_dvd_mul_left _ (dvd_sub_pow_of_dvd_sub (hφ (coeff l φ a i)) (n - i))

theorem exists_witt_ghost_iterate : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A),
    (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A,
      ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  intro l _ A _ φ hφ a
  refine ⟨WittVector.mk l (coeff l φ a), fun n => ?_⟩
  rw [WittVector.ghostComponent_apply, aeval_wittPolynomial, ghost_eq l φ hφ a n]

end GlobalTheory.DworkGhost
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittVectorGhostEqFrobeniusIterateStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.exists_wittVector_ghost_eq_frobenius_iterate : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → ∀ a : A, ∃ w : WittVector l A, ∀ n, WittVector.ghostComponent n w = φ^[n] a := by
  first | exact @GlobalTheory.DworkGhost.exists_witt_ghost_iterate | exact GlobalTheory.DworkGhost.exists_witt_ghost_iterate | (intros; apply GlobalTheory.DworkGhost.exists_witt_ghost_iterate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GhostComponentInjectiveOfNoTorsion

section

@[expose] public section

open scoped NNReal

namespace GlobalTheory

theorem WittVector.ghostComponent_injective_of_noTorsion :
    ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
      ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  intro l _ A _ hA x y h
  have hpow : ∀ (k : ℕ) (a : A), ((l : ℕ) : A) ^ k * a = 0 → a = 0 := by
    intro k
    induction k with
    | zero => intro a ha; simpa using ha
    | succ k ih =>
      intro a ha
      apply hA
      apply ih
      rw [← mul_assoc, ← pow_succ]
      exact ha
  apply _root_.WittVector.ext
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hn := h n
    rw [_root_.WittVector.ghostComponent_apply, _root_.WittVector.ghostComponent_apply,
      wittPolynomial_eq_sum_C_mul_X_pow] at hn

    simp only [map_sum, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
    eq_intCast, Int.cast_natCast, map_natCast] at hn
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hn
    have hs : ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * x.coeff i ^ l ^ (n - i) =
        ∑ i ∈ Finset.range n, ((l : ℕ) : A) ^ i * y.coeff i ^ l ^ (n - i) :=
      Finset.sum_congr rfl (fun i hi => by rw [ih i (Finset.mem_range.1 hi)])
    rw [hs, add_left_cancel_iff, Nat.sub_self, pow_zero, pow_one, pow_one] at hn
    apply sub_eq_zero.1
    apply hpow n
    rw [mul_sub, hn, sub_self]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GhostComponentInjectiveOfNoTorsionStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.wittVector_eq_of_ghostComponent_eq_of_no_torsion : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A], (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ x y : WittVector l A, (∀ n, WittVector.ghostComponent n x = WittVector.ghostComponent n y) → x = y := by
  first | exact @GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | exact GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion | (intros; apply GlobalTheory.WittVector.ghostComponent_injective_of_noTorsion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusCompatibleLift

section

@[expose] public section

open scoped NNReal

namespace GlobalTheory.DworkLift

theorem exists_frobenius_compatible_lift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A),
    (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) →
    ∀ (O : Type) [CommRing O] [CharP O l] (f : A →+* O), ∃ F : A →+* WittVector l O,
      (∀ a, (F a).coeff 0 = f a) ∧ ∀ a, F (φ a) = WittVector.frobenius (F a) := by
  intro l _ A _ φ hφ htor O _ _ f
  have hex := GlobalTheory.T.exists_wittVector_ghost_eq_frobenius_iterate l A φ hφ
  have inj := GlobalTheory.T.wittVector_eq_of_ghostComponent_eq_of_no_torsion l A htor
  let s : A → WittVector l A := fun a => Classical.choose (hex a)
  have hs : ∀ a n, WittVector.ghostComponent n (s a) = φ^[n] a := fun a => Classical.choose_spec (hex a)
  have hit : ∀ (n : ℕ) (a : A), φ^[n] a = (φ ^ n) a := fun n a => by rw [RingHom.coe_pow]
  let S : A →+* WittVector l A :=
    { toFun := s
      map_one' := inj _ _ fun n => by rw [hs, map_one, hit, map_one]
      map_mul' := fun a b => inj _ _ fun n => by rw [map_mul, hs, hs, hs, hit, hit, hit, map_mul]
      map_zero' := inj _ _ fun n => by rw [hs, map_zero, hit, map_zero]
      map_add' := fun a b => inj _ _ fun n => by rw [map_add (f := _), hs, hs, hs, hit, hit, hit, map_add (f := _)] }
  have hS0 : ∀ a, (S a).coeff 0 = a := fun a => by
    change (s a).coeff 0 = a
    have h := hs a 0
    rw [WittVector.ghostComponent_apply, wittPolynomial_zero] at h
    simpa using h
  have hSφ : ∀ a, S (φ a) = WittVector.frobenius (S a) := fun a => inj _ _ fun n => by
    change WittVector.ghostComponent n (s (φ a)) = WittVector.ghostComponent n (WittVector.frobenius (s a))
    rw [WittVector.ghostComponent_frobenius, hs, hs, Function.iterate_succ_apply]
  refine ⟨(WittVector.map f).comp S, fun a => ?_, fun a => ?_⟩
  · simp only [RingHom.comp_apply, WittVector.map_coeff, hS0]
  · simp only [RingHom.comp_apply, hSφ]
    exact WittVector.IsPoly.map (WittVector.frobenius_isPoly l) f (S a)

end GlobalTheory.DworkLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusCompatibleLiftStatement

section

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.exists_frobenius_compatible_wittVector_lift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ (O : Type) [CommRing O] [CharP O l] (f : A →+* O), ∃ F : A →+* WittVector l O, (∀ a, (F a).coeff 0 = f a) ∧ ∀ a, F (φ a) = WittVector.frobenius (F a) := by
  first | exact @GlobalTheory.DworkLift.exists_frobenius_compatible_lift | exact GlobalTheory.DworkLift.exists_frobenius_compatible_lift | (intros; apply GlobalTheory.DworkLift.exists_frobenius_compatible_lift <;> assumption)
end
end
