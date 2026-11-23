module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaConditionShiftAndDivVariableMem
public import Mathlib.Algebra.Polynomial.AlgebraMap
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisBis

section

@[expose] public section

namespace GlobalTheory.PowerMembershipInertiaEigenvalues

theorem pow_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U)
    (Q : Submodule k U) (hT : ∀ y ∈ Q, (T : U → U) y ∈ Q) (n : ℕ) :
    ∀ y ∈ Q, ((T ^ n : Module.End k U) : U → U) y ∈ Q := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    rw [pow_succ, Module.End.mul_apply]
    exact ih _ (hT y hy)

theorem main : ∀ {k U : Type} [inst : Field k] [inst_1 : AddCommGroup U] [inst_2 : Module k U] (T : Module.End k U) (Q : Submodule k U), (∀ y ∈ Q, (T : U → U) y ∈ Q) → ∀ (p : Polynomial k), ∀ y ∈ Q, ((Polynomial.aeval T : Polynomial k → Module.End k U) p : U → U) y ∈ Q := by
  intro k U _ _ _ T Q hT p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y hy
    simp only [map_add (f := _), LinearMap.add_apply]
    exact Q.add_mem (hp y hy) (hq y hy)
  | monomial n a =>
    intro y hy
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Q.smul_mem a (pow_mem T Q hT n y hy)

end GlobalTheory.PowerMembershipInertiaEigenvalues
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaNablaMemOfKillingPolynomial

section

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.GenKernelFit

theorem aeval_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (Q : Submodule k U)
    (hQ : ∀ y ∈ Q, T y ∈ Q) (p : Polynomial k) : ∀ y ∈ Q, Polynomial.aeval T p y ∈ Q := by
  first
  | exact @_root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main
  | exact _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main
  | (apply _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerMembershipInertiaEigenvalues.main ..)

theorem apply_mem {k U : Type} [Field k] [AddCommGroup U] [Module k U] (T : Module.End k U) (Q : Submodule k U)
    (hQ : ∀ y ∈ Q, T y ∈ Q) (f : Polynomial k) (hf : f.eval 0 ≠ 0) (x : U)
    (h1 : T (Polynomial.aeval T f x) ∈ Q) (j : ℕ) (h2 : (T ^ j) x ∈ Q) : T x ∈ Q := by
  have hc : IsCoprime f Polynomial.X := by
    refine ((Polynomial.irreducible_X.coprime_iff_not_dvd).2 ?_).symm
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact hf
  obtain ⟨a, b, hab⟩ := hc.pow_right (n := j)
  have e : (Polynomial.X : Polynomial k) =
      a * (Polynomial.X * f) + b * (Polynomial.X * Polynomial.X ^ j) := by
    linear_combination (-Polynomial.X) * hab
  have e2 : T x = Polynomial.aeval T a (T (Polynomial.aeval T f x)) + Polynomial.aeval T b (T ((T ^ j) x)) := by
    have := congrArg (fun p => Polynomial.aeval T p x) e
    simpa only [map_add (f := _), map_mul, map_pow, Polynomial.aeval_X, LinearMap.add_apply, Module.End.mul_apply]
      using this
  rw [e2]
  exact Q.add_mem (aeval_mem T Q hQ a _ h1) (aeval_mem T Q hQ b _ (hQ _ h2))

theorem nab_mem_of_ePoly : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (i : ZMod n) (N : Submodule k⟦X⟧ (Vc k m)) (s : ℤ), CondC (D.γ i) N → EPoly (D.γ i) N s → ∀ x ∈ N, (∃ j : ℕ, ((nab (D.γ i)) ^ j) x ∈ sh s N) → nab (D.γ i) x ∈ sh s N := by
  intro k _ l n m _ _ _ R D i N s hC hE x hx hj
  obtain ⟨f, hf, hE⟩ := hE
  obtain ⟨j, hj⟩ := hj
  exact apply_mem (nab (D.γ i)) ((sh s N).restrictScalars k)
    (GlobalTheory.PhiGam.condC_sh_and_nab_mem R (D.γ i) (D.γ_semi i) N hC s).2 f hf x (hE x hx) j hj

end GlobalTheory.GenKernelFit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaNablaMemOfKillingPolynomialStatement

section

@[expose] public section

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.gammaNabla_mem_of_killing_polynomial : ∀ {k : Type} [Field k] {l n m : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (D : ModPG R n (Vc k m)) (i : ZMod n) (N : Submodule k⟦X⟧ (Vc k m)) (s : ℤ), CondC (D.γ i) N → EPoly (D.γ i) N s → ∀ x ∈ N, (∃ j : ℕ, ((nab (D.γ i)) ^ j) x ∈ sh s N) → nab (D.γ i) x ∈ sh s N := by
  first | exact @GlobalTheory.GenKernelFit.nab_mem_of_ePoly | exact GlobalTheory.GenKernelFit.nab_mem_of_ePoly | (intros; apply GlobalTheory.GenKernelFit.nab_mem_of_ePoly <;> assumption)
end
end
