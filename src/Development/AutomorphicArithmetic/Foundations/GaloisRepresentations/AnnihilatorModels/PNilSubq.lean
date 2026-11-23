module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalInterAlt

section

@[expose] public section

theorem UpperTheory.Reformulated.B.Qi58.aeval_inter :
    ∀ {L M N : Type} [inst : Field L]
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module L M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module L N]
    (c : M →ₗ[L] N) (f : Module.End L M) (g : Module.End L N),
    (∀ (x : M), (c : M → N) ((f : M → M) x) = (g : N → N) ((c : M → N) x)) →
      ∀ (Q : Polynomial L) (x : M),
        (c : M → N) (((Polynomial.aeval f : Polynomial L → Module.End L M) Q : M → M) x) =
          ((Polynomial.aeval g : Polynomial L → Module.End L N) Q : N → N) ((c : M → N) x) := by
  intro L M N _ _ _ _ _ c f g h Q x
  have hp : ∀ (n : ℕ) (y : M), c ((f ^ n) y) = (g ^ n) (c y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction Q using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add (f := _), LinearMap.add_apply, hp', hq']
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hp]
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilSubq

section

@[expose] public section

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem pow_inter {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (c : M →ₗ[L] N) (f : End L M) (g : End L N) (h : ∀ x, c (f x) = g (c x)) (n : ℕ) (x : M) :
    c ((f ^ n) x) = (g ^ n) (c x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem aeval_inter {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (c : M →ₗ[L] N) (f : End L M) (g : End L N) (h : ∀ x, c (f x) = g (c x)) (Q : Polynomial L) (x : M) :
    c (Polynomial.aeval f Q x) = Polynomial.aeval g Q (c x) :=
  _root_.UpperTheory.Reformulated.B.Qi58.aeval_inter c f g h Q x

theorem UpperTheory.Gal.crystallineComparison.nilSubq_of :
    AdmExact → NilEmb → NilSubq := by
  intro hA hE F G B _ _ _ _ σ ψ L _ _ e hB V W _ _ _ _ _ _ _ _ _ ρ ρ' hS hAdm
  obtain ⟨U, _, _, ρU, i, p, hi, hinj, hp, hsurj⟩ := hS
  letI : Module F U := Module.compHom U (algebraMap F L)
  haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite L U := Module.Finite.of_injective i hinj
  haveI : Module.Finite L W := Module.Finite.of_surjective p hsurj
  have hU : admitted σ e ρU := (hA F G B σ L e hB U V ρU ρ i hi).1 hinj hAdm
  obtain ⟨hW, hmap⟩ := (hA F G B σ L e hB U W ρU ρ' p hp).2 hsurj hU
  refine ⟨hW, fun Q hQ => ?_⟩
  obtain ⟨N, hN⟩ : NilD σ ψ ρU Q :=
    hE F G B σ ψ L U ρU Unit (fun _ => V) (fun _ => ρ) (fun _ => i) (fun _ => hi)
      (fun v h => hinj (by simpa using h ())) Q (fun _ => hQ)
  refine ⟨N, fun y hy => ?_⟩
  rw [← hmap] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have h1 : ∀ z : U ⊗[F] B, AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) (onPer ψ L U z) =
      onPer ψ L W (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul u b => simp [onPer]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← pow_inter _ _ _ (fun z => aeval_inter _ _ _ h1 Q z) N x, hN x hx, map_zero]
end
end
