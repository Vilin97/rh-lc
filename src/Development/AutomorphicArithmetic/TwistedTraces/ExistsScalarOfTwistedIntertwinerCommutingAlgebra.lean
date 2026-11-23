module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.TwistedTraces.ListOfFnProdEqMulUpdateOneOfPairwiseCommute
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.LinearFormEqMulTraceOfTwistedInvariant

section

@[expose] public section

open scoped BigOperators

theorem UpperTheory.linearForm_eq_mul_trace_of_twisted_invariant :
    ∀ (P : Type) [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P] (J E : Module.End ℂ P) (l : Module.End ℂ P →ₗ[ℂ] ℂ), LinearMap.trace ℂ P (E * J) = 1 → (∀ a a' b : Module.End ℂ P, a' * J = J * a → l (b * a') = l (a * b)) → ∀ b, l b = l E * LinearMap.trace ℂ P (b * J) := by
  intro P _ _ _ J E l hE h
  have tr : ∀ (η : P →ₗ[ℂ] ℂ) (u : P), LinearMap.trace ℂ P (η.smulRight u) = η u := by
    intro η u
    have h0 := LinearMap.trace_eq_contract_apply ℂ P
      (TensorProduct.tmul ℂ (show Module.Dual ℂ P from η) u)
    have h1 : dualTensorHom ℂ P P (TensorProduct.tmul ℂ (show Module.Dual ℂ P from η) u)
        = η.smulRight u := by
      apply LinearMap.ext
      intro y
      simp [dualTensorHom_apply]
    rw [h1] at h0
    rw [h0]
    simp [contractLeft_apply]
  have key : ∀ (u x : P) (η ξ : P →ₗ[ℂ] ℂ),
      ξ (J x) * l (η.smulRight u) = η (J u) * l (ξ.smulRight x) := by
    intro u x η ξ
    have hc : (η.smulRight (J x)) * J = J * ((η ∘ₗ J).smulRight x) := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply]
    have h1 := h ((η ∘ₗ J).smulRight x) (η.smulRight (J x)) (ξ.smulRight u) hc
    have e1 : ξ.smulRight u * η.smulRight (J x) = ξ (J x) • η.smulRight u := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply, smul_smul, mul_comm]
    have e2 : (η ∘ₗ J).smulRight x * ξ.smulRight u = η (J u) • ξ.smulRight x := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply, smul_smul, mul_comm]
    rw [e1, e2, map_smul, map_smul] at h1
    simpa [smul_eq_mul] using h1
  have hJ : ∃ x, J x ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hJ0 : J = 0 := LinearMap.ext hne
    rw [hJ0] at hE
    simp at hE
  obtain ⟨x₀, hx₀⟩ := hJ
  have hφ : ∃ φ : Module.Dual ℂ P, φ (J x₀) ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ (J x₀)).1 hne)
  obtain ⟨φ, hφ⟩ := hφ
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : P →ₗ[ℂ] ℂ, ξ₀ (J x₀) = 1 :=
    ⟨(φ (J x₀))⁻¹ • φ, by simp [hφ]⟩
  have rank1 : ∀ (η : P →ₗ[ℂ] ℂ) (u : P),
      l (η.smulRight u) = l (ξ₀.smulRight x₀) * LinearMap.trace ℂ P (η.smulRight u * J) := by
    intro η u
    have e : η.smulRight u * J = (η ∘ₗ J).smulRight u := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply]
    have hk := key u x₀ η ξ₀
    rw [hξ₀, one_mul] at hk
    rw [e, tr, hk]
    simp [mul_comm]
  have all : ∀ b : Module.End ℂ P,
      l b = l (ξ₀.smulRight x₀) * LinearMap.trace ℂ P (b * J) := by
    intro b
    obtain ⟨t, rfl⟩ := (dualTensorHomEquiv ℂ P P).surjective b
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul η u =>
      have h1 : dualTensorHomEquiv ℂ P P (TensorProduct.tmul ℂ η u)
          = LinearMap.smulRight (show P →ₗ[ℂ] ℂ from η) u := by
        apply LinearMap.ext
        intro y
        simp [dualTensorHomEquiv, dualTensorHom_apply]
      rw [h1]
      exact rank1 η u
    | add s t hs ht =>
      rw [map_add (f := _), map_add (f := _), add_mul, map_add (f := _), mul_add, hs, ht]
  intro b
  have hκ := all E
  rw [hE, mul_one] at hκ
  rw [hκ]
  exact all b
end
end

-- Source module: Development.AutomorphicArithmetic.TwistedTraces.ExistsScalarOfTwistedIntertwinerCommutingAlgebra

section

@[expose] public section

open scoped BigOperators

theorem UpperTheory.exists_scalar_of_twisted_intertwiner_commuting_algebras :
    ∀ (r : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (P : Fin r → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, FiniteDimensional ℂ (P i)] (c : ∀ i, Module.End ℂ (P i) →ₐ[ℂ] Module.End ℂ X) (J : ∀ i, Module.End ℂ (P i)) (ρ : Module.End ℂ X), (∀ i j, i ≠ j → ∀ s t, Commute (c i s) (c j t)) → (∀ i, J i ≠ 0) → (∀ i a b, b * J i = J i * a → ρ * c i a = c i b * ρ) → ∃ κ : ℂ, ∀ b : ∀ i, Module.End ℂ (P i), LinearMap.trace ℂ X ((List.ofFn fun i => c i (b i)).prod * ρ) = κ * ∏ i, LinearMap.trace ℂ (P i) (b i * J i) := by
  intro r X _ _ _ P _ _ _ c J ρ hc hJ hρ
  have hE : ∀ i, ∃ E : Module.End ℂ (P i), LinearMap.trace ℂ (P i) (E * J i) = 1 := by
    intro i
    have hx : ∃ x, J i x ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hJ i (LinearMap.ext hne)
    obtain ⟨x₀, hx₀⟩ := hx
    have hφ : ∃ φ : Module.Dual ℂ (P i), φ (J i x₀) ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ (J i x₀)).1 hne)
    obtain ⟨φ, hφ⟩ := hφ
    refine ⟨((φ (J i x₀))⁻¹ • φ).smulRight x₀, ?_⟩
    have e : (((φ (J i x₀))⁻¹ • φ).smulRight x₀) * J i
        = dualTensorHom ℂ (P i) (P i)
            (TensorProduct.tmul ℂ (((φ (J i x₀))⁻¹ • φ) ∘ₗ J i) x₀) := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply, dualTensorHom_apply]
    rw [e, LinearMap.trace_eq_contract_apply ℂ (P i)]
    simp [contractLeft_apply, hφ]
  choose E hE using hE
  obtain ⟨F, hF⟩ : ∃ F : (∀ i, Module.End ℂ (P i)) → ℂ, ∀ b, F b =
      LinearMap.trace ℂ X ((List.ofFn fun i => c i (b i)).prod * ρ) := ⟨_, fun _ => rfl⟩
  have step : ∀ (b : ∀ i, Module.End ℂ (P i)) (i : Fin r) (y : Module.End ℂ (P i)),
      F (Function.update b i y)
        = F (Function.update b i (E i)) * LinearMap.trace ℂ (P i) (y * J i) := by
    intro b i y
    obtain ⟨a, ha⟩ : ∃ a : Fin r → Module.End ℂ X, a = fun j => c j (b j) := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : Module.End ℂ X, Q = (List.ofFn (Function.update a i 1)).prod :=
      ⟨_, rfl⟩
    have fac : ∀ z, (List.ofFn fun j => c j (Function.update b i z j)).prod = c i z * Q := by
      intro z
      have h := (UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (Module.End ℂ X) r (fun j => c j (Function.update b i z j))
        (fun p q hpq => hc p q hpq _ _) i).1
      have e : Function.update (fun j => c j (Function.update b i z j)) i 1
          = Function.update a i 1 := by
        funext j
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj, ha]
      rw [h, e, Function.update_self, hQ]
    have com : ∀ z, Commute (c i z) Q := by
      intro z
      rw [hQ]
      refine (UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (Module.End ℂ X) r a ?_ i).2 (c i z) ?_
      · intro p q hpq
        rw [ha]
        exact hc p q hpq _ _
      · intro j hj
        rw [ha]
        exact hc i j (Ne.symm hj) _ _
    obtain ⟨l, hl⟩ : ∃ l : Module.End ℂ (P i) →ₗ[ℂ] ℂ,
        ∀ z, l z = LinearMap.trace ℂ X (c i z * Q * ρ) :=
      ⟨(LinearMap.trace ℂ X) ∘ₗ (LinearMap.mulRight ℂ (Q * ρ)) ∘ₗ (c i).toLinearMap, by
        intro z
        simp [mul_assoc]⟩
    have hyp : ∀ a a' t : Module.End ℂ (P i), a' * J i = J i * a → l (t * a') = l (a * t) := by
      intro a a' t h
      have h1 := hρ i a a' h
      have e1 : c i (t * a') * Q * ρ = (c i t * Q * ρ) * c i a := by
        rw [map_mul, mul_assoc (c i t), (com a').eq, mul_assoc (c i t * Q) ρ, h1]
        simp only [mul_assoc]
      have e2 : c i (a * t) * Q * ρ = c i a * (c i t * Q * ρ) := by
        rw [map_mul]
        simp only [mul_assoc]
      rw [hl, hl, e1, e2, LinearMap.trace_mul_comm]
    have key := UpperTheory.linearForm_eq_mul_trace_of_twisted_invariant (P i) (J i) (E i) l (hE i) hyp y
    rw [hF, hF, fac, fac, ← hl, ← hl]
    exact key
  have ind : ∀ (S : Finset (Fin r)) (b : ∀ i, Module.End ℂ (P i)),
      F b = F (S.piecewise E b) * ∏ i ∈ S, LinearMap.trace ℂ (P i) (b i * J i) := by
    intro S b
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      have hb : S.piecewise E b i = b i := Finset.piecewise_eq_of_notMem _ _ _ hi
      have h1 := step (S.piecewise E b) i (b i)
      rw [← hb, Function.update_eq_self, hb] at h1
      rw [Finset.prod_insert hi, Finset.piecewise_insert, ih, h1]
      ring
  refine ⟨F E, fun b => ?_⟩
  have h := ind Finset.univ b
  rw [Finset.piecewise_univ] at h
  rw [← hF, h]
end
end
