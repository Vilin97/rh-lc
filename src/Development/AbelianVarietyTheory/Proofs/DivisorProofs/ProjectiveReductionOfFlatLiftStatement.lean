module

public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorLiftOfMulEqPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalUniformiserAbovePrimeStatement
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeOfPrincipalMaximalIdealOfKerSmulLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedFieldTensorIntFiniteReducedStatement
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationMaximalIdealEqSpanNilpotentArtinianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedModuleMemAnnSpanSmulTopStatement
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfSurjectiveTensorSemilinear

section

@[expose] public section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem finite_of_surjective_tensor_semilinear : ∀ (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (O : Type) [CommRing O] (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], Module.Finite Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → Module.Finite (k ⊗[ℤ] O) N := by
  intro Λ _ k _ π O _ M _ _ _ _ hM N _ _ f hf
  classical
  obtain ⟨s, hs⟩ := hM.fg_top
  refine ⟨⟨s.image f, ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  rintro n -
  obtain ⟨m, rfl⟩ := hf n
  have hm : m ∈ Submodule.span Λ (s : Set M) := hs ▸ Submodule.mem_top
  induction hm using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx =>
    have h : a • x = (algebraMap Λ (Λ ⊗[ℤ] O) a) • x := (algebraMap_smul (Λ ⊗[ℤ] O) a x).symm
    rw [h, LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ hx

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOfSurjectiveTensorSemilinearStatement

section

@[expose] public section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.finite_of_surjective_semilinear_tensor : ∀ (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (O : Type) [CommRing O] (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] O) M] [IsScalarTower Λ (Λ ⊗[ℤ] O) M], Module.Finite Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] O) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ O)).toRingHom] N), Function.Surjective f → Module.Finite (k ⊗[ℤ] O) N := by
  first | exact @GlobalTheory.finite_of_surjective_tensor_semilinear | exact GlobalTheory.finite_of_surjective_tensor_semilinear | (intros; apply GlobalTheory.finite_of_surjective_tensor_semilinear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedQuotTensorOfReducedModP

section

@[expose] public section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem reduced_quot_tensor_of_reduced_modp :
    ∀ (O : Type) [CommRing O] (k : Type) [Field k] (p : ℕ) (ϖ : O), (p : k) = 0 →
      IsReduced (k ⊗[ℤ] (O ⧸ Ideal.span {(p : O), ϖ})) →
      IsReduced ((k ⊗[ℤ] O) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ}) := by
  intro O _ k _ p ϖ hp hred
  set I : Ideal O := Ideal.span {(p : O), ϖ}
  set f := Algebra.TensorProduct.map (AlgHom.id ℤ k) (Ideal.Quotient.mkₐ ℤ I) with hf
  have hker : RingHom.ker f.toRingHom = Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ} := by
    have h := Algebra.TensorProduct.lTensor_ker (A := k) (Ideal.Quotient.mkₐ ℤ I)
      (Ideal.Quotient.mkₐ_surjective ℤ I)
    have hk : RingHom.ker (Ideal.Quotient.mkₐ ℤ I) = I := Ideal.Quotient.mkₐ_ker ℤ I
    have h0 : (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] k ⊗[ℤ] O) (p : O) = 0 := by
      rw [map_natCast]
      have : ((p : ℕ) : k ⊗[ℤ] O) = (Algebra.TensorProduct.includeLeft : k →ₐ[ℤ] k ⊗[ℤ] O) (p : k) := by
        rw [map_natCast]
      rw [this, hp, map_zero]
    have h1 : (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] k ⊗[ℤ] O) ϖ = (1 : k) ⊗ₜ[ℤ] ϖ := rfl
    have e := h
    rw [hk] at e
    change RingHom.ker f.toRingHom = _ at e
    rw [e, Ideal.map_span, Set.image_pair]
    erw [h0, h1]
    exact Ideal.span_insert_zero
  have hinj : Function.Injective (RingHom.kerLift f.toRingHom) := RingHom.kerLift_injective _
  have hR : IsReduced (k ⊗[ℤ] O ⧸ RingHom.ker f.toRingHom) := isReduced_of_injective _ hinj
  rw [hker] at hR
  exact hR

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedQuotTensorOfReducedModPStatement

section

@[expose] public section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.isReduced_quot_tensor_of_reduced_mod_p : ∀ (O : Type) [CommRing O] (k : Type) [Field k] (p : ℕ) (ϖ : O), (p : k) = 0 → IsReduced (k ⊗[ℤ] (O ⧸ Ideal.span {(p : O), ϖ})) → IsReduced ((k ⊗[ℤ] O) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ}) := by
  first | exact @GlobalTheory.reduced_quot_tensor_of_reduced_modp | exact GlobalTheory.reduced_quot_tensor_of_reduced_modp | (intros; apply GlobalTheory.reduced_quot_tensor_of_reduced_modp <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerSmulLeIdealSmulOfFree

section

@[expose] public section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem ker_smul_le_ideal_smul_of_free : ∀ (Λ : Type) [CommRing Λ] (t : Λ), (∀ x : Λ, t * x = 0 → x ∈ Ideal.span {t}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M], Module.Free Λ M → ∀ m : M, t • m = 0 → m ∈ Ideal.span {t} • (⊤ : Submodule Λ M) := by
  intro Λ _ t ht M _ _ hfree m hm
  let b := Module.Free.chooseBasis Λ M
  have hc : ∀ i, ∃ d, b.repr m i = t * d := by
    intro i
    have h0 : t * b.repr m i = 0 := by
      have := congrArg (fun x => b.repr x i) hm
      simpa using this
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (ht _ h0)
    exact ⟨d, by rw [← hd, mul_comm]⟩
  choose d hd using hc
  have hm' : m = t • ∑ i ∈ (b.repr m).support, d i • b i := by
    have e := b.linearCombination_repr m
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at e
    rw [Finset.smul_sum]
    conv_lhs => rw [← e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hd i, mul_smul]
  rw [hm']
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerSmulLeIdealSmulOfFreeStatement

section

@[expose] public section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.mem_span_smul_of_smul_eq_zero_of_free : ∀ (Λ : Type) [CommRing Λ] (t : Λ), (∀ x : Λ, t * x = 0 → x ∈ Ideal.span {t}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M], Module.Free Λ M → ∀ m : M, t • m = 0 → m ∈ Ideal.span {t} • (⊤ : Submodule Λ M) := by
  first | exact @GlobalTheory.ker_smul_le_ideal_smul_of_free | exact GlobalTheory.ker_smul_le_ideal_smul_of_free | (intros; apply GlobalTheory.ker_smul_le_ideal_smul_of_free <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveReductionOfFlatLift

section

@[expose] public section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.FlatLift

theorem projective_of_nilpotent_of_reduced_quotient (D : Type) [CommRing D] [IsArtinianRing D] (x : D) (hx : IsNilpotent x)
    (hr : IsReduced (D ⧸ Ideal.span {x})) (N : Type 1) [AddCommGroup N] [Module D N]
    [Module.Finite D N]
    (h : ∀ n : N, x • n = 0 → n ∈ Ideal.span {a : D | x * a = 0} • (⊤ : Submodule D N)) :
    Module.Projective D N := by
  have hflat : Module.Flat D N := by
    apply Module.flat_of_localized_maximal
    intro P _
    have hloc := GlobalTheory.T.localization_maximalIdeal_eq_span_nilpotent_artinian D x hx hr P
    have hann := GlobalTheory.T.localizedModule_mem_annSpan_smul_of_mem D P.primeCompl x N h
    haveI := GlobalTheory.T.free_of_principal_maximalIdeal_of_ker_smul_le' (Localization.AtPrime P) (algebraMap D _ x) hloc
      (LocalizedModule P.primeCompl N) inferInstance hann
    exact Module.Flat.trans D (Localization.AtPrime P) _
  haveI : Module.FinitePresentation D N := Module.finitePresentation_of_finite D N
  exact Module.Flat.projective_of_finitePresentation

theorem projective_reduction_of_flat_lift : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), Function.Surjective π → RingHom.ker π = Ideal.span {(p : Λ)} → (p : Λ) ^ 2 = 0 → (∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] 𝓞 F) M] [IsScalarTower Λ (Λ ⊗[ℤ] 𝓞 F) M], Module.Finite Λ M → Module.Free Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] 𝓞 F) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ M)) → Module.Projective (k ⊗[ℤ] 𝓞 F) N := by
  intro p _ F _ _ Λ _ k _ π hπ hker hp2 hann M _ _ _ _ hfin hfree N _ _ f hf hkerf
  have hpk : (p : k) = 0 := by
    have : (p : Λ) ∈ RingHom.ker π := by rw [hker]; exact Ideal.subset_span rfl
    simpa using this
  have hkerp := GlobalTheory.T.mem_span_smul_of_smul_eq_zero_of_free Λ (p : Λ) hann M hfree
  have hkerf' : ∀ m, f m = 0 → m ∈ Ideal.span {(p : Λ)} • (⊤ : Submodule Λ M) := by
    intro m hm; rw [← hker]; exact hkerf m hm
  obtain ⟨ϖ, z, hϖz, ⟨n0, hn0⟩, hred⟩ := GlobalTheory.T.exists_global_uniformizer_above_prime p F
  haveI : IsArtinianRing (k ⊗[ℤ] 𝓞 F) := IsArtinianRing.of_finite k (k ⊗[ℤ] 𝓞 F)
  haveI : Module.Finite (k ⊗[ℤ] 𝓞 F) N := GlobalTheory.T.finite_of_surjective_semilinear_tensor Λ k π (𝓞 F) M hfin N f hf
  have hnil : IsNilpotent ((1 : k) ⊗ₜ[ℤ] ϖ) := by
    refine ⟨n0, ?_⟩
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hn0
    rw [Algebra.TensorProduct.tmul_pow, one_pow, ← hy, mul_comm, ← nsmul_eq_mul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, mul_one, hpk,
      TensorProduct.zero_tmul]
  have hfinQ : Finite (𝓞 F ⧸ Ideal.span {(p : 𝓞 F), ϖ}) := by
    have hne : Ideal.span {(p : 𝓞 F)} ≠ ⊥ := by
      simp [Ideal.span_singleton_eq_bot, (Fact.out : p.Prime).ne_zero]
    haveI : Finite (𝓞 F ⧸ Ideal.span {(p : 𝓞 F)}) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective
      (Ideal.span_mono (by simp : ({(p : 𝓞 F)} : Set (𝓞 F)) ⊆ {(p : 𝓞 F), ϖ})))
  have hredD := GlobalTheory.T.isReduced_quot_tensor_of_reduced_mod_p (𝓞 F) k p ϖ hpk (GlobalTheory.T.isReduced_field_tensor_int_finite_reduced _ k)
  have hannN := GlobalTheory.T.annihilator_lift_of_mul_eq_p_alt p (𝓞 F) Λ k π hpk hp2 M hkerp N f hf hkerf' ϖ z hϖz
  exact projective_of_nilpotent_of_reduced_quotient _ _ hnil hredD N hannN

end GlobalTheory.FlatLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveReductionOfFlatLiftStatement

section

@[expose] public section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.projective_of_surjective_ker_le_smul : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k), Function.Surjective π → RingHom.ker π = Ideal.span {(p : Λ)} → (p : Λ) ^ 2 = 0 → (∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M] [Module (Λ ⊗[ℤ] 𝓞 F) M] [IsScalarTower Λ (Λ ⊗[ℤ] 𝓞 F) M], Module.Finite Λ M → Module.Free Λ M → ∀ (N : Type 1) [AddCommGroup N] [Module (k ⊗[ℤ] 𝓞 F) N] (f : M →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] N), Function.Surjective f → (∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ M)) → Module.Projective (k ⊗[ℤ] 𝓞 F) N := by
  first | exact @GlobalTheory.FlatLift.projective_reduction_of_flat_lift | exact GlobalTheory.FlatLift.projective_reduction_of_flat_lift | (intros; apply GlobalTheory.FlatLift.projective_reduction_of_flat_lift <;> assumption)
end
end
