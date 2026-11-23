module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.Ideal.Span
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
import Mathlib.Topology.Sheaves.Presheaf
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
public import Mathlib.RingTheory.Ideal.Operations
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.KjMap
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Ideal.Quotient.Index
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.SpecializationMapCompUniversalSection

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SmulPowLeOfStep

section

@[expose] public section

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.smul_pow_le_of_step :
    ∀ (R : Type) [CommRing R] (𝔞 I 𝔶 : Ideal R) (f : R),
      (∀ (X : Type) [AddCommGroup X] [Module R X] (X₀ : Type) [AddCommGroup X₀] [Module R X₀] (φ : X₀ →ₗ[R] X) (ψ : X →ₗ[R] X₀) (n : R), (∀ x, φ (ψ x) = n • x) → n ∣ f →
        (𝔞 • ⊤ : Submodule R X₀) ≤ I • ⊤ → ((Ideal.span {f} * 𝔞) • ⊤ : Submodule R X) ≤ I • ⊤) ∧
      (∀ (M : Type) [AddCommGroup M] [Module R M], ((Ideal.span {f} * 𝔞) • ⊤ : Submodule R M) ≤ (I ⊔ 𝔶) • ⊤ →
        ∀ k : ℕ, ((Ideal.span {f ^ k} * 𝔞 ^ k) • ⊤ : Submodule R M) ≤ (I ⊔ 𝔶 ^ k) • ⊤) := by
  intro R _ 𝔞 I 𝔶 f
  refine ⟨?_, ?_⟩
  · intro X _ _ X₀ _ _ φ ψ n hn hnf h
    obtain ⟨c, rfl⟩ := hnf
    refine Submodule.smul_le.2 ?_
    intro r hr x _
    obtain ⟨a, ha, rfl⟩ := Ideal.mem_span_singleton_mul.1 hr
    have h1 : a • ψ x ∈ (I • ⊤ : Submodule R X₀) :=
      h (Submodule.smul_mem_smul ha Submodule.mem_top)
    have h2 : φ (a • ψ x) ∈ (I • ⊤ : Submodule R X) := by
      have h3 : φ (a • ψ x) ∈ (I • ⊤ : Submodule R X₀).map φ := Submodule.mem_map_of_mem h1
      rw [Submodule.map_smul''] at h3
      exact Submodule.smul_mono le_rfl le_top h3
    have h4 : (n * c * a) • x = c • φ (a • ψ x) := by
      rw [map_smul, hn, smul_smul, smul_smul]
      congr 1
      ring
    rw [h4]
    exact Submodule.smul_mem _ c h2
  · intro M _ _ h k
    rw [← Ideal.span_singleton_pow, ← mul_pow]
    generalize Ideal.span {f} * 𝔞 = b at h
    induction k with
    | zero => simp
    | succ k ih =>
      have hle : (I ⊔ 𝔶 ^ k) * (I ⊔ 𝔶) ≤ I ⊔ 𝔶 ^ (k + 1) := by
        rw [Ideal.sup_mul, Ideal.mul_sup (𝔶 ^ k), pow_succ]
        refine sup_le (le_sup_of_le_left Ideal.mul_le_left) (sup_le (le_sup_of_le_left Ideal.mul_le_right) le_sup_right)
      calc (b ^ (k + 1) • ⊤ : Submodule R M) = b • (b ^ k • ⊤) := by
            rw [pow_succ', mul_smul]
        _ ≤ b • ((I ⊔ 𝔶 ^ k) • ⊤) := smul_mono_right b ih
        _ = (I ⊔ 𝔶 ^ k) • (b • ⊤) := by
            rw [← mul_smul, ← mul_smul, mul_comm]
        _ ≤ (I ⊔ 𝔶 ^ k) • ((I ⊔ 𝔶) • ⊤) := smul_mono_right _ h
        _ = ((I ⊔ 𝔶 ^ k) * (I ⊔ 𝔶)) • ⊤ := by rw [mul_smul]
        _ ≤ (I ⊔ 𝔶 ^ (k + 1)) • ⊤ := Submodule.smul_mono_left hle
end
end

-- Source module: Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FiniteModuleMaximalIdealAnnihilation

section

@[expose] public section

theorem UpperTheory.Reformulated.B.FiniteModuleMaximalIdealAnnihilation.exists_pow_maximalIdeal_smul_finite_eq_zero :
    ∀ (R Q : Type) [inst : CommRing R] [inst_1 : IsLocalRing R]
    [inst_2 : AddCommGroup Q] [inst_3 : _root_.Module R Q] [Finite Q],
    ∃ (c : ℕ), ∀ a ∈ IsLocalRing.maximalIdeal R ^ c, ∀ (z : Q), a • z = (0 : Q) := by
  intro R Q _ _ _ _ _
  haveI : Finite (Submodule R Q) :=
    Finite.of_injective (fun N : Submodule R Q => (N : Set Q)) SetLike.coe_injective
  obtain ⟨i, j, hij, h⟩ : ∃ i j : ℕ, i < j ∧
      (IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)) =
        IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := by
    obtain ⟨i, j, hne, h⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R Q))
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact ⟨i, j, hlt, h⟩
    · exact ⟨j, i, hlt, h.symm⟩
  have hbot : IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) = ⊥ := by
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
      (Submodule.fg_def.2 ⟨_, Set.toFinite _, Submodule.span_eq _⟩) ?_
      (IsLocalRing.maximalIdeal_le_jacobson _)
    calc IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q)
        = IsLocalRing.maximalIdeal R ^ j • (⊤ : Submodule R Q) := h
      _ ≤ IsLocalRing.maximalIdeal R ^ (i + 1) • (⊤ : Submodule R Q) :=
          Submodule.smul_mono_left (Ideal.pow_le_pow_right hij)
      _ = _ := by rw [pow_succ', Submodule.mul_smul]
  refine ⟨i, fun a ha z => ?_⟩
  have hz : a • z ∈ IsLocalRing.maximalIdeal R ^ i • (⊤ : Submodule R Q) :=
    Submodule.smul_mem_smul ha Submodule.mem_top
  rwa [hbot, Submodule.mem_bot] at hz
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.ExistsPowMaximalIdealSmulFiniteEqZero

section

@[expose] public section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Core
open scoped TensorProduct

private theorem exists_pow_maximalIdeal_smul_finite_eq_zero (R Q : Type) [CommRing R] [IsLocalRing R] [AddCommGroup Q] [Module R Q] [Finite Q] :
    ∃ c : ℕ, ∀ a ∈ maximalIdeal R ^ c, ∀ z : Q, a • z = 0 :=
  _root_.UpperTheory.Reformulated.B.FiniteModuleMaximalIdealAnnihilation.exists_pow_maximalIdeal_smul_finite_eq_zero R Q

private theorem finite_quotient_of_power_maximal_ideal_le (Λ R X : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [IsNoetherianRing Λ]
    [Finite (ResidueField Λ)] [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X] (t : Λ →+* R)
    (ht : ∀ (a : Λ) (x : X), a • x = t a • x) (j : ℕ) (K : Ideal R) (hK : (maximalIdeal Λ).map t ^ j ≤ K) :
    Finite (X ⧸ (K • ⊤ : Submodule R X)) := by
  haveI h0 : Finite (Λ ⧸ maximalIdeal Λ) := ‹Finite (ResidueField Λ)›
  haveI h1 : Finite (Λ ⧸ maximalIdeal Λ ^ j) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) j
  haveI h2 : Finite (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) :=
    Submodule.finite_quotient_smul _ (Module.Finite.fg_top)
  have hle : ∀ x ∈ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X), x ∈ (K • ⊤ : Submodule R X) := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha y _
      rw [ht]
      refine Submodule.smul_mem_smul (hK ?_) Submodule.mem_top
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ ha
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  let g : (X ⧸ (maximalIdeal Λ ^ j • ⊤ : Submodule Λ X)) → (X ⧸ (K • ⊤ : Submodule R X)) := fun q =>
    Quotient.liftOn' q (fun x => Submodule.Quotient.mk x)
      (fun a b h => (Submodule.Quotient.eq _).2 (hle _ ((Submodule.quotientRel_def _).1 h)))
  refine Finite.of_surjective g fun z => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨Submodule.Quotient.mk x, rfl⟩

theorem UpperTheory.V.Pa.Core.finite_quotient_of_ultrafilter_limit_module :
    ∀ (Λ R σ : Type) [CommRing Λ] [IsLocalRing Λ] [CommRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) [IsNoetherianRing Λ] [Finite (ResidueField Λ)] [IsLocalRing R] (U : Ultrafilter ℕ) (f : R) (M : ℕ → Type) [∀ N, AddCommGroup (M N)] [∀ N, Module R (M N)] (X : Type) [AddCommGroup X] [Module R X] [Module Λ X] [Module.Finite Λ X], (∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x) → (∀ a (x : X), s (MvPowerSeries.X a) • x = 0) → (∀ j, ∀ᶠ N in (U : Filter ℕ), ∃ (φ : (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) →ₗ[R] (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N)))) (ψ : (M N ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R (M N))) →ₗ[R] (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))), (∀ z, φ (ψ z) = f • z) ∧ ∀ z, ψ (φ z) = f • z) → ∀ k j : ℕ, ∃ c : ℕ, ∀ᶠ N in (U : Filter ℕ), ∀ a ∈ maximalIdeal R ^ c, ∀ x : M N, (f ^ k * a) • x ∈ ((Ideal.span (Set.range (fun a => s (MvPowerSeries.X a))) ^ k ⊔ ((maximalIdeal Λ).map (s.comp MvPowerSeries.C)) ^ j) • ⊤ : Submodule R (M N)) := by
  intro Λ R σ _ _ _ _ s _ _ _ U f M _ _ X _ _ _ _ hC _ h k j
  have hK := kjMap Λ R σ s 1 j
  haveI : Finite (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X)) :=
    finite_quotient_of_power_maximal_ideal_le Λ R X (s.comp MvPowerSeries.C) hC j _ (hK ▸ le_sup_right)
  obtain ⟨c, hc⟩ := exists_pow_maximalIdeal_smul_finite_eq_zero R (X ⧸ ((kjIdeal Λ σ 1 j).map s • ⊤ : Submodule R X))
  refine ⟨c * k, (h j).mono ?_⟩
  rintro N ⟨φ, ψ, hφψ, -⟩ a ha x
  have h1 : ((Ideal.span {f} * maximalIdeal R ^ c) • ⊤ : Submodule R (M N)) ≤ (kjIdeal Λ σ 1 j).map s • ⊤ := by
    refine Submodule.smul_le.2 ?_
    intro r hr y _
    obtain ⟨b, hb, rfl⟩ := Ideal.mem_span_singleton_mul.1 hr
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, mul_comm, mul_smul, ← hφψ, ← map_smul,
      hc b hb, map_zero]
  rw [hK, pow_one, sup_comm] at h1
  have h2 := (smul_pow_le_of_step R (maximalIdeal R ^ c) _ _ f).2 (M N) h1 k
  rw [sup_comm]
  refine h2 (Submodule.smul_mem_smul (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) ?_) Submodule.mem_top)
  rwa [← pow_mul]
end
end
