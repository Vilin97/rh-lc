module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Trace.Defs
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
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Flat.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfMaximalIdealPowOfLocallySurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfTraceOfSmulMemRangeStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraTraceMapOfCokernelKilledByScalar

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem algebraTrace_map_of_cokernel_killed (S A B : Type) [CommRing S] [IsDomain S] [CommRing A]
    [Algebra S A] [Module.Free S A] [Module.Finite S A] [CommRing B] [Algebra S B]
    [Module.Free S B] [Module.Finite S B] (φ : A →ₐ[S] B) (hφ : Function.Injective φ)
    (s : S) (hs : s ≠ 0) (hr : ∀ b : B, s • b ∈ φ.range) (x : A) :
    Algebra.trace S B (φ x) = Algebra.trace S A x := by
  classical
  choose g hg using fun b => (AlgHom.mem_range φ).1 (hr b)
  let gl : B →ₗ[S] A :=
    { toFun := g
      map_add' := by
        intro b c
        apply hφ
        rw [map_add (f := _), hg, hg, hg, smul_add]
      map_smul' := by
        intro r b
        apply hφ
        rw [hg, RingHom.id_apply, map_smul, hg, smul_comm] }
  have h1 : φ.toLinearMap ∘ₗ gl = s • LinearMap.id := by
    ext b
    simp [gl, hg]
  have h2 : gl ∘ₗ φ.toLinearMap = s • LinearMap.id := by
    ext a
    apply hφ
    simp [gl, hg]
  have h3 : Algebra.lmul S B (φ x) ∘ₗ φ.toLinearMap = φ.toLinearMap ∘ₗ Algebra.lmul S A x := by
    ext a
    simp
  have key : s * Algebra.trace S B (φ x) = s * Algebra.trace S A x := by
    rw [Algebra.trace_apply, Algebra.trace_apply]
    calc s * LinearMap.trace S B (Algebra.lmul S B (φ x))
        = LinearMap.trace S B (Algebra.lmul S B (φ x) ∘ₗ (φ.toLinearMap ∘ₗ gl)) := by
          rw [h1, LinearMap.comp_smul, LinearMap.comp_id, map_smul, smul_eq_mul]
      _ = LinearMap.trace S B (φ.toLinearMap ∘ₗ (Algebra.lmul S A x ∘ₗ gl)) := by
          rw [← LinearMap.comp_assoc, h3, LinearMap.comp_assoc]
      _ = LinearMap.trace S A ((Algebra.lmul S A x ∘ₗ gl) ∘ₗ φ.toLinearMap) := by
          rw [LinearMap.trace_comp_comm']
      _ = s * LinearMap.trace S A (Algebra.lmul S A x) := by
          rw [LinearMap.comp_assoc, h2, LinearMap.comp_smul, LinearMap.comp_id, map_smul,
            smul_eq_mul]
  exact mul_left_cancel₀ hs key

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraTraceMapOfCokernelKilledByScalarStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.algebra_trace_map_of_cokernel_killed_by_scalar : ∀ (S A B : Type) [CommRing S] [IsDomain S] [CommRing A] [Algebra S A] [Module.Free S A] [Module.Finite S A] [CommRing B] [Algebra S B] [Module.Free S B] [Module.Finite S B] (φ : A →ₐ[S] B), Function.Injective φ → ∀ s : S, s ≠ 0 → (∀ b : B, s • b ∈ φ.range) → ∀ x : A, Algebra.trace S B (φ x) = Algebra.trace S A x := by
  first | exact @GlobalTheory.algebraTrace_map_of_cokernel_killed | exact GlobalTheory.algebraTrace_map_of_cokernel_killed | (intros; apply GlobalTheory.algebraTrace_map_of_cokernel_killed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemRangeOfSurjectiveLocalizedMap

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem exists_smul_mem_range_of_surjective_localization_map
    (R A B : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B)
    (hs : Function.Surjective (Algebra.TensorProduct.map
      (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ)) :
    ∀ b : B, ∃ t ∉ p, t • b ∈ ψ.range := by
  intro b
  classical
  set L := Localization.AtPrime p
  set N : Submodule R B := LinearMap.range ψ.toLinearMap
  let π := N.mkQ
  let g : L ⊗[R] B →ₗ[R] L ⊗[R] (B ⧸ N) := LinearMap.lTensor L π
  obtain ⟨z, hz⟩ := hs ((1 : L) ⊗ₜ[R] b)
  have key : ∀ w : L ⊗[R] A, g (Algebra.TensorProduct.map
      (AlgHom.id L L) ψ w) = 0 := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul]
      simp only [g, LinearMap.lTensor_tmul]
      have : π (ψ y) = 0 := by
        simp only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨y, rfl⟩
      rw [this, TensorProduct.tmul_zero]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  have h0 : (TensorProduct.mk R L (B ⧸ N) 1) (π b) = 0 := by
    have := key z
    rw [hz] at this
    simpa [g] using this
  have hloc : IsLocalizedModule p.primeCompl (TensorProduct.mk R L (B ⧸ N) 1) :=
    (isLocalizedModule_iff_isBaseChange p.primeCompl L _).mpr (TensorProduct.isBaseChange R _ L)
  obtain ⟨s, hs'⟩ := (IsLocalizedModule.eq_zero_iff p.primeCompl _).mp h0
  refine ⟨s, s.2, ?_⟩
  have : π ((s : R) • b) = 0 := by
    rw [map_smul]; exact hs'
  simp only [π, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, N] at this
  obtain ⟨a, ha⟩ := this
  exact ⟨a, ha⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemRangeOfSurjectiveLocalizedMapStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.exists_smul_mem_range_of_surjective_localized_map : ∀ (R A B : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B), Function.Surjective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) → ∀ b : B, ∃ t ∉ p, t • b ∈ ψ.range := by
  exact @GlobalTheory.exists_smul_mem_range_of_surjective_localization_map
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationTensorMapInjectiveCokerKilled

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory

theorem localization_map_injective_coker_killed (R A B : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B) :
    Function.Injective ψ → ∀ s : R, s ≠ 0 → (∀ b : B, s • b ∈ ψ.range) →
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) ∧
      algebraMap R (Localization.AtPrime p) s ≠ 0 ∧
      ∀ y : Localization.AtPrime p ⊗[R] B, algebraMap R (Localization.AtPrime p) s • y ∈
        (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ).range := by
  intro hψ s hs hrange
  set L := Localization.AtPrime p
  refine ⟨?_, ?_, ?_⟩
  · have heq : ((Algebra.TensorProduct.map (AlgHom.id L L) ψ).toLinearMap.restrictScalars R) =
        LinearMap.lTensor L ψ.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      simp
    have : Function.Injective (LinearMap.lTensor L ψ.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hψ
    rw [← heq] at this
    exact this
  · intro h0
    apply hs
    have hinj : Function.Injective (algebraMap R L) :=
      IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors p)
    exact hinj (by rw [h0, map_zero])
  · intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      obtain ⟨a, ha⟩ := hrange b
      refine ⟨t ⊗ₜ a, ?_⟩
      have ha' : ψ a = s • b := ha
      change Algebra.TensorProduct.map (AlgHom.id L L) ψ (t ⊗ₜ a) = _
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ha', TensorProduct.smul_tmul', algebraMap_smul,
        TensorProduct.smul_tmul]
    | add x y hx hy =>
      rw [smul_add]
      exact Subalgebra.add_mem _ hx hy

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationTensorMapInjectiveCokerKilledStatement

section

@[expose] public section

open IsLocalRing TensorProduct

theorem _root_.GlobalTheory.T.localization_tensor_map_injective_coker_killed : ∀ (R A B : Type) [CommRing R] [IsDomain R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (p : Ideal R) [p.IsPrime] (ψ : A →ₐ[R] B), Function.Injective ψ → ∀ s : R, s ≠ 0 → (∀ b : B, s • b ∈ ψ.range) → Function.Injective (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ) ∧ algebraMap R (Localization.AtPrime p) s ≠ 0 ∧ ∀ y : Localization.AtPrime p ⊗[R] B, algebraMap R (Localization.AtPrime p) s • y ∈ (Algebra.TensorProduct.map (AlgHom.id (Localization.AtPrime p) (Localization.AtPrime p)) ψ).range := by
  first | exact @GlobalTheory.localization_map_injective_coker_killed | exact GlobalTheory.localization_map_injective_coker_killed | (intros; apply GlobalTheory.localization_map_injective_coker_killed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLengthCokerOfEtalePuncturedSpectrum

section

@[expose] public section

open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleCoker

theorem main : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] (A B : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] [Module.Finite R B], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B)) → ∀ ψ : A →ₐ[R] B, Function.Injective ψ → (∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ ψ.range := by
  intro R _ _ _ _ A B _ _ _ _ _ _ hA hB ψ hψ ⟨s, hs, hsb⟩
  obtain ⟨k, hk⟩ := GlobalTheory.T.smul_mem_of_maximalIdeal_pow_of_locally_surjective R B (ψ.range.toSubmodule.restrictScalars R) (fun p hp hpm => by
    haveI := hp
    haveI := hA p hpm
    haveI := hB p hpm
    let S := Localization.AtPrime p
    haveI : Module.Free S (S ⊗[R] A) := Module.free_of_flat_of_isLocalRing
    haveI : Module.Free S (S ⊗[R] B) := Module.free_of_flat_of_isLocalRing
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.localization_tensor_map_injective_coker_killed R A B p ψ hψ s hs hsb
    have htr := GlobalTheory.T.algebra_trace_map_of_cokernel_killed_by_scalar S _ _ _ h1 _ h2 h3
    exact GlobalTheory.T.exists_smul_mem_range_of_surjective_localized_map R A B p ψ (GlobalTheory.T.surjective_of_injective_of_trace_eq_of_smul_mem_range S _ _ _ h1 _ h2 h3 htr))
  exact ⟨k, fun x hx b => hk x hx b⟩

end GlobalTheory.EtaleCoker
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteLengthCokerOfEtalePuncturedSpectrumStatement

section

@[expose] public section

open IsLocalRing

theorem _root_.GlobalTheory.T.finiteLength_coker_of_etale_punctured_spectrum : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] (A B : Type) [CommRing A] [Algebra R A] [Module.Finite R A] [CommRing B] [Algebra R B] [Module.Finite R B], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) B)) → ∀ ψ : A →ₐ[R] B, Function.Injective ψ → (∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range) → ∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, x • b ∈ ψ.range := by
  first | (exact @GlobalTheory.EtaleCoker.main) | (exact GlobalTheory.EtaleCoker.main) | (intros; apply GlobalTheory.EtaleCoker.main  <;> assumption)
end
end
