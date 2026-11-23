module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRham
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCohomologyProjectiveModuleStatement
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.WittVector.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Teichmuller
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.Unramified.Field
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveReductionOfFlatLiftStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRhamStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.crystal_finite_free_reduces_to_deRham : ∀ (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (hπ : Function.Surjective π) (hI : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (divided₂ hI) (spMap π) a; letI := tensorModule (dp0 k) (𝟙 _) a; Module.Finite Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ Module.Free Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ ∃ f : Crys (divided₂ hI) (spMap π) A₀ →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] HdR A₀, Function.Surjective f ∧ ∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ (Crys (divided₂ hI) (spMap π) A₀)) := by
  first | exact @GlobalTheory.CrysFree.crys_free_and_red | exact GlobalTheory.CrysFree.crys_free_and_red | (intros; apply GlobalTheory.CrysFree.crys_free_and_red <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatLiftModPSqPerfectField

section

@[expose] public section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem wittVector_dvd_of_coeff_zero_eq_zero (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (a : WittVector p k) (ha : a.coeff 0 = 0) :
    (p : WittVector p k) ∣ a := by
  by_cases h0 : a = 0
  · exact h0 ▸ dvd_zero _
  obtain ⟨m, b, hb, rfl⟩ := WittVector.exists_eq_pow_p_mul a h0
  cases m with
  | zero =>
    exfalso
    simp only [pow_zero, one_mul] at ha
    exact hb ha
  | succ n => exact ⟨(p : WittVector p k) ^ n * b, by ring⟩

theorem wittVector_natCast_ne_zero (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] : (p : WittVector p k) ≠ 0 := by
  intro h
  have := WittVector.coeff_p_pow p k 1
  rw [pow_one, h] at this
  simp at this

theorem exists_flat_lift_mod_p_sq : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectField k], ∃ (Λ : Type) (_ : CommRing Λ) (π : Λ →+* k), Function.Surjective π ∧
      RingHom.ker π = Ideal.span {(p : Λ)} ∧ (p : Λ) ^ 2 = 0 ∧
      ∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)} := by
  intro p _ k _ _ _
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  set I : Ideal (WittVector p k) := Ideal.span {(p : WittVector p k) ^ 2} with hI
  have hlift : ∀ a ∈ I, WittVector.constantCoeff a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp ha
    simp [map_mul, map_pow, map_natCast, CharP.cast_eq_zero]
  let π : (WittVector p k ⧸ I) →+* k := Ideal.Quotient.lift I WittVector.constantCoeff hlift
  have hπ : ∀ a, π (Ideal.Quotient.mk I a) = a.coeff 0 := by
    intro a
    simp [π, Ideal.Quotient.lift_mk, WittVector.constantCoeff_apply]
  have hp0 : π (p : WittVector p k ⧸ I) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero k p
  refine ⟨WittVector p k ⧸ I, inferInstance, π, ?_, ?_, ?_, ?_⟩
  · intro r
    refine ⟨Ideal.Quotient.mk I (WittVector.teichmuller p r), ?_⟩
    rw [hπ, WittVector.teichmuller_coeff_zero]
  · ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, hπ, Ideal.mem_span_singleton]
    constructor
    · intro ha
      obtain ⟨c, rfl⟩ := wittVector_dvd_of_coeff_zero_eq_zero p k a ha
      exact ⟨Ideal.Quotient.mk I c, by rw [map_mul, map_natCast]⟩
    · rintro ⟨c, hc⟩
      rw [← hπ, hc, map_mul, hp0, zero_mul]
  · rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_natCast (Ideal.Quotient.mk I), ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at hx
    obtain ⟨c, hc⟩ := hx
    have hpne := wittVector_natCast_ne_zero p k
    have hac : a = (p : WittVector p k) * c := by
      apply mul_left_cancel₀ hpne
      rw [hc]; ring
    rw [Ideal.mem_span_singleton]
    exact ⟨Ideal.Quotient.mk I c, by rw [hac, map_mul, map_natCast]⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlatLiftModPSqPerfectFieldStatement

section

@[expose] public section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_flat_lift_mod_p_sq_perfect_field : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectField k], ∃ (Λ : Type) (_ : CommRing Λ) (π : Λ →+* k), Function.Surjective π ∧ RingHom.ker π = Ideal.span {(p : Λ)} ∧ (p : Λ) ^ 2 = 0 ∧ ∀ x : Λ, (p : Λ) * x = 0 → x ∈ Ideal.span {(p : Λ)} := by
  first | exact @GlobalTheory.exists_flat_lift_mod_p_sq | exact GlobalTheory.exists_flat_lift_mod_p_sq | (intros; apply GlobalTheory.exists_flat_lift_mod_p_sq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveCharZeroTensorRingOfIntegers

section

@[expose] public section

open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem isReduced_charZero_tensor_ringOfIntegers (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] : IsReduced (k ⊗[ℤ] 𝓞 F) := by
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℤ F := Algebra.FormallyUnramified.comp ℤ ℚ F
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ ℚ F
  haveI : IsReduced (k ⊗[ℤ] F) := Algebra.FormallyUnramified.isReduced_of_field k (k ⊗[ℤ] F)
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℤ k) (IsScalarTower.toAlgHom ℤ (𝓞 F) F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  exact isReduced_of_injective _ hinj

instance isSemisimpleRing_charZero_tensor_ringOfIntegers (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] : IsSemisimpleRing (k ⊗[ℤ] 𝓞 F) := by
  haveI := isReduced_charZero_tensor_ringOfIntegers F k
  haveI : IsArtinianRing (k ⊗[ℤ] 𝓞 F) := IsArtinianRing.of_finite k _
  exact IsArtinianRing.isSemisimpleRing_of_isReduced _

theorem projective_charZero_tensor_ringOfIntegers : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k]
    [CharZero k] (M : Type 1) [AddCommGroup M] [Module (k ⊗[ℤ] 𝓞 F) M], Module.Projective (k ⊗[ℤ] 𝓞 F) M := by
  intro F _ _ k _ _ M _ _
  exact Module.projective_of_isSemisimpleRing _ _

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveCharZeroTensorRingOfIntegersStatement

section

@[expose] public section

open NumberField
open scoped TensorProduct

theorem _root_.GlobalTheory.T.projective_charZero_tensor_ringOfIntegers' : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k] [CharZero k] (M : Type 1) [AddCommGroup M] [Module (k ⊗[ℤ] 𝓞 F) M], Module.Projective (k ⊗[ℤ] 𝓞 F) M := by
  first | exact @GlobalTheory.projective_charZero_tensor_ringOfIntegers | exact GlobalTheory.projective_charZero_tensor_ringOfIntegers | (intros; apply GlobalTheory.projective_charZero_tensor_ringOfIntegers <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstDeRhamHomologyProjectiveOverTensorIntegers

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CrysProj

theorem hdR_projective : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (dp0 k) (𝟙 _) a; Module.Projective (k ⊗[ℤ] 𝓞 F) (HdR A₀) := by
  intro F _ _ k _ A₀ _ _ hA a
  rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp
  · haveI : Fact (ringChar k).Prime := ⟨hp⟩
    refine GlobalTheory.T.de_rham_cohomology_projective_module F k ?_ A₀ hA a
    intro B₀ _ _ hB b
    set K := AlgebraicClosure k
    haveI : CharP K (ringChar k) := charP_of_injective_algebraMap (algebraMap k K).injective _
    obtain ⟨Λ, _, π, hπ, hker, hp2, hann⟩ := GlobalTheory.T.exists_flat_lift_mod_p_sq_perfect_field (ringChar k) K
    have hI : RingHom.ker π ^ 2 = 0 := by
      rw [hker, Ideal.span_singleton_pow, hp2, Ideal.span_singleton_eq_bot.2 rfl]; rfl
    obtain ⟨hfin, hfree, f, hf, hk⟩ := GlobalTheory.T.crystal_finite_free_reduces_to_deRham F Λ K π hπ hI B₀ hB b
    letI := tensorModule (divided₂ hI) (spMap π) b
    haveI := isScalarTower_tensorModule (divided₂ hI) (spMap π) b
    letI := tensorModule (dp0 K) (𝟙 _) b
    exact GlobalTheory.T.projective_of_surjective_ker_le_smul (ringChar k) F Λ K π hπ hker hp2 hann _ hfin hfree _ f hf hk
  · haveI : CharP k 0 := hp ▸ ringChar.charP k
    haveI : CharZero k := CharP.charP_to_charZero k
    letI := tensorModule (dp0 k) (𝟙 _) a
    exact GlobalTheory.T.projective_charZero_tensor_ringOfIntegers' F k _

end GlobalTheory.CrysProj
end
end
