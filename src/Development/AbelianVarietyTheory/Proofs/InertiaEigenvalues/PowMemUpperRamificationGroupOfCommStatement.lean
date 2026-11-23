module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import GroundTheory.LocalFields.HerbrandFunction
public import GroundTheory.LocalFields.SeparableClosure
public import Mathlib.FieldTheory.Galois.Abelian
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeAndRangePowLe
public import GroundTheory.LocalFields.UnramifiedHensel
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.ConductorReciprocity
import GroundTheory.LocalFields.ConductorTransport
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeMemUnitFiltrationUnitsMin

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_one_add_pow_eq {R : Type*} [CommRing R] (y : R) (k : ℕ) :
    ∃ w : R, (1 + y) ^ k = 1 + (k : R) * y + y ^ 2 * w := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(1 + y) * w + k, ?_⟩
    rw [pow_succ, hw]; push_cast; ring

theorem one_add_pow_sub_one_mem {R : Type*} [CommRing R] (I : Ideal R) {n e k : ℕ} {y : R}
    (hy : y ∈ I ^ n) (hk : (k : R) ∈ I ^ e) :
    (1 + y) ^ k - 1 ∈ I ^ min (2 * n) (n + e) := by
  obtain ⟨w, hw⟩ := exists_one_add_pow_eq y k
  have h : (1 + y) ^ k - 1 = (k : R) * y + y ^ 2 * w := by rw [hw]; ring
  rw [h]
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.pow_le_pow_right (min_le_right _ _) ?_
    rw [add_comm n e, pow_add]
    exact Ideal.mul_mem_mul hk hy
  · refine Ideal.pow_le_pow_right (min_le_left _ _) ?_
    refine Ideal.mul_mem_right _ _ ?_
    rw [two_mul, pow_add, pow_two]
    exact Ideal.mul_mem_mul hy hy

theorem natCast_mem_maximalIdeal_pow_of_ordIs {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {p e : ℕ} (h : OrdIs F p e) : (p : 𝒪[F]) ∈ 𝓂[F] ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ]
  rw [OrdIs] at h
  rw [h]
  simp

theorem pow_mem_unitFiltrationUnits (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p e n : ℕ) (hp : OrdIs F p e) :
    ∀ x ∈ unitFiltrationUnits F n, x ^ p ∈ unitFiltrationUnits F (min (2 * n) (n + e)) := by
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨u ^ p, ?_, by simp⟩
  rw [SetLike.mem_coe, mem_unitFiltration] at hu ⊢
  have := one_add_pow_sub_one_mem (𝓂[F]) hu (natCast_mem_maximalIdeal_pow_of_ordIs hp)
  simpa using this

end GlobalTheory.PMon.Ram

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeMemUnitFiltrationUnitsMinStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.pow_prime_mem_unitFiltrationUnits_min : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p e n : ℕ), OrdIs F p e → ∀ x ∈ unitFiltrationUnits F n, x ^ p ∈ unitFiltrationUnits F (min (2 * n) (n + e)) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits | exact GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits | (intros; apply GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupAbelianNat

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_abelian_nat :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
      (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e n : ℕ),
      OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M (n : ℝ),
        σ ^ p ∈ upperRamificationGroup F ↥M ((min (2 * n) (n + e) : ℕ) : ℝ) := by
  intro F _ _ _ _ M _ _ p e n h σ hσ
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap (Ω := SeparableClosure F) M n] at hσ
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hσ
  rw [← map_unitFiltrationUnits_restrictAb_localArtinMap (Ω := SeparableClosure F) M
    (min (2 * n) (n + e)), ← map_pow]
  exact Subgroup.mem_map_of_mem _ (GlobalTheory.T.pow_prime_mem_unitFiltrationUnits_min F p e n h x hx)

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupAbelianNatStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_nat' : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e n : ℕ), OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M (n : ℝ), σ ^ p ∈ upperRamificationGroup F ↥M ((min (2 * n) (n + e) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_abelian_nat | exact GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_abelian_nat | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_abelian_nat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupReal

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_real : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e : ℕ) (v : ℝ), 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M v, σ ^ p ∈ upperRamificationGroup F ↥M (min (2 * v) (v + e)) := by
  intro F _ _ _ _ M _ _ p e v hv hOrd σ hσ

  have hc : (0 : ℤ) ≤ ⌈v⌉ := Int.ceil_nonneg hv
  have hn : ((⌈v⌉.toNat : ℕ) : ℝ) = ((⌈v⌉ : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hc
  have hσn : σ ∈ upperRamificationGroup F ↥M ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn, ← upperRamificationGroup_eq_ceil]
    exact hσ
  have hpow := GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_nat' F M p e ⌈v⌉.toNat hOrd σ hσn

  have hvn : v ≤ ((⌈v⌉.toNat : ℕ) : ℝ) := by
    rw [hn]; exact Int.le_ceil v
  have hle : min (2 * v) (v + e) ≤ ((min (2 * ⌈v⌉.toNat) (⌈v⌉.toNat + e) : ℕ) : ℝ) := by
    push_cast
    exact min_le_min (by linarith) (by linarith)
  exact upperRamificationGroup_antitone F ↥M hle hpow

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupRealStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_real : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (M : IntermediateField F (SeparableClosure F)) [FiniteDimensional F ↥M] [IsAbelianGalois F ↥M] (p e : ℕ) (v : ℝ), 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F ↥M v, σ ^ p ∈ upperRamificationGroup F ↥M (min (2 * v) (v + e)) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_real | exact GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_real | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_real <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupOfComm

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem pow_mem_upperRamificationGroup_of_comm : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ) (v : ℝ), (∀ σ τ : M ≃ₐ[F] M, σ * τ = τ * σ) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F M v, σ ^ p ∈ upperRamificationGroup F M (min (2 * v) (v + e)) := by
  intro F M _ _ _ _ _ _ _ _ _ _ _ _ p e v hcomm hv hord σ hσ

  let f : M →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let φ : M ≃ₐ[F] f.fieldRange := f.equivFieldRange
  haveI : FiniteDimensional F f.fieldRange := LinearEquiv.finiteDimensional φ.toLinearEquiv
  haveI : IsMulCommutative (M ≃ₐ[F] M) := ⟨⟨hcomm⟩⟩
  haveI : IsAbelianGalois F M := IsAbelianGalois.mk
  haveI : IsAbelianGalois F f.fieldRange := IsAbelianGalois.of_algHom φ.symm.toAlgHom

  have h1 : φ.autCongr σ ∈ upperRamificationGroup F f.fieldRange v := by
    rw [← map_upperRamificationGroup_autCongr φ v]
    exact ⟨σ, hσ, rfl⟩
  have h2 := GlobalTheory.T.pow_mem_upperRamificationGroup_abelian_real F f.fieldRange p e v hv hord _ h1
  rw [← map_upperRamificationGroup_autCongr φ] at h2
  obtain ⟨τ, hτ, hτσ⟩ := h2
  have hτ' : τ = σ ^ p := φ.autCongr.injective (by simpa [map_pow] using hτσ)
  exact hτ' ▸ hτ

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperRamificationGroupOfCommStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.pow_mem_upperRamificationGroup_of_comm' : ∀ (F M : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M] [Algebra F M] [ValuativeExtension F M] [FiniteDimensional F M] [IsGalois F M] (p e : ℕ) (v : ℝ), (∀ σ τ : M ≃ₐ[F] M, σ * τ = τ * σ) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F M v, σ ^ p ∈ upperRamificationGroup F M (min (2 * v) (v + e)) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm | exact GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upperRamificationGroup_of_comm <;> assumption)
end
end
