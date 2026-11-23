module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMemStatement
public import GroundTheory.LocalFields.HerbrandFunction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulHerbrandPhiNatCastTotallyRamifiedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltrationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRangeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBotStatement
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperModCommutator
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjective
import GroundTheory.LocalFields.SeparableClosure

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemUpperRamificationGroupJumpSumNotMem

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_mem_upperRamificationGroup_jumpSum_not_mem :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L]
      [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
      [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)),
      lowerRamificationGroup F L 0 = ⊤ → B ≠ ⊤ →
        ∃ σ ∈ upperRamificationGroup F L ((jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ)), σ ∉ B := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ B h0 hB
  obtain ⟨hanti, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_initialSegment_not_inf_le_filtration _ (wild F L) ⊤ B hanti hbot
  have hjs := GlobalTheory.T.ramificationJumpSum_eq_sum_range _ (wild F L) ⊤ B n hanti hn
  have hphi := GlobalTheory.T.card_mul_herbrandPhi_natCast_totallyRamified F L h0 n
  simp only [top_inf_eq] at hjs hn
  have hcard : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ) := by
    exact_mod_cast Nat.card_pos
  have hidx : (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ) = herbrandPhi F L n := by
    rw [hjs, ← hphi]
    field_simp
  rw [hidx, upperRamificationGroup_herbrandPhi, lowerRamificationGroupReal_natCast]
  cases n with
  | zero =>
    obtain ⟨σ, hσ⟩ : ∃ σ, σ ∉ B := by
      by_contra h
      push_neg at h
      exact hB (eq_top_iff.mpr fun σ _ => h σ)
    refine ⟨σ, ?_, hσ⟩
    rw [Nat.cast_zero, h0]
    exact Subgroup.mem_top σ
  | succ k =>
    have hk : ¬ wild F L k ≤ B := (hn k).mp (Nat.lt_succ_self k)
    obtain ⟨σ, hσ, hσB⟩ := SetLike.not_le_iff_exists.mp hk
    refine ⟨σ, ?_, hσB⟩
    have : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; rfl
    rw [this]
    exact hσ

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMemUpperRamificationGroupJumpSumNotMemStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.exists_mem_upperRamificationGroup_jumpSum_not_mem' : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → B ≠ ⊤ → ∃ σ ∈ upperRamificationGroup F L ((jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ)), σ ∉ B := by
  first | exact @GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem | exact GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem | (intros; apply GlobalTheory.PMon.Ram.exists_mem_upperRamificationGroup_jumpSum_not_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMemUpperModCommutatorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.exists_upper_mem_inv_mul_pow_mem_of_commutator : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p e : ℕ) (v : ℝ) (C : Subgroup (L ≃ₐ[F] L)), (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → 0 ≤ v → OrdIs F p e → ∀ σ ∈ upperRamificationGroup F L v, ∃ τ ∈ upperRamificationGroup F L (min (2 * v) (v + e)), τ⁻¹ * σ ^ p ∈ C := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator | exact GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator | (intros; apply GlobalTheory.PMon.Ram.pow_mem_upper_mod_commutator <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinJumpSumLeOfPowMemOfInertiaEqTop

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem min_jumpSum_le_of_pow_mem_of_inertia_eq_top : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B C : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) ≤ jumpSum (wild F L) ⊤ C := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E B C h0 hE hcomm hpow
  by_cases hB : B = ⊤
  ·
    subst hB
    have hzero : jumpSum (wild F L) ⊤ (⊤ : Subgroup (L ≃ₐ[F] L)) = 0 := by
      simp [jumpSum]
    simp [hzero]
  ·
    obtain ⟨e, he, hEe, hram⟩ := GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension F L p E hE
    have hcard : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) = Nat.card (L ≃ₐ[F] L) := by
      rw [hram, h0]; simp
    have hnpos : (0 : ℝ) < (Nat.card (L ≃ₐ[F] L) : ℝ) := by
      exact_mod_cast Nat.card_pos

    obtain ⟨σ, hσ, hσB⟩ := GlobalTheory.T.exists_mem_upperRamificationGroup_jumpSum_not_mem' F L B h0 hB
    have hv : (0 : ℝ) ≤ (jumpSum (wild F L) ⊤ B : ℝ) / (Nat.card (L ≃ₐ[F] L) : ℝ) := by
      positivity

    obtain ⟨τ, hτ, hτC⟩ := GlobalTheory.T.exists_upper_mem_inv_mul_pow_mem_of_commutator F L p e _ C hcomm hv he σ hσ

    have hτ' : τ ∉ C := by
      intro hτmem
      apply hσB
      apply hpow
      have hsplit : σ ^ p = τ * (τ⁻¹ * σ ^ p) := by group
      rw [hsplit]
      exact C.mul_mem hτmem hτC
    have key := GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem F L C _ h0 τ hτ hτ'
    have hR : ((min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) : ℕ) : ℝ)
        ≤ (jumpSum (wild F L) ⊤ C : ℝ) := by
      refine le_trans (le_of_eq ?_) key
      rw [mul_min_of_nonneg _ _ hnpos.le, hEe, hcard]
      push_cast
      congr 1
      · field_simp
      · field_simp
    exact_mod_cast hR

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinJumpSumLeOfPowMemOfInertiaEqTopStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.min_jumpSum_le_jumpSum_of_totally_ramified : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B C : Subgroup (L ≃ₐ[F] L)), lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild F L) ⊤ B) (jumpSum (wild F L) ⊤ B + E) ≤ jumpSum (wild F L) ⊤ C := by
  first | exact @GlobalTheory.PMon.Ram.min_jumpSum_le_of_pow_mem_of_inertia_eq_top | exact GlobalTheory.PMon.Ram.min_jumpSum_le_of_pow_mem_of_inertia_eq_top | (intros; apply GlobalTheory.PMon.Ram.min_jumpSum_le_of_pow_mem_of_inertia_eq_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumPowGrowth

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_pow_growth :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B C : Subgroup (L ≃ₐ[K] L)), A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ ∈ A, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild K L) A B) (jumpSum (wild K L) A B + E) ≤ jumpSum (wild K L) A C := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E A B C hA hE hC hB
  obtain ⟨j, hj, hr, -, hG⟩ := GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A
  have hmem : ∀ σ, j σ ∈ A := fun σ => hr.le ⟨σ, rfl⟩
  have hw : wild ↥(IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hG _
  have h0 : lowerRamificationGroup ↥(IntermediateField.fixedField A) L 0 = ⊤ := by
    rw [hG, eq_top_iff]
    intro σ _
    exact hA (hmem σ)
  have key := GlobalTheory.T.min_jumpSum_le_jumpSum_of_totally_ramified ↥(IntermediateField.fixedField A) L p E (B.comap j) (C.comap j) h0 hE
    (fun σ τ => by
      have := hC _ (hmem σ) _ (hmem τ)
      simpa [Subgroup.mem_comap, map_mul, map_inv] using this)
    (fun σ h => by
      have h' : j σ ^ p ∈ C := by simpa [Subgroup.mem_comap, map_pow] using h
      exact hB _ (hmem σ) h')
  rw [hw, jumpSum_comap_injective _ _ j _ B hj, jumpSum_comap_injective _ _ j _ C hj, hr] at key
  exact key

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumPowGrowthStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.ramificationJumpSum_pow_growth : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E : ℕ) (A B C : Subgroup (L ≃ₐ[K] L)), A ≤ lowerRamificationGroup K L 0 → OrdIs L p E → (∀ σ ∈ A, ∀ τ ∈ A, σ * τ * σ⁻¹ * τ⁻¹ ∈ C) → (∀ σ ∈ A, σ ^ p ∈ C → σ ∈ B) → min (2 * jumpSum (wild K L) A B) (jumpSum (wild K L) A B + E) ≤ jumpSum (wild K L) A C := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_pow_growth | exact GlobalTheory.PMon.Ram.jumpSum_pow_growth | (intros; apply GlobalTheory.PMon.Ram.jumpSum_pow_growth <;> assumption)
end
end
