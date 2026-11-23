module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisGroupFixedFieldBaseChangeLocalFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInitialSegmentNotInfLeFiltrationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpSumKernelCoboundaryCharLeSixMulStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumEqSumRangeStatement
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildLowerRamificationGroupAntitoneEventuallyBotStatement
import Mathlib.Tactic.ENatToNat
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumMonoOfLe

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram


open Classical in
theorem jumpSum_mono_of_le :
    ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) →
      (∀ t, A ⊓ R t ≤ C → A ⊓ R t ≤ B) → jumpSum R A B ≤ jumpSum R A C := by
  intro G _ R A B C hR ⟨m, hm⟩ hBC
  have hbot : ∀ t, m ≤ t → ∀ D : Subgroup G, A ⊓ R t ≤ D := by
    intro t ht D
    have : R t ≤ ⊥ := hm ▸ hR ht
    exact le_trans inf_le_right (le_trans this bot_le)
  have hfin : ∀ D : Subgroup G,
      (Function.support fun t : ℕ => if A ⊓ R t ≤ D then 0 else Nat.card ↥(A ⊓ R t)) ⊆ ↑(Finset.range m) := by
    intro D
    intro t ht
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    apply ht
    simp [hbot t (not_lt.mp h) D]
  unfold jumpSum
  rw [finsum_eq_sum_of_support_subset _ (hfin B), finsum_eq_sum_of_support_subset _ (hfin C)]
  apply Finset.sum_le_sum
  intro t _
  by_cases hC : A ⊓ R t ≤ C
  · simp [hBC t hC]
  · rw [if_neg hC]
    split_ifs <;> simp

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumMonoOfLeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.ramificationJumpSum_mono_of_le : ∀ (G : Type) [Group G] (R : ℕ → Subgroup G) (A B C : Subgroup G), Antitone R → (∃ m, R m = ⊥) → (∀ t, A ⊓ R t ≤ C → A ⊓ R t ≤ B) → jumpSum R A B ≤ jumpSum R A C := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_mono_of_le | exact GlobalTheory.PMon.Ram.jumpSum_mono_of_le | (intros; apply GlobalTheory.PMon.Ram.jumpSum_mono_of_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfCoboundaryDetects

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_wild_top_le_of_detects : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → Detects p r ⊤ B → jumpSum (wild F L) ⊤ B ≤ 6 * E := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E r B hp hE hord hax hdet
  obtain ⟨hanti, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_initialSegment_not_inf_le_filtration _ (wild F L) ⊤ B hanti hbot
  rcases n with _ | k
  · rw [GlobalTheory.T.ramificationJumpSum_eq_sum_range _ (wild F L) ⊤ B 0 hanti hn]
    simp
  · have hk : ¬ (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L k ≤ B := (hn k).1 (Nat.lt_succ_self k)
    obtain ⟨σ₀, hσ₀, hσ₀B⟩ := SetLike.not_le_iff_exists.1 hk
    have hσ₀k : σ₀ ∈ wild F L k := (Subgroup.mem_inf.1 hσ₀).2
    obtain ⟨x, a, hxa, hnd⟩ := hdet σ₀ (Subgroup.mem_top σ₀) hσ₀B
    obtain ⟨J, hJ, hJsum⟩ := GlobalTheory.T.jumpSum_kernel_coboundaryChar_le_six_mul F L p E r x a hp hE hord hax
      (fun σ => hxa σ (Subgroup.mem_top σ)) ⟨σ₀, hnd⟩
    have hσ₀J : σ₀ ∉ J := fun h => hnd ((hJ σ₀).1 h)
    have hmono : ∀ t, (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L t ≤ J → (⊤ : Subgroup (L ≃ₐ[F] L)) ⊓ wild F L t ≤ B := by
      intro t ht
      by_contra hB
      have htk : t ≤ k := Nat.lt_succ_iff.1 ((hn t).2 hB)
      have hσ₀t : σ₀ ∈ wild F L t := hanti htk hσ₀k
      exact hσ₀J (ht (Subgroup.mem_inf.2 ⟨Subgroup.mem_top σ₀, hσ₀t⟩))
    exact le_trans (GlobalTheory.T.ramificationJumpSum_mono_of_le _ (wild F L) ⊤ B J hanti hbot hmono) hJsum

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfCoboundaryDetectsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.wild_jumpSum_le_of_coboundary_detects : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E r : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E → OrdIs L p E → AxIn F L p → Detects p r ⊤ B → jumpSum (wild F L) ⊤ B ≤ 6 * E := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_wild_top_le_of_detects | exact GlobalTheory.PMon.Ram.jumpSum_wild_top_le_of_detects | (intros; apply GlobalTheory.PMon.Ram.jumpSum_wild_top_le_of_detects <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfDetectingCoboundaryCharacters

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_le_of_detects : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Detects p r A B → jumpSum (wild K L) A B ≤ 6 * E := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ p E r A B hp hE hord hax hdet
  obtain ⟨j, hinj, hrange, happ, hram⟩ := GlobalTheory.T.galoisGroup_fixedField_baseChange_localField K L A

  have haxF : AxIn (IntermediateField.fixedField A) L p := by
    intro J x hx
    obtain ⟨y, hy, hxy⟩ := hax (J.map j) x (by
      rintro σ ⟨τ, hτ, rfl⟩
      rw [happ]
      exact hx τ hτ)
    refine ⟨y, fun τ hτ => ?_, hxy⟩
    rw [← happ]
    exact hy (j τ) ⟨τ, hτ, rfl⟩
  have hdetF : Detects p r ⊤ (B.comap j) := by
    intro τ₀ _ hτ₀
    have hA : j τ₀ ∈ A := hrange.le (MonoidHom.mem_range.mpr ⟨τ₀, rfl⟩)
    obtain ⟨x, a, hxa, hnd⟩ := hdet (j τ₀) hA hτ₀
    refine ⟨x, fun τ => a (j τ), fun τ _ => ?_, hnd⟩
    obtain ⟨z, hz, hzx⟩ := hxa (j τ) (hrange.le (MonoidHom.mem_range.mpr ⟨τ, rfl⟩))
    refine ⟨z, hz, ?_⟩
    rw [← happ]
    exact hzx
  have key := GlobalTheory.T.wild_jumpSum_le_of_coboundary_detects (IntermediateField.fixedField A) L p E r (B.comap j) hp hE hord haxF hdetF
  have hwild : wild (IntermediateField.fixedField A) L = fun t => (wild K L t).comap j := by
    funext t
    exact hram _
  rw [hwild, jumpSum_comap_injective _ _ j _ B hinj, hrange] at key
  exact key

end GlobalTheory.PMon.Ram
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildJumpSumLeOfDetectingCoboundaryCharactersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

theorem _root_.GlobalTheory.T.wildJumpSum_le_of_detecting_coboundary_characters : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L] (p E r : ℕ) (A B : Subgroup (L ≃ₐ[K] L)), p.Prime → 0 < E → OrdIs L p E → AxIn K L p → Detects p r A B → jumpSum (wild K L) A B ≤ 6 * E := by
  first | exact @GlobalTheory.PMon.Ram.jumpSum_le_of_detects | exact GlobalTheory.PMon.Ram.jumpSum_le_of_detects | (intros; apply GlobalTheory.PMon.Ram.jumpSum_le_of_detects <;> assumption)
end
end
