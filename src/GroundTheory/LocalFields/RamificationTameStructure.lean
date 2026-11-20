import Mathlib
import GroundTheory.LocalFields.RamificationTame
import GroundTheory.LocalFields.UnramifiedHensel

noncomputable section

open scoped IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem exists_tame_structure (he : Nat.Coprime ((_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K)))) (ringChar 𝓀[K])) :
    ∃ T : IntermediateField K L, IsUnramified K T ∧
      Module.finrank K T = ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[K])) ∧ ((IsLocalRing.maximalIdeal 𝒪[L]).inertiaDeg (𝒪[T])) = 1 ∧
      (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation T))) = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) ∧
      Module.finrank T L = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) ∧
      ∃ π : 𝒪[T], Irreducible π ∧ ∃ α : 𝒪[L], Irreducible α ∧
        α ^ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = algebraMap 𝒪[T] 𝒪[L] π ∧ T⟮(α : L)⟯ = ⊤ := by
  obtain ⟨β, -, -, -, -, hun, hdeg, hres⟩ := exists_unramified_adjoin K L
  set T := K⟮(β : L)⟯
  obtain ⟨htow, hrest⟩ := exists_pow_eq_uniformizer_of_isUnramified T hres he
  have hfin : Module.finrank T L = (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) := by
    have := ramificationIndex_mul_residueDegree T L
    rw [hres, mul_one, htow] at this
    exact this.symm
  exact ⟨T, hun, hdeg, hres, htow, hfin, hrest⟩

end GroundTheory.LocalField
