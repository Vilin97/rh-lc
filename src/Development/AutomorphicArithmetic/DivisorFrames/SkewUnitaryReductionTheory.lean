module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
public import Development.AutomorphicArithmetic.LocalEmbeddings.LeviRedDef

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

section
open GlobalTheory.LeviRed
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem absE_rE (h : IsCMExt F E σ) {s : ℝ} (hs : 0 < s) (u : (AF F ⊗[F] E)ˣ) (hu : u.1 = rE F E s) :
    (GlobalTheory.Doubling.absE F E u : ℝ) = s ^ (2 * Fintype.card (InfinitePlace F)) := by
  have hN : Algebra.norm (AF F) u.1 = GlobalTheory.TorusTheta.infScale F s ^ 2 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    haveI : Nontrivial (AF F) := (evInf F w).toRingHom.domain_nontrivial
    rw [hu, rE, Algebra.norm_algebraMap, Module.finrank_baseChange, h.2.2.1]
  have hfin : ∀ v, GlobalTheory.Doubling.absEv F E v (GlobalTheory.Doubling.unitFin F E v u) = 1 := fun v => by
    have : evFin F v (GlobalTheory.TorusTheta.infScale F s) = 1 := rfl
    rw [GlobalTheory.Doubling.absEv_unitFin, hN, map_pow, this]
    simp
  have hinf : ∀ w, (GlobalTheory.Doubling.absEw F E w (GlobalTheory.Doubling.unitInf F E w u) : ℝ) = s ^ 2 := fun w => by
    obtain ⟨τ⟩ := (inferInstance : Nonempty (EmbOver E w))
    have e : infEmb τ (GlobalTheory.Doubling.unitInf F E w u).1 = s := by
      rw [← GlobalTheory.TorusMat.piInf_infScale h τ s]
      change infEmb τ (compInf F E w u.1) = _
      rw [hu]
      rfl
    rw [GlobalTheory.Doubling.absEw_eq_sq h τ, e, NNReal.coe_pow, coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg hs.le]
  rw [GlobalTheory.Doubling.absE_apply, finprod_eq_one_of_forall_eq_one hfin, mul_one, NNReal.coe_prod,
    Finset.prod_congr rfl fun w _ => hinf w, Finset.prod_const, Finset.card_univ, pow_mul]

private theorem exists_unit (h : IsCMExt F E σ) {s : ℝ} (hs : 0 < s) :
    ∃ u : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ, u.1 = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.TorusTheta.infScale F s) ∧ s ≤ 1 + (absE F E u : ℝ) := by
  let u : (AF F ⊗[F] E)ˣ := ⟨rE F E s, rE F E s⁻¹, by rw [← rE_mul, mul_inv_cancel₀ hs.ne', rE_one],
    by rw [← rE_mul, inv_mul_cancel₀ hs.ne', rE_one]⟩
  refine ⟨u, rfl, ?_⟩
  rw [absE_rE h hs u rfl]
  have hm : 2 * Fintype.card (InfinitePlace F) ≠ 0 := Nat.mul_ne_zero two_ne_zero Fintype.card_ne_zero
  rcases le_total s 1 with h1 | h1
  · exact h1.trans (le_add_of_nonneg_right (by positivity))
  · exact (le_self_pow₀ h1 hm).trans (le_add_of_nonneg_left zero_le_one)

end
