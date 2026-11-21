import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StabCosetDomain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)

theorem incV_inj {n : ℕ} : Function.Injective (incV (E := E) (n := n) F) :=
  fun x y h => funext fun i => inclR_inj (congrFun h i)

theorem cA_inclR (σ : E →ₐ[F] E) (e : E) :
    cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.map_tmul]

theorem mat_inv_mul {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) :
    mat g⁻¹ * mat g = 1 := Units.inv_mul g.1

theorem eq_of_mulVec {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : UA σ J) {x y v : Fin n → E}
    (hx : mat h *ᵥ incV F x = incV F v) (hy : mat h *ᵥ incV F y = incV F v) : x = y := by
  apply incV_inj (F := F)
  have e : ∀ z, incV F z = mat h⁻¹ *ᵥ (mat h *ᵥ incV F z) := fun z => by
    rw [Matrix.mulVec_mulVec, mat_inv_mul, Matrix.one_mulVec]
  rw [e x, e y, hx, hy]

theorem rat_desc {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (δ : UA σ J) (hδ : δ ∈ ratU σ J) :
    ∃ g : Matrix (Fin n) (Fin n) E, mat δ = g.map (inclR (F := F) (AF F)) ∧ gᵀ * J * g.map σ = J := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.1 hδ
  have hm : mat δ = g₀.1.map (inclR (F := F) (AF F)) := by
    show δ.1.1 = _
    rw [← hg₀]; rfl
  refine ⟨g₀.1, hm, ?_⟩
  have hu : (mat δ)ᵀ * incM F J * (mat δ).map (cA σ) = incM F J := δ.2
  have key : (g₀.1ᵀ * J * g₀.1.map σ).map (inclR (F := F) (AF F)) = J.map (inclR (F := F) (AF F)) := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    have e2 : (g₀.1.map σ).map (inclR (F := F) (AF F)) = (mat δ).map (cA σ) := by
      rw [hm]; ext i j; simp [cA_inclR]
    rw [e2, ← hm]
    exact hu
  exact Matrix.ext fun i j => inclR_inj (congrFun (congrFun key i) j)

end GlobalTheory.StabCosetDomain

open GlobalTheory.StabCosetDomain in
