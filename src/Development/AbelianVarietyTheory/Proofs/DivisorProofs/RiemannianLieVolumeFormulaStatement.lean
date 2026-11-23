module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDualIndexStatement
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Mathlib.RingTheory.Norm.Transitivity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTraceFormDetIndex
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianVolumeLieBasisStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSq

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory

theorem cm_type_normSq_prod_eq_abs_norm (E : Type) [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (d : E) :
    ‖∏ τ : Ψ, τ.1 d‖ ^ 2 = |((Algebra.norm ℚ d : ℚ) : ℝ)| := by
  classical
  have hcc : ∀ τ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ) = τ := by
    intro τ; ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  have h1 : ((Algebra.norm ℚ d : ℚ) : ℂ) = ∏ τ : E →+* ℂ, τ d := by
    have := Algebra.norm_eq_prod_embeddings ℚ ℂ d
    rw [eq_ratCast] at this
    rw [this]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom E ℂ).symm _ _ (fun σ => rfl)
  have hcompl : ∏ τ ∈ Ψᶜ, τ d = ∏ τ ∈ Ψ, (starRingEnd ℂ) (τ d) := by
    refine Finset.prod_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_compl, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hτ ⊢
      rw [hΨ, hcc]; exact hτ
    · intro τ hτ
      simp only [Finset.mem_compl, Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hτ ⊢
      exact (hΨ τ).mp hτ
    · intro τ _; exact hcc τ
    · intro τ _; exact hcc τ
    · intro τ _; simp [ComplexEmbedding.conjugate_coe_eq]
  have hsub : ∏ τ : Ψ, τ.1 d = ∏ τ ∈ Ψ, τ d := Finset.prod_coe_sort Ψ (fun τ => τ d)
  set P := ∏ τ ∈ Ψ, τ d with hP
  have h2 : ((Algebra.norm ℚ d : ℚ) : ℂ) = ((Complex.normSq P : ℝ) : ℂ) := by
    rw [h1, ← Finset.prod_mul_prod_compl Ψ, hcompl, ← map_prod, Complex.mul_conj]
  have h3 : ((Algebra.norm ℚ d : ℚ) : ℝ) = Complex.normSq P := by
    have := h2
    rw [show ((Algebra.norm ℚ d : ℚ) : ℂ) = (((Algebra.norm ℚ d : ℚ) : ℝ) : ℂ) by push_cast; rfl] at this
    exact_mod_cast this
  rw [hsub, h3, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSqStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.norm_cm_type_product_sq : ∀ (E : Type) [Field E] [NumberField E] (Ψ : Finset (E →+* ℂ)), (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → ∀ d : E, ‖∏ τ : Ψ, τ.1 d‖ ^ 2 = |((Algebra.norm ℚ d : ℚ) : ℝ)| := by
  first | exact @GlobalTheory.cm_type_normSq_prod_eq_abs_norm | exact GlobalTheory.cm_type_normSq_prod_eq_abs_norm | (intros; apply GlobalTheory.cm_type_normSq_prod_eq_abs_norm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTraceFormDetIndexStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.norm_trace_form_det_index : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → SelfDualLat G Λ → (∀ i, e i ∈ lieLat G Λ) → LinearIndependent (maximalRealSubfield E) e → |((Algebra.norm ℚ (Matrix.of fun i j => Matrix.trace (e i * e j)).det : ℚ) : ℝ)| = (((lieLat G Λ).relIndex (AddSubgroup.closure {Y : Matrix (Fin r) (Fin r) E | Y.trace = 0 ∧ (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) ∧ ∀ X ∈ lieLat G Λ, IsIntegral ℤ (Matrix.trace (X * Y))}) : ℝ) * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) ^ 2) ^ 2 := by
  first | exact @GlobalTheory.LieIndex.abs_norm_gram_eq_index | exact GlobalTheory.LieIndex.abs_norm_gram_eq_index | (intros; apply GlobalTheory.LieIndex.abs_norm_gram_eq_index <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieVolumeFormula

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.LieCovol

theorem riemLie_eq_sqrt_index_smul_formLie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Frame X.Ψ r) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → Unr E → SelfDualLat X.Gm Λ → IsOrth X x → (∀ i, e i ∈ lieLat X.Gm Λ) → LinearIndependent (maximalRealSubfield E) e → riemLie X.Ψ X.Gm x = ENNReal.ofReal (Real.sqrt r ^ fdeg E * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat X.Gm Λ) : ℝ)) • formLie X.Ψ e := by
  intro E _ _ _ r X Λ x e hr hU hΛ hx he hli
  rw [GlobalTheory.T.riemannian_volume_lie_basis E r X x e hr hx (fun i => ⟨(he i).1, (he i).2.1⟩) hli]
  congr 1
  congr 1
  have h1 := GlobalTheory.T.norm_cm_type_product_sq E X.Ψ X.cmType (Matrix.of fun i j => Matrix.trace (e i * e j)).det
  have h2 := GlobalTheory.T.norm_trace_form_det_index E r X.Gm Λ e hr hΛ he hli
  have h3 := GlobalTheory.T.lie_lattice_dual_index E r X.Gm Λ hr hU hΛ
  rw [h3] at h2
  rw [h2] at h1
  push_cast at h1
  have hn : ‖∏ τ : X.Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖ = (r : ℝ) ^ fdeg E * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat X.Gm Λ) : ℝ) ^ 2 :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h1
  have hs : Real.sqrt ((r : ℝ) ^ fdeg E) = Real.sqrt r ^ fdeg E := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow, Real.mul_self_sqrt (by positivity)]
  rw [hn, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), hs]

end GlobalTheory.LieCovol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieVolumeFormulaStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.riemannian_lie_volume_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Frame X.Ψ r) (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E), 2 ≤ r → Unr E → SelfDualLat X.Gm Λ → IsOrth X x → (∀ i, e i ∈ lieLat X.Gm Λ) → LinearIndependent (maximalRealSubfield E) e → riemLie X.Ψ X.Gm x = ENNReal.ofReal (Real.sqrt r ^ fdeg E * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat X.Gm Λ) : ℝ)) • formLie X.Ψ e := by
  first | exact @GlobalTheory.LieCovol.riemLie_eq_sqrt_index_smul_formLie | exact GlobalTheory.LieCovol.riemLie_eq_sqrt_index_smul_formLie | (intros; apply GlobalTheory.LieCovol.riemLie_eq_sqrt_index_smul_formLie <;> assumption)
end
end
