module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBasisMem
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetMul
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetDivIndexEqOfSpanEq

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E]

theorem exists_common_integral_refinement {V ι : Type} [AddCommGroup V] [Module E V]
    [Fintype ι] [DecidableEq ι] (w w' : ι → V) (hw' : LinearIndependent E w')
    (h : Submodule.span E (Set.range w) = Submodule.span E (Set.range w')) :
    ∃ A A' : Matrix ι ι (𝓞 E), A.det ≠ 0 ∧ A'.det ≠ 0 ∧
      (fun a => ∑ b, ((A b a : 𝓞 E) : E) • w b) = (fun a => ∑ b, ((A' b a : 𝓞 E) : E) • w' b) := by
  have h1 : ∀ a, ∃ c : ι → E, ∑ b, c b • w b = w' a := fun a =>
    (Submodule.mem_span_range_iff_exists_fun E).1
      (h ▸ Submodule.subset_span (Set.mem_range_self a))
  choose B hB using h1
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E))
    (fun p : ι × ι => B p.1 p.2)
  have hc' : ∀ a b, ∃ y : 𝓞 E, (y : E) = ((c : 𝓞 E) : E) * B a b := by
    intro a b
    obtain ⟨y, hy⟩ := hc (a, b)
    refine ⟨y, ?_⟩
    have : (y : E) = algebraMap (𝓞 E) E y := rfl
    rw [this, hy, Algebra.smul_def]
  choose A hA using hc'
  have hc0 : (c : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero c
  have hcE : ((c : 𝓞 E) : E) ≠ 0 := by
    simp
  have key : ∀ a, ∑ b, ((A a b : 𝓞 E) : E) • w b = ((c : 𝓞 E) : E) • w' a := by
    intro a
    rw [← hB a, Finset.smul_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [hA, mul_smul]
  refine ⟨Matrix.of fun b a => A a b, Matrix.diagonal fun _ => (c : 𝓞 E), ?_, ?_, ?_⟩
  · intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have h2 : ∑ a, (((v a : 𝓞 E) : E) * ((c : 𝓞 E) : E)) • w' a = 0 := by
      have : ∀ a, (((v a : 𝓞 E) : E) * ((c : 𝓞 E) : E)) • w' a
          = ∑ b, (((A a b * v a : 𝓞 E)) : E) • w b := by
        intro a
        rw [mul_smul, ← key, Finset.smul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← mul_smul, mul_comm]
        simp
      rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_comm]
      refine Finset.sum_eq_zero fun b _ => ?_
      rw [← Finset.sum_smul]
      have hb : ∑ a, A a b * v a = 0 := by
        have := congrFun hv b
        simpa [Matrix.mulVec, dotProduct] using this
      have hb' : ∑ a, (((A a b * v a : 𝓞 E)) : E) = 0 := by
        have := congrArg (algebraMap (𝓞 E) E) hb

        rw [map_sum, map_zero] at this
        exact this
      rw [hb', zero_smul]
    funext a
    have h3 := Fintype.linearIndependent_iff.1 hw' _ h2 a
    have h4 : ((v a : 𝓞 E) : E) = 0 := (mul_eq_zero.1 h3).resolve_right hcE
    simpa using h4
  · rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun _ _ => hc0
  · funext a
    simp only [Matrix.of_apply]
    rw [key, Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ hb]
    · simp

theorem gram_div_index_eq_of_span_eq [IsCMField E] : (∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ι : Type) [Fintype ι] [DecidableEq ι] (w w' : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → LinearIndependent E w' → (∀ a, w' a ∈ X.Λ) → Submodule.span E (Set.range w) = Submodule.span E (Set.range w') → ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w' a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w' a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w')).toAddSubgroup)) : ℝ))) := by
  intro r X x ι _ _ w w' hw hΛ hw' hΛ' h
  obtain ⟨A, A', hA, hA', he⟩ := exists_common_integral_refinement w w' hw' h
  have h1 := GlobalTheory.ValMul.value_mul_eq r X x ι w hw hΛ A hA
  have h2 := GlobalTheory.ValMul.value_mul_eq r X x ι w' hw' hΛ' A' hA'
  rw [← h1, ← h2, he]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetDivIndexEqOfSpanEqStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.gramDet_div_index_eq_of_span_eq : (∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) (ι : Type) [Fintype ι] [DecidableEq ι] (w w' : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → LinearIndependent E w' → (∀ a, w' a ∈ X.Λ) → Submodule.span E (Set.range w) = Submodule.span E (Set.range w') → ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w' a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w' a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w')).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w')).toAddSubgroup)) : ℝ))) := by
  first | exact @GlobalTheory.gram_div_index_eq_of_span_eq | exact GlobalTheory.gram_div_index_eq_of_span_eq | (intros; apply GlobalTheory.gram_div_index_eq_of_span_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsSubspaceHeightGramDeterminant

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SubspaceHeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem det_gram_reindex {r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) (A : Matrix (Fin r) (Fin r) ℂ) (f : ι → Fin r → ℂ) :
    ((A * (Matrix.of fun k a => f (e a) k))ᴴ * (A * (Matrix.of fun k a => f (e a) k))).det =
      ((A * (Matrix.of fun k a => f a k))ᴴ * (A * (Matrix.of fun k a => f a k))).det := by
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1

theorem exists_height : (∀ (r : ℕ) (X : Data E r), ∃ d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ, (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ)))) := by
  intro r X
  choose b hb hΛ hsp using GlobalTheory.LatBasis.exists_basis_mem r X
  refine ⟨fun x W => ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (b W a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (b W a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range (b W))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (b W))).toAddSubgroup)) : ℝ)), ?_⟩
  intro x _ ι _ _ w hw hwΛ
  have hc : Module.finrank E (Submodule.span E (Set.range w)) = Fintype.card ι :=
    finrank_span_eq_card hw
  let e : Fin (Module.finrank E (Submodule.span E (Set.range w))) ≃ ι :=
    (Fintype.equivFinOfCardEq hc.symm).symm
  have hr : Set.range (fun a => w (e a)) = Set.range w := e.surjective.range_comp w
  have key := GlobalTheory.T.gramDet_div_index_eq_of_span_eq r X x _ (b (Submodule.span E (Set.range w))) (fun a => w (e a))
    (hb _) (hΛ _) (hw.comp e e.injective) (fun a => hwΛ _) (by rw [hr, hsp])
  refine key.trans ?_
  rw [hr]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  exact congrArg Complex.re (det_gram_reindex e _ (fun a k => τ.1 (w a k)))

end GlobalTheory.SubspaceHeight
end
end
