module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Tactic.Continuity
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LatDen
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetInequalitiesClosedFormsStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexIntegralSpanSupermultiplicativeStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanNeZero
import Mathlib.Analysis.Matrix.PosDef

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBasisAdaptedTwoSubspaces

section

@[expose] public section

namespace GlobalTheory

theorem exists_relCompl_submodule {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {U W : Submodule K V} (h : U ≤ W) : ∃ C : Submodule K V, Disjoint U C ∧ U ⊔ C = W := by
  obtain ⟨C, hC⟩ := U.exists_isCompl
  refine ⟨C ⊓ W, hC.disjoint.mono_right inf_le_left, ?_⟩
  rw [← sup_inf_assoc_of_le C h, hC.sup_eq_top, top_inf_eq]

theorem exists_fin_independent_span_eq {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (S : Submodule K V) :
    ∃ (n : ℕ) (v : Fin n → V), LinearIndependent K v ∧ Submodule.span K (Set.range v) = S := by
  let b := Module.finBasis K S
  refine ⟨_, S.subtype ∘ b, b.linearIndependent.map' S.subtype (Submodule.ker_subtype S), ?_⟩
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

theorem exists_basis_adapted_two_subspaces (K V : Type) [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W₁ W₂ : Submodule K V) :
    ∃ (a b c : ℕ) (w : Fin a ⊕ Fin b ⊕ Fin c → V), LinearIndependent K w ∧
      Submodule.span K (Set.range (w ∘ Sum.inl)) = W₁ ⊓ W₂ ∧
      Submodule.span K (Set.range (w ∘ Sum.map id Sum.inl)) = W₁ ∧
      Submodule.span K (Set.range (w ∘ Sum.map id Sum.inr)) = W₂ ∧
      Submodule.span K (Set.range w) = W₁ ⊔ W₂ := by
  obtain ⟨C₁, hd₁, hs₁⟩ := exists_relCompl_submodule (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
  obtain ⟨C₂, hd₂, hs₂⟩ := exists_relCompl_submodule (inf_le_right : W₁ ⊓ W₂ ≤ W₂)
  obtain ⟨a, u, hu, hus⟩ := exists_fin_independent_span_eq (W₁ ⊓ W₂)
  obtain ⟨b, v₁, hv₁, hvs₁⟩ := exists_fin_independent_span_eq C₁
  obtain ⟨c, v₂, hv₂, hvs₂⟩ := exists_fin_independent_span_eq C₂
  have hC₁ : C₁ ≤ W₁ := hs₁ ▸ le_sup_right
  have hC₂ : C₂ ≤ W₂ := hs₂ ▸ le_sup_right
  have h12 : Disjoint C₁ C₂ := by
    rw [Submodule.disjoint_def]
    intro x hx₁ hx₂
    exact (Submodule.disjoint_def.1 hd₁) x ⟨hC₁ hx₁, hC₂ hx₂⟩ hx₁
  have hU : Disjoint (W₁ ⊓ W₂) (C₁ ⊔ C₂) := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
    have hz1 : z ∈ W₁ := by
      have := W₁.sub_mem hx.1 (hC₁ hy)
      simpa using this
    have hz0 : z = 0 := (Submodule.disjoint_def.1 hd₂) z ⟨hz1, hC₂ hz⟩ hz
    subst hz0
    rw [add_zero] at hx ⊢
    exact (Submodule.disjoint_def.1 hd₁) y hx hy
  have hv : LinearIndependent K (Sum.elim v₁ v₂) :=
    hv₁.sum_type hv₂ (by rw [hvs₁, hvs₂]; exact h12)
  have hvs : Submodule.span K (Set.range (Sum.elim v₁ v₂)) = C₁ ⊔ C₂ := by
    rw [Set.Sum.elim_range, Submodule.span_union, hvs₁, hvs₂]
  refine ⟨a, b, c, Sum.elim u (Sum.elim v₁ v₂),
    hu.sum_type hv (by rw [hus, hvs]; exact hU), ?_, ?_, ?_, ?_⟩
  · rw [Sum.elim_comp_inl, hus]
  · have : Sum.elim u (Sum.elim v₁ v₂) ∘ Sum.map id Sum.inl = Sum.elim u v₁ := by
      funext x; cases x <;> rfl
    rw [this, Set.Sum.elim_range, Submodule.span_union, hus, hvs₁, hs₁]
  · have : Sum.elim u (Sum.elim v₁ v₂) ∘ Sum.map id Sum.inr = Sum.elim u v₂ := by
      funext x; cases x <;> rfl
    rw [this, Set.Sum.elim_range, Submodule.span_union, hus, hvs₂, hs₂]
  · rw [Set.Sum.elim_range, Submodule.span_union, hus, hvs, sup_sup_distrib_left, hs₁, hs₂]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsBasisAdaptedMem

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.LatBasisAdapted

theorem span_range_smul_comp {K V ι κ : Type*} [Field K] [AddCommGroup V] [Module K V]
    (c : ι → K) (hc : ∀ i, c i ≠ 0) (w : ι → V) (f : κ → ι) :
    Submodule.span K (Set.range ((fun i => c i • w i) ∘ f)) =
      Submodule.span K (Set.range (w ∘ f)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    have h : (w ∘ f) k = (c (f k))⁻¹ • ((fun i => c i • w i) ∘ f) k := by
      simp [smul_smul, inv_mul_cancel₀ (hc (f k))]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_basis_adapted_mem : (∀ (r : ℕ) (X : Data E r) (W₁ W₂ : Submodule E (Fin r → E)), ∃ (a b c : ℕ) (w : Fin a ⊕ Fin b ⊕ Fin c → Fin r → E), LinearIndependent E w ∧ (∀ k, w k ∈ X.Λ) ∧ Submodule.span E (Set.range (w ∘ Sum.inl)) = W₁ ⊓ W₂ ∧ Submodule.span E (Set.range (w ∘ Sum.map id Sum.inl)) = W₁ ∧ Submodule.span E (Set.range (w ∘ Sum.map id Sum.inr)) = W₂ ∧ Submodule.span E (Set.range w) = W₁ ⊔ W₂) := by
  intro r X W₁ W₂
  obtain ⟨a, b, c, w, hw, h0, h1, h2, h3⟩ :=
    GlobalTheory.exists_basis_adapted_two_subspaces E (Fin r → E) W₁ W₂
  choose n hn hm using fun k => (GlobalTheory.LatDen.latDen r X).1 (w k)
  have hc : ∀ k, (n k : E) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hn k).ne'
  refine ⟨a, b, c, fun k => (n k : E) • w k, ?_, hm, ?_, ?_, ?_, ?_⟩
  · exact hw.units_smul (fun k => Units.mk0 _ (hc k))
  · rw [span_range_smul_comp _ hc, h0]
  · rw [span_range_smul_comp _ hc, h1]
  · rw [span_range_smul_comp _ hc, h2]
  · exact (span_range_smul_comp _ hc w id).trans h3

end GlobalTheory.LatBasisAdapted
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GramDetReNonneg

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.HeightSubmodular

theorem gram_det_re_nonneg {m ι : Type} [Fintype m] [Fintype ι] [DecidableEq ι]
    (N : Matrix m ι ℂ) : 0 ≤ (Nᴴ * N).det.re := by
  have h : (0 : ℂ) ≤ (Nᴴ * N).det := (Matrix.posSemidef_conjTranspose_mul_self N).det_nonneg
  exact (Complex.nonneg_iff.mp h).1

theorem div_mul_div_le {p q p' q' : ℝ} {i j i' j' : ℕ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h : p * q ≤ p' * q') (hi : i' ≠ 0) (hj : j' ≠ 0) (hij : i' * j' ≤ i * j) :
    p / i * (q / j) ≤ p' / i' * (q' / j') := by
  have hnum : 0 ≤ p' * q' := (mul_nonneg hp hq).trans h
  have hden : (0 : ℝ) < (i' : ℝ) * j' :=
    mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hi) (by exact_mod_cast Nat.pos_of_ne_zero hj)
  rw [div_mul_div_comm, div_mul_div_comm]
  rcases Nat.eq_zero_or_pos (i * j) with h0 | h0
  · have hz : (i : ℝ) * j = 0 := by exact_mod_cast h0
    rw [hz, div_zero]
    exact div_nonneg hnum hden.le
  · exact div_le_div₀ hnum h hden (by exact_mod_cast hij)

theorem height_submodular : (∀ (r : ℕ) (X : Data E r) (d : Frame X.Ψ r → Submodule E (Fin r → E) → ℝ), (∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → d x (Submodule.span E (Set.range w)) = ((∏ τ : X.Ψ, ((((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))ᴴ * ((mat x τ)⁻¹ * (Matrix.of fun k a => τ.1 (w a k)))).det.re)) / (((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup)) : ℝ))) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, (mat x τ).det ≠ 0) → ∀ W₁ W₂, d x (W₁ ⊓ W₂) * d x (W₁ ⊔ W₂) ≤ d x W₁ * d x W₂) := by
  intro r X d hd x hx W₁ W₂
  obtain ⟨a, b, c, w, hli, hmem, h0, h1, h2, h3⟩ :=
    GlobalTheory.LatBasisAdapted.exists_basis_adapted_mem r X W₁ W₂
  have hsub : ∀ {κ : Type} (f : κ → Fin a ⊕ Fin b ⊕ Fin c) (τ : X.Ψ),
      (mat x τ)⁻¹ * (Matrix.of fun k l => τ.1 ((w ∘ f) l k)) =
        ((mat x τ)⁻¹ * Matrix.of fun k l => τ.1 (w l k)).submatrix id f := by
    intro κ f τ
    ext k l
    simp [Matrix.mul_apply]
  have key := fun {κ : Type} [Fintype κ] [DecidableEq κ] (f : κ → Fin a ⊕ Fin b ⊕ Fin c)
      (hf : Function.Injective f) =>
    hd x hx κ (w ∘ f) (hli.comp f hf) (fun l => hmem (f l))
  have hI := fun {κ : Type} [Fintype κ] [DecidableEq κ] (f : κ → Fin a ⊕ Fin b ⊕ Fin c)
      (hf : Function.Injective f) =>
    GlobalTheory.SpanIndex.relIndex_span_ne_zero r X κ (w ∘ f) (hli.comp f hf) (fun l => hmem (f l))
  have i1 : Function.Injective (Sum.map id Sum.inl : Fin a ⊕ Fin b → Fin a ⊕ Fin b ⊕ Fin c) :=
    Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩
  have i2 : Function.Injective (Sum.map id Sum.inr : Fin a ⊕ Fin c → Fin a ⊕ Fin b ⊕ Fin c) :=
    Sum.map_injective.mpr ⟨Function.injective_id, Sum.inr_injective⟩
  rw [← h0, ← h3, ← h1, ← h2, key _ Sum.inl_injective, key _ i1, key _ i2,
    hd x hx _ w hli hmem]
  apply div_mul_div_le
  · exact Finset.prod_nonneg fun τ _ => gram_det_re_nonneg _
  · exact Finset.prod_nonneg fun τ _ => gram_det_re_nonneg _
  · rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro τ _
      exact mul_nonneg (gram_det_re_nonneg _) (gram_det_re_nonneg _)
    · intro τ _
      simp only [hsub]
      exact (GlobalTheory.T.gramDet_inequalities_closed_forms).1 (Fin r) (Fin a) (Fin b) (Fin c) _
  · exact hI _ i1
  · exact hI _ i2
  · exact (GlobalTheory.T.relIndex_integralSpan_supermultiplicative) r X (Fin a) (Fin b) (Fin c) w hli hmem

end GlobalTheory.HeightSubmodular
end
end
