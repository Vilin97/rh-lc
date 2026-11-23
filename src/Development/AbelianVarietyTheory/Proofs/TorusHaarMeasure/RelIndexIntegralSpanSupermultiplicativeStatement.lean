module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSpanNeZero
public import Mathlib.GroupTheory.Index
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
public import Mathlib.Order.ModularLattice
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.Tactic.Continuity
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexSupMulRelIndexInfSame

section

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem relIndex_sup_mul_relIndex_inf_same {A : Type} [AddCommGroup A] (M L N : AddSubgroup A)
    (h : M ≤ L) :
    (M ⊔ N).relIndex (L ⊔ N) * (M ⊓ N).relIndex (L ⊓ N) = M.relIndex L := by
  have h1 : (M ⊔ N).relIndex (L ⊔ N) = (M ⊔ (N ⊓ L)).relIndex L := by
    have e : L ⊔ N = L ⊔ (M ⊔ N) := by
      rw [← sup_assoc, sup_eq_left.mpr h]
    rw [e, AddSubgroup.relIndex_sup_right, ← AddSubgroup.inf_relIndex_right (M ⊔ N) L,
      sup_inf_assoc_of_le N h]
  have h2 : (M ⊓ N).relIndex (L ⊓ N) = M.relIndex (M ⊔ (N ⊓ L)) := by
    have e : M ⊓ N = M ⊓ (L ⊓ N) := by
      rw [← inf_assoc, inf_eq_left.mpr h]
    rw [e, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_sup_left, inf_comm]
  rw [h1, h2, mul_comm]
  exact AddSubgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le h inf_le_right)

theorem relIndex_sup_mul_relIndex_inf :
    (∀ (A : Type) [AddCommGroup A] (M₁ L₁ M₂ L₂ : AddSubgroup A), M₁ ≤ L₁ → M₂ ≤ L₂ →
      (M₁ ⊔ M₂).relIndex (L₁ ⊔ L₂) * (M₁ ⊓ M₂).relIndex (L₁ ⊓ L₂) =
        M₁.relIndex L₁ * M₂.relIndex L₂) := by
  intro A _ M₁ L₁ M₂ L₂ h₁ h₂
  have a := relIndex_sup_mul_relIndex_inf_same M₁ L₁ M₂ h₁
  have b := relIndex_sup_mul_relIndex_inf_same M₂ L₂ L₁ h₂
  rw [sup_comm M₂, sup_comm L₂, inf_comm M₂, inf_comm L₂] at b
  rw [← a, ← b,
    ← AddSubgroup.relIndex_mul_relIndex (M₁ ⊔ M₂) (L₁ ⊔ M₂) (L₁ ⊔ L₂)
      (sup_le_sup_right h₁ _) (sup_le_sup_left h₂ _),
    ← AddSubgroup.relIndex_mul_relIndex (M₁ ⊓ M₂) (L₁ ⊓ M₂) (L₁ ⊓ L₂)
      (inf_le_inf_right _ h₁) (inf_le_inf_left _ h₂)]
  ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SpanImageInfSpanImageOfLinearIndependent

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory

theorem span_image_inf_span_image_of_linearIndependent {R V ι : Type} [CommRing R]
    [AddCommGroup V] [Module R V] {w : ι → V} (hw : LinearIndependent R w) (s t : Set ι) :
    Submodule.span R (w '' s) ⊓ Submodule.span R (w '' t) = Submodule.span R (w '' (s ∩ t)) := by
  apply le_antisymm
  · rintro x ⟨hs, ht⟩
    obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 hs
    obtain ⟨m, hm, hmx⟩ := (Finsupp.mem_span_image_iff_linearCombination R).1 ht
    have hlm : l = m := hw (hlx.trans hmx.symm)
    subst hlm
    refine (Finsupp.mem_span_image_iff_linearCombination R).2 ⟨l, ?_, hlx⟩
    rw [Finsupp.mem_supported] at hl hm ⊢
    exact Set.subset_inter hl hm
  · exact le_inf (Submodule.span_mono (Set.image_mono Set.inter_subset_left))
      (Submodule.span_mono (Set.image_mono Set.inter_subset_right))

theorem span_inf_sup_overlapping_parts :
    ∀ (R V α β γ : Type) [CommRing R] [AddCommGroup V] [Module R V] (w : α ⊕ β ⊕ γ → V),
      LinearIndependent R w →
      Submodule.span R (Set.range (w ∘ Sum.map id Sum.inl)) ⊓
          Submodule.span R (Set.range (w ∘ Sum.map id Sum.inr)) =
        Submodule.span R (Set.range (w ∘ Sum.inl)) ∧
      Submodule.span R (Set.range (w ∘ Sum.map id Sum.inl)) ⊔
          Submodule.span R (Set.range (w ∘ Sum.map id Sum.inr)) =
        Submodule.span R (Set.range w) := by
  intro R V α β γ _ _ _ w hw
  constructor
  · rw [Set.range_comp, Set.range_comp, Set.range_comp,
      span_image_inf_span_image_of_linearIndependent hw]
    congr 2
    ext x
    rcases x with a | b | c <;> simp
  · rw [← Submodule.span_union, Set.range_comp, Set.range_comp, ← Set.image_union,
      show (Set.range (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ) ∪
          Set.range (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)) = Set.univ from by
        ext x
        rcases x with a | b | c <;> simp, Set.image_univ]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexIntegralSpanSupermultiplicative

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.SpanIndex

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem relIndex_mul_le_of_le {A : Type} [AddCommGroup A] (M₁ M₂ W₁ W₂ Λ : AddSubgroup A)
    (h₁ : M₁ ≤ Λ ⊓ W₁) (h₂ : M₂ ≤ Λ ⊓ W₂)
    (hne : (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) ≠ 0) :
    M₁.relIndex (Λ ⊓ W₁) * M₂.relIndex (Λ ⊓ W₂) ≤
      (M₁ ⊓ M₂).relIndex (Λ ⊓ (W₁ ⊓ W₂)) * (M₁ ⊔ M₂).relIndex (Λ ⊓ (W₁ ⊔ W₂)) := by
  rw [← GlobalTheory.relIndex_sup_mul_relIndex_inf A M₁ _ M₂ _ h₁ h₂, mul_comm, ← inf_inf_distrib_left]
  refine Nat.mul_le_mul_left _ (AddSubgroup.relIndex_le_of_le_right ?_ hne)
  exact sup_le (inf_le_inf_left _ le_sup_left) (inf_le_inf_left _ le_sup_right)


omit [IsCMField E] in
theorem span_le_inf_span {r : ℕ} (Λ : Submodule (𝓞 E) (Fin r → E)) {ι : Type}
    (w : ι → Fin r → E) (hw : ∀ a, w a ∈ Λ) :
    (Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup ≤
      Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup := by
  refine le_inf ?_ ?_
  · have : Submodule.span (𝓞 E) (Set.range w) ≤ Λ :=
      Submodule.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hw a)
    exact fun x hx => this hx
  · exact fun x hx => Submodule.span_le_restrictScalars (𝓞 E) E _ hx

theorem relIndex_span_mul_le : (∀ (r : ℕ) (X : Data E r) (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (w : α ⊕ β ⊕ γ → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup)) ≤ ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup))) := by
  intro r X α β γ _ _ _ _ _ _ w hw hΛ
  have hw' : LinearIndependent (𝓞 E) w := hw.restrict_scalars' (𝓞 E)
  obtain ⟨i₁, s₁⟩ := GlobalTheory.span_inf_sup_overlapping_parts (𝓞 E) _ α β γ w hw'
  obtain ⟨i₂, s₂⟩ := GlobalTheory.span_inf_sup_overlapping_parts E _ α β γ w hw
  have hne := relIndex_span_ne_zero r X _ w hw hΛ
  rw [← s₁, ← s₂, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup] at hne
  have key := relIndex_mul_le_of_le _ _ _ _ _
    (span_le_inf_span X.Λ (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)) fun a => hΛ _)
    (span_le_inf_span X.Λ (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)) fun a => hΛ _) hne
  rw [← i₁, ← i₂, ← s₁, ← s₂, Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup]
  exact key

end GlobalTheory.SpanIndex
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.RelIndexIntegralSpanSupermultiplicativeStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.relIndex_integralSpan_supermultiplicative : (∀ (r : ℕ) (X : Data E r) (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (w : α ⊕ β ⊕ γ → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup)) ≤ ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup))) := by
  first | exact @GlobalTheory.SpanIndex.relIndex_span_mul_le | exact GlobalTheory.SpanIndex.relIndex_span_mul_le | (intros; apply GlobalTheory.SpanIndex.relIndex_span_mul_le <;> assumption)
end
end
