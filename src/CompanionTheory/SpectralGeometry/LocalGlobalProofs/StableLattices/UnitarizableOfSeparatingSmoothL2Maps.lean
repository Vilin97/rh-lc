module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.L2Embedding
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Smooth
public import Formalism.RealPlaceAnalysis.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Unitary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RregRep

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUnitaryImage

section

@[expose] public section

noncomputable section

open ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.CompanionTheory.Unitarize

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {X : Type*} [AddCommGroup X] [Module ℂ X]

theorem injective_of_simple {M : Type*} [AddCommGroup M] [Module ℂ M]
    {E : Fin n → Fin n → Module.End ℂ X} {F : Fin n → Fin n → Module.End ℂ M}
    (hS : ∀ W : Submodule ℂ X, (∀ a b, ∀ x ∈ W, E a b x ∈ W) → W = ⊥ ∨ W = ⊤)
    (c : X →ₗ[ℂ] M) (hc : ∀ a b x, c (E a b x) = F a b (c x)) (h0 : c ≠ 0) :
    Function.Injective c := by
  have hst : ∀ a b, ∀ x ∈ LinearMap.ker c, E a b x ∈ LinearMap.ker c := by
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hc, hx, map_zero]
  rcases hS _ hst with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) h0

theorem adjSign_eq_sgn (ε : Fin n → Bool) (a b : Fin n) :
    adjSign ε a b = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) := by
  unfold adjSign Formalism.REAL.sgn
  split_ifs <;> simp

theorem exists_unitary_image {ε : Fin n → Bool} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) {E : Fin n → Fin n → Module.End ℂ X}
    (hS : ∀ W : Submodule ℂ X, (∀ a b, ∀ x ∈ W, E a b x ∈ W) → W = ⊥ ∨ W = ⊤)
    (c : X →ₗ[ℂ] smD ε σ) (hc : ∀ a b x, c (E a b x) = smE ε σ a b (c x)) (h0 : c ≠ 0) :
    ∃ (V : Submodule ℂ H) (E' : Fin n → Fin n → Module.End ℂ V) (e : X ≃ₗ[ℂ] V),
      (∀ x, ((e x : V) : H) = ((c x : smD ε σ) : H)) ∧
      Formalism.REAL.GlRel E' ∧ Formalism.REAL.IsUnitary ε E' ∧
      ∀ a b x, e (E a b x) = E' a b (e x) := by
  have hinj : Function.Injective c := injective_of_simple hS c hc h0
  set d : X →ₗ[ℂ] H := (smD ε σ).subtype ∘ₗ c with hd
  have hdinj : Function.Injective d := Subtype.val_injective.comp hinj
  let e : X ≃ₗ[ℂ] LinearMap.range d := LinearEquiv.ofInjective d hdinj
  have he : ∀ x, ((e x : LinearMap.range d) : H) = ((c x : smD ε σ) : H) := fun x => rfl
  let E' : Fin n → Fin n → Module.End ℂ (LinearMap.range d) := fun a b =>
    e.toLinearMap ∘ₗ E a b ∘ₗ e.symm.toLinearMap
  have hE' : ∀ a b x, E' a b (e x) = e (E a b x) := by
    intro a b x
    simp [E']
  have hcoe : ∀ a b x, ((E' a b (e x) : LinearMap.range d) : H) =
      ((smE ε σ a b (c x) : smD ε σ) : H) := by
    intro a b x
    rw [hE', he, hc]
  have hgl : IsGlRep (smE ε σ) := (isDerivedOn_smE hσ).glRep
  have hU : IsInfUnitary ε (smE ε σ) := isInfUnitary_of_isDerivedOn hσ (isDerivedOn_smE hσ)
  refine ⟨LinearMap.range d, E', e, he, ?_, ?_, fun a b x => (hE' a b x).symm⟩
  · intro a b c' d'
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    have h := LinearMap.congr_fun (hgl a b c' d') (c x)
    have h' := congrArg (Subtype.val) h
    apply Subtype.ext
    have hEE : ∀ a b c' d', ((E' a b (E' c' d' (e x)) : LinearMap.range d) : H) =
        ((smE ε σ a b (smE ε σ c' d' (c x)) : smD ε σ) : H) := by
      intro a b c' d'
      rw [hE', hcoe, hc]
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Submodule.coe_sub] at h' ⊢
    rw [hEE, hEE, h']
    split_ifs <;> simp [hcoe]
  · intro a b y z
    obtain ⟨u, rfl⟩ := e.surjective y
    obtain ⟨v, rfl⟩ := e.surjective z
    have h := hU a b (c u) (c v)
    rw [← adjSign_eq_sgn]
    rw [Submodule.coe_inner, Submodule.coe_inner, hcoe, hcoe, he, he]
    simpa [Submodule.coe_inner] using h

end GlobalTheory.CompanionTheory.Unitarize
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitarizableOfSeparatingSmoothL2Maps

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExhFin

open CompanionTheory.RgExh ReciprocityTheory.ChartRestriction.DS
open Formalism.REAL (GlRel IsUnitary)

theorem unitarizable_of_separating_smooth_l2_maps :
    ∀ (n : ℕ) (ε : Fin n → Bool) (X : GMod n), L2Embedding ε X → IsSimple X →
      ∃ (V : Type) (_ : NormedAddCommGroup V) (_ : InnerProductSpace ℂ V)
        (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E),
        IsUnitary ε E ∧ Iso X ⟨V, E, hE⟩ := by
  intro n ε X hL hS
  obtain ⟨hnt, hsub⟩ := hS
  obtain ⟨u, hu⟩ := exists_ne (0 : X.V)
  obtain ⟨c, hc, hcu⟩ := hL u hu
  have h0 : c ≠ 0 := fun h => hcu (by simp [h])
  obtain ⟨V, E', e, -, hgl, hU, he⟩ :=
    GlobalTheory.CompanionTheory.Unitarize.exists_unitary_image (rreg_isURepOn ε) hsub c hc h0
  exact ⟨V, inferInstance, inferInstance, E', hgl, hU, e, he⟩

end GlobalTheory.CompanionTheory.RgExhFin
end
end
end
