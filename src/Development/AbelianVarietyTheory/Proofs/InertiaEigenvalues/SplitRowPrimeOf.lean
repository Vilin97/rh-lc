module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrime
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPrimeImpliesPlacesSplit

-- Source module: Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TorsionExponentCondition

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
open Classical

namespace GlobalTheory.HubX.Check

variable {D : D7}

variable {L : SizeData₂ D} {HW : HWOf D.loc} {R : KillingConditions.RowK} {X : KillingConditions.HubData D}

theorem not_inert {l : ℕ} (h1 : TwistedPlaces.SplitK D l) : ¬ TwistedPlaces.InertK D l := by
  intro h2
  unfold TwistedPlaces.SplitK at h1
  unfold TwistedPlaces.InertK at h2
  rw [h1] at h2
  rcases h2 with h2 | h2 <;> cases h2

theorem decl (h : Canon L HW R X) (hJ : AdmissibleParameterJ.ConclusionJa D) (i : D.nd.Loc) (hg : D.nd.l i ∉ TwistedPlaces.gset D)
    (hr : KillingConditions.RangeAD L X.exc (D.nd.l i)) (hs : TwistedPlaces.SplitK D (D.nd.l i))
    (hex : ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc hJ.choose) : EmbeddingTypes.hypDecl i (X.dc i) hJ.choose := by
  have hp := (D.nd.lPrime i).out
  have h5 : 5 ≤ D.nd.l i := by
    have h2 := hp.two_le
    have h3 : D.nd.l i ≠ 3 := fun e => hr.1 (Or.inr e)
    have h2' : D.nd.l i ≠ 2 := fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))
    have h4 : D.nd.l i ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    omega
  have hsp : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) := by
    refine ⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩
    rw [e]
    fin_cases k <;> simp [TwistedPlaces.gset]
  have he : epJ D = hJ.choose := epJ_eq hJ
  have hc : GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) ∧ ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc (epJ D) :=
    ⟨hsp, by rw [he]; exact hex⟩
  rw [h.dc i (not_inert hs), dcOf, dite_eq_left hc, ← he]
  exact hc.2.choose_spec

end GlobalTheory.HubX.Check

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

theorem _root_.GlobalTheory.T.exists_splitPlacesDeclaration_splitRowPrime : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → (∃ dc : TruncatedSeriesCountingIdentities.Decl D i, EmbeddingTypes.hypDecl i dc ep) ∧ EmbeddingTypes.hypL i := by
  first | exact @GlobalTheory.SplitDecl.main | exact GlobalTheory.SplitDecl.main | (intros; apply GlobalTheory.SplitDecl.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowPrimeOf

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.HubX.SplitDecl

theorem splitRowPrime_of {D : D7} {L : SizeData₂ D} {X : KillingConditions.HubData D} (i : D.nd.Loc)
    (hg : D.nd.l i ∉ TwistedPlaces.gset D) (hr : KillingConditions.RangeAD L X.exc (D.nd.l i)) (hs : TwistedPlaces.SplitK D (D.nd.l i)) :
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) := by
  have hp := (D.nd.lPrime i).out
  have h5 : 5 ≤ D.nd.l i := by
    have h2 := hp.two_le
    have h3 : D.nd.l i ≠ 3 := fun e => hr.1 (Or.inr e)
    have h2' : D.nd.l i ≠ 2 := fun e => hr.1 (Or.inl (e ▸ D.host.toHostRaw.two_mem_small))
    have h4 : D.nd.l i ≠ 4 := fun e => by rw [e] at hp; norm_num at hp
    omega
  refine ⟨hp, h5, fun e => hr.2.1 (Or.inl e), fun e => hr.2.1 (Or.inr e), fun k e => hg ?_, hs⟩
  rw [e]
  fin_cases k <;> simp [TwistedPlaces.gset]

theorem main : ∀ (D : D7) (L : SizeData₂ D) (HW : HWOf D.loc) (R : KillingConditions.RowK) (X : KillingConditions.HubData D),
    GlobalTheory.HubX.Canon L HW R X → ∀ (hJ : AdmissibleParameterJ.ConclusionJa D) (i : D.nd.Loc), TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D →
    KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) →
    EmbeddingTypes.hypDecl i (X.dc i) (Exists.choose hJ) ∧
      ∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1 := by
  intro D L HW R X h hJ i _ hg hr hs
  have hsp := splitRowPrime_of (L := L) (X := X) i hg hr hs
  refine ⟨GlobalTheory.HubX.Check.decl h hJ i hg hr hs ((GlobalTheory.T.exists_splitPlacesDeclaration_splitRowPrime D i hJ.choose hsp).1), ?_⟩
  intro v hv
  exact (GlobalTheory.SplitPlaces.placesSplit D.host (D.nd.l i) hsp v hv).1

end GlobalTheory.HubX.SplitDecl
end
end
