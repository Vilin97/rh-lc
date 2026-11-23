module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.SplitPlaceTypes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitPlacesDeclarationSplitRowPrime
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitRowAt

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbTypeUeIffLocalEmbeddingInCMHalfType

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TypeUeHalf

theorem main : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), EmbeddingTypes.EmbTypeUe (i := i) (w := w) (hw := hw) ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ :=
  fun _ _ _ _ ep τ => GlobalTheory.SplitDecl.embTypeUe_iff ep τ

end GlobalTheory.TypeUeHalf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EmbTypeUeIffLocalEmbeddingInCMHalfTypeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (ep : Bool) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw), EmbeddingTypes.EmbTypeUe (i := i) (w := w) (hw := hw) ep τ ↔ GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.EmbIn (N := D.nd) D.nbr i ep w hw τ := by
  first | exact @GlobalTheory.TypeUeHalf.main | exact GlobalTheory.TypeUeHalf.main | (intros; apply GlobalTheory.TypeUeHalf.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientTypeConjugatePlaceAtSplitPrime

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes

namespace GlobalTheory.TypeConjSplit

theorem ambTypeD_of_splitRow : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool),
    GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  intro D i ep hi u hu hU w hw hc τ₀ hτ
  obtain ⟨-, h2, h3, -⟩ := (GlobalTheory.SplitRowAll.splitRow_at D).2 i hi
  have hUin : ∀ τ, EmbIn (N := D.nd) D.nbr i ep u hu τ :=
    fun τ => (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i u hu ep τ).1 (hU τ)
  have hwin : EmbIn (N := D.nd) D.nbr i ep w hw τ₀ := (GlobalTheory.T.embTypeUe_iff_localEmbeddingInCMHalfType D i w hw ep τ₀).1 hτ
  rcases h3 u w hu hw hc with ⟨hpu, hpw⟩ | ⟨hpu, hpw⟩ <;> cases ep
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hpu.2 τ, hUin τ⟩
  · exact h2 w hw τ₀ ⟨hwin, hpw.2 τ₀⟩
  · exact h2 w hw τ₀ ⟨hpw.2 τ₀, hwin⟩
  · obtain ⟨τ⟩ := hpu.1
    exact h2 u hu τ ⟨hUin τ, hpu.2 τ⟩

end GlobalTheory.TypeConjSplit
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AmbientTypeConjugatePlaceAtSplitPrimeStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem _root_.GlobalTheory.T.ambientType_conjugatePlace_at_splitPrime : ∀ (D : D7) (i : D.nd.Loc) (ep : Bool), GlobalTheory.IndefiniteRowSideFullHecke.SplitPlaceTypes.SplitRowPrime D.host (D.nd.l i) → EmbeddingTypes.ambTypeD (D := D) i ep := by
  first | exact @GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow | exact GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow | (intros; apply GlobalTheory.TypeConjSplit.ambTypeD_of_splitRow <;> assumption)
end
end
