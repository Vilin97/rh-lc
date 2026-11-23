module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Imports
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
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleIntersectionSymmetryStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementAStatement
import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementDStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SameGenericLinearEquivStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionComparison

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : (∀ k, ι k) → AddSubgroup V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), QuotExact O x A A' E.lat E'.lat C.lat C'.lat → ∃ E'' : ChartBundle O (mseg x) N V, LatLE O x E' E'' ∧ LatLE O x E'' E ∧ QuotEquiv O x A A' E''.lat E'.lat ∧ QuotEquiv O x E.lat E''.lat C.lat C'.lat := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N₀ N N₂ V₀ _ _ V _ _ V₂ _ _ A A' E E' C C' hQ
  obtain ⟨Γ, Δ, hΓ, hΔ, hX⟩ := hQ
  have bundleOfFamily : ∀ (N : ℕ) (W : Type) [AddCommGroup W] [Module Ω W],
      (∀ Γ : (∀ k, ι k) → AddSubgroup W, IsLatFamily O x Γ →
        (∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (Γ s)) →
        ∃ E : ChartBundle O (mseg x) N W, ∀ s, mseg x s ≠ 0 → E.lat s = Γ s) ∧
      ∀ E : ChartBundle O (mseg x) N W, IsLatFamily O x E.lat ∧
        ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (E.lat s) := by
    classical
    intro N W _ _
    refine ⟨fun Γ hfam hloc => ?_, fun E => ⟨⟨fun s _ => E.stable s, fun s t hs ht => E.overlap s t hs ht⟩, fun s hs => ⟨E.stable s, E.frame s hs⟩⟩⟩
    refine ⟨{ lat := fun s => if mseg x s = 0 then ⊥ else Γ s
              stable := ?_
              frame := ?_
              overlap := ?_ }, ?_⟩
    · intro s a ha e he
      by_cases h : mseg x s = 0
      · simp only [h, if_true, AddSubgroup.mem_bot] at he ⊢
        rw [he, smul_zero]
      · simp only [h, if_false] at he ⊢
        exact hfam.1 s h a ha e he
    · intro s hs
      simp only [hs, if_false]
      exact (hloc s hs).2
    · intro s t hs ht e he
      simp only [hs, ht, if_false] at he ⊢
      exact hfam.2 s t hs ht e he
    · intro s hs
      simp only [hs, if_false]
  obtain ⟨F, hF⟩ : ∃ F : (∀ k, ι k) → AddSubgroup V,
      F = fun s => (Δ s).comap (AddMonoidHom.inl V V₂) := ⟨_, rfl⟩
  have memF : ∀ s b, b ∈ F s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s b
    subst hF
    exact Iff.rfl
  have hFlat : IsLatFamily O x F := by
    refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
    · have h := hΔ.1.1 s hs a ha (v, 0) ((memF s v).1 hv)
      rw [memF]
      simpa using h
    · obtain ⟨m, hm⟩ := hΔ.1.2 s t hs ht (v, 0) ((memF s v).1 hv)
      refine ⟨m, ?_⟩
      rw [memF]
      simpa using hm
  have hFfree : ∀ s, mseg x s ≠ 0 → LocFree (chartRing O (mseg x) s) N (F s) := by
    intro s hs
    have hE := ((bundleOfFamily N V).2 E).2 s hs
    have hC := ((bundleOfFamily N₂ V₂).2 C).2 s hs
    have hC' := ((bundleOfFamily N₂ V₂).2 C').2 s hs
    have h := (GlobalTheory.CompanionTheory.Ar.Num.LocFreeSchanuel.main (chartRing O (mseg x) s) N N₂ (E.lat s) (C.lat s)
      (C'.lat s) (Δ s) hE hC hC' (fun a ha v hv => hΔ.1.1 s hs a ha v hv)
      (fun v w h => (hΔ.2 s hs).1 v w h) (fun v hv => (hΔ.2 s hs).2.1 v hv)
      (fun w => (hΔ.2 s hs).2.2.1 w) (fun w hw => (hX s hs).2.1 w hw)).2
    rw [hF]
    exact h
  obtain ⟨E'', hE''⟩ := (bundleOfFamily N V).1 F hFlat hFfree
  have memE'' : ∀ s, mseg x s ≠ 0 → ∀ b, b ∈ E''.lat s ↔ (b, (0 : V₂)) ∈ Δ s := by
    intro s hs b
    rw [hE'' s hs, memF]
  refine ⟨E'', fun s hs b hb => ?_, fun s hs b hb => ?_,
    ⟨Γ, ⟨hΓ.1, fun s hs => ⟨fun v w h => ⟨((hΓ.2 s hs).1 v w h).1,
        (memE'' s hs w).2 (((hX s hs).2.2 w).2 ⟨v, h⟩)⟩,
      (hΓ.2 s hs).2.1, (hΓ.2 s hs).2.2.1, (hΓ.2 s hs).2.2.2⟩⟩,
      fun s hs => ⟨(hX s hs).1, fun w hw => ((hX s hs).2.2 w).1 ((memE'' s hs w).1 hw)⟩⟩,
    ⟨Δ, ⟨hΔ.1, fun s hs => ⟨(hΔ.2 s hs).1, (hΔ.2 s hs).2.1, (hΔ.2 s hs).2.2.1,
        fun v hv => (memE'' s hs v).1 hv⟩⟩,
      fun s hs => ⟨fun v hv => (memE'' s hs v).2 hv, (hX s hs).2.1⟩⟩⟩
  · exact (memE'' s hs b).2 ((hΔ.2 s hs).2.2.2 b hb)
  · exact ((hΔ.2 s hs).1 b 0 ((memE'' s hs b).1 hb)).1

end GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionComparisonStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.chart_bundle_extension_comparison : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : (∀ k, ι k) → AddSubgroup V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), QuotExact O x A A' E.lat E'.lat C.lat C'.lat → ∃ E'' : ChartBundle O (mseg x) N V, LatLE O x E' E'' ∧ LatLE O x E'' E ∧ QuotEquiv O x A A' E''.lat E'.lat ∧ QuotEquiv O x E.lat E''.lat C.lat C'.lat := by
  exact @GlobalTheory.CompanionTheory.Ar.Num.QuotExactMiddle.main
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionIntersection

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotAdd

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : ChartBundle O (mseg x) N₀ V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x A A' → SameGeneric O x E E' → SameGeneric O x C C' → QuotExact O x A.lat A'.lat E.lat E'.lat C.lat C'.lat → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ck O x d N₀ A A' k L Q + ck O x d N₂ C C' k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d N₀ N N₂ V₀ _ _ V _ _ V₂ _ _ A A' E E' C C' hM hA hE hC hX k hk1 hk2 q L Q hQ
  obtain ⟨E'', h1, h2, h3, h4⟩ :=
    GlobalTheory.T.chart_bundle_extension_comparison O Ω K ι x N₀ N N₂ V₀ V V₂ A.lat A'.lat E E' C C' hX
  have hEE'' : SameGeneric O x E E'' := fun s hs =>
    ⟨fun v hv => by
        obtain ⟨c, hc, hcv⟩ := (hE s hs).1 v hv
        exact ⟨c, hc, h1 s hs hcv⟩,
      fun v hv => ⟨1, one_ne_zero, by simpa using h2 s hs hv⟩⟩
  have hE''E' : SameGeneric O x E'' E' := fun s hs =>
    ⟨fun v hv => (hE s hs).1 v (h2 s hs hv),
      fun v hv => ⟨1, one_ne_zero, by simpa using h1 s hs hv⟩⟩
  have hcoc := (GlobalTheory.T.dvr_bundle_statement_a O Ω K ι x d N V E E'' E' hM hEE'' hE''E' k hk1 hk2 q L Q hQ).1
  have hAe := GlobalTheory.T.chart_bundle_intersection_symmetry O Ω K ι x d N₀ N V₀ V A A' E'' E' hM hA hE''E' h3 k hk1 hk2 q L Q hQ
  have hCe := GlobalTheory.T.chart_bundle_intersection_symmetry O Ω K ι x d N N₂ V V₂ E E'' C C' hM hEE'' hC h4 k hk1 hk2 q L Q hQ
  rw [hcoc, hAe, hCe, add_comm]

end GlobalTheory.CompanionTheory.Ar.Num.QuotAdd
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionIntersectionStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.chart_bundle_extension_intersection : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : ChartBundle O (mseg x) N₀ V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x A A' → SameGeneric O x E E' → SameGeneric O x C C' → QuotExact O x A.lat A'.lat E.lat E'.lat C.lat C'.lat → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ck O x d N₀ A A' k L Q + ck O x d N₂ C C' k L Q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.QuotAdd.main | exact GlobalTheory.CompanionTheory.Ar.Num.QuotAdd.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.QuotAdd.main <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLieBundleIntersection

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.HodgeTate

theorem algebraMap_ne_zero_of_model {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {x : (Σ k, ι k) → Ω} {d : ℕ}
    (hm : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d)
    {w : O} (hw : w ≠ 0) : algebraMap O Ω w ≠ 0 := by
  intro h0
  apply hw
  have hmem : w ∈ (mcIdeal O x).comap (C : O →+* MvPolynomial (Σ k, ι k) O) := by
    rw [Ideal.mem_comap]
    show _ = _
    have : (C w : MvPolynomial (Σ k, ι k) O) = algebraMap O _ w := rfl
    rw [this, AlgHom.commutes]
    simp [MvPolynomial.algebraMap_eq, h0]
  rw [hm.2.2.1] at hmem
  simpa using hmem

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d r s n : ℕ) (VL : Type) [AddCommGroup VL] [Module Ω VL] (VO : Type) [AddCommGroup VO] [Module Ω VO] (VH : Type) [AddCommGroup VH] [Module Ω VH] (Lie W La : ChartBundle O (mseg x) r VL) (om omHT : ChartBundle O (mseg x) s VO) (T H : ChartBundle O (mseg x) n VH) (w : O), w ≠ 0 → GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → LatLE O x Lie W → LatLE O x W La → IsScaled x (algebraMap O Ω w) La.lat Lie.lat → SameGeneric O x om omHT → SameGeneric O x H T → QuotExact O x La.lat W.lat H.lat T.lat om.lat omHT.lat → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d r Lie W k L Q + ck O x d s om omHT k L Q = ck O x d n H T k L Q - (k : ℤ) * rootNum O x d r Lie (psum (Fin r) ℤ (k - 1)) L Q w := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d r s n VL _ _ VO _ _ VH _ _ Lie W La om omHT T H w hw hm hLW hWL hsc
    hom hHT hex k hk1 hk2 q L Q hQ
  have hw' : algebraMap O Ω w ≠ 0 := algebraMap_ne_zero_of_model hm hw
  have hscale : ∀ s, mseg x s ≠ 0 → ∀ v ∈ La.lat s, algebraMap O Ω w • v ∈ Lie.lat s :=
    fun s hs v hv => (hsc s hs _).2 ⟨v, hv, rfl⟩
  have sWLa : SameGeneric O x W La := fun s hs =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hWL s hs hv⟩,
      fun v hv => ⟨w, hw, hLW s hs (hscale s hs v hv)⟩⟩
  have sLaW : SameGeneric O x La W := fun s hs => ⟨(sWLa s hs).2, (sWLa s hs).1⟩
  have sLieW : SameGeneric O x Lie W := fun s hs =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hLW s hs hv⟩,
      fun v hv => ⟨w, hw, hscale s hs v (hWL s hs hv)⟩⟩
  have sWLie : SameGeneric O x W Lie := fun s hs => ⟨(sLieW s hs).2, (sLieW s hs).1⟩
  have sLaLa : SameGeneric O x La La := fun s hs =>
    ⟨fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩, fun v hv => ⟨1, one_ne_zero, by simpa using hv⟩⟩
  have h1 := GlobalTheory.T.chart_bundle_extension_intersection O Ω K ι x d r n s VL VH VO La W H T om omHT hm sLaW hHT hom hex k hk1 hk2
    q L Q hQ
  have h2 := (GlobalTheory.T.dvr_bundle_statement_a O Ω K ι x d r VL La W Lie hm sLaW sWLie k hk1 hk2 q L Q hQ).1
  have h3 := (GlobalTheory.T.dvr_bundle_statement_a O Ω K ι x d r VL Lie W Lie hm sLieW sWLie k hk1 hk2 q L Q hQ).2
  have h4 := (GlobalTheory.T.dvr_bundle_statement_d O Ω K ι x d r VL La Lie w hw hm hsc k hk1 hk2 q L Q hQ).1
  have hcarry : ∀ s, mseg x s ≠ 0 → ∀ v,
      ((LinearEquiv.smulOfNeZero Ω VL _ hw') v ∈ Lie.lat s ↔ v ∈ La.lat s) ∧
        ((LinearEquiv.smulOfNeZero Ω VL _ hw') v ∈ Lie.lat s ↔ v ∈ La.lat s) := by
    intro s hs v
    have : (LinearEquiv.smulOfNeZero Ω VL _ hw') v ∈ Lie.lat s ↔ v ∈ La.lat s := by
      rw [LinearEquiv.smulOfNeZero_apply, hsc s hs]
      constructor
      · rintro ⟨e, he, hve⟩
        rwa [smul_right_injective VL hw' hve]
      · exact fun hv => ⟨v, hv, rfl⟩
    exact ⟨this, this⟩
  have hQ' : Q.IsHomogeneous (d - (k - 1)) := by
    have : d - (k - 1) = d + 1 - k := by omega
    rwa [this]
  have h5 := (GlobalTheory.T.same_generic_linear_equiv O Ω K ι x d hm r VL VL (LinearEquiv.smulOfNeZero Ω VL _ hw') La La Lie Lie
    sLaLa hcarry).2 (k - 1) (psum (Fin r) ℤ (k - 1)) (psum_isSymmetric _ _ _)
    (isHomogeneous_psum r (k - 1)) (by omega) q L Q hQ' w hw
  rw [h5]
  linarith

end GlobalTheory.CompanionTheory.Ar.Num.HodgeTate
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeLieBundleIntersectionStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

theorem _root_.GlobalTheory.T.hodge_lie_bundle_intersection : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d r s n : ℕ) (VL : Type) [AddCommGroup VL] [Module Ω VL] (VO : Type) [AddCommGroup VO] [Module Ω VO] (VH : Type) [AddCommGroup VH] [Module Ω VH] (Lie W La : ChartBundle O (mseg x) r VL) (om omHT : ChartBundle O (mseg x) s VO) (T H : ChartBundle O (mseg x) n VH) (w : O), w ≠ 0 → GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → LatLE O x Lie W → LatLE O x W La → IsScaled x (algebraMap O Ω w) La.lat Lie.lat → SameGeneric O x om omHT → SameGeneric O x H T → QuotExact O x La.lat W.lat H.lat T.lat om.lat omHT.lat → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d r Lie W k L Q + ck O x d s om omHT k L Q = ck O x d n H T k L Q - (k : ℤ) * rootNum O x d r Lie (psum (Fin r) ℤ (k - 1)) L Q w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.HodgeTate.main | exact GlobalTheory.CompanionTheory.Ar.Num.HodgeTate.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.HodgeTate.main <;> assumption)
end
end
