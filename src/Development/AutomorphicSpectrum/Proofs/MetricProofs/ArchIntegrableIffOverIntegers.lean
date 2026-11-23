module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernPartSheetImageEqStatement
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRange
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRangeStatement
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormSheetEqStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.IntegrableOnAndSetIntegralOfEmbeddings

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Metric

theorem measure_eq_sum_map_of_embeddings {α : Type} [Fintype α] {Y : Type} [MeasurableSpace Y]
    {Z : α → Type} [∀ a, MeasurableSpace (Z a)] {s : ∀ a, Z a → Y}
    (hs : ∀ a, MeasurableEmbedding (s a)) (hu : ∀ y, ∃! a, y ∈ Set.range (s a))
    {ν : Measure Y} {μ : ∀ a, Measure (Z a)}
    (hν : ∀ a (S : Set (Z a)), MeasurableSet S → ν (s a '' S) = μ a S) :
    ν = ∑ a, Measure.map (s a) (μ a) := by
  ext T hT
  rw [Measure.finsetSum_apply]
  have hcover : T = ⋃ a, T ∩ Set.range (s a) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro hy
      obtain ⟨a, ha, -⟩ := hu y
      exact ⟨a, hy, ha⟩
    · rintro ⟨a, hy, -⟩
      exact hy
  have hdisj : Pairwise (Function.onFun Disjoint fun a => T ∩ Set.range (s a)) := by
    intro a b hab
    rw [Function.onFun, Set.disjoint_left]
    rintro y ⟨-, hya⟩ ⟨-, hyb⟩
    obtain ⟨a', -, ha'⟩ := hu y
    exact hab ((ha' a hya).trans (ha' b hyb).symm)
  have hmeas : ∀ a, MeasurableSet (T ∩ Set.range (s a)) := fun a =>
    hT.inter (hs a).measurableSet_range
  rw [show ν T = ν (⋃ a, T ∩ Set.range (s a)) by rw [← hcover], measure_iUnion hdisj hmeas,
    tsum_fintype]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(hs a).map_apply, ← hν a _ ((hs a).measurable hT), Set.image_preimage_eq_inter_range]

theorem integrableOn_and_setIntegral_of_embeddings :
    ∀ (α : Type) [Finite α] (Y : Type) [MeasurableSpace Y] (Z : α → Type)
      [∀ a, MeasurableSpace (Z a)] (s : ∀ a, Z a → Y), (∀ a, MeasurableEmbedding (s a)) →
      (∀ y, ∃! a, y ∈ Set.range (s a)) → ∀ (ν : Measure Y) (μ : ∀ a, Measure (Z a)),
      (∀ a (S : Set (Z a)), MeasurableSet S → ν (s a '' S) = μ a S) →
      ∀ (S : Set Y), MeasurableSet S → ∀ f : Y → ℝ,
      (IntegrableOn f S ν ↔ ∀ a, IntegrableOn (fun z => f (s a z)) (s a ⁻¹' S) (μ a)) ∧
      (IntegrableOn f S ν →
        ∫ y in S, f y ∂ν = ∑ᶠ a, ∫ z in s a ⁻¹' S, f (s a z) ∂(μ a)) := by
  intro α _ Y _ Z _ s hs hu ν μ hν S hS f
  haveI := Fintype.ofFinite α
  have hνeq := measure_eq_sum_map_of_embeddings hs hu hν
  have hres : ν.restrict S = ∑ a, (Measure.map (s a) (μ a)).restrict S := by
    ext T hT
    rw [hνeq, Measure.restrict_apply hT, Measure.finsetSum_apply, Measure.finsetSum_apply]
    simp only [Measure.restrict_apply hT]
  have hint : IntegrableOn f S ν ↔ ∀ a, IntegrableOn (fun z => f (s a z)) (s a ⁻¹' S) (μ a) := by
    rw [IntegrableOn, hres, integrable_finsetSum_measure]
    simp only [Finset.mem_univ, forall_const]
    exact forall_congr' fun a => (hs a).integrableOn_map_iff
  refine ⟨hint, fun hf => ?_⟩
  have hf' : ∀ a ∈ Finset.univ, Integrable f ((Measure.map (s a) (μ a)).restrict S) := fun a _ =>
    (hs a).integrableOn_map_iff.mpr (hint.mp hf a)
  rw [finsum_eq_sum_of_fintype, hres, integral_finsetSum_measure hf']
  exact Finset.sum_congr rfl fun a _ => (hs a).setIntegral_map _ _

end GlobalTheory.CompanionTheory.Metric
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernIntegrableOnIffSheets

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Metric

theorem chernInt_eq_finsum_sheets : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (S : Set (CxPts t τ)), MeasurableSet S → ∀ f : CxPts t τ → ℝ, (ψ.ChernIntegrableOn D S f ↔ ∀ σ, (φ σ).ChernIntegrableOn D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) ∧ (ψ.ChernIntegrableOn D S f → ψ.chernInt D S f = ∑ᶠ σ, (φ σ).chernInt D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) := by
  intro k _ _ _ _ X p t τ hP D B φ ψ hW hφ hψ S hS f
  have hemb : ∀ σ : k →+* ℂ, MeasurableEmbedding (sheet (p := p) (σ := σ) t τ) := fun σ =>
    (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1.measurableEmbedding
  have huniq : ∀ y : CxPts t τ, ∃! σ : k →+* ℂ, y ∈ Set.range (sheet (p := p) (σ := σ) t τ) := by
    intro y
    refine ⟨emb p y, ?_, ?_⟩
    · show y ∈ Set.range (sheet (p := p) (σ := emb p y) t τ)
      rw [(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ _).2]
      rfl
    · intro σ hσ
      rw [(GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).2] at hσ
      exact hσ.symm
  have hfin : Finite (k →+* ℂ) := Sheet.finite_ringHom k
  have key := fun ε : ℤˣ => integrableOn_and_setIntegral_of_embeddings (k →+* ℂ) (CxPts t τ)
    (fun σ => CxPts p σ) (fun σ => sheet (p := p) (σ := σ) t τ) hemb huniq (ψ.chernPart D ε)
    (fun σ => (φ σ).chernPart D ε) (fun σ S' hS' => GlobalTheory.T.chernPart_sheet_image_eq k X p t τ hP σ D B φ ψ hW hφ hψ ε S' hS') S hS f
  obtain ⟨h1, h1'⟩ := key 1
  obtain ⟨h2, h2'⟩ := key (-1)
  refine ⟨?_, ?_⟩
  · simp only [GlobalTheory.Weight.ChernIntegrableOn]
    rw [h1, h2]
    exact forall_and.symm
  · intro hI
    simp only [GlobalTheory.Weight.chernInt]
    rw [h1' hI.1, h2' hI.2, finsum_sub_distrib (Set.toFinite _) (Set.toFinite _)]

end GlobalTheory.CompanionTheory.Metric
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernIntegrableOnIffSheetsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.chernIntegrableOn_iff_sheets : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (S : Set (CxPts t τ)), MeasurableSet S → ∀ f : CxPts t τ → ℝ, (ψ.ChernIntegrableOn D S f ↔ ∀ σ, (φ σ).ChernIntegrableOn D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) ∧ (ψ.ChernIntegrableOn D S f → ψ.chernInt D S f = ∑ᶠ σ, (φ σ).chernInt D (sheet t τ ⁻¹' S) (fun z => f (sheet t τ z))) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.chernInt_eq_finsum_sheets | exact GlobalTheory.CompanionTheory.Metric.chernInt_eq_finsum_sheets | (intros; apply GlobalTheory.CompanionTheory.Metric.chernInt_eq_finsum_sheets <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchIntegrableIffOverIntegers

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

private theorem chernIntegrableOn_and_chernInt_congr {k : Type} [CommRing k] {Y : Scheme} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    {B : ReciprocityTheory.ChartRestriction.G.Semi.LB Y} (φ : GlobalTheory.Weight q σ B) (d : ℕ) {S : Set (GlobalTheory.CxPts q σ)}
    (hS : MeasurableSet S) {f g : GlobalTheory.CxPts q σ → ℝ} (h : Set.EqOn f g S) :
    (φ.ChernIntegrableOn d S f ↔ φ.ChernIntegrableOn d S g) ∧ φ.chernInt d S f = φ.chernInt d S g := by
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.Weight.ChernIntegrableOn
    rw [integrableOn_congr_fun h hS, integrableOn_congr_fun h hS]
  · unfold GlobalTheory.Weight.chernInt
    rw [setIntegral_congr_fun hS h, setIntegral_congr_fun hS h]

theorem archInt_over_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (D : ℕ), IsArithVar p D → ∀ (N M : HermLB p) (ψ : Weight t τ N.B) (ν : Weight t τ M.B), WOver N.φ ψ → WOver M.φ ν → ψ.IsCInf → ∀ (e : ℕ) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (ψ.ChernIntegrableOn e (offSupp t τ (M.div hr)) (logNorm ν r) ↔ N.ArchIntegrable M e hr) ∧ (N.ArchIntegrable M e hr → ψ.chernInt e (offSupp t τ (M.div hr)) (logNorm ν r) = N.archInt M e hr) := by
  intro k _ X _ p t τ D hX N M ψ ν hψN hνM hψ e r hr
  by_cases hσ : Nonempty (k →+* ℂ)
  · obtain ⟨σ₀⟩ := hσ
    haveI : CharZero k := σ₀.charZero
    haveI := hX.isDomain
    haveI := hX.finite
    have hS : MeasurableSet (offSupp t τ (M.div hr)) := (GlobalTheory.CxPts.isOpen_ptsIn _).measurableSet
    obtain ⟨h1, h2⟩ := GlobalTheory.T.chernIntegrableOn_iff_sheets k X p t τ hX.isProjOver e N.B N.φ ψ hψN N.cInf hψ _ hS (logNorm ν r)
    have hmeas : ∀ σ : k →+* ℂ, MeasurableSet (offSupp p σ (M.div hr)) :=
      fun σ => (GlobalTheory.CxPts.isOpen_ptsIn _).measurableSet
    have hEq : ∀ σ : k →+* ℂ, Set.EqOn (fun z => logNorm ν r (GlobalTheory.CompanionTheory.Ar.BaseZ.sheet t τ z))
        (logNorm (M.φ σ) r) (offSupp p σ (M.div hr)) :=
      fun σ y hy => GlobalTheory.T.logNorm_sheet_eq k X p t τ M.B M.φ ν hνM r hr σ y hy
    have hiff : ψ.ChernIntegrableOn e (offSupp t τ (M.div hr)) (logNorm ν r) ↔ N.ArchIntegrable M e hr := by
      rw [h1]
      unfold GlobalTheory.HermLB.ArchIntegrable
      exact forall_congr' fun σ => (chernIntegrableOn_and_chernInt_congr (N.φ σ) e (hmeas σ) (hEq σ)).1
    refine ⟨hiff, fun hInt => ?_⟩
    rw [h2 (hiff.mpr hInt)]
    unfold GlobalTheory.HermLB.archInt
    exact finsum_congr fun σ => (chernIntegrableOn_and_chernInt_congr (N.φ σ) e (hmeas σ) (hEq σ)).2
  · have hE : IsEmpty (k →+* ℂ) := not_nonempty_iff.mp hσ
    haveI : IsEmpty (GlobalTheory.CxPts t τ) := ⟨fun y => hE.false (Spec.preimage (Subtype.val y ≫ p)).hom⟩
    have hS0 : offSupp t τ (M.div hr) = ∅ := Set.eq_empty_of_isEmpty _
    have hA : N.ArchIntegrable M e hr := by
      unfold GlobalTheory.HermLB.ArchIntegrable
      intro σ
      exact hE.elim σ
    refine ⟨⟨fun _ => hA, fun _ => ?_⟩, fun _ => ?_⟩
    · unfold GlobalTheory.Weight.ChernIntegrableOn
      rw [hS0]
      exact ⟨integrableOn_empty, integrableOn_empty⟩
    · unfold GlobalTheory.HermLB.archInt GlobalTheory.Weight.chernInt
      rw [hS0, finsum_of_isEmpty]
      simp

end GlobalTheory.CompanionTheory.Ar.BaseZ
end
end
