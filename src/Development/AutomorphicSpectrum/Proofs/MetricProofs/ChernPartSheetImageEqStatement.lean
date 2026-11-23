module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.SheetUnsheet
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
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtaleOverIntegersLocalizationStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EtalePolynomialBaseChangeIffStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRangeStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartOverIntegers
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRange
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SheetIsOpenEmbeddingRangeStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernDensitySheetEq

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ZDens

theorem chernDens_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart t τ D), (∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y) → ∀ y ∈ c.e.source, c'.chernDens ψ (sheet t τ y) = c.chernDens (φ σ) y := by
  intro k _ _ _ _ X p t τ σ D B φ ψ hW hφ hψ c c' hm y hy
  obtain ⟨hy', he⟩ := hm y hy
  have hi := GlobalTheory.CxPts.mem_pick (φ σ).isLB y
  set i := GlobalTheory.CxPts.pick (φ σ).isLB y
  have hi' : sheet t τ y ∈ ptsIn t τ (B.U i) := hi
  rw [c'.chernDens_eq hψ hy' hi', c.chernDens_eq (hφ σ) hy hi, AlgChart.hess, AlgChart.hess, he]
  have ho := GlobalTheory.ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))
  have hmem := GlobalTheory.ChartGlue.mem_over c.e hy hi
  have e : (fun v => ((ψ.φ i (c'.e.symm v) : ℝ) : ℂ)) =ᶠ[𝓝 (c.e y)]
      fun v => (((φ σ).φ i (c.e.symm v) : ℝ) : ℂ) := by
    filter_upwards [ho.mem_nhds hmem] with v hv
    have hw := c.e.map_target hv.1
    obtain ⟨h₁, h₂⟩ := hm _ hw
    have hs : c'.e.symm v = sheet t τ (c.e.symm v) := by
      rw [← c'.e.left_inv h₁, h₂, c.e.right_inv hv.1]
    rw [hs, hW σ i _ hv.2]
  rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]

end GlobalTheory.CompanionTheory.Ar.ZDens
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernDensitySheetEqStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.chernDensity_sheet_eq : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (c : AlgChart p σ D) (c' : AlgChart t τ D), (∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y) → ∀ y ∈ c.e.source, c'.chernDens ψ (sheet t τ y) = c.chernDens (φ σ) y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ZDens.chernDens_sheet | exact GlobalTheory.CompanionTheory.Ar.ZDens.chernDens_sheet | (intros; apply GlobalTheory.CompanionTheory.Ar.ZDens.chernDens_sheet <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartFromIntegers

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown

theorem etale_res_int {X : Scheme.{0}} (t : X ⟶ Sp ℤ) {U : X.Opens} (hU : IsAffineOpen U) (n : Γ(X, U))
    {D : ℕ} (x : Fin D → Γ(X, U)) (h : (MvPolynomial.eval₂Hom (algX t U) x).Etale) :
    (MvPolynomial.eval₂Hom (Int.castRingHom Γ(X, X.basicOpen n))
      fun a => resG X (X.basicOpen_le n) (x a)).Etale := by
  have hloc := hU.isLocalization_basicOpen n
  have hres : (resG X (X.basicOpen_le n)).Etale :=
    RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway n)
  have hcomp := RingHom.Etale.stableUnderComposition _ _ h hres
  rw [MvPolynomial.comp_eval₂Hom] at hcomp
  rwa [show (resG X (X.basicOpen_le n)).comp (algX t U) = Int.castRingHom _ from RingHom.ext_int _ _] at hcomp

theorem isUnit_natCast_basicOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (N : ℕ) :
    IsUnit (N : Γ(X, X.basicOpen (N : Γ(X, U)))) := by
  have hloc := hU.isLocalization_basicOpen (N : Γ(X, U))
  have := IsLocalization.Away.algebraMap_isUnit (S := Γ(X, X.basicOpen (N : Γ(X, U)))) (N : Γ(X, U))
  simpa using this

theorem mem_ptsIn_basicOpen_natCast {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {U : X.Opens} {N : ℕ} (hN : N ≠ 0) {y : CxPts p σ} (hy : y ∈ ptsIn p σ U) :
    y ∈ ptsIn p σ (X.basicOpen (N : Γ(X, U))) := by
  refine (mem_ptsIn_basicOpen hy _).2 ?_
  have h := ev_algX hy (N : k)
  rw [map_natCast, map_natCast] at h
  rw [h]
  exact_mod_cast hN

end GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown


open GlobalTheory.CompanionTheory.Ar.BaseZ.ChartDown in
theorem GlobalTheory.CompanionTheory.Ar.BaseZ.exists_chart_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (c' : AlgChart t τ D), Nonempty (CxPts p σ) → ∃ c : AlgChart p σ D, c.e.source = sheet t τ ⁻¹' c'.e.source ∧ ∀ y ∈ c.e.source, c'.e (sheet t τ y) = c.e y := by
  intro k _ _ _ _ X p t τ σ D c' hne
  obtain ⟨N, hN0, hN⟩ := GlobalTheory.T.etale_over_integers_localization k
  obtain ⟨hemb, -⟩ := GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ
  have hle := X.basicOpen_le (N : Γ(X, c'.U))
  have hetZ := etale_res_int t c'.affine (N : Γ(X, c'.U)) c'.x c'.etale
  have hetk := (GlobalTheory.T.etale_polynomial_base_change_iff k _ N hN (algX p (X.basicOpen (N : Γ(X, c'.U))))
    (isUnit_natCast_basicOpen c'.affine N) D _).2 hetZ
  let s := IsOpenEmbedding.toOpenPartialHomeomorph (sheet t τ : CxPts p σ → CxPts t τ) hemb
  have hs : (s : CxPts p σ → CxPts t τ) = sheet t τ := IsOpenEmbedding.toOpenPartialHomeomorph_apply _ hemb
  have hss : s.source = Set.univ := IsOpenEmbedding.toOpenPartialHomeomorph_source _ hemb
  have hst : s.target = Set.range (sheet t τ : CxPts p σ → CxPts t τ) :=
    IsOpenEmbedding.toOpenPartialHomeomorph_target _ hemb
  have hsrc : (s.trans c'.e).source = sheet t τ ⁻¹' c'.e.source := by
    rw [OpenPartialHomeomorph.trans_source, hss, Set.univ_inter, hs]
  have happ : ∀ y, (s.trans c'.e) y = c'.e (sheet t τ y) := fun y => by
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hs]
  have hsym : ∀ v ∈ (s.trans c'.e).target, sheet t τ ((s.trans c'.e).symm v) = c'.e.symm v := by
    intro v hv
    rw [OpenPartialHomeomorph.trans_target] at hv
    have h2 : c'.e.symm v ∈ s.target := hv.2
    rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.coe_trans,
      Function.comp_apply, ← hs]
    exact s.right_inv h2
  refine ⟨{ e := s.trans c'.e
            U := X.basicOpen (N : Γ(X, c'.U))
            affine := c'.affine.basicOpen _
            x := fun a => resG X hle (c'.x a)
            etale := hetk
            source_subset := ?_
            apply_eq := ?_
            holo := ?_ }, hsrc, fun y _ => (happ y).symm⟩
  · intro y hy
    rw [hsrc] at hy
    have h1 : sheet t τ y ∈ ptsIn t τ c'.U := c'.source_subset hy
    exact mem_ptsIn_basicOpen_natCast hN0 (show y ∈ ptsIn p σ c'.U from h1)
  · intro y hy a
    rw [hsrc] at hy
    have h1 : sheet t τ y ∈ ptsIn t τ c'.U := c'.source_subset hy
    have hB := mem_ptsIn_basicOpen_natCast hN0 (show y ∈ ptsIn p σ c'.U from h1)
    rw [happ, c'.apply_eq _ hy a, ev_res hle hB]
    rfl
  · intro W f
    refine ((c'.holo W f).mono ?_).congr ?_
    · rintro v ⟨hv, hw⟩
      refine ⟨?_, ?_⟩
      · rw [OpenPartialHomeomorph.trans_target] at hv
        exact hv.1
      · show c'.e.symm v ∈ ptsIn t τ W
        rw [← hsym v hv]
        exact hw
    · rintro v ⟨hv, -⟩
      show ev p σ W f _ = ev t τ W f (c'.e.symm v)
      rw [← hsym v hv]
      rfl
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartFromIntegersStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.exists_algChart_from_integers : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (c' : AlgChart t τ D), Nonempty (CxPts p σ) → ∃ c : AlgChart p σ D, c.e.source = sheet t τ ⁻¹' c'.e.source ∧ ∀ y ∈ c.e.source, c'.e (sheet t τ y) = c.e y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.exists_chart_sheet | exact GlobalTheory.CompanionTheory.Ar.BaseZ.exists_chart_sheet | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.exists_chart_sheet <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAlgChartOverIntegersStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.exists_algChart_over_integers : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ) (σ : k →+* ℂ) (D : ℕ) (c : AlgChart p σ D), ∃ c' : AlgChart t τ D, c'.e.source = sheet t τ '' c.e.source ∧ ∀ y ∈ c.e.source, c'.e (sheet t τ y) = c.e y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.algChart_toZ | exact GlobalTheory.CompanionTheory.Ar.BaseZ.algChart_toZ | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.algChart_toZ <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernPartSheetImageEq

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (ε : ℤˣ) (S : Set (CxPts p σ)), MeasurableSet S → ψ.chernPart D ε (sheet t τ '' S) = (φ σ).chernPart D ε S := by
  intro k _ _ _ _ X p t τ hp σ D B φ ψ hW hφ hψ ε S hS
  have hSC : ∀ σ' : k →+* ℂ, SecondCountableTopology (CxPts p σ') := by
    obtain ⟨N, i, hi, hpe⟩ := hp
    intro σ'
    haveI := hi
    subst hpe
    exact GlobalTheory.CxPts.secondCountableTopology _ σ'
  haveI hscp : SecondCountableTopology (CxPts p σ) := hSC σ
  haveI hsct : SecondCountableTopology (CxPts t τ) := by
    haveI : Finite (k →+* ℂ) := Sheet.finite_ringHom k
    have hopen : ∀ σ' : k →+* ℂ, IsOpen (Set.range (sheet t τ : CxPts p σ' → CxPts t τ)) :=
      fun σ' => (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ').1.isOpen_range
    haveI : ∀ σ' : k →+* ℂ,
        SecondCountableTopology (Set.range (sheet t τ : CxPts p σ' → CxPts t τ)) := by
      intro σ'
      haveI := hSC σ'
      exact (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ').1.isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
    refine TopologicalSpace.secondCountableTopology_of_countable_cover hopen ?_
    exact Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 ⟨emb p y, unsheet p y, sheet_unsheet p y⟩
  have hemb : Topology.IsOpenEmbedding (sheet t τ : CxPts p σ → CxPts t τ) :=
    (GlobalTheory.T.sheet_isOpenEmbedding_range k X p t τ σ).1
  have hme : MeasurableEmbedding (sheet t τ : CxPts p σ → CxPts t τ) :=
    hemb.measurableEmbedding
  have key : ∀ (c : AlgChart p σ D) (A : Set (CxPts p σ)), MeasurableSet A → A ⊆ c.e.source →
      ψ.chernPart D ε (sheet t τ '' A) = (φ σ).chernPart D ε A := by
    intro c A hA hAc
    obtain ⟨c', hc's, hc'e⟩ := GlobalTheory.T.exists_algChart_over_integers k X p t τ σ D c
    have hcomp : ∀ y ∈ c.e.source, sheet t τ y ∈ c'.e.source ∧ c'.e (sheet t τ y) = c.e y :=
      fun y hy => ⟨hc's ▸ Set.mem_image_of_mem _ hy, hc'e y hy⟩
    have hdens := GlobalTheory.T.chernDensity_sheet_eq k X p t τ σ D B φ ψ hW hφ hψ c c' hcomp
    have hA' : sheet t τ '' A ⊆ c'.e.source := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hcomp y (hAc hy)).1
    rw [GlobalTheory.Weight.chernPart_apply hψ ε c' (hme.measurableSet_image' hA) hA',
      GlobalTheory.Weight.chernPart_apply (hφ σ) ε c hA hAc]
    have himg : c'.e '' (sheet t τ '' A) = c.e '' A := by
      rw [Set.image_image]
      exact Set.image_congr fun y hy => (hcomp y (hAc hy)).2
    rw [himg]
    refine MeasureTheory.setLIntegral_congr_fun (GlobalTheory.ChartGlue.measurableSet_image c.e hA hAc) ?_
    rintro _ ⟨y, hy, rfl⟩
    dsimp only
    have h1 : c.e.symm (c.e y) = y := c.e.left_inv (hAc hy)
    have h2 : c'.e.symm (c.e y) = sheet t τ y := by
      rw [← (hcomp y (hAc hy)).2]
      exact c'.e.left_inv (hcomp y (hAc hy)).1
    rw [h1, h2, hdens y (hAc hy)]
  have hμA : ∀ A : Set (CxPts p σ),
      Measure.comap (sheet t τ) (ψ.chernPart D ε) A = ψ.chernPart D ε (sheet t τ '' A) :=
    fun A => hme.comap_apply _ A
  have hUo : IsOpen (⋃ c : AlgChart p σ D, c.e.source) := isOpen_iUnion fun c => c.e.open_source
  have hUm : MeasurableSet (⋃ c : AlgChart p σ D, c.e.source) := hUo.measurableSet
  have hzν : ((φ σ).chernPart D ε).restrict (⋃ c : AlgChart p σ D, c.e.source)ᶜ = 0 := by
    refine Measure.restrict_eq_zero.2 (GlobalTheory.Weight.chernPart_eq_zero ε hUm.compl fun c => ?_)
    rw [Set.disjoint_left]
    intro y hy hy'
    exact hy' (Set.mem_iUnion.2 ⟨c, hy⟩)
  have hzμ : (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict
      (⋃ c : AlgChart p σ D, c.e.source)ᶜ = 0 := by
    refine Measure.restrict_eq_zero.2 ?_
    rw [hμA]
    refine GlobalTheory.Weight.chernPart_eq_zero ε (hme.measurableSet_image' hUm.compl) fun c' => ?_
    rw [Set.disjoint_left]
    rintro _ hz ⟨y, hy, rfl⟩
    obtain ⟨c, hcs, -⟩ := GlobalTheory.T.exists_algChart_from_integers k X p t τ σ D c' ⟨y⟩
    exact hy (Set.mem_iUnion.2 ⟨c, by rw [hcs]; exact hz⟩)
  have hU : (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict
      (⋃ c : AlgChart p σ D, c.e.source) = ((φ σ).chernPart D ε).restrict
      (⋃ c : AlgChart p σ D, c.e.source) := by
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun c : AlgChart p σ D => c.e.source) fun c => c.e.open_source
    have hU' : (⋃ c : AlgChart p σ D, c.e.source) = ⋃ c : T, (c : AlgChart p σ D).e.source := by
      rw [Set.iUnion_subtype]
      exact hTU.symm
    haveI : Countable T := hTc.to_subtype
    rw [hU', Measure.restrict_iUnion_congr]
    intro c
    ext A hA
    have hAm : MeasurableSet (A ∩ (c : AlgChart p σ D).e.source) :=
      hA.inter (c : AlgChart p σ D).e.open_source.measurableSet
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA, hμA]
    exact key c _ hAm Set.inter_subset_right
  have hμν : Measure.comap (sheet t τ) (ψ.chernPart D ε) = (φ σ).chernPart D ε := by
    calc Measure.comap (sheet t τ) (ψ.chernPart D ε)
        = (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict (⋃ c : AlgChart p σ D, c.e.source)
          + (Measure.comap (sheet t τ) (ψ.chernPart D ε)).restrict
            (⋃ c : AlgChart p σ D, c.e.source)ᶜ := (Measure.restrict_add_restrict_compl hUm).symm
      _ = ((φ σ).chernPart D ε).restrict (⋃ c : AlgChart p σ D, c.e.source)
          + ((φ σ).chernPart D ε).restrict (⋃ c : AlgChart p σ D, c.e.source)ᶜ := by
        rw [hU, hzμ, hzν]
      _ = (φ σ).chernPart D ε := Measure.restrict_add_restrict_compl hUm
  rw [← hμA, hμν]
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ChernPartSheetImageEqStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem _root_.GlobalTheory.T.chernPart_sheet_image_eq : ∀ (k : Type) [CommRing k] [IsDomain k] [CharZero k] [Module.Finite ℤ k] (X : Scheme.{0}) (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (τ : ℤ →+* ℂ), IsProjOver p → ∀ (σ : k →+* ℂ) (D : ℕ) (B : LB X) (φ : ∀ σ : k →+* ℂ, Weight p σ B) (ψ : Weight t τ B), WOver φ ψ → (∀ σ, (φ σ).IsCInf) → ψ.IsCInf → ∀ (ε : ℤˣ) (S : Set (CxPts p σ)), MeasurableSet S → ψ.chernPart D ε (sheet t τ '' S) = (φ σ).chernPart D ε S := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet | exact GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet | (intros; apply GlobalTheory.CompanionTheory.Ar.BaseZ.chernPart_sheet <;> assumption)
end
end
