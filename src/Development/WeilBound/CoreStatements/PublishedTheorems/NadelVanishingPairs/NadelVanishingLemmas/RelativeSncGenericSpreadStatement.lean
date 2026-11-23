module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartBaseChange
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDescendsStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOpenContainingFibreContainsNear

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem spMap_base_mem_basicOpen {R T : Type} [CommRing R] [CommRing T] (χ : R →+* T) (a : R)
    (ha : IsUnit (χ a)) (t : Sp T) : (spMap χ).base t ∈ (PrimeSpectrum.basicOpen a : (Sp R).Opens) := by
  change a ∉ (PrimeSpectrum.comap χ t).asIdeal
  intro h
  exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h ha)

theorem tube_of_universallyClosed : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0})
    (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [UniversallyClosed f] (W : X.Opens),
    IsPullback π f' f (spMap φ) → π ⁻¹ᵁ W = ⊤ → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T),
    IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → ρ ⁻¹ᵁ W = ⊤ := by
  intro R k _ _ φ X X' f f' π _ W H hW
  have hc : IsClosed (f.base '' (W : Set X)ᶜ) := f.isClosedMap _ W.isOpen.isClosed_compl
  let t : Sp k := ⟨⊥, Ideal.isPrime_bot⟩
  have hx : (spMap φ).base t ∈ (f.base '' (W : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, e⟩
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback H x t e
    exact hx (hW.ge (Set.mem_univ z))
  obtain ⟨_, ⟨a, rfl⟩, ha, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hx hc.isOpen_compl
  refine ⟨a, ?_, ?_⟩
  · intro h0
    apply ha
    change φ a ∈ (⊥ : Ideal k)
    exact h0
  · intro T _ χ hχ Z g ρ H'
    refine top_le_iff.1 fun z _ => ?_
    by_contra hz
    have hm := spMap_base_mem_basicOpen χ a hχ (g.base z)
    have e : f.base (ρ.base z) = (spMap χ).base (g.base z) := by
      have := congrArg (fun h : Z ⟶ Sp R => h.base z) H'.w
      simpa using this
    exact hle (e ▸ hm : f.base (ρ.base z) ∈ _) ⟨ρ.base z, hz, rfl⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOpenContainingFibreContainsNearStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.universallyClosed_open_containing_fibre_contains_nearby : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [UniversallyClosed f] (W : X.Opens), IsPullback π f' f (spMap φ) → π ⁻¹ᵁ W = ⊤ → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → ρ ⁻¹ᵁ W = ⊤ := by
  first | exact @GlobalTheory.tube_of_universallyClosed | exact GlobalTheory.tube_of_universallyClosed | (intros; apply GlobalTheory.tube_of_universallyClosed <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartBaseChange

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.snc_chart_base_change : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C : SncChart f d L σ), IsPullback π f' f (spMap φ) → ∃ C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π), C'.U = π ⁻¹ᵁ C.U := by
  first | exact @_root_.GlobalTheory.LogPair.sncChart_baseChange | exact _root_.GlobalTheory.LogPair.sncChart_baseChange | (intros; apply _root_.GlobalTheory.LogPair.sncChart_baseChange <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncGenericSpread

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem GlobalTheory.LogPair.relSnc_spread : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [Smooth f] [IsProper f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → (∀ i, (L i).IsLB) → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → RelSnc g d (fun i => (L i).pull ρ) (fun i => Cartier.secPull (σ i) ρ) := by
  intro R k _ _ φ X X' f f' π _ _ d s L σ hpb hL hrel
  let W : X.Opens := ⨆ C : SncChart f d L σ, C.U
  have hW : π ⁻¹ᵁ W = ⊤ := by
    refine top_unique fun y _ => ?_
    obtain ⟨C', hC'⟩ := hrel.chart y
    obtain ⟨C, hC⟩ := GlobalTheory.T.snc_chart_descends R k φ X X' f f' π d s L σ C' y hpb hC'
    show π y ∈ W
    exact (Opens.mem_iSup).2 ⟨C, hC⟩
  obtain ⟨a, ha, h⟩ := GlobalTheory.T.universallyClosed_open_containing_fibre_contains_nearby R k φ X X' f f' π W hpb hW
  refine ⟨a, ha, fun T _ χ hχ Z g ρ hρ => ?_⟩
  have hZ := h T χ hχ Z g ρ hρ
  refine ⟨fun i => LB.isLB_pull (hL i) ρ, fun z => ?_⟩
  have hz : ρ z ∈ W := by
    have : z ∈ ρ ⁻¹ᵁ W := by rw [hZ]; trivial
    exact this
  obtain ⟨C, hC⟩ := (Opens.mem_iSup).1 hz
  obtain ⟨C', hC'⟩ := GlobalTheory.T.snc_chart_base_change R T χ X Z f g ρ d s L σ C hρ
  refine ⟨C', ?_⟩
  rw [hC']
  exact hC
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncGenericSpreadStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.relative_snc_generic_spread : ∀ (R k : Type) [CommRing R] [Field k] (φ : R →+* k) (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp k) (π : X' ⟶ X) [Smooth f] [IsProper f] (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec), IsPullback π f' f (spMap φ) → (∀ i, (L i).IsLB) → RelSnc f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π) → ∃ a : R, φ a ≠ 0 ∧ ∀ (T : Type) [CommRing T] (χ : R →+* T), IsUnit (χ a) → ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp T) (ρ : Z ⟶ X), IsPullback ρ g f (spMap χ) → RelSnc g d (fun i => (L i).pull ρ) (fun i => Cartier.secPull (σ i) ρ) := by
  first | exact @_root_.GlobalTheory.LogPair.relSnc_spread | exact _root_.GlobalTheory.LogPair.relSnc_spread | (intros; apply _root_.GlobalTheory.LogPair.relSnc_spread <;> assumption)
end
end
