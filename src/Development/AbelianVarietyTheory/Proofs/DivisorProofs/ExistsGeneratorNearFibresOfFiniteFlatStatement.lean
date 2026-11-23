module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocus
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
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.PullSec
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroSectionOfFiniteFreeBaseChangeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingOverClosedPointFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializationClosedInAffineNeighbourhoodStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.RingHom.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOnSmallerOpenOfNonvanishingSectio

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GenRestrict

theorem exists_gen_restrict : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (O O' : Z.Opens), O ≤ O' →
    ∀ u : LB.Sec (L.pull O'.ι), (∀ z : O'.toScheme, O'.ι z ∈ O → z ∈ nonzeroLocus u) →
    ∃ t : LB.Gen (L.pull O.ι), t.IsGen := by
  intro Z L _ O O' hle u hu
  have e : ∀ _k : PUnit, Z.homOfLE hle ≫ (fun _ : PUnit => O'.ι) _k = (fun _ : PUnit => O.ι) _k :=
    fun _ => Scheme.homOfLE_ι Z hle
  let v : LB.Sec (L.pull O.ι) := PullbackSections.pullSecLC L _ _ _ (Z.homOfLE hle) e u
  refine GlobalTheory.LocusPull.exists_gen_of_nonzeroLocus_eq_top v (top_unique fun z _ => ?_)
  have heq : O'.ι (Z.homOfLE hle z) = O.ι z := by
    exact congrArg (fun f : O.toScheme ⟶ Z => f z) (Scheme.homOfLE_ι Z hle)
  have hz : O'.ι (Z.homOfLE hle z) ∈ O := by
    rw [heq]
    exact (Scheme.Opens.ι_apply O z).symm ▸ z.2
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 (hu _ hz)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨k, ?_⟩
  show z ∈ O.toScheme.basicOpen ((Scheme.Hom.appLE (Z.homOfLE hle) _ _ _).hom (u.f k))
  rw [Scheme.basicOpen_appLE]
  refine ⟨?_, hk⟩
  have h1 : Z.homOfLE hle z ∈ (L.pull O'.ι).U k := Scheme.basicOpen_le _ _ hk
  refine mem_pull.2 ?_
  rw [← heq]
  exact mem_pull.1 h1

end GlobalTheory.GenRestrict
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorOnSmallerOpenOfNonvanishingSectioStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section : ∀ (Z : Scheme.{0}) (L : LB Z), L.IsLB → ∀ (O O' : Z.Opens), O ≤ O' → ∀ u : LB.Sec (L.pull O'.ι), (∀ z : O'.toScheme, O'.ι z ∈ O → z ∈ nonzeroLocus u) → ∃ t : LB.Gen (L.pull O.ι), t.IsGen := by
  first | exact @GlobalTheory.GenRestrict.exists_gen_restrict | exact GlobalTheory.GenRestrict.exists_gen_restrict | (intros; apply GlobalTheory.GenRestrict.exists_gen_restrict <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsNonzeroOfIsClosedMap

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_nhds_nonzero_of_isClosedMap :
    ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), IsClosedMap p.base → ∀ (L : LB Z) (V : Y.Opens) (u : LB.Sec (L.pull (p ⁻¹ᵁ V).ι)) (y : Y), y ∈ V → (∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) = y → z ∈ nonzeroLocus u) → ∃ V₁ : Y.Opens, y ∈ V₁ ∧ V₁ ≤ V ∧ ∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) ∈ V₁ → z ∈ nonzeroLocus u := by
  intro Z Y p hp L V u y hy h
  have hO : IsOpen ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme)) :=
    (p ⁻¹ᵁ V).ι.isOpenEmbedding.isOpenMap _ (nonzeroLocus u).isOpen
  have hC : IsClosed (p.base '' ((p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme))ᶜ) :=
    hp _ hO.isClosed_compl
  refine ⟨V ⊓ ⟨_, hC.isOpen_compl⟩, ⟨hy, ?_⟩, inf_le_left, ?_⟩
  · rintro ⟨c, hc, hcy⟩
    have hcV : c ∈ p ⁻¹ᵁ V := by
      change p c ∈ V
      have : p c = y := hcy
      rw [this]; exact hy
    exact hc ⟨⟨c, hcV⟩, h ⟨c, hcV⟩ hcy, rfl⟩
  · intro z hz
    have h2 : (p ⁻¹ᵁ V).ι z ∈ (p ⁻¹ᵁ V).ι '' (nonzeroLocus u : Set (p ⁻¹ᵁ V).toScheme) := by
      by_contra hn
      exact hz.2 ⟨_, hn, rfl⟩
    obtain ⟨w, hw, hwz⟩ := h2
    have : w = z := (p ⁻¹ᵁ V).ι.isOpenEmbedding.injective hwz
    subst this
    exact hw

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNhdsNonzeroOfIsClosedMapStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap : ∀ (Z Y : Scheme.{0}) (p : Z ⟶ Y), IsClosedMap p.base → ∀ (L : LB Z) (V : Y.Opens) (u : LB.Sec (L.pull (p ⁻¹ᵁ V).ι)) (y : Y), y ∈ V → (∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) = y → z ∈ nonzeroLocus u) → ∃ V₁ : Y.Opens, y ∈ V₁ ∧ V₁ ≤ V ∧ ∀ z : (p ⁻¹ᵁ V).toScheme, p ((p ⁻¹ᵁ V).ι z) ∈ V₁ → z ∈ nonzeroLocus u := by
  first | exact @GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap | exact GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap | (intros; apply GlobalTheory.Mum.exists_nhds_nonzero_of_isClosedMap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatLocalBaseChangeOfProperPropertiesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.finite_flat_local_baseChange_of_proper_properties : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsFinite k ∧ QuasiCompact p' ∧ QuasiSeparated p' ∧ Function.Surjective k'.base ∧ IsClosedMap (p' ≫ k).base ∧ IsClosedMap p.base ∧ (∀ V : Y.Opens, IsAffineOpen V → IsCompact (p ⁻¹ᵁ V : Set Z) ∧ IsQuasiSeparated (p ⁻¹ᵁ V : Set Z)) ∧ ∃ (d : ℕ) (b : Fin d → R'), ∀ r' : R', ∃! c : Fin d → R, r' = ∑ l, ρ (c l) * b l := by
  first | exact @GlobalTheory.finiteFlat_proper_baseChange_facts | exact GlobalTheory.finiteFlat_proper_baseChange_facts | (intros; apply GlobalTheory.finiteFlat_proper_baseChange_facts <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorNearFibresOfFiniteFlat

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_gen_near_of_finFlat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsLocallyNoetherian Y → (∀ V : Y.Opens, Function.Bijective (p.app V).hom) → ∀ L' : LB Z, L'.IsLB → (∀ x : Y', ∃ V : Y'.Opens, x ∈ V ∧ ∃ t : LB.Gen ((L'.pull k').pull (p' ⁻¹ᵁ V).ι), t.IsGen) → ∀ x : Y, ∃ V : Y.Opens, x ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen := by
  intro R _ _ _ hR R' _ _ _ ρ hfin hflat Z Y Z' Y' p p' y y' k k' hk hk' hp hY hbij L hL hloc x
  haveI : IsNoetherianRing R := hR.1
  obtain ⟨hkf, hqc, hqs, hsurj, hcl, hclp, hO, d, b, hb⟩ :=
    GlobalTheory.T.finite_flat_local_baseChange_of_proper_properties R R' ρ hfin.2.1 hfin.2.2 hflat Z Y Z' Y' p p' y y' k k' hk hk' hp
  obtain ⟨V, hV, y₀, hy₀, hxy, hE⟩ := GlobalTheory.T.exists_specialization_closed_in_affine_neighbourhood Y x
  obtain ⟨hclV, -⟩ := hE V le_rfl hV hy₀
  have hL' : (L.pull k').IsLB := LB.isLB_pull hL _
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_section_nonvanishing_over_closed_point_fibre Y Y' Z' k hkf p' hqc hqs V hV y₀ hy₀ hclV (L.pull k') hL' (fun x' _ => hloc x')
  obtain ⟨V₁, hy₁, hV₁V, hV₁⟩ := GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap Z' Y (p' ≫ k) hcl (L.pull k') V s y₀ hy₀ hs
  obtain ⟨f, hf1, hf2⟩ := hV.exists_basicOpen_le ⟨y₀, hy₁⟩ hy₀
  have hV₂V : Y.basicOpen f ≤ V := Y.basicOpen_le f
  have hV₂ : IsAffineOpen (Y.basicOpen f) := hV.basicOpen f
  obtain ⟨-, M, hM, hMiff⟩ := hE (Y.basicOpen f) hV₂V hV₂ hf2
  have hcomm : ∀ z : Z', p (k' z) = k (p' z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hk'.w]
  have hle : k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f) ≤ p' ⁻¹ᵁ (k ⁻¹ᵁ V) := fun z hz => by
    show k (p' z) ∈ V
    rw [← hcomm]
    exact hV₂V hz
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section Z' (L.pull k') hL' _ _ hle s (fun z₀ hz₀ => hV₁ z₀ (by
    rw [Scheme.Hom.comp_apply, ← hcomm]
    exact hf1 hz₀))
  have hsurjp : Function.Surjective (p.app (Y.basicOpen f)).hom := (hbij _).2
  let e := RingEquiv.ofBijective (p.app (Y.basicOpen f)).hom (hbij _)
  haveI hm : (Ideal.comap e.symm.toRingHom M).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  obtain ⟨hOc, hOq⟩ := hO _ hV₂
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_nonzero_section_of_finite_free_baseChange R R' ρ d b hb Z Z' k' (p ≫ y) (p' ≫ y') (hk'.paste_vert hk) (p ⁻¹ᵁ Y.basicOpen f) hOc hOq
    L hL σ hσ _ hm
  have hfib : ∀ z₀ : (p ⁻¹ᵁ Y.basicOpen f).toScheme, p ((p ⁻¹ᵁ Y.basicOpen f).ι z₀) = y₀ → z₀ ∈ nonzeroLocus u := by
    intro z₀ hz₀
    obtain ⟨z', hz'⟩ := hsurj ((p ⁻¹ᵁ Y.basicOpen f).ι z₀)
    have hz'O : z' ∈ k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f) := by
      show k' z' ∈ p ⁻¹ᵁ Y.basicOpen f
      rw [hz']
      first | exact z₀.2 | simpa using z₀.2 | exact (Scheme.Opens.range_ι _).subset ⟨z₀, rfl⟩
    obtain ⟨w, hw⟩ : z' ∈ Set.range (k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f)).ι.base := by
      rw [Scheme.Opens.range_ι]; exact hz'O
    refine hu w (fun a ha => ?_) z₀ (by rw [← hz']; exact congrArg k'.base hw |>.symm)
    have ha₀ : e.symm a ∈ M := ha
    have ea : a = p.app (Y.basicOpen f) (e.symm a) := (e.apply_symm_apply a).symm
    intro hmem
    rw [ea, ← Scheme.preimage_basicOpen] at hmem
    have : k' ((k' ⁻¹ᵁ (p ⁻¹ᵁ Y.basicOpen f)).ι w) = (p ⁻¹ᵁ Y.basicOpen f).ι z₀ := by
      rw [← hz']; exact congrArg k'.base hw
    rw [this] at hmem
    have hmem' : p ((p ⁻¹ᵁ Y.basicOpen f).ι z₀) ∈ Y.basicOpen (e.symm a) := hmem
    rw [hz₀] at hmem'
    exact (hMiff _).1 ha₀ hmem'
  obtain ⟨V₃, hy₃, hV₃, hV₃u⟩ := GlobalTheory.T.exists_nhds_subset_nonzeroLocus_of_isClosedMap Z Y p hclp L _ u y₀ hf2 hfib
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_generator_on_smaller_open_of_nonvanishing_section Z L hL (p ⁻¹ᵁ V₃) (p ⁻¹ᵁ Y.basicOpen f) (fun z hz => hV₃ hz) u
    (fun z hz => hV₃u z hz)
  exact ⟨V₃, hxy.mem_open V₃.isOpen hy₃, t, ht⟩

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorNearFibresOfFiniteFlatStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_generator_near_fibres_of_finiteFlat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ρ.Flat → ∀ (Z Y Z' Y' : Scheme.{0}) (p : Z ⟶ Y) (p' : Z' ⟶ Y') (y : Y ⟶ Sp R) (y' : Y' ⟶ Sp R') (k : Y' ⟶ Y) (k' : Z' ⟶ Z), IsPullback k y' y (spMap ρ) → IsPullback k' p' p k → IsProper p → IsLocallyNoetherian Y → (∀ V : Y.Opens, Function.Bijective (p.app V).hom) → ∀ L' : LB Z, L'.IsLB → (∀ x : Y', ∃ V : Y'.Opens, x ∈ V ∧ ∃ t : LB.Gen ((L'.pull k').pull (p' ⁻¹ᵁ V).ι), t.IsGen) → ∀ x : Y, ∃ V : Y.Opens, x ∈ V ∧ ∃ t : LB.Gen (L'.pull (p ⁻¹ᵁ V).ι), t.IsGen := by
  first | exact @GlobalTheory.Mum.exists_gen_near_of_finFlat | exact GlobalTheory.Mum.exists_gen_near_of_finFlat | (intros; apply GlobalTheory.Mum.exists_gen_near_of_finFlat <;> assumption)
end
end
