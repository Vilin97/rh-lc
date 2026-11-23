module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreconnectedSpaceOfFinGenSubfieldBaseChangesStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceClosedFibreFinitelyGeneratedExt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem connectedSpace_pullback_of_finitelyGenerated_residue :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      IsProper π → Surjective π → Function.Bijective π.appTop.hom →
      ∀ (K : Type) [Field K] (κ : ResidueField R →+* K) (L : Subfield K) (hL : ∀ x, κ x ∈ L) (n : ℕ) (c : Fin n → K),
        L = Subfield.closure (Set.range κ ∪ Set.range c) →
        ConnectedSpace (pullback π (spMap ((κ.codRestrict L hL).comp (residue R))) : Scheme.{0}) := by
  intro R _ _ _ S π hprop hsurj hbij K _ κ L hL n c hLc
  haveI := hprop
  haveI := hsurj
  have hc : ∀ j, c j ∈ L := fun j => hLc ▸ Subfield.subset_closure (Or.inr ⟨j, rfl⟩)
  set A := MvPolynomial (Fin n) R
  set ιC : R →+* A := MvPolynomial.C with hC
  set β : R →+* L := (κ.codRestrict L hL).comp (residue R) with hβ
  set φ : A →+* L := MvPolynomial.eval₂Hom β (fun j => ⟨c j, hc j⟩) with hφ
  have hφC : φ.comp ιC = β := by
    refine RingHom.ext fun r => ?_
    show MvPolynomial.eval₂ β (fun j => (⟨c j, hc j⟩ : L)) (MvPolynomial.C r) = β r
    exact MvPolynomial.eval₂_C _ _ _
  have hx : spMap β = spMap φ ≫ spMap ιC := by
    rw [← hφC]
    show Spec.map (CommRingCat.ofHom (φ.comp ιC)) = Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ιC)
    rw [← Spec.map_comp]; rfl

  have hdiv : ∀ x : L, ∃ a b : A, φ b ≠ 0 ∧ φ b * x = φ a := by
    have hsub : Subring.closure (Set.range κ ∪ Set.range c) ≤ (φ.range).map L.subtype := by
      rw [Subring.closure_le]
      rintro y (⟨z, rfl⟩ | ⟨j, rfl⟩)
      · obtain ⟨r, rfl⟩ := residue_surjective z
        exact ⟨β r, ⟨MvPolynomial.C r, MvPolynomial.eval₂_C _ _ _⟩, rfl⟩
      · exact ⟨⟨c j, hc j⟩, ⟨MvPolynomial.X j, MvPolynomial.eval₂_X _ _ _⟩, rfl⟩
    intro x
    have hx' : (x : K) ∈ Subfield.closure (Set.range κ ∪ Set.range c) := hLc ▸ x.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.1 hx'
    obtain ⟨y', ⟨a, rfl⟩, rfl⟩ := hsub hy
    obtain ⟨z', ⟨b, rfl⟩, rfl⟩ := hsub hz
    by_cases hb : φ b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      have : (x : K) = 0 := by rw [← hyz]; simp [hb]
      have : x = 0 := Subtype.ext this
      simp [this]
    · refine ⟨a, b, hb, ?_⟩
      apply Subtype.ext
      have hb' : ((φ b : L) : K) ≠ 0 := fun h => hb (Subtype.ext h)
      simp only [Subfield.coe_mul, L.subtype_apply] at hyz ⊢
      rw [← hyz]; field_simp
  have hstalk : φ.SurjectiveOnStalks := by
    refine RingHom.surjectiveOnStalks_of_exists_div fun x => ?_
    obtain ⟨a, b, hb, e⟩ := hdiv x
    exact ⟨a, b, (isUnit_iff_ne_zero).2 hb, e⟩
  haveI hpre : IsPreimmersion (spMap φ) := by
    rw [IsPreimmersion.SpecMap_iff]
    refine ⟨?_, hstalk⟩
    haveI : Subsingleton (PrimeSpectrum L) := inferInstance
    exact Topology.IsEmbedding.of_subsingleton _

  set π' : pullback π (spMap ιC) ⟶ Sp A := pullback.snd π (spMap ιC) with hπ'
  have hflat : Flat (spMap ιC) := by
    refine Flat.SpecMap_iff.2 ?_
    show (algebraMap R A).Flat
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have hbij' : ∀ V : (Sp A).Opens, Function.Bijective (π'.app V).hom :=
    GlobalTheory.Mum.app_bijective_of_flat_baseChange R S (Sp A) _ π (spMap ιC) _ _ inferInstance inferInstance
      hbij hflat (IsPullback.of_hasPullback π (spMap ιC)).flip
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum L) := inferInstance
  have hconn := GlobalTheory.T.zariski_connectedness_isPreconnected_fibre _ _ π' inferInstance inferInstance hbij' (spMap φ q)
  have hrange : Set.range (spMap φ) = {spMap φ q} := by
    ext y
    constructor
    · rintro ⟨q', rfl⟩; rw [Subsingleton.elim q' q]; rfl
    · rintro rfl; exact ⟨q, rfl⟩
  set f := pullback.fst π' (spMap φ) with hf
  have hfr : Set.range f = {s | π' s = spMap φ q} := by
    rw [hf, Scheme.Pullback.range_fst, hrange]; rfl
  have hP : PreconnectedSpace ↥(pullback π' (spMap φ)) := by
    refine ⟨?_⟩
    rw [← f.isEmbedding.isInducing.isPreconnected_image, Set.image_univ, hfr]
    exact hconn
  have e : pullback π (spMap β) ≅ pullback π' (spMap φ) :=
    pullback.congrHom rfl hx ≪≫ (pullbackLeftPullbackSndIso π (spMap ιC) (spMap φ)).symm
  obtain ⟨z, -⟩ := (pullback.snd π (spMap β)).surjective q
  haveI : ConnectedSpace ↥(pullback π' (spMap φ)) := ConnectedSpace.mk ⟨e.hom z⟩
  exact (Scheme.homeoOfIso e).symm.surjective.connectedSpace (Scheme.homeoOfIso e).symm.continuous

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceClosedFibreFinitelyGeneratedExtStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.connectedSpace_closedFibre_finitelyGenerated_ext : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      IsProper π → Surjective π → Function.Bijective π.appTop.hom →
      ∀ (K : Type) [Field K] (κ : ResidueField R →+* K) (L : Subfield K) (hL : ∀ x, κ x ∈ L) (n : ℕ) (c : Fin n → K),
        L = Subfield.closure (Set.range κ ∪ Set.range c) →
        ConnectedSpace (pullback π (spMap ((κ.codRestrict L hL).comp (residue R))) : Scheme.{0}) := by
  first | exact @GlobalTheory.Mum.connectedSpace_pullback_of_finitelyGenerated_residue | exact GlobalTheory.Mum.connectedSpace_pullback_of_finitelyGenerated_residue | (intros; apply GlobalTheory.Mum.connectedSpace_pullback_of_finitelyGenerated_residue <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceClosedFibreModificationFieldExtens

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) := by
  intro R _ _ _ hA M K _ κ
  obtain ⟨hN, -, hIC, -⟩ := hA
  haveI := hN
  haveI := hIC
  obtain ⟨hbij, hsurj⟩ := Modif.appTop_bijective_surjective R M
  haveI := M.proper
  haveI := hsurj
  have hcomp : ∀ {A : Type} [CommRing A] (ψ : ResidueField R →+* A),
      spMap ψ ≫ spMap (residue R) = spMap (ψ.comp (residue R)) := fun ψ => by
    rw [← Spec.map_comp]; rfl
  have pc : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) [PreconnectedSpace X], PreconnectedSpace Y :=
    fun h _ => ⟨by rw [← h.surjective.range_eq, ← Set.image_univ]; exact isPreconnected_univ.image _ h.continuous.continuousOn⟩
  let f := pullback.snd M.π (spMap (residue R))
  have e : ∀ {A : Type} [CommRing A] (ψ : ResidueField R →+* A),
      pullback f (spMap ψ) ≅ pullback M.π (spMap (ψ.comp (residue R))) := fun ψ =>
    pullbackLeftPullbackSndIso M.π (spMap (residue R)) (spMap ψ) ≪≫ pullback.congrHom rfl (hcomp ψ)
  have hP : PreconnectedSpace (pullback f (spMap κ) : Scheme.{0}) := by
    refine GlobalTheory.T.preconnectedSpace_of_finGen_subfield_baseChanges (ResidueField R) _ f inferInstance inferInstance K κ fun L hL n c hc => ?_
    have hc' := GlobalTheory.T.connectedSpace_closedFibre_finitelyGenerated_ext R M.S M.π inferInstance hsurj hbij K κ L hL n c hc
    exact @pc _ _ _ _ (Scheme.homeoOfIso (e _)).symm hc'.toPreconnectedSpace
  haveI : PreconnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) :=
    pc (Scheme.homeoOfIso (e κ))
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨z, -⟩ := (pullback.snd M.π (spMap (κ.comp (residue R)))).surjective q
  exact ConnectedSpace.mk ⟨z⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceClosedFibreModificationFieldExtensStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.connectedSpace_closedFibre_modification_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) := by
  first | exact @GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field | exact GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field | (intros; apply GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field <;> assumption)
end
end
