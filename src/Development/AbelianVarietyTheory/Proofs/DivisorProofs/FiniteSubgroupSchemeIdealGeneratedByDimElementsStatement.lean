module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubfunctorStalkIdealCriterionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientAbelianVarietyFiniteSubgroupSchemeStatement
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Mathlib.RingTheory.Ideal.Height
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkOfSmoothLocal
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanMaximalIdealMapOfFlatRegular

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
open IsLocalRing

theorem maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre :
    ∀ (O' O : Type) [CommRing O'] [IsRegularLocalRing O'] [CommRing O] [IsLocalRing O]
      [IsNoetherianRing O] (σ : O' →+* O), IsLocalHom σ → σ.Flat →
      IsArtinianRing (O ⧸ (IsLocalRing.maximalIdeal O').map σ) → ∀ g : ℕ, ringKrullDim O = g →
      ∃ f : Fin g → O, Ideal.span (Set.range f) = (IsLocalRing.maximalIdeal O').map σ := by
  intro O' O _ _ _ _ _ σ hloc hflat hart g hg
  letI := σ.toAlgebra
  haveI : Module.Flat O' O := hflat
  haveI : Algebra.HasGoingDown O' O := Algebra.HasGoingDown.of_flat
  haveI : IsLocalHom (algebraMap O' O) := hloc
  haveI : IsLocalHom σ := hloc
  set I : Ideal O := (maximalIdeal O').map σ with hI
  have hIle : I ≤ maximalIdeal O := IsLocalRing.map_maximalIdeal_le _
  haveI : Nontrivial (O ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal O).ne_top hIle)
  haveI : IsLocalRing (O ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal O).map (Ideal.Quotient.mk I) = maximalIdeal (O ⧸ I) :=
    IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hF : (maximalIdeal (O ⧸ I)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    refine ⟨⟨inferInstance, bot_le⟩, fun q ⟨hq, _⟩ hle => ?_⟩
    exact ((IsArtinianRing.isMaximal_of_isPrime q).eq_of_le (maximalIdeal.isMaximal _).ne_top
      hle).ge
  have H := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal O') (maximalIdeal O)
  have hIalg : (maximalIdeal O').map (algebraMap O' O) = I := rfl
  rw [hIalg, hmap, hF, add_zero] at H
  have hdim : ((maximalIdeal O').spanFinrank : WithBot ℕ∞) = g := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal, ← maximalIdeal_height_eq_ringKrullDim, ← H,
      maximalIdeal_height_eq_ringKrullDim, hg]
  have hg' : (maximalIdeal O').spanFinrank = g := by exact_mod_cast hdim
  have hfg : (maximalIdeal O').FG := IsNoetherian.noetherian _
  obtain ⟨t, htcard, htspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  rw [hg'] at htcard
  let u : Fin g → O' := fun i => (t.equivFin.symm (Fin.cast htcard.symm i) : O')
  have hu : Set.range u = (t : Set O') := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩; exact (t.equivFin.symm _).2
    · intro hx; exact ⟨Fin.cast htcard (t.equivFin ⟨x, hx⟩), by simp [u]⟩
  refine ⟨fun i => σ (u i), ?_⟩
  rw [hI, ← htspan, Ideal.map_span, ← hu, ← Set.range_comp]
  rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanMaximalIdealMapOfFlatRegularStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_span_maximalIdeal_map_of_flat_regular : ∀ (O' O : Type) [CommRing O'] [IsRegularLocalRing O'] [CommRing O] [IsLocalRing O] [IsNoetherianRing O] (σ : O' →+* O), IsLocalHom σ → σ.Flat → IsArtinianRing (O ⧸ (IsLocalRing.maximalIdeal O').map σ) → ∀ g : ℕ, ringKrullDim O = g → ∃ f : Fin g → O, Ideal.span (Set.range f) = (IsLocalRing.maximalIdeal O').map σ := by
  first | exact @GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre | exact GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre | (intros; apply GlobalTheory.maximalIdeal_map_span_of_flat_of_isArtinianRing_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupSchemeIdealGeneratedByDimElements

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FinSubGen

theorem pullback_lift_iff : ∀ (K : Type) [Field K] (A A' H : Over (Sp K)) [GrpObj A'] (j : H ⟶ A) (q : A ⟶ A'), IsPullback j (toUnit H) q η[A'] → ∀ (T : Scheme.{0}) (y' : T ⟶ A.left), (∃ y : T ⟶ H.left, y ≫ j.left = y') ↔ ∃ z : T ⟶ Sp K, z ≫ (η[A']).left = y' ≫ q.left := by
  intro K _ A A' H _ j q hpb T y'
  have h2 := hpb.map (Over.forget (Sp K))
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y ≫ (toUnit H).left, ?_⟩
    simp only [Category.assoc, ← Over.comp_left, hpb.w]
  · rintro ⟨z, hz⟩
    exact ⟨h2.lift y' z hz.symm, h2.lift_fst _ _ _⟩

theorem section_factor_iff : ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Sp K) (s : Sp K ⟶ X), s ≫ f = 𝟙 _ → ∀ x : X, x ∈ Set.range s.base → ∀ (R' : Type) [CommRing R'] (φ : X.presheaf.stalk x →+* R'), (∃ z : Sp R' ⟶ Sp K, z ≫ s = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk x) ↔ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤ RingHom.ker φ := by
  intro K _ X f s hs x hx R' _ φ
  obtain ⟨p, rfl⟩ := hx
  obtain rfl : p = IsLocalRing.closedPoint (CommRingCat.of K) := Subsingleton.elim _ _
  set r := Scheme.stalkClosedPointTo s
  have hr : Spec.map r ≫ X.fromSpecStalk _ = s := Scheme.Spec_stalkClosedPointTo_fromSpecStalk s
  set c : K →+* X.presheaf.stalk (s.base (IsLocalRing.closedPoint (CommRingCat.of K))) :=
    (Spec.preimage (X.fromSpecStalk _ ≫ f)).hom with hcdef
  have hc : Spec.map (CommRingCat.ofHom c) = X.fromSpecStalk _ ≫ f := by simp [c]
  have hrc : ∀ t : K, r.hom (c t) = t := by
    have h1 : Spec.map (CommRingCat.ofHom c ≫ r) = Spec.map (𝟙 (CommRingCat.of K)) := by
      rw [Spec.map_comp, hc, ← Category.assoc, hr, hs, Spec.map_id]
    have h2 := Spec.map_injective h1
    intro t
    exact congrArg (fun u : CommRingCat.of K ⟶ CommRingCat.of K => u.hom t) h2
  have hm : ∀ a, a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (s.base (IsLocalRing.closedPoint (CommRingCat.of K)))) → r.hom a = 0 := by
    intro a ha
    by_contra h
    exact (IsLocalRing.mem_maximalIdeal _).mp ha (isUnit_of_map_unit r.hom a (isUnit_iff_ne_zero.mpr h))
  constructor
  · rintro ⟨z, hz⟩ a ha
    have hz2 : (z ≫ Spec.map r) ≫ X.fromSpecStalk _ = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk _ := by
      rw [Category.assoc, hr]; exact hz
    have hz' := (cancel_mono _).mp hz2
    rw [← Spec.map_preimage z, ← Spec.map_comp] at hz'
    have h3 := Spec.map_injective hz'
    have h4 : φ a = (Spec.preimage z).hom (r.hom a) :=
      (congrArg (fun u : _ ⟶ CommRingCat.of R' => u.hom a) h3).symm
    rw [RingHom.mem_ker, h4, hm a ha, map_zero]
  · intro hφ
    refine ⟨Spec.map (CommRingCat.ofHom (φ.comp c)), ?_⟩
    have e1 : Spec.map (CommRingCat.ofHom (φ.comp c)) ≫ Spec.map r ≫ X.fromSpecStalk _ = Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk _ := by
      rw [← Category.assoc, ← Spec.map_comp]
      congr 2
      ext a
      show φ (c (r.hom a)) = φ a
      have hmem : c (r.hom a) - a ∈ IsLocalRing.maximalIdeal _ := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        have := hu.map r.hom
        rw [map_sub, hrc, sub_self] at this
        exact not_isUnit_zero this
      have := hφ hmem
      rw [RingHom.mem_ker, map_sub, sub_eq_zero] at this
      exact this
    rwa [hr] at e1

theorem stalk_regular_of_section : ∀ (K : Type) [Field K] (X : Scheme.{0}) (f : X ⟶ Sp K) [IsSeparated f] (g : ℕ), SmoothOfRelativeDimension g f → ∀ (s : Sp K ⟶ X), s ≫ f = 𝟙 _ → ∀ x : X, x ∈ Set.range s.base → IsNoetherianRing (X.presheaf.stalk x) ∧ IsRegularLocalRing (X.presheaf.stalk x) ∧ ringKrullDim (X.presheaf.stalk x) = g := by
  intro K _ X f _ g hg s hs x hx
  have hci : IsClosedImmersion s := isClosedImmersion_of_comp_eq_id f s hs
  have hcl : IsClosed ({x} : Set X) := by
    have e : Set.range s.base = {x} := by
      obtain ⟨p, rfl⟩ := hx
      ext y
      constructor
      · rintro ⟨p', rfl⟩
        rw [Subsingleton.elim p' p]
        rfl
      · rintro rfl
        exact ⟨p, rfl⟩
    rw [← e]
    exact s.isClosedEmbedding.isClosed_range
  set σ : K →+* X.presheaf.stalk x := (Spec.preimage (X.fromSpecStalk x ≫ f)).hom with hσdef
  have hσ : X.fromSpecStalk x ≫ f = Spec.map (CommRingCat.ofHom σ) := by
    simp [σ]
  haveI : IsLocalHom σ := ⟨fun a ha => isUnit_iff_ne_zero.mpr (by rintro rfl; simp at ha)⟩
  obtain ⟨h1, -, h3, h4⟩ := GlobalTheory.StabFlat.stalk_of_smooth_local K X f g hg x hcl σ hσ inferInstance
  have hb : (IsLocalRing.maximalIdeal K).map σ = ⊥ := by
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.map_bot]
  let e : (X.presheaf.stalk x ⧸ (IsLocalRing.maximalIdeal K).map σ) ≃+* X.presheaf.stalk x :=
    (Ideal.quotEquivOfEq hb).trans (RingEquiv.quotientBot _)
  exact ⟨h1, IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h4⟩

theorem ideal_eq_span_fin : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → ∃ f : Fin g → A.left.presheaf.stalk x₀, Ideal.span (Set.range f) = J := by
  intro K _ _ A _ g hA hg H _ j hj hci hfin x₀ hx₀ J hJ
  have hmono : Mono j := Over.mono_of_mono_left j
  obtain ⟨A', _, hA', q, hq, hqfin, hqflat, hqsurj, hpb⟩ := GlobalTheory.T.exists_quotient_abelianVariety_finite_subgroupScheme K A hA H j hj hmono hfin
  have hη : η[A] ≫ q = η[A'] := IsMonHom.one_hom q
  have hsA : (η[A]).left ≫ A.hom = 𝟙 _ := Over.w η[A]
  have hsA' : (η[A']).left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  obtain ⟨p, hp⟩ := hx₀
  have hx' : q.left.base x₀ ∈ Set.range (η[A']).left.base := ⟨p, by
    rw [← hp, ← hη]; rfl⟩
  have hAs := hA.smooth
  have hAp := hA.proper
  have hA's := hA'.smooth
  have hA'p := hA'.proper
  have hA'c := hA'.geomConnected
  have : ConnectedSpace A'.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := A'.hom) (𝟙 _) (𝟙 _) A'.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected A'.hom (q.left.base x₀)
  have Lreg : IsRegularLocalRing (A'.left.presheaf.stalk (q.left.base x₀)) :=
    (stalk_regular_of_section K A'.left A'.hom n hn _ hsA' _ hx').2.1
  have Ldim := stalk_regular_of_section K A.left A.hom g hg _ hsA x₀ ⟨p, hp⟩
  set σ := (q.left.stalkMap x₀).hom
  have key : ∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), J ≤ RingHom.ker ψ ↔ (IsLocalRing.maximalIdeal (A'.left.presheaf.stalk (q.left.base x₀))).map σ ≤ RingHom.ker ψ := by
    intro R' _ ψ
    rw [← hJ, pullback_lift_iff K A A' H j q hpb, Ideal.map_le_iff_le_comap, RingHom.comap_ker,
      ← section_factor_iff K A'.left A'.hom _ hsA' _ hx' R' (ψ.comp σ)]
    have e : Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀ ≫ q.left =
        Spec.map (CommRingCat.ofHom (ψ.comp σ)) ≫ A'.left.fromSpecStalk (q.left.base x₀) := by
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, ← Spec.map_comp]
      rfl
    simp only [Category.assoc, e]
  have Lgeo : J = (IsLocalRing.maximalIdeal (A'.left.presheaf.stalk (q.left.base x₀))).map σ := by
    apply le_antisymm
    · simpa using (key _ (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal (A'.left.presheaf.stalk (q.left.base x₀))).map σ))).2 (by simp)
    · simpa using (key _ (Ideal.Quotient.mk J)).1 (by simp)
  obtain ⟨_, hart⟩ := GlobalTheory.T.closed_subfunctor_stalk_ideal_criterion K A H j hj hci hfin x₀ ⟨p, hp⟩ J hJ
  have hflat : σ.Flat := Flat.stalkMap q.left x₀
  haveI := Ldim.1
  rw [Lgeo] at hart ⊢
  exact GlobalTheory.T.exists_span_maximalIdeal_map_of_flat_regular _ _ σ inferInstance hflat hart g Ldim.2.2

end GlobalTheory.FinSubGen
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSubgroupSchemeIdealGeneratedByDimElementsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.finiteSubgroupScheme_ideal_generated_by_dim_elements : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → ∃ f : Fin g → A.left.presheaf.stalk x₀, Ideal.span (Set.range f) = J := by
  first | exact @GlobalTheory.FinSubGen.ideal_eq_span_fin | exact GlobalTheory.FinSubGen.ideal_eq_span_fin | (intros; apply GlobalTheory.FinSubGen.ideal_eq_span_fin <;> assumption)
end
end
