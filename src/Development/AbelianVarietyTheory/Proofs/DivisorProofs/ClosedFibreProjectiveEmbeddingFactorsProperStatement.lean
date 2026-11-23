module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteOpenImmersionNbhdIsolatedFibrePointsStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftGeometricPointOverClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftToProjectiveBaseInjectiveOverClosedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictProperSectionsBijectiveToFibreOpenStatement
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibreStatement
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteCohOfForallModification
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFibreClosedFibrePointSubsetOpenPartStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreEmbeddingLiftSeparatedFiniteTypeQuasi

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem emb_lift_sep_loft_qc : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G',
    IsSeparated (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧
      LocallyOfFiniteType (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧
      QuasiCompact (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) := by
  intro R _ _ _ hR M G' _ _ hG E
  have : IsNoetherianRing R := hR.1
  have : Smooth G'.hom := hG.smooth
  have : IsSeparated G'.hom := hG.separated
  have : QuasiCompact G'.hom := hG.quasiCompact
  have : IsProper M.π := M.proper
  have : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  have : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have : IsProper (PSpace.str R E.N) := isProper_str R E.N
  set φ := pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over
  have hφ : φ ≫ pullback.snd (PSpace.str R E.N) M.π = E.H.ι ≫ G'.hom := pullback.lift_snd _ _ _
  have h1 : IsSeparated (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  have h2 : LocallyOfFiniteType (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  have h3 : QuasiCompact (φ ≫ pullback.snd (PSpace.str R E.N) M.π) := by rw [hφ]; infer_instance
  exact ⟨IsSeparated.of_comp φ (pullback.snd _ _), locallyOfFiniteType_of_comp φ (pullback.snd _ _),
    QuasiCompact.of_comp φ (pullback.snd _ _)⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreEmbeddingLiftSeparatedFiniteTypeQuasiStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibreEmbedding_lift_separated_finiteType_quasiCompact : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', IsSeparated (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧ LocallyOfFiniteType (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) ∧ QuasiCompact (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) := by
  first | exact @GlobalTheory.Mum.emb_lift_sep_loft_qc | exact GlobalTheory.Mum.emb_lift_sep_loft_qc | (intros; apply GlobalTheory.Mum.emb_lift_sep_loft_qc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianProjectiveSpaceAndPullbackProper

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem pspace_noeth_and_pullback : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
    IsProper π → ∀ N : ℕ, IsNoetherian (PSpace R N) ∧ IsNoetherian (pullback (PSpace.str R N) π) := by
  intro R _ _ S π hπ N
  have hP : IsProper (PSpace.str R N) := isProper_str R N
  have h1 : IsNoetherian (PSpace R N) := by
    have : IsLocallyNoetherian (PSpace R N) := LocallyOfFiniteType.isLocallyNoetherian (PSpace.str R N)
    have : CompactSpace (PSpace R N) := QuasiCompact.compactSpace_of_compactSpace (PSpace.str R N)
    exact {}
  refine ⟨h1, ?_⟩
  haveI := hπ
  have : IsProper (pullback.fst (PSpace.str R N) π) := inferInstance
  haveI := LocallyOfFiniteType.isLocallyNoetherian (pullback.fst (PSpace.str R N) π)
  haveI := QuasiCompact.compactSpace_of_compactSpace (pullback.fst (PSpace.str R N) π)
  exact {}

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNoetherianProjectiveSpaceAndPullbackProperStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isNoetherian_projectiveSpace_and_pullback_proper : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → ∀ N : ℕ, IsNoetherian (PSpace R N) ∧ IsNoetherian (pullback (PSpace.str R N) π) := by
  first | exact @GlobalTheory.Mum.pspace_noeth_and_pullback | exact GlobalTheory.Mum.pspace_noeth_and_pullback | (intros; apply GlobalTheory.Mum.pspace_noeth_and_pullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibres

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SteinFact

theorem finite_appTop_of_isProper {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}}
    (f : X ⟶ Sp R) [IsProper f] :
    ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom.Finite := by
  letI := GlobalTheory.algebraΓOfHom f
  have h0 := GlobalTheory.ProperFinite.finite_coh_of_isProper f (GlobalTheory.structureModule X) 0
  have h1 := Module.Finite.equiv (GlobalTheory.cohOn.zeroEquiv R (GlobalTheory.structureModule X) ⊤)
  let ρ : GlobalTheory.sectionsOn (GlobalTheory.structureModule X) ⊤ →ₗ[R] Γ(X, ⊤) :=
    { toFun := fun s => (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤ s : Γ(X, ⊤))
      map_add' := fun s t => map_add (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤) s t
      map_smul' := fun r s => by
        rw [GlobalTheory.sectionsOn.toΓ_smul]
        rw [GlobalTheory.restrictGlobal_top]
        rfl }
  have hρ : Function.Bijective ρ := (GlobalTheory.sectionsOn.toΓ (GlobalTheory.structureModule X) ⊤).bijective
  exact Module.Finite.equiv (LinearEquiv.ofBijective ρ hρ)

theorem finite_app_of_isProper {X Y : Scheme.{0}} (g : X ⟶ Y) [IsProper g] {V : Y.Opens}
    (hV : IsAffineOpen V) [IsNoetherianRing Γ(Y, V)] : (g.app V).hom.Finite := by
  let j := (g ⁻¹ᵁ V).ι
  let g' : (g ⁻¹ᵁ V).toScheme ⟶ Sp Γ(Y, V) := g ∣_ V ≫ hV.isoSpec.hom
  have : IsProper g' := inferInstanceAs (IsProper (g ∣_ V ≫ hV.isoSpec.hom))
  have h1 := finite_appTop_of_isProper g'
  have hle : j ''ᵁ ⊤ ≤ g ⁻¹ᵁ V := (g ⁻¹ᵁ V).ι_image_top.le
  have e : (Scheme.ΓSpecIso (.of Γ(Y, V))).inv ≫ g'.appTop = g.appLE V (j ''ᵁ ⊤) hle := by
    ext r
    change (g ∣_ V ≫ hV.isoSpec.hom).appTop ((Scheme.ΓSpecIso Γ(Y, V)).inv r) = _
    rw [Scheme.Hom.comp_appTop, IsAffineOpen.isoSpec_hom_appTop, ← CommRingCat.comp_apply, Category.assoc,
      Iso.inv_hom_id_assoc, GlobalTheory.ProperFinite.topIso_inv_appTop]
  rw [e] at h1
  have hi : IsIso (X.presheaf.map (homOfLE hle).op) := by
    rw [show homOfLE hle = eqToHom (g ⁻¹ᵁ V).ι_image_top from Subsingleton.elim _ _]
    infer_instance
  exact (RingHom.finite_respectsIso.cancel_right_isIso _ (X.presheaf.map (homOfLE hle).op)).1 h1

theorem stein_factorisation : ∀ (X Y : Scheme.{0}) (g : X ⟶ Y), IsLocallyNoetherian Y → IsProper g → ∃ (Y' : Scheme.{0}) (a : X ⟶ Y') (b : Y' ⟶ Y), a ≫ b = g ∧ IsFinite b ∧ IsProper a ∧ Surjective a ∧ (∀ V : Y'.Opens, Function.Bijective (a.app V).hom) ∧ ∀ y : Y', _root_.IsPreconnected {x : X | a x = y} := by
  intro X Y g hY hg
  have hb : IsFinite g.fromNormalization := by
    refine { toIsAffineHom := inferInstance, finite_app := fun U hU => ?_ }
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    letI := (g.app U).hom.toAlgebra
    have : Module.Finite Γ(Y, U) Γ(X, g ⁻¹ᵁ U) := finite_app_of_isProper g hU
    have : Module.Finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U)) :=
      Module.IsNoetherian.finite Γ(Y, U) (integralClosure Γ(Y, U) Γ(X, g ⁻¹ᵁ U)).toSubmodule
    rw [g.fromNormalization_app hU]
    exact (RingHom.finite_respectsIso.cancel_right_isIso _ _).2 (RingHom.finite_algebraMap.2 this)
  have hY' : IsLocallyNoetherian g.normalization := LocallyOfFiniteType.isLocallyNoetherian g.fromNormalization
  have ha : IsProper g.toNormalization := by
    have : IsProper (g.toNormalization ≫ g.fromNormalization) := by
      rw [g.toNormalization_fromNormalization]; exact hg
    exact IsProper.of_comp _ g.fromNormalization
  have hbij : ∀ V : g.normalization.Opens, Function.Bijective (g.toNormalization.app V).hom := by
    intro V
    refine ⟨g.toNormalization.app_injective V, fun t => ?_⟩
    obtain ⟨s, hs⟩ := GlobalTheory.mem_range_app_of_forall_isAffineOpen g.toNormalization V t fun W hW hWV => by
      have : IsNoetherianRing Γ(g.normalization, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
      exact GlobalTheory.mem_range_toNormalization_app g W _
        (RingHom.IsIntegral.of_finite (finite_app_of_isProper g.toNormalization hW) _)
    exact ⟨s, hs⟩
  have hs : Surjective g.toNormalization := by
    have h := g.toNormalization.denseRange.closure_range
    rw [g.toNormalization.isClosedMap.isClosed_range.closure_eq] at h
    exact ⟨Set.range_eq_univ.mp h⟩
  exact ⟨g.normalization, g.toNormalization, g.fromNormalization, g.toNormalization_fromNormalization, hb, ha, hs,
    hbij, fun y => GlobalTheory.T.zariski_connectedness_isPreconnected_fibre X _ g.toNormalization hY' ha hbij y⟩

end GlobalTheory.SteinFact
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SteinFactorisationConnectedFibresStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.stein_factorisation_connected_fibres : ∀ (X Y : Scheme.{0}) (g : X ⟶ Y), IsLocallyNoetherian Y → IsProper g → ∃ (Y' : Scheme.{0}) (a : X ⟶ Y') (b : Y' ⟶ Y), a ≫ b = g ∧ IsFinite b ∧ IsProper a ∧ Surjective a ∧ (∀ V : Y'.Opens, Function.Bijective (a.app V).hom) ∧ ∀ y : Y', _root_.IsPreconnected {x : X | a x = y} := by
  first | exact @GlobalTheory.SteinFact.stein_factorisation | exact GlobalTheory.SteinFact.stein_factorisation | (intros; apply GlobalTheory.SteinFact.stein_factorisation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProjectiveEmbeddingFactorsProper

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem closedFibre_chart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∃ (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), IsNoetherian P' ∧ IsSeparated b ∧ LocallyOfFiniteType b ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ a ≫ b = X.ι ≫ E.f ∧ (∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X) ∧ ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
  intro R _ _ _ hR M G' _ _ hG E
  haveI : IsNoetherianRing R := hR.1
  haveI := M.proper
  obtain ⟨hPn, hTn⟩ := GlobalTheory.T.isNoetherian_projectiveSpace_and_pullback_proper R M.S M.π M.proper E.N
  obtain ⟨hs, hl, hq⟩ := GlobalTheory.T.closedFibreEmbedding_lift_separated_finiteType_quasiCompact R hR M G' hG E
  obtain ⟨H', X'', ν, i, hZ, hν, hi, hiν, -, -⟩ := GlobalTheory.T.exists_finite_openImmersion_nbhd_isolatedFibrePoints E.H.toScheme _
    (pullback.lift E.f (E.H.ι ≫ G'.hom) E.f_over) hTn hs hl hq
    {z | M.π (G'.hom (E.H.ι z)) = closedPoint R} (fun z hz => ⟨⊤, trivial, fun w _ hw => GlobalTheory.T.lift_to_projective_base_injective_over_closedFibre R hR M G' hG E z w hz hw⟩)
  haveI := hν; haveI := hi; haveI := hPn
  have hprop : IsProper (ν ≫ pullback.fst (PSpace.str R E.N) M.π) := inferInstance
  obtain ⟨P'', a'', b'', hab, hb'', ha'', hsurj, hbij, hconn⟩ :=
    GlobalTheory.T.stein_factorisation_connected_fibres X'' (PSpace R E.N) _ inferInstance hprop
  haveI := hb''
  obtain ⟨P', c, X, k, a, hc, hP', hpa, hsa, hba, hk, hac, hsat, -⟩ :=
    GlobalTheory.T.exists_proper_surjective_sections_bijective_over_fibre_open (PSpace R E.N) E.H.toScheme X'' P'' H' i a'' b'' hPn hi ha'' hsurj hbij hb''
  haveI := hc
  have hf : a ≫ c ≫ b'' = X.ι ≫ E.f := by
    rw [← Category.assoc, hac, Category.assoc, Category.assoc, hab, ← Category.assoc i, hiν, ← hk]
    simp only [← Category.assoc]
    rw [Category.assoc (k ≫ H'.ι)]
    erw [pullback.lift_fst]
  have hX : ∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X := by
    intro z hz
    have hz' : z ∈ H' := hZ hz
    obtain ⟨z', rfl⟩ : z ∈ Set.range H'.ι := by rwa [Scheme.Opens.range_ι]
    exact hsat z' (GlobalTheory.T.steinFibre_closedFibre_point_subset_open_part R hR M G' hG E H' X'' ν i P'' a'' b'' hν hi hiν hab hb'' ha'' hconn (fun h hh => hZ hh) z' hz)
  refine ⟨P', c ≫ b'', X, a, hP', inferInstance, inferInstance, hpa, hsa, hba, hf, hX, ?_⟩
  exact GlobalTheory.T.lift_geometricPoint_over_closed_fibre R hR M G' hG E P' (c ≫ b'') X a inferInstance hsa hf hX

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProjectiveEmbeddingFactorsProperStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedFibre_projectiveEmbedding_factors_proper : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∃ (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), IsNoetherian P' ∧ IsSeparated b ∧ LocallyOfFiniteType b ∧ IsProper a ∧ Surjective a ∧ (∀ V : P'.Opens, Function.Bijective (a.app V).hom) ∧ a ≫ b = X.ι ≫ E.f ∧ (∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X) ∧ ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
  first | exact @GlobalTheory.Mum.closedFibre_chart | exact GlobalTheory.Mum.closedFibre_chart | (intros; apply GlobalTheory.Mum.closedFibre_chart <;> assumption)
end
end
