module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomainStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProductCoordConstantOnProjectionFibreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenMulPointOnPullbackContainingClosedFibrStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctionsStatement
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
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.Order.CompletePartialOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismDescendsNearFibreRigidity

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDesc

theorem factor_of_isIso_appTop {X T A : Scheme.{0}} (f : X ⟶ T) [IsIso f.appTop] [IsAffine A]
    (g : X ⟶ A) : ∃ g₀ : T ⟶ A, f ≫ g₀ = g := by
  refine ⟨T.toSpecΓ ≫ Spec.map (g.appTop ≫ inv f.appTop) ≫ A.isoSpec.inv, ?_⟩
  rw [← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, ← Category.assoc (Spec.map _),
    ← Spec.map_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id, ← Category.assoc,
    ← Scheme.toSpecΓ_naturality, Category.assoc, ← Scheme.isoSpec_hom, Iso.hom_inv_id, Category.comp_id]

theorem morphism_descends : ∀ (R : Type) [CommRing R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → Function.Bijective π.appTop.hom → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (y₀ : Y) (w : W), (∀ z : Z, p z = y₀ → z ∈ O) → (∀ z : O.toScheme, p (O.ι z) = y₀ → h z = w) → ∃ (V : Y.Opens) (hV : p ⁻¹ᵁ V ≤ O) (h₀ : V.toScheme ⟶ W), y₀ ∈ V ∧ (p ∣_ V) ≫ h₀ = Z.homOfLE hV ≫ h := by
  intro R _ S Y Z W π y p q hprop _ hbij hflat hpb O h y₀ w hfib hconst
  haveI : IsProper π := hprop
  haveI : IsProper p := MorphismProperty.of_isPullback (P := @IsProper) hpb.flip hprop
  obtain ⟨O', hO', hwO', -⟩ := exists_isAffineOpen_mem_and_subset (show w ∈ (⊤ : W.Opens) from trivial)
  haveI : IsAffine O'.toScheme := hO'
  let T : Z.Opens := O.ι ''ᵁ (h ⁻¹ᵁ O')
  have hTO : T ≤ O := Scheme.Opens.ι_image_le O _
  have hcl : IsClosed (p '' (T : Set Z)ᶜ) := p.isClosedMap _ T.isOpen.isClosed_compl
  let V : Y.Opens := ⟨(p '' (T : Set Z)ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hVT : p ⁻¹ᵁ V ≤ T := by
    intro z hz
    by_contra hzT
    exact hz ⟨z, hzT, rfl⟩
  have hy₀ : y₀ ∈ V := by
    rintro ⟨z, hzT, hz⟩
    apply hzT
    have hzO := hfib z hz
    refine ⟨⟨z, hzO⟩, ?_, Scheme.Opens.ι_apply O _⟩
    show h ⟨z, hzO⟩ ∈ O'
    rw [hconst ⟨z, hzO⟩ (by rw [Scheme.Opens.ι_apply]; exact hz)]
    exact hwO'
  have hV : p ⁻¹ᵁ V ≤ O := hVT.trans hTO
  have hrange : Set.range (Z.homOfLE hV ≫ h) ⊆ Set.range O'.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    obtain ⟨u, hu, hux⟩ := hVT x.2
    have : Z.homOfLE hV x = u := by
      apply Subtype.ext
      refine (Scheme.homOfLE_apply hV x).trans ?_
      exact hux.symm.trans (Scheme.Opens.ι_apply O u)
    show h (Z.homOfLE hV x) ∈ O'
    rw [this]
    exact hu
  have hg := IsOpenImmersion.lift_fac O'.ι _ hrange
  haveI hiso : IsIso (p.app (V.ι ''ᵁ ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions R S Y Z π y p q inferInstance inferInstance hbij hflat hpb _)
  haveI : IsIso (p ∣_ V).appTop := by
    rw [morphismRestrict_appTop]
    refine @IsIso.comp_isIso _ _ _ _ _ _ _ hiso ?_
    first
      | exact Functor.map_isIso _ _
      | exact (Z.presheaf.mapIso (eqToIso _).op).isIso_hom
      | (apply Functor.map_isIso)
  obtain ⟨g₀, hg₀⟩ := factor_of_isIso_appTop (p ∣_ V) (IsOpenImmersion.lift O'.ι _ hrange)
  refine ⟨V, hV, g₀ ≫ O'.ι, hy₀, ?_⟩
  rw [← Category.assoc, hg₀, hg]

end GlobalTheory.MorDesc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismDescendsNearFibreRigidityStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.morphism_descends_near_fibre_rigidity : ∀ (R : Type) [CommRing R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → Function.Bijective π.appTop.hom → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (y₀ : Y) (w : W), (∀ z : Z, p z = y₀ → z ∈ O) → (∀ z : O.toScheme, p (O.ι z) = y₀ → h z = w) → ∃ (V : Y.Opens) (hV : p ⁻¹ᵁ V ≤ O) (h₀ : V.toScheme ⟶ W), y₀ ∈ V ∧ (p ∣_ V) ≫ h₀ = Z.homOfLE hV ≫ h := by
  first | exact @GlobalTheory.MorDesc.morphism_descends | exact GlobalTheory.MorDesc.morphism_descends | (intros; apply GlobalTheory.MorDesc.morphism_descends <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismLocalDescentsGlueUnion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MorDescent

theorem descend_glue : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (I : Type) (V : I → Y.Opens) (hV : ∀ i, p ⁻¹ᵁ V i ≤ O) (h₀ : ∀ i, (V i).toScheme ⟶ W), (∀ i, (p ∣_ V i) ≫ h₀ i = Z.homOfLE (hV i) ≫ h) → ∃ (hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O) (m : (⨆ i, V i).toScheme ⟶ W), (p ∣_ (⨆ i, V i)) ≫ m = Z.homOfLE hV' ≫ h ∧ ∀ (W' : Scheme.{0}) (g g' : (⨆ i, V i).toScheme ⟶ W'), (p ∣_ (⨆ i, V i)) ≫ g = (p ∣_ (⨆ i, V i)) ≫ g' → g = g' := by
  intro R _ _ _ _ S Y Z W π y p q hπp hπs hSi hy hpb O h I V hV h₀ hh
  have hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O := by
    rw [Scheme.Hom.preimage_iSup]; exact iSup_le hV
  haveI := hy
  have hflat : Flat ((⨆ i, V i).ι ≫ y) := inferInstance
  have hsq : IsPullback (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) ((⨆ i, V i).ι ≫ y) π :=
    (isPullback_morphismRestrict p (⨆ i, V i)).paste_vert hpb
  have loc : ∀ (i : I) (T : Scheme.{0}) (k : T ⟶ (p ⁻¹ᵁ (⨆ i, V i)).toScheme) (t : T ⟶ (V i).toScheme),
      k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι ≫ p = t ≫ (V i).ι → k ≫ Z.homOfLE hV' ≫ h = t ≫ h₀ i := by
    intro i T k t hkt
    have sq := isPullback_morphismRestrict p (V i)
    have w : t ≫ (V i).ι = (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) ≫ p := by rw [Category.assoc]; exact hkt.symm
    have h1 : sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ (p ∣_ V i) = t := sq.lift_fst _ _ _
    have h2 : sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ (p ⁻¹ᵁ V i).ι = k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι :=
      sq.lift_snd _ _ _
    have h3 : k ≫ Z.homOfLE hV' = sq.lift t (k ≫ (p ⁻¹ᵁ (⨆ i, V i)).ι) w ≫ Z.homOfLE (hV i) := by
      rw [← cancel_mono O.ι]; simp [h2]
    rw [reassoc_of% h3, ← hh i, reassoc_of% h1]
  have heq : pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (Z.homOfLE hV' ≫ h) =
      pullback.snd (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (Z.homOfLE hV' ≫ h) := by
    let a : pullback (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ⟶ Y :=
      pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (p ∣_ (⨆ i, V i)) ≫ (⨆ i, V i).ι
    have hcov : TopologicalSpace.IsOpenCover (fun i => a ⁻¹ᵁ V i) := by
      rw [TopologicalSpace.IsOpenCover, ← Scheme.Hom.preimage_iSup, eq_top_iff]
      intro x _
      have hx : a.base x ∈ Set.range (⨆ i, V i).ι.base := by
        have ha : a = (pullback.fst (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i)) ≫ (p ∣_ (⨆ i, V i))) ≫ (⨆ i, V i).ι :=
          (Category.assoc _ _ _).symm
        rw [ha]
        first
          | exact ⟨_, rfl⟩
          | (rw [Scheme.comp_base]; exact ⟨_, rfl⟩)
          | exact ⟨_, (Scheme.Hom.comp_apply _ _ _).symm⟩
      rw [Scheme.Opens.range_ι] at hx
      exact hx
    refine Scheme.Cover.hom_ext ((pullback (p ∣_ (⨆ i, V i)) (p ∣_ (⨆ i, V i))).openCoverOfIsOpenCover _ hcov)
      _ _ fun i => ?_
    change (a ⁻¹ᵁ V i).ι ≫ _ = (a ⁻¹ᵁ V i).ι ≫ _
    rw [← Category.assoc, loc i _ _ (a ∣_ V i), ← Category.assoc, loc i _ _ (a ∣_ V i)]
    · rw [morphismRestrict_ι]
      simp only [a, Category.assoc, ← morphismRestrict_ι, pullback.condition_assoc]
    · rw [morphismRestrict_ι]
      simp only [a, Category.assoc, ← morphismRestrict_ι]
  obtain ⟨m, hm, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (⨆ i, V i).toScheme (p ⁻¹ᵁ (⨆ i, V i)).toScheme W π ((⨆ i, V i).ι ≫ y)
    (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) hπp hπs hSi hflat hsq (Z.homOfLE hV' ≫ h) heq
  refine ⟨hV', m, hm, fun W' g g' hg => ?_⟩
  have key := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S (⨆ i, V i).toScheme (p ⁻¹ᵁ (⨆ i, V i)).toScheme W' π ((⨆ i, V i).ι ≫ y)
    (p ∣_ (⨆ i, V i)) ((p ⁻¹ᵁ (⨆ i, V i)).ι ≫ q) hπp hπs hSi hflat hsq ((p ∣_ (⨆ i, V i)) ≫ g)
    (by rw [pullback.condition_assoc])
  exact key.unique rfl hg.symm

end GlobalTheory.MorDescent
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismLocalDescentsGlueUnionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.morphism_local_descents_glue_union : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S Y Z W : Scheme.{0}) (π : S ⟶ Sp R) (y : Y ⟶ Sp R) (p : Z ⟶ Y) (q : Z ⟶ S), IsProper π → Surjective π → IsIntegral S → Flat y → IsPullback p q y π → ∀ (O : Z.Opens) (h : O.toScheme ⟶ W) (I : Type) (V : I → Y.Opens) (hV : ∀ i, p ⁻¹ᵁ V i ≤ O) (h₀ : ∀ i, (V i).toScheme ⟶ W), (∀ i, (p ∣_ V i) ≫ h₀ i = Z.homOfLE (hV i) ≫ h) → ∃ (hV' : p ⁻¹ᵁ (⨆ i, V i) ≤ O) (m : (⨆ i, V i).toScheme ⟶ W), (p ∣_ (⨆ i, V i)) ≫ m = Z.homOfLE hV' ≫ h ∧ ∀ (W' : Scheme.{0}) (g g' : (⨆ i, V i).toScheme ⟶ W'), (p ∣_ (⨆ i, V i)) ≫ g = (p ∣_ (⨆ i, V i)) ≫ g' → g = g' := by
  first | exact @GlobalTheory.MorDescent.descend_glue | exact GlobalTheory.MorDescent.descend_glue | (intros; apply GlobalTheory.MorDescent.descend_glue <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulDescendsNearClosedFibreOfEmbedding

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Near.law_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → N.Law := by
  intro R _ _ _ hR M G' _ _ _ E N fU l hl1 hl2
  obtain ⟨hNoeth, -, hIC, -⟩ := hR
  obtain ⟨hbij, hsurj⟩ := GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M
  haveI := M.proper
  haveI := M.integral
  haveI := N.smooth
  obtain ⟨O, h, hfib, hover, hpt⟩ := GlobalTheory.T.exists_open_mul_point_on_pullback_containing_closedFibre R M G' N
  have hconst := GlobalTheory.T.closedFibre_productCoord_constant_on_projectionFibres R M G' E N fU l hl1 hl2 hsurj O h hpt
  have hflat : Flat (N.U ⊗ N.U).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hPB : IsPullback (pullback.fst (N.U ⊗ N.U).hom M.π) (pullback.snd (N.U ⊗ N.U).hom M.π) (N.U ⊗ N.U).hom M.π :=
    IsPullback.of_hasPullback _ _
  have hpsurj : Surjective (pullback.fst (N.U ⊗ N.U).hom M.π) := by
    haveI : Surjective M.π := hsurj
    infer_instance
  have key : ∀ i : {y₀ : (N.U ⊗ N.U).left // (N.U ⊗ N.U).hom y₀ = closedPoint R},
      ∃ (V : (N.U ⊗ N.U).left.Opens) (hV : pullback.fst (N.U ⊗ N.U).hom M.π ⁻¹ᵁ V ≤ O) (h₀ : V.toScheme ⟶ N.U.left),
        i.1 ∈ V ∧ (pullback.fst (N.U ⊗ N.U).hom M.π ∣_ V) ≫ h₀ = (pullback (N.U ⊗ N.U).hom M.π).homOfLE hV ≫ h := by
    rintro ⟨y₀, hy₀⟩
    obtain ⟨z, hz⟩ := hpsurj.surj y₀
    have hzO : z ∈ O := hfib z (by rw [hz]; exact hy₀)
    exact GlobalTheory.T.morphism_descends_near_fibre_rigidity R M.S _ _ N.U.left M.π _ _ _ M.proper hsurj hbij hflat hPB O h y₀ (h ⟨z, hzO⟩)
      (fun z' hz' => hfib z' (by rw [hz']; exact hy₀))
      (fun z' hz' => hconst z' ⟨z, hzO⟩ (by rw [hz']; exact hz.symm) (by rw [hz']; exact hy₀))
  choose V hV h₀ hmem hcomm using key
  obtain ⟨hV', m, hm, huniq⟩ := GlobalTheory.T.morphism_local_descents_glue_union R M.S _ _ N.U.left M.π _ _ _ M.proper hsurj M.integral hflat hPB O h _ V hV h₀ hcomm
  refine ⟨⨆ i, V i, m, fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hmem _⟩, ?_, ?_⟩
  · apply huniq
    simp only [reassoc_of% hm, hover, Scheme.homOfLE_ι_assoc, morphismRestrict_ι_assoc]
  · intro T v s x y hx hy
    have hc : (v ≫ (⨆ i, V i).ι) ≫ (N.U ⊗ N.U).hom = s ≫ M.π := by
      obtain ⟨x₀, h1, h2, -⟩ := hx
      have e1 : (fst N.U N.U).left ≫ N.U.hom = (N.U ⊗ N.U).hom := Over.w _
      simp only [← e1, ← h2, Category.assoc, ← pullback.condition]
      rw [reassoc_of% h1]
    let z : T ⟶ pullback (N.U ⊗ N.U).hom M.π := pullback.lift (v ≫ (⨆ i, V i).ι) s hc
    let z₁ := (isPullback_morphismRestrict (pullback.fst (N.U ⊗ N.U).hom M.π) (⨆ i, V i)).lift v z (pullback.lift_fst _ _ _).symm
    have hz₁a : z₁ ≫ (pullback.fst (N.U ⊗ N.U).hom M.π ∣_ ⨆ i, V i) = v := IsPullback.lift_fst _ _ _ _
    have hz₁b : z₁ ≫ (pullback.fst (N.U ⊗ N.U).hom M.π ⁻¹ᵁ ⨆ i, V i).ι = z := IsPullback.lift_snd _ _ _ _
    let t := z₁ ≫ (pullback (N.U ⊗ N.U).hom M.π).homOfLE hV'
    have ht : t ≫ O.ι = z := by
      simp only [t, Category.assoc, Scheme.homOfLE_ι, hz₁b]
    have hvm : v ≫ m = t ≫ h := by rw [← hz₁a, Category.assoc, hm, Category.assoc]
    rw [hvm]
    refine hpt T t s x y (by rw [reassoc_of% ht, pullback.lift_snd]) ?_ ?_
    · rw [reassoc_of% ht, pullback.lift_fst_assoc]; exact hx
    · rw [reassoc_of% ht, pullback.lift_fst_assoc]; exact hy

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulDescendsNearClosedFibreOfEmbeddingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mul_descends_near_closed_fibre_of_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → N.Law := by
  first | exact @GlobalTheory.Mum.Near.law_of_emb | exact GlobalTheory.Mum.Near.law_of_emb | (intros; apply GlobalTheory.Mum.Near.law_of_emb <;> assumption)
end
end
