module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.ConclusionOfSmooth
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.NotSubsetOfDenseCompl
public import Development.AutomorphicSpectrum.PublishedTheorems.Metrics₂.PoincareLelongInv
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HasAffineChartId
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeActionAffineChart
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
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.OrbitAffineNeighbourhoodStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientOfAffineChartCoverStatement
import Mathlib.CategoryTheory.Limits.Shapes.Connected
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.QuotientIsAbelianSchemeOfQuotientScheme
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FormallyUnramifiedOfCompOfEtaleOfSurjective
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFlatSubgroupSchemeStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyOfFinitePresentationOfCancelStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormLineBundleDescentStatement
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormMapRestrictionCompatible
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Tactic.Lemma
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResKOfResolutionPrincipalisation
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArithIntersectionSystemOfPoincareLelong
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.PoincareLelongOfInv

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeActionAffineChartStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

theorem _root_.GlobalTheory.T.free_action_affine_chart : ∀ {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X], IsFiniteLocallyFree G.hom → IsFreeAction G X → ∀ (V : X.left.Opens) (W : S.Opens), IsAffineOpen V → IsAffineOpen W → V ≤ X.hom ⁻¹ᵁ W → (γ[G, X] : G ⊗ X ⟶ X).left ⁻¹ᵁ V = (snd G X).left ⁻¹ᵁ V → HasAffineChart (γ[G, X] : G ⊗ X ⟶ X).left (snd G X).left V := by
  first | exact @GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable | exact GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable | (intros; apply GlobalTheory.CompanionTheory.FreeQuotProof.Chart.hasAffineChart_of_stable <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FreeQuotientSchemeHolds

section

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Hypotheses₂
open FreeQuot GlobalTheory.CompanionTheory.FreeQuotProof

theorem FreeQuotientScheme_holds : FreeQuotientScheme := by
  intro S G X _ _ hG hfree horb
  obtain ⟨Y₀, q₀, hfin, hflat, hfp, hsurj, hpb⟩ :=
    GlobalTheory.T.quotient_of_affine_chart_cover _ _ (fun x => by
      obtain ⟨U, hU, hxU⟩ := horb x
      obtain ⟨V, W, hxV, hV, hW, hVW, hinv⟩ :=
        GlobalTheory.T.orbit_affine_neighbourhood G X hG x U hU hxU
      exact ⟨V, hxV,
        GlobalTheory.T.free_action_affine_chart G X hG hfree V W hV hW hVW hinv⟩)
  haveI : IsFinite q₀ := hfin
  haveI : Flat q₀ := hflat
  haveI : LocallyOfFinitePresentation q₀ := hfp
  haveI : Surjective q₀ := hsurj
  have hdesc : ∀ {Z} (g₁ g₂ : Z ⟶ X.left), g₁ ≫ q₀ = g₂ ≫ q₀ → g₁ ≫ X.hom = g₂ ≫ X.hom := by
    intro Z g₁ g₂ hg
    rw [← hpb.lift_fst g₁ g₂ hg]
    conv_rhs => rw [← hpb.lift_snd g₁ g₂ hg]
    simp only [Category.assoc]
    first
      | exact hpb.lift g₁ g₂ hg ≫= ((Over.w _).trans (Over.w _).symm)
      | (simp only [Over.w]; try rfl)
  have key : ∀ {Y : Over S} (q : X ⟶ Y), GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfTorsor G q →
      GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfQuotient G q ∧ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfTorsor G q := fun _ h => ⟨h.isFppfQuotient, h⟩
  refine ⟨Over.mk (EffectiveEpi.desc q₀ X.hom hdesc),
    Over.homMk q₀ (EffectiveEpi.fac q₀ X.hom hdesc), key _ ?_⟩
  unfold GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFppfTorsor
  refine ⟨IsPullback.of_map_of_faithful (Over.forget S) hpb, PUnit, fun _ => X.left, fun _ => q₀,
    fun _ => ⟨hflat, hfp⟩, fun y => ?_, fun _ => ⟨𝟙 _, Category.id_comp _⟩⟩
  obtain ⟨z, hz⟩ := hsurj.surj y
  exact ⟨PUnit.unit, z, hz⟩

end GlobalTheory.CompanionTheory.Hypotheses₂
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormMapRestrictionCompatibleStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.norm_map_restriction_compatible : ∀ {X Y : Scheme.{0}} (q : X ⟶ Y), IsFinite q → Flat q → LocallyOfFinitePresentation q → ∃ N : ∀ V : Y.Opens, Γ(X, q ⁻¹ᵁ V) →* Γ(Y, V), (∀ (V W : Y.Opens) (h : W ≤ V) (a : Γ(X, q ⁻¹ᵁ V)), (Y.presheaf.map (homOfLE h).op).hom (N V a) = N W ((X.presheaf.map (homOfLE (show q ⁻¹ᵁ W ≤ q ⁻¹ᵁ V from fun _ hx => h hx)).op).hom a)) ∧ ∀ (V : Y.Opens) (a : Γ(X, q ⁻¹ᵁ V)) (y : Y), y ∈ V → (y ∈ Y.basicOpen (N V a) ↔ ∀ x : X, q x = y → x ∈ X.basicOpen a) := by
  first | exact @GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf | exact GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf | (intros; apply GlobalTheory.CompanionTheory.FinFlatNorm.exists_norm_sheaf <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SeparatedOfFiniteSurjectiveQuotient

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.QuotientSide

theorem isSeparated_of_finite_surjective {S X Y : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S)
    (r : X ⟶ Y) (w : r ≫ g = f) [IsSeparated f] [IsFinite r] [Surjective r] : IsSeparated g := by
  subst w
  let m : pullback (r ≫ g) (r ≫ g) ⟶ pullback g g :=
    pullback.map _ _ _ _ r r (𝟙 S) (by simp) (by simp)
  have hm : IsFinite m :=
    MorphismProperty.pullbackMap (P := @IsFinite) (i₁ := r) (i₂ := r) inferInstance inferInstance
      rfl rfl
  have comm : pullback.diagonal (r ≫ g) ≫ m = r ≫ pullback.diagonal g := by
    have h₁ : m ≫ pullback.fst g g = pullback.fst (r ≫ g) (r ≫ g) ≫ r := pullback.lift_fst _ _ _
    have h₂ : m ≫ pullback.snd g g = pullback.snd (r ≫ g) (r ≫ g) ≫ r := pullback.lift_snd _ _ _
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, h₁, ← Category.assoc, pullback.diagonal_fst,
        pullback.diagonal_fst, Category.id_comp, Category.comp_id]
    · rw [Category.assoc, Category.assoc, h₂, ← Category.assoc, pullback.diagonal_snd,
        pullback.diagonal_snd, Category.id_comp, Category.comp_id]
  have hrange : Set.range (pullback.diagonal g) =
      m '' Set.range (pullback.diagonal (r ≫ g)) := by
    rw [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, comm,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr r.surjective, Set.image_univ]
  have hclosed : IsClosed (Set.range (pullback.diagonal g)) := by
    rw [hrange]
    exact m.isClosedMap _ (pullback.diagonal (r ≫ g)).isClosedEmbedding.isClosed_range
  exact ⟨IsClosedImmersion.of_isPreimmersion _ hclosed⟩

theorem isSeparated_target_of_finite_surjective :
    ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q →
      IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left →
      IsSeparated Y.hom := by
  intro S X Y K q p₁ p₂ _ _ hX hq hs
  exact isSeparated_of_finite_surjective X.hom Y.hom q.left (Over.w q)

end GlobalTheory.CompanionTheory.QuotientSide
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SeparatedOfFiniteSurjectiveQuotientStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.separated_of_finite_surjective_quotient : ∀ {S : Scheme.{0}} {X Y K : Over S} (q : X ⟶ Y) (p₁ p₂ : K ⟶ X), IsPullback p₁ p₂ q q → IsFinite p₂.left → IsSeparated X.hom → IsFinite q.left → Surjective q.left → IsSeparated Y.hom := by
  first | exact @GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective | exact GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective | (intros; apply GlobalTheory.CompanionTheory.QuotientSide.isSeparated_target_of_finite_surjective <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.QuotientByFiniteFlatOfFreeQuotient

section

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.GR.QuotSide

section Act
variable {S : Scheme.{0}} {G A : Over S} [GrpObj G] [GrpObj A] (h : G ⟶ A) [IsMonHom h]

abbrev act : ModObj G A :=
  letI := ModObj.regular A
  Mod.scalarRestriction h A

lemma act_smul : (act h).smul = (fst G A ≫ h) * snd G A := by
  rw [Hom.mul_def]
  change h ▷ A ≫ μ[A] = _
  congr 1

end Act

theorem quotientByFiniteFlat_of_freeQuotient (hF : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme) :
    QuotientByFiniteFlatStatement := by
  intro R _ A _ L hA hL hamp B _ _ h hsub
  have := hA.comm
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  obtain ⟨_, hmon, hmono⟩ := GlobalTheory.T.finite_flat_subgroup_scheme R A B h hsub
  letI := act h
  have hgam : (γ[sp (R₀ := R) B, A] : sp (R₀ := R) B ⊗ A ⟶ A) = (fst _ A ≫ h) * snd _ A := act_smul h
  have hsmul : ∀ {T : Over (Spec (CommRingCat.of R))} (g : T ⟶ sp (R₀ := R) B) (x : T ⟶ A),
      g • x = (g ≫ h) * x := by
    intro T g x
    rw [Hom.smul_def, hgam, comp_mul]
    simp
  have hample : GlobalTheory.IsAmpleLB L := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine A hL hamp
  have hG : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFiniteLocallyFree (sp (R₀ := R) B).hom := by
    have e : (sp (R₀ := R) B).hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) := rfl
    have := hsub.proj
    have := hsub.fin
    have : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
    have hfp : (algebraMap R B).FinitePresentation :=
      RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation R B)
    rw [e]
    refine ⟨(IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance),
      Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance), ?_⟩
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).2 hfp
  have hfree : GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.IsFreeAction (sp (R₀ := R) B) A := by
    intro T g x hx
    rw [hsmul] at hx
    have h1 : g ≫ h = 1 := mul_eq_right.mp hx
    rw [← cancel_mono h, h1, MonObj.one_comp]
  have horb : ∀ x : A.left, ∃ U : A.left.Opens, IsAffineOpen U ∧
      GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀ := R) B) A x ⊆ U := by
    intro x
    have hf : IsFinite (sp (R₀ := R) B).hom := hG.1
    have hs : IsFinite (snd (sp (R₀ := R) B) A).left := by
      rw [Over.snd_left]; infer_instance
    have hfin : (GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot.orbit (sp (R₀ := R) B) A x).Finite :=
      (Scheme.Hom.finite_preimage_singleton _ x).image _
    obtain ⟨n, -, s, h₁, -, h₂⟩ := hample.exists_affine_finite_subset hfin
      (U := ⊤) (fun _ _ => trivial)
    exact ⟨_, h₂, h₁⟩
  obtain ⟨Y, q, -, hT⟩ := hF _ (sp (R₀ := R) B) A hG hfree horb
  obtain ⟨hq1, hq2, hq3⟩ := hT.isFiniteLocallyFree hG
  have hq4 := hT.surjective
  have hq : IsPullback ((fst _ A ≫ h) * snd _ A) (snd _ A) q q := hgam ▸ hT.1
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨inst, hcomm, hhom, hker⟩ := GlobalTheory.AbelianQuotient.exists_grpObj h q hq
  have hw : q.left ≫ Y.hom = A.hom := Over.w q
  have hsnd : IsFinite (snd (sp (R₀ := R) B) A).left := by
    have hf : IsFinite (sp (R₀ := R) B).hom := hG.1
    rw [Over.snd_left]; infer_instance
  have hab : IsAbelianScheme Y := by
    have := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth
      hA.geomConnected
    have : IsSeparated Y.hom := GlobalTheory.T.separated_of_finite_surjective_quotient q _ _ hq hsnd inferInstance hq1 hq4
    have : Flat (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : UniversallyClosed (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : GeometricallyReduced (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have : GeometricallyConnected (q.left ≫ Y.hom) := by rw [hw]; infer_instance
    have := GlobalTheory.flat_of_comp_of_flat_of_surjective q.left Y.hom
    have := UniversallyClosed.of_comp_surjective q.left Y.hom
    have := GlobalTheory.AbelianQuotient.geometricallyReduced_of_comp q.left Y.hom
    have : LocallyOfFinitePresentation Y.hom :=
      GlobalTheory.T.locallyOfFinitePresentation_of_cancel q.left Y.hom hq1 hq2 hq3 hq4 (by rw [hw]; infer_instance)
    exact ⟨hcomm, GlobalTheory.AbelianQuotient.smooth_of_grpObj_of_flat Y, ⟨⟩,
      GlobalTheory.AbelianQuotient.geometricallyConnected_of_comp q.left Y.hom⟩
  have := hab.proper
  obtain ⟨N, hN₁, hN₂⟩ := GlobalTheory.T.norm_map_restriction_compatible q.left hq1 hq2 hq3
  obtain ⟨L', hL', hN⟩ := GlobalTheory.T.norm_line_bundle_descent q.left hq1 N hN₁ hN₂ L hL (by
    intro y
    obtain ⟨W, -, h₁, -, t⟩ := hample.exists_affine_finite_subset_trivial hL
      (Scheme.Hom.finite_preimage_singleton q.left y) (U := ⊤) (fun _ _ => trivial)
    exact ⟨W, fun x hx => h₁ hx, t⟩)
  refine ⟨Y, inst, L', q, hab, hL', ?_, hhom, hq1, hq2, hq4, ?_⟩
  · have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
    have : CompactSpace Y.left := q.left.surjective.compactSpace q.left.continuous
    refine (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine Y hL').2
      (GlobalTheory.isAmpleLB_of_forall_le hL' fun y U hy => ?_)
    obtain ⟨n, hn, s, h₁, h₂, -⟩ := hample.exists_affine_finite_subset
      (Scheme.Hom.finite_preimage_singleton q.left y) (U := q.left ⁻¹ᵁ U)
      (fun x hx => show q.left x ∈ U from (show q.left x = y from hx) ▸ hy)
    obtain ⟨σ, hσ⟩ := hN n s
    refine ⟨n, hn, σ, (hσ y).2 fun x hx => h₁ hx, fun y' hy' => ?_⟩
    obtain ⟨x, rfl⟩ := q.left.surjective y'
    exact h₂ ((hσ _).1 hy' x rfl)
  · intro S _ _ z
    have hhq : h ≫ q = 1 := hker.w.trans Hom.one_def.symm
    constructor
    · intro hz
      let y : sp (R₀ := R) S ⟶ sp (R₀ := R) B :=
        hker.lift z (toUnit _) (by rw [hz, Hom.one_def])
      have hy : y ≫ h = z := hker.lift_fst _ _ _
      obtain ⟨ψ, hψ⟩ := Spec.map_surjective y.left
      have hc : CommRingCat.ofHom (algebraMap R B) ≫ ψ = CommRingCat.ofHom (algebraMap R S) := by
        apply Spec.map_injective
        rw [Spec.map_comp, hψ]
        exact Over.w y
      let φ : B →ₐ[R] S := { ψ.hom with
        commutes' := fun r => congr($hc r) }
      have hφ : spMap φ = y := Over.OverMorphism.ext hψ
      exact ⟨φ, by rw [hφ, hy]⟩
    · rintro ⟨φ, rfl⟩
      rw [Category.assoc, hhq, comp_one]

end GlobalTheory.CompanionTheory.Ar.GR.QuotSide
end
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.AhSlim

section

@[expose] public section

namespace PositivityTheory.HtPt.Ah

open GlobalTheory.CompanionTheory.Ar

theorem resK (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero) :
    ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement :=
  GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide.resK_of_resolution_principalisation h₁ h₂

theorem ais (h₁ : GlobalTheory.CompanionTheory.Hypotheses₂.ResolutionCharZero) (h₂ : GlobalTheory.CompanionTheory.Hypotheses₂.PrincipalisationCharZero)
    (hPL : GlobalTheory.CompanionTheory.Hypotheses₂.PoincareLelongInv) : ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement :=
  Pub.arithIntersectionSystem_of_poincareLelong_resK (Tw.Main.poincareLelong_of_inv (resK h₁ h₂) hPL) (resK h₁ h₂)

theorem quot : GR.QuotientByFiniteFlatStatement :=
  GR.QuotSide.quotientByFiniteFlat_of_freeQuotient GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuotientScheme_holds

end PositivityTheory.HtPt.Ah
end
end
