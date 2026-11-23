module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HdimEqZeroOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.BijectiveToPushforwardComp
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CanonicalBundleOpenRestrict
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KodairaVanishingModPSquaredStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.RelativeSncOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfDisjointOpenCover

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem coh_subsingleton_of_disjoint_cover : ∀ (X : Scheme.{0}) (M : LB X) (κ : Type) (U : κ → X.Opens), M.IsLB → ⨆ c, U c = ⊤ → (Pairwise fun a b => Disjoint (U a) (U b)) → ∀ q : ℕ, (∀ c, Subsingleton (coh (LB.toMod (M.pull (U c).ι)) q)) → Subsingleton (coh (LB.toMod M) q) := by
  intro X M κ U hM hc hd q h
  have hj : ∀ (i : κ) (r : ℤ), (U i).ι.appTop (algebraMap ℤ Γ(X, ⊤) r) =
      algebraMap ℤ Γ((U i).toScheme, ⊤) r := fun i r => by simp
  have hs : ∀ i, Subsingleton (coh ((LB.toMod M).restrict (U i).ι) q) := fun i =>
    (cohOn.mapIso ℤ ⊤ q ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app _ ≪≫
      LB.pullbackIso hM (U i).ι)).toEquiv.subsingleton_congr.2 (h i)
  exact (coh.disjointRestrictEquiv ℤ (fun i => (U i).ι) hj (by simpa using hc)
    (by simpa using hd) (LB.toMod M) q).toEquiv.subsingleton

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologySubsingletonOfDisjointOpenCoverStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.cohomology_subsingleton_of_disjoint_open_cover : ∀ (X : Scheme.{0}) (M : LB X) (κ : Type) (U : κ → X.Opens), M.IsLB → ⨆ c, U c = ⊤ → (Pairwise fun a b => Disjoint (U a) (U b)) → ∀ q : ℕ, (∀ c, Subsingleton (coh (LB.toMod (M.pull (U c).ι)) q)) → Subsingleton (coh (LB.toMod M) q) := by
  first | exact @GlobalTheory.coh_subsingleton_of_disjoint_cover | exact GlobalTheory.coh_subsingleton_of_disjoint_cover | (intros; apply GlobalTheory.coh_subsingleton_of_disjoint_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClopenCoverOfSmoothQuasiCompactFie

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem exists_integral_clopen_cover_of_smooth_field :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) [Smooth f] [QuasiCompact f], ∃ (κ : Type) (U : κ → X.Opens), ⨆ c, U c = ⊤ ∧ (Pairwise fun a b => Disjoint (U a) (U b)) ∧ ∀ c, IsIntegral (U c).toScheme ∧ IsClosedImmersion (U c).ι := by
  intro k _ X f _ _
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hopen : ∀ c : _root_.ConnectedComponents X, IsOpen ((_root_.ConnectedComponents.mk : X → _) ⁻¹' {c}) := by
    intro c
    obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian X inferInstance x
  let U : _root_.ConnectedComponents X → X.Opens := fun c => ⟨_, hopen c⟩
  refine ⟨_root_.ConnectedComponents X, U, ?_, ?_, fun c => ?_⟩
  · rw [eq_top_iff]
    intro x _
    exact Opens.mem_iSup.2 ⟨_root_.ConnectedComponents.mk x, rfl⟩
  · intro a b hab
    rw [disjoint_iff, ← SetLike.coe_set_eq]
    ext x
    simp only [U, Opens.coe_inf, Opens.coe_mk, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl rfl
    exact hab rfl
  · obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    have hU : ((U (_root_.ConnectedComponents.mk x) : X.Opens) : Set X) = connectedComponent x :=
      connectedComponents_preimage_singleton
    constructor
    · haveI : ConnectedSpace (U (_root_.ConnectedComponents.mk x)).toScheme := by
        show ConnectedSpace ((U (_root_.ConnectedComponents.mk x) : Set X))
        rw [← isConnected_iff_connectedSpace, hU]
        exact isConnected_connectedComponent
      exact isIntegral_of_smooth_field_of_connectedSpace ((U (_root_.ConnectedComponents.mk x)).ι ≫ f)
    · refine IsClosedImmersion.of_isPreimmersion _ ?_
      rw [Scheme.Opens.range_ι, hU]
      exact isClosed_connectedComponent

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClopenCoverOfSmoothQuasiCompactFieStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_integral_clopen_cover_of_smooth_quasiCompact_field : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) [Smooth f] [QuasiCompact f], ∃ (κ : Type) (U : κ → X.Opens), ⨆ c, U c = ⊤ ∧ (Pairwise fun a b => Disjoint (U a) (U b)) ∧ ∀ c, IsIntegral (U c).toScheme ∧ IsClosedImmersion (U c).ι := by
  first | exact @GlobalTheory.exists_integral_clopen_cover_of_smooth_field | exact GlobalTheory.exists_integral_clopen_cover_of_smooth_field | (intros; apply GlobalTheory.exists_integral_clopen_cover_of_smooth_field <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenSubschemeClosedBaseChange

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem openSubscheme_closedFibre_lift (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R')
    (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X'.Opens)
    (hφ : Function.Surjective φ) (h : IsPullback π f' f (spMap φ)) :
    ∃ (W : X.Opens) (ρ : U.toScheme ⟶ W.toScheme), ρ ≫ W.ι = U.ι ≫ π ∧
      IsPullback ρ (U.ι ≫ f') (W.ι ≫ f) (spMap φ) := by
  have hsp : IsClosedImmersion (spMap φ) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  have hπ : IsClosedImmersion π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) h.flip hsp
  obtain ⟨t, ht, hts⟩ :=
    (IsClosedImmersion.isClosedEmbedding π).isInducing.isOpen_iff.mp U.isOpen
  let W : X.Opens := ⟨t, ht⟩
  have hW : π ⁻¹ᵁ W = U := Opens.ext hts
  subst hW
  refine ⟨W, π ∣_ W, morphismRestrict_ι π W, ?_⟩
  exact IsPullback.paste_vert (isPullback_morphismRestrict π W) h

end GlobalTheory
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.OpenSubschemeClosedBaseChange

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct
theorem _root_.GlobalTheory.T.open_subscheme_closed_base_change : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X'.Opens), Function.Surjective φ → IsPullback π f' f (spMap φ) → ∃ (W : X.Opens) (ρ : U.toScheme ⟶ W.toScheme), ρ ≫ W.ι = U.ι ≫ π ∧ IsPullback ρ (U.ι ≫ f') (W.ι ≫ f) (spMap φ) := by
  first | exact @_root_.GlobalTheory.openSubscheme_closedFibre_lift | exact _root_.GlobalTheory.openSubscheme_closedFibre_lift | (intros; apply _root_.GlobalTheory.openSubscheme_closedFibre_lift <;> assumption)
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.KawamataViehwegModPSquared

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair

namespace GlobalTheory

theorem charp_vanishing_liftable : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0}) (g : Y ⟶ Sp (ZMod (p ^ 2))) (f : X ⟶ Sp (ZMod p)) (π : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f], IsPullback π f g (spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) → IsProjOver f → d < p → ∀ (s : ℕ) (L : Fin s → LB Y) (σ : ∀ i, (L i).Sec) (h : RelSnc g d L σ), ∀ (K : CanonLB f d) (M A : LB X) (hM : M.IsLB) (hA : IsAmpleLB A) (r : ℕ) (b : Fin s → ℕ), 0 < r → (∀ i, b i < r) → r • cls M hM = r • cls K.bundle K.isLB + ∑ i, b i • CechPic.pull π (cls (L i) (h.isLB i)) + cls A hA.isLB → ∀ q : ℕ, 0 < q → Subsingleton (coh (LB.toMod M) q) := by
  intro p _ Y X g f π d _ hpb hproj hdp s L σ h K M A hM hA r b hr hb heq q hq
  have hprop : IsProper f := GlobalTheory.SchemeWords.isProper_of_isProjOver hproj
  have : Smooth f := SmoothOfRelativeDimension.smooth d f
  obtain ⟨κ, U, hcov, hdisj, hU⟩ := GlobalTheory.T.exists_integral_clopen_cover_of_smooth_quasiCompact_field (ZMod p) X f
  refine GlobalTheory.T.cohomology_subsingleton_of_disjoint_open_cover X M κ U hM hcov hdisj q (fun c => ?_)
  have hint := (hU c).1
  have hcl := (hU c).2
  obtain ⟨W, ρ, hρ, hpb'⟩ := GlobalTheory.T.open_subscheme_closed_base_change (ZMod (p ^ 2)) (ZMod p)
    (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) Y X g f π (U c) (ZMod.ringHom_surjective _) hpb
  have hsm : SmoothOfRelativeDimension d ((U c).ι ≫ f) := by
    have := smoothOfRelativeDimension_comp (f := (U c).ι) 0 d f
    simpa using this
  have hproj' : IsProjOver ((U c).ι ≫ f) := by
    obtain ⟨N, i, hi, e⟩ := hproj
    exact ⟨N, (U c).ι ≫ i, inferInstance, by rw [Category.assoc, e]⟩
  have h' := GlobalTheory.T.relative_snc_open_immersion (ZMod (p ^ 2)) Y W.toScheme g W.ι d s L σ h
  let K' : CanonLB ((U c).ι ≫ f) d := Classical.choice inferInstance
  have hA' : IsAmpleLB (A.pull (U c).ι) := hA.pull_of_isClosedImmersion (U c).ι
  have hK := GlobalTheory.T.canonical_bundle_open_restrict (ZMod p) X (U c).toScheme f (U c).ι d K K'
  refine GlobalTheory.T.kodaira_vanishing_mod_p_squared p W.toScheme (U c).toScheme (W.ι ≫ g) ((U c).ι ≫ f) ρ d hpb' hproj' hdp s
    (fun i => (L i).pull W.ι) (fun i => Cartier.secPull (σ i) W.ι) h' K' (M.pull (U c).ι) (A.pull (U c).ι)
    (pull_isLB hM _) hA' r b hr hb ?_ q hq
  have e2 := congrArg (CechPic.pull (U c).ι) heq

  simp only [map_nsmul, map_add (f := _), map_sum] at e2
  rw [cls_pull hM (U c).ι, hK, cls_pull hA.isLB (U c).ι, e2]
  congr 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← pull_comp, ← hρ, pull_comp]
  rfl

end GlobalTheory
end
end
