module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierLocusOverDenseOpenBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemPreimageSupOfStalkKrullDimLeOneFlatStatement
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
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
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusPullbackAndVanishIntoLocusStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoSmulPicardClassExtendsAbelianSchemeStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsAffineOpenOfRingKrullDimLeOne

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

namespace GlobalTheory

theorem isIso_of_isAffine_of_coheight_le_one {X Y : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] [IsAffine X] [IsAffine Y] (f : Y ⟶ X) [IsOpenImmersion f]
    (hf : ∀ x : X, Order.coheight x ≤ 1 → x ∈ Set.range f) : IsIso f := by
  have h : IsIso (f.appTop) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (bijective_app_of_coheight_le_one f hf ⊤)
  have : IsIso (Spec.map f.appTop) := inferInstance
  have e : f = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ X.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp
  rw [e]
  infer_instance

theorem eq_of_isAffineOpen_of_ringKrullDim_le_one (X : Scheme.{0}) [IsLocallyNoetherian X]
    [X.IsSeparated] (hX : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (V V' : X.Opens)
    (hV : IsAffineOpen V) (hle : V ≤ V')
    (h : ∀ z ∈ V', ringKrullDim (X.presheaf.stalk z) ≤ 1 → z ∈ V) : V' = V := by
  have := GlobalTheory.IsNormalScheme.of_pred hX
  refine le_antisymm (fun z hz ↦ ?_) hle
  obtain ⟨_, ⟨N, hN, rfl⟩, hzN, hNV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hz V'.isOpen
  have hN' : IsAffineOpen N := hN
  have hNV' : IsAffineOpen (N ⊓ V) := hN'.inf hV
  have : IsAffine N := hN'
  have : IsAffine (N ⊓ V : X.Opens) := hNV'
  have hiso : IsIso (X.homOfLE (inf_le_left : N ⊓ V ≤ N)) := by
    refine isIso_of_isAffine_of_coheight_le_one _ fun x hx ↦ ?_
    have hx' : Order.coheight (Scheme.Opens.ι N x) ≤ 1 := by rwa [coheight_apply_of_isOpenImmersion]
    have hxV : Scheme.Opens.ι N x ∈ V := h _ (hNV x.2) ((ringKrullDim_stalk_le_one_iff _).mpr hx')
    exact ⟨⟨x.1, x.2, hxV⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
  obtain ⟨y, hy⟩ := (X.homOfLE (inf_le_left : N ⊓ V ≤ N)).surjective ⟨z, hzN⟩
  have hyz : y.1 = z := (Scheme.homOfLE_apply _ y).symm.trans (congrArg Subtype.val hy)
  exact hyz ▸ y.2.2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfIsAffineOpenOfRingKrullDimLeOneStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.eq_of_isAffineOpen_of_ringKrullDim_le_one' : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] [X.IsSeparated], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ V V' : X.Opens, IsAffineOpen V → V ≤ V' → (∀ z ∈ V', ringKrullDim (X.presheaf.stalk z) ≤ 1 → z ∈ V) → V' = V := by
  first | exact @GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one | exact GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one | (intros; apply GlobalTheory.eq_of_isAffineOpen_of_ringKrullDim_le_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusExtendFromBigOpen

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem extend_isLocus_of_big_open : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] [X.IsSeparated], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ V W : X.Opens, IsAffineOpen V → V ≤ W → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic X, IsLocus (GlobalTheory.CechPic.pull W.ι c) (W.ι ⁻¹ᵁ V) → IsLocus c V := by
  intro X _ _ hX V W hV hVW hW c hloc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨r, hr⟩ := IsLocus.exists_sec (pull_isLB hL W.ι) hloc
  obtain ⟨t, ht, -⟩ := ((GlobalTheory.extension_over_codim_two X hX).1 W hW).2.1 L r
  have e : GlobalTheory.secPull t W.ι = r := (GlobalTheory.lbSec_ext fun i => rfl).trans ht
  have h1 : W.ι ⁻¹ᵁ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t = W.ι ⁻¹ᵁ V := by
    rw [← GlobalTheory.nonzeroLocus_secPull, e, hr]
  have key : ∀ x (hx : x ∈ W), x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t ↔ x ∈ V := fun x hx => by
    have := congrArg (fun U : W.toScheme.Opens => (⟨x, hx⟩ : W.toScheme) ∈ U) h1
    exact Iff.of_eq this
  refine ⟨L, hL, t, rfl, ?_⟩
  exact GlobalTheory.T.eq_of_isAffineOpen_of_ringKrullDim_le_one' X hX V (ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t) hV (fun x hx => (key x (hVW hx)).2 hx)
    (fun z hz hz1 => (key z (hW z hz1)).1 hz)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusExtendFromBigOpenStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.nonvanishingLocus_extend_from_big_open : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] [X.IsSeparated], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → ∀ V W : X.Opens, IsAffineOpen V → V ≤ W → (∀ z : X, ringKrullDim ((X).presheaf.stalk z) ≤ 1 → z ∈ W) → ∀ c : Pic X, IsLocus (GlobalTheory.CechPic.pull W.ι c) (W.ι ⁻¹ᵁ V) → IsLocus c V := by
  first | exact @GlobalTheory.extend_isLocus_of_big_open | exact GlobalTheory.extend_isLocus_of_big_open | (intros; apply GlobalTheory.extend_isLocus_of_big_open <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenMeetingFibresIsNonvanishingLocus

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AffineLocus

theorem isLocus_of_isAffineOpen_of_meets_fibres : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ c : Pic A.left, IsLocus c V := by
  intro R _ _ _ _ A _ hA V hV hfib
  have := hA.smooth
  have := hA.proper
  have := hA.geomConnected
  have hnS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (Sp R) := GlobalTheory.IsNormalScheme.pred (Sp R)
  obtain ⟨U, c, hU, hc⟩ := GlobalTheory.T.exists_cartier_locus_over_dense_open_base R A hA V hV hfib
  have hVW : V ≤ A.hom ⁻¹ᵁ U ⊔ V := le_sup_right
  have h0 : GlobalTheory.CechPic.pull (A.left.homOfLE hVW) c = 0 := by
    refine GlobalTheory.T.nonvanishingLocus_pullback_and_vanish_into_locus.2 _ _ _ c _ hc fun y => ?_
    show (A.left.homOfLE hVW ≫ (A.hom ⁻¹ᵁ U ⊔ V).ι) y ∈ V
    rw [Scheme.homOfLE_ι]
    exact y.2
  obtain ⟨c', hc'⟩ := GlobalTheory.T.two_smul_picardClass_extends_abelianScheme (Sp R) hnS A hA U V hU hfib c h0
  have h2 : IsLocus (GlobalTheory.CechPic.pull (A.hom ⁻¹ᵁ U ⊔ V).ι c') ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V) := by
    rw [hc', two_nsmul, ← inf_idem ((A.hom ⁻¹ᵁ U ⊔ V).ι ⁻¹ᵁ V)]
    exact hc.add hc
  have : Flat A.hom := inferInstance
  have : GeometricallyIntegral A.hom := GlobalTheory.geometricallyIntegral_of_smooth _
  have hbig := GlobalTheory.T.mem_preimage_sup_of_stalk_krullDim_le_one_flat A.left (Sp R) A.hom V U hfib hU
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : A.left.IsSeparated := by
    have : IsSeparated (terminal.from A.left) := by rw [← terminal.comp_from A.hom]; infer_instance
    exact ⟨this⟩
  have : GlobalTheory.IsNormalScheme A.left := GlobalTheory.isNormalScheme_of_smooth A.hom
  exact ⟨c', GlobalTheory.T.nonvanishingLocus_extend_from_big_open A.left (GlobalTheory.IsNormalScheme.pred _) V _ hV hVW hbig c' h2⟩

end GlobalTheory.AffineLocus
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenMeetingFibresIsNonvanishingLocusStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.affineOpen_meeting_fibres_is_nonvanishingLocus : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ c : Pic A.left, IsLocus c V := by
  first | exact @GlobalTheory.AffineLocus.isLocus_of_isAffineOpen_of_meets_fibres | exact GlobalTheory.AffineLocus.isLocus_of_isAffineOpen_of_meets_fibres | (intros; apply GlobalTheory.AffineLocus.isLocus_of_isAffineOpen_of_meets_fibres <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionNonzeroLocusEqAffineOpenA

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_lineBundle_section_nonzeroLocus_eq_affineOpen :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R]
      (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V →
      (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) →
      ∃ M : LB A.left, M.IsLB ∧ ∃ s : LB.Sec M, Out.nonzeroLocus s = V := by
  intro R _ _ _ _ A _ hA V hV hs
  obtain ⟨c, L, hL, s, -, e⟩ := GlobalTheory.T.affineOpen_meeting_fibres_is_nonvanishingLocus R A hA V hV hs
  exact ⟨L, hL, s, e⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionNonzeroLocusEqAffineOpenAStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_section_nonzeroLocus_eq_affineOpen : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ M : LB A.left, M.IsLB ∧ ∃ s : LB.Sec M, Out.nonzeroLocus s = V := by
  first | exact @GlobalTheory.exists_lineBundle_section_nonzeroLocus_eq_affineOpen | exact GlobalTheory.exists_lineBundle_section_nonzeroLocus_eq_affineOpen | (intros; apply GlobalTheory.exists_lineBundle_section_nonzeroLocus_eq_affineOpen <;> assumption)
end
end
