module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleSectionNonzeroLocusEqAffineOpenAStatement
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAmpleCubSpFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GroupLawsOnCoverAgreeOnCommonPoints
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleLineBundlePullbackOfTranslatesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorTrivialOnFibers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProjOverOfIsProjOverBase
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteCoverByTranslatePairs

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCover

theorem cover : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, (V : Set A.left).Nonempty → ∃ (n : ℕ) (a : Fin n → (𝟙_ (Over (Sp K)) ⟶ A)), ⨆ i, ((𝟙 A * (toUnit A ≫ a i)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  classical
  intro K _ _ A _ hA V hV
  have := hA.smooth
  have := hA.proper
  have : GeometricallyIntegral A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  let O : (𝟙_ (Over (Sp K)) ⟶ A) → A.left.Opens := fun a =>
    (𝟙 A * (toUnit A ≫ a)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a)⁻¹).left ⁻¹ᵁ V
  have key : ∀ y : 𝟙_ (Over (Sp K)) ⟶ A, ∃ a : 𝟙_ (Over (Sp K)) ⟶ A, ∀ p, y.left p ∈ O a := by
    intro y
    have := GlobalTheory.AbelianProjective.isIso_transl_left y
    have : IsIso ((toUnit A ≫ y) * 𝟙 A).left :=
      inferInstanceAs (IsIso ((Over.forget _).map ((toUnit A ≫ y) * 𝟙 A)))
    have : IsIso (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left :=
      inferInstanceAs (IsIso ((Over.forget _).map (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A))))
    have h1 : ((((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ V : A.left.Opens) : Set A.left).Nonempty :=
      GlobalTheory.SS.AmpCub.nonempty_preimage _ hV
    have h2 : (((ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left ⁻¹ᵁ V : A.left.Opens) : Set A.left).Nonempty :=
      GlobalTheory.SS.AmpCub.nonempty_preimage _ hV
    have h3 := nonempty_preirreducible_inter (TopologicalSpace.Opens.isOpen _)
      (TopologicalSpace.Opens.isOpen _) h1 h2
    obtain ⟨a, ha⟩ := GlobalTheory.AbelianProjective.exists_point A
      ((((toUnit A ≫ y) * 𝟙 A).left ⁻¹ᵁ V ⊓ (ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A)).left ⁻¹ᵁ V).isOpen).isLocallyClosed h3
    refine ⟨a, fun p => ?_⟩
    have e : y ≫ (𝟙 A * (toUnit A ≫ a)) = a ≫ ((toUnit A ≫ y) * 𝟙 A) := by
      simp [MonObj.comp_mul, ← Category.assoc]
    have e' : y ≫ (𝟙 A * (toUnit A ≫ a)⁻¹) = a ≫ ι[A] ≫ ((toUnit A ≫ y) * 𝟙 A) := by
      simp [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc]
      rfl
    have hp := ha p
    refine ⟨?_, ?_⟩
    · change (y.left ≫ (𝟙 A * (toUnit A ≫ a)).left) p ∈ V
      rw [← Over.comp_left, e, Over.comp_left]
      exact hp.1
    · change (y.left ≫ (𝟙 A * (toUnit A ≫ a)⁻¹).left) p ∈ V
      rw [← Over.comp_left, e', Over.comp_left]
      exact hp.2
  have htop : ⨆ a, O a = ⊤ := by
    by_contra hne
    have hc : ((⨆ a, O a : A.left.Opens) : Set A.left)ᶜ.Nonempty :=
      Set.nonempty_compl.2 fun h => hne (TopologicalSpace.Opens.ext h)
    obtain ⟨y, hy⟩ := GlobalTheory.AbelianProjective.exists_point A
      (TopologicalSpace.Opens.isOpen _).isClosed_compl.isLocallyClosed hc
    obtain ⟨a, ha⟩ := key y
    exact hy (IsLocalRing.closedPoint K) (TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha _⟩)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover (fun a => (O a : Set A.left))
    (fun a => (O a).isOpen) fun x _ => by
      have hx : x ∈ ⨆ a, O a := by rw [htop]; trivial
      exact Set.mem_iUnion.2 (TopologicalSpace.Opens.mem_iSup.1 hx)
  refine ⟨F.card, fun i => (F.equivFin.symm i).1, top_unique fun x _ => ?_⟩
  obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨F.equivFin ⟨a, ha⟩, by simp only [Equiv.symm_apply_apply]; exact hx⟩

end GlobalTheory.AbCover
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyFiniteCoverByTranslatePairsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelianVariety_finite_cover_by_translate_pairs : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, (V : Set A.left).Nonempty → ∃ (n : ℕ) (a : Fin n → (𝟙_ (Over (Sp K)) ⟶ A)), ⨆ i, ((𝟙 A * (toUnit A ≫ a i)).left ⁻¹ᵁ V ⊓ (𝟙 A * (toUnit A ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  first | exact @GlobalTheory.AbCover.cover | exact GlobalTheory.AbCover.cover | (intros; apply GlobalTheory.AbCover.cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTranslatesCoverGeometricFibre

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FibreCover

theorem cover_geometric_fibre : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (K : Type) [Field K] [IsAlgClosed K] (ξ : Sp K ⟶ S), (∀ z, ∃ x ∈ V, A.hom x = ξ z) → ∃ (n : ℕ) (a : Fin n → (Over.mk ξ ⟶ A)), ⨆ i, ((fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  intro S A _ hA V K _ _ ξ hcov
  have hA' : IsAbelianScheme ((Over.pullback ξ).obj A) := GlobalTheory.isAbelianScheme_pullback_obj ξ A hA
  have hpb := isGrpPullback_pullback A ξ
  have hne : ((pullback.fst A.hom ξ ⁻¹ᵁ V : ((Over.pullback ξ).obj A).left.Opens) : Set ((Over.pullback ξ).obj A).left).Nonempty := by
    obtain ⟨x, hxV, hx⟩ := hcov (default : PrimeSpectrum K)
    obtain ⟨p, hp, -⟩ := Scheme.exists_preimage_of_isPullback hpb.1 x _ hx
    exact ⟨p, by show pullback.fst A.hom ξ p ∈ V; rw [hp]; exact hxV⟩
  obtain ⟨n, a', ha'⟩ := GlobalTheory.T.abelianVariety_finite_cover_by_translate_pairs K ((Over.pullback ξ).obj A) hA' (pullback.fst A.hom ξ ⁻¹ᵁ V) hne
  let a : Fin n → (Over.mk ξ ⟶ A) := fun i => Over.homMk ((a' i).left ≫ pullback.fst A.hom ξ) (by
    show ((a' i).left ≫ pullback.fst A.hom ξ) ≫ A.hom = ξ
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    have h := Over.w (a' i)
    change (a' i).left ≫ pullback.snd A.hom ξ = 𝟙 _ at h
    rw [h, Category.id_comp])
  refine ⟨n, a, ?_⟩
  have e : (A ⊗ Over.mk ξ).hom = ((Over.pullback ξ).obj A).hom ≫ ξ := by
    first | rfl | exact pullback.condition
  have hx : (fst A (Over.mk ξ)).left = Over.Hom.left (𝟙 ((Over.pullback ξ).obj A)) ≫ pullback.fst A.hom ξ := by
    first | rfl | simp
  have hy : ∀ i, (snd A (Over.mk ξ) ≫ a i).left = (toUnit ((Over.pullback ξ).obj A) ≫ a' i).left ≫ pullback.fst A.hom ξ := by
    intro i; first | rfl | simp [a]
  have key₁ : ∀ i, (fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)).left =
      (𝟙 ((Over.pullback ξ).obj A) * (toUnit ((Over.pullback ξ).obj A) ≫ a' i)).left ≫ pullback.fst A.hom ξ := fun i =>
    GlobalTheory.CoverOpCompat.push_mul hpb (T := ((Over.pullback ξ).obj A).left) (ρ := ((Over.pullback ξ).obj A).hom)
      (r := (A ⊗ Over.mk ξ).hom) e (𝟙 ((Over.pullback ξ).obj A)) (toUnit ((Over.pullback ξ).obj A) ≫ a' i)
      (fst A (Over.mk ξ)) (snd A (Over.mk ξ) ≫ a i) hx (hy i)
  have key₂ : ∀ i, ((snd A (Over.mk ξ) ≫ a i)⁻¹).left =
      ((toUnit ((Over.pullback ξ).obj A) ≫ a' i)⁻¹).left ≫ pullback.fst A.hom ξ := fun i =>
    GlobalTheory.CoverOpCompat.push_inv hpb (T := ((Over.pullback ξ).obj A).left) (ρ := ((Over.pullback ξ).obj A).hom)
      (r := (A ⊗ Over.mk ξ).hom) e (toUnit ((Over.pullback ξ).obj A) ≫ a' i) (snd A (Over.mk ξ) ≫ a i) (hy i)
  have key₃ : ∀ i, (fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)⁻¹).left =
      (𝟙 ((Over.pullback ξ).obj A) * (toUnit ((Over.pullback ξ).obj A) ≫ a' i)⁻¹).left ≫ pullback.fst A.hom ξ := fun i =>
    GlobalTheory.CoverOpCompat.push_mul hpb (T := ((Over.pullback ξ).obj A).left) (ρ := ((Over.pullback ξ).obj A).hom)
      (r := (A ⊗ Over.mk ξ).hom) e (𝟙 ((Over.pullback ξ).obj A)) ((toUnit ((Over.pullback ξ).obj A) ≫ a' i)⁻¹)
      (fst A (Over.mk ξ)) ((snd A (Over.mk ξ) ≫ a i)⁻¹) hx (key₂ i)
  refine Eq.trans ?_ ha'
  congr 1
  funext i
  rw [key₁ i, key₃ i, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]

end GlobalTheory.FibreCover
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTranslatesCoverGeometricFibreStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_translates_cover_geometric_fibre : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (V : A.left.Opens) (K : Type) [Field K] [IsAlgClosed K] (ξ : Sp K ⟶ S), (∀ z, ∃ x ∈ V, A.hom x = ξ z) → ∃ (n : ℕ) (a : Fin n → (Over.mk ξ ⟶ A)), ⨆ i, ((fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)).left ⁻¹ᵁ V ⊓ (fst A (Over.mk ξ) * (snd A (Over.mk ξ) ≫ a i)⁻¹).left ⁻¹ᵁ V) = ⊤ := by
  first | exact @GlobalTheory.FibreCover.cover_geometric_fibre | exact GlobalTheory.FibreCover.cover_geometric_fibre | (intros; apply GlobalTheory.FibreCover.cover_geometric_fibre <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAffineNonzeroLocusAbelianSchemeNoether

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AffineLocusAmple

theorem relAmple_of_affine_nonzeroLocus : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ s : LB.Sec M, IsAffineOpen (Out.nonzeroLocus s) → (∀ p : Sp R, ∃ x ∈ Out.nonzeroLocus s, A.hom x = p) → Out.RelAmple A M := by
  intro R _ _ A _ hA M hM s hV hs
  have := hA.proper
  have := hA.smooth
  refine GlobalTheory.ProperFinite.relAmple_of_geometricFibres A hM fun K _ _ y => ?_
  obtain ⟨n, a, ha⟩ := GlobalTheory.T.exists_finite_translates_cover_geometric_fibre (Sp R) A hA _ K y fun z => hs (y z)
  have : IsAffine (Over.mk y).left := inferInstanceAs (IsAffine (Sp K))
  have h := GlobalTheory.T.isAmple_lineBundle_pullback_of_translates R A hA M hM _ _ rfl hV ⟨M, hM, s, rfl, rfl⟩ (Over.mk y) n a ha
    fun i => GlobalTheory.cechPic_sp_field_eq_zero K _
  exact h

end GlobalTheory.AffineLocusAmple
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfAffineNonzeroLocusAbelianSchemeNoetherStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.relAmple_of_affine_nonzeroLocus_abelianScheme_noetherian : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (M : LB A.left), M.IsLB → ∀ s : LB.Sec M, IsAffineOpen (Out.nonzeroLocus s) → (∀ p : Sp R, ∃ x ∈ Out.nonzeroLocus s, A.hom x = p) → Out.RelAmple A M := by
  first | exact @GlobalTheory.AffineLocusAmple.relAmple_of_affine_nonzeroLocus | exact GlobalTheory.AffineLocusAmple.relAmple_of_affine_nonzeroLocus | (intros; apply GlobalTheory.AffineLocusAmple.relAmple_of_affine_nonzeroLocus <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelAmpleOfAffineOpenMeetsFibres

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjNormal

theorem exists_relAmple_of_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsDomain R] [IsIntegrallyClosed R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ V : A.left.Opens, IsAffineOpen V → (∀ s : Sp R, ∃ x ∈ V, A.hom x = s) → ∃ L : LB A.left, L.IsLB ∧ Out.RelAmple A L := by
  intro R _ _ _ _ A _ hA V hV hV'
  obtain ⟨M, hM, s, hs⟩ := GlobalTheory.T.exists_section_nonzeroLocus_eq_affineOpen R A hA V hV hV'
  exact ⟨M, hM, GlobalTheory.T.relAmple_of_affine_nonzeroLocus_abelianScheme_noetherian R A hA M hM s (hs ▸ hV) (hs ▸ hV')⟩

end GlobalTheory.ProjNormal
end
end
