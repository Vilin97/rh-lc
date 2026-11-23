module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
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
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.LevelCoverSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MfCoords
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFullLevelFiniteExtensionStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullLevelGenericCoverStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointNormalCoordsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverRestrictIntStatement
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPrimitiveRootOfLevel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HodgeExists

theorem exists_lift_torsion {S S' Z : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (b : Z ⟶ S') (a : Z ⟶ S) (hab : a = b ≫ f) (n : ℕ)
    (g : Over.mk a ⟶ G) (hg : g ^ n = 1) : ∃ g' : Over.mk b ⟶ G', g'.left ≫ φ = g.left ∧ g' ^ n = 1 := by
  subst hab
  let P : (Over.mk b ⟶ G') → (Over.mk (b ≫ f) ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this])
  have hP : ∀ x, (P x).left = x.left ≫ φ := fun _ => rfl
  let Φ : (Over.mk b ⟶ G') →* (Over.mk (b ≫ f) ⟶ G) := MonoidHom.mk' P fun x y =>
    Over.OverMorphism.ext ((hP _).trans (h.2 (Over.mk b) x y (P x) (P y) rfl rfl).symm)
  have hinj : Function.Injective Φ := fun x y hxy => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg CommaMorphism.left hxy) ((Over.w x).trans (Over.w y).symm))
  let g' : Over.mk b ⟶ G' := Over.homMk (h.1.lift g.left b (Over.w g)) (h.1.lift_snd _ _ _)
  have hg' : g'.left ≫ φ = g.left := h.1.lift_fst _ _ _
  refine ⟨g', hg', hinj ?_⟩
  have : Φ g' = g := Over.OverMorphism.ext hg'
  rw [map_pow, this, hg, map_one]

theorem fullTorsion_push {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ S'}
    {N n : ℕ} (hn : n ∣ N) (ht : FullTorsion G' ξ N) : FullTorsion G (ξ ≫ f) n := by
  intro k _ i g hg
  obtain ⟨g', e, hg'⟩ := exists_lift_torsion h (spMap i ≫ ξ) _ (Category.assoc _ _ _).symm n g hg
  obtain ⟨m, rfl⟩ := hn
  obtain ⟨x, hx⟩ := ht k i g' (by rw [pow_mul, hg', one_pow])
  refine ⟨Over.homMk (x.left ≫ φ) ?_, ?_⟩
  · have := Over.w x
    simp only [Over.mk_hom] at this
    simp only [Category.assoc, Over.mk_hom, h.1.w]
    rw [← Category.assoc, this]
  · rw [← e, hx]
    exact Category.assoc _ _ _

theorem finite_of_dominates {X Y : Scheme.{0}} {Ω Ω₀ : Type} [Field Ω] [Field Ω₀] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y} (hξ : IsCptGen ξ) (f : X ⟶ Y) [IsFinite f] {i : Ω₀ →+* Ω}
    (h : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f i) : i.Finite := by
  have h1 : LocallyQuasiFinite (Spec.map (Scheme.stalkClosedPointTo ξ)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).2
      (.of_finite (RingHom.Finite.of_surjective _ hξ.bij.2))
  have h2 : LocallyQuasiFinite ξ := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    infer_instance
  have h3 : LocallyQuasiFinite (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) := by
    rw [← h]
    infer_instance
  have h4 : i.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite) (φ := CommRingCat.ofHom i)).1
      (LocallyQuasiFinite.of_comp _ ξ₀)
  algebraize [i]
  exact .of_quasiFinite

end GlobalTheory.CompanionTheory.Ar.HodgeExists
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteNormalModelOfResidueFinite

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.CompanionTheory.Relay.exists_finite_normal_model_of_residue_finite : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℤ), IsProjOver s → ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X), (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom.Finite → ∃ (n : ℕ) (x : Fin n → Ω) (M : PModel ℤ x) (π : M.X ⟶ X), Flat.NormalCpt M.ξ ∧ IsFinite π ∧ M.ξ ≫ π = ξ := by
  first | exact @PositivityTheory.HtPt.Mf.xr_norm | exact PositivityTheory.HtPt.Mf.xr_norm
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteNormalModelOfResidueFiniteStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_finite_normal_model_of_residue_finite : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℤ), IsProjOver s → ∀ (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Sp Ω ⟶ X), (Scheme.descResidueField (Scheme.stalkClosedPointTo ξ)).hom.Finite → ∃ (n : ℕ) (x : Fin n → Ω) (M : PModel ℤ x) (π : M.X ⟶ X), Flat.NormalCpt M.ξ ∧ IsFinite π ∧ M.ξ ≫ π = ξ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.exists_finite_normal_model_of_residue_finite | exact GlobalTheory.CompanionTheory.Relay.exists_finite_normal_model_of_residue_finite | (intros; apply GlobalTheory.CompanionTheory.Relay.exists_finite_normal_model_of_residue_finite <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelCoverStHolds

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem genPt_spMap_comp {X : Scheme.{0}} {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) (ξ : Sp K ⟶ X) :
    genPt (spMap i ≫ ξ) = genPt ξ := by
  unfold genPt
  show ξ ((spMap i) (closedPoint Ω)) = ξ (closedPoint K)
  congr 1
  first
  | exact Subsingleton.elim _ _
  | exact IsLocalRing.comap_closedPoint i
  | exact (IsLocalRing.PrimeSpectrum.comap_closedPoint i)

theorem finite_descResidueField_spMap_comp {X : Scheme.{0}} {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω)
    (hi : i.Finite) (ξ : Sp K ⟶ X) (hξ : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) :
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (spMap i ≫ ξ))).hom.Finite := by
  have hA : ∀ p : Sp K, (ξ.stalkMap p).hom.Finite := by
    intro p
    obtain rfl : p = closedPoint K := Subsingleton.elim _ _
    apply RingHom.Finite.of_surjective
    have e : Scheme.stalkClosedPointTo ξ =
        ξ.stalkMap (closedPoint K) ≫ (stalkClosedPointIso (CommRingCat.of K)).hom := by
      first
      | rfl
      | simp [Scheme.stalkClosedPointTo]
    intro y
    obtain ⟨a, ha⟩ := hξ ((stalkClosedPointIso (CommRingCat.of K)).hom y)
    refine ⟨a, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).hom).1
    rw [← ha, e]
    rfl
  have hB : (Scheme.stalkClosedPointTo (spMap i)).hom.Finite := by
    change (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i))).hom.Finite
    have h := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom i)
    refine RingHom.Finite.of_comp_finite
      (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec (CommRingCat.of K)).presheaf.germ ⊤
        ((Spec.map (CommRingCat.ofHom i)) (closedPoint Ω)) trivial).hom) ?_
    rw [← CommRingCat.hom_comp, Category.assoc, h, Iso.inv_hom_id_assoc]
    simpa using hi
  have hC : (Scheme.stalkClosedPointTo (spMap i ≫ ξ)).hom.Finite := by
    have e2 := Scheme.stalkClosedPointTo_comp (R := CommRingCat.of Ω) (spMap i) ξ
    have h3 := hB.comp (hA ((spMap i) (closedPoint Ω)))
    rw [← CommRingCat.hom_comp] at h3
    first
    | exact e2 ▸ h3
    | exact (congrArg (fun φ => (CommRingCat.Hom.hom φ).Finite) e2).mpr h3
    | (rw [e2]; exact h3)
  refine RingHom.Finite.of_comp_finite (f := (X.residue _).hom) ?_
  rw [← CommRingCat.hom_comp, Scheme.residue_descResidueField]
  exact hC

theorem levelCover : LevelCoverSt := by
  intro E _ _ _ H D l Xo c Y e he N hN
  obtain ⟨K, _, _, n0, x0, y0, htie, -, hgen⟩ := GlobalTheory.T.generic_point_normal_coords E H D l Xo c Y e he
  obtain ⟨Ω, _, _, z, ev, hfd, hfull⟩ := GlobalTheory.T.exists_full_level_finite_extension E H D l Xo c _ _ Y K y0 N hN
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : NumberField c.F :=
    { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hproj : IsProjOver (Y.s ≫ spMap (Int.castRingHom (𝓞 c.F))) :=
    GlobalTheory.T.projective_over_restrict_int _ Y.X Y.s Y.proj
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo (y0 ≫ Y.j)).hom := by
    obtain ⟨hg, -, -, -⟩ := htie
    obtain ⟨hb, -⟩ := hg
    exact hb.2
  have hi : (algebraMap K Ω).Finite := by
    first
    | exact RingHom.finite_algebraMap.mpr hfd
    | exact hfd
  have hfin := finite_descResidueField_spMap_comp (algebraMap K Ω) hi (y0 ≫ Y.j) hsurj
  obtain ⟨n, x, M, π, hMn, hπ, hMπ⟩ :=
    GlobalTheory.T.exists_finite_normal_model_of_residue_finite Y.X _ hproj Ω (spMap (algebraMap K Ω) ≫ (y0 ≫ Y.j)) hfin
  have hMg : IsCptGen M.ξ := by
    obtain ⟨hg, -, -, -⟩ := M.tie
    exact hg
  obtain ⟨t, hx, ev', h1, h2, h3⟩ :=
    GlobalTheory.T.full_level_generic_cover E H D l Xo c Y K Ω (algebraMap K Ω) y0 N z ev hN hfull M.X M.ξ hMg hMn π hMπ
  refine ⟨Ω, inferInstance, inferInstance, n, x, M, π, spMap (algebraMap K Ω) ≫ y0, t, hx, z, ev',
    hMn, hπ, ?_, ?_, h1, h2, h3⟩
  · show genPt (M.ξ ≫ π) = e
    rw [hMπ, genPt_spMap_comp, hgen]
  · rw [hMπ, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.XR
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelCoverStHoldsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.LevelCoverSt_holds : GlobalTheory.CompanionTheory.Ar.XR.LevelCoverSt := by
  first | exact @GlobalTheory.CompanionTheory.Ar.XR.levelCover | exact GlobalTheory.CompanionTheory.Ar.XR.levelCover | (intros; apply GlobalTheory.CompanionTheory.Ar.XR.levelCover <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteExtensionPrimes

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChgField

theorem exists_compositum (κ Ω₁ Ω' : Type) [Field κ] [Field Ω₁] [Field Ω'] (i₁ : κ →+* Ω₁) (i₂ : κ →+* Ω')
    (h : i₂.Finite) :
    ∃ (Ω : Type) (_ : Field Ω) (a : Ω₁ →+* Ω) (b : Ω' →+* Ω), a.Finite ∧ a.comp i₁ = b.comp i₂ := by
  letI := i₁.toAlgebra
  letI := i₂.toAlgebra
  haveI : Module.Finite κ Ω' := h
  haveI : Module.Finite Ω₁ (TensorProduct κ Ω₁ Ω') := inferInstance
  haveI : Nontrivial (TensorProduct κ Ω₁ Ω') := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct κ Ω₁ Ω')
  let q := Ideal.Quotient.mk m
  refine ⟨TensorProduct κ Ω₁ Ω' ⧸ m, Ideal.Quotient.field m,
    q.comp (algebraMap Ω₁ (TensorProduct κ Ω₁ Ω')),
    q.comp (Algebra.TensorProduct.includeRight : Ω' →ₐ[κ] TensorProduct κ Ω₁ Ω').toRingHom, ?_, ?_⟩
  · exact RingHom.Finite.comp (RingHom.Finite.of_surjective q Ideal.Quotient.mk_surjective)
      (RingHom.finite_algebraMap.2 inferInstance)
  · ext x
    have e : algebraMap Ω₁ (TensorProduct κ Ω₁ Ω') (i₁ x) = (1 : Ω₁) ⊗ₜ[κ] (i₂ x) := by
      have h1 : i₁ x = x • (1 : Ω₁) := by rw [Algebra.smul_def, _root_.mul_one]; rfl
      have h2 : i₂ x = x • (1 : Ω') := by rw [Algebra.smul_def, _root_.mul_one]; rfl
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, h1, h2,
        TensorProduct.smul_tmul]
    simp only [RingHom.comp_apply]
    rw [e]
    rfl

theorem exists_root (K : Type) [Field K] [CharZero K] (N : ℕ) (hN : N ≠ 0) :
    ∃ (L : Type) (_ : Field L) (j : K →+* L), j.Finite ∧ ∃ ζ : L, IsPrimitiveRoot ζ N := by
  haveI : NeZero N := ⟨hN⟩
  haveI : NeZero ((N : ℕ) : K) := ⟨Nat.cast_ne_zero.2 hN⟩
  haveI : Module.Finite K (CyclotomicField N K) := by
    first
      | exact IsCyclotomicExtension.finiteDimensional {N} K _
      | exact IsCyclotomicExtension.finite {N} K _
      | exact Polynomial.IsSplittingField.finiteDimensional _ (Polynomial.cyclotomic N K)
  exact ⟨CyclotomicField N K, inferInstance, algebraMap _ _, RingHom.finite_algebraMap.2 inferInstance,
    IsCyclotomicExtension.zeta N K _, IsCyclotomicExtension.zeta_spec N K _⟩

theorem fullTorsion_ext {X : Scheme.{0}} {Ω Ω' : Type} [Field Ω] [Field Ω'] {G : Over X} [GrpObj G]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} (j : Ω →+* Ω') {n : ℕ} (hf : FullTorsion G ξ n) :
    FullTorsion G (spMap j ≫ ξ) n := by
  intro k _ i g hg
  have hs : spMap (i.comp j) = spMap i ≫ spMap j := by
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : spMap i ≫ spMap j ≫ ξ = spMap (i.comp j) ≫ ξ := by
    rw [hs, Category.assoc]
  revert g
  rw [e]
  intro g hg
  obtain ⟨x, hx⟩ := hf k (i.comp j) g hg
  have hxw : x.left ≫ G.hom = ξ := by simpa using Over.w x
  refine ⟨Over.homMk (spMap j ≫ x.left) ?_, ?_⟩
  · simp only [Over.mk_hom, Category.assoc, hxw]
  · show g.left = spMap i ≫ spMap j ≫ x.left
    rw [hx, hs]
    exact Category.assoc _ _ _

theorem exists_factor {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (e : X)
    (h : genPt ξ = e) : ∃ i : X.residueField e →+* Ω, ξ = spMap i ≫ X.fromSpecResidueField e := by
  subst h
  exact ⟨(X.descResidueField (Scheme.stalkClosedPointTo ξ)).hom,
    ((Scheme.SpecToEquivOfField Ω X).left_inv ξ).symm⟩

theorem exists_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₁ : Type) [Field Ω₁] [CharZero Ω₁] (ξ₁ : Spec (CommRingCat.of Ω₁) ⟶ Y.X) (S : Finset ℕ), GlobalTheory.CompanionTheory.Ar.genPt ξ₁ ∈ genericPoints Y.X → (∀ p ∈ S, p.Prime) → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (i : Ω₁ →+* Ω), (letI := i.toAlgebra; FiniteDimensional Ω₁ Ω) ∧ (∀ p ∈ S, FullTorsion Y.t.G (spMap i ≫ ξ₁) (p ^ 4)) ∧ ∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 4) := by
  intro E _ _ _ H D l Xo c Y Ω₁ _ _ ξ₁ S he hS
  have hN0 : (∏ p ∈ S, p ^ 4) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun p hp => pow_ne_zero _ (hS p hp).ne_zero
  obtain ⟨Ω', _, _, n, x, M, f, y, t, m, z, ev, -, hfin, hfe, -, -, htor, -⟩ :=
    GlobalTheory.T.LevelCoverSt_holds E H D l Xo c Y _ he (∏ p ∈ S, p ^ 4) (Nat.one_le_iff_ne_zero.2 hN0)
  haveI := hfin
  obtain ⟨i₁, h₁⟩ := exists_factor ξ₁ _ rfl
  obtain ⟨i₂, h₂⟩ := exists_factor (M.ξ ≫ f) (genPt ξ₁) (by
    rw [← hfe]
    first
      | rfl
      | simp [GlobalTheory.CompanionTheory.Ar.genPt])
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates M.ξ (Y.X.fromSpecResidueField (genPt ξ₁)) f i₂ := h₂
  have hi₂ : i₂.Finite := HodgeExists.finite_of_dominates M.tie.gen f hdom
  obtain ⟨Ω₂, _, a, b, ha, hab⟩ := exists_compositum _ Ω₁ Ω' i₁ i₂ hi₂
  haveI : CharZero Ω₂ := charZero_of_injective_ringHom a.injective
  obtain ⟨Ω, _, j, hj, ζ, hζ⟩ := exists_root Ω₂ _ hN0
  haveI : CharZero Ω := charZero_of_injective_ringHom j.injective
  have hsp : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (u : R →+* R') (v : R' →+* R''),
      spMap (v.comp u) = spMap v ≫ spMap u := by
    intro R R' R'' _ _ _ u v
    simp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hpt : spMap (j.comp a) ≫ ξ₁ = spMap (j.comp b) ≫ M.ξ ≫ f := by
    rw [h₂]
    conv_lhs => rw [h₁]
    rw [← Category.assoc, ← Category.assoc, ← hsp, ← hsp, RingHom.comp_assoc, RingHom.comp_assoc, hab]
  have hdvd : ∀ p ∈ S, p ^ 4 ∣ ∏ p ∈ S, p ^ 4 := fun p hp => Finset.dvd_prod_of_mem (fun p => p ^ 4) hp
  refine ⟨Ω, inferInstance, inferInstance, j.comp a, RingHom.Finite.comp hj ha, fun p hp => ?_, fun p hp => ?_⟩
  · rw [hpt]
    exact fullTorsion_ext (j.comp b) (HodgeExists.fullTorsion_push m.cart (hdvd p hp) htor)
  · obtain ⟨d, hd⟩ := hdvd p hp
    exact ⟨ζ ^ d, hζ.pow (Nat.pos_of_ne_zero hN0) (by rw [hd, mul_comm])⟩

end GlobalTheory.CompanionTheory.Ar.ChgField
end
end
end
