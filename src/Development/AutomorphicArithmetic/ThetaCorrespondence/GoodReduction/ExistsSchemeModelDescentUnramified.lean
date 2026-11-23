module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExtendsUnramifiedStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvr
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqOneOfPowEqOneOfCompEqOne
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
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixDescentUnramifiedDvrStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.ExistsVeryAmpleFamiliesStableMatrix
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionAbelianDvr

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbHomExtDvr

theorem existsUnique_hom_extension_abelian_dvr :
    ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G G' : Over (Sp W)) [GrpObj G] [GrpObj G'], IsAbelianScheme G → IsAbelianScheme G' → ∀ f : (Over.pullback (spMap (algebraMap W L))).obj G ⟶ (Over.pullback (spMap (algebraMap W L))).obj G', IsMonHom f → ∃! F : G ⟶ G', (Over.pullback (spMap (algebraMap W L))).map F = f := by
  intro W L _ _ _ _ _ _ G G' _ _ hG hG' f hf
  have hsm : GlobalTheory.SS.SmConn G := ⟨hG.comm, hG.smooth, by have := hG.proper; infer_instance,
    by have := hG.proper; infer_instance, hG.geomConnected⟩
  obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr W L G G' hsm
    (GlobalTheory.isSemiAbelian_of_isAbelianScheme G' hG') f hf
  have := hG.smooth
  have := hG'.proper
  have : Flat G.hom := inferInstance
  refine ⟨F, hF, fun F' hF' => ?_⟩
  exact GlobalTheory.KernelNoTorsion.eq_of_generic W L (hF'.trans hF.symm)

end GlobalTheory.AbHomExtDvr
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentIntegralStructure

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemilinTwist

variable {W K' : Type} [CommRing W] [CommRing K'] [Algebra W K']

noncomputable def restrictFun (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) : W :=
  Classical.choose (h x)

theorem algebraMap_restrictFun (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) :
    algebraMap W K' (restrictFun σ h x) = σ (algebraMap W K' x) :=
  (Classical.choose_spec (h x)).symm

noncomputable def restrictHom (hinj : Function.Injective (algebraMap W K')) (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) : W →+* W where
  toFun := restrictFun σ h
  map_one' := hinj (by simp only [algebraMap_restrictFun, map_one])
  map_mul' x y := hinj (by simp only [algebraMap_restrictFun, map_mul])
  map_zero' := hinj (by simp only [algebraMap_restrictFun, map_zero])
  map_add' x y := hinj (by simp only [algebraMap_restrictFun, map_add (f := _)])

theorem algebraMap_restrictHom (hinj : Function.Injective (algebraMap W K')) (σ : K' →+* K')
    (h : ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) (x : W) :
    σ (algebraMap W K' x) = algebraMap W K' (restrictHom hinj σ h x) :=
  (algebraMap_restrictFun σ h x).symm

theorem exists_semilinear_twist : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'] (σ : K' ≃ₐ[K] K'), (∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K')) := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ hσ A _ _ hA G _ hG e he
  have hinj : Function.Injective (algebraMap W K') := IsFractionRing.injective W K'
  let τ : W →+* W := restrictHom hinj (σ : K' →+* K') hσ
  have hτ : ∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x) :=
    algebraMap_restrictHom hinj (σ : K' →+* K') hσ
  have hsq : spMap (σ : K' →+* K') ≫ spMap (algebraMap W K') = spMap (algebraMap W K') ≫ spMap τ := by
    rw [← Spec.map_comp, ← Spec.map_comp]; congr 1; ext x; simpa using hτ x
  have hK : spMap (algebraMap K K') = spMap (σ : K' →+* K') ≫ spMap (algebraMap K K') := by
    rw [← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm
  let s := pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _)
    (spMap (σ : K' →+* K')) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm)
  have hs1 : s ≫ pullback.fst A.hom (spMap (algebraMap K K')) = pullback.fst A.hom (spMap (algebraMap K K')) :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have hs2 : s ≫ pullback.snd A.hom (spMap (algebraMap K K')) =
      pullback.snd A.hom (spMap (algebraMap K K')) ≫ spMap (σ : K' →+* K') :=
    pullback.lift_snd _ _ _
  have hA1 := isGrpPullback_pullback A (spMap (algebraMap K K'))
  have hAs : IsGrpPullback ((Over.pullback (spMap (algebraMap K K'))).obj A)
      ((Over.pullback (spMap (algebraMap K K'))).obj A) (spMap (σ : K' →+* K')) s :=
    IsGrpPullback.cancel hA1 (hA1.congr hK hs1.symm) hs2
  haveI : IsMonHom e.hom := he
  have he1 := isGrpPullback_of_iso e
  haveI : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have he2 := isGrpPullback_of_iso e.symm
  have hG1 := isGrpPullback_pullback G (spMap (algebraMap W K'))
  have h1 := (((he1.comp hAs).comp he2).comp hG1).congr
    (by rw [Category.id_comp, Category.comp_id, hsq]) rfl
  have hGτ := isGrpPullback_pullback G (spMap τ)
  have hGτK := isGrpPullback_pullback ((Over.pullback (spMap τ)).obj G) (spMap (algebraMap W K'))
  obtain ⟨e', he', he'φ⟩ := grpPullback_iso h1 (hGτK.comp hGτ)
  obtain ⟨F, hF, -⟩ := GlobalTheory.AbHomExtDvr.existsUnique_hom_extension_abelian_dvr W K' G
    ((Over.pullback (spMap τ)).obj G) hG (isAbelianScheme_pullback_obj _ G hG) e'.hom he'
  refine ⟨τ, F.left ≫ pullback.fst G.hom (spMap τ), hτ, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ spMap τ) (Over.w F)
  · have hFl : ((Over.pullback (spMap (algebraMap W K'))).map F).left ≫
        pullback.fst ((Over.pullback (spMap τ)).obj G).hom (spMap (algebraMap W K')) =
        pullback.fst G.hom (spMap (algebraMap W K')) ≫ F.left := pullback.lift_fst _ _ _
    rw [hF] at hFl
    rw [← Category.assoc, ← hFl, Category.assoc, he'φ]
    simp only [Category.assoc, Iso.symm_hom]
    rfl

end GlobalTheory.SemilinTwist
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisDescentIntegralStructureStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.galois_descent_integral_structure : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'] (σ : K' ≃ₐ[K] K'), (∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K')) := by
  first | exact @GlobalTheory.SemilinTwist.exists_semilinear_twist | exact GlobalTheory.SemilinTwist.exists_semilinear_twist | (intros; apply GlobalTheory.SemilinTwist.exists_semilinear_twist <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChangeStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.isVeryAmpleBySections_of_invertible_linear_change : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (n : ℕ) (s : Fin (n + 1) → H.Sec) (a : Matrix (Fin (n + 1)) (Fin (n + 1)) R), IsUnit a.det → H.IsLB → GlobalTheory.AbLaw.VeryAmpleBy f H s → GlobalTheory.AbLaw.VeryAmpleBy f H (fun i => ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • s j) := by
  first | exact @GlobalTheory.veryAmpleBy_linChange | exact GlobalTheory.veryAmpleBy_linChange | (intros; apply GlobalTheory.veryAmpleBy_linChange <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.ExistsCompatibleProjectiveEmbeddings

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.C3
open GlobalTheory

theorem appTop_cst {X Y : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (β : Y ⟶ X)
    (f : X ⟶ Sp R) (f' : Y ⟶ Sp R') (c : R →+* R') (h : β ≫ f = f' ≫ spMap c) (r : R) :
    β.appTop (GlobalTheory.AbLaw.cst f ⊤ r) = GlobalTheory.AbLaw.cst f' ⊤ (c r) := by
  simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, GlobalTheory.AbLaw.rs_self]
  have h1 := congrArg (fun φ : Y ⟶ Sp R => φ.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at h1
  rw [h1]
  congr 1
  have h2 := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom c))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  exact h2.symm

theorem secPull_add {X Y : Scheme.{0}} {L : LB X} (s t : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (s + t) φ = Cartier.secPull s φ + Cartier.secPull t φ :=
  GlobalTheory.LB.f_injective (funext fun i => by simp only [Cartier.secPull, GlobalTheory.LB.add_f, map_add (f := _)])

theorem secPull_smul {X Y : Scheme.{0}} {L : LB X} (c : Γ(X, ⊤)) (s : L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (c • s) φ = φ.appTop c • Cartier.secPull s φ :=
  GlobalTheory.LB.f_injective (funext fun i => by
    simp only [Cartier.secPull, GlobalTheory.LB.smul_f, map_mul, Cartier.app_resG, Cartier.resG_resG]
    rfl)

theorem secPull_sum_smul {X Y : Scheme.{0}} {L : LB X} {J : Type} (S : Finset J) (c : J → Γ(X, ⊤))
    (s : J → L.Sec) (φ : Y ⟶ X) :
    Cartier.secPull (∑ i ∈ S, c i • s i) φ = ∑ i ∈ S, φ.appTop (c i) • Cartier.secPull (s i) φ := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact GlobalTheory.LB.f_injective (funext fun i => by simp [Cartier.secPull, GlobalTheory.LB.zero_f])
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, secPull_add, secPull_smul, ih]

theorem secMaps_sum_smul {X : Scheme.{0}} {A B : LB X} (w : LB.Iso A B) {J : Type} (S : Finset J)
    (c : J → Γ(X, ⊤)) (a : J → A.Sec) (b : J → B.Sec) (h : ∀ i, Cartier.SecMaps w (a i) (b i)) :
    Cartier.SecMaps w (∑ i ∈ S, c i • a i) (∑ i ∈ S, c i • b i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro p
    simp [GlobalTheory.LB.zero_f]
  | insert x S hx ih =>
    intro p
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    simp only [GlobalTheory.LB.add_f, GlobalTheory.LB.smul_f, map_add (f := _), map_mul, ih p, h x p, Cartier.resG_resG]
    ring

theorem spMap_tower (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T]
    [Algebra R T] [IsScalarTower R S T] :
    spMap (algebraMap S T) ≫ spMap (algebraMap R S) = spMap (algebraMap R T) := by
  rw [← Spec.map_comp, IsScalarTower.algebraMap_eq R S T]
  rfl

theorem exists_compatible_projective_embeddings : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ D : Set (K' ≃ₐ[K] K'), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → (∀ σ ∈ D, ∃ (τ : W →+* W) (φ : G.left ⟶ G.left), (∀ x : W, σ (algebraMap W K' x) = algebraMap W K' (τ x)) ∧ φ ≫ G.hom = G.hom ≫ spMap τ ∧ pullback.fst G.hom (spMap (algebraMap W K')) ≫ φ = (e.hom.left ≫ pullback.map A.hom (spMap (algebraMap K K')) A.hom (spMap (algebraMap K K')) (𝟙 _) (spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext x; exact (σ.commutes x).symm) ≫ e.inv.left) ≫ pullback.fst G.hom (spMap (algebraMap W K'))) → ∃ (P : Over (Sp R)) (_ : QuasiSeparated P.hom) (iA : A.left ⟶ P.left) (hA : iA ≫ P.hom = A.hom ≫ spMap (algebraMap R K)) (_ : IsClosedImmersion (pullback.lift iA A.hom hA)) (iG : G.left ⟶ P.left) (hG : iG ≫ P.hom = G.hom ≫ spMap (algebraMap R W)) (_ : IsClosedImmersion (pullback.lift iG G.hom hG)), e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ iA = pullback.fst G.hom (spMap (algebraMap W K')) ≫ iG := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm D hD1 hD2 hres A _ _ hA G _ hG e he hφ
  obtain ⟨N, H, s, M, t, w, g, hH, hM, hs, ht, hg, hw, hD⟩ := UpperTheory.Lit.Nos.C2.exists_veryAmple_families_stable_matrix R K W K' hm D hD1 hD2 hres A hA G hG e he hφ
  obtain ⟨h, k, hh, hk⟩ := GlobalTheory.T.matrix_descent_unramified_dvr R K W K' hm D hD1 hD2 hres (N + 1) g hg hD
  have hkdet : IsUnit k.det := by
    have e1 : algebraMap K K' k.det = algebraMap W K' h.det * g.det := by
      rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]; exact congrArg Matrix.det hk
    have hu : IsUnit (algebraMap K K' k.det) := by
      rw [e1]; exact ((hh.map (algebraMap W K')).mul hg)
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at hu
    exact not_isUnit_zero hu
  have hs' := GlobalTheory.T.isVeryAmpleBySections_of_invertible_linear_change K A.left A.hom H N s k hkdet hH hs
  have ht' := GlobalTheory.T.isVeryAmpleBySections_of_invertible_linear_change W G.left G.hom M N t h hh hM ht
  obtain ⟨hs0, hsci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff _ _).1 hs'
  obtain ⟨ht0, htci⟩ := (GlobalTheory.ProjSpace.veryAmpleBy_iff _ _).1 ht'
  have hqA : (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ A.hom = (pullback.snd G.hom (spMap (algebraMap W K'))) ≫ spMap (algebraMap K K') := by
    have h1 : e.hom.left ≫ pullback.snd A.hom (spMap (algebraMap K K')) = (pullback.snd G.hom (spMap (algebraMap W K'))) := Over.w e.hom
    rw [Category.assoc, pullback.condition, ← Category.assoc, h1]
  have hqG : (pullback.fst G.hom (spMap (algebraMap W K'))) ≫ G.hom = (pullback.snd G.hom (spMap (algebraMap W K'))) ≫ spMap (algebraMap W K') := pullback.condition
  have hbase : (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ A.hom ≫ spMap (algebraMap R K) = (pullback.fst G.hom (spMap (algebraMap W K'))) ≫ G.hom ≫ spMap (algebraMap R W) := by
    rw [← Category.assoc, hqA, ← Category.assoc, hqG, Category.assoc, Category.assoc,
      spMap_tower R K K', spMap_tower R W K']
  have hsec : ∀ j, Cartier.SecMaps w (Cartier.secPull (∑ l, GlobalTheory.AbLaw.cst G.hom ⊤ (h j l) • t l) (pullback.fst G.hom (spMap (algebraMap W K'))))
      (Cartier.secPull (∑ m, GlobalTheory.AbLaw.cst A.hom ⊤ (k j m) • s m) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')))) := by
    intro j
    rw [UpperTheory.Lit.Nos.C3.secPull_sum_smul, UpperTheory.Lit.Nos.C3.secPull_sum_smul]
    have e2 : ∑ m, (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))).appTop (GlobalTheory.AbLaw.cst A.hom ⊤ (k j m)) • Cartier.secPull (s m) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) =
        ∑ l, (pullback.fst G.hom (spMap (algebraMap W K'))).appTop (GlobalTheory.AbLaw.cst G.hom ⊤ (h j l)) •
          ∑ m, GlobalTheory.AbLaw.cst (pullback.snd G.hom (spMap (algebraMap W K'))) ⊤ (g l m) • Cartier.secPull (s m) (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) := by
      simp only [UpperTheory.Lit.Nos.C3.appTop_cst (e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) A.hom (pullback.snd G.hom (spMap (algebraMap W K'))) (algebraMap K K') hqA,
        UpperTheory.Lit.Nos.C3.appTop_cst (pullback.fst G.hom (spMap (algebraMap W K'))) G.hom (pullback.snd G.hom (spMap (algebraMap W K'))) (algebraMap W K') hqG, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      have e3 := congrFun (congrFun hk j) m
      simp only [Matrix.map_apply, Matrix.mul_apply] at e3

      rw [e3, map_sum]
      simp only [map_mul]
    rw [e2]
    exact UpperTheory.Lit.Nos.C3.secMaps_sum_smul w _ _ _ _ hw
  refine ⟨Over.mk (PSpace.str R N), by show QuasiSeparated (PSpace.str R N); unfold PSpace.str; infer_instance,
    GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R K),
    by simp only [Over.mk_hom, Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc], ?_,
    GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R W),
    by simp only [Over.mk_hom, Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc], ?_, ?_⟩
  · have hci : IsClosedImmersion (GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫
        (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R K)).isoPullback.hom) := inferInstance
    change IsClosedImmersion (pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R K))
      (GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R K)) A.hom _)
    have key : pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R K))
        (GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R K)) A.hom
        (by simp only [Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc]) =
        GlobalTheory.ProjSpace.toProj A.hom _ hs0 ≫ (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R K)).isoPullback.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, GlobalTheory.ProjSpace.toProj_str]
    rw [key]
    exact hci
  · have hci : IsClosedImmersion (GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫
        (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R W)).isoPullback.hom) := inferInstance
    change IsClosedImmersion (pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R W))
      (GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R W)) G.hom _)
    have key : pullback.lift (f := PSpace.str R N) (g := spMap (algebraMap R W))
        (GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap R W)) G.hom
        (by simp only [Category.assoc, GlobalTheory.ProjSpace.baseChange_str, GlobalTheory.ProjSpace.toProj_str_assoc]) =
        GlobalTheory.ProjSpace.toProj G.hom _ ht0 ≫ (GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap R W)).isoPullback.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, Category.assoc, IsPullback.isoPullback_hom_snd, GlobalTheory.ProjSpace.toProj_str]
    rw [key]
    exact hci
  · rw [GlobalTheory.ProjSpace.toProj_baseChange, GlobalTheory.ProjSpace.toProj_baseChange, ← Category.assoc,
      ← GlobalTheory.ProjSpace.toProj_secPull hs0, ← GlobalTheory.ProjSpace.toProj_secPull ht0]
    change GlobalTheory.ProjSpace.toProj ((e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K'))) ≫ A.hom ≫ spMap (algebraMap R K)) _ _ =
      GlobalTheory.ProjSpace.toProj ((pullback.fst G.hom (spMap (algebraMap W K'))) ≫ G.hom ≫ spMap (algebraMap R W)) _ _
    rw [hbase]
    exact GlobalTheory.ProjSpace.toProj_eq_of_secMaps _ _ hsec

end UpperTheory.Lit.Nos.C3
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.GoodReduction.ExistsSchemeModelDescentUnramified

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace UpperTheory.Lit.Nos.C4
open GlobalTheory

theorem exists_scheme_model_descent_unramified : ∀ (R K W K' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] [Algebra R W] [Algebra K K'] [Algebra R K'] [IsScalarTower R W K'] [IsScalarTower R K K'], (maximalIdeal R).map (algebraMap R W) = maximalIdeal W → ∀ D : Set (K' ≃ₐ[K] K'), (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ σ ∈ D, ∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, (∀ σ ∈ D, ∀ y : W, σ (algebraMap W K' x) = algebraMap W K' y → y - x ∈ maximalIdeal W) → ∃ r : R, x - algebraMap R W r ∈ maximalIdeal W) → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (G : Over (Sp W)) [GrpObj G], IsAbelianScheme G → ∀ e : (Over.pullback (spMap (algebraMap W K'))).obj G ≅ (Over.pullback (spMap (algebraMap K K'))).obj A, IsMonHom e.hom → ∃ (X : Over (Sp R)) (a : A.left ⟶ X.left) (g : G.left ⟶ X.left), IsPullback a A.hom X.hom (spMap (algebraMap R K)) ∧ IsPullback g G.hom X.hom (spMap (algebraMap R W)) ∧ e.hom.left ≫ pullback.fst A.hom (spMap (algebraMap K K')) ≫ a = pullback.fst G.hom (spMap (algebraMap W K')) ≫ g := by
  intro R K W K' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hm D hD1 hD2 hres A _ _ hA G _ hG e he
  obtain ⟨P, hPs, iA, hA', hiA, iG, hG', hiG, hc⟩ := UpperTheory.Lit.Nos.C3.exists_compatible_projective_embeddings R K W K' hm D hD1 hD2 hres A hA G hG e he
    (fun σ _ => GlobalTheory.T.galois_descent_integral_structure R K W K' σ (hD1 σ ‹_›) A hA G hG e he)
  have := hA.proper
  have := hG.proper
  have := hG.smooth
  exact GlobalTheory.T.abelian_variety_extends_unramified R K W K' hm P hPs A inferInstance G inferInstance inferInstance e iA hA' hiA iG hG' hiG hc

end UpperTheory.Lit.Nos.C4
end
end
