module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightOnePrimeDvrStalkStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeRangeOfStalkStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelIsBaseChangeStatement
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteProjectiveStatement
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.GroupWithZero.Submonoid.CancelMulZero
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieLatticeEqStatement
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PHeightOneIntersection
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PLatticesAgree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDescendsBaseChange

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem dualMap_comp_algebraMap (c : R →+* R') :
    (dualMap c).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp c := by
  refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap (c : R →+* R') :
    (TrivSqZeroExt.fstHom R' R' R').toRingHom.comp (dualMap c) =
      c.comp (TrivSqZeroExt.fstHom R R R).toRingHom := by
  refine RingHom.ext fun a => ?_
  simp [dualMap]

theorem dualMap_comp_epsMul (c : R →+* R') (r : R) :
    (dualMap c).comp (epsMul r) = (epsMul (c r)).comp (dualMap c) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_
  · simp [dualMap, epsMul]
  · simp [dualMap, epsMul, mul_comm]

def epsBase (c : R →+* R') (x : Sp R ⟶ S) : epsAt (spMap c ≫ x) ⟶ epsAt x :=
  Over.homMk (spMap (dualMap c)) (by
    change spMap (dualMap c) ≫ Spec.map _ ≫ x = Spec.map _ ≫ spMap c ≫ x
    simp only [spMap]
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, dualMap_comp_algebraMap])

def ptBase (c : R →+* R') (x : Sp R ⟶ S) : Over.mk (spMap c ≫ x) ⟶ Over.mk x :=
  Over.homMk (spMap c) rfl

theorem isTanAt_base (G : Over S) [GrpObj G] (c : R →+* R') (x : Sp R ⟶ S) (v : epsAt x ⟶ G)
    (hv : IsTanAt G x v) : IsTanAt G (spMap c ≫ x) (epsBase c x ≫ v) := by
  have h1 : (ptBase c x ≫ (1 : Over.mk x ⟶ G)) = 1 := MonObj.comp_one _
  have h2 : spMap c ≫ (1 : Over.mk x ⟶ G).left = (1 : Over.mk (spMap c ≫ x) ⟶ G).left := by
    rw [← h1]; rfl
  unfold IsTanAt at hv ⊢
  rw [← h2, ← hv]
  change Spec.map _ ≫ spMap (dualMap c) ≫ v.left = spMap c ≫ Spec.map _ ≫ v.left
  simp only [spMap]
  rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, fst_comp_dualMap]

theorem exists_isBaseChange (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type)
    [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E' : Type) [AddCommGroup E'] [Module R' E']
    [Module R E'] [IsScalarTower R R' E'] (M' : LieModel G (spMap (algebraMap R R') ≫ x) E') :
    ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E) (M : LieModel G x E) (j : E →ₗ[R] E'),
      IsBaseChange R' j ∧ ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := by
  obtain ⟨E, iA, iM, ⟨M⟩⟩ := lieModel_exists S G R x
  have hex : ∀ e, ∃ e', M'.pt e' = epsBase (algebraMap R R') x ≫ M.pt e :=
    fun e => M'.onto _ (isTanAt_base G _ x _ (M.tan e))
  choose f hf using hex
  have hleft : ∀ e, (M'.pt (f e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := fun e => by
    rw [hf e]; rfl
  let j : E →ₗ[R] E' :=
    { toFun := f
      map_add' := fun a b => M'.inj (by
        rw [M'.add, hf, hf, hf, M.add, MonObj.comp_mul])
      map_smul' := fun r a => M'.inj (Over.OverMorphism.ext (by
        rw [RingHom.id_apply, ← algebraMap_smul R' r (f a), M'.smul, hleft, hleft, M.smul]
        simp only [spMap]
        rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← CommRingCat.ofHom_comp, dualMap_comp_epsMul])) }
  refine ⟨E, iA, iM, M, j, GlobalTheory.T.lie_model_isBaseChange S G R R' x E E' M M' j fun e => ?_, hleft⟩
  simpa only [Category.comp_id, j, LinearMap.coe_mk, AddHom.coe_mk] using hleft e

end GlobalTheory.CompanionTheory.Ar.LieBaseChange
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelDescendsBaseChangeStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

theorem _root_.GlobalTheory.T.lie_model_descends_base_change : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (x : Sp R ⟶ S) (E' : Type) [AddCommGroup E'] [Module R' E'] [Module R E'] [IsScalarTower R R' E'] (M' : LieModel G (spMap (algebraMap R R') ≫ x) E'), ∃ (E : Type) (_ : AddCommGroup E) (_ : Module R E) (M : LieModel G x E) (j : E →ₗ[R] E'), IsBaseChange R' j ∧ ∀ e, (M'.pt (j e)).left = spMap (dualMap (algebraMap R R')) ≫ (M.pt e).left := by
  exact @GlobalTheory.CompanionTheory.Ar.LieBaseChange.exists_isBaseChange
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalRingFractionField

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

theorem exists_germ_frac {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Sp Ω ⟶ X)
    (hb : Function.Bijective (Scheme.stalkClosedPointTo ξ).hom) {y : X}
    (hs : ξ (IsLocalRing.closedPoint Ω) ⤳ y) (a : Ω) :
    ∃ f g : X.presheaf.stalk y,
      (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom g ≠ 0 ∧
      a * (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom g =
        (X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo ξ).hom f := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := y) (U := ⊤) trivial
  have hzU : ξ (IsLocalRing.closedPoint Ω) ∈ U := hs.mem_open U.isOpen hyU
  let z : U := ⟨_, hzU⟩
  letI := X.presheaf.algebra_section_stalk z
  have hl := hU.isLocalization_stalk z
  obtain ⟨s, rfl⟩ := hb.2 a
  obtain ⟨⟨f, g⟩, e⟩ := IsLocalization.surj (S := X.presheaf.stalk z.1)
    (hU.primeIdealOf z).asIdeal.primeCompl s
  have hgerm : ∀ r : Γ(X, U), (X.presheaf.stalkSpecializes hs).hom (X.presheaf.germ U y hyU r) =
      X.presheaf.germ U _ hzU r := fun r =>
    ConcreteCategory.congr_hom (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hyU hs) r
  refine ⟨X.presheaf.germ U y hyU f, X.presheaf.germ U y hyU g.1, ?_, ?_⟩
  · have hu : IsUnit (X.presheaf.germ U _ hzU g.1) :=
      IsLocalization.map_units (X.presheaf.stalk z.1) g
    have := hu.map (Scheme.stalkClosedPointTo ξ).hom
    simpa [hgerm] using this.ne_zero
  · have e' : s * X.presheaf.germ U _ hzU g.1 = X.presheaf.germ U _ hzU f := e
    have := congrArg (Scheme.stalkClosedPointTo ξ).hom e'
    simpa [hgerm] using this

theorem isFractionRing_regAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ →
    ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω := by
  intro X Ω _ ξ h p
  refine IsFractionRing.of_field (regAt ξ p) Ω fun a => ?_
  obtain ⟨f, g, hg, e⟩ := exists_germ_frac ξ h.bij (y := p.1) p.2 a
  refine ⟨⟨genMap ξ p f, f, rfl⟩, ⟨genMap ξ p g, g, rfl⟩, ?_⟩
  exact eq_div_of_mul_eq hg e

end GlobalTheory.CompanionTheory.Ar.LieStalk
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularLocalRingFractionFieldStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

theorem _root_.GlobalTheory.T.regular_local_ring_fraction_field : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt | exact GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt | (intros; apply GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieLatticeAgree

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem exists_model (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) :
    ∃ (Ep : Type) (_ : AddCommGroup Ep) (_ : Module (regAt ξ p) Ep) (Mp : LieModel G (regPt h p) Ep)
      (j : Ep →ₗ[regAt ξ p] E), IsBaseChange Ω j ∧
        ∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left := by
  obtain ⟨Ep, i1, i2, Mp, j, hb, hj⟩ := GlobalTheory.T.lie_model_descends_base_change X G (regAt ξ p) Ω (regPt h p) E
    (castPt (spMap_algebraMap_regPt h p).symm M)
  exact ⟨Ep, i1, i2, Mp, j, hb, fun e =>
    (castPt_pt_left (spMap_algebraMap_regPt h p).symm M (j e)).symm.trans (hj e)⟩

theorem lat_fin (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) :
    Module.Finite (regAt ξ p) (M.lat p) ∧ Module.Projective (regAt ξ p) (M.lat p) ∧
      Submodule.span Ω (M.lat p : Set E) = ⊤ := by
  obtain ⟨Ep, i1, i2, Mp, j, hb, hj⟩ := exists_model h G M p
  have hr := GlobalTheory.T.lie_lattice_range_of_stalk X Ω ξ h G E M p Ep Mp j hj
  obtain ⟨hf, hp⟩ := GlobalTheory.T.lie_model_finite_projective X G (regAt ξ p) (regPt h p) Ep Mp
  haveI := GlobalTheory.T.regular_local_ring_fraction_field X Ω ξ h p
  have hl : IsLocalizedModule (nonZeroDivisors (regAt ξ p)) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (regAt ξ p)) Ω j).mpr hb
  have hinj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro m hm
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (regAt ξ p)) j).1 hm
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Ep) c.2
    exact hreg (show (c : regAt ξ p) • m = (c : regAt ξ p) • 0 by rw [smul_zero]; exact hc)
  have hMeq : M.lat p = LinearMap.range j := SetLike.coe_injective (hr.trans (LinearMap.coe_range j).symm)
  let e : Ep ≃ₗ[regAt ξ p] M.lat p := (LinearEquiv.ofInjective j hinj).trans (LinearEquiv.ofEq _ _ hMeq.symm)
  refine ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, ?_⟩
  rw [eq_top_iff]
  intro v _
  refine hb.inductionOn v (motive := fun v => v ∈ Submodule.span Ω (M.lat p : Set E)) (fun m => ?_)
    (fun s n hn => Submodule.smul_mem _ s hn) (fun a b ha hb => add_mem ha hb)
  exact Submodule.subset_span (by rw [hr]; exact ⟨m, rfl⟩)

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  apply RingHom.ext
  intro a
  ext <;> simp [dualMap]

theorem lat_gen (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {p q : Cpt ξ} (hs : q.1 ⤳ p.1) :
    M.lat q = Submodule.span (regAt ξ q) (M.lat p : Set E) := by
  obtain ⟨Eq, i1, i2, Mq, jq, hbq, hjq⟩ := exists_model h G M q
  letI : Algebra (regAt ξ p) (regAt ξ q) := (regIncl hs).toAlgebra
  letI : Module (regAt ξ p) Eq := Module.compHom Eq (regIncl hs)
  haveI : IsScalarTower (regAt ξ p) (regAt ξ q) Eq := ⟨fun a b c => by
    change (regIncl hs a * b) • c = regIncl hs a • (b • c)
    rw [mul_smul]⟩
  obtain ⟨Ep, i3, i4, Mp, j, hb, hj⟩ := GlobalTheory.T.lie_model_descends_base_change X G (regAt ξ p) (regAt ξ q) (regPt h p) Eq
    (castPt (spMap_regIncl_regPt h hs).symm Mq)
  let jp : Ep →ₗ[regAt ξ p] E :=
    { toFun := fun e => jq (j e)
      map_add' := fun a b => by simp
      map_smul' := fun c e => by
        rw [map_smul]
        change jq (regIncl hs c • j e) = _
        rw [map_smul]
        rfl }
  have hjp : ∀ e, (M.pt (jp e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left := by
    intro e
    have h1 := hjq (j e)
    have h2 := (castPt_pt_left (spMap_regIncl_regPt h hs).symm Mq (j e)).symm.trans (hj e)
    have h3 : (dualMap (algebraMap (regAt ξ q) Ω)).comp (dualMap (algebraMap (regAt ξ p) (regAt ξ q))) =
        dualMap (algebraMap (regAt ξ p) Ω) := dualMap_comp _ _
    refine h1.trans ?_
    rw [h2, ← h3]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hrp := GlobalTheory.T.lie_lattice_range_of_stalk X Ω ξ h G E M p Ep Mp jp hjp
  have hrq := GlobalTheory.T.lie_lattice_range_of_stalk X Ω ξ h G E M q Eq Mq jq hjq
  have hMq : M.lat q = LinearMap.range jq := SetLike.coe_injective (hrq.trans (LinearMap.coe_range jq).symm)
  rw [hrp, hMq]
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    refine hb.inductionOn w (motive := fun w => jq w ∈ Submodule.span (regAt ξ q) (Set.range jp)) (fun m => ?_)
      (fun s n hn => by rw [map_smul]; exact Submodule.smul_mem _ s hn)
      (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    exact Submodule.subset_span ⟨m, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨e, rfl⟩
    exact ⟨j e, rfl⟩

theorem mem_localizedIn_iff (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {p q : Cpt ξ} (hs : q.1 ⤳ p.1)
    (P : PrimeSpectrum (regAt ξ p)) (hu : ∀ s : regAt ξ p, s ∉ P.asIdeal → (s : Ω)⁻¹ ∈ regAt ξ q)
    (hd : ∀ a ∈ regAt ξ q, ∃ s : regAt ξ p, s ∉ P.asIdeal ∧ (s : Ω) * a ∈ regAt ξ p) (v : E) :
    v ∈ GroundTheory.Heights₂.Heights.Model.localizedIn P.asIdeal (M.lat p) ↔ v ∈ M.lat q := by
  have hg := lat_gen h G M hs
  constructor
  · rintro ⟨s, hsP, hv⟩
    have h0 : (s : Ω) ≠ 0 := fun h0 => hsP (by
      have : s = 0 := Subtype.ext h0
      rw [this]; exact zero_mem _)
    have h1 : (s : Ω) • v ∈ M.lat q := by rw [hg]; exact Submodule.subset_span hv
    have h2 := (M.lat q).smul_mem (⟨_, hu s hsP⟩ : regAt ξ q) h1
    have h3 : (⟨_, hu s hsP⟩ : regAt ξ q) • (s : Ω) • v = v := by
      rw [Subring.smul_def, smul_smul]
      simp [h0]
    rwa [h3] at h2
  · intro hv
    rw [hg] at hv
    induction hv using Submodule.span_induction with
    | mem w hw => exact ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hw⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul a w _ hw =>
      obtain ⟨s, hsP, hsw⟩ := hw
      obtain ⟨t, htP, hta⟩ := hd a a.2
      refine ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim htP hsP, ?_⟩
      have e : (t * s) • a • w = (⟨_, hta⟩ : regAt ξ p) • s • w := by
        simp only [Subring.smul_def, smul_smul, Subring.coe_mul]
        congr 1
        ring
      rw [e]
      exact (M.lat p).smul_mem _ hsw

theorem lat_eq_of_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (M' : LieModel G' ξ E), (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left) → IsLocallyNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → M.lat = M'.lat := by
  intro X Ω _ ξ hξ G G' _ _ GΩ _ φ φ' hS hS' hP hP' E _ _ M M' hv hN hnorm
  funext p
  haveI := hS.comm
  haveI := hS.smooth
  haveI := hS'.comm
  haveI := hS'.smooth
  haveI := GlobalTheory.T.regular_local_ring_fraction_field X Ω ξ hξ p
  obtain ⟨hdom, hic⟩ := hnorm p.1
  haveI : IsDomain (regAt ξ p) := inferInstance
  haveI : IsNoetherianRing (X.presheaf.stalk p.1) := inferInstance
  haveI : IsNoetherianRing (regAt ξ p) := isNoetherianRing_of_ringEquiv _ (regIso hξ p)
  haveI : IsIntegrallyClosed (regAt ξ p) := IsIntegrallyClosed.of_equiv (regIso hξ p)
  haveI : FiniteDimensional Ω E := (GlobalTheory.T.lie_model_finite_projective X G Ω ξ E M).1
  obtain ⟨f1, p1, s1⟩ := lat_fin hξ G M p
  obtain ⟨f2, p2, s2⟩ := lat_fin hξ G' M' p
  refine GroundTheory.Heights₂.Heights.Model.LatticesAgree.proof GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.proof (regAt ξ p) Ω E (M.lat p) (M'.lat p) f1 p1 f2 p2 s1 s2 ?_
  intro P hP1
  obtain ⟨q, hs, hdvr, hu, hd⟩ := GlobalTheory.T.height_one_prime_dvr_stalk X Ω ξ hξ hN hnorm p P hP1
  have hq := GlobalTheory.T.semiabelian_lie_lattice_eq X Ω ξ hξ G G' GΩ φ φ' hS hS' hP hP' E M M' hv q hdvr
  ext v
  rw [mem_localizedIn_iff hξ G M hs P hu hd, mem_localizedIn_iff hξ G' M' hs P hu hd, hq]

end GlobalTheory.CompanionTheory.Ar.LieStalk
end
end
end
