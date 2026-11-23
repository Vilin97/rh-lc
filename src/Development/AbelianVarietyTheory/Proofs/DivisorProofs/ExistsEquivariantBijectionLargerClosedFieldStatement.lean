module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantLinearExtensionToAlgClosedFieldStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionOfIsPushout
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOverFiniteExt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFieldExtensionStatement
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFinsetRepresentatives
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfExpT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SymFrameClause
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivExtensionFieldBaseChange

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.FieldBaseChange

def basisOfIsExtension {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) : Module.Basis I F W :=
  Module.Basis.mk (GlobalTheory.ConstFam.linearIndependent_of_isExtension ha B.linearIndependent) (by
    have h : Submodule.span K (Set.range B) ≤
        Submodule.comap a (Submodule.span F (Set.range fun i => a (B i))) :=
      Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact Submodule.subset_span ⟨i, rfl⟩)
    rw [← ha.span, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span K (Set.range B) := B.span_eq ▸ Submodule.mem_top
    exact h hv)

theorem basisOfIsExtension_apply {K F V W : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module F W] {a : V →ₛₗ[algebraMap K F] W} (ha : IsExtension a) {I : Type}
    (B : Module.Basis I K V) (i : I) : basisOfIsExtension ha B i = a (B i) := by
  simp [basisOfIsExtension]

theorem exists_bijective_extension : ∀ (K F V V' W W' : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W'] (a : V →ₛₗ[algebraMap K F] W) (d : V' →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension a → GlobalTheory.FieldBaseChange.IsExtension d → ∀ e : V →ₗ[K] V', Function.Bijective e → ∃ e' : W →ₗ[F] W', Function.Bijective e' ∧ ∀ v, e' (a v) = d (e v) := by
  intro K F V V' W W' _ _ _ _ _ _ _ _ _ _ _ a d ha hd e he
  let B := Module.Basis.ofVectorSpace K V
  let B' := B.map (LinearEquiv.ofBijective e he)
  let C := basisOfIsExtension ha B
  let C' := basisOfIsExtension hd B'
  let E := C.equiv C' (Equiv.refl _)
  refine ⟨E.toLinearMap, E.bijective, fun v => ?_⟩
  have key : (E.toLinearMap.comp a : V →ₛₗ[algebraMap K F] W') = d.comp e := B.ext fun i => by
    have h1 : a (B i) = C i := (basisOfIsExtension_apply ha B i).symm
    have h2 : d (e (B i)) = C' i := by
      rw [basisOfIsExtension_apply hd B' i]; simp [B']
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h1, h2, E, Module.Basis.equiv_apply, Equiv.refl_apply]
  exact LinearMap.congr_fun key v

end GlobalTheory.FieldBaseChange
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivExtensionFieldBaseChangeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_linearEquiv_extension_fieldBaseChange : ∀ (K F V V' W W' : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V'] [AddCommGroup W] [Module F W] [AddCommGroup W'] [Module F W'] (a : V →ₛₗ[algebraMap K F] W) (d : V' →ₛₗ[algebraMap K F] W'), GlobalTheory.FieldBaseChange.IsExtension a → GlobalTheory.FieldBaseChange.IsExtension d → ∀ e : V →ₗ[K] V', Function.Bijective e → ∃ e' : W →ₗ[F] W', Function.Bijective e' ∧ ∀ v, e' (a v) = d (e v) := by
  first | exact @GlobalTheory.FieldBaseChange.exists_bijective_extension | exact GlobalTheory.FieldBaseChange.exists_bijective_extension | (intros; apply GlobalTheory.FieldBaseChange.exists_bijective_extension <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointFromFractionAlgClosure

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Mum.UpExt

theorem torsion_from_closure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  intro R _ _ A F _ _ _ em N hN x hx
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A N)
    (AbTorsionAnyBase.isFinite_and_flat_torsion (Sp (FractionRing R)) A.A A.isAb N hN).1
  let i : K' →ₐ[FractionRing R] Kb R := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let : Algebra K' (Kb R) := i.toRingHom.toAlgebra
  have : IsScalarTower (FractionRing R) K' (Kb R) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  have hmul : x ≫ mulN A.A N = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]
  let t0 : _ ⟶ torsion A.A N := pullback.lift x (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι A.A N = x := pullback.lift_fst _ _ _
  have hs : (TFK (R := R) F).hom = spMap (em.toRingHom.comp (algebraMap (FractionRing R) (Kb R))) :=
    congrArg spMap em.comp_algebraMap.symm
  obtain ⟨w, hw⟩ := H (Kb R) F em.toRingHom t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion A.A N).hom = (TFK (R := R) (Kb R)).hom := by
    have : Surjective (spMap em.toRingHom) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
    have : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
    apply (cancel_epi (spMap em.toRingHom)).1
    rw [← Category.assoc, hw, Over.w t0, hs, ← spMap_comp_spMap]
    rfl
  let w1 : TFK (R := R) (Kb R) ⟶ torsion A.A N := Over.homMk w hw2
  refine ⟨w1 ≫ torsion.ι A.A N, ?_, ?_⟩
  · have hc : torsion.ι A.A N ≫ mulN A.A N = toUnit _ ≫ η :=
      pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))
    have h1 : (w1 ≫ torsion.ι A.A N) ≫ mulN A.A N = toUnit _ ≫ η := by
      rw [Category.assoc, hc, ← Category.assoc, comp_toUnit]
    rwa [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, ← Hom.one_def] at h1
  · rw [← ht0, Over.comp_left, ← hw, Category.assoc]
    rfl

end GlobalTheory.Mum.UpExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointFromFractionAlgClosureStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  first | exact @GlobalTheory.Mum.UpExt.torsion_from_closure | exact GlobalTheory.Mum.UpExt.torsion_from_closure | (intros; apply GlobalTheory.Mum.UpExt.torsion_from_closure <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaFamilyOverDegenerationFamilyPullbac

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Mum.UpExt

theorem over_famPull : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] (s : Fam D E k), F₀.Over s → F₀.Over (famPull D E F GlobalTheory.globalFns_holds k s) := by
  intro R _ _ I D k F₀ E F _ _ _ _ _ _ s h α
  have hL := D.P.isLB
  have g1 : ∀ {W : Scheme.{0}} (w : W), gs (𝟙 W) w ⊤ (1 : Γ(W, ⊤)) = 1 := fun w => by
    rw [gs_eq _ w ⊤ trivial, map_one, map_one]
  have h1 := (secScal_iff_val hL _ _ _ _).1 (h α)
  refine (secScal_iff_val hL _ _ _ _).2 fun y J hJ => ?_
  have e1 : (𝟙 _ ≫ (DegPre.prB D F).left) = (famMap D E F).left ≫ (𝟙 _ ≫ (DegPre.prB D E).left) := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, famMap_snd]
  have e2 : (𝟙 _ ≫ (famMap D E F).left) = (famMap D E F).left ≫ 𝟙 _ := by
    rw [Category.id_comp, Category.comp_id]
  change _ = _ * sval (termPull D E F k α (s.s α)) _ y J
  rw [g1, _root_.one_mul, show sval (termPull D E F k α (s.s α)) (𝟙 _) y J =
      sval (s.s α) (𝟙 _ ≫ (famMap D E F).left) y J from sval_pullOver _ _ _ _ hJ, e1, e2, GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ,
    GlobalTheory.UU.IntExp.sval_comp _ _ _ _ _ hJ, h1 _ _ (fun ψ => hJ _), g1, _root_.one_mul]

end GlobalTheory.Mum.UpExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaFamilyOverDegenerationFamilyPullbacStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.integralThetaFamily_over_degenerationFamilyPullback : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (k : ℕ) (F₀ : IntFam I D k) (E F : Type) [Field E] [Field F] [Algebra (FractionRing R) E] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F] (s : Fam D E k), F₀.Over s → F₀.Over (famPull D E F GlobalTheory.globalFns_holds k s) := by
  first | exact @GlobalTheory.Mum.UpExt.over_famPull | exact GlobalTheory.Mum.UpExt.over_famPull | (intros; apply GlobalTheory.Mum.UpExt.over_famPull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantBijectionLargerClosedField

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UpExt
open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem exists_eqv_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  intro R _ _ _ hR D A N hN lab E₀ Φ hE hΦ F _ _ _ em lab' hlab
  have hN1 : 1 ≤ N := hN.pos
  haveI : CharZero R := hR.2
  letI : Algebra (Kb R) F := em.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (em.commutes x).symm
  have hem : IsScalarTower.toAlgHom (FractionRing R) (Kb R) F = em := AlgHom.ext fun _ => rfl
  let e : Fam D.toPre (Kb R) N →ₗ[Kb R] SecF A (Kb R) N :=
    { toFun := E₀
      map_add' := fun s t => SecOver.ext _ _ fun j => hE.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => SecOver.ext _ _ fun j => hE.smul c s (c • s) ((isSmul_iff _ _ _).2 rfl) j }
  obtain ⟨e', he', hc⟩ := GlobalTheory.T.exists_linearEquiv_extension_fieldBaseChange _ _ _ _ _ _ (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N) (secPull A (Kb R) F N)
    (isExtension_famPull _ _ _ GlobalTheory.globalFns_holds hN1) (isExtension_secPull A (Kb R) F N) e hE.bij
  have hq := GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D.toPre F em N hN1
  have onto : ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure R A F em N hN1 x hx
      obtain ⟨p₀, hp₀⟩ := (hE.onto y).1 hy
      obtain ⟨p', hp', -⟩ := hq.1 p₀
      refine ⟨p', Over.OverMorphism.ext ?_⟩
      rw [hlab p₀ p' hp', hp₀, hxy]
    · rintro ⟨p, rfl⟩
      obtain ⟨p₀, hp₀, -⟩ := hq.2 p
      have hy := (hE.onto (lab p₀)).2 ⟨p₀, rfl⟩
      have e1 : lab' p = baseK (Kb R) F ≫ lab p₀ := Over.OverMorphism.ext (hlab p₀ p hp₀)
      rw [e1, ← MonObj.comp_pow, hy, MonObj.comp_one]
  refine ⟨fun s => e' s, ⟨he', fun s s' s'' h j => ?_, fun c s s' h j => ?_, onto,
    fun p => ((GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hR.1 D F N hN p).1),
    fun p => GlobalTheory.SymFrameClause.exists_symLift R A F N hN (lab' p) ((onto _).2 ⟨p, rfl⟩),
    fun p w θ s s' hw hθ hs => GlobalTheory.T.equivariant_linearExtension_to_algClosedField R hR D A N hN lab E₀ hE F lab' (hem ▸ hlab) e' hc p w θ s s' hw hθ hs⟩, ?_⟩
  · obtain rfl : s'' = s + s' := fam_ext h
    rw [map_add (f := _)]
    rfl
  · obtain rfl : s' = c • s := (isSmul_iff _ _ _).1 h
    rw [map_smul]
    rfl
  · intro F₀ s hs
    obtain ⟨s₀, hs₀, -⟩ := GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ (Kb R)
    have h1 := GlobalTheory.T.integralThetaFamily_over_degenerationFamilyPullback R (maximalIdeal R) D.toPre N F₀ (Kb R) F s₀ hs₀
    obtain rfl := (GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ F).unique hs h1
    intro Z p p' hpp z J hJ
    show sval (e' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s₀)) p z J = _
    rw [hc]
    refine (sval_pullOver _ _ _ _ hJ).trans (hΦ F₀ s₀ hs₀ Z (p ≫ (secMap A (Kb R) F).left) p' ?_ z J hJ)
    rw [Category.assoc, ← hpp]
    exact congrArg (p ≫ ·) (congrArg (fun q => q.left) (secMap_snd A (Kb R) F))
end GlobalTheory.Mum.UpExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantBijectionLargerClosedFieldStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_equivariant_bijection_larger_closed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  first | exact @GlobalTheory.Mum.UpExt.exists_eqv_ext | exact GlobalTheory.Mum.UpExt.exists_eqv_ext | (intros; apply GlobalTheory.Mum.UpExt.exists_eqv_ext <;> assumption)
end
end
