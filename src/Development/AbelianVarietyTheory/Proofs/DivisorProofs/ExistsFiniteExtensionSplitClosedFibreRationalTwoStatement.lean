module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinExtTqClosedFibre
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionRationalOverFiniteExt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
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
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacks

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TwoTorsPull

theorem twoTorsRat_of_pullback : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (K' : Type) (_ : Field K') (_ : Algebra (FractionRing R) K'), Module.Finite (FractionRing R) K' ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] (ρ : R →+* R₂) (i : K' →+* FractionRing R₂), (∀ r : R, i (algebraMap (FractionRing R) K' (algebraMap R (FractionRing R) r)) = algebraMap R₂ (FractionRing R₂) (ρ r)) → ∀ (G₁ : Over (Sp R₂)) [GrpObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → TwoTorsRat G₁ := by
  intro R _ _ G _ A gen hgen
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A 2)
    (AbTorsionAnyBase.isFinite_and_flat_torsion _ A.A A.isAb 2 (by norm_num)).1
  refine ⟨K', inferInstance, inferInstance, hfin, ?_⟩
  intro R₂ _ _ ρ i hi G₁ _ β hβ F _ _ x hx
  let f : FractionRing R →+* FractionRing R₂ := i.comp (algebraMap (FractionRing R) K')
  letI : Algebra K' (FractionRing R₂) := i.toAlgebra
  letI : Algebra (FractionRing R) (FractionRing R₂) := f.toAlgebra
  haveI : IsScalarTower (FractionRing R) K' (FractionRing R₂) := IsScalarTower.of_algebraMap_eq' rfl
  let σ : FractionRing R₂ →+* F := algebraMap (FractionRing R₂) F
  have hsq : spMap f ≫ jK R = jK R₂ ≫ spMap ρ := by
    rw [jK, jK, spMap, spMap, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact hi r
  have hx2 : x ^ 2 = 1 := by rw [pow_two, hx]

  let x0 := ObjPull.pushEquiv hβ _ x
  have hx0 : x0 ^ 2 = 1 := by simp only [x0, ← map_pow, hx2, map_one]
  have hx0l : x0.left = x.left ≫ β := rfl

  let T : Over (Sp (FractionRing R)) := Over.mk (spMap σ ≫ spMap f)
  have hT : T.hom ≫ jK R = (Over.mk (spMap σ ≫ jK R₂)).hom ≫ spMap ρ := by
    show (spMap σ ≫ spMap f) ≫ jK R = (spMap σ ≫ jK R₂) ≫ spMap ρ
    rw [Category.assoc, hsq, Category.assoc]
  let e : Over.mk (T.hom ≫ jK R) ⟶ Over.mk ((Over.mk (spMap σ ≫ jK R₂)).hom ≫ spMap ρ) :=
    Over.homMk (𝟙 _) (by simpa using hT.symm)
  let x1 := preHom e x0
  have hx1 : x1 ^ 2 = 1 := by rw [← map_pow, hx0, map_one]
  have hx1l : x1.left = x0.left := by
    show (e ≫ x0).left = _
    rw [Over.comp_left]
    exact Category.id_comp _
  let hpb := isGrpPullback_pullback G (jK R)
  let x2 := (ObjPull.pushEquiv hpb T).symm x1
  have hx2' : x2 ^ 2 = 1 := by simp only [x2, ← map_pow, hx1, map_one]
  have hx2l : x2.left ≫ pullback.fst G.hom (jK R) = x1.left := ObjPull.pushEquiv_symm_left hpb T x1
  let x3 := x2 ≫ gen.hom
  have hx3 : x3 ^ 2 = 1 := by
    simp only [x3, pow_two] at hx2' ⊢
    rw [← MonObj.mul_comp, hx2', MonObj.one_comp]
  have hmul : x3 ≫ mulN A.A 2 = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx3, Hom.one_def]
  let t0 : T ⟶ torsion A.A 2 := pullback.lift x3 (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι A.A 2 = x3 := pullback.lift_fst _ _ _
  have hs : T.hom = spMap (σ.comp (algebraMap (FractionRing R) (FractionRing R₂))) := by
    show spMap σ ≫ spMap f = _
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨w, hw⟩ := H (FractionRing R₂) F σ t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion A.A 2).hom = spMap f := by
    have spec_map_field_cancel {K C : Type} [Field K] [Field C] (gam : K →+* C)
        {X : Scheme} (y y' : Sp K ⟶ X)
        (h : spMap gam ≫ y = spMap gam ≫ y') : y = y' := by
      obtain ⟨⟨p, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
      obtain ⟨⟨p', φ'⟩, rfl⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y'
      simp only [Scheme.SpecToEquivOfField_symm_apply] at h ⊢
      have e : ∀ (q : X) (ψ : X.residueField q ⟶ CommRingCat.of K),
          spMap gam ≫ (Spec.map ψ ≫ X.fromSpecResidueField q) =
            (Scheme.SpecToEquivOfField C X).symm ⟨q, ψ ≫ CommRingCat.ofHom gam⟩ := by
        intro q ψ
        simp only [Scheme.SpecToEquivOfField_symm_apply, spMap, Spec.map_comp, Category.assoc]
      rw [e, e] at h
      have h2 := (Scheme.SpecToEquivOfField C X).symm.injective h
      simp only [Sigma.mk.inj_iff] at h2
      obtain ⟨rfl, h3⟩ := h2
      have h4 : φ = φ' := by
        have h5 : φ ≫ CommRingCat.ofHom gam = φ' ≫ CommRingCat.ofHom gam := eq_of_heq h3
        ext x
        apply gam.injective
        have := congrArg (fun f => f.hom x) h5
        simpa using this
      rw [h4]
    refine spec_map_field_cancel σ _ _ ?_
    rw [← Category.assoc, hw, Over.w t0]
    rfl
  let z : Sp (FractionRing R₂) ⟶ G.left := w ≫ (torsion.ι A.A 2).left ≫ gen.inv.left ≫ pullback.fst G.hom (jK R)
  have hz : z ≫ G.hom = jK R₂ ≫ spMap ρ := by
    simp only [z, Category.assoc]
    have hgi : gen.inv.left ≫ pullback.snd G.hom (jK R) = A.A.hom := Over.w gen.inv
    rw [pullback.condition, ← Category.assoc gen.inv.left, hgi, ← Category.assoc (torsion.ι A.A 2).left,
      Over.w (torsion.ι A.A 2), ← Category.assoc w, hw2, hsq]
  let y : Over.mk (jK R₂) ⟶ G₁ := Over.homMk (hβ.1.lift z (jK R₂) hz) (hβ.1.lift_snd _ _ _)
  refine ⟨y, hβ.1.hom_ext ?_ ?_⟩
  · show x.left ≫ β = spMap σ ≫ hβ.1.lift z (jK R₂) hz ≫ β
    rw [hβ.1.lift_fst, ← hx0l, ← hx1l, ← hx2l]
    have hgh : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    simp only [z, ← Category.assoc]
    rw [hw, ← Over.comp_left, ht0]
    show x2.left ≫ pullback.fst G.hom (jK R) = ((x2.left ≫ gen.hom.left) ≫ gen.inv.left) ≫ pullback.fst G.hom (jK R)
    rw [Category.assoc x2.left, hgh, Category.comp_id]
  · show x.left ≫ G₁.hom = spMap σ ≫ hβ.1.lift z (jK R₂) hz ≫ G₁.hom
    rw [hβ.1.lift_snd]
    exact Over.w x

end GlobalTheory.TwoTorsPull
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtTwoTorsionRationalPullbacksStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finite_ext_two_torsion_rational_pullbacks : ∀ (R : Type) [CommRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G] (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (K' : Type) (_ : Field K') (_ : Algebra (FractionRing R) K'), Module.Finite (FractionRing R) K' ∧ ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] (ρ : R →+* R₂) (i : K' →+* FractionRing R₂), (∀ r : R, i (algebraMap (FractionRing R) K' (algebraMap R (FractionRing R) r)) = algebraMap R₂ (FractionRing R₂) (ρ r)) → ∀ (G₁ : Over (Sp R₂)) [GrpObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → TwoTorsRat G₁ := by
  first | exact @GlobalTheory.TwoTorsPull.twoTorsRat_of_pullback | exact GlobalTheory.TwoTorsPull.twoTorsRat_of_pullback | (intros; apply GlobalTheory.TwoTorsPull.twoTorsRat_of_pullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompleteDVRCharZeroOfFiniteInjectiveExtension

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem cDvr_of_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R → FinExt ρ → GlobalTheory.LN.CDvr R' := by
  intro R R' _ _ _ _ _ _ ρ hR hE
  obtain ⟨hdvr, -, hc0⟩ := hR
  obtain ⟨⟨hnoeth, -, hic, hcomp⟩, hinj, hfin⟩ := hE
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Module.Finite R R' := hfin
  haveI : Algebra.IsIntegral R R' := inferInstance
  haveI := hnoeth
  haveI := hic
  have hinj' : Function.Injective (algebraMap R R') := hinj
  haveI : Ring.DimensionLEOne R' := Ring.DimensionLEOne.of_isIntegral R R'
  haveI : IsDedekindDomain R' := { }
  have hnf : ¬ IsField R' := fun h =>
    IsDiscreteValuationRing.not_isField R (isField_of_isIntegral_of_isField hinj' h)
  have hdvr' : IsDiscreteValuationRing R' := ((IsDiscreteValuationRing.TFAE R' hnf).out 1 3).2 (inferInstance : IsDedekindDomain R')
  exact ⟨hdvr', hcomp, charZero_of_injective_algebraMap hinj'⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompleteDVRCharZeroOfFiniteInjectiveExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.isCompleteDVRCharZero_of_finiteInjectiveExtension : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), GlobalTheory.LN.CDvr R → FinExt ρ → GlobalTheory.LN.CDvr R' := by
  first | exact @GlobalTheory.Mum.cDvr_of_finExt | exact GlobalTheory.Mum.cDvr_of_finExt | (intros; apply GlobalTheory.Mum.cDvr_of_finExt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSplitClosedFibreRationalTwo

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem splitClosed_of_isGrpPullback_id {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G' G₁ : Over (Sp R)}
    [GrpObj G'] [GrpObj G₁] {φ : G₁.left ⟶ G'.left} (hφ : IsGrpPullback G₁ G' (𝟙 _) φ) (h : SplitClosed G') :
    SplitClosed G₁ := by
  obtain ⟨X, _, _, _, ⟨Q⟩⟩ := h
  let t := thick R (maximalIdeal R) 0
  have h2 := (isGrpPullback_pullback G₁ t).comp hφ
  have h3 := isGrpPullback_pullback G' t
  let ψ : (thickObj R (maximalIdeal R) 0 G₁).left ⟶ (thickObj R (maximalIdeal R) 0 G').left :=
    pullback.lift (pullback.fst G₁.hom t ≫ φ) (pullback.snd G₁.hom t) (by
      rw [Category.assoc, hφ.1.w, Category.comp_id, pullback.condition])
  have hc : IsGrpPullback (thickObj R (maximalIdeal R) 0 G₁) (thickObj R (maximalIdeal R) 0 G') (𝟙 _) ψ :=
    IsGrpPullback.cancel h3 (h2.congr (by rw [Category.comp_id, Category.id_comp]) (pullback.lift_fst _ _ _).symm)
      (by
        rw [Category.comp_id]
        exact pullback.lift_snd _ _ _)
  obtain ⟨Q', -⟩ := GlobalTheory.UU.exists_tq_baseChange _ _ (𝟙 _) X _ _ ψ hc Q
  exact ⟨X, inferInstance, inferInstance, inferInstance, ⟨Q'⟩⟩

noncomputable section

theorem exists_finExt_splitClosed_twoTorsRat : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R'), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → SplitClosed G₁ ∧ TwoTorsRat G₁ := by
  intro R _ _ _ hR G _ _ hG A gen hgen
  obtain ⟨K', _, _, hK'fin, H⟩ := GlobalTheory.T.exists_finite_ext_two_torsion_rational_pullbacks R G A gen hgen
  haveI : IsDiscreteValuationRing R := hR.1
  haveI : IsAdicComplete (maximalIdeal R) R := hR.2.1
  haveI : CharZero R := hR.2.2
  haveI : CharZero (FractionRing R) := (algebraMap R (FractionRing R)).charZero_iff (IsFractionRing.injective R _) |>.1 inferInstance
  obtain ⟨W, _, _, _, hWc, _, _, _, hc, hWfin, hWinj, hWloc, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension R (FractionRing R) K'
  haveI : CharZero W := (algebraMap R W).charZero_iff hWinj |>.1 inferInstance
  have hWd : GlobalTheory.LN.CDvr W := ⟨inferInstance, hWc, inferInstance⟩
  have hGW : IsSemiAbelian ((Over.pullback (spMap (algebraMap R W))).obj G) := IsSemiAbelian.pullback _ G hG
  obtain ⟨R₂, _, _, _, ρ₂, G', _, _, β', X, _, _, _, hfin₂, hpb', ⟨Q⟩⟩ :=
    GlobalTheory.Mum.exists_finExt_tq_closedFibre W ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩ _ hGW
  have hsp : spMap (ρ₂.comp (algebraMap R W)) = spMap ρ₂ ≫ spMap (algebraMap R W) := by
    rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, ρ₂.comp (algebraMap R W), GlobalTheory.T.isCompleteDVRCharZero_of_finiteInjectiveExtension W R₂ ρ₂ hWd hfin₂,
    ⟨hfin₂.1, hfin₂.2.1.comp hWinj, hfin₂.2.2.comp (RingHom.finite_algebraMap.2 hWfin)⟩, ?_⟩
  intro G₁ _ _ β hβ
  have hGWp := isGrpPullback_pullback G (spMap (algebraMap R W))
  let gam : G₁.left ⟶ ((Over.pullback (spMap (algebraMap R W))).obj G).left :=
    pullback.lift β (G₁.hom ≫ spMap ρ₂) (by rw [hβ.1.w, hsp, Category.assoc])
  have hgam : IsGrpPullback G₁ _ (spMap ρ₂) gam :=
    IsGrpPullback.cancel hGWp (hβ.congr hsp (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  obtain ⟨e, he, -⟩ := grpPullback_iso hgam hpb'
  haveI := he
  have hsplit' : SplitClosed G' := ⟨X, inferInstance, inferInstance, inferInstance, ⟨Q⟩⟩
  refine ⟨splitClosed_of_isGrpPullback_id (isGrpPullback_of_iso e) hsplit', ?_⟩
  · let j : FractionRing W →+* FractionRing R₂ :=
      IsLocalization.map (M := nonZeroDivisors W) (T := nonZeroDivisors R₂) (FractionRing R₂) ρ₂
        (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective ρ₂ hfin₂.2.1)
    let i : K' →+* FractionRing R₂ := j.comp (FractionRing.algEquiv W K').symm.toRingHom
    refine H R₂ (ρ₂.comp (algebraMap R W)) i (fun r => ?_) G₁ β hβ
    have h1 := congrArg (fun f => f r) hc
    simp only [RingHom.comp_apply] at h1
    rw [← h1]
    show j ((FractionRing.algEquiv W K').symm (algebraMap W K' (algebraMap R W r))) = _
    rw [AlgEquiv.commutes]
    exact IsLocalization.map_eq _ _

end

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSplitClosedFibreRationalTwoStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_finiteExtension_splitClosedFibre_rationalTwoTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R'), GlobalTheory.LN.CDvr R' ∧ FinExt ρ ∧ ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁] (β : G₁.left ⟶ G.left), IsGrpPullback G₁ G (spMap ρ) β → SplitClosed G₁ ∧ TwoTorsRat G₁ := by
  first | exact @GlobalTheory.Mum.exists_finExt_splitClosed_twoTorsRat | exact GlobalTheory.Mum.exists_finExt_splitClosed_twoTorsRat | (intros; apply GlobalTheory.Mum.exists_finExt_splitClosed_twoTorsRat <;> assumption)
end
end
