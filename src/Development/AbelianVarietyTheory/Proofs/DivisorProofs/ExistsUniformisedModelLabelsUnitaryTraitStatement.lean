module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionCompleteDvrPadicAlgCl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitThroughModuliGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicMemRangeCompleteDvrPadicAlgCl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBallEqOfIntegralDvr
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ActCommOfClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueFractionRingOfPsiCoord
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionLatticeMovesByRingActionCompleteDVRStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UTorsClosed

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitFiniteExtensionClassicalPoint

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.UTraitExtLab

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → ∃ (T' : UTrait Xo cf) (ι' : FractionRing T'.V →+* PadicAlgCl p) (yK : ratHull S.R →+* FractionRing T'.V) (e : T'.P.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X) (k : ℕ), (∀ x, ‖ι' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V (FractionRing T'.V))) ∧ ι'.comp yK = y₁ ∧ spMap yK ≫ u' = T'.y ∧ ‖ι (algebraMap T.V _ T.ϖ)‖ = ‖ι' (algebraMap T'.V _ T'.ϖ)‖ ^ k ∧ ∀ a b, T'.be a b = (k : ℤ) * T.be (e a) (e b) := by
  intro E _ _ _ H Dw l Xo cf o Ω _ _ _ _ S u' p _ y₁ T ι hι hy
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (o := o) (Ω := Ω)
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  haveI : Algebra.FiniteType ℤ S.R := Algebra.FiniteType.trans (S := o) inferInstance inferInstance
  haveI : IsDiscreteValuationRing T.V := T.cdvr.1
  haveI hTc : IsAdicComplete (maximalIdeal T.V) T.V := T.cdvr.2.1
  haveI : CharZero T.V := T.cdvr.2.2
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p T.V hTc ι hι
  obtain ⟨W, _, _, _, hWc, _, fV, fK, κ, hfV, hfVl, -, hfK, hκι, hκ, hy₀⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p T.V hTc ι hι hQ S.R (y₁.comp (toRat S.R))
  have hy₁ : ∀ a, y₁ a ∈ κ.range := fun a => by
    obtain ⟨n, hn, ha⟩ := mem_ratHull.1 a.2
    obtain ⟨x, hx⟩ := hy₀ ⟨_, ha⟩
    have h0 : (n : PadicAlgCl p) ≠ 0 := Int.cast_ne_zero.2 hn
    have h1 : toRat S.R ⟨_, ha⟩ = (n : ratHull S.R) * a := Subtype.ext rfl
    rw [RingHom.comp_apply, h1, map_mul, map_intCast] at hx
    refine ⟨(n : FractionRing W)⁻¹ * x, ?_⟩
    rw [map_mul, map_inv₀, map_intCast, hx, inv_mul_cancel_left₀ h0]
  have hbase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T', f, gK, hf, hfl, hff, hgK, hTy⟩ :=
    GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo cf W hbase inferInstance (spMap fK ≫ T.y)
  haveI : IsDiscreteValuationRing T'.V := T'.cdvr.1
  haveI hTc' : IsAdicComplete (maximalIdeal T'.V) T'.V := T'.cdvr.2.1
  haveI : CharZero T'.V := T'.cdvr.2.2
  letI : Algebra (FractionRing W) (FractionRing T'.V) := gK.toAlgebra
  letI : Algebra W T'.V := f.toAlgebra
  haveI : Module.Finite W T'.V := hff
  haveI : Algebra.IsIntegral W T'.V := Algebra.IsIntegral.of_finite W T'.V
  haveI : IsLocalHom (algebraMap W T'.V) := hfl
  have hcomp : (algebraMap (FractionRing W) (FractionRing T'.V)).comp (algebraMap W (FractionRing W)) =
      (algebraMap T'.V (FractionRing T'.V)).comp (algebraMap W T'.V) := RingHom.ext hgK
  have hI : ∀ a : T'.V, _root_.IsIntegral (FractionRing W) (algebraMap T'.V (FractionRing T'.V) a) := fun a =>
    IsIntegral.map_of_comp_eq (algebraMap W (FractionRing W)) (algebraMap T'.V (FractionRing T'.V)) hcomp
      (Algebra.IsIntegral.isIntegral a)
  haveI : Algebra.IsAlgebraic (FractionRing W) (FractionRing T'.V) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := T'.V) x
    rw [div_eq_mul_inv]
    exact (hI a).isAlgebraic.mul (hI b).isAlgebraic.inv⟩
  letI : Algebra (FractionRing W) (PadicAlgCl p) := κ.toAlgebra
  let ιA : FractionRing T'.V →ₐ[FractionRing W] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ι' : FractionRing T'.V →+* PadicAlgCl p := ιA
  have hι'κ : ι'.comp gK = κ := ιA.comp_algebraMap
  have hint := GlobalTheory.unitBall_eq_of_integral_dvr p W T'.V hf κ ι' (fun v => by
    show ι' (algebraMap T'.V (FractionRing T'.V) (f v)) = _
    rw [← hgK]
    exact congrArg (fun h : FractionRing W →+* PadicAlgCl p => h (algebraMap W (FractionRing W) v)) hι'κ) hκ
  have hιc : ι'.comp (gK.comp fK) = ι := by rw [← RingHom.comp_assoc, hι'κ, hκι]

  have hr : ∀ a, y₁ a ∈ ι'.range := fun a => by
    obtain ⟨x, hx⟩ := hy₁ a
    exact ⟨gK x, by rw [← hx, ← hι'κ]; rfl⟩
  let eι : FractionRing T'.V ≃+* ι'.range := RingEquiv.ofBijective ι'.rangeRestrict
    ⟨fun a b hab => ι'.injective (congrArg Subtype.val hab), ι'.rangeRestrict_surjective⟩
  let yK : ratHull S.R →+* FractionRing T'.V := eι.symm.toRingHom.comp (y₁.codRestrict ι'.range hr)
  have hyK : ι'.comp yK = y₁ := RingHom.ext fun a =>
    congrArg Subtype.val (eι.apply_symm_apply (y₁.codRestrict ι'.range hr a))

  have hne : f (fV T.ϖ) ≠ 0 := fun h => T.irr.ne_zero (hfV (hf (by rw [h, map_zero, map_zero])))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T'.irr
  have hbase' : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, hTc'⟩, inferInstance⟩
  haveI : IsLocalHom (f.comp fV) := by
    haveI : IsLocalHom f := hfl
    haveI : IsLocalHom fV := hfVl
    exact RingHom.isLocalHom_comp f fV
  obtain ⟨e₀, he₀⟩ := GlobalTheory.UPoinc.uTraitUniqSt_holds E H Dw l Xo cf T T' T'.V (f.comp fV) (RingHom.id _) (gK.comp fK)
    (RingHom.id _) hbase' inferInstance (hf.comp hfV) Function.injective_id inferInstance inferInstance
    (fun a => by simp only [RingHom.comp_apply, hfK, hgK]) (fun a => rfl)
    (by
      rw [hTy, spMap_comp_ringHom, Category.assoc]
      rw [show spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ from Spec.map_id _, Category.id_comp])
    T'.ϖ m 1 T'.irr hm (by rw [pow_one, RingHom.id_apply])
  refine ⟨T', ι', yK, e₀.symm, m, hint, hyK, ?_, ?_, ?_⟩
  · haveI : Epi (spMap ι') := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (spMap ι'), ← Category.assoc, ← spMap_comp_ringHom, hyK, hy, hTy, ← hιc, spMap_comp_ringHom,
      spMap_comp_ringHom, Category.assoc, Category.assoc]
  · obtain ⟨u, hu⟩ := hm
    have hunit : ∀ w : T'.Vˣ, ‖ι' (algebraMap T'.V _ (w : T'.V))‖ = 1 := fun w => by
      have h1 := (hint _).2 ⟨(w : T'.V), rfl⟩
      have h2 := (hint _).2 ⟨((w⁻¹ : T'.Vˣ) : T'.V), rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (w : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (w : T'.V))),
        norm_nonneg (ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V)))]
    have e1 : ι (algebraMap T.V _ T.ϖ) = ι' (algebraMap T'.V _ (f (fV T.ϖ))) := by
      rw [← hιc, RingHom.comp_apply, RingHom.comp_apply, hfK, hgK]
    have e2 : f (fV T.ϖ) = T'.ϖ ^ m * ((u⁻¹ : T'.Vˣ) : T'.V) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e1, e2, map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]
  · intro a b
    have h := he₀ (e₀.symm a) (e₀.symm b)
    simp only [LinearEquiv.apply_symm_apply, Nat.cast_one, one_mul] at h
    exact h.symm

end GlobalTheory.UTraitExtLab
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitFiniteExtensionClassicalPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unitaryTrait_finiteExtension_classicalPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → ∃ (T' : UTrait Xo cf) (ι' : FractionRing T'.V →+* PadicAlgCl p) (yK : ratHull S.R →+* FractionRing T'.V) (e : T'.P.D.toPre.X ≃ₗ[𝓞 E] T.P.D.toPre.X) (k : ℕ), (∀ x, ‖ι' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V (FractionRing T'.V))) ∧ ι'.comp yK = y₁ ∧ spMap yK ≫ u' = T'.y ∧ ‖ι (algebraMap T.V _ T.ϖ)‖ = ‖ι' (algebraMap T'.V _ T'.ϖ)‖ ^ k ∧ ∀ a b, T'.be a b = (k : ℤ) * T.be (e a) (e b) := by
  first | exact @GlobalTheory.UTraitExtLab.main | exact GlobalTheory.UTraitExtLab.main | (intros; apply GlobalTheory.UTraitExtLab.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitPullbackThetaSystem

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.TraitPullAct

theorem mono_spMap_toRat {o Ω F : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field F] [CharZero F] (R : Subalgebra o Ω)
    (s : Sp (ratHull R) ⟶ Sp F) : Mono (spMap (toRat R)) := by
  haveI : CharZero Ω :=
    (RingHom.charZero_iff ((ratHull R).val.toRingHom.comp (Spec.preimage s).hom).injective).1 inferInstance
  letI := (toRat R).toAlgebra
  haveI := isLocalization_ratHull R
  haveI : IsPreimmersion (spMap (toRat R)) :=
    IsPreimmersion.of_isLocalization (Algebra.algebraMapSubmonoid R (nonZeroDivisors ℤ))
  exact SurjectiveOnStalks.mono_of_injective (IsPreimmersion.isEmbedding _).injective

theorem exists_pull_univ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} (T : UTrait Xo c) :
    ∃ ψ : T.P.A.A.left ⟶ Xo.univ.t.G.left, IsGrpPullback T.P.A.A Xo.univ.t.G (T.y ≫ pullback.fst _ _) ψ ∧
      LBIso T.P.A.L (Xo.univ.t.PP.L.pull ψ) ∧
      ∀ a : 𝓞 E, (T.P.oA.act a).left ≫ ψ = ψ ≫ (Xo.univ.t.act.act a).left := by
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  have hm := T.P.U.gen_hom
  haveI : IsMonHom T.P.U.gen.symm.hom := inferInstanceAs (IsMonHom T.P.U.gen.inv)
  have hgen : IsGrpPullback T.P.A.A T.t.G (jK T.V) (T.P.U.gen.inv.left ≫ pullback.fst T.t.G.hom (jK T.V)) :=
    ((isGrpPullback_of_iso T.P.U.gen.symm).comp (isGrpPullback_pullback T.t.G (jK T.V))).congr (Category.id_comp _) rfl
  obtain ⟨e, he, he₁⟩ := grpPullback_iso hgen m₁.cart
  haveI := he
  refine ⟨e.hom.left ≫ m₂.cm.F, ((isGrpPullback_of_iso e).comp m₂.cart).congr (Category.id_comp _) rfl, ?_, fun a => ?_⟩
  · have hext : LBIso (T.t.PP.L.pull (pullback.fst T.t.G.hom (jK T.V))) (T.P.A.L.pull T.P.U.gen.hom.left) := by
      obtain ⟨w, hw⟩ := T.P.U.ext
      have hb := T.P.bundle
      exact LBIso.symm (hb ▸ ⟨w, hw⟩)
    have s1 := GlobalTheory.TripleTheta.lbIso_inv T.P.U.gen hext
    have s2 := (GlobalTheory.GenSpread.lbIso_pull_pull T.t.PP.isLB (a := pullback.fst T.t.G.hom (jK T.V))
      T.P.U.gen.inv.left rfl).symm
    have s3 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.TripleTheta.lbIso_of_sabMap m₁) e.hom.left he₁.symm
    have s4 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso (GlobalTheory.TripleTheta.lbIso_of_sabMap m₂) e.hom.left rfl
    exact LBIso.trans T.P.A.isLB (pull_isLB (pull_isLB T.t.PP.isLB _) _) (pull_isLB Xo.univ.t.PP.isLB _) s1
      (LBIso.trans (pull_isLB (pull_isLB T.t.PP.isLB _) _) (pull_isLB T.t.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) s2
      (LBIso.trans (pull_isLB T.t.PP.isLB _) (pull_isLB tK.PP.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) (LBIso.symm s3) s4))
  · letI := H.starRing
    have h0 := T.P.lin.ext a
    have h1 : T.P.oA.act a ≫ T.P.U.gen.inv = T.P.U.gen.inv ≫ (Over.pullback (jK T.V)).map (T.t.act.act a) := by
      rw [Iso.comp_inv_eq, Category.assoc, eq_comm, Iso.inv_comp_eq]
      exact h0
    have h2 : ((Over.pullback (jK T.V)).map (T.t.act.act a)).left ≫ pullback.fst T.t.G.hom (jK T.V) =
        pullback.fst T.t.G.hom (jK T.V) ≫ (T.t.act.act a).left := pullback.lift_fst _ _ _
    have h3 : (T.P.oA.act a).left ≫ e.hom.left = e.hom.left ≫ (tK.act.act a).left := by
      apply m₁.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, m₁.act a, ← Category.assoc e.hom.left, he₁, ← Category.assoc,
          ← Over.comp_left, h1, Over.comp_left, Category.assoc, h2, Category.assoc]
      · rw [← Over.comp_left, ← Over.comp_left, Over.w, Over.w]
    rw [← Category.assoc, h3, Category.assoc, m₂.act a, Category.assoc]

theorem exists_pull_act : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (T : UTrait Xo cf) (yK : ratHull S.R →+* FractionRing T.V), spMap yK ≫ u' = T.y → ∃ φ : T.P.A.A.left ⟶ ρ.P.A.left, IsGrpPullback T.P.A.A ρ.P.A (spMap (yK.comp (toRat S.R))) φ ∧ LBIso T.P.A.L (ρ.P.L.pull φ) ∧ ∀ (Y : Over (Sp (FractionRing T.V))) (x x' : Y ⟶ T.P.A.A) (w w' : Y.left ⟶ G.left) (a : 𝓞 E), w ≫ α = x.left ≫ φ → w' ≫ α = x'.left ≫ φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → x' = x ≫ T.P.oA.act a := by
  intro E _ _ _ H Dw l Xo cf o Ω _ _ _ S ρ u' G _ α β hα hβ hL T yK hy
  obtain ⟨ψ, hψ, hψL, hψa⟩ := exists_pull_univ T
  have e₀ : T.y ≫ pullback.fst _ _ = spMap yK ≫ u' ≫ pullback.fst _ _ := by rw [← hy, Category.assoc]
  have w₀ : ψ ≫ Xo.univ.t.G.hom = (T.P.A.A.hom ≫ spMap yK) ≫ u' ≫ pullback.fst _ _ := by
    rw [Category.assoc, ← e₀]; exact hψ.1.w
  have e₁ := hβ.1.lift_fst _ _ w₀
  have hγ := hβ.cancel (hψ.congr e₀ e₁.symm) (hβ.1.lift_snd _ _ w₀)
  generalize hβ.1.lift _ _ w₀ = γ at e₁ hγ
  refine ⟨γ ≫ α, (hγ.comp hα).congr (by rw [← Spec.map_comp]; rfl) rfl, ?_, fun Y x x' w w' a hw hw' h => ?_⟩
  · exact LBIso.trans T.P.A.isLB (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB ρ.P.isLB _) hψL
      (GlobalTheory.GenSpread.lbIso_pull_comp γ rfl e₁.symm hL).symm
  · haveI := mono_spMap_toRat S.R (u' ≫ pullback.snd _ _)
    haveI : Mono α := ⟨fun f g hfg => hα.1.hom_ext hfg ((cancel_mono (spMap (toRat S.R))).1 (by
      rw [Category.assoc, Category.assoc, ← hα.1.w, ← Category.assoc, hfg, Category.assoc]))⟩
    obtain rfl : w = x.left ≫ γ := (cancel_mono α).1 (hw.trans (Category.assoc _ _ _).symm)
    obtain rfl : w' = x'.left ≫ γ := (cancel_mono α).1 (hw'.trans (Category.assoc _ _ _).symm)
    apply Over.OverMorphism.ext
    apply hψ.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hψa a, ← e₁]
      simpa only [Category.assoc] using h
    · rw [Over.w, Over.w]

end GlobalTheory.UPoinc.TraitPullAct
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryTraitPullbackThetaSystemStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_unitaryTrait_pullback_thetaSystem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (T : UTrait Xo cf) (yK : ratHull S.R →+* FractionRing T.V), spMap yK ≫ u' = T.y → ∃ φ : T.P.A.A.left ⟶ ρ.P.A.left, IsGrpPullback T.P.A.A ρ.P.A (spMap (yK.comp (toRat S.R))) φ ∧ LBIso T.P.A.L (ρ.P.L.pull φ) ∧ ∀ (Y : Over (Sp (FractionRing T.V))) (x x' : Y ⟶ T.P.A.A) (w w' : Y.left ⟶ G.left) (a : 𝓞 E), w ≫ α = x.left ≫ φ → w' ≫ α = x'.left ≫ φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → x' = x ≫ T.P.oA.act a := by
  first | exact @GlobalTheory.UPoinc.TraitPullAct.exists_pull_act | exact GlobalTheory.UPoinc.TraitPullAct.exists_pull_act | (intros; apply GlobalTheory.UPoinc.TraitPullAct.exists_pull_act <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedModelLabelsUnitaryTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc.UTraitLab

theorem q_eq_of_isMonomial : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (lb : u.Lab) (ϖ : u.V) (be : LinearMap.BilinForm ℤ u.D.toPre.X), ϖ ≠ 0 → IsMonomial u.D.toPre ![ϖ] ![be] → ∀ χ, lb.q χ = -Real.log ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖ * (be χ χ : ℝ) / 2 := by
  intro o Ω _ _ _ S ρ p _ y₀ u lb ϖ be hϖ hmono χ
  obtain ⟨v, n, hn, hc⟩ := hmono χ
  obtain ⟨jc, hjc, hval⟩ := GlobalTheory.Poinc.valF_psi_of_psiCoord u.V u.D.toPre χ _ hc
  have hq := lb.q_eq χ jc hjc
  rw [hval] at hq
  simp only [Fin.prod_univ_one, Matrix.cons_val_zero] at hq
  have hunit : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ = 1 := by
    have h1 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ ≤ 1 := (u.norm_le _).2 ⟨_, rfl⟩
    have h2 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V))‖ ≤ 1 :=
      (u.norm_le _).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))‖ *
        ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ (v : u.V))),
      norm_nonneg (algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V _ ((v⁻¹ : u.Vˣ) : u.V)))]
  rw [map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hq
  set a := ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖ with ha
  have hapos : 0 < a := by
    rw [ha, norm_pos_iff]
    intro h0
    have h1 : algebraMap u.V (FractionRing u.V) ϖ = 0 :=
      (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (by rw [h0, map_zero])
    exact hϖ (IsFractionRing.injective u.V (FractionRing u.V) (by rw [h1, map_zero]))
  have hl : -lb.q χ = (n 0 : ℝ) * Real.log a := by
    rw [← Real.log_pow, hq, Real.log_exp]
  have hb : (be χ χ : ℝ) = 2 * (n 0 : ℝ) := by
    have := hn 0
    simp only [Matrix.cons_val_zero] at this
    rw [this]; push_cast; ring
  rw [hb]
  linarith

end GlobalTheory.UPoinc.UTraitLab

namespace GlobalTheory.UPoinc


open GlobalTheory.UPoinc.UTraitLab in
theorem uTraitLabels : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₁ (toRat S.R (algebraMap o S.R a))‖ ≤ 1) → ∃ (u : ρ.UTest p (y₁.comp (toRat S.R))) (lb : u.Lab) (j : u.D.toPre.X ≃+ T.P.D.toPre.X), (∀ χ, lb.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (T.be (j χ) (j χ) : ℝ) / 2) ∧ ∀ (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w w' : Sp (PadicAlgCl p) ⟶ G.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ α = x.left ≫ u.φ → w' ≫ α = x'.left ≫ u.φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → CongMod m (j pk'.y) (a • j pk.y) := by
  intro E _ _ _ H Dw hpq l Xo cf o Ω _ _ _ _ S ρ u' G _ α β hα hβ hL p _ y₁ T ι hι hsp hint
  obtain ⟨T', ι', yK, e, k, hι', hfac, hy', hϖ, hbe⟩ := GlobalTheory.T.exists_unitaryTrait_finiteExtension_classicalPoint E H Dw l Xo cf o Ω S u' p y₁ T ι hι hsp
  obtain ⟨φ, cart, lb, hact⟩ := GlobalTheory.T.exists_unitaryTrait_pullback_thetaSystem E H Dw l Xo cf o Ω S ρ u' G inferInstance α β hα hβ hL T' yK hy'
  haveI : IsDiscreteValuationRing T'.V := T'.cdvr.1
  letI : Algebra (FractionRing T'.V) (PadicAlgCl p) := ι'.toAlgebra
  let u : ρ.UTest p (y₁.comp (toRat S.R)) :=
    { V := T'.V, complete := T'.cdvr.2.1, norm_le := hι', yK := yK.comp (toRat S.R),
      fac := by rw [← RingHom.comp_assoc, RingHom.algebraMap_toAlgebra, hfac],
      A := T'.P.A, φ := φ, cart := cart, lb := lb, G := T'.t.G, semi := T'.t.semi, D := T'.P.D, U := T'.P.U }
  obtain ⟨lab⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p _ u
    hint
  refine ⟨u, lab, e.toAddEquiv, ?_, ?_⟩
  · intro χ
    have hq := q_eq_of_isMonomial o Ω S ρ p _ u lab T'.ϖ T'.be T'.irr.ne_zero T'.mono χ
    rw [hq]
    change -Real.log ‖ι' (algebraMap T'.V _ T'.ϖ)‖ * ((T'.be χ χ : ℤ) : ℝ) / 2 =
      -Real.log ‖ι (algebraMap T.V _ T.ϖ)‖ * ((T.be (e χ) (e χ) : ℤ) : ℝ) / 2
    rw [hϖ, Real.log_pow, hbe χ χ]
    push_cast
    ring
  · intro m a pk pk' x x' w w' hm h1 h2 hw hw' hww
    have hx : x' = x ≫ T'.P.oA.act a := hact _ x x' w w' a hw hw' hww
    obtain ⟨z, hz⟩ := GlobalTheory.T.torsionLattice_moves_by_ringAction_completeDVR E H T'.V T'.cdvr T'.t T'.P (PadicAlgCl p) m a pk pk' x x' hm h1 h2 hx
    exact ⟨e z, by simp [hz, map_add (f := _), map_nsmul]⟩

end GlobalTheory.UPoinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedModelLabelsUnitaryTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_uniformisedModel_labels_unitaryTrait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (u' : Sp (ratHull S.R) ⟶ Xo.XF cf) (G : Over (Sp (ratHull S.R))) (_ : GrpObj G) (α : G.left ⟶ ρ.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ.P.A (spMap (toRat S.R)) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∀ (p : ℕ) [Fact p.Prime] (y₁ : ratHull S.R →+* PadicAlgCl p) (T : UTrait Xo cf) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₁ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₁ (toRat S.R (algebraMap o S.R a))‖ ≤ 1) → ∃ (u : ρ.UTest p (y₁.comp (toRat S.R))) (lb : u.Lab) (j : u.D.toPre.X ≃+ T.P.D.toPre.X), (∀ χ, lb.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * (T.be (j χ) (j χ) : ℝ) / 2) ∧ ∀ (m : ℕ) (a : 𝓞 E) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (w w' : Sp (PadicAlgCl p) ⟶ G.left), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → w ≫ α = x.left ≫ u.φ → w' ≫ α = x'.left ≫ u.φ → w' ≫ β = w ≫ β ≫ (Xo.univ.t.act.act a).left → CongMod m (j pk'.y) (a • j pk.y) := by
  first | exact @GlobalTheory.UPoinc.uTraitLabels | exact GlobalTheory.UPoinc.uTraitLabels | (intros; apply GlobalTheory.UPoinc.uTraitLabels <;> assumption)
end
end
