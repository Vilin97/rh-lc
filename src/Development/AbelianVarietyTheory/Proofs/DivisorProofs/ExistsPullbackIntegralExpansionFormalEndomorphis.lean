module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumTwistedSectionFamilyTendsToZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedIotaGenerator
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordEndRatioDescends
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedExpansionAdicSumsAdmissibleBaseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationOfAdicSumTermwiseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationPullbackOfIntegralThetaFunctionalStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTwistedIotaGeneratorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_normalisedTwistedIotaGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ α : D.toPre.X, ∃ u : LB.Gen (IotaLB D.toPre a α (h' α)), IsIota u := by
  first | exact @GlobalTheory.TwFam.exists_iota | exact GlobalTheory.TwFam.exists_iota | (intros; apply GlobalTheory.TwFam.exists_iota <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTwistedSectionVanishing

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem formEq_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (a : D.P.A ⟶ D.P.A) (k : ℕ) (α δ : D.X) :
    FormEq (Sum.elim (fun i => a.left ≫ D.famφB α i) (Sum.elim (D.Oφ (𝟙 D.P.A) δ) (D.Oφ a α)))
      (Sum.elim (DegPre.famε k) (Sum.elim Oε Oinvε)) (tφ D a δ) (tε 0 k) := by
  intro U _ h
  have e₁ : a.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c α)).left = (padd D.P.A a (toUnit _ ≫ D.c α)).left := by
    rw [← Over.comp_left, padd, padd, ← Category.assoc, comp_lift, Category.comp_id, ← Category.assoc, comp_toUnit]
  have e₂ : a.left ≫ (toUnit D.P.A ≫ D.c α).left = (toUnit D.P.A ≫ D.c α).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  have e₃ : a.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (toUnit D.P.A ≫ η[D.P.A]).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, DegPre.famφB,
    DegPre.Oφ, tφ, tε, DegPre.famε, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_succ, e₁, e₂, e₃,
    Category.comp_id, Over.id_left]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_one]
  module

theorem exists_isPullT : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (k : ℕ) (α δ : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α δ)) (f : D.toPre.SecB k α), u.IsGen → ∃ s : SecT D.toPre a 0 k δ, IsPullT u f s ∧ ∀ e, VanMod (maximalIdeal R) f e → Van (maximalIdeal R) s e := by
  intro R _ _ _ _ D a k α δ u f hu
  obtain ⟨s, hs⟩ := exists_sec D.toPre.P.isLB (formEq_pull D.toPre a k α δ) (pullMulSec f a.left u hu)
  have hp : IsPullT u f s := fun Z x z J hJ => (hs Z x z J hJ).trans (sval_pullMulSec f a.left u hu x z hJ)
  refine ⟨s, hp, fun e hb Z x z J hJ => ?_⟩
  obtain ⟨h, hh⟩ : ∃ h : Z ⟶ pullback D.toPre.P.A.hom (thick R (maximalIdeal R) e),
      h ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
        (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ a.left :=
    ⟨pullback.lift _ (x ≫ pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) e)) (by
      rw [Category.assoc, Over.w, Category.assoc, Category.assoc, pullback.condition]), pullback.lift_fst _ _ _⟩
  have z₁ : sval f ((x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)) ≫ a.left) z J = 0 := by
    rw [← hh]
    have hm := hJ.mem (D.toPre.famφB α) (h ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e))
    exact (gs_pull h _ z _ hm _).symm.trans ((congrArg (gs h z _) (hb _)).trans (DVR.gs_zero h z _ hm))
  rw [hp Z _ z J hJ, z₁, zero_mul]

end GlobalTheory.TwFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackTwistedSectionVanishingStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.exists_pullbackTwistedSection_vanishing : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A), ∀ (k : ℕ) (α δ : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α δ)) (f : D.toPre.SecB k α), u.IsGen → ∃ s : SecT D.toPre a 0 k δ, IsPullT u f s ∧ ∀ e, VanMod (maximalIdeal R) f e → Van (maximalIdeal R) s e := by
  first | exact @GlobalTheory.TwFam.exists_isPullT | exact GlobalTheory.TwFam.exists_isPullT | (intros; apply GlobalTheory.TwFam.exists_isPullT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalEndomorphismPullsTorusCoordinateNormalised

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem coord_of_formalEnd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))), IsIota u → ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J), Good D.toPre.P.L z J → val ((U.gt e).t α) (x ≫ (b e).left) z J = val ((U.gt e).t (h' α)) x z J * val u (x ≫ (U.gt e).pG.left) z J := by
  intro R _ _ _ _ D a a' h h' hE A G _ _ _ U b ⟨hb, _, hq, ht⟩ α u ⟨hu, hu1⟩ e Z x z J hJ
  obtain ⟨t, ht, hi⟩ := ht e
  have := hb e
  have := (U.gt e).q_hom
  obtain ⟨v, hv, vv⟩ := GlobalTheory.gtCoord_end_ratio_descends R (maximalIdeal R) D.toPre e G (U.gt e) (b e) a h' t
    (hb e) ht hi (hq e) α
  have hA : IsAbelianScheme (thickObj R (maximalIdeal R) e D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  have key := gen_unique D.toPre.P.isLB (thickObj R (maximalIdeal R) e D.toPre.P.A).hom
    (η[thickObj R (maximalIdeal R) e D.toPre.P.A]).left (Over.w _) (GlobalTheory.globalFns_holds _ _ hA).2 hv
    (DVR.pullGen_isGen _ _ _ _ hu (pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e)))
    (fun y J hJ => by
      have k := vv _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
        thickObj R (maximalIdeal R) e G).left y J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶
          thickObj R (maximalIdeal R) e D.toPre.P.A) = η[thickObj R (maximalIdeal R) e D.toPre.P.A] := by
        simp [Hom.one_def]
      rw [o] at k
      exact k.symm.trans ((hu1 _ (thick R (maximalIdeal R) e) y J hJ).symm.trans
        ((congrArg (fun p => val u p y J)
          (UnitValue.eSec_pullback_fst (thick R (maximalIdeal R) e) D.toPre.P.A).symm).trans
          (val_pull hJ _ _ _).symm)))
  refine (vv Z x z J hJ).trans (congrArg (_ * ·) ((key Z _ z J hJ).trans ((val_pull hJ _ _ _).trans ?_)))
  exact congrArg (fun p => val u p z J) (Category.assoc _ _ _)

end GlobalTheory.TwFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalEndomorphismPullsTorusCoordinateNormalisedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.formalEndomorphism_pulls_torusCoordinate_normalisedGenerator : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (α : D.toPre.X) (u : LB.Gen (IotaLB D.toPre a α (h' α))), IsIota u → ∀ (e : ℕ) (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J), Good D.toPre.P.L z J → val ((U.gt e).t α) (x ≫ (b e).left) z J = val ((U.gt e).t (h' α)) x z J * val u (x ≫ (U.gt e).pG.left) z J := by
  first | exact @GlobalTheory.TwFam.coord_of_formalEnd | exact GlobalTheory.TwFam.coord_of_formalEnd | (intros; apply GlobalTheory.TwFam.coord_of_formalEnd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionPullbackFormalEndomorphismTermwise

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem texp_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k e : ℕ) (σ : H0 U.LG.L k) (f : ∀ α, D.toPre.SecB k α) (u : ∀ α, LB.Gen (IotaLB D.toPre a α (h' α))) (s : ∀ α, SecT D.toPre a 0 k (h' α)) (τ : SecE U.toUnifPre (b e) 0 k), U.ExpandsAt e k σ f → (∀ α, IsIota (u α)) → (∀ α, IsPullT (u α) (f α) (s α)) → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') → TExp U.toUnifPre τ s := by
  intro R _ _ _ hR D a a' h h' hE A G _ _ hG U b hb k e σ f u s τ hσ hu hs hτ S hS Z x z J J' hJ hJ'
  classical
  obtain ⟨S₀, hS₀⟩ := DVR.expandsAt_val U.toUnifPre e k σ f hσ
  have hp : (U.gt e).pG.left = (U.gt e).q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) := rfl
  have hc : (b e).left ≫ (U.gt e).pG.left = (U.gt e).pG.left ≫ a.left := by
    have h₁ := congrArg (fun m => m.left) (hb.2.2.1 e)
    have h₂ : ((Over.pullback (thick R (maximalIdeal R) e)).map a).left ≫
        pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) =
        pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) e) ≫ a.left := pullback.lift_fst _ _ _
    rw [hp]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))
  have hx : (x ≫ (b e).left) ≫ (U.gt e).pG.left = (x ≫ (U.gt e).pG.left) ≫ a.left := by
    rw [Category.assoc, hc, Category.assoc]
  obtain ⟨z₀, e₀⟩ := hS₀ Z (x ≫ (b e).left) z J hJ
  have e₁ := e₀ (J' (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left)) (hJ' (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left))
  have term : ∀ α, sval (f α) ((x ≫ (b e).left) ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t α) (x ≫ (b e).left) z J).val =
      sval (s α) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (h' α)) x z J).val := fun α => by
    rw [hs α Z _ z J hJ, GlobalTheory.T.formalEndomorphism_pulls_torusCoordinate_normalisedGenerator R hR D a a' h h' hE A G hG U b hb α (u α) (hu α) e Z x z J hJ, hx, Units.val_mul]
    ring
  have l : evalE U.toUnifPre τ x z J J' = ∑ α ∈ S₀, sval (s α) (x ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (h' α)) x z J).val := by
    refine Eq.trans ?_ (e₁.trans (Finset.sum_congr rfl fun α _ => term α))
    rw [evalE, hτ Z x z J' hJ', zpow_zero, _root_.one_mul, zpow_natCast, Category.assoc, Category.assoc,
      sval_of σ _ z J' (fun _ => J' (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left))
        (fun _ => congrArg J' (Category.comp_id _))]
    rfl
  rw [l]
  refine (Finset.sum_subset (Finset.subset_union_left (s₂ := S)) fun α _ hα => ?_).trans
    (Finset.sum_subset (Finset.subset_union_right (s₁ := S₀)) fun α _ hα => ?_).symm
  · rw [← term α, z₀ α hα, zero_mul]
  · have := hS α hα Z (x ≫ (U.gt e).q.left) z J hJ
    rw [hp, ← Category.assoc, this, zero_mul]

end GlobalTheory.TwFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionPullbackFormalEndomorphismTermwiseStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

theorem _root_.GlobalTheory.T.expansion_pullback_formal_endomorphism_termwise : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k e : ℕ) (σ : H0 U.LG.L k) (f : ∀ α, D.toPre.SecB k α) (u : ∀ α, LB.Gen (IotaLB D.toPre a α (h' α))) (s : ∀ α, SecT D.toPre a 0 k (h' α)) (τ : SecE U.toUnifPre (b e) 0 k), U.ExpandsAt e k σ f → (∀ α, IsIota (u α)) → (∀ α, IsPullT (u α) (f α) (s α)) → (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') → TExp U.toUnifPre τ s := by
  first | exact @GlobalTheory.TwFam.texp_pull | exact GlobalTheory.TwFam.texp_pull | (intros; apply GlobalTheory.TwFam.texp_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackIntegralExpansionFormalEndomorphis

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFam

theorem exists_pull_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G), ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (k : ℕ) (σ : H0 U.LG.L k) (f : IntFam (maximalIdeal R) D.toPre k), (∀ e, U.ExpandsAt e k σ f.f) → ∃ ρ : ∀ β, SecT D.toPre a 0 k β, Small (maximalIdeal R) (w := id) ρ ∧ TFE h h' ρ ∧ ∀ e, ∃ τ : SecE U.toUnifPre (b e) 0 k, (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' → sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J') ∧ TExp U.toUnifPre τ (w := id) ρ := by
  intro R _ _ _ hR D a a' h h' hE A G _ _ hG U b hb k σ f hσ
  choose u hu using GlobalTheory.T.exists_normalisedTwistedIotaGenerator R hR D a a' h h' hE
  choose s hs hv using fun α => GlobalTheory.T.exists_pullbackTwistedSection_vanishing R hR D a k α (h' α) (u α) (f.f α) (hu α).1
  have hsm : Small (maximalIdeal R) (w := fun α => h' α) s := fun e =>
    (f.small e).subset fun α hα hf => hα (hv α e hf)
  obtain ⟨ρ, hρ, hρs⟩ := GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero R hR D a 0 k _ (fun α => h' α) s hsm
  refine ⟨ρ, hρs, GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise R hR D a a' h h' hE 0 k _ (fun α => h' α) s ρ
    (fun mu => Equiv.addRight (k • h mu)) hsm hρ (fun mu i => by simp [shift])
    (fun mu i => GlobalTheory.T.twistedRelation_pullback_of_integralThetaFunctionalEquation R hR D a a' h h' hE k f mu i _ _ _ _ (hu _) (hu _) (hs _) (hs _)), fun e => ?_⟩
  have hL : U.LG.L.IsLB := U.LG.isLB
  have h1 : (LB.oneGen U.LG.L (Y := (thickObj R (maximalIdeal R) e G).left)).IsGen := fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm
  obtain ⟨τ, hτ⟩ := exists_sec hL (K' := Fin 2)
    (φ' := ![(fstG (maximalIdeal R) e G).left, (b e).left ≫ (fstG (maximalIdeal R) e G).left]) (ε' := ![(0 : ℤ), (k : ℤ)])
    (fun V _ g => by simp [Fintype.prod_sum_type, Fin.prod_univ_two])
    (pullMulSec σ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (LB.oneGen U.LG.L) h1)
  have key : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J'), Good U.LG.L z J' →
      sval τ x z J' = sval σ (x ≫ (b e).left ≫ (fstG (maximalIdeal R) e G).left) z J' := fun Z x z J hJ => by
    rw [hτ Z x z J hJ, sval_pullMulSec _ _ _ _ _ _ hJ, val_one, Units.val_one, _root_.mul_one]
  exact ⟨τ, key, GlobalTheory.T.twistedExpansion_adicSums_admissibleBase R hR D a A G hG U e (b e) 0 k τ _ (fun α => h' α) s ρ hsm hρ
    (GlobalTheory.T.expansion_pullback_formal_endomorphism_termwise R hR D a a' h h' hE A G hG U b hb k e σ f.f u s τ (hσ e) hu hs key)⟩

end GlobalTheory.TwFam
end
end
