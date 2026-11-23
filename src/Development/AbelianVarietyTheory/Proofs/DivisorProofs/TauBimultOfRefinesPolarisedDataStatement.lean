module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLawsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.mumfordBundleIso_normalised_respects_laws : ∀ (S S' : Scheme.{0}) (B : Over S) (B' : Over S') [GrpObj B] [IsCommMonObj B] [GrpObj B'] [IsCommMonObj B'] (M : RigLB B) (M' : RigLB B') (c : CubicalStr B M) (c' : CubicalStr B' M') (f : S' ⟶ S) (β : B'.left ⟶ B.left) (β₂ : (G2 B').left ⟶ (G2 B).left) (w : LB.Iso (abelian₂ B' M'.L) ((abelian₂ B M.L).pull β₂)) (hβ : IsGrpPullback B' B f β), IsAbelianScheme B' → IsSquare β β₂ → w.IsGen → (∀ (T : Over S') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift (1 : T ⟶ B') (1 : T ⟶ B')).left z J J' = 1) → ∀ (T : Over S') (x x' y : T ⟶ B') z J J', Good M.L z J → Good M'.L z J' → lamVal w (lift x y).left z J J' = lamVal w (lift y x).left z J J' ∧ ∀ (u u' v : Over.mk (T.hom ≫ f) ⟶ B), u.left = x.left ≫ β → u'.left = x'.left ≫ β → v.left = y.left ≫ β → lamVal w (lift (x * x') y).left z J J' * cubV c' z J' x x' y = @id (T.left.presheaf.stalk z)ˣ (cubV (T := Over.mk (T.hom ≫ f)) c z J u u' v) * lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' := by
  first | exact @GlobalTheory.LamRigid.lam_iso_laws | exact GlobalTheory.LamRigid.lam_iso_laws | (intros; apply GlobalTheory.LamRigid.lam_iso_laws <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauBimultOfRefinesPolarisedData

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

theorem exists_fracSpec {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) : ∃ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ := by
  have hu : ∀ y : nonZeroDivisors R, IsUnit ((algebraMap R' (FractionRing R')).comp ρ y) := fun y => by
    refine IsUnit.mk0 _ ?_
    rw [RingHom.comp_apply, ne_eq, IsFractionRing.to_map_eq_zero_iff]
    exact (map_ne_zero_iff ρ hρ).2 (nonZeroDivisors.ne_zero y.2)
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors R) (S := FractionRing R) hu)), ?_⟩
  simp only [jK, spMap, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsLocalization.lift_eq]

theorem toUnit_left {S : Scheme.{0}} (T : Over S) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

theorem tauBimult_of_half : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R)
    (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) →
    D.TauBimult := by
  intro R _ _ R' _ _ Q ρ D e hρ h
  obtain ⟨κ, hκ⟩ := exists_fracSpec ρ hρ
  obtain ⟨β, β₂, w, hpb, hsq, hgen, hnorm, hc, hper⟩ := h
  have per : ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' → val (D.tau a b) (𝟙 _) z J' =
      lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J := by
    intro a b z J J' hJ hJ'
    have := hper κ hκ a b z J J' hJ hJ'
    rwa [show unitOn (1 : (FractionRing R')ˣ) = 1 from map_one _, map_one, _root_.mul_one] at this
  let k : Over.mk ((TK R').hom ≫ spMap ρ) ⟶ TK R := Over.homMk κ hκ
  have hQ : ∀ a a' b : Q.X, ∀ z J, Good Q.M.L z J →
      val (Q.tau (a + a') b) κ z J * @id ((TK R').left.presheaf.stalk z)ˣ
        (cubV (T := Over.mk ((TK R').hom ≫ spMap ρ)) Q.cub z J
        (k ≫ toUnit (TK R) ≫ Q.c a) (k ≫ toUnit (TK R) ≫ Q.c a') (k ≫ toUnit (TK R) ≫ Q.c b)) =
      val (Q.tau a b) κ z J * val (Q.tau a' b) κ z J := by
    intro a a' b z J hJ
    have hcorr : LB.Gen.Corr Q.M.L _ _ _ _ (LB.mulGen Q.M.L _ _ _ _ (Q.tau (a + a') b)
        (LB.pullGen Q.M.L (thφ Q.B (x3 Q.B)) thε Q.cub.t
          (lift (toUnit (TK R) ≫ Q.c a) (lift (toUnit (TK R) ≫ Q.c a') (toUnit (TK R) ≫ Q.c b))).left))
        (LB.mulGen Q.M.L _ _ _ _ (Q.tau a b) (Q.tau a' b)) := by
      refine corr_of_val Q.M.isLB fun y J hJ => ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
      refine (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)).trans ?_
      rw [Category.id_comp]
      exact Q.tau_add a a' b y J hJ
    have := (val_mul hJ _ _ _).symm.trans ((val_corr hJ hcorr κ).trans (val_mul hJ _ _ _))
    refine Eq.trans ?_ this
    exact congrArg₂ (· * ·) rfl (val_cub Q.cub k hJ _ _ _).symm
  intro a a' b
  refine corr_of_val D.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ, -⟩ := exists_good Q.M.L Q.M.isLB y (K := PEmpty) (fun i => i.elim) (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim)
  refine (val_mul hJ' _ _ _).trans (Eq.trans ?_ (val_mul hJ' _ _ _).symm)
  refine (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _)).trans ?_
  rw [Category.id_comp]
  have hx : toUnit (TK R') ≫ D.c (a + a') = (toUnit (TK R') ≫ D.c a) * (toUnit (TK R') ≫ D.c a') := by
    rw [D.c_add, padd, comp_lift_assoc, Hom.mul_def]
  have hu : ∀ χ : D.X, (k ≫ toUnit (TK R) ≫ Q.c (e χ)).left = (toUnit (TK R') ≫ D.c χ).left ≫ β := by
    intro χ
    simp only [Over.comp_left, Over.homMk_left, toUnit_left, Category.assoc, hc, k]
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ Over.Hom.left (Q.c (e χ))) hκ
  obtain ⟨-, hw⟩ := GlobalTheory.T.mumfordBundleIso_normalised_respects_laws _ _ Q.B D.P.A Q.M ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ Q.cub D.cub (spMap ρ) β β₂ w
    hpb D.P.isAb hsq hgen hnorm (TK R') (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)
    y J J' hJ hJ'
  have hw' := hw _ _ _ (hu a) (hu a') (hu b)
  rw [← hx] at hw'
  have hq := hQ (e a) (e a') (e b) y J hJ
  rw [← map_add (f := _)] at hq
  change val (D.tau (a + a') b) (𝟙 _) y J' * cubV D.cub y J' _ _ _ = _
  rw [per _ _ y J J' hJ hJ', per _ _ y J J' hJ hJ', per _ _ y J J' hJ hJ']
  calc _ = (lamVal w (lift (toUnit (TK R') ≫ D.c (a + a')) (toUnit (TK R') ≫ D.c b)).left y J J' *
        cubV D.cub y J' (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)) *
        val (Q.tau (e (a + a')) (e b)) κ y J := by ac_rfl
    _ = _ := by
      rw [hw']
      calc _ = lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left y J J' *
            lamVal w (lift (toUnit (TK R') ≫ D.c a') (toUnit (TK R') ≫ D.c b)).left y J J' *
            (val (Q.tau (e (a + a')) (e b)) κ y J * @id ((TK R').left.presheaf.stalk y)ˣ
              (cubV (T := Over.mk ((TK R').hom ≫ spMap ρ)) Q.cub y J
              (k ≫ toUnit (TK R) ≫ Q.c (e a)) (k ≫ toUnit (TK R) ≫ Q.c (e a')) (k ≫ toUnit (TK R) ≫ Q.c (e b)))) := by
            ac_rfl
        _ = _ := by rw [hq]; ac_rfl

end GlobalTheory.PolDeg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TauBimultOfRefinesPolarisedDataStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tauBimult_of_refines_polarised_data : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) → D.TauBimult := by
  first | exact @GlobalTheory.PolDeg.tauBimult_of_half | exact GlobalTheory.PolDeg.tauBimult_of_half | (intros; apply GlobalTheory.PolDeg.tauBimult_of_half <;> assumption)
end
end
