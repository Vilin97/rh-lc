module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSquareGeneratorThroughSquareIso
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PGAppEqZeroIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSecPowExt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TermExpansionWeightCorrespondenceAtLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCoordSquaresCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbelianPartSectionSqEqOfThickeningPoints

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqDescend

variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem wchart_sq_le (φ : K → (Y ⟶ X)) (p : K → Fin 1 → L.ι) :
    LB.wchart (SqLB.sq L) φ p ≤ LB.wchart L φ (fun k => p k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0

theorem gm_sq_g' (f : Y ⟶ X) (y : Y) (j j' : Fin 1 → L.ι) (hj : f y ∈ (SqLB.sq L).U j)
    (hj' : f y ∈ (SqLB.sq L).U j') :
    gm f y ((SqLB.sq L).U j ⊓ (SqLB.sq L).U j') ((SqLB.sq L).g j j') =
      gm f y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ (2 : ℤ) := by
  obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨b, rfl⟩ : ∃ b, j' = fun _ => b := ⟨j' 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  exact SqLB.gm_sq_g f y (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0)

theorem gs_sub (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_zero (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem trF_sq (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y : Y) (p p' : K → Fin 1 → L.ι)
    (hy : y ∈ LB.wchart (SqLB.sq L) φ p ⊓ LB.wchart (SqLB.sq L) φ p') :
    (∏ k, gm (𝟙 Y ≫ φ k) y ((SqLB.sq L).U (p k) ⊓ (SqLB.sq L).U (p' k)) ((SqLB.sq L).g (p k) (p' k)) ^ ε k) =
      trF φ ε (𝟙 Y) y (fun k => p k 0) (fun k => p' k 0) ^ 2 := by
  simp only [trF]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gm_sq_g' (𝟙 Y ≫ φ k) y (p k) (p' k) (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k), ← zpow_mul, ← zpow_natCast,
    ← zpow_mul]
  congr 1
  push_cast
  ring

def sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb (SqLB.sq L) φ ε) where
  f := fun p => (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0)) *
    (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))
  compat := fun p p' => fn_ext fun y hy => by
    have h₁ := wchart_sq_le φ p hy.1
    have h₂ := wchart_sq_le φ p' hy.2
    have eA : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p k 0)) (s.f (fun k => p k 0)) := gs_res (𝟙 Y) y _ hy.1 _
    have eB : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p')).op).hom (s.f (fun k => p' k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p' k 0)) (s.f (fun k => p' k 0)) := gs_res (𝟙 Y) y _ hy.2 _
    have eL := (gs_res (𝟙 Y) y inf_le_left hy _).trans ((gs_mul (𝟙 Y) y _ hy.1 _ _).trans (congrArg₂ (· * ·) eA eA))
    have eR := (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val ((gm_linComb (SqLB.sq L) φ ε (𝟙 Y) y p p' hy.1 hy.2).trans (trF_sq φ ε y p p' hy))))
      ((gs_res (𝟙 Y) y inf_le_right hy _).trans ((gs_mul (𝟙 Y) y _ hy.2 _ _).trans (congrArg₂ (· * ·) eB eB))))
    refine eL.trans (Eq.trans ?_ eR.symm)
    rw [sec_trans s (𝟙 Y) y h₁ h₂, Units.val_pow_eq_pow_val]
    ring

theorem good_sq {J : (Z ⟶ X) → L.ι} {z : Z} (hJ : Good L z J) : Good (SqLB.sq L) z (fun q _ => J q) :=
  fun ψ => Set.mem_iInter.2 fun _ => hJ ψ

theorem sval_sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (sqSec s) r z (fun q _ => J q) = sval s r z J ^ 2 := by
  have h0 := hJ.mem φ r
  have hm : r z ∈ LB.wchart (SqLB.sq L) φ (fun k _ => J (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h0 k
  exact (gs_mul r z _ hm _ _).trans ((congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _)).trans
    (pow_two _).symm)

def secSub {M : LB Y} (a b : LB.Sec M) : LB.Sec M where
  f := fun i => a.f i - b.f i
  compat := fun i j => by rw [map_sub, map_sub, a.compat, b.compat, mul_sub]

theorem sval_secSub {M : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb M φ ε)) (r : Z ⟶ Y)
    (z : Z) {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) :
    sval (secSub a b) r z J = sval a r z J - sval b r z J :=
  gs_sub r z _ (hJ.mem φ r) _ _

end GlobalTheory.SqDescend


open GlobalTheory.SqDescend in
theorem GlobalTheory.sq_corr_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ (α : D.toPre.X) (α' : D'.toPre.X), (∀ κ, D'.toPre.famφB α' κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB α κ) → ∀ (s : D.toPre.SecB 2 α) (s' : D'.toPre.SecB 2 α'), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (r ≫ (U.gt e).pG.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' (r ≫ (U'.gt e).pG.left) z J' ^ 2) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' ρ z J' ^ 2 := by
  intro R _ _ _ hCN G _ _ hSA D D' A A' U U' Φ w hw hpG α α' hφ s s' hE Z ρ z J J' hJ hJ'
  classical
  have hL := D.toPre.P.isLB
  have hL' := D'.toPre.P.isLB
  have hM : (SqLB.sq D.toPre.P.L).IsLB := DVR.linComb_isLB _ hL _ _
  have hM' : (SqLB.sq D'.toPre.P.L).IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ _ _ Φ.hom.left hM hM' w hw (Fin 4)
    (D'.toPre.famφB α') (D.toPre.famφB α) (DegPre.famε 2) Φ.hom.left hφ (sqSec s)
  have hT : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
      (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' →
      sval s (r ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
        (r ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval a r z (fun q _ => J' q) := by
    intro Z r z J J' hJ hJ'
    rw [← sval_sqSec s _ z hJ]
    exact ExpTrans.sec_val w _ _ _ Φ.hom.left hφ (sqSec s) a r z (ha Z r z) (good_sq hJ) (good_sq hJ')
  have hvan : ∀ (e : ℕ) (q : Fin 4 → Fin 1 → D'.toPre.P.L.ι),
      ((U'.gt e).pG.left.app _).hom ((secSub a (sqSec s')).f q) = 0 := by
    intro e q
    refine fn_ext fun y hy => ?_
    choose J₁ hJ₁ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D.toPre.P.A.left =>
      exists_chart hL (ψ y)
    choose J₂ hJ₂ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D'.toPre.P.A.left =>
      exists_chart hL' (ψ y)
    have g₁ : Good D.toPre.P.L y J₁ := hJ₁
    have g₂ : Good D'.toPre.P.L y J₂ := hJ₂
    have e1 := hE e _ (𝟙 _) y J₁ J₂ g₁ g₂
    have e2 := hT _ (U'.gt e).pG.left y J₁ J₂ g₁ g₂
    simp only [Category.id_comp] at e1
    rw [hpG e, e1, ← sval_sqSec s' _ y g₂] at e2
    have e3 := (Units.mul_right_inj _).1 e2
    have hΔ : sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0 := by
      rw [sval_secSub a (sqSec s') _ y (good_sq g₂), e3, sub_self]
    refine (gs_pull (𝟙 _) (U'.gt e).pG.left y _ hy _).trans ?_
    rw [Category.id_comp, gs_zero]
    refine (sec_trans (secSub a (sqSec s')) (U'.gt e).pG.left y (j := q) hy ((good_sq g₂).mem _ _)).trans ?_
    change _ * sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0
    rw [hΔ, mul_zero]
  obtain ⟨hN, -, -, -⟩ := TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have := D'.toPre.P.isAb.smooth
  have := D'.toPre.P.isAb.geomConnected
  have h0 := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) hI D'.toPre.P.A).1 _
    (DVR.linComb_isLB _ hM' _ _) (secSub a (sqSec s'))
    fun e q => (ExtDiv.pG_app_eq_zero_iff (U'.gt e) _ _).1 (hvan e q)
  have key : sval a ρ z (fun q _ => J' q) = sval (sqSec s') ρ z (fun q _ => J' q) := by
    have h1 : sval (secSub a (sqSec s')) ρ z (fun q _ => J' q) = 0 := by
      show gs _ _ _ _ = 0
      exact (congrArg (gs ρ z _) (h0 _)).trans (gs_zero _ _ _)
    have h2 := sval_secSub a (sqSec s') ρ z (good_sq hJ')
    rw [h1] at h2
    exact sub_eq_zero.1 h2.symm
  rw [hT Z ρ z J J' hJ hJ', key, sval_sqSec s' ρ z hJ']
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbelianPartSectionSqEqOfThickeningPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.abelianPart_section_sq_eq_of_thickening_points : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ (α : D.toPre.X) (α' : D'.toPre.X), (∀ κ, D'.toPre.famφB α' κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB α κ) → ∀ (s : D.toPre.SecB 2 α) (s' : D'.toPre.SecB 2 α'), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (r ≫ (U.gt e).pG.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' (r ≫ (U'.gt e).pG.left) z J' ^ 2) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' ρ z J' ^ 2 := by
  first | exact @GlobalTheory.sq_corr_of_thickenings | exact GlobalTheory.sq_corr_of_thickenings | (intros; apply GlobalTheory.sq_corr_of_thickenings <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBundleSquareSectionTransportExpansion

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqTransport


open ReciprocityTheory.ChartRestriction.G.DVR in
theorem exists_transport_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen → ∀ (σ : H0 U.LG.L 2), ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') := by
  intro R _ _ _ hCN G _ _ _ D D' A A' U U' wL hwL σ
  have hR := TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  haveI : IsNoetherianRing R := hR.1
  have hL := linComb_isLB U.LG.L U.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  have hL' := linComb_isLB U'.LG.L U'.LG.isLB (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)
  let σ' : H0 U'.LG.L 2 := secOfIso σ hwL hL' hL
  obtain ⟨s, hs⟩ := exists_sec U'.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R))
    (ε' := fun _ => ((2 : ℕ) : ℤ)) (fun _ _ h => by simp only [Category.comp_id])
    (H1.SectionArithmetic.pullSec σ' (pullback.fst G.hom (jK R)))
  obtain ⟨E, hsE, -⟩ := (U'.expand 2 (by norm_num)).1 s
  obtain ⟨f', hf', -⟩ := IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D' A' G U'.toUnifPre 2 σ' s
    (SectionScalarValuation.secScal_of_sval U'.LG.isLB fun y J hJ =>
      ((hs _ _ y J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm) E hsE
  refine ⟨σ', f', hf', fun Z r z J J' hJ hJ' => ?_⟩
  have hm : r z ∈ (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)).U (fun _ => J' r) ⊓
      (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)).U (fun _ => J r) :=
    ⟨Set.mem_iInter.2 fun _ => hJ' r, Set.mem_iInter.2 fun _ => hJ r⟩
  have e := gs_secOfIso_eq wL σ hwL hL' hL (fun _ => J' r) (fun _ => J r) r z hm
  rw [sval_of σ r z J (fun _ => J r) (fun _ => by rw [Category.comp_id]),
    sval_of σ' r z J' (fun _ => J' r) (fun _ => by rw [Category.comp_id])]
  show _ = (gm r z _ (wL.s ((fun _ => J r), (fun _ => J' r)))).val * _
  have e' : gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J' r) (σ'.f fun _ => J' r) =
      ((gm r z _ (wL.s ((fun _ => J r), (fun _ => J' r))))⁻¹).val *
        gs r z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => J r) (σ.f fun _ => J r) := e
  rw [e', ← _root_.mul_assoc, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, _root_.one_mul]

end GlobalTheory.SqTransport
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBundleSquareSectionTransportExpansionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_bundleSquare_section_transport_expansion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), wL.IsGen → ∀ (σ : H0 U.LG.L 2), ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') := by
  first | exact @GlobalTheory.SqTransport.exists_transport_expansion | exact GlobalTheory.SqTransport.exists_transport_expansion | (intros; apply GlobalTheory.SqTransport.exists_transport_expansion <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TermExpansionWeightCorrespondenceAtLevelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.termExpansion_weight_correspondence_at_level : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → ∀ (σ : H0 U.LG.L 2) (σ' : H0 U'.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') → (∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι) (J' : (Z ⟶ G.left) → U'.LG.L.ι), Good U.LG.L z J → Good U'.LG.L z J' → sval σ r z J = (gv wL r z (fun _ => J r) (fun _ => J' r)).val * sval σ' r z J') → ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → ∀ α' : D'.toPre.X, sval (f (xe α')) (r ≫ (U.gt e).pG.left) z J * (val ((U.gt e).t (xe α')) r z J).val = (ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)).val * sval (f' α') (r ≫ (U'.gt e).pG.left) z J' * (val ((U'.gt e).t α') r z J').val := by
  first | exact @GlobalTheory.termMatch_at_level | exact GlobalTheory.termMatch_at_level | (intros; apply GlobalTheory.termMatch_at_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiSquareEvenTermsCorrespondTransport

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqCorr

theorem psi_sq_terms_correspond : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)) (wL : LB.Iso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen → wL.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG (maximalIdeal R) e G).left (r z) ∈ U.LG.L.U jL → (fstG (maximalIdeal R) e G).left (r z) ∈ U'.LG.L.U jL' → gw w (r ≫ (U'.gt e).pG.left) z (fun _ => jM) (fun _ => jM') * gw (U'.w e) r z jM' (fun _ => jL') ^ 2 = gw (U.w e) r z jM (fun _ => jL) ^ 2 * gv wL (r ≫ (fstG (maximalIdeal R) e G).left) z (fun _ => jL) (fun _ => jL')) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG (maximalIdeal R) e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, val ((U.gt e).t (xe x)) r z J = val ((U'.gt e).t x) r z J') → (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x)))  → ∀ (σ : H0 U.LG.L 2) (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α), (∀ e : ℕ, U.ExpandsAt e 2 σ f) → ∃ (σ' : H0 U'.LG.L 2) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ e : ℕ, U'.ExpandsAt e 2 σ' f') ∧ ∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2 := by
  intro R _ _ _ hR G _ _ hsa D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht hc σ f hE
  obtain ⟨σ', f', hE', hrel⟩ := GlobalTheory.T.exists_bundleSquare_section_transport_expansion R hR G hsa D D' A A' U U' wL hwL σ
  refine ⟨σ', f', hE', fun β Z ρ z J J' hJ hJ' => ?_⟩
  have hφ : ∀ κ, D'.toPre.famφB (2 • β) κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB (xe (2 • β)) κ :=
    PsiCompare.famφB_comp Φ.hom (hc β)
  refine GlobalTheory.T.abelianPart_section_sq_eq_of_thickening_points R hR G hsa D D' A A' U U' Φ w hw (fun e => (hlev e).1) _ _ hφ (f _) (f' _)
    (fun e Z r z J J' hJ hJ' => ?_) Z ρ z J J' hJ hJ'
  have hB := GlobalTheory.T.termExpansion_weight_correspondence_at_level R hR G hsa D D' A A' U U' Φ w wL hw hwL hΦ hlev xe ht σ σ' f f' hE hE' hrel e Z r z J J' hJ hJ' (2 • β)
  have hC := GlobalTheory.T.torus_coord_squares_correspond' R hR G hsa D D' A A' U U' Φ w hw hΦ (fun e => (hlev e).1) xe ht β (hc β) e Z r z J J' hJ hJ'
  have hP := ExpTrans.prod_fam U'.toUnifPre e 2 (fun ψ => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ ψ)) (2 • β)

  set a := sval (f (xe (2 • β))) (r ≫ (U.gt e).pG.left) z J
  set b := sval (f' (2 • β)) (r ≫ (U'.gt e).pG.left) z J'
  set T := val ((U.gt e).t (xe (2 • β))) r z J
  set T' := val ((U'.gt e).t (2 • β)) r z J'
  set O := ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left)
  set P := ∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ D'.toPre.Oφ (U'.gt e).pG (2 • β) κ) ^ Oinvε κ
  set F := ∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ
  have hP' : F * P = O ^ 2 := hP
  have key : a ^ 2 * (P * T' ^ 2).val = F.val * b ^ 2 * (P * T' ^ 2).val := by
    calc a ^ 2 * (P * T' ^ 2).val = a ^ 2 * (T ^ 2).val := by rw [hC]
      _ = (a * T.val) ^ 2 := by simp only [Units.val_pow_eq_pow_val]; ring
      _ = (O.val * b * T'.val) ^ 2 := by rw [hB]
      _ = (O ^ 2).val * b ^ 2 * (T' ^ 2).val := by simp only [Units.val_pow_eq_pow_val]; ring
      _ = (F * P).val * b ^ 2 * (T' ^ 2).val := by rw [hP']
      _ = F.val * b ^ 2 * (P * T' ^ 2).val := by simp only [Units.val_mul, Units.val_pow_eq_pow_val]; ring
  exact (Units.mul_left_inj (P * T' ^ 2)).1 key

end GlobalTheory.SqCorr
end
end
end
