module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrSt
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAbelianSchemePullbackUniversalTriple
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGPassesToPullback
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
public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartFrameTrA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermBPrim

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGPassesToPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.primitiveIsoG_passes_to_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 X1 : Scheme.{0}) (t : SAB H X0) (t' : SAB H X1) (f : X1 ⟶ X0) (mp : SABMap t' t f) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ wP : PrimTyG t, IsPrimG t wP → ∃ wP' : PrimTyG t', IsPrimG t' wP' ∧ (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) := by
  first | exact @GlobalTheory.primG_pullback | exact GlobalTheory.primG_pullback | (intros; apply GlobalTheory.primG_pullback <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGUniqueOnAbelian

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory

theorem linComb_gen_eq_of_eSec (hGF : GlobalFnsSt) {S X : Scheme.{0}} (A : Over S) [GrpObj A]
    (hA : IsAbelianScheme A) {L : LB X} (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (A.left ⟶ X)} {ε : K → ℤ} {φ' : K' → ((𝟙_ (Over S)).left ⟶ X)} {ε' : K' → ℤ}
    {a b : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (hb : b.IsGen) {r : LB.Gen (LB.LinComb L φ' ε')}
    (har : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε a (eSec A)) r)
    (hbr : LB.Gen.Corr L _ _ _ _ (LB.pullGen L φ ε b (eSec A)) r) : a = b := by
  have hcov : ∀ x : A.left, ∃ i, x ∈ (LB.LinComb L φ ε).U i := fun x => by
    choose I hI using fun k => exists_chart hL (φ k x)
    exact ⟨I, Set.mem_iInter.2 hI⟩
  obtain ⟨u, hu⟩ := ChartFrameTrA.exists_ratio_gen hcov ha hb
  suffices hu1 : u = 1 by
    cases a
    cases b
    congr 1
    funext p
    exact (hu p).trans (by rw [hu1, map_one, _root_.one_mul])
  apply ChartFrameTrA.unit_eq_one_of_eSec hGF A hA u
  have key : pullU (eSec A) ⊤ u = 1 := by
    refine unit_ext fun z hz => ?_
    choose J hJ using fun χ : (𝟙_ (Over S)).left ⟶ X => exists_chart hL (χ z)
    have hJ' : Good L z J := hJ
    have e1 := (val_pull hJ' a (eSec A) (𝟙 _)).symm.trans ((val_corr hJ' har (𝟙 _)).trans
      ((val_corr hJ' hbr (𝟙 _)).symm.trans (val_pull hJ' b (eSec A) (𝟙 _))))
    have hm := hJ'.mem φ (𝟙 _ ≫ eSec A)
    have e2 : val a (𝟙 _ ≫ eSec A) z J = gm (𝟙 _ ≫ eSec A) z ⊤ u * val b (𝟙 _ ≫ eSec A) z J :=
      (congrArg (gm _ z _) (hu _)).trans ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) (gm_res _ z _ hm _) rfl))
    have e3 : gm (𝟙 _ ≫ eSec A) z ⊤ u = 1 := mul_eq_right.1 (e2.symm.trans e1)
    exact (gm_pull (𝟙 _) (eSec A) z ⊤ trivial u).trans (e3.trans (map_one _).symm)
  exact congrArg Units.val key

theorem isPrimG_unique : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (X0 : Scheme.{0}) (t : SAB H X0), IsAbelianScheme t.G → ∀ wP wP' : PrimTyG t,
    IsPrimG t wP → IsPrimG t wP' → wP = wP' :=
  fun hGF _ _ _ _ _ _ t hA _ _ h h' =>
    linComb_gen_eq_of_eSec hGF t.G hA t.PP.isLB h.1 h'.1 h.2 h'.2

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PrimitiveIsoGUniqueOnAbelianStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.primitiveIsoG_unique_on_abelian : GlobalFnsSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0), IsAbelianScheme t.G → ∀ wP wP' : PrimTyG t, IsPrimG t wP → IsPrimG t wP' → wP = wP' := by
  first | exact @GlobalTheory.isPrimG_unique | exact GlobalTheory.isPrimG_unique | (intros; apply GlobalTheory.isPrimG_unique <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramedPointDiagonalBiextensionIsoCompati

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem chartPrimTr_holds : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartPrimTrSt Xo c := by
  intro E _ _ _ H Dw l Xo c T io y I wPT hT
  obtain ⟨wP, hP⟩ := GermB.exists_wP Xo.univ.t
  obtain ⟨w₁, hw₁, h₁⟩ := GlobalTheory.T.primitiveIsoG_passes_to_pullback E H _ _ _ _ _ I.m1 I.w1 I.rig1 wP hP
  obtain ⟨w₂, hw₂, h₂⟩ := GlobalTheory.T.primitiveIsoG_passes_to_pullback E H _ _ _ _ _ I.m2 I.w2 I.rig2 wPT hT
  have hab := GlobalTheory.isAbelianScheme_of_pullback_univ E H Dw l Xo _ _ _ I.m1
  have e : w₁ = w₂ := GlobalTheory.T.primitiveIsoG_unique_on_abelian GlobalTheory.firstFiveLaws.1.globalFns E H _ I.t' hab w₁ w₂ hw₁ hw₂
  subst e
  exact ⟨wP, (isPrim_iff wP).2 hP, w₁, hw₁.1, h₂, h₁⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IntegralFramedPointDiagonalBiextensionIsoCompatiStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.integralFramedPoint_diagonalBiextensionIso_compatible : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartPrimTrSt Xo c := by
  first | exact @GlobalTheory.chartPrimTr_holds | exact GlobalTheory.chartPrimTr_holds | (intros; apply GlobalTheory.chartPrimTr_holds <;> assumption)
end
end
