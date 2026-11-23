module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.BilLActRight
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.FlatGenInjective
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
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
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanPf
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.EigDirInt

-- Source module: Formalism.SharpRestriction.Divisibility.GeneratorPowers.FrTanDir

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FrTan

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_char {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
    (T : CDVR) (io : c.F →+* T.Fr) (σ : E →+* ℂ) :
    ∃ χ : 𝓞 E →+* T.V, ∀ a : 𝓞 E, algebraMap T.V T.Fr (χ a) = io (embK c σ a) := by
  have hint : ∀ a : 𝓞 E, ∃ z : T.V, algebraMap T.V T.Fr z = io (embK c σ a) := by
    intro a
    have h1 : IsIntegral T.V ((io.comp (embK c σ)) a) :=
      IsIntegral.map_of_comp_eq (Int.castRingHom T.V) (io.comp (embK c σ)) (RingHom.ext_int _ _)
        (RingOfIntegers.isIntegral a)
    exact IsIntegrallyClosed.isIntegral_iff.1 h1
  choose χ hχ using hint
  refine ⟨{ toFun := χ, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hχ⟩ <;>
    intros <;> apply IsFractionRing.injective T.V T.Fr <;> simp [hχ]

end Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersActIntegralChartEigenDirections

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartAct

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth
  GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart GlobalTheory.LawLog

theorem logOf_eq {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ} (G : Germ.FGLaw k d) (i : Fin d) :
    GlobalTheory.FormalLog.logOf G i = ReciprocityTheory.ChartRestriction.G.TB.LogPf.logOf G i := rfl

theorem subst_act_log {k O : Type} [CommRing k] [Algebra ℚ k] [CommRing O] {d : ℕ} (G : Germ.FGLaw k d)
    (A : Germ.OAct O G) (a : O) (b : Fin d) :
    subst (fun i => subst (oneVar k d) (A.act a i)) (subst (oneVar k d) (GlobalTheory.FormalLog.logOf G b)) =
      ∑ j, coeff (Finsupp.single ((0 : Fin 1), j) 1) (A.act a b) •
        (subst (oneVar k d) (GlobalTheory.FormalLog.logOf G j) : MvPowerSeries (Fin d) k) := by

  rw [subst_oneVar _ cc_oneVar _ (A.const a), logOf_eq, GlobalTheory.TwistCheck.log_act, ← coe_substAlgHom hs_oneVar, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← smul_eq_C_mul, map_smul]
  rfl

theorem isIntHom_actX_and_eigen (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR)
    (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (a : 𝓞 E) :
    IsIntHom (fgl Ch X) (fgl Ch X) (actX Ch X a) (tanX Ch X a) ∧
      ∀ ℓ : Lt1 Dw, (tanX Ch X a).mulVec (lieVec Ch X ℓ) = embX io X ℓ.1 a • lieVec Ch X ℓ := by
  refine ⟨⟨fun b => ?_, fun b α => ?_, fun b => ?_⟩, fun ℓ => ?_⟩
  · refine constantCoeff_subst_eq_zero hs_oneVar cc_oneVar ?_
    rw [constantCoeff_map, (GlobalTheory.IntChartCheck.const_zero Ch).2 a b, map_zero]
  · have e : actX Ch X a b = map (jX X) (subst (oneVar T.V _) (Ch.actT a b)) := by
      rw [actX, map_subst hs_oneVar]
      congr 1
      funext q
      simp [oneVar]
    rw [e, coeff_map]
    exact isIntV_jX X _
  · let _ := io.toAlgebra
    let A : Germ.OAct (𝓞 E) (lawX Ch X) := GlobalTheory.FBMap.mapAct X.ιF Ch.ch.B.A
    have hA : ∀ i, A.act a i = map (jX X) (Ch.actT a i) := fun i => by
      show map X.ιF (Ch.ch.B.A.act a i) = _
      rw [Ch.gen.1.2.1 a i, jX, map_comp]; rfl
    have h := subst_act_log (lawX Ch X) A a b
    simp only [hA, coeff_map] at h
    exact h
  · obtain ⟨χ, hχ⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.FrTanDir.exists_char c T io ℓ.1
    have h := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD.eigDir_int Xo c T io y Ch ℓ a (χ a) (hχ a)
    have hz : embX io X ℓ.1 a = jX X (χ a) := by
      rw [jX, RingHom.comp_apply, hχ]; rfl
    funext i
    have h2 := congrArg (jX X) (congrFun h i)

    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, map_sum, map_mul, Pi.smul_apply, smul_eq_mul] at h2
    rw [hz]
    simpa only [Matrix.mulVec, dotProduct, tanX, lieVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul] using h2

end GlobalTheory.ChartAct
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersActIntegralChartEigenDirectionsStatement

section

@[expose] public section

open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

theorem _root_.GlobalTheory.T.integers_act_integralChart_eigenDirections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (X : ValExt T p) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y), ∀ a : 𝓞 E, IsIntHom (fgl Ch X) (fgl Ch X) (actX Ch X a) (tanX Ch X a) ∧ ∀ ℓ : Lt1 Dw, (tanX Ch X a).mulVec (lieVec Ch X ℓ) = embX io X ℓ.1 a • lieVec Ch X ℓ := by
  first | exact @GlobalTheory.ChartAct.isIntHom_actX_and_eigen | exact GlobalTheory.ChartAct.isIntHom_actX_and_eigen | (intros; apply GlobalTheory.ChartAct.isIntHom_actX_and_eigen <;> assumption)
end
end
