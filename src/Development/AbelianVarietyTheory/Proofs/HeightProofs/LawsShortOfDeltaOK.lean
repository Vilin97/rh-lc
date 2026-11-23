module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartIndependenceUnconditional
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.BetaExistsOfNeOne
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePoints
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeries
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ShortThetaSeriesDominantWeightIsCuspFormStatement
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitCOfFiniteCharacter
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CoreArithmeticGroupContainsPrincipalCongruenceStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts

-- Source module: Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormsLeSpanShortThetaSeriesStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

theorem _root_.GlobalTheory.T.cuspForms_le_span_shortThetaSeries : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r) (σ : c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ) → 1 ≤ r → l.A = 1 → (∀ k k', ((U σ).X k).Gm = ((U σ).X k').Gm ∧ ((U σ).X k).ξ0 = ((U σ).X k').ξ0) → (∀ k, HasPrinc ((U σ).X k) l.M) → (∀ a n, Dom a n → ∀ k, ChiOne ((U σ).X k) (Formalism.L2.PjFree.laU (U σ) a n k)) → ∀ (nab : NabV Xo c) (bad nV : ℕ) (dδ : ∀ n, DeltaDat Xo c n), 0 < bad → (∀ n, (dδ n).IsLev ∧ (∃ _ : StarRing (𝓞 E), IsNab (dδ n).Xo₂ (dδ n).c₂ (dδ n).nab₂) ∧ UnitC (dδ n) ∧ ¬ 3 ∣ (dδ n).pd ∧ (Dw.p + Dw.q ≤ n → ∃ ph ψ x₀, (dδ n).PhiPin ph ψ x₀) ∧ ∀ a, Dom a n → ShortValTot Xo c nab bad nV a n (dδ n)) → SpanningAtDominantWeight Xo c nab bad nV (Formalism.L2.PjFree.cusp Xo c U) dδ := by
  first | exact @GlobalTheory.cusp_le_span_shortGen | exact GlobalTheory.cusp_le_span_shortGen | (intros; apply GlobalTheory.cusp_le_span_shortGen <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCharacter

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.RootOfUnityFn

theorem evR_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (m : ℕ) :
    evR Xo c (f ^ m) y = evR Xo c f y ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact evalAt_one _ _ y h
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact evalAt_mul _ _ _ _ y

theorem exists_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n) (m : ℕ), 0 < m → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → d.cδ ^ m = 1 → (∀ y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom), ∃ a : d.c₂.F, evR d.Xo₂ d.c₂ d.cδ y = algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom) a) → ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls) (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false := by
  intro E _ _ _ H Dw l Xo c n d m hm hsec hpow hval
  choose a ha using hval
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : IsReduced (CAt d.c₂.F.val.toRingHom) := (inferInstance : IsReduced ℂ)
  have hinj : Function.Injective (algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom)) :=
    (d.c₂.F.val.toRingHom).injective
  have hroot : ∀ y, a y ^ m = 1 := by
    intro y
    have hT := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ _ y
    have h1 := evR_pow d.Xo₂ d.c₂ d.cδ y hT m
    have h0 := evR_pow d.Xo₂ d.c₂ d.cδ y hT 0
    rw [pow_zero, pow_zero] at h0
    rw [hpow, h0, ha, ← map_pow] at h1
    exact hinj (by rw [map_one]; exact h1.symm)
  refine ⟨rootsOfUnity m d.c₂.F, inferInstance, inferInstance, (rootsOfUnity m d.c₂.F).subtype,
    fun y => rootsOfUnity.mkOfPowEq (a y) (hroot y), hsec, fun y => ?_⟩
  rw [ha]
  rfl

end GlobalTheory.RootOfUnityFn
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SameSpaceOfLawsJ

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta

namespace GlobalTheory.ShortLaws

theorem sameSpace_of_lawsJ {D : D7} (J : CoreJ D) (T : Top D) (hJ : LawsJ J) (hT : T.toCore = J.toCore) :
    ∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧
      ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0 := by
  have key : ∀ C : Core D, C = J.toCore → ∀ j, InR D j → ∀ k k', ((C.U j C.σ₀).X k).Gm = ((C.U j C.σ₀).X k').Gm ∧
      ((C.U j C.σ₀).X k).ξ0 = ((C.U j C.σ₀).X k').ξ0 := by
    rintro C rfl j hj k k'
    obtain ⟨hr, hm⟩ := hJ.modelW j hj J.toCore.σ₀ J.toCore.good_σ₀
    exact ⟨(hm k).1.trans (hm k').1.symm, (hm k).2.trans (hm k').2.symm⟩
  exact key _ hT

theorem lawsSh_of_pinned (hC : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2) {D : D7} (T : Top D) (h : LawsP T) (hb : 0 < badN D)
    (hsp : ∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧
      ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0)
    (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde')
    (hd : ∀ j, InR D j → ∀ n, (T.dδ j n).pd = p ∧ (T.dδ j n).IsLev ∧ (T.dδ j n).l₂.A = 1 ∧
      (∃ _ : StarRing (𝓞 D.host.E), IsNab (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).nab₂) ∧
      (∃ m : ℕ, 0 < m ∧ (T.dδ j n).cδ ^ m = 1) ∧
      (∀ y : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom), ∃ a : (T.dδ j n).c₂.F,
        evR (T.dδ j n).Xo₂ (T.dδ j n).c₂ (T.dδ j n).cδ y =
          algebraMap (T.dδ j n).c₂.F (CAt (T.dδ j n).c₂.F.val.toRingHom) a) ∧
      ((T.Q.Dw j).p + (T.Q.Dw j).q ≤ n → ∃ ph ψ x₀, ψ ≠ 1 ∧ (T.dδ j n).PhiPin ph ψ x₀ ∧ (T.dδ j n).PsiTie ψ)) :
    LawsSh T := by
  have hM : LawsM T.toCore := h.toLawsCore.toLawsM
  obtain ⟨-, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q hM.pins
  have hL : ReciprocityTheory.ChartRestriction.G.Out.Laws := GlobalTheory.firstFiveLaws.1
  have hr : ∀ j, InR D j → (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := fun j hj => (hnum j hj).1
  have hr1 : ∀ j, InR D j → 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := fun j hj => (hr j hj).symm ▸ (hnum j hj).2.1
  have hb1 : badN D ≠ 1 := by
    have h2 : 2 ∣ badN D := by
      unfold badN
      exact ((D.host.two_dvd_QS.mul_right _).mul_right _).mul_right _
    omega
  have hroot : ∀ j, InR D j → ∀ n, ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls)
      (δ : Cls →* (T.dδ j n).c₂.Fˣ)
      (gdet : FrPt (T.dδ j n).Xo₂ (T.dδ j n).c₂ (CAt (T.dδ j n).c₂.F.val.toRingHom) → Cls),
      CMP (T.Q.Xo j) T.Q.c (T.dδ j n) _ Cls δ gdet false := by
    intro j hj n
    obtain ⟨-, hlev, -, -, ⟨m, hm, hm1⟩, hval, -⟩ := hd j hj n
    exact GlobalTheory.RootOfUnityFn.exists_character _ _ _ _ _ _ n (T.dδ j n) m hm hlev.2.2.2.2.2.2.2.1 hm1 hval
  have htot : ∀ j, InR D j → ∀ a n,
      ShortValTot (T.Q.Xo j) T.Q.c (T.nab j) (badN D) D.R.nV a n (T.dδ j n) := by
    intro j hj a n
    obtain ⟨-, hlev, hA2, hnab, -, -, hphi⟩ := hd j hj n
    refine GlobalTheory.shortValTot_of_pinned hL hC _ _ _ _ _ _ n (T.dδ j n)
      (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 _ _ _ (hr1 j hj)).1 (hM.evalWD j hj) (h.allTest j hj)
      (GlobalTheory.Frames.algebraic_laws hL.secBaseChange _ _ _ _ _ _).2.2.1
      (GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange _ _ _ _ _ _) hlev (hA2.trans hA.symm) hnab ?_ _ _ _ a
    intro hn
    obtain ⟨ph, ψ, x₀, -, h1, h2⟩ := hphi hn
    exact ⟨ph, ψ, x₀, h1, h2⟩
  have hpin : ∀ j, InR D j → ∀ n, (T.Q.Dw j).p + (T.Q.Dw j).q ≤ n → ∃ ph ψ x₀, (T.dδ j n).PhiPin ph ψ x₀ := by
    intro j hj n hn
    obtain ⟨ph, ψ, x₀, -, h1, -⟩ := (hd j hj n).2.2.2.2.2.2 hn
    exact ⟨ph, ψ, x₀, h1⟩
  have hunit : ∀ j, InR D j → ∀ n, GlobalTheory.Dict.UnitC (T.dδ j n) := by
    intro j hj n
    obtain ⟨Cls, _, _, δ, gdet, hc⟩ := hroot j hj n
    exact GlobalTheory.Dict.unitC_of_finite_character _ _ _ _ _ _ _ _ Cls δ gdet (hr1 j hj) hc
  refine
    { beta := fun j _ n => GlobalTheory.betaExists_of_ne_one _ _ _ _ _ n _ hb1
      dLev := fun j hj n => (hd j hj n).2.1
      dNab := fun j hj n => (hd j hj n).2.2.2.1
      dPd := ⟨p, hp, fun j hj n => (hd j hj n).1⟩
      dPhi := fun j hj n hn => (hd j hj n).2.2.2.2.2.2 ((hr j hj).symm ▸ hn)
      dRoot := hroot
      shTot := fun j hj a n _ => htot j hj a n
      shCusp := fun j hj a n _ _ => GlobalTheory.T.short_thetaSeries_dominant_weight_isCuspForm hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c n (T.dδ j n)
        D.R.r (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (hnum j hj).2.1 (fun σ hσ => hM.unf j hj σ hσ)
        (hd j hj n).2.1 (hd j hj n).2.2.2.1 (hunit j hj n) (hpin j hj n) (T.nab j) (badN D) D.R.nV a
      shNe := ?_ }
  intro j h1 h2
  have hj : InR D j := ⟨h1, h2.le⟩
  refine shortNe0_of_t4Span _ _ _ _ _ _ _ ?_
  refine GlobalTheory.T.cuspForms_le_span_shortThetaSeries hC D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) T.σ₀ T.good_σ₀ (hM.unf j hj _ T.good_σ₀) (hnum j hj).2.1 hA
    (hsp j hj) ?_ (fun a n hdom k => hM.chiTriv j hj _ T.good_σ₀ a n hdom k) (T.nab j) (badN D) D.R.nV (T.dδ j) hb ?_
  · intro k ga hga hv
    refine GlobalTheory.T.coreArithmeticGroup_contains_principalCongruence D T.toCore h.toLawsCore j hj _ T.good_σ₀ k ga hga fun x hx => ?_
    obtain ⟨u, hu, he⟩ := hv x hx
    refine ⟨u, hu, ?_⟩
    rw [he, Nat.cast_smul_eq_nsmul]
    exact add_sub_cancel_left _ _
  · intro n
    refine ⟨(hd j hj n).2.1, (hd j hj n).2.2.2.1, hunit j hj n, ?_, hpin j hj n, fun a _ => htot j hj a n⟩
    rw [(hd j hj n).1]
    have := D.host.pde_mod
    rcases hp with rfl | rfl <;> omega

end GlobalTheory.ShortLaws
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.LawsShortOfDeltaOK

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin

theorem laws_short_of_deltaOK : ∀ (D : D7) (J : CoreJ D) (T : Top D), LawsJ J → LawsP T → T.toCore = J.toCore → 0 ∉ D.host.levelPrimes → ∀ (p : ℕ) (I : Ideal (𝓞 D.host.E)), (p = D.host.pde ∨ p = D.host.pde') → ∀ dd : ∀ j n, DeltaDat (T.Q.Xo j) T.Q.c n, (∀ j, InR D j → ∀ n, DeltaOK (dd j n) p I) → LawsP ({ T with dδ := dd } : Top D) ∧ LawsSh ({ T with dδ := dd } : Top D) := by
  intro D J T hJ h hT h0 p I hp dd hd
  have h' : LawsP ({ T with dδ := dd } : Top D) := { h with }
  have hb : 0 < badN D := by
    have := D.host.qd_big
    unfold badN
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos D.host.QS_pos (by omega)) (by omega))
      (Finset.prod_pos fun x hx => Nat.pos_of_ne_zero fun h => h0 (h ▸ hx))
  refine ⟨h', GlobalTheory.ShortLaws.lawsSh_of_pinned GlobalTheory.chartIndependence_unconditional _ h' hb
    (GlobalTheory.ShortLaws.sameSpace_of_lawsJ J T hJ hT) p hp fun j hj n => ?_⟩
  obtain ⟨⟨h1, -, h3, h4, h5⟩, ⟨h6, h7⟩, h8⟩ := hd j hj n
  exact ⟨h1, h3, h4, h5, h6, h7, h8⟩

end GlobalTheory.FinalJoin
end
end
