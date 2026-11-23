module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsValCharTwist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCongLevelOfIsBlockLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariant
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Mathlib.Algebra.Ring.IsFormallyReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftPeterssonNormEqRallisIntegral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionBottomPair
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftPeterssonNormEqRallisIntegral

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormBigOfNonvanishing

section

@[expose] public section

open Finset
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum
open GlobalTheory.NormSum (Pair)
open GlobalTheory.CMVal (IsHeckeL)

namespace GlobalTheory.NormBigProof

theorem squareBottomHalfRankSum_le_halfRank (D : Formalism.BasicNotions.D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  unfold h0 halfRank botBig botSmall
  exact Nat.div_le_div_right (Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _))

end GlobalTheory.NormBigProof
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenKLeFockStab

section

@[expose] public section

open NumberField MeasureTheory Finset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup)
open GlobalTheory.FunObj.SqNum GlobalTheory.SqTop
open GlobalTheory.CMVal (IsHeckeL)

noncomputable section
namespace GlobalTheory.NormAdelic
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q}

theorem minorPol_ne_zero {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : GlobalTheory.NormSum.minorPol D T ≠ 0 := by
  unfold GlobalTheory.NormSum.minorPol
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  set f : Fin a × Fin a → Formalism.MainNotions.GL3Theta.Idx D a d := fun p => (τ, (T τ j).1 p.1, p.2) with hf
  have hfi : Function.Injective f := by
    intro p q e
    simp only [hf, Prod.mk.injEq] at e
    exact Prod.ext ((T τ j).2.injective e.2.1) e.2.2
  have e : (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
      (MvPolynomial.rename f).toRingHom.mapMatrix (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ) := by
    ext i i'
    simp [Matrix.mvPolynomialX, hf]
  rw [e, ← RingHom.map_det]
  intro h0
  exact Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
    ((MvPolynomial.rename_injective f hfi) (h0.trans (map_zero _).symm))

end GlobalTheory.NormAdelic
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockIpSelfRePos

section

@[expose] public section

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem fockIp_self_re_pos {ι : Type} {p : MvPolynomial ι ℂ} (hp : p ≠ 0) :
    0 < (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp p p).re := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp
  rw [Complex.re_sum]
  refine Finset.sum_pos (fun k hk => ?_) (MvPolynomial.support_nonempty.2 hp)
  rw [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  refine mul_pos (Complex.normSq_pos.2 (MvPolynomial.mem_support_iff.1 hk)) ?_
  exact Nat.cast_pos.2 (Finset.prod_pos fun _ _ => Nat.factorial_pos _)

theorem fockSum_ne_zero : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ), a ≤ d → fockSum D a d n ≠ 0 := by
  intro D a d n had h0
  have hpos : 0 < (fockSum D a d n).re := by
    unfold fockSum
    rw [Complex.re_sum]
    haveI : Nonempty (GlobalTheory.NormSum.Tup D a d n) := ⟨fun _ _ => ⟨Fin.castLE had, fun _ _ h => h⟩⟩
    exact Finset.sum_pos (fun T _ => fockIp_self_re_pos (GlobalTheory.NormAdelic.minorPol_ne_zero T)) (by
      classical exact ⟨fun _ _ => ⟨Fin.castLE had, fun _ _ h => h⟩, by simp⟩)
  rw [h0] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.NormRatio
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdMassNeZero

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem std_mass_ne_zero : ∀ (D : D7) (N : ℕ), mass D N ≠ 0 := by
  intro D N
  haveI := (GlobalTheory.NormSum.cls_finite_card_le D N).1
  haveI := Fintype.ofFinite (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))
  have hne : (Finset.univ : Finset (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))).Nonempty :=
    ⟨DoubleCoset.mk _ _ 1, Finset.mem_univ _⟩
  have hpos : (0 : ℝ) < ∑ x : GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N),
      ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D N) x.out : ℝ))⁻¹ :=
    Finset.sum_pos (fun x _ => inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero
      (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D N _ le_rfl x.out).1))) hne
  unfold mass
  rw [finsum_eq_sum_of_fintype]
  have h := Complex.ofReal_ne_zero.2 hpos.ne'
  push_cast at h
  exact h

end GlobalTheory.NormRatio
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacNormNeZero

section

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumNorm

theorem vacNorm_ne_zero : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ), Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ →
    Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (Formalism.MainNotions.TaylorLogMetric.lamOf D cc δ) t0 → ∀ a d : ℕ, vacNorm D cc δ t0 a d ≠ 0 :=
  fun D cc δ t0 hc ht _ _ =>
    pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D (GlobalTheory.InducedType.induced_type D).1 cc δ t0 hc ht)

end GlobalTheory.VacuumNorm
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BigThetaLiftNeZeroOfPeterssonNorm

section

@[expose] public section

section
noncomputable section
open NumberField
open GlobalTheory.SqTop
namespace GlobalTheory.NormBigNe
theorem big_theta_petersson_norm_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} _ _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) t (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q),
    GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' → P.norm ≠ 0 := by
  rintro hP hI ⟨a, k⟩
  refine ⟨a, fun ε CF hCF => ?_⟩
  obtain ⟨c, x, l⟩ := k ε CF hCF
  refine ⟨c, x, fun C hC D large₂ he hx hR T Lc μ₀ hμ G δ t0 i j t Q P P' hb => ?_⟩
  obtain ⟨Λ, hΛ, hne⟩ := (l C hC D large₂ he hx hR T Lc μ₀ hμ G i j).1 t
  have e := _root_.GlobalTheory.NormRatio.petersson_norm_bottom_theta_lift_eq hP (hI D) hR hμ G hb hΛ
  have hrk := GlobalTheory.FunObj.SqNum.Model.bot_ranks (D := D) i j
  have hPa := hb.rank.1
  have hPd := hb.rank.2.2.1
  have hre : 0 < (((P.d - P.a : ℕ) : ℂ) / 2).re := by
    have : (0 : ℝ) < ((P.d - P.a : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < P.d - P.a)
    rw [show (((P.d - P.a : ℕ) : ℂ) / 2) = ((((P.d - P.a : ℕ) : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
    positivity
  intro h0
  rw [h0, Complex.ofReal_zero] at e
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun s hs => ?_) e.symm
  · unfold GlobalTheory.NormRatio.normFactor
    refine div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (GlobalTheory.NormRatio.std_mass_ne_zero D _))
      (GlobalTheory.NormRatio.std_mass_ne_zero D _))
      (GlobalTheory.NormRatio.fockSum_ne_zero D _ _ _ P.a_le)) ?_) (GlobalTheory.LFun.dSfun_ne_zero_of_re_pos _ _ _ hre)
    · exact_mod_cast (GlobalTheory.NormExact.normConst_pos P.crv _ _).ne'
    · exact_mod_cast GlobalTheory.VacuumNorm.vacNorm_ne_zero D ⊤ δ t0 P.crv P.pt0 _ _
  · obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
    exact hne s hs1 (hs2.trans (by exact_mod_cast GlobalTheory.SqTop.squareBottomHalfRankSum_le_halfRank D i j))
end GlobalTheory.NormBigNe
end
end

section
open GlobalTheory.SqTop

theorem _root_.GlobalTheory.T.big_theta_lift_ne_zero_of_petersson_norm : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.LNe → GlobalTheory.SqTop.GBig fun {D} _ _ _ G _ _ _ _ =>
  ∀ (δ t0 : ℂ) (i j : Fin D.R.m) t (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q),
    GlobalTheory.FunObj.SqNum.IsBottom G t i j (GlobalTheory.SqTop.modT G t) P P' → P.norm ≠ 0 := by
  first | exact @_root_.GlobalTheory.NormBigNe.big_theta_petersson_norm_ne_zero | exact _root_.GlobalTheory.NormBigNe.big_theta_petersson_norm_ne_zero | (intros; apply _root_.GlobalTheory.NormBigNe.big_theta_petersson_norm_ne_zero <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.NormBigOfNonvanishing

section

@[expose] public section

section
open Finset
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum
open GlobalTheory.NormSum (Pair)
open GlobalTheory.CMVal (IsHeckeL)
namespace GlobalTheory.NormBigProof
theorem normBig_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → NormBig := by
  intro hP hI hL
  obtain ⟨a1, k1⟩ := hL
  obtain ⟨a2, k2⟩ := _root_.GlobalTheory.T.theta_lift_petersson_norm_ratio_formula hP hI ⟨a1, k1⟩
  obtain ⟨a3, k3⟩ := _root_.GlobalTheory.T.big_theta_lift_ne_zero_of_petersson_norm hP hI ⟨a1, k1⟩
  refine ⟨max a1 (max a2 a3), fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, l1⟩ := k1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, l2⟩ := k2 ε CF (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCF)
  obtain ⟨c3, x3, l3⟩ := k3 ε CF (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCF)
  refine ⟨max c1 (max c2 c3), max x1 (max x2 x3), fun C hC D large₂ he hx hRec T Lc μ₀ hμ G => ?_⟩
  have hl := l1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hRec T Lc μ₀ hμ G
  have hr := l2 C (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) hRec T Lc μ₀ hμ G
  have hz := l3 C (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hC) D large₂ he
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx) hRec T Lc μ₀ hμ G
  intro δ t0 i j
  by_cases hex : ∃ (t : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G t i j (modT G t) P P'
  · obtain ⟨t₀, Q₀, P₀, P₀', hb₀⟩ := hex
    obtain ⟨Λ₀, hΛ₀, hne⟩ := (hl i j).1 t₀
    have hprod : ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ₀ s ≠ 0 :=
      prod_ne_zero_iff.2 fun s hs => hne s (mem_Icc.1 hs).1
        (le_trans (mem_Icc.1 hs).2 (by exact_mod_cast squareBottomHalfRankSum_le_halfRank D i j))
    have hn₀ : (P₀.norm : ℂ) ≠ 0 := by exact_mod_cast hz δ t0 i j t₀ Q₀ P₀ P₀' hb₀
    refine ⟨(P₀.norm : ℂ) / ∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ₀ s, div_ne_zero hn₀ hprod,
      fun t Q P P' Λ hb hΛ => ?_⟩
    have e := hr δ t0 i j t t₀ Q Q₀ P P' P₀ P₀' Λ Λ₀ hb hb₀ hΛ hΛ₀
    rw [div_mul_eq_mul_div, eq_div_iff hprod, e]
  · exact ⟨1, one_ne_zero, fun t Q P P' Λ hb _ => absurd ⟨t, Q, P, P', hb⟩ hex⟩
end GlobalTheory.NormBigProof
end

section
open GlobalTheory.SqTop

theorem _root_.GlobalTheory.T.normBig_of_lNe : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → NormBig := by
  first | exact @_root_.GlobalTheory.NormBigProof.normBig_alt | exact _root_.GlobalTheory.NormBigProof.normBig_alt | (intros; apply _root_.GlobalTheory.NormBigProof.normBig_alt <;> assumption)
end
end
end
