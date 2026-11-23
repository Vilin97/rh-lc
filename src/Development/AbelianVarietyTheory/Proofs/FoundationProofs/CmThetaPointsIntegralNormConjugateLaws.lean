module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.CoeffSubstInvMemOfTwoLeOrder
public import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.HomotheticLatticeIntegralS2
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveEndoAll
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementW
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
public import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.EndInt
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PhNorm
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PowerSeriesEmbedding
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SigmaAlg
import Formalism.LocalToGlobal.TorsionIntegrality.ComplexLatticeClosure.LamConjTheta0
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HasCMByStable
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.SecondLogDerivativeUnique
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.CurveFormalFirstLevelHolds
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.Points
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSysW
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.TransW
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.ShiftAnalyticW
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormLeOneOfQuad
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FstMemClosureNatCast
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulByIntegralIsClosed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PhAtMulByNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditive
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.BeConjOfNormHolds
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.FamilyLogGammaSmallHolds
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RetcutA
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.TypeStar
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgBasic

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormPrime

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.CMUnit

open Formalism.MainNotions.GL3Theta

theorem unif_setup (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p)
    (hA : At D cc δ g) :
    ∃ (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair), Formalism.L2.KerInert.IotaExt g.lam ι ∧
      Formalism.L2.Th1.CM.HasCMBy D.host.d L ∧ Formalism.L2.Th1.E.Unif p L ι g.W ∧ Formalism.L2.Th1.E.IntCurve g.W := by
  obtain ⟨hcurve, -, hδ12, hLam, hOk⟩ := hA
  have hcc : cc ≠ ⊥ := hcurve.1
  have hδ : δ ≠ 0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.brcc_delta_ne D cc hcurve δ hδ12
  obtain ⟨⟨L, hL⟩, -⟩ := Formalism.L2.Th1.F2.lamOfLat D cc δ hcc hδ
  have hLg : g.abelian₂ = L.lattice.toAddSubgroup := hLam.trans hL.symm
  obtain ⟨hg2, hg3⟩ := Formalism.L2.KerInert.Sigma.invAlg' D cc δ hcurve hδ12 L hL
  set a2 : Qbar := ⟨L.g₂, hg2⟩ with ha2
  set a3 : Qbar := ⟨L.g₃, hg3⟩ with ha3
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L
    (congrArg (fun A : AddSubgroup ℂ => (A : Set ℂ)) hLg.symm)
  have hcmby := Formalism.L2.KerInert.Sigma.ChartWirtingerDerivatives.hasCMBy_curve D cc δ hcurve hδ12 L hL
  obtain ⟨ι, hι⟩ := Formalism.L2.KerInert.lamExt p g.lam
  have hιg2 : ι L.g₂ = g.lam a2 := hι a2
  have hιg3 : ι L.g₃ = g.lam a3 := hι a3
  have hwm : wModel g.lam g.abelian₂ = Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) := by
    have e4 : lamC g.lam (-(g2 g.abelian₂) / 4) = -(g.lam a2) / 4 := by
      have : -(g2 g.abelian₂) / 4 = ((-a2 / 4 : Qbar) : ℂ) := by rw [e2]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    have e6 : lamC g.lam (-(g3 g.abelian₂) / 4) = -(g.lam a3) / 4 := by
      have : -(g3 g.abelian₂) / 4 = ((-a3 / 4 : Qbar) : ℂ) := by rw [e3]; push_cast; rfl
      rw [this, Formalism.L2.KerInert.Sigma.lamC_coe, map_div₀, map_neg, map_ofNat]
    rw [hιg2, hιg3]
    ext <;> simp [wModel, Formalism.L2.Th1.A.shortW, e4, e6]
  set W0 : WeierstrassCurve ℂ_[p] := Formalism.L2.Th1.A.shortW (ι L.g₂) (ι L.g₃) with hW0
  have hgW : g.W = g.C • W0 := by rw [G1.W, hwm]
  obtain ⟨i1, i2, i3, i4, i6, hΔ⟩ := hOk.1
  have hWint : Formalism.L2.Th1.E.IntCurve g.W := ⟨i1, i2, i3, i4, i6, hΔ⟩
  have hW0' := Formalism.L2.KerInert.Sigma.wModel_g g.lam g.abelian₂ a2 a3 e2 e3
  rw [hwm] at hW0'
  obtain ⟨c2, c3⟩ := Formalism.L2.KerInert.PN.g_change' W0 g.C
  rw [← hgW, hW0'.1] at c2
  rw [← hgW, hW0'.2] at c3
  set uu : ℂ_[p] := ((g.C.u : ℂ_[p]ˣ) : ℂ_[p]) with huu
  have hc : ι.symm uu ≠ 0 := by
    intro h
    exact Units.ne_zero g.C.u (by rw [← huu, ← ι.apply_symm_apply uu, h, map_zero])
  have hιc : ι (ι.symm uu) = uu := ι.apply_symm_apply uu
  have hH := Formalism.L2.Th1.F.homogeneity L (ι.symm uu) hc
  have hU' : Formalism.L2.Th1.E.Unif p (Formalism.L2.Th1.F.scalePair L (ι.symm uu) hc) ι g.W := by
    refine ⟨?_, ?_⟩
    · rw [c2, hH.2.2.2.2.2.2.2.2.2.1, map_mul, map_inv₀, map_pow, hιc, ← hιg2, Units.val_inv_eq_inv_val, inv_pow]
    · rw [c3, hH.2.2.2.2.2.2.2.2.2.2, map_mul, map_inv₀, map_pow, hιc, ← hιg3, Units.val_inv_eq_inv_val, inv_pow]
  have hcm' : Formalism.L2.Th1.CM.HasCMBy D.host.d (Formalism.L2.Th1.F.scalePair L (ι.symm uu) hc) :=
    Formalism.L2.Th1.F.hasCMByScale _ L _ hc hcmby
  exact ⟨ι, _, hι, hcm', hU', hWint⟩

theorem exists_norm_prime (dK : ℕ) (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ m : ℤ, ¬ (p : ℤ) ∣ Formalism.L2.Th1.D.normInt dK m 1 := by
  by_contra h
  push_neg at h
  have h0 := h 0
  have h1 := h 1
  have e : Formalism.L2.Th1.D.normInt dK 1 1 - Formalism.L2.Th1.D.normInt dK 0 1 = 2 := by
    unfold Formalism.L2.Th1.D.normInt; ring
  have h2 : (p : ℤ) ∣ 2 := by rw [← e]; exact dvd_sub h1 h0
  have h2' : p ∣ 2 := by exact_mod_cast h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2')

theorem hb_odd (dK : ℕ) (L : PeriodPair) (hmod : dK % 4 = 3) (hCM : Formalism.L2.Th1.CM.HasCMBy dK L)
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (ι : ℂ ≃+* ℂ_[p]) (W : WeierstrassCurve ℂ_[p])
    (hU : Formalism.L2.Th1.E.Unif p L ι W) (hW : Formalism.L2.Th1.E.IntCurve W) (m n : ℤ)
    (hN : ¬ (p : ℤ) ∣ Formalism.L2.Th1.D.normInt dK m n) :
    ‖(ι ((m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK) ^ 2 - 1) * (W.b₂ / 12)‖ ≤ 1 := by
  have hN0 : Formalism.L2.Th1.D.normInt dK m n ≠ 0 := fun h => hN (by rw [h]; exact dvd_zero _)
  set b : ℂ := (m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK with hb
  set bb : ℂ := (m : ℂ) + (n : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK dK) with hbb
  have hprodC : b * bb = ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ) :=
    Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.prod_bar hmod m n
  have hb0 : b ≠ 0 := by
    intro h
    apply hN0
    have h' := hprodC
    rw [h, zero_mul] at h'
    exact_mod_cast h'.symm
  have hst : Formalism.L2.Th1.F.MulStable L b := (Formalism.L2.Th1.F.hasCMByStable dK L hCM m n).1
  have hstb : Formalism.L2.Th1.F.MulStable L bb := by
    have h := (Formalism.L2.Th1.F.hasCMByStable dK L hCM (m + n) (-n)).1
    have e : (((m + n : ℤ) : ℂ) + ((-n : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK dK) = bb := by
      rw [hbb]; push_cast; ring
    rwa [e] at h
  obtain ⟨S, hS⟩ := Formalism.L2.Th1.F.kerRepsExist L b hb0 hst
  set t : ℂ := L.ω₁ / 2 with ht
  have ht0 : t ∉ L.lattice := L.ω₁_div_two_notMem_lattice
  have ht2 : 2 * t ∈ L.lattice := by
    rw [ht, mul_div_cancel₀ _ two_ne_zero]; exact L.ω₁_mem_lattice
  set Q : ℂ := t / b with hQ
  have hbQ : b * Q = t := by rw [hQ, mul_div_cancel₀ _ hb0]
  have hiso := Formalism.L2.Th1.F.isogenyP L b S hb0 hst hS Q (by rw [hbQ]; exact ht0)
  rw [hbQ] at hiso

  set M : ℕ := 2 * (Formalism.L2.Th1.D.normInt dK m n).natAbs with hM
  have hpM : ¬ p ∣ M := by
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).1 h with h2 | h2
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)
    · exact hN (Int.natCast_dvd.2 h2)
  have hMR : ∀ R : ℂ, (2 * (b * bb)) * R ∈ L.lattice → (M : ℂ) * R ∈ L.lattice := by
    intro R hR
    rw [hprodC] at hR
    rcases Int.natAbs_eq (Formalism.L2.Th1.D.normInt dK m n) with e | e
    · have hc : ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ) = ((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ) := by
        rw [← Int.cast_natCast, ← e]
      rw [hc] at hR
      have e2 : (M : ℂ) = 2 * ((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ) := by rw [hM]; push_cast; ring
      rw [e2]; exact hR
    · have hc : ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ) = -((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ) := by
        rw [← Int.cast_natCast, ← Int.cast_neg, ← e]
      rw [hc] at hR
      have e2 : (M : ℂ) * R = -(2 * -((Formalism.L2.Th1.D.normInt dK m n).natAbs : ℂ) * R) := by rw [hM]; push_cast; ring
      rw [e2]; exact neg_mem hR
  have intR : ∀ R : ℂ, R ∉ L.lattice → (2 * (b * bb)) * R ∈ L.lattice →
      ι (L.weierstrassP R) - W.b₂ / 12 ∈ Formalism.G.unitBall ℂ_[p] := by
    intro R hR h
    have h1 := (Formalism.L2.Th1.E.TransW.ptW_int Formalism.L2.Th1.E.ptWAdd Formalism.L2.Th1.E.ptWZero hU hW R M hpM
      (hMR R h) hR).1
    rw [Formalism.L2.Th1.E.AnaSysW.px_ptW hU R hR] at h1
    exact h1
  have mt : (2 * (b * bb)) * t ∈ L.lattice := by
    have e : (2 * (b * bb)) * t = b * (bb * (2 * t)) := by ring
    rw [e]; exact hst _ (hstb _ ht2)
  have mQ : (2 * (b * bb)) * Q ∈ L.lattice := by
    have e : (2 * (b * bb)) * Q = bb * (2 * (b * Q)) := by ring
    rw [e, hbQ]; exact hstb _ ht2
  have mP : ∀ P ∈ S, (2 * (b * bb)) * P ∈ L.lattice := by
    intro P hP
    have h := (hS.1 P hP).1
    have e : (2 * (b * bb)) * P = bb * (b * P) + bb * (b * P) := by ring
    rw [e]; exact add_mem (hstb _ h) (hstb _ h)
  have nQ : Q ∉ L.lattice := by
    intro h; apply ht0; rw [← hbQ]; exact hst _ h
  have nQP : ∀ P ∈ S, Q + P ∉ L.lattice := by
    intro P hP h
    apply ht0
    have e : t = b * (Q + P) - b * P := by rw [← hbQ]; ring
    rw [e]; exact sub_mem (hst _ h) (hS.1 P hP).1
  have iT := intR t ht0 mt
  have iQ := intR Q nQ mQ
  have iP : ∀ P ∈ S, ι (L.weierstrassP P) - W.b₂ / 12 ∈ Formalism.G.unitBall ℂ_[p] :=
    fun P hP => intR P (hS.1 P hP).2 (mP P hP)
  have iQP : ∀ P ∈ S, ι (L.weierstrassP (Q + P)) - W.b₂ / 12 ∈ Formalism.G.unitBall ℂ_[p] := by
    intro P hP
    refine intR (Q + P) (nQP P hP) ?_
    rw [mul_add]; exact add_mem mQ (mP P hP)

  have hbI : ι b ∈ Formalism.G.unitBall ℂ_[p] := by
    have hs : ι b + ι bb = ((2 * m + n : ℤ) : ℂ_[p]) := by
      rw [← map_add (f := _), hb, hbb]
      have e : ((m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK) +
          ((m : ℂ) + (n : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK dK)) = ((2 * m + n : ℤ) : ℂ) := by
        push_cast; ring
      rw [e, map_intCast]
    have hp : ι b * ι bb = ((Formalism.L2.Th1.D.normInt dK m n : ℤ) : ℂ_[p]) := by
      rw [← map_mul, hprodC, map_intCast]
    exact Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_le_one_of_quad hs hp
      (IsUltrametricDist.norm_intCast_le_one ℂ_[p] _)

  have hi := congrArg ι hiso

  simp only [map_mul, map_pow, map_add (f := _), map_sum, map_sub] at hi
  have key : (ι b ^ 2 - 1) * (W.b₂ / 12) =
      (ι (L.weierstrassP Q) - W.b₂ / 12) +
        ∑ P ∈ S, ((ι (L.weierstrassP (Q + P)) - W.b₂ / 12) - (ι (L.weierstrassP P) - W.b₂ / 12)) -
        ι b ^ 2 * (ι (L.weierstrassP t) - W.b₂ / 12) := by
    have e : ∑ P ∈ S, ((ι (L.weierstrassP (Q + P)) - W.b₂ / 12) - (ι (L.weierstrassP P) - W.b₂ / 12)) =
        ∑ P ∈ S, (ι (L.weierstrassP (Q + P)) - ι (L.weierstrassP P)) :=
      Finset.sum_congr rfl (fun _ _ => by ring)
    rw [e]
    linear_combination hi
  have hmem : (ι b ^ 2 - 1) * (W.b₂ / 12) ∈ Formalism.G.unitBall ℂ_[p] := by
    rw [key]
    refine sub_mem (add_mem iQ (Subring.sum_mem _ fun P hP => sub_mem (iQP P hP) (iP P hP)))
      (mul_mem (pow_mem hbI 2) iT)
  exact hmem

theorem endoDatum_model (dK : ℕ) (L : PeriodPair) (hmod : dK % 4 = 3) (hCM : Formalism.L2.Th1.CM.HasCMBy dK L)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (W : WeierstrassCurve ℂ_[p])
    (hU : Formalism.L2.Th1.E.Unif p L ι W) (hW : Formalism.L2.Th1.E.IntCurve W) (m n : ℤ)
    (hN : ¬ (p : ℤ) ∣ Formalism.L2.Th1.D.normInt dK m n) :
    ∃ (S : Finset ℂ) (neg : S → S) (xP yP : S → ℂ_[p]),
      Formalism.L2.Th1.C.IsEndoCurve W neg xP yP (ι ((m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK)) ∧
      (∀ P, ‖xP P‖ ≤ 1) ∧ (∀ P, ‖yP P‖ ≤ 1) ∧
      ι ((m : ℂ) + (n : ℂ) * Formalism.L2.Th1.CM.omegaK dK) * ι ((m : ℂ) + (n : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK dK)) =
        (Fintype.card S : ℂ_[p]) + 1 := by
  have hN0 : Formalism.L2.Th1.D.normInt dK m n ≠ 0 := by
    intro h
    apply hN
    rw [h]
    exact dvd_zero _
  obtain ⟨S, neg, hcard, hker, hnegP, hE, hprod, -⟩ :=
    Formalism.L2.Th1.D.CurveNormEndomorphisms.cdata L hmod hCM m n hN0
  have hpN : ¬ p ∣ (S.card + 1) := by
    intro h
    apply hN
    rw [← hcard]
    exact_mod_cast h
  refine ⟨S, neg, fun P => Formalism.L2.Th1.E.AnaSysW.xc p L ι W (P : ℂ),
    fun P => Formalism.L2.Th1.E.AnaSysW.yc p L ι W (P : ℂ), ?_, ?_, ?_, ?_⟩
  · apply Formalism.L2.Th1.D.CurveNormEndomorphisms.endoCurve_of_endoZ (RingHom.id ℂ_[p]) W
      (wF := fun P : S => PowerSeries.map (ι : ℂ →+* ℂ_[p])
        (Formalism.L2.Th1.F.taylor0 (fun z => L.weierstrassP (z + (P : ℂ)))))
    · intro P
      exact (Formalism.L2.Th1.E.AnaSysW.nonsing hU _ (hker P).2).1
    · intro P
      refine ⟨?_, ?_⟩
      · simp only [Formalism.L2.Th1.E.AnaSysW.xc, (hnegP P).1]
      · simp only [Formalism.L2.Th1.E.AnaSysW.yc, Formalism.L2.Th1.E.AnaSysW.xc, WeierstrassCurve.Affine.negY,
          (hnegP P).1, (hnegP P).2, map_neg]
        ring
    · have h := Formalism.L2.Th1.D.CurveNormEndomorphisms.isEndoZ_map (ι : ℂ →+* ℂ_[p]) hE
      simp only [PowerSeries.map_id, RingHom.id_apply, Formalism.L2.Th1.E.AnaSysW.xc, sub_add_cancel]
      rw [Formalism.L2.Th1.E.AnaSysW.wpBridge hU]
      exact h
  · intro P
    have h := (Formalism.L2.Th1.E.TransW.ptW_int Formalism.L2.Th1.E.ptWAdd Formalism.L2.Th1.E.ptWZero hU hW (P : ℂ)
      (S.card + 1) hpN (hker P).1 (hker P).2).1
    rwa [Formalism.L2.Th1.E.AnaSysW.px_ptW hU _ (hker P).2] at h
  · intro P
    have h := (Formalism.L2.Th1.E.TransW.ptW_int Formalism.L2.Th1.E.ptWAdd Formalism.L2.Th1.E.ptWZero hU hW (P : ℂ)
      (S.card + 1) hpN (hker P).1 (hker P).2).2
    rw [Formalism.L2.Th1.E.AnaSysW.ptW_notMem hU _ (hker P).2] at h
    exact h
  · rw [← map_mul, hprod, Fintype.card_coe]
    simp

theorem unit_endo : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → p ≠ 2 → ∀ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p →
    IntegralMv (g.mulBy (GL3Theta.tauK D g.lam (a : D.host.K)) (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  intro D p _ cc δ g hA hp2 a _
  have hOk : g.Ok := hA.2.2.2.2
  obtain ⟨ι, L, hι, hcm, hU, hW⟩ := unif_setup D p cc δ g hA
  have hd4 : D.host.d % 4 = 3 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨m, hm⟩ := exists_norm_prime D.host.d p hp2
  obtain ⟨S, neg, xP, yP, hE, hx, hy, hprod⟩ :=
    endoDatum_model D.host.d L hd4 hcm p ι g.W hU hW m 1 hm
  have hb := hb_odd D.host.d L hd4 hcm p hp2 ι g.W hU hW m 1 hm
  set β := ι ((m : ℂ) + ((1 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d) with hβ
  set β' := ι ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK D.host.d)) with hβ'
  have h2 : ‖(2 : ℂ_[p])‖ = 1 := Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_two p hp2
  have hsum : β + β' = ((2 * m + 1 : ℤ) : ℂ_[p]) := by
    rw [hβ, hβ', ← map_add (f := _)]
    have e : ((m : ℂ) + ((1 : ℤ) : ℂ) * Formalism.L2.Th1.CM.omegaK D.host.d) +
        ((m : ℂ) + ((1 : ℤ) : ℂ) * (1 - Formalism.L2.Th1.CM.omegaK D.host.d)) = ((2 * m + 1 : ℤ) : ℂ) := by
      push_cast; ring
    rw [e, map_intCast]
  have hN1 : ‖(Fintype.card S : ℂ_[p]) + 1‖ = 1 := by
    have e := Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.prod_bar hd4 m 1
    have e' : β * β' = ((Formalism.L2.Th1.D.normInt D.host.d m 1 : ℤ) : ℂ_[p]) := by
      rw [hβ, hβ', ← map_mul, e, map_intCast]
    rw [← hprod, e']
    exact Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_int p hm
  have hβ1 : ‖β‖ = 1 := Formalism.L2.Th1.Top.OrthogonalGaussModelNormLemmas.norm_eq_one_of_quad hsum hprod hN1
  have hβinv : β⁻¹ ∈ Formalism.L2.KerInert.IwahoriBlocks.RB p := by
    show ‖β⁻¹‖ ≤ 1
    rw [norm_inv, hβ1, inv_one]
  have hR := Formalism.L2.Th1.C.curveEndoR ℂ_[p] (Formalism.L2.KerInert.IwahoriBlocks.RB p) g.W
    (Formalism.L2.KerInert.IwahoriBlocks.coeffIn_g g hOk) S neg xP yP β β' hE (fun P => hx P) (fun P => hy P) hprod
    hβ1.le hβinv hb
  obtain ⟨hlp, hwp, hAx, hFG, -⟩ := Formalism.L2.Th1.C.curveFrame ℂ_[p] (Formalism.L2.KerInert.IwahoriBlocks.RB p) g.W
    (Formalism.L2.KerInert.IwahoriBlocks.coeffIn_g g hOk)
  have h2R : (2 : ℂ_[p])⁻¹ ∈ Formalism.L2.KerInert.IwahoriBlocks.RB p := by
    show ‖(2 : ℂ_[p])⁻¹‖ ≤ 1
    rw [norm_inv, h2, inv_one]
  have hEβ := Formalism.L2.Th1.C.endIntFromDatum ℂ_[p] (Formalism.L2.KerInert.IwahoriBlocks.RB p) _ _ _ _ _ S neg xP _ _ β β'
    hlp hwp hAx h2R hR
  have hEω : Formalism.L2.Th1.C.EndInt (Formalism.L2.KerInert.IwahoriBlocks.RB p) (Formalism.L2.Th1.A.logSer g.W)
      (Formalism.L2.Th1.A.expSer g.W) (ι (Formalism.L2.Th1.CM.omegaK D.host.d)) := by
    have hm' := Formalism.L2.Th1.G.WeierstrassCurveSeries.endInt_int (Formalism.L2.KerInert.IwahoriBlocks.RB p) _ _ hlp hFG (-m)
    have h := Formalism.L2.Th1.C.Pts.endInt_add hlp hFG hEβ hm'
    have e : β + ((-m : ℤ) : ℂ_[p]) = ι (Formalism.L2.Th1.CM.omegaK D.host.d) := by
      rw [hβ, map_add (f := _), map_mul, map_intCast, map_intCast]; push_cast; ring
    rwa [e] at h
  exact Formalism.L2.KerInert.IwahoriBlocks.integralMv_of_endInt g hOk _
    (Formalism.L2.KerInert.IwahoriBlocks.endInt_OK D p g hOk ι hι hEω a)

end GlobalTheory.CMUnit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLaws

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.CMEndo

section Series
open Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ : Type*}

theorem const_l : PowerSeries.constantCoeff g.l = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem ex_l (h : g.Ok) : PowerSeries.subst g.l g.ex = PowerSeries.X := by
  obtain ⟨-, -, h0, h1⟩ := h
  have hl : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.l : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => const_l g
  have he : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.ex : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => h0
  have h2 : ∀ i : Unit, MvPowerSeries.subst (fun _ : Unit => (g.ex : MvPowerSeries Unit ℂ_[p]))
      (g.l : MvPowerSeries Unit ℂ_[p]) = MvPowerSeries.X i := fun _ => h1
  have h3 := GlobalTheory.FormalInv.eq_substInv_of_right hl he h2
  have h4 := GlobalTheory.FormalInv.subst_substInv_left hl
    (IsUnit.of_mul_eq_one _ (GlobalTheory.FormalInv.linearPart_mul_eq_one hl he h2)) ()
  rw [← h3] at h4
  exact h4

theorem pt_lg (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.pt (g.lg a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [GL3Theta.G1.pt, GL3Theta.G1.lg, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (const_l g)) ha', ex_l g h, PowerSeries.subst_X ha']

theorem subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries σ ℂ_[p]) f = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries σ ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, zero_mul]

theorem mulBy_one (h : g.Ok) (i : σ) : g.mulBy 1 (GL3Theta.Xv i) = GL3Theta.Xv i := by
  rw [GL3Theta.G1.mulBy, map_one, one_mul, pt_lg g h (MvPowerSeries.constantCoeff_X i)]

theorem mulBy_zero (h : g.Ok) (a : MvPowerSeries σ ℂ_[p]) : g.mulBy 0 a = 0 := by
  rw [GL3Theta.G1.mulBy, map_zero, zero_mul, GL3Theta.G1.pt, subst_zero h.2.2.1]

theorem constantCoeff_subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0)
    {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, map_mul, ha, zero_mul]

theorem constantCoeff_lg {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.lg a) = 0 :=
  constantCoeff_subst_zero (const_l g) ha

theorem constantCoeff_pt (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.pt a) = 0 :=
  constantCoeff_subst_zero h.2.2.1 ha

theorem lg_pt (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.lg (g.pt a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [G1.lg, G1.pt, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' h.2.2.1) ha', h.2.2.2, PowerSeries.subst_X ha']

theorem lg_mulBy (h : g.Ok) (c : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.lg (g.mulBy c a) = MvPowerSeries.C c * g.lg a := by
  rw [G1.mulBy, lg_pt g h]
  rw [map_mul, constantCoeff_lg g ha, mul_zero]

theorem mulBy_add (h : g.Ok) (c c' : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.mulBy (c + c') a = g.add (g.mulBy c a) (g.mulBy c' a) := by
  rw [G1.add, lg_mulBy g h c ha, lg_mulBy g h c' ha, G1.mulBy, map_add (f := _), add_mul]

theorem add_eq_subst (h : g.Ok) (A B : MvPowerSeries σ ℂ_[p]) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    g.add A B = MvPowerSeries.subst ![A, B] (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
  have hab : MvPowerSeries.HasSubst ![A, B] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hA, hB])
  have hs : MvPowerSeries.constantCoeff (g.lg (Xv 0) + g.lg (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_add (f := _), constantCoeff_lg g (MvPowerSeries.constantCoeff_X _),
      constantCoeff_lg g (MvPowerSeries.constantCoeff_X _), add_zero]
  have hsl : ∀ i : Fin 2, MvPowerSeries.subst ![A, B] (g.lg (Xv i) : MvPowerSeries (Fin 2) ℂ_[p]) =
      g.lg (![A, B] i) := by
    intro i
    have hX : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)
    rw [G1.lg, G1.lg, PowerSeries.subst, PowerSeries.subst,
      MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X i)) hab]
    congr 1
    funext _
    exact MvPowerSeries.subst_X hab i
  rw [G1.add, G1.add, G1.pt, G1.pt, PowerSeries.subst, PowerSeries.subst,
    MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hs)) hab]
  congr 1
  funext _
  rw [MvPowerSeries.subst_add hab, hsl 0, hsl 1]
  rfl

theorem integralMv_zero : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := fun n => by
  simp [IsIntP]

theorem integralMv_X (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := fun n => by
  unfold IsIntP
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem integral_mulBy_semiring : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok →
    IntegralMv (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    IntegralMv (g.mulBy 0 (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
    IntegralMv (g.mulBy 1 (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
    ∀ c c' : ℂ_[p], IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (g.mulBy c' (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (g.mulBy (c + c') (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  intro p _ g h hadd
  have hX : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := MvPowerSeries.constantCoeff_X _
  refine ⟨?_, ?_, ?_⟩
  · rw [mulBy_zero g h]; exact integralMv_zero
  · rw [mulBy_one g h]; exact integralMv_X ()
  · intro c c' hc hc'
    have h0 : ∀ d : ℂ_[p], MvPowerSeries.constantCoeff (g.mulBy d (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
      fun d => constantCoeff_pt g h (by rw [map_mul, constantCoeff_lg g hX, mul_zero])
    rw [mulBy_add g h c c' hX, add_eq_subst g h _ _ (h0 c) (h0 c')]
    exact ReciprocityTheory.ChartRestriction.L1.integralMv_subst2 (fun d => hadd d)
      (fun i => by fin_cases i <;> simp [h0]) (fun i => by
        fin_cases i
        · exact fun d => hc d
        · exact fun d => hc' d)

end Series

theorem endInt_all (D : D7) : GL3Theta.endInt D := by
  intro p _ cc δ g hA α hα
  have hok : g.Ok := hA.2.2.2.2
  have hadd := ((GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.1 p cc δ g hA).1
  obtain ⟨h0, h1, hplus⟩ := integral_mulBy_semiring p g hok hadd
  set S : Set ℂ_[p] := {c | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} with hS
  have hcl : IsClosed S := GlobalTheory.mulBy_integral_isClosed p g
  have hnat : ∀ n : ℕ, (n : ℂ_[p]) ∈ S := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero]; exact h0
    | succ n ih =>
      rw [Nat.cast_succ]; exact hplus _ _ ih h1
  by_cases hp : p = 2
  · subst hp
    have h2 := GlobalTheory.TwoAdicFirst.fst_mem_closure_natCast D g.lam α hα
    have hsub : closure (Set.range (Nat.cast : ℕ → ℂ_[2])) ⊆ S :=
      closure_minimal (by rintro _ ⟨n, rfl⟩; exact hnat n) hcl
    exact hsub h2
  · obtain ⟨β, hβ, γ, hγ, hb1, hb2, hc1, hc2, rfl⟩ := Formalism.MainNotions.Ext.CutA.okpTwoUnits2_holds D p g.lam hp α hα
    have hunit : ∀ β ∈ GL3Theta.OKp D g.lam, ‖β.1‖ = 1 → ‖β.2‖ = 1 → β.1 ∈ S := by
      intro β hβ h1 h2
      have hc := Formalism.MainNotions.Ext.CutA.okpUnitsDense_holds D p g.lam hp β hβ h1 h2
      have hm := map_mem_closure continuous_fst hc (t := S) (by
        rintro _ ⟨a, ha, rfl⟩
        exact GlobalTheory.CMUnit.unit_endo D p cc δ g hA hp a ha)
      rwa [hcl.closure_eq] at hm
    exact hplus _ _ (hunit β hβ hb1 hb2) (hunit γ hγ hc1 hc2)

theorem endo_all : ∀ D : D7, GL3Theta.endInt D ∧ GL3Theta.phNorm D ∧ GL3Theta.beConj D := by
  intro D
  have he := endInt_all D
  have ha := (GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.1
  have hB := (GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.2
  have hok : Formalism.MainNotions.Ext.CutA.PhNormOK D := GlobalTheory.CMNormPhi.phAt_mulBy_norm D he ha
  have hn := Formalism.MainNotions.Ext.CutA.phNorm_of' Formalism.MainNotions.Ext.CutA.phNormOfUnits_holds Formalism.MainNotions.Ext.CutA.phNormClosed_holds D hok he ha hB
  exact ⟨he, hn, Formalism.MainNotions.Ext.CutA.beConj_of' Formalism.MainNotions.Ext.CutA.beConjOfNorm_holds D he ha hn hB⟩

end GlobalTheory.CMEndo
end
end
end
