module

public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.AtVariableWeierstrassDerivative
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalD
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffEqZeroOfParallelogram
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffLawWithInverseThree
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffSeriesAtVariable
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.WeierstrassSeriesIntegral
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LogarithmEquivalence
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.ConstantCoeffQuotientXSq
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementE
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.CocycleDiffExpEquiv

section

@[expose] public section

noncomputable section

namespace Formalism.L2.Th1.B.BeE

open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst)

section Alg

variable {K : Type} [Field K] [CharZero K]

theorem cob_sub {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f g : PowerSeries K) : cob F (f - g) = cob F f - cob F g := by
  have h0 := PowerSeries.HasSubst.of_constantCoeff_zero hF
  simp only [cob, at1, PowerSeries.subst_sub h0, PowerSeries.subst_sub (PowerSeries.HasSubst.X (0 : Fin 2)),
    PowerSeries.subst_sub (PowerSeries.HasSubst.X (1 : Fin 2))]
  ring

theorem cob_add {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f g : PowerSeries K) : cob F (f + g) = cob F f + cob F g := by
  have h0 := PowerSeries.HasSubst.of_constantCoeff_zero hF
  simp only [cob, at1, PowerSeries.subst_add h0, PowerSeries.subst_add (PowerSeries.HasSubst.X (0 : Fin 2)),
    PowerSeries.subst_add (PowerSeries.HasSubst.X (1 : Fin 2))]
  ring

theorem cob_zero {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0) :
    cob F (0 : PowerSeries K) = 0 := by
  simpa using cob_sub hF (0 : PowerSeries K) 0

theorem cob_neg {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    (f : PowerSeries K) : cob F (-f) = -cob F f := by
  have h := cob_sub hF (0 : PowerSeries K) f
  rwa [zero_sub, cob_zero hF, zero_sub] at h

theorem psubst_fLog {ι : Type} {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0)
    {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 1) :
    PowerSeries.subst U (fLog g) = fLog (PowerSeries.subst U g) := by
  have hg1 : PowerSeries.constantCoeff (g - 1) = 0 := by simp [hg]
  have hU' := PowerSeries.HasSubst.of_constantCoeff_zero hU
  unfold fLog
  rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg1) hU',
    PowerSeries.subst_sub hU']
  congr 2
  rw [← map_one (PowerSeries.C (R := K)), PowerSeries.subst_C, map_one]

theorem cc_psubst {ι : Type} {U : MvPowerSeries ι K} (hU : MvPowerSeries.constantCoeff U = 0)
    {g : PowerSeries K} {c : K} (hg : PowerSeries.constantCoeff g = c) :
    MvPowerSeries.constantCoeff (PowerSeries.subst U g) = c := by
  have hU' := PowerSeries.HasSubst.of_constantCoeff_zero hU
  have hgc : PowerSeries.constantCoeff (g - PowerSeries.C c) = 0 := by simp [hg]
  have e : g = PowerSeries.C c + (g - PowerSeries.C c) := by ring
  rw [e, PowerSeries.subst_add hU', PowerSeries.subst_C, map_add (f := _),
    PowerSeries.constantCoeff_subst_eq_zero hU _ hgc]
  simp

theorem cob_fLog {F : MvPowerSeries (Fin 2) K} (hF : MvPowerSeries.constantCoeff F = 0)
    {g : PowerSeries K} (hg : PowerSeries.constantCoeff g = 1) :
    cob F (fLog g) = fLog (PowerSeries.subst F g) - fLog (at1 0 g) - fLog (at1 1 g) := by
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
    fun i => MvPowerSeries.constantCoeff_X i
  simp only [cob, at1]
  rw [psubst_fLog hF hg, psubst_fLog (hX 0) hg, psubst_fLog (hX 1) hg]

theorem two_ne {ι : Type} : (2 : MvPowerSeries ι K) ≠ 0 := by
  intro h
  have h2 := congrArg MvPowerSeries.constantCoeff h
  have e2 : MvPowerSeries.constantCoeff (2 : MvPowerSeries ι K) = 2 := map_ofNat _ 2
  rw [e2, map_zero] at h2
  exact two_ne_zero h2

end Alg

theorem BeESim_of (hG : GCob) (hL : LDiv) : BeESim := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨nu, hnuI, hnu0, hLT⟩ := hL K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨hy, hcub, hx, -, -, hk⟩ := hT
  have hGC := hG K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hC hC3 hy hcub
  have hF0 := hF.1
  have hce : c0 - (xT + c0) = -xT := by ring
  have hn : ‖c0 - (xT + c0)‖ ≤ 1 := by rw [hce, norm_neg]; exact hx
  have hg : ep + PowerSeries.C (c0 - (xT + c0)) * PowerSeries.X ^ 2 = gT ep xT := by
    rw [hce, map_neg, gT]; ring
  have hD := (diffPh K g2 g3 s2 c0 (xT + c0) P l i ep F hP hcub hF hC).1
  obtain ⟨hw, hwI⟩ := wIntegral K c0 (xT + c0) P l i ep F hF hC hn
  rw [hg] at hD hw
  have hg0 : PowerSeries.constantCoeff (gT ep xT) = 1 := by
    rw [gT, map_sub, hC.2.1]; simp
  have hw0 : PowerSeries.constantCoeff (PowerSeries.subst l (wOf (xT + c0) P)) = 0 := by
    have := congrArg PowerSeries.constantCoeff hw
    rw [map_mul, hg0, mul_one] at this
    rw [this]; simp
  generalize PowerSeries.subst l (wOf (xT + c0) P) = wl at hGC hwI hw0
  generalize phE s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l = ph' at hD ⊢
  generalize 3 * (xT + c0) ^ 2 - g2 / 4 = kap at hGC hk
  generalize phO s2 P l = ph at hD ⊢
  generalize gT ep xT = g at hGC hD hg0
  obtain ⟨d, hd⟩ : ∃ d : MvPowerSeries (Fin 2) K,
      d = 1 - MvPowerSeries.C kap * at1 0 wl * at1 1 wl := ⟨_, rfl⟩
  rw [← hd, hLT] at hGC
  have hdI : Integral d := by
    rw [hd]
    exact ParE.integral_sub' Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_one'
      (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (ParE.integral_C' hk)
        (integral_series_at_variable 0 wl hwI)) (integral_series_at_variable 1 wl hwI))
  have hd0 : MvPowerSeries.constantCoeff d = 1 := by
    rw [hd, map_sub, map_mul, map_mul, constantCoeff_series_at_variable 0 wl hw0]; simp
  have hFne : F ≠ 0 := by
    intro h
    have := law_coeff_single hF 0
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hmain : PowerSeries.subst F g * (nu * nu) = at1 0 g * at1 1 g * (d * d) := by
    refine mul_right_cancel₀ (pow_ne_zero 2 hFne) ?_
    linear_combination hGC
  have cF := cc_psubst hF0 hg0
  have cA : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) g) = 1 := cc_psubst (by simp) hg0
  have cB : MvPowerSeries.constantCoeff (at1 (1 : Fin 2) g) = 1 := cc_psubst (by simp) hg0
  have hlog := congrArg fLog hmain
  rw [ParO.fLog_mul cF (by rw [map_mul, hnu0, mul_one]), ParO.fLog_mul hnu0 hnu0,
    ParO.fLog_mul (by rw [map_mul, cA, cB, mul_one]) (by rw [map_mul, hd0, mul_one]),
    ParO.fLog_mul cA cB, ParO.fLog_mul hd0 hd0] at hlog
  have h2 : cob F (2 * (ph' - ph)) = 2 * (cob F ph' - cob F ph) := by
    rw [two_mul, cob_add hF0, cob_sub hF0]; ring
  have h3 := congrArg (cob F) hD
  rw [h2, cob_neg hF0, cob_fLog hF0 hg0] at h3
  have e : cob F ph' - cob F ph = fLog nu - fLog d := by
    refine mul_left_cancel₀ (two_ne (K := K)) ?_
    linear_combination h3 - hlog
  have s := (simeqInt K (Fin 2) _ _ _ _ (simeqLog K (Fin 2) nu hnu0 hnuI).1
    (simeqLog K (Fin 2) d hd0 hdI).1).1
  unfold Simeq at s ⊢
  rw [e]
  simpa using s

theorem cocycle_diff_exp_equiv : CocycleDiffExpEquiv := by
  intro K _ _ _ F H H' hF0 hFi hHH'
  obtain ⟨-, -, -, -, hsub⟩ := equivalence_rules K (Fin 2)
  obtain ⟨hrefl, hsymm, -, hadd, -⟩ := equivalence_rules K (Fin 3)
  have hneg : ∀ a b : MvPowerSeries (Fin 3) K, Simeq a b → Simeq (-a) (-b) := by
    intro a b h
    have h' := hadd b a (-a - b) (-a - b) (hsymm a b h) (hrefl _)
    have e1 : b + (-a - b) = -a := by ring
    have e2 : a + (-a - b) = -b := by ring
    rwa [e1, e2] at h'
  have hsub' : ∀ a b c d : MvPowerSeries (Fin 3) K, Simeq a b → Simeq c d → Simeq (a - c) (b - d) := by
    intro a b c d h1 h2
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact hadd _ _ _ _ h1 (hneg _ _ h2)
  have hX : ∀ j : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) = 0 :=
    fun j => MvPowerSeries.constantCoeff_X j
  have iX : ∀ j : Fin 3, Integral (MvPowerSeries.X j : MvPowerSeries (Fin 3) K) :=
    fun j => integral_mvPowerSeries_X j
  have c3 : MvPowerSeries.constantCoeff (in3 F) = 0 := Formalism.L2.Th1.B.E2.constantCoeff_law_first_two_of_three hF0
  have i3 : Integral (in3 F) := integral_subst_two_variables hFi _ _ (hX 0) (hX 1) (iX 0) (iX 1)
  unfold d1
  refine hsub' _ _ _ _ (hsub' _ _ _ _ ?_ ?_) ?_
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [c3, i3, hX, iX]
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [hX, iX]
  · refine hsub (Fin 3) H H' _ ?_ ?_ hHH' <;> intro j <;> fin_cases j <;> simp [hX, iX]

theorem CubeE_of (hB : BeESim) (hD : CocycleDiffExpEquiv) : CubeE := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 xT yT P l i ep F hW hLaw hI hC hC3 hT
  intro ph'
  have hl0 : PowerSeries.constantCoeff l = 0 := hLaw.2.2.1
  have hcc : PowerSeries.constantCoeff ph' = 0 :=
    (phEDef K s2 (xT + c0) (3 * (xT + c0) ^ 2 - g2 / 4) (wOf (xT + c0) P) l hl0).1
  obtain ⟨hdiv, hsw⟩ := cobRules K F l ph' hLaw hcc
  have hO := (first_level_all_formal_groups K g2 g3 s2 c0 a1 a3 P l i ep F hW hLaw hI hC hC3).2.2.1
  have hBE := hB K g2 g3 s2 c0 a1 a3 xT yT P l i ep F hW hLaw hI hC hC3 hT
  have hDD := hD K F _ _ hLaw.1 hLaw.2.1 hBE
  obtain ⟨-, -, htrans, -, -⟩ := equivalence_rules K (Fin 3)
  have h3 : Simeq (d1 F (cob F ph')) 0 := htrans _ _ _ hDD hO
  exact ⟨hdiv, hsw, h3, by rw [hsw]; exact h3⟩

end Formalism.L2.Th1.B.BeE
end
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.DivLaw

section

section

noncomputable section

namespace Formalism.L2.Th1.B.LDiv

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob)
open Formalism.InvariantFactorPaths.G7.LogarithmEquivalence (integral_mul' integral_one' integral_of_mul_eq_one)
open Formalism.L2.Th1.B.ParE (integral_add' integral_sub' integral_C')
open Formalism.G.LogP (hs2 subst2_subst subst_XX)

section Div

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem div_law {F G : MvPowerSeries (Fin 2) K} {l i : PowerSeries K} (hF : LawLog F l)
    (hi : IsInv l i) (hG : Integral G)
    (hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] G = 0) :
    ∃ n : MvPowerSeries (Fin 2) K, Integral n ∧ G = F * n := by
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have ci : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) i) = 0 := constantCoeff_series_at_variable 0 i hi.1
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)
  have ii : Integral (at1 (0 : Fin 2) i) := integral_series_at_variable 0 i hi.2.1
  obtain ⟨D, hD⟩ : ∃ D, D = MvPowerSeries.subst
      ![at1 (0 : Fin 2) i, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] F := ⟨_, rfl⟩
  have cD : MvPowerSeries.constantCoeff D = 0 := by
    rw [hD]
    exact law_constantCoeff_subst2 F hF.1 _ _ ci c1
  have iD : Integral D := by
    rw [hD]
    exact integral_subst_two_variables hF.2.1 _ _ ci c1 ii i1
  obtain ⟨H, hH⟩ : ∃ H, H = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), D] G := ⟨_, rfl⟩
  have iH : Integral H := by
    rw [hH]
    exact integral_subst_two_variables hG _ _ c0 cD i0 iD
  have hH0 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] H = 0 := by
    have hb := hs2 c0 cz
    rw [hH, subst2_subst G c0 cD hb, MvPowerSeries.subst_X hb, hD, subst2_subst F ci c1 hb,
      MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 0 hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    change MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.subst ![at1 (0 : Fin 2) i, 0] F] G
      = 0
    rw [law_right_zero hF _ ci]
    exact hd
  have hdvd : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ H := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [law_coeff_axis0 H m hm, hH0, map_zero]
  obtain ⟨H1, e1⟩ := hdvd
  have iH1 : Integral H1 := by
    intro n
    have := iH (Finsupp.single 1 1 + n)
    rwa [e1, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul] at this
  have hb := hs2 c0 hF.1
  refine ⟨MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), F] H1,
    integral_subst_two_variables iH1 _ _ c0 hF.1 i0 hF.2.1, ?_⟩
  have e3 : MvPowerSeries.subst ![at1 (0 : Fin 2) i, F] F =
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
    refine law_eq_of_log hF _ _ _ ci hF.1 c1 ?_
    have e4 := law_subst hF (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) (MvPowerSeries.X 1) c0 c1
    rw [subst_XX] at e4
    rw [e4, log_subst_formal_inverse hi 0]
    change -at1 0 l + (at1 0 l + _) = _
    rw [neg_add_cancel_left]
  have e2 : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), F] H = G := by
    rw [hH, subst2_subst G c0 cD hb, MvPowerSeries.subst_X hb, hD, subst2_subst F ci c1 hb,
      MvPowerSeries.subst_X hb, subst_at_variable_eq_subst i 0 hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    change MvPowerSeries.subst ![MvPowerSeries.X 0, MvPowerSeries.subst ![at1 (0 : Fin 2) i, F] F] G
      = G
    rw [e3]
    exact subst_XX G
  rw [← e2, e1, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_X hb]
  rfl

end Div

theorem LDiv_of (hG : GCob) : LDiv := by
  intro K _ _ _ g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hi hC hC3 hT
  obtain ⟨hT1, hT2, nx, ny, na, -⟩ := hT
  have hep := hC.1
  have hep0 := hC.2.1
  have c0' : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1' : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have ci : MvPowerSeries.constantCoeff (at1 (0 : Fin 2) i) = 0 := constantCoeff_series_at_variable 0 i hi.1
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)

  have hX : Integral (ι := Unit) (PowerSeries.X : PowerSeries K) := law_integral_X ()
  have hX2 : Integral (ι := Unit) (PowerSeries.X ^ 2 : PowerSeries K) := by
    rw [pow_two]
    exact integral_mul' hX hX
  have hX3 : Integral (ι := Unit) (PowerSeries.X ^ 3 : PowerSeries K) := by
    rw [pow_succ]
    exact integral_mul' hX2 hX
  have hg0 : PowerSeries.constantCoeff (gT ep xT) = 1 := by simp [gT, hep0]
  have hgi : Integral (ι := Unit) (gT ep xT) :=
    integral_sub' hep (integral_mul' (integral_C' nx) hX2)
  have hinv : (gT ep xT)⁻¹ * gT ep xT = 1 :=
    PowerSeries.inv_mul_cancel _ (by rw [hg0]; exact one_ne_zero)
  have hginv : Integral (ι := Unit) (gT ep xT)⁻¹ := integral_of_mul_eq_one hgi hg0 hinv
  have hth : Integral (ι := Unit) (thT ep xT yT) :=
    integral_mul' (integral_add' hep (integral_mul' (integral_C' ny) hX3)) hginv
  have hth0 : PowerSeries.constantCoeff (thT ep xT yT) = 1 := by
    have e := congrArg PowerSeries.constantCoeff hinv
    rw [map_mul, hg0, mul_one, map_one] at e
    unfold thT
    rw [map_mul, e]
    simp [hep0]
  have hL : Integral (LT ep xT yT a1) :=
    integral_sub' (integral_add' (integral_mul' i1 (integral_series_at_variable 0 _ hth))
      (integral_mul' i0 (integral_series_at_variable 1 _ hth)))
      (integral_mul' (integral_mul' (integral_C' na) i0) i1)

  have hb := hs2 c0' ci
  have eF : MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] F = 0 := by
    refine law_eq_of_log hF _ _ 0 c0' ci cz ?_
    rw [law_subst_zero l hF.2.2.1, log_subst_formal_inverse hi 0]
    exact add_neg_cancel _
  have hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i] (LT ep xT yT a1) = 0 := by
    have e := congrArg (MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), at1 0 i])
      (hG K g2 g3 c0 a1 a3 xT yT P l i ep F hP hF hC hC3 hT1 hT2)
    rw [MvPowerSeries.subst_mul hb, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_mul hb,
      MvPowerSeries.subst_pow hb F, eF, psubst_msubst _ hF.1 hb, eF] at e
    have e5 : PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) (gT ep xT) ≠ 0 := by
      intro h
      rw [PowerSeries.subst_zero_eq_C_constantCoeff, hg0] at h
      simp at h
    rw [MvPowerSeries.subst_pow hb] at e
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul] at e
    rcases mul_eq_zero.1 e with h | h
    · exact absurd h e5
    · exact pow_eq_zero_iff (two_ne_zero) |>.1 h
  obtain ⟨nu, hnu, e⟩ := div_law hF hi hL hd
  refine ⟨nu, hnu, ?_, e⟩

  have a0 : ∀ n : MvPowerSeries (Fin 2) K,
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (MvPowerSeries.X 1 * n) =
      MvPowerSeries.constantCoeff n := by
    intro n
    have := MvPowerSeries.coeff_add_monomial_mul (Finsupp.single (1 : Fin 2) 1) 0 n (1 : K)
    rwa [add_zero, one_mul] at this
  have a1' : ∀ n : MvPowerSeries (Fin 2) K,
      MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (MvPowerSeries.X 0 * n) = 0 := by
    intro n
    have hx : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ∣ MvPowerSeries.X 0 * n :=
      Dvd.intro _ rfl
    exact MvPowerSeries.X_dvd_iff.1 hx _ (by simp)
  have h1 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (LT ep xT yT a1) = 1 := by
    unfold LT
    have e6 : MvPowerSeries.C a1 * MvPowerSeries.X 0 * MvPowerSeries.X 1 =
        (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) * (MvPowerSeries.C a1 * MvPowerSeries.X 1) := by
      ring
    rw [e6, map_sub, map_add (f := _), a0, a1', a1', add_zero, sub_zero]
    exact (Formalism.G.LogP.constantCoeff_subst_of_zero (σ := Unit) (thT ep xT yT)
      (b := fun _ => (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) (fun _ => c0')).trans hth0
  have h2 : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) (F * nu) =
      MvPowerSeries.constantCoeff nu := by
    classical
    rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
    simp [Finset.Nat.antidiagonal_succ, law_coeff_single hF 1, hF.1]
  rw [e, h2] at h1
  exact h1

end Formalism.L2.Th1.B.LDiv
end
end
end

-- Source module: Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalE

section

@[expose] public section

namespace Formalism.L2.Th1.B

theorem wAdd : WAdd := SAdd.weierstrass_addition_holds
theorem wPrimeU : WPrimeU := GCob.weierstrass_derivative_unit_holds
theorem gCob : GCob := GCob.GCob_of wAdd wPrimeU
theorem lDiv : LDiv := LDiv.LDiv_of gCob
theorem beESim : BeESim := BeE.BeESim_of gCob lDiv
theorem first_cocycle_simeq_zero : CocycleDiffExpEquiv := BeE.cocycle_diff_exp_equiv
theorem cubeE : CubeE := BeE.CubeE_of beESim first_cocycle_simeq_zero

end Formalism.L2.Th1.B
end
end
