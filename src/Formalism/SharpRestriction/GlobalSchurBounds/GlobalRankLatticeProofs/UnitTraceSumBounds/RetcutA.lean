module

public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.PhNormOfUnits
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormLimit
public import Formalism.PeriodIntegrals.PhNormUnits
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffVar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsSubstitution
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.SimeqSubst1
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffFormalSMul
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TendstoCoeffOfCont
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Field.Instances
import Mathlib.RingTheory.WittVector.IsPoly

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.StepUnitsOf

section

@[expose] public section

noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

theorem stepUnits_of (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense) : StepUnits := by
  intro p _ l ex ph S hS α hα h1 h2
  obtain ⟨hex0, hinv, hp2, h22, hswap, -, -, hint_r, hIA, -, hprod, -, hB, hNorm⟩ := hS
  have hph : PowerSeries.constantCoeff ph = 0 := by
    have h2n : ‖(2 : ℂ_[p])‖ = 1 := norm_two_of hp2
    have h2' := hNorm ((2 : ℂ_[p]), (2 : ℂ_[p])) h22 h2n h2n
    dsimp only at h2'
    exact ph_const_of h2' hex0 hinv
  obtain ⟨n, hn⟩ := hprod α hα
  have hU := hNorm α hα h1 h2
  have hc : α.1 ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hnorm : ‖PI.PhNormUnits.zc n‖ = 1 := by rw [← hn, norm_mul, h1, h2, one_mul]
  obtain ⟨m, hm⟩ := zc_inv_of n hnorm
  have hinvc : α.1⁻¹ = α.2 * PI.PhNormUnits.zc m := by
    apply inv_eq_of_mul_eq_one_right
    rw [← mul_assoc, hn, hm]
  have h1v : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have hd : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex α.2 (PI.PhNormUnits.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
    have h := hint_r _ (hswap α hα)
    rw [Prod.fst_swap] at h
    exact h
  have hw : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex α.1⁻¹ (PI.PhNormUnits.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
    rw [hinvc, ← mulBy_mulBy hex0 hinv α.2 (PI.PhNormUnits.zc m) (PI.PhNormUnits.Xv (1 : Fin 2)) h1v]
    exact int_mulBy_of hSub hex0 hinv α.2 hd _
      (constantCoeff_formalSMul hex0 hinv _ _ h1v)
      (int_mulBy_zp hSub hex0 hinv hC hD hIA _ h1v
        (int_X _) m)
  have step1 := units_i hE hSub hex0 hinv hIA α.1 (α.1 * α.2) hU
  have step2 := units_ii hE hSub hC hD hex0 hinv hph hIA hB α.1 α.2 n hn
  exact units_iv hE hSub hex0 hinv α.1 α.2 hc hw (sTrans hE step1 step2)

theorem stepAll_of (hE : CalcEquiv) (hSub : CalcSubst) : StepAll := by
  intro p _ l ex ph S hS hU α hα
  obtain ⟨hex0, hinv, -, -, hswap, -, -, hint_r, hIA, -, -, hdec, hB, -⟩ := hS
  obtain ⟨β, hβ, γ, hγ, hb1, hb2, hg1, hg2, rfl⟩ := hdec α hα
  have h0 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have h1 : MvPowerSeries.constantCoeff (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 :=
    constantCoeff_var _
  have i0 : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.Xv (0 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) := int_X _
  have i1 : PI.PhNormUnits.IntegralMv (PI.PhNormUnits.Xv (1 : Fin 2) : MvPowerSeries (Fin 2) ℂ_[p]) := int_X _
  have hI1 : ∀ δ ∈ S, ∀ x : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff x = 0 →
      PI.PhNormUnits.IntegralMv x → PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex δ.1 x) :=
    fun δ hδ x hx0 hx => int_mulBy_of hSub hex0 hinv δ.1 (hint_r δ hδ) x hx0 hx
  have hI2 : ∀ δ ∈ S, ∀ x : MvPowerSeries (Fin 2) ℂ_[p], MvPowerSeries.constantCoeff x = 0 →
      PI.PhNormUnits.IntegralMv x → PI.PhNormUnits.IntegralMv (PI.PhNormUnits.mulBy l ex δ.2 x) :=
    fun δ hδ x hx0 hx => by
      have h := hint_r _ (hswap δ hδ)
      rw [Prod.fst_swap] at h
      exact int_mulBy_of hSub hex0 hinv δ.2 h x hx0 hx
  have c0 : ∀ (c : ℂ_[p]) (x : MvPowerSeries (Fin 2) ℂ_[p]), MvPowerSeries.constantCoeff x = 0 →
      MvPowerSeries.constantCoeff (PI.PhNormUnits.mulBy l ex c x) = 0 :=
    fun c x hx => constantCoeff_formalSMul hex0 hinv c x hx
  show PI.PhNormUnits.Simeq (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.mulBy l ex (β.1 + γ.1) (PI.PhNormUnits.Xv 0)) (PI.PhNormUnits.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
    (PI.PhNormUnits.be l ex ph (PI.PhNormUnits.Xv 0) (PI.PhNormUnits.mulBy l ex (β.2 + γ.2) (PI.PhNormUnits.Xv 1)))
  rw [← add_mulBy hex0 hinv β.1 γ.1 _ h0,
    ← add_mulBy hex0 hinv β.2 γ.2 _ h1]
  have L := be_add_left hSub hex0 hinv hB (PI.PhNormUnits.mulBy l ex β.1 (PI.PhNormUnits.Xv 0))
    (PI.PhNormUnits.mulBy l ex γ.1 (PI.PhNormUnits.Xv 0)) (PI.PhNormUnits.Xv 1) (c0 _ _ h0) (c0 _ _ h0) h1
    (hI1 β hβ _ h0 i0) (hI1 γ hγ _ h0 i0) i1
  have R := be_add_right hSub hex0 hinv hB (PI.PhNormUnits.mulBy l ex β.2 (PI.PhNormUnits.Xv 1))
    (PI.PhNormUnits.mulBy l ex γ.2 (PI.PhNormUnits.Xv 1)) (PI.PhNormUnits.Xv 0) (c0 _ _ h1) (c0 _ _ h1) h0
    (hI2 β hβ _ h1 i1) (hI2 γ hγ _ h1 i1) i0
  exact sTrans hE L (sTrans hE
    (sAdd hE (hU β hβ hb1 hb2) (hU γ hγ hg1 hg2)) (sSymm hE R))

end PI.PhNormUnits.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.TraceAt

section

@[expose] public section

noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

variable {p : ℕ} [Fact p.Prime]

section

variable (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense) (hZ : CalcZpScale)
variable {l ex ph : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X) (hph : PowerSeries.constantCoeff ph = 0)
  (hIA : IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
  (hB : Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)))

include hE hSub hC hD hZ hex0 hinv hph hIA hB in
theorem trace_at (c d : ℂ_[p]) (hc : IntegralMv (mulBy l ex c (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (hd : IntegralMv (mulBy l ex d (Xv ()) : MvPowerSeries Unit ℂ_[p])) (t : ℤ_[p]) (ht : c + d = zc t)
    (hsw : Simeq (be l ex ph (mulBy l ex c (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex d (Xv 1))))
    (hU2 : Simeq (phAt ph (mulBy l ex 2 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (2 * 2) * phAt ph (Xv ())))
    (h2inv : ∃ h : ℤ_[p], 2 * zc h = 1) {τ : Type} (w : MvPowerSeries τ ℂ_[p])
    (w0 : MvPowerSeries.constantCoeff w = 0) (wI : IntegralMv w) :
    Simeq (be l ex ph w (mulBy l ex c w)) (MvPowerSeries.C (c + d) * phAt ph w) := by
  have hw2 : ∀ i, MvPowerSeries.constantCoeff (![w, w] i) = 0 := by
    intro i; fin_cases i <;> simpa using w0
  have hcw0 : MvPowerSeries.constantCoeff (mulBy l ex c w) = 0 := constantCoeff_formalSMul hex0 hinv c w w0
  have hdw0 : MvPowerSeries.constantCoeff (mulBy l ex d w) = 0 := constantCoeff_formalSMul hex0 hinv d w w0
  have hcw : IntegralMv (mulBy l ex c w) := int_mulBy_of hSub hex0 hinv c hc w w0 wI
  have hdw : IntegralMv (mulBy l ex d w) := int_mulBy_of hSub hex0 hinv d hd w w0 wI
  have S1 : Simeq (be l ex ph (mulBy l ex c w) w) (be l ex ph w (mulBy l ex d w)) := by
    have e := simeq_subst2 hSub hex0 hinv w w w0 w0 wI wI hsw
    rw [sb_be (![w, w]) hw2 hex0 hinv ph _ _ (constantCoeff_formalSMul hex0 hinv c _ (constantCoeff_var 0)) (constantCoeff_var 1),
      sb_be (![w, w]) hw2 hex0 hinv ph _ _ (constantCoeff_var 0) (constantCoeff_formalSMul hex0 hinv d _ (constantCoeff_var 1)),
      sb_mulBy (![w, w]) hw2 hex0 hinv c _ (constantCoeff_var 0), sb_mulBy (![w, w]) hw2 hex0 hinv d _ (constantCoeff_var 1),
      sb_X (![w, w]) hw2, sb_X (![w, w]) hw2] at e
    simpa using e
  have A : Simeq (be l ex ph w (mulBy l ex c w)) (be l ex ph w (mulBy l ex d w)) := by
    rw [be_comm]; exact S1
  have S3 : Simeq (be l ex ph w (mulBy l ex (zc t) w))
      (be l ex ph w (mulBy l ex c w) + be l ex ph w (mulBy l ex d w)) := by
    rw [← ht, ← add_mulBy hex0 hinv c d w w0]
    exact be_add_right hSub hex0 hinv hB _ _ _ hcw0 hdw0 w0 hcw hdw wI
  have S4 := be_zp hE hSub hex0 hinv hB hC hD hph hIA w w w0 w0 wI wI t
  have S5 : Simeq (be l ex ph w w) (MvPowerSeries.C 2 * phAt ph w) := by
    have n2 := PI.PhNormUnits.UnitaryGroupMassFormula.norm_at hSub hex0 hinv 2 (2 * 2) hU2 w w0 wI
    have e : be l ex ph w w = phAt ph (mulBy l ex 2 w) - phAt ph w - phAt ph w := by
      rw [be, add_self hex0 hinv w w0]
    rw [e]
    refine sTrans hE (sSub hE (sSub hE n2 (sRefl hE _)) (sRefl hE _)) (sOfEq hE ?_)
    simp only [map_mul, map_ofNat]
    ring
  have T1 : Simeq (MvPowerSeries.C 2 * be l ex ph w (mulBy l ex c w))
      (MvPowerSeries.C 2 * (MvPowerSeries.C (c + d) * phAt ph w)) := by
    have e1 : MvPowerSeries.C (2 : ℂ_[p]) * be l ex ph w (mulBy l ex c w) =
        be l ex ph w (mulBy l ex c w) + be l ex ph w (mulBy l ex c w) := by
      simp only [map_ofNat]; ring
    rw [e1]
    refine sTrans hE (sAdd hE (sRefl hE _) A) (sTrans hE (sSymm hE S3) (sTrans hE S4 ?_))
    refine sTrans hE (hZ p τ _ _ t S5) (sOfEq hE ?_)
    rw [← ht]
    ring
  obtain ⟨h, hh⟩ := h2inv
  have T2 := hZ p τ _ _ h T1
  refine sTrans hE (sOfEq hE ?_) (sTrans hE T2 (sOfEq hE ?_))
  · rw [← mul_assoc, ← map_mul, mul_comm (zc h), hh, map_one, one_mul]
  · rw [← mul_assoc, ← map_mul, mul_comm (zc h), hh, map_one, one_mul]

include hE hSub hex0 hinv in
theorem sum_at (β γ : ℂ_[p] × ℂ_[p]) (iγ : IntegralMv (mulBy l ex γ.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (hsw : Simeq (be l ex ph (mulBy l ex β.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
      (be l ex ph (Xv 0) (mulBy l ex β.2 (Xv 1))))
    (htr : Simeq (be l ex ph (Xv ()) (mulBy l ex (β.2 * γ.1) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (β.2 * γ.1 + β.1 * γ.2) * phAt ph (Xv ())))
    (nβ : Simeq (phAt ph (mulBy l ex β.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (β.1 * β.2) * phAt ph (Xv ())))
    (nγ : Simeq (phAt ph (mulBy l ex γ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (γ.1 * γ.2) * phAt ph (Xv ()))) :
    Simeq (phAt ph (mulBy l ex (β.1 + γ.1) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C ((β.1 + γ.1) * (β.2 + γ.2)) * phAt ph (Xv ())) := by
  have hX0 : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := constantCoeff_var ()
  have hg0 : MvPowerSeries.constantCoeff (mulBy l ex γ.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
    constantCoeff_formalSMul hex0 hinv γ.1 _ hX0
  have hb0 : MvPowerSeries.constantCoeff (mulBy l ex β.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
    constantCoeff_formalSMul hex0 hinv β.1 _ hX0
  have hs2 : ∀ i, MvPowerSeries.constantCoeff
      (![Xv (), mulBy l ex γ.1 (Xv ())] i : MvPowerSeries Unit ℂ_[p]) = 0 := by
    intro i; fin_cases i
    · simp [hX0]
    · simpa using hg0
  have S1 : Simeq (be l ex ph (mulBy l ex β.1 (Xv ())) (mulBy l ex γ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (be l ex ph (Xv ()) (mulBy l ex (β.2 * γ.1) (Xv ()))) := by
    have e := simeq_subst2 hSub hex0 hinv (Xv ()) (mulBy l ex γ.1 (Xv ())) hX0 hg0 (int_X ()) iγ hsw
    rw [sb_be _ hs2 hex0 hinv ph _ _ (constantCoeff_formalSMul hex0 hinv β.1 _ (constantCoeff_var 0)) (constantCoeff_var 1),
      sb_be _ hs2 hex0 hinv ph _ _ (constantCoeff_var 0) (constantCoeff_formalSMul hex0 hinv β.2 _ (constantCoeff_var 1)),
      sb_mulBy _ hs2 hex0 hinv β.1 _ (constantCoeff_var 0), sb_mulBy _ hs2 hex0 hinv β.2 _ (constantCoeff_var 1),
      sb_X _ hs2, sb_X _ hs2] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    rwa [mulBy_mulBy hex0 hinv β.2 γ.1 _ hX0] at e
  have e : phAt ph (mulBy l ex (β.1 + γ.1) (Xv ())) =
      be l ex ph (mulBy l ex β.1 (Xv ())) (mulBy l ex γ.1 (Xv ())) +
        phAt ph (mulBy l ex β.1 (Xv ())) + phAt ph (mulBy l ex γ.1 (Xv ())) := by
    rw [be, add_mulBy hex0 hinv β.1 γ.1 _ hX0]
    ring
  rw [e]
  refine sTrans hE (sAdd hE (sAdd hE (sTrans hE S1 htr) nβ) nγ) (sOfEq hE ?_)
  simp only [map_add (f := _), map_mul]
  ring

end

end PI.PhNormUnits.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.NormUnitsOfCalculation

section

@[expose] public section

noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

theorem stepTrace_of (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
    (hZ : CalcZpScale) : StepTrace := by
  intro p _ l ex ph S hH hA δ hδ
  obtain ⟨hex0, hinv, hp2, h22, hswap, -, -, hintS, hIA, htr, -, -, hB, hunit⟩ := hH
  have hU2 := hunit ((2 : ℂ_[p]), (2 : ℂ_[p])) h22 (norm_two_of hp2) (norm_two_of hp2)
  have hph := ph_const_of hU2 hex0 hinv
  obtain ⟨t, ht⟩ := htr δ hδ
  have h2inv : ∃ h : ℤ_[p], 2 * zc h = 1 := by
    obtain ⟨h, hh⟩ := zc_inv_of (2 : ℤ_[p]) (by rw [zc_two]; exact norm_two_of hp2)
    exact ⟨h, by rwa [zc_two] at hh⟩
  exact trace_at hE hSub hC hD hZ hex0 hinv hph hIA hB δ.1 δ.2 (hintS δ hδ) (hintS δ.swap (hswap δ hδ)) t ht
    (hA δ hδ) hU2 h2inv (Xv ()) (constantCoeff_var ()) (int_X ())

theorem stepSum_of (hE : CalcEquiv) (hSub : CalcSubst) : StepSum := by
  intro p _ l ex ph S hH hA hT α hα
  obtain ⟨hex0, hinv, -, -, hswap, -, hmul, hintS, -, -, -, hdec, -, hunit⟩ := hH
  obtain ⟨β, hβ, γ, hγ, hb1, hb2, hg1, hg2, rfl⟩ := hdec α hα
  exact sum_at hE hSub hex0 hinv β γ (hintS γ hγ) (hA β hβ) (hT (β.swap * γ) (hmul β.swap (hswap β hβ) γ hγ))
    (hunit β hβ hb1 hb2) (hunit γ hγ hg1 hg2)

theorem target_of_calc (hE : CalcEquiv) (hSub : CalcSubst) (hC : CalcClosed) (hD : NatDense)
    (hZ : CalcZpScale) : Target :=
  target_of_steps (stepUnits_of hE hSub hC hD) (stepAll_of hE hSub) (stepTrace_of hE hSub hC hD hZ)
    (stepSum_of hE hSub)

theorem norm_units_of_calculation : Target :=
  target_of_calc norm_units_equivalence norm_units_substitution norm_units_closed_form natCast_dense_p_adic norm_units_zp_scaling

end PI.PhNormUnits.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.PhNormUnits

section

@[expose] public section

theorem phase_norm_units : PI.PhNormUnits.Target := PI.PhNormUnits.UnitaryGroupMassFormula.norm_units_of_calculation
end
end

-- Source module: Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.RetcutA

section

@[expose] public section

namespace Formalism.MainNotions.Ext.CutA

theorem phNormOfUnits_holds : PhNormOfUnits := by
  intro p _ g S hok
  exact phase_norm_units p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

theorem phNormClosed_holds : PhNormClosed := by
  intro p _ g S hok
  exact phase_norm_limit_target p g.l g.ex g.ph S hok.2.2.1 hok.2.2.2

end Formalism.MainNotions.Ext.CutA
end
end
