module

public import Formalism.PeriodIntegrals.GTLower
public import Formalism.PeriodIntegrals.HwIrred
public import Formalism.PeriodIntegrals.SchurFock
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.Params
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Capelli2_2
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionAdj
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionBrInt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionIo
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionLift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.InterlacingDefectEqCard
public import Formalism.PeriodIntegrals.GTDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.CardEraseIccMin
import Mathlib.Algebra.Order.Star.Int
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.EvalInitMinorNormLe

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.Assembly

section

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem ioIntegral_of (hZ : CapelliZ) (hL : LiftMod) (hV : ZScalarVanish) : IoIntegral := by
  intro n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨Z, hZi, hZa⟩ := hZ n N h lam sg hI
  obtain ⟨m, hm, hd⟩ := hL n N h lam sg hI io0 hE hx hW s hs
  obtain ⟨f', hf', hZf⟩ := hZi m hm
  refine ⟨f', hf', ?_⟩
  have hsC : MvPolynomial.map (Int.castRingHom ℂ) s ∈ nablaSq ℂ n sg :=
    Formalism.GradedWeylDivisibility.dualWeylMap ℤ ℂ (Int.castRingHom ℂ) n n sg.natW s hs
  have hO : OtherPart h lam sg ≤ LinearMap.ker Z := by
    unfold OtherPart
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun hne => iSup_le fun hw =>
      iSup_le fun φ => iSup_le fun hφ => ?_
    rintro _ ⟨t, ht, rfl⟩
    rw [LinearMap.mem_ker, hZa mu hmu φ hφ t ht, hV n N h lam sg mu hI hmu hne hw, Int.cast_zero, zero_smul]
  have h0 := hO hd
  rw [LinearMap.mem_ker, map_sub, hZf, hZa sg hI io0 hE _ hsC] at h0
  have hz : zScalar h lam sg sg = cBr h lam sg := rfl
  rw [hz] at h0
  rw [map_smul]
  exact (sub_eq_zero.mp h0).symm

theorem sqAct_smul {k : ℕ} (mu : DomWeight k) (g : GL (Fin k) ℂ) (c : ℂ)
    (x : MvPolynomial (Fin k × Fin k) ℂ) : sqAct ℂ k mu g (c • x) = c • sqAct ℂ k mu g x := by
  rw [sqAct, sqAct, map_smul, smul_comm]

theorem gTLower_of_steps (hN : Numbers) (hX : XiFacts) (hE : IoExists) (hP4 : IoIntegral)
    (hA : AdjointBr) (hB : BrIntegral) : PI.GTLower := by
  intro n N h lam sg hI
  obtain ⟨hc0, hcB, hdeg⟩ := hN n N h lam sg hI
  obtain ⟨hxi0, -⟩ := hX n N h lam sg hI
  obtain ⟨io0, ⟨hE1, hE2⟩, hx, hW⟩ := hE n N h lam sg hI
  let c : ℂ := ((cBr h lam sg : ℤ) : ℂ)
  let io := c • io0
  have hio : ∀ x, io x = c • io0 x := fun x => rfl
  have I2 : ∀ s ∈ nablaSq ℂ n sg, io s ∈ nablaSq ℂ N lam := fun s hs =>
    Submodule.smul_mem _ _ (hE1 s hs)
  have I3 : ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n sg,
      io (sqAct ℂ n sg g s) = sqAct ℂ N lam (embGL ℂ n N h g) (io s) := by
    intro g s hs
    rw [hio, hio, hE2 g s hs, sqAct_smul]
  have I4 : io (extremal ℂ n sg) = c • xi ℂ h lam sg := by rw [hio, hx]
  have I5 : LastWeight lam sg io := by
    intro a s hs
    rw [hio, sqAct_smul, hW a s hs, smul_comm]
  have I1 : ∀ s ∈ nablaSq ℤ n sg, ∃ f ∈ nablaSq ℤ N lam,
      io (MvPolynomial.map (Int.castRingHom ℂ) s) = MvPolynomial.map (Int.castRingHom ℂ) f := by
    intro s hs
    obtain ⟨f, hf, hf'⟩ := hP4 n N h lam sg hI io0 ⟨hE1, hE2⟩ hx hW s hs
    exact ⟨f, hf, by rw [hio, ← map_smul]; exact hf'⟩
  obtain ⟨I6, br, hrest, hT⟩ := hA n N h lam sg hI io ⟨I2, I3⟩ I4 I5
  have B1 := hB n N h lam sg hI io br I1 I2 hrest.1 hT
  exact ⟨hc0, hcB, hxi0, hdeg, io, br, ⟨I1, I2, I3, I4, I5, I6⟩, ⟨B1, hrest⟩, hT⟩

end PI.WGL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinTopCoefficient.NumMore

section

@[expose] public section

noncomputable section

namespace PI.GTNum

open Formalism.BasicNotions PI Finset

variable {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)

theorem sg_le_top (hI : Interlace h lam sg) (j : Fin n) : sg.w j ≤ lam.w ⟨0, by omega⟩ :=
  le_trans (hI j).1 (lam.anti (Fin.mk_le_mk.2 (Nat.zero_le _)))

theorem mem_R_bounds_top (i : Fin n) (v : ℤ) (hv : v ∈ Rset h lam sg i) :
    lam.w ⟨N - 1, by omega⟩ ≤ v ∧ v ≤ lam.w ⟨0, by omega⟩ := by
  unfold Rset at hv
  rw [Finset.mem_Icc] at hv
  have h1 := lam_le_last h lam (i.1 + 1) (by omega)
  have h2 : lam.w ⟨i.1, by omega⟩ ≤ lam.w ⟨0, by omega⟩ := lam.anti (Fin.mk_le_mk.2 (Nat.zero_le _))
  have h5 := min_le_left (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg)
  constructor <;> omega

theorem cBr_ne_zero (hI : Interlace h lam sg) : cBr h lam sg ≠ 0 := by
  unfold cBr
  refine Finset.prod_ne_zero_iff.2 (fun i _ => Finset.prod_ne_zero_iff.2 (fun v hv =>
    Finset.prod_ne_zero_iff.2 (fun j _ => ?_)))
  have hvs : v ≠ sg.w i := Finset.ne_of_mem_erase hv
  have hvR := Finset.mem_of_mem_erase hv
  unfold Rset at hvR
  rw [Finset.mem_Icc] at hvR
  have h5 := min_le_left (lam.w ⟨i.1, by omega⟩) (lam.w ⟨i.1 + 1, by omega⟩ + D0 h lam sg)
  rcases lt_trichotomy j.1 i.1 with hji | hji | hji
  · have a1 : lam.w ⟨i.1, by omega⟩ ≤ lam.w ⟨j.1 + 1, by omega⟩ := lam.anti (Fin.mk_le_mk.2 (by omega))
    have a2 := (hI j).2
    omega
  · have e : j = i := Fin.ext hji
    subst e
    omega
  · have a1 : lam.w ⟨j.1, by omega⟩ ≤ lam.w ⟨i.1 + 1, by omega⟩ := lam.anti (Fin.mk_le_mk.2 (by omega))
    have a2 := (hI j).1
    omega

theorem abs_cBr_le_top (hI : Interlace h lam sg) :
    |cBr h lam sg| ≤ (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^
      (n * ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card) := by
  unfold cBr
  rw [← prod_pow_pow]
  refine abs_prod_le_prod _ _ _ (fun i _ => ?_)
  refine abs_prod_le_pow _ _ _ (fun v hv => ?_)
  have hc : ((lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ n) =
      (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ (univ : Finset (Fin n)).card := by
    rw [Finset.card_univ, Fintype.card_fin]
  rw [hc]
  refine abs_prod_le_pow _ _ _ (fun j _ => ?_)
  have hv' := mem_R_bounds_top h lam sg i v (Finset.mem_of_mem_erase hv)
  have hs1 := last_le_sg h lam sg hI j
  have hs2 := sg_le_top h lam sg hI j
  have hi := i.2
  have hj := j.2
  rw [abs_le]
  constructor <;> omega

theorem abs_cBr_le_cBd (hI : Interlace h lam sg) :
    |((cBr h lam sg : ℤ) : ℝ)| ≤ cBd h lam sg := by
  set K : ℕ := ∑ i : Fin n, ((Rset h lam sg i).erase (sg.w i)).card with hK
  have hD1 : (N : ℤ) * D1 h lam sg = ((N * K : ℕ) : ℤ) := by
    rw [interlacing_defect_eq_card h lam sg hI, ← hK, Nat.cast_mul]
  have hN : 0 < N := by omega
  have hsp : lam.spread = lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + N := by
    unfold DomWeight.spread
    rw [dite_eq_left hN]
  have hlast := lam_le_last h lam 0 (by omega)
  have hb := abs_cBr_le_top h lam sg hI
  rw [← hK] at hb
  have hb2 : (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ (n * K) ≤
      (2 * lam.spread) ^ (N * K) := by
    calc (lam.w ⟨0, by omega⟩ - lam.w ⟨N - 1, by omega⟩ + (n : ℤ)) ^ (n * K)
        ≤ (2 * lam.spread) ^ (n * K) := by
          apply pow_le_pow_left₀ (by omega)
          rw [hsp]
          omega
      _ ≤ (2 * lam.spread) ^ (N * K) := by
          apply pow_le_pow_right₀ (by rw [hsp]; omega)
          exact Nat.mul_le_mul_right K (by omega)
  unfold cBd
  rw [hD1, Int.cast_natCast, Real.rpow_natCast, ← Int.cast_abs]
  exact_mod_cast le_trans hb hb2

theorem degZ_eq : degZ lam sg = lam.w ⟨0, by omega⟩ - D0 h lam sg := by
  subst h
  unfold degZ wsum D0
  rw [Fin.sum_univ_succ, Finset.sum_sub_distrib]
  have e1 : ∑ i : Fin n, lam.w i.succ = ∑ i : Fin n, lam.w ⟨i.1 + 1, by omega⟩ := rfl
  have e0 : lam.w 0 = lam.w ⟨0, by omega⟩ := rfl
  rw [e1, e0]
  ring

end PI.GTNum
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionNum

section

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem numbers_dominant_large : Numbers := by
  intro n N h lam sg hI
  exact ⟨PI.GTNum.cBr_ne_zero h lam sg hI, PI.GTNum.abs_cBr_le_cBd h lam sg hI,
    PI.GTNum.degZ_eq h lam sg⟩

theorem scalar_vanishing_criterion : ZScalarVanish := by
  intro n N h lam sg mu hsg hmu hne hw
  have hsum : (∑ i : Fin n, mu.w i) = ∑ i : Fin n, sg.w i := by
    unfold wsum at hw
    exact hw
  have hD : D0 h lam mu = D0 h lam sg := by
    unfold D0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hsum]
  obtain ⟨i, hi⟩ : ∃ i, mu.w i ≠ sg.w i := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  have hmem : mu.w i ∈ Rset h lam sg i := by
    have hm := PI.GTNum.sg_mem_R h lam mu hmu i
    unfold Rset at hm ⊢
    rw [hD] at hm
    exact hm
  unfold zScalar
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, hmem⟩)
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  ring

end PI.WGL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionXi

section

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem xi_coefficient_facts : XiFacts := by
  intro n N h lam sg hI
  refine ⟨XiB.xi_ne h lam sg, XiB.xi_mem h lam sg hI, ?_, ?_, ?_, ?_⟩
  · intro g hlow hdiag
    exact XiB.xi_unitri h lam sg g hlow hdiag
  · intro t
    exact XiB.xi_torus h lam sg hI t
  · intro a
    exact XiB.xi_last h lam sg hI a
  · intro x hx
    exact XiB.xi_unitary h lam sg x hx

end PI.WGL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.GTLowerOf

section

@[expose] public section

noncomputable section

namespace PI.WGL

theorem gTLower_of (h2 : Formalism.BasicNotions.FactDelDualNabla) (h3 : PI.HwIrred) (h4 : PI.GTBranch)
    (h5 : PI.SchurFock) : PI.GTLower := by
  have hN : Numbers := numbers_dominant_large
  have hX : XiFacts := xi_coefficient_facts
  have hZ : CapelliZ := capelli_scalar_identity
  have hV : ZScalarVanish := scalar_vanishing_criterion
  exact gTLower_of_steps hN hX (ioExists_of h3 h4 hX)
    (ioIntegral_of hZ (liftMod_of h3 h4 hZ hV hN hX) hV)
    (adjointBr_of h3 h5 hN hX) (brIntegral_of h2 h3)

end PI.WGL
end
end
end
