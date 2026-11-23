module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalLogCoeffMemOfSubOneMemDpStatement
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DlogEqSumLinearCoefficientsFormExplicitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusFormalLogSubSmulIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodFormalLogLiftCharacterSeriesStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerTensorStatement
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.Cob1FormalLogMapMemKer

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
  GlobalTheory.FormalCalc

namespace GlobalTheory.CobLog

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {d : ℕ}

theorem hasSubst_inl : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_inr : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem map_inL (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inL f) = inL (map φ f) := by
  unfold inL
  rw [map_subst hasSubst_inl]
  simp

theorem map_inR (φ : R →+* S) (f : MvPowerSeries (Fin d) R) : map φ (inR f) = inR (map φ f) := by
  unfold inR
  rw [map_subst hasSubst_inr]
  simp

theorem constantCoeff_subst_one {σ τ : Type} {a : σ → MvPowerSeries τ R} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {f : MvPowerSeries σ R} (hf : constantCoeff f = 1) :
    constantCoeff (subst a f) = 1 := by
  rw [GlobalTheory.FormalCalc.constantCoeff_subst_of_zero ha ha0, hf, map_one]

theorem constantCoeff_inL {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 1) :
    constantCoeff (inL f) = 1 :=
  constantCoeff_subst_one hasSubst_inl (fun _ => constantCoeff_X _) hf

theorem constantCoeff_inR {f : MvPowerSeries (Fin d) R} (hf : constantCoeff f = 1) :
    constantCoeff (inR f) = 1 :=
  constantCoeff_subst_one hasSubst_inr (fun _ => constantCoeff_X _) hf

end SlopeTestRemainingChoices

theorem cob1_formalLog_mem_ker : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ)
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ' i) = 0) →
    ∀ g : MvPowerSeries (Fin d) B, constantCoeff g = 1 →
    subst (fun i => map θ (μ' i)) (map θ g) = inL (map θ g) * inR (map θ g) →
    In (RingHom.ker θ) (cob1 (up Q μ') (formalLog (map (algebraMap B Q) g))) := by
  intro p _ B O Q _ _ _ _ _ θ hF d μ' hμ g hg hmul
  have hsμ : HasSubst μ' := hasSubst_of_constantCoeff_zero hμ
  have hμQ : ∀ i, constantCoeff (up Q μ' i) = 0 := fun i => by
    simp [up, hμ i]
  have hsμQ : HasSubst (up Q μ') := hasSubst_of_constantCoeff_zero hμQ
  set a : MvPowerSeries (Fin d ⊕ Fin d) B := subst μ' g with ha_def
  set b : MvPowerSeries (Fin d ⊕ Fin d) B := inL g * inR g with hb_def
  have ha1 : constantCoeff a = 1 := constantCoeff_subst_one hsμ hμ hg
  have hbL : constantCoeff (inL g) = 1 := constantCoeff_inL hg
  have hbR : constantCoeff (inR g) = 1 := constantCoeff_inR hg
  have hb1 : constantCoeff b = ((1 : Bˣ) : B) := by simp [hb_def, hbL, hbR]
  set h : MvPowerSeries (Fin d ⊕ Fin d) B := a * invOfUnit b 1 with hh_def
  have hab : a = h * b := by
    rw [hh_def, mul_assoc, invOfUnit_mul b 1 hb1, mul_one]
  have hh1 : constantCoeff h = 1 := by
    rw [hh_def, map_mul, ha1, constantCoeff_invOfUnit]
    simp

  have hG : constantCoeff (map (algebraMap B Q) g) = 1 := by simp [hg]
  have key : cob1 (up Q μ') (formalLog (map (algebraMap B Q) g)) =
      formalLog (map (algebraMap B Q) h) := by
    unfold cob1
    have e1 : subst (up Q μ') (formalLog (map (algebraMap B Q) g)) =
        formalLog (map (algebraMap B Q) a) := by
      rw [subst_formalLog hsμQ hG, ha_def, map_subst hsμ]
      rfl
    have e2 : inL (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inL g)) := by
      rw [map_inL]
      exact subst_formalLog hasSubst_inl hG
    have e3 : inR (formalLog (map (algebraMap B Q) g)) = formalLog (map (algebraMap B Q) (inR g)) := by
      rw [map_inR]
      exact subst_formalLog hasSubst_inr hG
    have hmh : constantCoeff (map (algebraMap B Q) h) = 1 := by simp [hh1]
    have hmL : constantCoeff (map (algebraMap B Q) (inL g)) = 1 := by simp [hbL]
    have hmR : constantCoeff (map (algebraMap B Q) (inR g)) = 1 := by simp [hbR]
    have e4 : formalLog (map (algebraMap B Q) a) = formalLog (map (algebraMap B Q) h) +
        formalLog (map (algebraMap B Q) (inL g)) + formalLog (map (algebraMap B Q) (inR g)) := by
      rw [hab, hb_def, ← mul_assoc, map_mul, map_mul,
        formalLog_mul (by rw [map_mul, hmh, hmL, mul_one]) hmR, formalLog_mul hmh hmL]
    rw [e1, e2, e3, e4]
    abel

  have hθb : IsUnit (map θ b) := isUnit_iff_constantCoeff.mpr (by simp [hb_def, hbL, hbR])
  have hθh : map θ h = 1 := by
    have h1 : map θ a = map θ b := by
      rw [ha_def, map_subst hsμ, hmul, hb_def, map_mul, map_inL, map_inR]
    rw [hab, map_mul] at h1
    exact (IsUnit.mul_left_inj hθb).1 (h1.trans (one_mul _).symm)
  have hJ : ∀ x ∈ RingHom.ker θ, ∃ y ∈ RingHom.ker θ, x ^ p = p * y := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hF.pd x (RingHom.mem_ker.1 hx)
    exact ⟨y, RingHom.mem_ker.2 hy, hxy⟩
  have hker : ∀ α, coeff α (h - 1) ∈ RingHom.ker θ := by
    intro α
    rw [RingHom.mem_ker, ← coeff_map, map_sub, hθh, map_one, sub_self, map_zero]
  rw [key]
  exact GlobalTheory.T.formalLog_coeff_mem_of_sub_one_mem_dp p B O Q θ hF (RingHom.ker θ) hJ (Fin d ⊕ Fin d) h hh1 hker

end GlobalTheory.CobLog
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.Cob1FormalLogMapMemKerStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.cob1_formalLog_mem_ker_of_map_grouplike : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] [Algebra ℚ Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), (∀ i, constantCoeff (μ' i) = 0) → ∀ g : MvPowerSeries (Fin d) B, constantCoeff g = 1 → subst (fun i => map θ (μ' i)) (map θ g) = inL (map θ g) * inR (map θ g) → In (RingHom.ker θ) (cob1 (up Q μ') (formalLog (map (algebraMap B Q) g))) := by
  first | exact @GlobalTheory.CobLog.cob1_formalLog_mem_ker | exact GlobalTheory.CobLog.cob1_formalLog_mem_ker | (intros; apply GlobalTheory.CobLog.cob1_formalLog_mem_ker <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesLinearCoefficientsMvPowerSeriesFormal

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

namespace GlobalTheory.FormalCalc

theorem lin_formalLog (Q : Type) [CommRing Q] [Algebra ℚ Q] (d : ℕ) (g : MvPowerSeries (Fin d) Q) :
    constantCoeff g = 1 → ∀ i, lin (formalLog g) i = lin g i := by
  intro hg i
  have h := congrArg (coeff (0 : Fin d →₀ ℕ)) (mul_pderiv_formalLog hg i)
  rw [coeff_zero_eq_constantCoeff_apply, map_mul, hg, one_mul, ← coeff_zero_eq_constantCoeff_apply,
    coeff_pderiv, coeff_pderiv] at h
  simpa [lin] using h

end GlobalTheory.FormalCalc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesLinearCoefficientsMvPowerSeriesFormalStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.powerSeriesLinearCoefficients_mvPowerSeriesFormalLog : ∀ (Q : Type) [CommRing Q] [Algebra ℚ Q] (d : ℕ) (g : MvPowerSeries (Fin d) Q), constantCoeff g = 1 → ∀ i, lin (formalLog g) i = lin g i := by
  first | exact @GlobalTheory.FormalCalc.lin_formalLog | exact GlobalTheory.FormalCalc.lin_formalLog | (intros; apply GlobalTheory.FormalCalc.lin_formalLog <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstGroupLawEqMulOfDualTateCharacter

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc
open TensorProduct

namespace GlobalTheory.QLog.Chart

theorem subst_μ_eq_inL_mul_inR : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d)
    (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), (∀ n, c.ev n u = charElem χ n) →
    subst c.μ u = inL u * inR u := by
  intro p _ O _ _ _ G d c χ u hu
  set D := subst c.μ u - inL u * inR u with hD
  have hev : ∀ n, c.ev₂ n D = 0 := by
    intro n
    obtain ⟨h1, h2, h3, -⟩ := ev₂_eval p O G d c n u
    rw [hD, map_sub, map_mul, h1, h2, h3, hu n, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      (isGroupLikeElem_charElem χ n).comul_eq_tmul_self, sub_self]
  rw [← sub_eq_zero, ← hD]
  ext α
  rw [map_zero]
  refine IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {(p : O)})) _ fun m => ?_
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, sub_zero]
  obtain ⟨n, hn⟩ := c.ker m (α.degree + 1)
  exact T.dvd_coeff_of_ker_sum_of_dvd_coeff_ker p O (G.A n) (G.A n) (Fin d) (Fin d) (c.x n) (c.x n) (c.ev n) (c.ev n) (c.ev₂ n) m
    (α.degree + 1) (c.isEval n) (c.isEval n) (c.isEval₂ n) (c.surj n) (c.surj n) hn hn D (hev n) α
    (Nat.lt_succ_self _)

end GlobalTheory.QLog.Chart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstGroupLawEqMulOfDualTateCharacterStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem _root_.GlobalTheory.T.subst_groupLaw_eq_mul_of_dualTateCharacter : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate) (u : MvPowerSeries (Fin d) O), (∀ n, c.ev n u = charElem χ n) → subst c.μ u = inL u * inR u := by
  first | exact @GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR | exact GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR | (intros; apply GlobalTheory.QLog.Chart.subst_μ_eq_inL_mul_inR <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogarithmOfDualCharacter

section

@[expose] public section

namespace GlobalTheory.CharLog

variable {p : ℕ} {B O Q : Type} [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] {θ : B →+* O}

theorem isUnit_intCast [Fact p.Prime] (h : GlobalTheory.QLog.IsFrame p Q θ) {n : ℤ} (hn : n ≠ 0) :
    IsUnit (n : Q) := by
  have hna : n.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hn
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hna p (Fact.out : p.Prime).ne_one
  have hcop : Nat.Coprime m p :=
    Nat.coprime_comm.1 (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hm)
  have hu : IsUnit (n.natAbs : Q) := by
    rw [hnm, Nat.cast_mul, Nat.cast_pow]
    refine (h.unit_p.pow k).mul ?_
    simpa using (h.unit_coprime m hcop).map (algebraMap B Q)
  rcases Int.natAbs_eq n with h' | h'
  · rw [h', Int.cast_natCast]; exact hu
  · rw [h', Int.cast_neg, Int.cast_natCast]; exact hu.neg

noncomputable def ratAlgebra [Fact p.Prime] (h : GlobalTheory.QLog.IsFrame p Q θ) : Algebra ℚ Q :=
  (IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) (g := Int.castRingHom Q)
    fun y => by simpa using isUnit_intCast h (nonZeroDivisors.ne_zero y.2)).toAlgebra

end GlobalTheory.CharLog

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

theorem GlobalTheory.CharLog.exists_log_char_period : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ χ : G.dual.Tate, ∃ (f : MvPowerSeries (Fin d) F.Q) (w : Fin d → F.B), QL μ' ⊤ f ∧ In (RingHom.ker F.θ) (cob1 (up F.Q μ') f) ∧ In (⊤ : Ideal F.B) (frob p F.s f - (p : F.Q) • f) ∧ (∀ i, lin f i = algebraMap F.B F.Q (w i)) ∧ dlog G χ = ∑ i, F.θ (w i) • c.form i ∧ ∀ t, c.HasPeriod F.θ t f (F.a (Sandwich.mu ε * ofPadic p O (epsPairing hε G t χ))) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hμ χ
  letI : Algebra ℚ F.Q := GlobalTheory.CharLog.ratAlgebra F.frame
  obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_charSeries' p O G d c χ
  have hmul := GlobalTheory.T.subst_groupLaw_eq_mul_of_dualTateCharacter p O G d c χ u hu
  choose g0 hg0 using fun α => F.frame.surj (coeff α u)
  let g : MvPowerSeries (Fin d) F.B := fun α => if α = 0 then 1 else g0 α
  have hg : map F.θ g = u := by
    ext α
    rw [coeff_map]
    by_cases h : α = 0
    · subst h
      change F.θ (if (0 : Fin d →₀ ℕ) = 0 then 1 else g0 0) = _
      rw [if_pos rfl, map_one, coeff_zero_eq_constantCoeff_apply, hu0]
    · change F.θ (if α = 0 then 1 else g0 α) = _
      rw [if_neg h, hg0]
  have hg1 : constantCoeff g = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    change (if (0 : Fin d →₀ ℕ) = 0 then 1 else g0 0) = 1
    rw [if_pos rfl]
  have hlin : ∀ i, lin (formalLog (map (algebraMap F.B F.Q) g)) i =
      algebraMap F.B F.Q (coeff (Finsupp.single i 1) g) := fun i => by
    rw [GlobalTheory.T.powerSeriesLinearCoefficients_mvPowerSeriesFormalLog F.Q d _ (by rw [constantCoeff_map, hg1, map_one]) i, lin, coeff_map]
  have hcob := GlobalTheory.T.cob1_formalLog_mem_ker_of_map_grouplike p F.B O F.Q F.θ F.frame d μ' hlift.const g hg1 (by
    rw [hg]; convert hmul using 2; funext i; exact hμ i)
  refine ⟨formalLog (map (algebraMap F.B F.Q) g), fun i => coeff (Finsupp.single i 1) g,
    ⟨constantCoeff_formalLog (by rw [constantCoeff_map, hg1, map_one]),
      fun i => ⟨_, Submodule.mem_top, hlin i⟩,
      fun α => by obtain ⟨b, -, hb⟩ := hcob α; exact ⟨b, Submodule.mem_top, hb⟩⟩,
    hcob, GlobalTheory.T.frobenius_formalLog_sub_smul_integral p F.B O F.Q F.θ F.frame F.σ F.s F.s_alg F.σ_pow d g hg1, hlin, ?_, ?_⟩
  · rw [GlobalTheory.T.dlog_eq_sum_linearCoefficients_form_explicit p O G d c χ u hu0 hu]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hg, lin, coeff_map]
  · exact GlobalTheory.T.period_formalLog_lift_characterSeries p C v O hv ε hε F G d c χ g hg1 (by rw [hg]; exact hu)
end
end
