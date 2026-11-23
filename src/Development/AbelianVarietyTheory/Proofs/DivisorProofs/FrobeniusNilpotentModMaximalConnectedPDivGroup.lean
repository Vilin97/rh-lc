module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffNmul
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupChartLevelOneNilpotentModPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelOneDefectsIndependentModMaximalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmLevelOneDefectFrobeniusPowStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffQuasiLogarithmMultiplicationDefect

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDefect

theorem constantCoeff_defect : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f → ∀ n : ℕ, constantCoeff (defect μ n f) = 0 := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ f hf n
  have hU : ∀ j, constantCoeff (up Q (nmul μ n) j) = 0 := by
    intro j
    simp only [up]
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_nmul hμ.const n j, map_zero]
  unfold defect
  rw [map_sub, constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hU) hU hf.1, sub_zero]
  simp [hf.1]

end GlobalTheory.QLogDefect
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffQuasiLogarithmMultiplicationDefectStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.constantCoeff_quasiLogarithmMultiplicationDefect : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ f : MvPowerSeries (Fin d) Q, QL μ ⊤ f → ∀ n : ℕ, constantCoeff (defect μ n f) = 0 := by
  first | exact @GlobalTheory.QLogDefect.constantCoeff_defect | exact GlobalTheory.QLogDefect.constantCoeff_defect | (intros; apply GlobalTheory.QLogDefect.constantCoeff_defect <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmModIdealTopLinearCombination

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem ql_comb_top : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → ∀ w : ι → B, QL μ ⊤ (comb w e) := by
  intro B O Q _ _ _ _ θ d μ hμ ι _ e he w
  have hc : ∀ i, constantCoeff (up Q μ i) = 0 := by
    intro i
    simp [up, hμ.const i]
  have hzero : QL μ ⊤ (0 : MvPowerSeries (Fin d) Q) := by
    refine ⟨by simp, fun i => ⟨0, Submodule.mem_top, by simp [lin]⟩, fun α => ⟨0, Submodule.mem_top, ?_⟩⟩
    have := formalCoboundary_smul hc (0 : Q) 0
    rw [zero_smul, zero_smul] at this
    rw [this]; simp
  have hadd : ∀ f g : MvPowerSeries (Fin d) Q, QL μ ⊤ f → QL μ ⊤ g → QL μ ⊤ (f + g) := by
    rintro f g ⟨hf0, hf1, hf2⟩ ⟨hg0, hg1, hg2⟩
    refine ⟨by simp [hf0, hg0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      obtain ⟨b, -, hb⟩ := hg1 i
      exact ⟨a + b, Submodule.mem_top, by simp only [lin, map_add (f := _)] at ha hb ⊢; rw [ha, hb]⟩
    · obtain ⟨a, -, ha⟩ := hf2 α
      obtain ⟨b, -, hb⟩ := hg2 α
      exact ⟨a + b, Submodule.mem_top, by rw [formalCoboundary_add hc, map_add (f := _), ha, hb, map_add (f := _)]⟩
  have hsmul : ∀ (c : B) (f : MvPowerSeries (Fin d) Q), QL μ ⊤ f → QL μ ⊤ (algebraMap B Q c • f) := by
    rintro c f ⟨hf0, hf1, hf2⟩
    refine ⟨by simp [hf0], fun i => ?_, fun α => ?_⟩
    · obtain ⟨a, -, ha⟩ := hf1 i
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      simp only [lin, map_smul, smul_eq_mul] at ha ⊢
      rw [ha, map_mul]
    · obtain ⟨a, -, ha⟩ := hf2 α
      refine ⟨c * a, Submodule.mem_top, ?_⟩
      rw [formalCoboundary_smul hc, map_smul, smul_eq_mul, ha, map_mul]
  unfold comb
  exact Finset.sum_induction _ (QL μ ⊤) hadd hzero fun i _ => hsmul (w i) (e i) (he i)

end GlobalTheory.QLog
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQuasiLogarithmModIdealTopLinearCombinationStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.isQuasiLogarithmModIdeal_top_linearCombination : ∀ (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → ∀ w : ι → B, QL μ ⊤ (comb w e) := by
  first | exact @GlobalTheory.QLog.ql_comb_top | exact GlobalTheory.QLog.ql_comb_top | (intros; apply GlobalTheory.QLog.ql_comb_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesFrobeniusTwistLinearCombinationModInt

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.FrobStep

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem frob_eq_comp (p : ℕ) (hp : p ≠ 0) {σ : Type} (s : Q →+* Q) (f : MvPowerSeries σ Q) :
    frob p s f = ((substAlgHom (R := Q) (S := Q) (HasSubst.X_pow (σ := σ) (S := Q) hp)).toRingHom.comp
      (MvPowerSeries.map s)) f := by
  simp [frob]

theorem frob_smul (p : ℕ) (hp : p ≠ 0) {σ : Type} (τ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (τ b)) (b : B) (f : MvPowerSeries σ Q) :
    frob p s (algebraMap B Q b • f) = algebraMap B Q (τ b) • frob p s f := by
  unfold frob
  rw [smul_eq_C_mul, map_mul, map_C, hs, ← smul_eq_C_mul,
    subst_smul (HasSubst.X_pow (σ := σ) (S := Q) hp)]

theorem frob_comb (p : ℕ) (hp : p ≠ 0) {σ : Type} (τ : B →+* B) (s : Q →+* Q)
    (hs : ∀ b, s (algebraMap B Q b) = algebraMap B Q (τ b)) {ι : Type} [Fintype ι]
    (w : ι → B) (e : ι → MvPowerSeries σ Q) :
    frob p s (comb w e) = ∑ i, algebraMap B Q (τ (w i)) • frob p s (e i) := by

  rw [comb, frob_eq_comp p hp, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← frob_eq_comp p hp, frob_smul p hp τ s hs]

theorem in_top_sum_smul {σ : Type} {ι : Type} [Fintype ι] (c : ι → B)
    (g : ι → MvPowerSeries σ Q) (h : ∀ i, In (⊤ : Ideal B) (g i)) :
    In (⊤ : Ideal B) (∑ i, algebraMap B Q (c i) • g i) := by
  intro α
  choose b _ hb using fun i => h i α
  refine ⟨∑ i, c i * b i, Submodule.mem_top, ?_⟩

  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_smul, hb, map_mul]

theorem comb_mulVec {σ : Type} {ι : Type} [Fintype ι] (M : Matrix ι ι B) (v : ι → B)
    (e : ι → MvPowerSeries σ Q) :
    comb (M.mulVec v) e = ∑ i, algebraMap B Q (v i) • comb (fun l => M l i) e := by

  simp only [comb, Matrix.mulVec, dotProduct, map_sum, Finset.sum_smul, Finset.smul_sum, smul_smul,
  ← map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem frob_comb_step : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q]
    (σ : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) →
    ∀ (d : ℕ) (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q) (M : Matrix ι ι B),
    (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => M l i) e)) →
    ∀ w : ι → B, In (⊤ : Ideal B) (frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e) := by
  intro p hp B Q _ _ _ σ s hs d ι _ e M hM w
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have key : frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e =
      ∑ i, algebraMap B Q (σ (w i)) • (frob p s (e i) - comb (fun l => M l i) e) := by
    rw [frob_comb p hp0 σ s hs, comb_mulVec]
    simp only [smul_sub, Finset.sum_sub_distrib]
  rw [key]
  exact in_top_sum_smul _ _ hM

end GlobalTheory.FrobStep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesFrobeniusTwistLinearCombinationModIntStatement

section

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.powerSeriesFrobeniusTwist_linearCombination_mod_integral : ∀ (p : ℕ) [Fact p.Prime] (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (σ : B →+* B) (s : Q →+* Q), (∀ b, s (algebraMap B Q b) = algebraMap B Q (σ b)) → ∀ (d : ℕ) (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q) (M : Matrix ι ι B), (∀ i, In (⊤ : Ideal B) (frob p s (e i) - comb (fun l => M l i) e)) → ∀ w : ι → B, In (⊤ : Ideal B) (frob p s (comb w e) - comb (M.mulVec fun j => σ (w j)) e) := by
  first | exact @GlobalTheory.FrobStep.frob_comb_step | exact GlobalTheory.FrobStep.frob_comb_step | (intros; apply GlobalTheory.FrobStep.frob_comb_step <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusNilpotentModMaximalConnectedPDivGroup

section

@[expose] public section

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

theorem isNil_frobenius_chart : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) F.Q), IsBasis μ' e → IsAdapted F.θ μ' e → ∀ U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i, In (⊤ : Ideal F.B) (frob p F.s (e i) - comb (fun l => (U * blk d k (p : F.B) 1) l i) e)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F G d c μ' hlift hmap k e hbas hadp U hU
  set M := U * blk d k (p : F.B) 1 with hM
  let T : (Fin d ⊕ Fin k → F.B) → (Fin d ⊕ Fin k → F.B) := fun w => M.mulVec fun j => F.σ (w j)
  have hp : ¬IsUnit (p : O) := Fact.out
  have hθp : F.θ (p : F.B) = (p : O) := map_natCast _ _
  have nu_iff : ∀ x : O, ¬IsUnit x ↔ v (algebraMap O C x) < 1 := fun x => by
    rw [hv.isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => h.ne⟩
  have nu_add : ∀ x y : O, ¬IsUnit x → ¬IsUnit y → ¬IsUnit (x + y) := by
    intro x y hx hy
    rw [nu_iff] at hx hy ⊢
    rw [map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  have nu_sum : ∀ (s : Finset (Fin d ⊕ Fin k)) (f : Fin d ⊕ Fin k → O),
      (∀ i ∈ s, ¬IsUnit (f i)) → ¬IsUnit (∑ i ∈ s, f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using not_isUnit_zero
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact nu_add _ _ (hf a (Finset.mem_insert_self _ _))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
  have stepA : ∀ w : Fin d ⊕ Fin k → F.B, (∀ j, ¬IsUnit (F.θ (w (Sum.inr j)))) →
      ∀ i, ¬IsUnit (F.θ (T w i)) := by
    intro w hw i
    show ¬IsUnit (F.θ (∑ l, M i l * F.σ (w l)))

    rw [map_sum]
    apply nu_sum
    intro l _
    rw [hM, blk, Matrix.mul_diagonal]
    cases l with
    | inl l =>
      simp only [Sum.elim_inl, map_mul, hθp]
      exact fun h => hp (isUnit_of_mul_isUnit_right (isUnit_of_mul_isUnit_left h))
    | inr j =>
      simp only [Sum.elim_inr, mul_one, map_mul]
      obtain ⟨c', hc'⟩ := F.σ_pow (w (Sum.inr j))
      have hs : F.θ (F.σ (w (Sum.inr j))) = F.θ (w (Sum.inr j)) ^ p + p * F.θ c' := by
        have := congrArg F.θ hc'
        rw [map_sub, map_mul, map_pow, hθp] at this
        linear_combination this
      rw [hs]
      refine fun h => nu_add _ _ ?_ ?_ (isUnit_of_mul_isUnit_right h)
      · exact fun h' => hw j ((isUnit_pow_iff (Fact.out : p.Prime).ne_zero).1 h')
      · exact fun h' => hp (isUnit_of_mul_isUnit_left h')
  have hQL : ∀ w : Fin d ⊕ Fin k → F.B, QL μ' ⊤ (comb w e) := fun w => GlobalTheory.T.isQuasiLogarithmModIdeal_top_linearCombination _ _ _ F.θ d μ' hlift _ e hbas.1 w
  have hstep : ∀ w : Fin d ⊕ Fin k → F.B, In (⊤ : Ideal F.B) (frob p F.s (comb w e) - comb (T w) e) :=
    fun w => GlobalTheory.T.powerSeriesFrobeniusTwist_linearCombination_mod_integral p F.B F.Q F.σ F.s F.s_alg d _ e M hU w
  have hlf : ∀ w : Fin d ⊕ Fin k → F.B, ∃ a : MvPowerSeries (Fin d) F.B,
      map (algebraMap F.B F.Q) a = defect μ' p (comb w e) := by
    intro w
    have h := (QLogDefect.main p F.B O F.Q F.θ F.frame d μ' hlift ⊤ _ (hQL w) p).1
    choose b _ hb using h
    refine ⟨(fun α => b α : MvPowerSeries (Fin d) F.B), MvPowerSeries.ext fun α => ?_⟩
    exact (hb α).symm
  choose A hA using hlf
  let δ : (Fin d ⊕ Fin k → F.B) → G.A 1 := fun w => c.ev 1 (map F.θ (A w))
  set I := Ideal.span (algebraMap O (G.A 1) '' {o | ¬IsUnit o}) with hI
  have hδstep : ∀ w : Fin d ⊕ Fin k → F.B, δ (T w) - δ w ^ p ∈ I := fun w =>
    GlobalTheory.T.quasiLogarithm_levelOne_defect_frobenius_pow p C v O hv ε hε F G d c μ' hlift hmap _ _ _ _ (hQL w) (hQL (T w)) (hstep w) (hA w) (hA (T w))
  have hδit : ∀ n w, δ (T^[n] w) - δ w ^ (p ^ n) ∈ I := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [Function.iterate_succ_apply', pow_succ, pow_mul]
      have h1 := hδstep (T^[n] w)
      have h2 : δ (T^[n] w) ^ p - (δ w ^ p ^ n) ^ p ∈ I :=
        I.mem_of_dvd (sub_dvd_pow_sub_pow _ _ p) (ih w)
      have := I.add_mem h1 h2
      rwa [sub_add_sub_cancel] at this
  have hconst : ∀ w : Fin d ⊕ Fin k → F.B, constantCoeff (map F.θ (A w)) = 0 := by
    intro w
    have h0 := GlobalTheory.T.constantCoeff_quasiLogarithmMultiplicationDefect p F.B O F.Q F.θ F.frame d μ' hlift _ (hQL w) p
    rw [← hA w, MvPowerSeries.constantCoeff_map] at h0
    have h2 : constantCoeff (A w) = 0 := F.frame.inj (by rw [h0, map_zero])
    rw [MvPowerSeries.constantCoeff_map, h2, map_zero]
  obtain ⟨N0, hN0⟩ := GlobalTheory.T.exists_pDivGroupChart_level_one_nilpotent_mod_p p O G d c
  have hsmallp : ∀ x : G.A 1, (p : G.A 1) ∣ x → x ∈ I := by
    rintro x ⟨y, rfl⟩
    apply I.mul_mem_right
    apply Ideal.subset_span
    exact ⟨(p : O), hp, map_natCast _ _⟩
  have hδ0 : ∀ w : Fin d ⊕ Fin k → F.B, δ w ^ (p ^ N0) ∈ I := by
    intro w
    apply hsmallp
    have hle : N0 ≤ p ^ N0 := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
    rw [← Nat.sub_add_cancel hle, pow_add]
    exact Dvd.dvd.mul_left (hN0 _ (hconst w)) _
  refine ⟨N0 + 1, fun w i => ?_⟩
  rw [Function.iterate_succ_apply']
  apply stepA
  intro j
  apply GlobalTheory.T.levelOne_defects_independent_mod_maximal p C v O hv ε hε F G d c μ' hlift hmap k e hbas hadp _ (A _) (hA _)
  have := I.add_mem (hδit N0 w) (hδ0 w)
  rwa [sub_add_cancel] at this

end GlobalTheory.QLog
end
end
