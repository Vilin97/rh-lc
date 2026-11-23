module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTermsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawLinearCoeffAdditiveStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CoeffSingleLawAdd
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeqOfStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawLinearCoeffAdditiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesReductionModPrimeRulesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSuccessiveApproximationStep

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCob1WittLiftModP

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.WittStart

theorem eq_zero_or_single {ι : Type} [Fintype ι] [DecidableEq ι] (γ : ι →₀ ℕ) (h : γ.degree < 2) :
    γ = 0 ∨ ∃ s, γ = Finsupp.single s 1 := by
  by_cases h0 : γ = 0
  · exact Or.inl h0
  right
  obtain ⟨s, hs⟩ : ∃ s, γ s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (Finsupp.ext hc)
  rw [Finsupp.degree_eq_sum] at h
  have hsum : ∑ i, γ i = γ s + ∑ i ∈ Finset.univ.erase s, γ i :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ s)).symm
  refine ⟨s, Finsupp.ext fun t => ?_⟩
  by_cases hts : t = s
  · subst hts
    have : ∑ i ∈ Finset.univ.erase t, γ i ≥ 0 := Nat.zero_le _
    simp only [Finsupp.single_eq_same]
    omega
  · simp only [Finsupp.single_apply, Ne.symm hts, if_false]
    have : γ t ≤ ∑ i ∈ Finset.univ.erase s, γ i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hts, Finset.mem_univ t⟩)
    omega

variable {R : Type} [CommRing R] {d : ℕ}

theorem coeff_single_linear_substitution_pair {τ : Type} (c : MvPowerSeries (Fin d ⊕ Fin d) R)
    (u v : Fin d → MvPowerSeries τ R) (hu : ∀ i, constantCoeff (u i) = 0)
    (hv : ∀ i, constantCoeff (v i) = 0) (t : τ) :
    coeff (Finsupp.single t 1) (at2 c u v) =
      ∑ i, coeff (Finsupp.single (Sum.inl i) 1) c * coeff (Finsupp.single t 1) (u i) +
      ∑ i, coeff (Finsupp.single (Sum.inr i) 1) c * coeff (Finsupp.single t 1) (v i) := by
  unfold at2
  rw [GlobalTheory.FormalCalc.coeff_single_subst, Fintype.sum_sum_type]
  · rfl
  · rintro (i | i)
    · exact hu i
    · exact hv i

theorem constantCoeff_subst0 {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries σ R) :
    constantCoeff (subst a f) = constantCoeff f := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have h1 : f = (f - C (constantCoeff f)) + C (constantCoeff f) := by ring
  conv_lhs => rw [h1]
  rw [subst_add hs, map_add (f := _), constantCoeff_subst_eq_zero hs ha (by simp), subst_C, zero_add]
  simp

theorem constantCoeff_op {τ : Type} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ0 : ∀ i, constantCoeff (μ i) = 0) (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) :
    constantCoeff (op μ u v i) = 0 := by
  unfold op at2
  rw [constantCoeff_subst0 (fun s => by cases s with | inl s => exact hu s | inr s => exact hv s)]
  exact hμ0 i

theorem coeff_single_op {τ : Type} {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw R d i))
    (u v : Fin d → MvPowerSeries τ R)
    (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) (i : Fin d) (t : τ) :
    coeff (Finsupp.single t 1) (op μ u v i) =
      coeff (Finsupp.single t 1) (u i) + coeff (Finsupp.single t 1) (v i) := by
  classical
  unfold op
  rw [coeff_single_linear_substitution_pair _ _ _ hu hv]
  simp only [hμ, addLaw, map_add (f := _), GlobalTheory.FormalCalc.coeff_single_X]
  simp [add_mul, Finset.sum_add_distrib]

theorem coeff_single_coc {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ0 : ∀ i, constantCoeff (μ i) = 0)
    (hμ : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw R d i))
    (c : MvPowerSeries (Fin d ⊕ Fin d) R) (hc : IsCoc μ c) (s : Fin d ⊕ Fin d) :
    coeff (Finsupp.single s 1) c = 0 := by
  classical
  have hx1 : ∀ i, constantCoeff (x1 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx2 : ∀ i, constantCoeff (x2 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hx3 : ∀ i, constantCoeff (x3 (R := R) (d := d) i) = 0 := fun i => constantCoeff_X _
  have hinl : ∀ j, coeff (Finsupp.single (Sum.inl j) 1) c = 0 := by
    intro j
    have h := congrArg (coeff (Finsupp.single (Sum.inl j : Fin d ⊕ (Fin d ⊕ Fin d)) 1)) hc.1
    unfold cob2 at h
    rw [map_sub, map_add (f := _), map_sub, map_zero,
      coeff_single_linear_substitution_pair _ _ _ hx2 hx3,
      coeff_single_linear_substitution_pair _ _ _ (constantCoeff_op hμ0 _ _ hx1 hx2) hx3,
      coeff_single_linear_substitution_pair _ _ _ hx1 (constantCoeff_op hμ0 _ _ hx2 hx3),
      coeff_single_linear_substitution_pair _ _ _ hx1 hx2] at h
    simp only [coeff_single_op hμ _ _ hx1 hx2, coeff_single_op hμ _ _ hx2 hx3, x1, x2, x3,
      GlobalTheory.FormalCalc.coeff_single_X] at h
    simpa using h
  cases s with
  | inl j => exact hinl j
  | inr j =>
    have h := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) hc.2
    unfold swap at h
    rw [coeff_single_linear_substitution_pair _ _ _ (fun _ => constantCoeff_X _) (fun _ => constantCoeff_X _)] at h
    simp only [GlobalTheory.FormalCalc.coeff_single_X] at h
    simp only [Sum.inr.injEq, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero, zero_add,
      mul_ite, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    rw [← h]
    simp [hinl]

end GlobalTheory.WittStart

namespace GlobalTheory.WittStart

theorem start : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c →
    ∀ w : Fin d → k, ∃ f ∈ intBy p k (Fin d) 1, RedV p (lin f) w ∧
      ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < 2 → ∃ w : WittVector p k,
        coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) =
          algebraMap (WittVector p k) (Fr p k) (p * w) := by
  intro p _ k _ _ _ d μ hμ c hc w
  classical
  have hL := GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ
  have hdeg : ∀ s : Fin d ⊕ Fin d, (Finsupp.single s 1).degree ≤ 1 := fun s => by
    rw [Finsupp.degree_single]
  have hμk : ∀ i s, coeff (Finsupp.single s 1) (μ i) = coeff (Finsupp.single s 1) (addLaw k d i) :=
    fun i s => (hL i _ (hdeg s)).1
  have hμF : ∀ i s, coeff (Finsupp.single s 1) (Katz.lift p (μ i)) =
      coeff (Finsupp.single s 1) (addLaw (Fr p k) d i) := fun i s => (hL i _ (hdeg s)).2
  have hμ0F : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  have hclin := coeff_single_coc hμ.const hμk c hc
  set T : k → Fr p k := fun x => algebraMap (WittVector p k) (Fr p k) (WittVector.teichmuller p x)
    with hT
  set f : MvPowerSeries (Fin d) (Fr p k) :=
    (-(WittVector.teichmuller p (constantCoeff c))) • (1 : MvPowerSeries (Fin d) (Fr p k)) +
      ∑ i, WittVector.teichmuller p (w i) • (X i : MvPowerSeries (Fin d) (Fr p k)) with hf
  have hcoeff : ∀ α, coeff α f = (if α = 0 then -T (constantCoeff c) else 0) +
      ∑ i, if α = Finsupp.single i 1 then T (w i) else 0 := by
    intro α

    rw [hf, map_add (f := _), map_sum]
    have e : ∀ (r : WittVector p k) (g : MvPowerSeries (Fin d) (Fr p k)),
        coeff α (r • g) = algebraMap (WittVector p k) (Fr p k) r * coeff α g := fun r g => by
      rw [← algebraMap_smul (Fr p k) r g, coeff_smul]
    simp only [e, coeff_one, coeff_X, hT, map_neg]
    congr 1
    · split_ifs <;> simp
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
  refine ⟨f, ?_, ?_, ?_⟩
  · intro α
    rw [hcoeff α]
    refine ⟨(if α = 0 then -WittVector.teichmuller p (constantCoeff c) else 0) +
      ∑ i, if α = Finsupp.single i 1 then WittVector.teichmuller p (w i) else 0, ?_⟩

    rw [one_mul, map_add (f := _), map_sum]
    congr 1
    · split_ifs <;> simp [hT]
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp [hT]
  · intro i
    refine ⟨WittVector.teichmuller p (w i), ?_, ?_⟩
    · show coeff _ f = _
      rw [hcoeff]
      simp [Finsupp.single_eq_single_iff, hT]
    · rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  · intro γ hγ
    refine ⟨0, ?_⟩
    rw [mul_zero, map_zero]
    rcases eq_zero_or_single γ hγ with rfl | ⟨s, rfl⟩
    · have h0s : ∀ i : Fin d, (0 : Fin d →₀ ℕ) ≠ Finsupp.single i 1 :=
        fun i => (Finsupp.single_ne_zero.mpr one_ne_zero).symm
      rw [coeff_zero_eq_constantCoeff_apply, map_sub]
      unfold cob1 inL inR
      rw [map_sub, map_sub, constantCoeff_subst0 hμ0F, constantCoeff_subst0 (fun _ => constantCoeff_X _),
        constantCoeff_subst0 (fun _ => constantCoeff_X _), ← coeff_zero_eq_constantCoeff_apply,
        ← coeff_zero_eq_constantCoeff_apply, coeff_lift, hcoeff]
      simp [hT, coeff_zero_eq_constantCoeff_apply, h0s]
    · rw [map_sub, coeff_lift, hclin, WittVector.teichmuller_zero, map_zero, sub_zero]
      unfold cob1 inL inR
      rw [map_sub, map_sub, GlobalTheory.FormalCalc.coeff_single_subst hμ0F,
        GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _),
        GlobalTheory.FormalCalc.coeff_single_subst (fun _ => constantCoeff_X _)]
      simp only [hμF, addLaw, map_add (f := _), mul_add, Finset.sum_add_distrib]
      ring

end GlobalTheory.WittStart
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCob1WittLiftModPStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.exists_cob1_witt_lift_mod_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ intBy p k (Fin d) 1, RedV p (lin f) w ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < 2 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  first | exact @GlobalTheory.WittStart.start | exact GlobalTheory.WittStart.start | (intros; apply GlobalTheory.WittStart.start <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmSuccessiveApproximationStepStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.quasiLogarithm_successive_approximation_step : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ c, IsCoc μ c → ∀ (N : ℕ) (f : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → f ∈ quasiInt p k (Fin d) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w)) → ∃ h : MvPowerSeries (Fin d) (Fr p k), (∀ α : Fin d →₀ ℕ, α.degree ≠ N → coeff α h = 0) ∧ f - h ∈ quasiInt p k (Fin d) ∧ ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < N + 1 → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (f - h) - Katz.lift p c) = algebraMap (WittVector p k) (Fr p k) (p * w) := by
  first | exact @GlobalTheory.Katz.quasiLog_approx_step | exact GlobalTheory.Katz.quasiLog_approx_step | (intros; apply GlobalTheory.Katz.quasiLog_approx_step <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogRed

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

namespace Katz

theorem exists_seq_of_step {A : Type} (P : ℕ → A → Prop) (Q : ℕ → A → A → Prop) (a₀ : A)
    (h₀ : P 0 a₀) (hs : ∀ n a, P n a → ∃ b, P (n + 1) b ∧ Q n a b) :
    ∃ F : ℕ → A, F 0 = a₀ ∧ ∀ n, P n (F n) ∧ Q n (F n) (F (n + 1)) := by
  first
  | exact @_root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step
  | exact _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step
  | (apply _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> assumption)
  | (intros; apply _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SequenceFromIteration.exists_seq_of_step ..)

theorem exists_limit_of_steps {R σ : Type} [CommRing R] (F : ℕ → MvPowerSeries σ R)
    (hF : ∀ n (α : σ →₀ ℕ), α.degree ≠ n + 2 → coeff α (F (n + 1)) = coeff α (F n)) :
    ∃ f : MvPowerSeries σ R, ∀ n (α : σ →₀ ℕ), α.degree < n + 2 → coeff α f = coeff α (F n) := by
  have stab : ∀ n (α : σ →₀ ℕ), α.degree < n + 2 → ∀ m, n ≤ m →
      coeff α (F m) = coeff α (F n) := by
    intro n α hα m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih => rw [hF m α (by omega), ih]
  refine ⟨fun α => coeff α (F α.degree), fun n α hα => ?_⟩
  change coeff α (F α.degree) = _
  rw [← stab α.degree α (by omega) (max n α.degree) (le_max_right _ _),
    stab n α hα _ (le_max_left _ _)]

theorem exists_quasiLog_red (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ) :
    ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ quasiLog p h,
      Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w := by
  intro c hc w
  obtain ⟨f₀, hf₀, hw, hb⟩ := GlobalTheory.T.exists_cob1_witt_lift_mod_p p k d μ h c hc w
  have hq₀ : f₀ ∈ quasiInt p k (Fin d) := by
    intro α i
    obtain ⟨v, hv⟩ := hf₀ α
    exact ⟨(α i : WittVector p k) * (1 * v), by rw [hv, map_mul _ (α i : WittVector p k), map_natCast]⟩
  obtain ⟨F, hF0, hF⟩ := exists_seq_of_step
    (fun n (f : MvPowerSeries (Fin d) (Fr p k)) => f ∈ quasiInt p k (Fin d) ∧
      ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree < n + 2 → ∃ w : WittVector p k,
        coeff γ (cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c) =
          algebraMap (WittVector p k) (Fr p k) (p * w))
    (fun n a b => ∀ α : Fin d →₀ ℕ, α.degree ≠ n + 2 → coeff α b = coeff α a) f₀ ⟨hq₀, hb⟩
    (by
      intro n a ha
      obtain ⟨g, hg0, hg1, hg2⟩ := GlobalTheory.T.quasiLogarithm_successive_approximation_step p k d μ h c hc (n + 2) a (by omega) ha.1 ha.2
      exact ⟨a - g, ⟨hg1, hg2⟩, fun α hα => by rw [map_sub, hg0 α hα, sub_zero]⟩)
  obtain ⟨f, hf⟩ := exists_limit_of_steps F fun n => (hF n).2
  have hq : f ∈ quasiInt p k (Fin d) := by
    intro α i
    rw [hf α.degree α (by omega)]
    exact (hF α.degree).1.1 α i
  have hp : cob1 (fun i => Katz.lift p (μ i)) f - Katz.lift p c ∈ intBy p k (Fin d ⊕ Fin d) p := by
    intro γ
    obtain ⟨v, hv⟩ := (hF γ.degree).1.2 γ (by omega)
    refine ⟨v, ?_⟩
    have h1 := ((GlobalTheory.T.coboundary_eq_additive_leading_terms (Fr p k) d (fun i => Katz.lift p (μ i)) (γ.degree + 2)
      (fun i α hα => (GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ h i α hα).2)).1 (f - F γ.degree)
      (fun α hα => by rw [map_sub, hf _ α hα, sub_self]) γ).1 (by omega)
    have h2 := formalCoboundary_add (fun i => constantCoeff_lift p (h.const i)) (f - F γ.degree) (F γ.degree)
    rw [sub_add_cancel] at h2
    rw [h2, add_sub_assoc, map_add (f := _), h1, zero_add, hv]
  obtain ⟨r1, -, r3, r4, -, r6, -⟩ := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)
  have hred : Red p (cob1 (fun i => Katz.lift p (μ i)) f) c := by
    have := (r4 _ _ _ _ ((r6 _).1 hp) (r3 c)).1
    rwa [sub_add_cancel, zero_add] at this
  refine ⟨f, ⟨hq, (r1 _).2 ⟨c, hred⟩⟩, hred, ?_⟩
  have hl : lin f = lin f₀ := by
    funext i
    unfold lin
    rw [hf 0 _ (by simp), hF0]
  rw [hl]
  exact hw

end Katz

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiLogRedStatement

section

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

theorem _root_.GlobalTheory.T.exists_quasiLog_red_coboundary_and_linear : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ), ∀ c, IsCoc μ c → ∀ w : Fin d → k, ∃ f ∈ quasiLog p h, Red p (cob1 (fun i => Katz.lift p (μ i)) f) c ∧ RedV p (lin f) w := by
  first | exact @GlobalTheory.Katz.exists_quasiLog_red | exact GlobalTheory.Katz.exists_quasiLog_red | (intros; apply GlobalTheory.Katz.exists_quasiLog_red <;> assumption)
end
end
