module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExpTeichmullerPowerSumFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrKIsometricAndOneSubSurjectiveStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExpTeichmullerPowerSumFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomicFrobeniusTwistedValueEqPowMulStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFrobeniusFormulaPosWeight

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage.PosWeight

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow_self (P : LocPrime l) (m : ℕ) : P.ζQ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem norm_nat_eq_one {a : ℕ} (ha : ¬ l ∣ a) : ‖(a : Om l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr ha)

theorem norm_frK_pow (P : LocPrime l) (K : FinExt l) (n : ℕ) (c : ↥(K0 K)) :
    ‖(((frK P K ^ n) c : ↥(K0 K)) : Om l)‖ = ‖(c : Om l)‖ := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1, ih]

def co {K : FinExt l} (e : ℕ) (lam : ℕ → ↥(K0 K)) (i : ℕ × Bool) : ↥(K0 K) :=
  if i.2 then lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹ else -(lam i.1 * ((i.1 : ↥(K0 K)) ^ e)⁻¹)

def ex (l s : ℕ) (i : ℕ × Bool) : ℕ := if i.2 then (1 + l ^ s) * i.1 else i.1

theorem formula_pos : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  intro LT l _ AI hT K s hs e he g hg hχ lam d hlam hd hrec
  have hl : l.Prime := Fact.out
  have hu : ¬ l ∣ 1 + l ^ s := by
    intro h
    have h1 : l ∣ l ^ s := dvd_pow_self l (by have := hs.1; omega)
    exact hl.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_left h1).mp h))
  have hmem : ∀ a ∈ primeTo l s, ¬ l ∣ a := fun a ha => (Finset.mem_filter.mp ha).2
  have hne : ∀ a ∈ primeTo l s, (a : Om l) ≠ 0 := fun a ha h => by
    have := norm_nat_eq_one (hmem a ha)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hne' : ∀ a ∈ primeTo l s, (a : ↥(K0 K)) ≠ 0 := fun a ha h =>
    hne a ha (by simpa using congrArg (fun x : ↥(K0 K) => (x : Om l)) h)
  set T : Finset (ℕ × Bool) := primeTo l s ×ˢ Finset.univ with hTdef
  have hc : ∀ i ∈ T, ‖(co e lam i : Om l)‖ ≤ 1 ∧ ¬ l ∣ ex l s i := by
    rintro ⟨a, b⟩ hi
    have ha : a ∈ primeTo l s := (Finset.mem_product.mp hi).1
    have h1 := norm_nat_eq_one (hmem a ha)
    have h2 : ‖(lam a : Om l) * ((a : Om l) ^ e)⁻¹‖ ≤ 1 := by
      rw [norm_mul, norm_inv, norm_pow, h1]
      simpa using hlam a
    cases b
    · refine ⟨?_, hmem a ha⟩
      simpa [co, -norm_mul] using h2
    · refine ⟨by simpa [co, -norm_mul] using h2, ?_⟩
      intro h
      rcases (Nat.Prime.dvd_mul hl).mp h with h | h
      · exact hu h
      · exact hmem a ha h
  have hall : ∀ j : ℕ, ∃ dj : ↥(K0 K), j ≤ e → (‖(dj : Om l)‖ ≤ 1 ∧
      dj - (l : ↥(K0 K)) ^ j * frK (LT l) K dj =
        (frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) ∧
      (j = e → dj = (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d) := by
    intro j
    by_cases hje : j = e
    · subst hje
      refine ⟨(((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d, fun _ => ⟨⟨?_, ?_⟩, fun _ => rfl⟩⟩
      · have h1 : ‖((1 + l ^ s : ℕ) : Om l) ^ j - 1‖ ≤ 1 := by
          have := IsUltrametricDist.norm_intCast_le_one (Om l) (((1 + l ^ s : ℕ) : ℤ) ^ j - 1)
          simpa using this
        have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ j - 1) * (d : Om l) := by simp
        rw [h2, norm_mul]
        exact mul_le_one₀ h1 (norm_nonneg _) hd
      · have h3 : ∑ i ∈ T, co j lam i * (ex l s i : ↥(K0 K)) ^ j =
            (((1 + l ^ s : ℕ) : ↥(K0 K)) ^ j - 1) * ∑ a ∈ primeTo l s, lam a := by
          rw [hTdef, Finset.sum_product, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          have := hne' a ha
          simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, Nat.cast_mul]
          field_simp
          ring
        rw [h3, map_mul, map_mul, ← hrec]
        simp only [map_sub, map_pow, map_natCast, map_one]
        ring
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · refine ⟨0, fun _ => ⟨⟨by simp, ?_⟩, fun h => absurd h hje⟩⟩
        rw [hTdef, Finset.sum_product]
        simp [co]
      · obtain ⟨dj, h1, h2⟩ := (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l (LT l) K).2 j hj
          ((frK (LT l) K ^ s) (∑ i ∈ T, co e lam i * (ex l s i : ↥(K0 K)) ^ j)) (by
            rw [norm_frK_pow, AddSubmonoidClass.coe_finsetSum]
            refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i hi => ?_
            have h2 : ((co e lam i * (ex l s i : ↥(K0 K)) ^ j : ↥(K0 K)) : Om l) =
              (co e lam i : Om l) * (ex l s i : Om l) ^ j := by simp
            rw [h2, norm_mul, norm_pow, norm_nat_eq_one (hc i hi).2]
            simpa using (hc i hi).1)
        exact ⟨dj, fun _ => ⟨⟨h1, h2⟩, fun h => absurd h hje⟩⟩
  choose D hD using hall
  obtain ⟨z, hz, hE⟩ := GlobalTheory.T.dualExp_teichmuller_power_sum_formula LT l AI hT K s hs e g hg hχ (ℕ × Bool) T (co e lam) (ex l s) D hc
    (fun j hj => (hD j hj).1)
  refine ⟨z, hz, ?_⟩
  have hlev : levSum (LT l) K s e T (co e lam) (ex l s) (D e) =
      (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * cycVal (LT l) K s e lam d := by
    rw [(hD e le_rfl).2 rfl]
    unfold levSum cycVal
    rw [mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_left_comm]
      congr 1
      rw [hTdef, Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have h0 := hne a ha
      have hz : (LT l).ζQ s ^ ((1 + l ^ s) * a * l ^ i) = (LT l).ζQ s ^ (a * l ^ i) := by
        rw [mul_assoc, add_mul, one_mul, pow_add, pow_mul _ (l ^ s), zeta_pow_self, one_pow, mul_one]
      have hco : (((frK (LT l) K ^ i) (lam a * ((a : ↥(K0 K)) ^ e)⁻¹) : ↥(K0 K)) : Om l) =
          (((frK (LT l) K ^ i) (lam a) : ↥(K0 K)) : Om l) * ((a : Om l) ^ e)⁻¹ := by
        rw [map_mul, map_inv₀, map_pow, map_natCast]
        simp
      simp only [Fintype.sum_bool, co, ex, if_true, Bool.false_eq_true, if_false, map_neg,
        NegMemClass.coe_neg, hco, hz, Nat.cast_mul]
      field_simp
      ring
    · have h2 : ((((((1 + l ^ s : ℕ) : ↥(K0 K)) ^ e - 1) * d : ↥(K0 K))) : Om l) =
            (((1 + l ^ s : ℕ) : Om l) ^ e - 1) * (d : Om l) := by simp
      rw [h2]
      ring
  rw [hlev] at hE
  convert hE using 1
  rw [div_eq_mul_inv, map_mul, map_sub, map_pow, map_natCast, map_one]
  ring

end GlobalTheory.ExpImage.PosWeight
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicTowerFrobeniusFormulaPosWeightStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.cyclotomicTower_frobenius_formula_pos_weight : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ), 1 ≤ e → ∀ (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 → d - (l : ↥(K0 K)) ^ e * frK (LT l) K d = (frK (LT l) K ^ s) (∑ a ∈ primeTo l s, lam a) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) ((((1 + l ^ s : ℕ) : ℚ_[l]) ^ e - 1) / (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))) * cycVal (LT l) K s e lam d) := by
  first | exact @GlobalTheory.ExpImage.PosWeight.formula_pos | exact GlobalTheory.ExpImage.PosWeight.formula_pos | (intros; apply GlobalTheory.ExpImage.PosWeight.formula_pos <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExponentialImageContainsLattice

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

noncomputable section

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime]

theorem norm_algebraMap_mul (κ : ℚ_[l]) (α : Om l) :
    ‖algebraMap ℚ_[l] (Om l) κ * α‖ = ‖κ‖ * ‖α‖ := by
  rw [norm_mul, PadicAlgCl.norm_extends]

theorem exists_gen (P : LocPrime l) (K : FinExt l) {s : ℕ} (hs : Lev l s) :
    ∃ g ∈ Gj K s, (P.χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) := by
  have hn : ‖((1 + l ^ s : ℕ) : ℚ_[l]) - 1‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hu : ‖((1 + l ^ s : ℕ) : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hs.1
    rw [hk, pow_succ]
    simp
  obtain ⟨g, hg, hχ⟩ := (GlobalTheory.Cyc.finrank_Ks_and_chi_surjective l K).2 P.χQ P.χQ_cyc _ hu
  exact ⟨g, (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g hg).1 s).2 (by rw [hχ, hn]), hχ⟩

theorem expStar_image : ∀ (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ e : ℕ, ∀ α : Om l, α ∈ Ks K s → ‖α‖ ≤ 1 → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar D.loc (Gj K s) e z ((l : Om l) ^ (betaE l s e) * α) := by
  intro D l _ K s hs e α hα hα1
  obtain ⟨g, hg, hχ⟩ := exists_gen (D.loc l) K hs
  set u : ℚ_[l] := ((1 + l ^ s : ℕ) : ℚ_[l]) with hu
  have hl0 : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hlr : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hn : ‖u - 1‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [hu]
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hlog : ‖logZl l u‖ = (l : ℝ) ^ (-(s : ℤ)) := by
    rw [(GlobalTheory.PadicLogUnits.logZl_hom l).2.2.2 s hs.1 hs.2 u hn.le, hn]
  have key : ∀ ρ : ℚ_[l], ‖ρ‖ = (l : ℝ) ^ (((e + 1) * (s - 1) : ℕ) - betaE l s e) →
      (∀ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) → ‖(d : Om l)‖ ≤ 1 →
        d - (l : ↥(K0 K)) ^ e * frK (D.loc l) K d = (frK (D.loc l) K ^ s) (∑ a ∈ primeTo l s, lam a) →
        ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar D.loc (Gj K s) e z
          (algebraMap ℚ_[l] (Om l) ρ * cycVal (D.loc l) K s e lam d)) →
      ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧
        ExpStar D.loc (Gj K s) e z ((l : Om l) ^ (betaE l s e) * α) := by
    intro ρ hρ H
    have hρ0 : ρ ≠ 0 := by
      rw [← norm_ne_zero_iff, hρ]
      exact (zpow_pos hlr _).ne'
    set κ : ℚ_[l] := (l : ℚ_[l]) ^ (betaE l s e) / (ρ * (l : ℚ_[l]) ^ ((e + 1) * (s - 1))) with hκ
    have hκ1 : ‖κ‖ = 1 := by
      rw [hκ, norm_div, norm_mul, hρ, Padic.norm_p_zpow, Padic.norm_p_pow, ← zpow_add₀ hlr.ne',
        div_eq_one_iff_eq (zpow_pos hlr _).ne']
      congr 1
      ring
    obtain ⟨lam, d, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_cyclotomicFrobeniusTwistedValue_eq_pow_mul l (D.loc l) K s e hs.1 (algebraMap ℚ_[l] (Om l) κ * α)
      (mul_mem (IntermediateField.algebraMap_mem _ _) hα) (by rw [norm_algebraMap_mul, hκ1, one_mul]; exact hα1)
    obtain ⟨z, hz, hE⟩ := H lam d h1 h2 h3
    refine ⟨z, hz, ?_⟩
    convert hE using 1
    have : ρ * (l : ℚ_[l]) ^ ((e + 1) * (s - 1)) * κ = (l : ℚ_[l]) ^ (betaE l s e) := by
      rw [hκ]
      field_simp
    have h5 := congrArg (algebraMap ℚ_[l] (Om l)) this
    rw [map_mul, map_mul, map_pow, map_zpow₀, map_natCast] at h5
    rw [h4, ← h5]
    ring
  obtain ⟨s', rfl⟩ := Nat.exists_eq_add_of_le' hs.1
  rcases Nat.eq_zero_or_pos e with rfl | he
  · refine key (logZl l u * (((0 : ℕ).factorial : ℚ_[l]) * (l : ℚ_[l]) ^ ((s' + 1) * 0)))⁻¹ ?_ ?_
    · simp only [Nat.factorial_zero, Nat.cast_one, mul_zero, pow_zero, mul_one, norm_inv, hlog, betaE]
      rw [← zpow_neg]
      congr 1
      simp
    · intro lam d h1 h2 h3
      have := GlobalTheory.T.dualExp_teichmuller_power_sum_formula D.loc l (D.locA l) (D.locT l) K (s' + 1) hs 0 g hg hχ ℕ (primeTo l (s' + 1)) lam id
        (fun _ => d) (fun i hi => ⟨h1 i, (Finset.mem_filter.1 hi).2⟩)
        (fun j hj => by
          obtain rfl : j = 0 := Nat.le_zero.1 hj
          exact ⟨h2, by simpa using h3⟩)
      convert this using 5
      simp [cycVal, levSum]
  · refine key _ ?_ (GlobalTheory.T.cyclotomicTower_frobenius_formula_pos_weight D.loc l (D.locA l) (D.locT l) K (s' + 1) hs e he g hg hχ)
    obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le' he
    have h6 := GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one l (s' + 1) hs u hn ((e' + 1 : ℕ) : ℤ) (by omega)
    rw [zpow_natCast, padicValInt.of_nat] at h6
    have h7 : ‖(((e' + 1).factorial : ℕ) : ℚ_[l])‖ =
        (l : ℝ) ^ (-((padicValNat l (e' + 1) : ℤ) + (padicValNat l e'.factorial : ℤ))) := by
      rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast (e' + 1).factorial_ne_zero),
        Padic.valuation_natCast, ← Nat.padicValNat_def, Nat.factorial_succ,
        (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero _) e'.factorial_ne_zero]
      push_cast
      rfl
    rw [← hu, norm_div, norm_mul, norm_mul, h6, hlog, h7, Padic.norm_p_pow, ← zpow_add₀ hlr.ne',
      ← zpow_add₀ hlr.ne', ← zpow_sub₀ hlr.ne']
    congr 1
    simp only [betaE, Nat.add_sub_cancel, Nat.succ_ne_zero, if_false]
    push_cast
    have hv : padicValRat l ((e' : ℚ) + 1) = (padicValNat l (e' + 1) : ℤ) := by
      simpa [Nat.add_comm, Nat.padicValNat_def] using (padicValRat_of_nat (p := l) (e' + 1)).symm
    rw [hv]
    ring

end GlobalTheory.ExpImage
end
end
end
