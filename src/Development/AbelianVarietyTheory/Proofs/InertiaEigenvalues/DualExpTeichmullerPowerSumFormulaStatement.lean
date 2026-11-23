module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfCocycleSolutionTeichmullerEpsilonRootPowStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDeRhamElementOfCocycleRecursionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftsOfNormLeOneStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpStarOfLowTermsRemovedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusEquationLiftAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonRootPowSubZetaExpMemFiltrationStatement
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
import Mathlib.RingTheory.PiTensorProduct
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

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSolutionExpansionModFiltration

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ExpImage.Expand

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l x ^ l := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem root_pow (AI : LocAinf l P) (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ m ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem epsT_pow (AI : LocAinf l P) (s : ℕ) :
    epsT AI s ^ (l ^ s) = WittVector.teichmuller l AI.ε := by
  rw [epsT, ← map_pow, root_pow]

theorem lifts_iter {AI : LocAinf l P} {K : FinExt l} {w : Ainf l} {c : ↥(K0 K)}
    (h : Lifts AI K w c) (k : ℕ) :
    Lifts AI K ((WittVector.frobenius : Ainf l → Ainf l)^[k] w) ((frK P K ^ k) c) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ', AlgHom.mul_apply]
    exact ih.frob

theorem qB_eq (z : ℚ_[l]) : qB P z = oB P (algebraMap ℚ_[l] (Om l) z) :=
  IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR z

theorem coeff_eq (K : FinExt l) (s j : ℕ) {ι : Type} (T : Finset ι) (c : ι → ↥(K0 K))
    (m : ι → ℕ) (d : ↥(K0 K)) :
    algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
        levSum P K s j T c m d =
      ∑ k ∈ Finset.range s, ∑ i ∈ T, (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (P.ζQ s ^ (m i * l ^ k) * algebraMap ℚ_[l] (Om l)
            ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]))) +
        algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l])⁻¹) * (d : Om l) := by
  have hl : (l : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hj : (j.factorial : ℚ_[l]) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [levSum, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j / (j.factorial : ℚ_[l]) =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * ((l : ℚ_[l]) ^ (j * k) * (m i : ℚ_[l]) ^ j) := by
      push_cast
      rw [div_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm k j]
      field_simp
    rw [e, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]
    ring
  · have e : (j.factorial : ℚ_[l])⁻¹ =
        ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * (l : ℚ_[l]) ^ (s * j) := by
      field_simp
    rw [e, map_mul, map_pow, map_natCast, mul_assoc]

theorem expand : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = (frK P K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * epsT AI s ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j ∈ FilB P (M : ℤ) := by
  intro l _ P AI TT K s ι T w c m M d hM hw hd
  obtain ⟨y₁, h1, h2⟩ := GlobalTheory.T.frobenius_equation_lift_Ainf l P AI TT K ι T
    (fun i => (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i)) (fun i => (frK P K ^ s) (c i)) m M d hM
    (fun i hi => lifts_iter (hw i hi) s) (fun j hj => ⟨(hd j hj).1, by

      rw [(hd j hj).2, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, map_natCast]⟩)
  set H : ℕ → Ainf l := fun k =>
    ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[k] (w i) * epsT AI s ^ (m i * l ^ k) with hH
  have hφ : ∀ k, WittVector.frobenius (H k) = H (k + 1) := by
    intro k
    simp only [hH]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow, Function.iterate_succ_apply', epsT, frob_teich, ← pow_mul]
    congr 2
    ring
  have hs : H s = ∑ i ∈ T, (WittVector.frobenius : Ainf l → Ainf l)^[s] (w i) *
      WittVector.teichmuller l AI.ε ^ m i := by
    simp only [hH]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (m i), pow_mul, epsT_pow]
  have h0 : H 0 = ∑ i ∈ T, w i * epsT AI s ^ m i := by simp [hH]
  refine ⟨∑ k ∈ Finset.range s, H k + y₁, ?_, ?_⟩
  · have ht := Finset.sum_range_sub' H s
    rw [Finset.sum_sub_distrib] at ht

    rw [map_add (f := _), map_sum, Finset.sum_congr rfl (fun k _ => hφ k), ← h0]
    rw [← hs] at h1
    linear_combination ht + h1
  · have hk : ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
        (io AI (epsT AI s ^ (m i * l ^ k)) - oB P (P.ζQ s ^ (m i * l ^ k)) *
          ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
            (j.factorial : ℚ_[l])) * tD P ^ j) ∈ FilB P (M : ℤ) := by
      refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i hi => ?_
      refine FilB_zero_mul ?_ (GlobalTheory.T.teichmullerEpsilonRoot_pow_sub_zeta_exp_mem_filtration l P AI TT s (m i * l ^ k) M)
      rw [← (lifts_iter (hw i hi) k).io_eq]
      exact io_mem AI _
    have e1 : io AI (∑ k ∈ Finset.range s, H k) = ∑ k ∈ Finset.range s, ∑ i ∈ T,
        oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) * io AI (epsT AI s ^ (m i * l ^ k)) := by

      rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [hH]

      rw [map_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [map_mul, (lifts_iter (hw i hi) k).io_eq]
    have e2 : ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l)
          ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j =
        ∑ k ∈ Finset.range s, ∑ i ∈ T, oB P (((frK P K ^ k) (c i) : ↥(K0 K)) : Om l) *
          (oB P (P.ζQ s ^ (m i * l ^ k)) *
            ∑ j ∈ Finset.range M, qB P ((((m i * l ^ k : ℕ) : ℚ_[l]) / (l : ℚ_[l]) ^ s) ^ j /
              (j.factorial : ℚ_[l])) * tD P ^ j) +
        ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * oB P (d j : Om l) * tD P ^ j := by

      simp only [coeff_eq, map_add (f := _), map_sum, map_mul, ← qB_eq, add_mul, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    have := add_mem hk h2
    rw [map_add (f := _), e1, e2]
    convert this using 1
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring

end GlobalTheory.ExpImage.Expand
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSolutionExpansionModFiltrationStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.frobeniusSolution_expansion_mod_filtration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (ι : Type) (T : Finset ι) (w : ι → Ainf l) (c : ι → ↥(K0 K)) (m : ι → ℕ) (M : ℕ) (d : ℕ → ↥(K0 K)), 1 ≤ M → (∀ i ∈ T, Lifts AI K (w i) (c i)) → (∀ j < M, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK P K (d j) = (frK P K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ y : Ainf l, y - WittVector.frobenius y = ∑ i ∈ T, w i * epsT AI s ^ m i ∧ io AI y - ∑ j ∈ Finset.range M, oB P (algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ * levSum P K s j T c m (d j)) * tD P ^ j ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.Expand.expand | exact GlobalTheory.ExpImage.Expand.expand | (intros; apply GlobalTheory.ExpImage.Expand.expand <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExpTeichmullerPowerSumFormula

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ExpImage

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem exists_inv_pow_one_add {l : ℕ} [Fact l.Prime] {s : ℕ} (hs : 1 ≤ s) (e : ℕ) (u : ℚ_[l]ˣ)
    (hu : (u : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l])) :
    ∃ U : ℤ_[l], (U : ℚ_[l]) = ((u ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) ∧ (l : ℤ_[l]) ^ s ∣ U - 1 := by
  have hn : (-(l : ℤ_[l]) ^ s) ∈ nonunits ℤ_[l] := by
    rw [PadicInt.mem_nonunits, norm_neg, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)) (by omega)
  have hunit := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hn
  obtain ⟨V, hV⟩ := hunit.exists_left_inv
  refine ⟨V ^ e, ?_, ?_⟩
  · have h1 : (V : ℚ_[l]) * (u : ℚ_[l]) = 1 := by
      have := congrArg (fun z : ℤ_[l] => (z : ℚ_[l])) hV
      rw [hu]
      push_cast at this ⊢
      linear_combination this
    have h2 : (V : ℚ_[l]) = (u : ℚ_[l])⁻¹ := eq_inv_of_mul_eq_one_left h1
    simp [h2]
  · have h1 : (l : ℤ_[l]) ^ s ∣ V - 1 := ⟨-V, by linear_combination hV⟩
    have h2 := sub_dvd_pow_sub_pow V 1 e
    rw [one_pow] at h2
    exact h1.trans h2

theorem zetaQ_pow_level {l : ℕ} [Fact l.Prime] (P : LocPrime l) (s : ℕ) : P.ζQ s ^ (l ^ s) = 1 := by
  induction s with
  | zero => simpa using P.ζQ_zero
  | succ s ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem levSum_mem_Ks {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s j : ℕ) {ι : Type}
    (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ↥(K0 K)) :
    levSum P K s j T c m d ∈ Ks K s := by
  have h0 : ∀ x : ↥(K0 K), (x : Om l) ∈ Ks K s := fun x => (le_sup_left : K0 K ≤ Ks K s) x.2
  have hζ : P.ζQ s ∈ Ks K s := by
    refine (le_sup_right : _ ≤ Ks K s) (IntermediateField.subset_adjoin _ _ ?_)
    exact zetaQ_pow_level P s
  unfold levSum
  refine add_mem (sum_mem fun i _ => mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun a _ =>
    mul_mem (mul_mem (h0 _) (pow_mem (natCast_mem _ _) _)) (pow_mem hζ _)))
    (mul_mem (pow_mem (natCast_mem _ _) _) (h0 _))

theorem expStar_levSum : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (ι : Type) (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ℕ → ↥(K0 K)), (∀ i ∈ T, ‖(c i : Om l)‖ ≤ 1 ∧ ¬ l ∣ m i) → (∀ j ≤ e, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK (LT l) K (d j) = (frK (LT l) K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))⁻¹ * levSum (LT l) K s e T c m (d e)) := by
  intro LT l _ AI hT K s hs e g hg hχ ι T c m d hc hd
  classical
  obtain ⟨U, hU, hU1⟩ := exists_inv_pow_one_add hs.1 e ((LT l).χQ g) hχ
  have hgen : IsGen (LT l).χQ K s g := by
    refine ⟨hg, ?_⟩
    rw [hχ]
    push_cast
    rw [add_sub_cancel_left, Padic.norm_p_pow]
  have hw : ∀ i, ∃ w : Ainf l, i ∈ T → Lifts AI K w (c i) := by
    intro i
    by_cases hi : i ∈ T
    · obtain ⟨w, hw⟩ := GlobalTheory.T.exists_lifts_of_norm_le_one_alt l (LT l) AI hT K (c i) (hc i hi).1
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose w hw using hw
  obtain ⟨y, hy, hexp⟩ := GlobalTheory.T.frobeniusSolution_expansion_mod_filtration l (LT l) AI hT K s ι T w c m (e + 1) d (by omega) hw
    (fun j hj => hd j (by omega))
  have hsolv : Solv AI K s g U (y - WittVector.frobenius y) := by
    rw [hy]
    refine Solv.sum T _ fun i hi => ?_
    exact (GlobalTheory.T.ainfCocycleSolution_teichmullerEpsilonRoot_pow l (LT l) AI K s hs g hχ U hU1 (m i) (hc i hi).2).mul
      ((hw i hi).act (Gj_le_fix s hg)) (fun h hh => (hw i hi).act (Hinf_le_fix hh))
  obtain ⟨b, hb0, hbH, z₀, hz₀⟩ := GlobalTheory.T.exists_deRham_element_of_cocycleRecursion l (LT l) AI hT K s hs g U (e + 1) (by omega) y hsolv
  obtain ⟨z, hz, hE⟩ := GlobalTheory.T.expStar_of_low_terms_removed LT l AI hT K s hs e g hgen
    (fun j => algebraMap ℚ_[l] (Om l) ((j.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * j))⁻¹ *
      levSum (LT l) K s j T c m (d j))
    (fun j => mul_mem (IntermediateField.algebraMap_mem _ _) (levSum_mem_Ks _ _ _ _ _ _ _ _))
    b hb0 hbH ⟨z₀, by
      have := add_mem hz₀ hexp
      rw [hU] at this
      convert this using 1
      ring⟩
  refine ⟨z, hz, ?_⟩
  rw [hχ, ← mul_assoc, ← map_mul, ← mul_inv] at hE
  exact hE

end GlobalTheory.ExpImage
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualExpTeichmullerPowerSumFormulaStatement

section

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

theorem _root_.GlobalTheory.T.dualExp_teichmuller_power_sum_formula : ∀ (LT : LocTheory) (l : ℕ) [Fact l.Prime] (AI : LocAinf l (LT l)), LocTied l (LT l) AI → ∀ (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (g : GQ l), g ∈ Gj K s → ((LT l).χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ (ι : Type) (T : Finset ι) (c : ι → ↥(K0 K)) (m : ι → ℕ) (d : ℕ → ↥(K0 K)), (∀ i ∈ T, ‖(c i : Om l)‖ ≤ 1 ∧ ¬ l ∣ m i) → (∀ j ≤ e, ‖(d j : Om l)‖ ≤ 1 ∧ d j - (l : ↥(K0 K)) ^ j * frK (LT l) K (d j) = (frK (LT l) K ^ s) (∑ i ∈ T, c i * (m i : ↥(K0 K)) ^ j)) → ∃ z : GQ l → ℚ_[l], (∀ σ ∈ Gj K s, ‖z σ‖ ≤ 1) ∧ ExpStar LT (Gj K s) e z (algebraMap ℚ_[l] (Om l) (logZl l ((1 + l ^ s : ℕ) : ℚ_[l]) * ((e.factorial : ℚ_[l]) * (l : ℚ_[l]) ^ (s * e)))⁻¹ * levSum (LT l) K s e T c m (d e)) := by
  first | exact @GlobalTheory.ExpImage.expStar_levSum | exact GlobalTheory.ExpImage.expStar_levSum | (intros; apply GlobalTheory.ExpImage.expStar_levSum <;> assumption)
end
end
