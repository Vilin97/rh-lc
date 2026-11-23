module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NatCastMulCoeffCharpolyRev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpan
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffCharpolyRevMemTracePowerProductRealSpan

section

@[expose] public section

set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem trace_pow_mul_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι)
    (j w : ℕ) (hj : 1 ≤ j) (f : Mat m S → S) (hf : f ∈ TrSpan m w S) :
    (fun A : Mat m S => ((A τ) ^ j).trace * f A) ∈ TrSpan m (j + w) S := by
  unfold TrSpan at hf
  induction hf using Submodule.span_induction with
  | mem f h =>
    obtain ⟨l, hl, hw, rfl⟩ := h
    refine Submodule.subset_span ⟨(τ, j) :: l, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hj
      · exact hl x hx
    · simp [hw]
    · funext A
      simp [trProd]
  | zero =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (0 : Mat m S → S) A) = 0 := by
      funext A; simp
    rw [this]; exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (f + g) A) =
        (fun A : Mat m S => ((A τ) ^ j).trace * f A) + (fun A : Mat m S => ((A τ) ^ j).trace * g A) := by
      funext A; simp [mul_add]
    rw [this]; exact Submodule.add_mem _ hf hg
  | smul c f _ hf =>
    have : (fun A : Mat m S => ((A τ) ^ j).trace * (c • f) A) =
        c • (fun A : Mat m S => ((A τ) ^ j).trace * f A) := by
      funext A; simp
    rw [this]; exact Submodule.smul_mem _ c hf

theorem coeff_charpolyRev_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (τ : ι) (k : ℕ) :
    (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) ∈ TrSpan m k S := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · refine Submodule.subset_span ⟨[], by simp, by simp, ?_⟩
      funext A
      simp [trProd, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
    · have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
      have key : (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) =
          (-(k : ℝ)⁻¹) • ∑ i ∈ Finset.range k, ((-1 : ℝ) ^ (i + 1)) •
            (fun A : Mat m S => ((A τ) ^ (i + 1)).trace *
              (Matrix.charpolyRev (-(A τ))).coeff (k - 1 - i)) := by
        funext A
        have h := GlobalTheory.natCast_mul_coeff_charpolyRev (-(A τ)) k
        have e : ∀ i : ℕ, ((-(A τ)) ^ (i + 1)).trace = ((-1 : ℝ) ^ (i + 1)) • ((A τ) ^ (i + 1)).trace := by
          intro i
          rw [← neg_one_smul ℝ (A τ), smul_pow, Matrix.trace_smul]
        simp only [e, smul_mul_assoc] at h
        simp only [Pi.smul_apply, Finset.sum_apply]
        rw [neg_smul, ← smul_neg, ← h, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
          inv_mul_cancel₀ hk', one_smul]
      rw [key]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_)
      have hi' := Finset.mem_range.1 hi
      have h := trace_pow_mul_mem_trSpan m S τ (i + 1) (k - 1 - i) (by omega) _ (ih (k - 1 - i) (by omega))
      rwa [show i + 1 + (k - 1 - i) = k by omega] at h

end GlobalTheory.GoodMetric.ChernSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffCharpolyRevMemTracePowerProductRealSpanStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.coeff_charpolyRev_mem_tracePowerProductRealSpan : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (τ : ι) (k : ℕ), (fun A : Mat m S => (Matrix.charpolyRev (-(A τ))).coeff k) ∈ TrSpan m k S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.coeff_charpolyRev_mem_trSpan | exact GlobalTheory.GoodMetric.ChernSpan.coeff_charpolyRev_mem_trSpan | (intros; apply GlobalTheory.GoodMetric.ChernSpan.coeff_charpolyRev_mem_trSpan <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerListProductMemChernCoefficientRealSpanStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (l : List (ι × ℕ)), (∀ x ∈ l, 1 ≤ x.2) → (l.map Prod.snd).sum = n → (fun A : Mat m S => trProd l A) ∈ Reach m n S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | exact GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trProd_mem_reach <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerProductRealSpanMulMem

section

@[expose] public section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem trSpan_mul : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w w' : ℕ)
    (f g : Mat m S → S), f ∈ TrSpan m w S → g ∈ TrSpan m w' S → f * g ∈ TrSpan m (w + w') S := by
  intro ι m S _ _ w w' f g hf hg
  induction hf using Submodule.span_induction with
  | mem x hx =>
    induction hg using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨l, hl1, hlw, rfl⟩ := hx
      obtain ⟨l', hl1', hlw', rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨l ++ l', ?_, ?_, ?_⟩
      · intro x hx
        rcases List.mem_append.1 hx with h | h
        · exact hl1 x h
        · exact hl1' x h
      · simp [List.map_append, List.sum_append, hlw, hlw']
      · funext A
        simp [trProd, List.map_append, List.prod_append]
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
    | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x z _ _ hx hz => rw [add_mul]; exact add_mem hx hz
  | smul a x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ a hx

end GlobalTheory.GoodMetric.ChernSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowerProductRealSpanMulMemStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.tracePowerProductRealSpan_mul_mem : ∀ {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w w' : ℕ) (f g : Mat m S → S), f ∈ TrSpan m w S → g ∈ TrSpan m w' S → f * g ∈ TrSpan m (w + w') S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.trSpan_mul | exact GlobalTheory.GoodMetric.ChernSpan.trSpan_mul | (intros; apply GlobalTheory.GoodMetric.ChernSpan.trSpan_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AevalWeightedHomogeneousChernMemChernCoefficient

section

@[expose] public section

set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem one_mem_trSpan_zero {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] :
    (1 : Mat m S → S) ∈ TrSpan m 0 S := by
  unfold TrSpan
  exact Submodule.subset_span ⟨[], by simp, by simp, by funext A; simp [trProd]⟩

theorem pow_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w : ℕ)
    (f : Mat m S → S) (hf : f ∈ TrSpan m w S) (e : ℕ) : f ^ e ∈ TrSpan m (e * w) S := by
  induction e with
  | zero => simpa using one_mem_trSpan_zero m S
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact GlobalTheory.T.tracePowerProductRealSpan_mul_mem m S (k * w) w _ _ ih hf

theorem prod_mem_trSpan {ι κ : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (s : Finset κ)
    (w : κ → ℕ) (f : κ → Mat m S → S) (hf : ∀ x ∈ s, f x ∈ TrSpan m (w x) S) :
    ∏ x ∈ s, f x ∈ TrSpan m (∑ x ∈ s, w x) S := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using one_mem_trSpan_zero m S
  · intro a t ha ih hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact GlobalTheory.T.tracePowerProductRealSpan_mul_mem m S _ _ _ _ (hf a (Finset.mem_insert_self a t))
      (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

theorem trSpan_le_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] :
    TrSpan m n S ≤ Reach m n S := by
  unfold TrSpan
  rw [Submodule.span_le]
  rintro f ⟨l, hl, hs, rfl⟩
  exact GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan m n S l hl hs

theorem aeval_chern_mem_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (R : MvPolynomial (ι × ℕ) ℝ) (hR : R.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) n) :
    (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) ∈ Reach m n S := by
  refine trSpan_le_reach m n S ?_

  have key : ∀ d ∈ R.support, (fun A : Mat m S =>
      aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d)))
        ∈ TrSpan m n S := by
    intro d hd
    have hdeg : Finsupp.weight Prod.snd d = n := hR (mem_support_iff.mp hd)
    have hprod := prod_mem_trSpan m S d.support (fun x => d x * x.2)
      (fun x (A : Mat m S) => (Matrix.charpolyRev (-(A x.1))).coeff x.2 ^ d x)
      (fun x _ => pow_mem_trSpan m S x.2 _ (GlobalTheory.T.coeff_charpolyRev_mem_tracePowerProductRealSpan m S x.1 x.2) (d x))
    have hw : ∑ x ∈ d.support, d x * x.2 = n := by
      rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
      simp [smul_eq_mul]
    rw [hw] at hprod
    convert Submodule.smul_mem _ (R.coeff d) hprod using 1
    funext A
    simp [aeval_monomial, Finsupp.prod, Finset.prod_apply, Algebra.smul_def]
  have hsum : (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) =
      ∑ d ∈ R.support, fun A : Mat m S =>
        aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d)) := by
    funext A
    conv_lhs => rw [R.as_sum]

    simp only [map_sum, Finset.sum_apply]
  rw [hsum]
  exact Submodule.sum_mem _ key

end GlobalTheory.GoodMetric.ChernSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AevalWeightedHomogeneousChernMemChernCoefficientStatement

section

@[expose] public section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

theorem _root_.GlobalTheory.T.aeval_weightedHomogeneous_chern_mem_chernCoefficientSpan : ∀ {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (R : MvPolynomial (ι × ℕ) ℝ), R.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) n → (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) ∈ Reach m n S := by
  first | exact @GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach | exact GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach | (intros; apply GlobalTheory.GoodMetric.ChernSpan.aeval_chern_mem_reach <;> assumption)
end
end
