module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ShintaniValuesNegativeIntegersRationalStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SizePowerLeInverseSquareProductStatement
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.PartialSum
import Formalism.SharpRestriction.GlobalSchurBounds.ShortIntervalPrimes
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceConeTermEq

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem cast_add_single_one {r : ℕ} (m : Fin r → ℕ) (c : Fin r) :
    (fun i => (((m + Pi.single c 1 : Fin r → ℕ) i : ℕ) : ℝ)) =
      (fun i => (m i : ℝ)) + Pi.single c 1 := by
  funext i
  by_cases h : i = c
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem DL_coneTerm_eq_DLR : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (cs : List (Fin r)) (m : Fin r → ℕ),
  DL cs (coneTerm a b s) m = DLR cs (Fr a b s 0) (fun i => (m i : ℝ)) := by
  intro ι _ r a b s cs m
  induction cs generalizing m with
  | nil => simp [DL, DLR, coneTerm, Fr, linF]
  | cons c cs ih =>
    have h1 : DL (c :: cs) (coneTerm a b s) m =
        DL cs (coneTerm a b s) (m + Pi.single c 1) - DL cs (coneTerm a b s) m := rfl
    have h2 : ∀ x : Fin r → ℝ, DLR (c :: cs) (Fr a b s 0) x =
        DLR cs (Fr a b s 0) (x + Pi.single c 1) - DLR cs (Fr a b s 0) x := fun _ => rfl
    rw [h1, h2, ih, ih, cast_add_single_one]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDifferenceConeTermEqStatement

section

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.finite_difference_cone_term_eq : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (s : ℂ) (cs : List (Fin r)) (m : Fin r → ℕ),
  DL cs (coneTerm a b s) m = DLR cs (Fr a b s 0) (fun i => (m i : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_eq_DLR <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.HighDifferenceVanishesNegativeInteger

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem coneTerm_differentiable_in_s_alt {ι : Type} [Fintype ι] {r : ℕ} {a : ι → Fin r → ℝ} {b : ι → ℝ}
    (ha : ∀ j i, 0 < a j i) (hb : ∀ j, 0 < b j) (m : Fin r → ℕ) :
    Differentiable ℂ (fun s => coneTerm a b s m) := by
  unfold GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.coneTerm
  refine Differentiable.fun_finsetProd fun j _ => ?_
  refine Differentiable.const_cpow differentiable_neg (Or.inl ?_)
  have hpos : 0 < b j + ∑ i, a j i * (m i : ℝ) :=
    add_pos_of_pos_of_nonneg (hb j)
      (Finset.sum_nonneg fun i _ => mul_nonneg (ha j i).le (Nat.cast_nonneg _))
  exact Complex.ofReal_ne_zero.mpr hpos.ne'

theorem DL_coneTerm_differentiable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ),
    (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (cs : List (Fin r)) (m : Fin r → ℕ),
      Differentiable ℂ (fun s => DL cs (coneTerm a b s) m) := by
  intro ι _ r a b ha hb cs
  induction cs with
  | nil => intro m; exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.coneTerm_differentiable_in_s_alt ha hb m
  | cons c cs ih =>
    intro m
    simp only [GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL, List.foldr_cons, GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.fd] at ih ⊢
    exact (ih (m + Pi.single c 1)).sub (ih m)

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.HighDifferenceVanishesNegativeIntegerStatement

section

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.finite_difference_cone_term_differentiable : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (cs : List (Fin r)) (m : Fin r → ℕ), Differentiable ℂ (fun s => DL cs (coneTerm a b s) m) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.DL_coneTerm_differentiable <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableInverseSquareProduct

section

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem summable_inv_one_add_sq :
    Summable (fun n : ℕ => ((1 + (n : ℝ)) ^ 2)⁻¹) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine ((summable_nat_add_iff 1).mpr h).congr fun n => ?_
  simp only [Nat.cast_add, Nat.cast_one, one_div, add_comm (n : ℝ) 1]

theorem summable_prod_inv_one_add_sq :
    ∀ r : ℕ, Summable (fun m : Fin r → ℕ => ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹) := by
  intro r
  induction r with
  | zero => exact Summable.of_finite
  | succ r ih =>
    have h := GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_inv_one_add_sq.mul_of_nonneg ih
      (fun n => inv_nonneg.mpr (sq_nonneg _))
      (fun m => Finset.prod_nonneg fun i _ => inv_nonneg.mpr (sq_nonneg _))
    rw [← (Fin.consEquiv fun _ : Fin (r + 1) => ℕ).summable_iff]
    refine h.congr fun p => ?_
    simp [Fin.consEquiv, Fin.prod_univ_succ, mul_comm]

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableInverseSquareProductStatement

section

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.summable_inverse_square_product : ∀ r : ℕ, Summable (fun m : Fin r → ℕ => ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_prod_inv_one_add_sq <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.WeightSumAsFiniteDifferences

section

@[expose] public section

set_option autoImplicit false

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem differentiableOn_tsum_weighted_DL_halfplane : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B N : ℕ) (cs : List (Fin r)) (u : (Fin r → ℕ) → ℚ), Fintype.card ι * B + 2 ≤ N → BddW u →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m) {s | -(B : ℝ) < s.re} := by
  intro ι _ r a b ha hb B N cs u hN hu hsupp
  classical
  obtain ⟨Cu, hCu⟩ := hu
  have hCu0 : 0 ≤ Cu := (abs_nonneg _).trans (hCu 0)
  have hopen : ∀ R : ℕ, IsOpen {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := fun R =>
    (isOpen_lt continuous_norm continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  have key : ∀ R : ℕ, DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m)
      {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := by
    intro R
    obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.real_difference_cone_bound ι r a b ha hb B R cs 0
    refine Complex.differentiableOn_tsum_of_summable_norm
      (u := fun m : Fin r → ℕ => Cu * C * ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹)
      ((GlobalTheory.T.summable_inverse_square_product r).mul_left _) ?_ (hopen R) ?_
    · intro m
      exact ((GlobalTheory.T.finite_difference_cone_term_differentiable ι r a b ha hb cs m).const_mul _).differentiableOn
    · intro m s hs
      have hprod : 0 ≤ ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ :=
        Finset.prod_nonneg fun i _ => by positivity
      by_cases hum : u m = 0
      · simp only [hum, Rat.cast_zero, zero_mul, norm_zero]
        positivity
      · have hcount : ∀ i, cs.count i = N ∨ m i = 0 := by
          intro i
          rcases hsupp i with h | h
          · exact Or.inl h
          · exact Or.inr (by_contra fun hne => hum (h m hne))
        have hbound := hC s hs.1.le hs.2.le (fun i => (m i : ℝ)) (fun i => Nat.cast_nonneg _)
        simp only [Pi.zero_apply, Nat.cast_zero, Finset.sum_const_zero, sub_zero] at hbound
        have hsize := GlobalTheory.T.size_power_le_inverse_square_product r (Fintype.card ι) B N cs m hN hcount
        have hDL : ‖DL cs (coneTerm a b s) m‖ ≤ C * ∏ i, ((1 + (m i : ℝ)) ^ 2)⁻¹ := by
          rw [GlobalTheory.T.finite_difference_cone_term_eq ι r a b s cs m]
          exact hbound.trans (mul_le_mul_of_nonneg_left hsize hC0)
        rw [norm_mul, Complex.norm_ratCast, mul_assoc]
        exact mul_le_mul (hCu m) hDL (norm_nonneg _) hCu0
  intro s hs
  obtain ⟨R, hR⟩ := exists_nat_gt ‖s‖
  have hmem : s ∈ {s : ℂ | ‖s‖ < (R : ℝ) ∧ -(B : ℝ) < s.re} := ⟨hR, hs⟩
  exact ((key R s hmem).differentiableAt ((hopen R).mem_nhds hmem)).differentiableWithinAt

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.WeightSumAsFiniteDifferencesStatement

section

@[expose] public section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.cone_series_differentiable_left_strip : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ), (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → ∀ (B N : ℕ) (cs : List (Fin r)) (u : (Fin r → ℕ) → ℚ), Fintype.card ι * B + 2 ≤ N → BddW u →
  (∀ i, cs.count i = N ∨ ∀ m, m i ≠ 0 → u m = 0) →
  DifferentiableOn ℂ (fun s => ∑' m, (u m : ℂ) * DL cs (coneTerm a b s) m) {s | -(B : ℝ) < s.re} := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.differentiableOn_tsum_weighted_DL_halfplane | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.differentiableOn_tsum_weighted_DL_halfplane | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.differentiableOn_tsum_weighted_DL_halfplane <;> assumption)
end
end
