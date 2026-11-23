module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteIrrCharactersAndFinsumCentralIdempotentsEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTraceIdempotentAndIrreducibleDegreeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraTracePatternIdempotentExchangeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraInductionCharacterRestrictionDecompStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceUnitriangularColumnVanishingIdempotentEqSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotentsPropertiesPrimeFieldStatement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicTraceGeWhittakerDimensionGLn

section

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.MirabolicComparison

theorem tr_add {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f h : G → ℂ) :
    tr a (fun x => f x + h x) = tr a f + tr a h := by
  simp [tr, mul_add, Finset.sum_add_distrib]

theorem tr_mul_const {G : Type} [Group G] [Fintype G] (a : MonoidAlgebra ℂ G) (f : G → ℂ) (c : ℂ) :
    tr a (fun x => f x * c) = tr a f * c := by
  simp only [tr, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem tr_tr_list_nat {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H]
    (a : MonoidAlgebra ℂ G) (b : MonoidAlgebra ℂ H) (ha : a * a = a) (hb : b * b = b) :
    ∀ L : List ((G → ℂ) × (H → ℂ)), (∀ p ∈ L, IsChar p.1 ∧ IsChar p.2) →
      ∃ n : ℕ, tr a (fun x => tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) = n := by
  intro L
  induction L with
  | nil =>
    intro _
    exact ⟨0, by simp [tr]⟩
  | cons p L ih =>
    intro hL
    obtain ⟨m, hm⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    obtain ⟨n₁, hn₁⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree G a p.1).1 ha (hL p (List.mem_cons_self ..)).1
    obtain ⟨n₂, hn₂⟩ := (GlobalTheory.T.groupAlgebraTrace_idempotent_and_irreducible_degree H b p.2).1 hb (hL p (List.mem_cons_self ..)).2
    refine ⟨n₁ * n₂ + m, ?_⟩
    simp only [List.map_cons, List.sum_cons]
    rw [show (fun x => tr b (fun y => p.1 x * p.2 y + (L.map fun p => p.1 x * p.2 y).sum)) =
        (fun x => p.1 x * tr b p.2 + tr b (fun y => (L.map fun p => p.1 x * p.2 y).sum)) from by
      funext x
      rw [tr_add]
      congr 1
      simp only [tr, Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring]
    rw [tr_add, tr_mul_const, hm, hn₁, hn₂]
    push_cast
    ring

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV]
  exact FDRep.char_conj V x y

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, _, hV⟩ := h
  exact ⟨V, hV⟩

theorem wh_der_nat (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N i : ℕ) (hi : i ≤ N)
    (χ : Gn g N → ℂ) (hχ : IsChar χ) : ∃ n : ℕ, wh ψ (der ψ i χ) = n := by
  obtain ⟨L, hL, hLeq⟩ := (GlobalTheory.T.harishChandra_induction_character_restriction_decomp g i (N - i) N (by omega)).2 χ hχ
  have hres : (fun h : Gn g i => wh ψ (res i (N - i) χ h)) =
      fun h => tr (eU g (N - i) ψ) (fun y => (L.map fun p => p.1 h * p.2 y).sum) := by
    funext h
    simp only [wh]
    congr 1
    funext y
    exact hLeq h y
  show ∃ n : ℕ, tr (eU g i ψ) (fun h => wh ψ (res i (N - i) χ h)) = n
  rw [hres]
  exact tr_tr_list_nat _ _ (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g i 0 0 ψ).1 (GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g (N - i) 0 0 ψ).1 L
    (fun p hp => ⟨isChar_of_isIrr (hL p hp).1, isChar_of_isIrr (hL p hp).2⟩)

theorem wh_der_zero (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (N : ℕ) (χ : Gn g N → ℂ) :
    wh ψ (der ψ 0 χ) = wh ψ χ := by
  haveI : Subsingleton (Gn g 0) := ⟨fun a b => Units.ext (Subsingleton.elim _ _)⟩
  have h1 : (eU g 0 ψ).coeff 1 = 1 := by
    rw [(GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g 0 0 0 ψ).2.1]; simp
  have hres : res 0 (N - 0) χ 1 = χ := by
    funext y
    change Gn g N at y
    simp only [res, Nat.zero_mul, pow_zero, inv_one, one_mul]
    rw [Finset.sum_eq_single y]
    · have : InPar 0 ((y : Gn g N) : Mt g N) ∧ tl 0 ((y : Gn g N) : Mt g N) = ((1 : Gn g 0) : Mt g 0) ∧
          br 0 (N - 0) ((y : Gn g N) : Mt g N) = ((y : Gn g (N - 0)) : Mt g (N - 0)) := by
        refine ⟨fun i j hj _ => absurd hj (Nat.not_lt_zero _), Subsingleton.elim _ _, ?_⟩
        funext i j
        simp [br, entN]
      rw [if_pos this]
    · intro x _ hx
      rw [if_neg]
      rintro ⟨_, _, hb⟩
      apply hx
      apply Units.ext
      rw [← hb]
      funext i j
      simp [br, entN]
    · intro h; exact absurd (Finset.mem_univ _) h
  show tr (eU g 0 ψ) (fun h => wh ψ (res 0 (N - 0) χ h)) = wh ψ χ
  simp only [tr]
  rw [Fintype.sum_subsingleton _ 1, h1, one_mul, hres]

end GlobalTheory.GLq.MirabolicComparison

namespace GlobalTheory.GLq.MirabolicComparison

theorem mirabolic_comparison : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ),
    N = k + 2 * s + 1 → 1 ≤ k → ∀ χ : Gn g N → ℂ, IsChar χ →
      ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤ (tr (eJ g N k s ψ) χ).re := by
  intro g _ ψ hψ N k s hN hk χ hχ
  have hcl := isClass_of_isChar hχ
  rw [GlobalTheory.T.groupAlgebraTrace_patternIdempotent_exchange g ψ hψ N k s hN χ hcl, GlobalTheory.T.trace_unitriangularColumnVanishingIdempotent_eq_sum_derivatives g ψ hψ N k hk (by omega) χ hcl]
  have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast (Fact.out : g.Prime).one_lt.le
  have hterm : ∀ i a b, (wh ψ (der ψ i χ) * ((g : ℂ) ^ a - (g : ℂ) ^ b)).re =
      (wh ψ (der ψ i χ)).re * ((g : ℝ) ^ a - (g : ℝ) ^ b) := by
    intro i a b
    rw [show ((g : ℂ) ^ a - (g : ℂ) ^ b) = (((g : ℝ) ^ a - (g : ℝ) ^ b : ℝ) : ℂ) by push_cast; ring]
    exact Complex.re_mul_ofReal _ _
  have hnn : ∀ i, i ≤ N → 0 ≤ (wh ψ (der ψ i χ)).re := by
    intro i hi
    obtain ⟨n, hn⟩ := wh_der_nat g ψ N i hi χ hχ
    rw [hn]
    simp
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [Finset.sum_range_succ', Complex.add_re, Complex.add_re, Complex.re_sum, hterm 0, wh_der_zero]
  have hrest : 0 ≤ ∑ i ∈ Finset.range k', (wh ψ (der ψ (i + 1) χ) *
      ((g : ℂ) ^ (k' + 1 - (i + 1)) - (g : ℂ) ^ (k' + 1 - (i + 1) - 1))).re := by
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hterm]
    apply mul_nonneg (hnn _ (by omega))
    rw [sub_nonneg]
    exact pow_le_pow_right₀ hg1 (by omega)
  have hlast := hnn (k' + 1) (by omega)
  have h0 : (wh ψ χ).re * ((g : ℝ) ^ (k' + 1 - 0) - (g : ℝ) ^ (k' + 1 - 0 - 1)) =
      ((g : ℝ) ^ (k' + 1) - (g : ℝ) ^ (k' + 1 - 1)) * (wh ψ χ).re := by
    simp only [Nat.sub_zero]
    ring
  linarith

end GlobalTheory.GLq.MirabolicComparison
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicTraceGeWhittakerDimensionGLnStatement

section

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.mirabolic_trace_ge_whittakerDimension_GLn : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ χ : Gn g N → ℂ, IsChar χ → ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤ (tr (eJ g N k s ψ) χ).re := by
  first | exact @GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison | exact GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison | (intros; apply GlobalTheory.GLq.MirabolicComparison.mirabolic_comparison <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLowerComparison

section

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

namespace GlobalTheory.GLq.LowerWt

theorem coeff_mul_eSerC {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (a : MonoidAlgebra ℂ (Gn g N))
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) :
    (a * eSerC L N f).coeff 1 = ∑ χ ∈ hfin.toFinset, χ 1 / (Fintype.card (Gn g N) : ℂ) * tr a χ := by
  unfold eSerC
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  simp only [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun χ _ => ?_
  exact ((GlobalTheory.GLq.trIdem (Gn g N) a χ).2.2)

theorem re_coeff_mul_eSerC {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (a : MonoidAlgebra ℂ (Gn g N))
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) :
    ((a * eSerC L N f).coeff 1).re =
      ∑ χ ∈ hfin.toFinset, (χ 1).re / (Fintype.card (Gn g N) : ℝ) * (tr a χ).re := by
  rw [coeff_mul_eSerC L f a hfin, Complex.re_sum]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
  obtain ⟨d, -, hd⟩ := (GlobalTheory.GLq.trIdem (Gn g N) a χ).2.1 hI
  rw [hd]
  have : (d : ℂ) / (Fintype.card (Gn g N) : ℂ) = (((d : ℝ) / (Fintype.card (Gn g N) : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [this, Complex.re_ofReal_mul]
  simp

theorem weight_nonneg {g : ℕ} [Fact g.Prime] (L : LabelDatum g) {N : ℕ} (f : (ZMod g)[X])
    (hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite) (χ : Gn g N → ℂ) (hχ : χ ∈ hfin.toFinset) :
    0 ≤ (χ 1).re / (Fintype.card (Gn g N) : ℝ) := by
  have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
  obtain ⟨d, -, hd⟩ := (GlobalTheory.GLq.trIdem (Gn g N) (1 : MonoidAlgebra ℂ (Gn g N)) χ).2.1 hI
  rw [hd]
  simp only [Complex.natCast_re]
  positivity

end GlobalTheory.GLq.LowerWt

theorem GlobalTheory.GLq.lowerWtComparison : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 →
    ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k →
      ∀ f, (1 - 1 / (g : ℝ)) * wtC L (eU g N ψ) f ≤ wtC L (eJ g N k s ψ) f := by
  intro g _ L ψ hψ N k s hN hk f
  have hL8 := GlobalTheory.T.mirabolic_trace_ge_whittakerDimension_GLn g ψ hψ N k s hN hk
  obtain ⟨-, hU1, hJ, -⟩ := GlobalTheory.T.whittakerJacquetIdempotents_properties_primeField g N k s ψ
  obtain ⟨-, hJ1⟩ := hJ hN
  have hfin : {χ : Gn g N → ℂ | IsIrr χ ∧ HasLabel L χ f}.Finite :=
    (irr_finite_and_finsum_zOf_eq_one (Gn g N)).1.subset fun χ h => h.1
  set T := hfin.toFinset
  set c : (Gn g N → ℂ) → ℝ := fun χ => (χ 1).re / (Fintype.card (Gn g N) : ℝ) with hc
  set A := ∑ χ ∈ T, c χ * (tr (eU g N ψ) χ).re with hA
  set B := ∑ χ ∈ T, c χ * (tr (eJ g N k s ψ) χ).re with hB
  have hAeq : ((eU g N ψ * eSerC L N f).coeff 1).re = A := LowerWt.re_coeff_mul_eSerC L f _ hfin
  have hBeq : ((eJ g N k s ψ * eSerC L N f).coeff 1).re = B := LowerWt.re_coeff_mul_eSerC L f _ hfin
  have hG : (0 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).pos
  set M := N * (N - 1) / 2
  have hU1r : ((eU g N ψ).coeff 1).re = ((g : ℝ) ^ M)⁻¹ := by
    rw [hU1]
    have : ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ M)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hJ1r : ((eJ g N k s ψ).coeff 1).re = (g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹ := by
    rw [hJ1]
    have : (g : ℂ) ^ k * ((g : ℂ) ^ M)⁻¹ = ((((g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹) : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.ofReal_re]
  have hBA : ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * A ≤ B := by
    rw [hA, hB, Finset.mul_sum]
    refine Finset.sum_le_sum fun χ hχ => ?_
    have h0 : 0 ≤ c χ := LowerWt.weight_nonneg L f hfin χ hχ
    have hI : IsIrr χ := ((Set.Finite.mem_toFinset hfin).1 hχ).1
    have hC : IsChar χ := by obtain ⟨V, -, hV⟩ := hI; exact ⟨V, hV⟩
    have h8 := hL8 χ hC
    unfold wh at h8
    calc ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (c χ * (tr (eU g N ψ) χ).re)
        = c χ * (((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (tr (eU g N ψ) χ).re) := by ring
      _ ≤ c χ * (tr (eJ g N k s ψ) χ).re := mul_le_mul_of_nonneg_left h8 h0
  have hpow : (g : ℝ) ^ k - (g : ℝ) ^ (k - 1) = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ]
    field_simp
  unfold wtC
  rw [hAeq, hBeq, hU1r, hJ1r]
  have hgk : (0 : ℝ) < (g : ℝ) ^ k := pow_pos hG k
  have hgM : (0 : ℝ) < (g : ℝ) ^ M := pow_pos hG M
  rw [hpow] at hBA
  rw [div_inv_eq_mul, le_div_iff₀ (mul_pos hgk (inv_pos.2 hgM))]
  calc (1 - 1 / (g : ℝ)) * (A * (g : ℝ) ^ M) * ((g : ℝ) ^ k * ((g : ℝ) ^ M)⁻¹)
      = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) * A * ((g : ℝ) ^ M * ((g : ℝ) ^ M)⁻¹) := by ring
    _ = (g : ℝ) ^ k * (1 - 1 / (g : ℝ)) * A := by rw [mul_inv_cancel₀ hgM.ne', mul_one]
    _ ≤ B := hBA
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesWeightLowerComparisonStatement

section

@[expose] public section

open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

theorem _root_.GlobalTheory.T.harishChandraSeriesWeight_lower_comparison : ∀ (g : ℕ) [Fact g.Prime] (L : LabelDatum g) (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (N k s : ℕ), N = k + 2 * s + 1 → 1 ≤ k → ∀ f, (1 - 1 / (g : ℝ)) * wtC L (eU g N ψ) f ≤ wtC L (eJ g N k s ψ) f := by
  first | exact @GlobalTheory.GLq.lowerWtComparison | exact GlobalTheory.GLq.lowerWtComparison | (intros; apply GlobalTheory.GLq.lowerWtComparison <;> assumption)
end
end
