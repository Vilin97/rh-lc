module

public import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralCoeffInterpolationBivariateSeriesStatement
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Normed.Group.Ultra
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupNatMulSeriesEvalOpenDiscPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FormalGroupTorsionTowerExactOrderStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesEvalTsumOpenPolydiscPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolyOfCharacter

section

@[expose] public section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem exists_integral_poly_of_character (K : Type) [NormedField K] [IsUltrametricDist K]
    (G : Type) [AddCommGroup G] [Fintype G] (x χ : G → K) (hx : Function.Injective x)
    (hχ : ∀ i j, χ (i + j) = χ i * χ j)
    (hc : ∀ k : Fin (Fintype.card G), ∃ c : Fin (Fintype.card G) → Fin (Fintype.card G) → K,
      (∀ a b, ‖c a b‖ ≤ 1) ∧
        ∀ i j, x (i + j) ^ (k : ℕ) = ∑ a, ∑ b, c a b * x i ^ (a : ℕ) * x j ^ (b : ℕ)) :
    ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ i, g.eval (x i) = χ i := by
  classical
  choose c hc1 hc2 using hc
  have van : ∀ v : Fin (Fintype.card G) → K, (∀ i, ∑ a, v a * x i ^ (a : ℕ) = 0) → v = 0 := by
    intro v hv
    exact Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (f := fun j => x ((Fintype.equivFin G).symm j))
      (hx.comp (Fintype.equivFin G).symm.injective) (fun j => hv _)
  set g : Polynomial K := Lagrange.interpolate Finset.univ x χ with hg
  have hinj : Set.InjOn x (Finset.univ : Finset G) := hx.injOn
  have hdeg : g.degree < (Fintype.card G : ℕ) := by
    exact Lagrange.degree_interpolate_lt (r := χ) hinj
  have hev : ∀ i, g.eval (x i) = χ i := fun i =>
    Lagrange.eval_interpolate_at_node χ hinj (Finset.mem_univ i)
  have hpos : 0 < Fintype.card G := Fintype.card_pos
  have hnat : g.natDegree < Fintype.card G := by
    by_cases h0 : g = 0
    · simpa [h0] using hpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 hdeg
  have hsum : ∀ i, χ i = ∑ a : Fin (Fintype.card G), g.coeff a * x i ^ (a : ℕ) := by
    intro i
    rw [← hev i, Polynomial.eval_eq_sum_range' hnat,
      Fin.sum_univ_eq_sum_range (fun a => g.coeff a * x i ^ a)]
  have key : ∀ a b : Fin (Fintype.card G),
      g.coeff a * g.coeff b = ∑ k : Fin (Fintype.card G), g.coeff k * c k a b := by
    have h1 : ∀ j, (fun a : Fin (Fintype.card G) => ∑ b : Fin (Fintype.card G),
        (g.coeff a * g.coeff b - ∑ k : Fin (Fintype.card G), g.coeff k * c k a b)
          * x j ^ (b : ℕ)) = 0 := by
      intro j
      apply van
      intro i
      have e1 : χ i * χ j = ∑ a : Fin (Fintype.card G), ∑ b : Fin (Fintype.card G),
          g.coeff a * g.coeff b * x j ^ (b : ℕ) * x i ^ (a : ℕ) := by
        rw [hsum i, hsum j, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
      have e2 : χ (i + j) = ∑ a : Fin (Fintype.card G), ∑ b : Fin (Fintype.card G),
          (∑ k : Fin (Fintype.card G), g.coeff k * c k a b) * x j ^ (b : ℕ) * x i ^ (a : ℕ) := by
        rw [hsum (i + j)]
        simp_rw [hc2, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
      have e3 := hχ i j
      rw [e1, e2] at e3
      simp_rw [Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      exact e3.symm
    intro a b
    have h2 := van _ (fun j => congrFun (h1 j) a)
    exact sub_eq_zero.1 (congrFun h2 b)
  haveI : Nonempty (Fin (Fintype.card G)) := ⟨⟨0, hpos⟩⟩
  obtain ⟨m, -, hm⟩ := Finset.exists_max_image Finset.univ
    (fun a : Fin (Fintype.card G) => ‖g.coeff a‖) Finset.univ_nonempty
  have hM : ‖g.coeff m‖ * ‖g.coeff m‖ ≤ ‖g.coeff m‖ := by
    rw [← norm_mul, key]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    intro k _
    rw [norm_mul]
    calc ‖g.coeff k‖ * ‖c k m m‖ ≤ ‖g.coeff k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hc1 k m m) (norm_nonneg _)
      _ ≤ ‖g.coeff m‖ := by simpa using hm k (Finset.mem_univ k)
  have hM1 : ‖g.coeff m‖ ≤ 1 := by nlinarith [norm_nonneg (g.coeff m)]
  refine ⟨g, fun k => ?_, hev⟩
  by_cases hk : k < Fintype.card G
  · exact (hm ⟨k, hk⟩ (Finset.mem_univ _)).trans hM1
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

end GlobalTheory.ConvSer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolyOfCharacterStatement

section

@[expose] public section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.exists_integral_poly_of_character' : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (G : Type) [AddCommGroup G] [Fintype G] (x χ : G → K), Function.Injective x → (∀ i j, χ (i + j) = χ i * χ j) → (∀ k : Fin (Fintype.card G), ∃ c : Fin (Fintype.card G) → Fin (Fintype.card G) → K, (∀ a b, ‖c a b‖ ≤ 1) ∧ ∀ i j, x (i + j) ^ (k : ℕ) = ∑ a, ∑ b, c a b * x i ^ (a : ℕ) * x j ^ (b : ℕ)) → ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ i, g.eval (x i) = χ i := by
  first | exact @GlobalTheory.ConvSer.exists_integral_poly_of_character | exact GlobalTheory.ConvSer.exists_integral_poly_of_character | (intros; apply GlobalTheory.ConvSer.exists_integral_poly_of_character <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolynomialTorsionCharacterLevel

section

@[expose] public section

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem ev_pow_of_intg (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (σ : Type) [Fintype σ] (x : σ → K) (hx : ∀ i, ‖x i‖ < 1) (S : MvPowerSeries σ K)
    (hS : Intg S) (k : ℕ) : ev (S ^ k) x = ev S x ^ k := by
  obtain ⟨-, halg, hC, -⟩ := GlobalTheory.T.mvPowerSeriesEvalTsum_openPolydisc_properties K σ x hx
  obtain ⟨-, -, hpow, -⟩ := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ
  have hB : Bdd S := (hpow S 0).2.2 hS
  induction k with
  | zero => simpa using hC 1
  | succ k ih => rw [pow_succ, (halg _ _ ((hpow S k).2.1 hB) hB).2.2, ih, pow_succ]

theorem exists_intg_polynomial_level (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K) (hF : Intg F.toPowerSeries)
    (t : ℕ → K) (ht : ∀ n, ‖t n‖ < 1) (h0 : t 0 = 0) (h1 : t 1 ≠ 0)
    (hp : ∀ n, ev1 (nMul F p) (t (n + 1)) = t n) (n : ℕ) (ζ : K) (hζ : ζ ^ (p ^ n) = 1) :
    ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧
      ∀ j : ℕ, g.eval (ev1 (nMul F j) (t n)) = ζ ^ j := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hord := (GlobalTheory.T.formalGroup_torsionTower_exact_order K p F hF t ht h0 h1 hp).2.2 n
  obtain ⟨-, -, hnorm, hadd, -⟩ := (GlobalTheory.T.formalGroupNatMulSeries_eval_openDisc_properties K F hF).2 (t n) (ht n)
  set x : ZMod (p ^ n) → K := fun i => ev1 (nMul F i.val) (t n) with hx
  have hxlt : ∀ i, ‖x i‖ < 1 := fun i => (hnorm i.val).1.trans_lt (ht n)
  have hinj : Function.Injective x := by
    intro i j hij
    have := (hord _ _).1 hij
    have h2 := (ZMod.natCast_eq_natCast_iff _ _ _).2 this
    simpa using h2
  have hxadd : ∀ i j, x (i + j) = ev F.toPowerSeries ![x i, x j] := by
    intro i j
    simp only [hx]
    rw [hadd, hord, ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hχ : ∀ i j : ZMod (p ^ n), ζ ^ (i + j).val = ζ ^ i.val * ζ ^ j.val := by
    intro i j
    rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hζ]
  have hcard : (Finset.univ.image x).card = Fintype.card (ZMod (p ^ n)) := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]
  obtain ⟨g, hg, hgx⟩ := GlobalTheory.T.exists_integral_poly_of_character' K (ZMod (p ^ n)) x (fun i => ζ ^ i.val) hinj hχ (by
    intro k
    have hc := GlobalTheory.T.exists_integral_coeff_interpolation_bivariate_series K (Finset.univ.image x) (F.toPowerSeries ^ (k : ℕ))
      (by
        intro y hy
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hy
        exact hxlt i)
      (((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K (Fin 2)).2.2.1 _ _).1 hF)
    rw [hcard] at hc
    obtain ⟨c, hc1, hc2⟩ := hc
    refine ⟨c, hc1, fun i j => ?_⟩
    rw [← hc2 _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)) _
      (Finset.mem_image_of_mem _ (Finset.mem_univ j)), hxadd,
      ev_pow_of_intg K (Fin 2) _ _ _ hF]
    intro l
    fin_cases l
    · exact hxlt i
    · exact hxlt j)
  refine ⟨g, hg, fun j => ?_⟩
  have := hgx (j : ZMod (p ^ n))
  simp only [hx, ZMod.val_natCast] at this
  rw [← pow_eq_pow_mod _ hζ] at this
  rw [← this, (hord j (j % p ^ n)).2 (Nat.mod_modEq _ _).symm]

end GlobalTheory.ConvSer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralPolynomialTorsionCharacterLevelStatement

section

@[expose] public section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.exists_integral_polynomial_torsion_character_level : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → ∀ (n : ℕ) (ζ : K), ζ ^ (p ^ n) = 1 → ∃ g : Polynomial K, (∀ k, ‖g.coeff k‖ ≤ 1) ∧ ∀ j : ℕ, g.eval (ev1 (nMul F j) (t n)) = ζ ^ j := by
  first | exact @GlobalTheory.ConvSer.exists_intg_polynomial_level | exact GlobalTheory.ConvSer.exists_intg_polynomial_level | (intros; apply GlobalTheory.ConvSer.exists_intg_polynomial_level <;> assumption)
end
end
