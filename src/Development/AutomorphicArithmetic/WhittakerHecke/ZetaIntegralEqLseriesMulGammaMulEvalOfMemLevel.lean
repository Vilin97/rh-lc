module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.WhittakerHecke.ExistsFactorizationOfIdeleCongruenceDivisorLevel
public import Development.AutomorphicArithmetic.WhittakerHecke.ExistsIdeleCorrectingLowerRightEntry
public import Development.AutomorphicArithmetic.WhittakerHecke.HasSumCoprimeIntegralEqIdeleIntegral
public import Mathlib.Analysis.PSeriesComplex
public import Development.AutomorphicArithmetic.WhittakerHecke.IdeleCongruenceArchIdeleMulFiniteNatIdele
public import Development.AutomorphicArithmetic.WhittakerHecke.IntegralEvenPowerGaussianMulAbsRpow
import Development.AutomorphicArithmetic.WhittakerHecke.RatIdeleAbsRealIdeleNatIdeleUnitIdeles
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.BottomRowCongruenceIffIdeleCongruence

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.bottomRow_congruence_iff_idele_congruence :
    ∀ N : ℕ, 0 < N → ∀ k ∈ KK ℚ, k ∈ SS N → ∀ ζ : (A ℚ)ˣ, ζ ∈ UU → (∀ v : H.P ℚ, (Bad N v → Dv N v ((ζ : A ℚ) * k 1 1 - 1)) ∧ (¬ Bad N v → H.cp v (ζ : A ℚ) = 1)) → ∀ y : (A ℚ)ˣ, (∀ v, Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 0) ∧ Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 1 - 1)) ↔ ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) := by
  intro N hN k hk hS ζ hζ hz y
  have hi : ∀ v i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun v i j => hk.2 v i j
  have hN1 : ∀ v : H.P ℚ, Valued.v (N : H.Kv v) ≤ 1 := fun v =>
    show (N : H.Kv v) ∈ v.adicCompletionIntegers ℚ from natCast_mem _ N
  have hv : ∀ v : H.P ℚ, (Bad N v → Valued.v (N : H.Kv v) < 1) ∧ (¬ Bad N v → Valued.v (N : H.Kv v) = 1) := fun v => by
    have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v (N : 𝓞 ℚ)
    rw [HeightOneSpectrum.valuation_of_algebraMap] at h1
    have h2 : Valued.v (N : H.Kv v) = v.intValuation (N : 𝓞 ℚ) := by simpa using h1
    rw [h2]
    exact ⟨fun h => (v.intValuation_lt_one_iff_mem _).2 h, fun h => HeightOneSpectrum.intValuation_eq_one_iff.2 h⟩
  have key : ∀ v : H.P ℚ, (Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 0) ∧ Dv N v ((y : A ℚ) * (ζ : A ℚ) * k 1 1 - 1)) ↔
      ((Bad N v → Dv N v ((y : A ℚ) - 1)) ∧ Valued.v (H.cp v (y : A ℚ)) ≤ 1) := fun v => by
    have hd : H.cp v (k 0 0) * H.cp v (k 1 1) - H.cp v (k 0 1) * H.cp v (k 1 0) = 1 := by
      have := congrArg (H.cp v) ((Matrix.det_fin_two k.1).symm.trans k.2)
      simpa using this
    have hs := hS v
    have hz' := hz v
    have hu := hζ.2 v
    have i00 := hi v 0 0
    have i01 := hi v 0 1
    have i10 := hi v 1 0
    have i11 := hi v 1 1
    simp only [Dv, map_mul, map_sub, map_one] at hs hz' ⊢
    generalize H.cp v (k 0 0) = a at *
    generalize H.cp v (k 0 1) = b at *
    generalize H.cp v (k 1 0) = c at *
    generalize H.cp v (k 1 1) = d at *
    generalize H.cp v (y : A ℚ) = x at *
    generalize H.cp v (ζ : A ℚ) = z at *
    by_cases hb : Bad N v
    · have h1 := hz'.1 hb
      have hlt := (hv v).1 hb
      have h2 : Valued.v (z * d) = 1 := by
        have := Valuation.map_one_add_of_lt Valued.v (h1.trans_lt hlt)
        rwa [add_sub_cancel] at this
      constructor
      · rintro ⟨-, h3⟩
        have h4 : Valued.v x ≤ 1 := by
          have := Valuation.map_one_add_of_lt Valued.v (h3.trans_lt hlt)
          rw [add_sub_cancel, mul_assoc, map_mul, h2, mul_one] at this
          exact this.le
        refine ⟨fun _ => ?_, h4⟩
        rw [show x - 1 = (x * z * d - 1) - x * (z * d - 1) by ring]
        exact Valuation.map_sub_le _ h3 (by rw [map_mul]; exact (mul_le_mul' h4 h1).trans_eq (one_mul _))
      · rintro ⟨h3, h4⟩
        refine ⟨by rw [hu, mul_one]; exact (mul_le_mul' h4 hs).trans_eq (one_mul _), ?_⟩
        rw [show x * z * d - 1 = (x - 1) * (z * d) + (z * d - 1) by ring]
        exact Valuation.map_add_le _ (by rw [map_mul, h2, mul_one]; exact h3 hb) h1
    · obtain rfl := hz'.2 hb
      rw [(hv v).2 hb]
      simp only [map_one, mul_one]
      constructor
      · rintro ⟨h3, h4⟩
        refine ⟨fun h => absurd h hb, ?_⟩
        rw [show x = a * ((x * d - 1) + 1) - b * (x * c) by linear_combination (-x) * hd]
        refine Valuation.map_sub_le _ ?_ ?_
        · rw [map_mul]
          exact mul_le_one' i00 (Valuation.map_add_le _ h4 (map_one _).le)
        · rw [map_mul, map_mul]
          exact mul_le_one' i01 h3
      · rintro ⟨-, h4⟩
        exact ⟨mul_le_one' h4 i10, Valuation.map_sub_le _ (by rw [map_mul]; exact mul_le_one' h4 i11) (map_one _).le⟩
  simp only [key, forall_and]
end
end

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.ExistsArchIdeleNatIdeleCongruenceUnitFactorizati

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_archIdele_natIdele_congruenceUnit_factorization :
    ∀ N : ℕ, 0 < N → ∀ y : (A ℚ)ˣ, ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) → ∃ (n : ℕ) (r : ℝ) (τ : (A ℚ)ˣ), 0 < n ∧ n.Coprime N ∧ r ≠ 0 ∧ τ ∈ TT N ∧ y = iy r * pin n * τ := by
  intro N hN y h
  exact UpperTheory.exists_factorization_of_ideleCongruence_divisor_level N N hN dvd_rfl (fun _ h => h) y h.1 fun v _ => h.2 v
end
end

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.HasSumCoprimeInvPowTwoMulEqLSeries

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.hasSum_coprime_inv_pow_two_mul_eq_LSeries :
    ∀ (N : ℕ) (s : ℂ), 0 < N → 1 < s.re → HasSum (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ((n : ℕ) : ℂ) ^ (-(2 * s))) (LSeries (sqN N) s) := by
  intro N s _ hs
  have hsum : Summable fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ((n : ℕ) : ℂ) ^ (-(2 * s)) := by
    have h : Summable fun n : ℕ => 1 / (n : ℂ) ^ (2 * s) :=
      Complex.summable_one_div_nat_cpow.2 (by simp; linarith)
    refine (h.subtype _).congr fun n => ?_
    simp [Complex.cpow_neg]
  have hinj : Function.Injective fun m : {n : ℕ // 0 < n ∧ n.Coprime N} => (m : ℕ) * m := fun a b e =>
    Subtype.ext (Nat.mul_self_inj.1 e)
  have h2 : HasSum (LSeries.term (sqN N) s) (∑' n : {n : ℕ // 0 < n ∧ n.Coprime N}, ((n : ℕ) : ℂ) ^ (-(2 * s))) := by
    refine (hinj.hasSum_iff fun x hx => ?_).1 ?_
    · rcases eq_or_ne x 0 with rfl | h0
      · simp
      · rw [LSeries.term_of_ne_zero h0, sqN, if_neg, zero_div]
        rintro ⟨m, rfl, hm⟩
        exact hx ⟨⟨m, Nat.pos_of_ne_zero fun e => h0 (by simp [e]), hm⟩, rfl⟩
    · convert hsum.hasSum using 1
      funext m
      have h0 : (m : ℕ) * m ≠ 0 := mul_ne_zero m.2.1.ne' m.2.1.ne'
      rw [Function.comp_apply, LSeries.term_of_ne_zero h0, sqN, if_pos ⟨m, rfl, m.2.2⟩, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, Complex.cpow_neg, two_mul,
        Complex.cpow_add _ _ (Nat.cast_ne_zero.2 m.2.1.ne'), one_div]
  rw [LSeries, h2.tsum_eq]
  exact hsum.hasSum
end
end

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.IdeleCongruenceConditionMulCongruenceUnitIff

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.ideleCongruenceCondition_mul_congruenceUnit_iff :
    ∀ N : ℕ, 0 < N → ∀ τ ∈ TT N, ∀ y : (A ℚ)ˣ, ((∀ v, Bad N v → Dv N v (((y * τ : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y * τ : (A ℚ)ˣ) : A ℚ)) ≤ 1) ↔ ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) := by
  intro N _ τ hτ y
  obtain ⟨⟨_, hu⟩, hd⟩ := hτ
  have h1 : ∀ v : H.P ℚ, Valued.v (H.cp v ((y * τ : (A ℚ)ˣ) : A ℚ)) = Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) := by
    intro v
    rw [Units.val_mul, map_mul, map_mul, hu v, mul_one]
  have h2 : ∀ v : H.P ℚ, Dv N v (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) ↔ Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1) := by
    intro v
    have hv := hd v
    have he : Valued.v (H.cp v (((y : A ℚ) - 1) * (τ : A ℚ))) = Valued.v (H.cp v ((y : A ℚ) - 1)) := by
      rw [map_mul, map_mul, hu v, mul_one]
    unfold Dv at hv ⊢
    constructor
    · intro h
      have e : ((y : A ℚ) - 1) * (τ : A ℚ) = (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) - ((τ : A ℚ) - 1) := by
        rw [Units.val_mul]; ring
      rw [← he, e, map_sub]
      exact Valuation.map_sub_le _ h hv
    · intro h
      have e : (((y * τ : (A ℚ)ˣ) : A ℚ) - 1) = ((y : A ℚ) - 1) * (τ : A ℚ) + ((τ : A ℚ) - 1) := by
        rw [Units.val_mul]; ring
      rw [e, map_add (f := _)]
      exact Valuation.map_add_le _ (he ▸ h) hv
  simp only [h1, h2]
end
end

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.ZetaIntegralEqLseriesMulGammaMulEvalOfMemLevel

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem re_mul' (a b : A ℚ) : re (a * b) = re a * re b := by simp [re, map_mul]

private theorem re_UU {t : (A ℚ)ˣ} (ht : t ∈ UU) : re (t : A ℚ) = 1 := by
  have h : TR.pInf ℚ (t : A ℚ) = 1 := by
    show (TR.infEq ℚ).symm (t : A ℚ).1 = 1
    rw [ht.1, map_one]
  simp [re, h]

private theorem ab_mul' (a b : (A ℚ)ˣ) : ab (a * b) = ab a * ab b := by simp [ab, map_mul]

private theorem homog {p : MvPolynomial (Fin 2) ℂ} {d : ℕ} (hp : p.IsHomogeneous d) (c a b : ℂ) :
    MvPolynomial.eval ![c * a, c * b] p = c ^ d * MvPolynomial.eval ![a, b] p := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : m 0 + m 1 = d := by
    have := hp (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype, Fin.sum_univ_two] using this
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_pow, ← hdeg, pow_add]
  ring

private theorem cpow_split (r : ℝ) (hr : r ≠ 0) (n : ℕ) (hn : 0 < n) (s : ℂ) :
    (((|r| * (n : ℝ)⁻¹ : ℝ)) : ℂ) ^ (2 * s) / ((|r| : ℝ) : ℂ) =
      ((n : ℂ) ^ (-(2 * s))) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1) := by
  have hr' : (((|r| : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hr
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (abs_nonneg r) (by positivity) (2 * s),
    Complex.cpow_sub _ _ hr', Complex.cpow_one, Complex.cpow_neg, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.inv_cpow _ _ (by rw [Complex.natCast_arg]; exact Real.pi_pos.ne)]
  ring

theorem UpperTheory.zeta_integral_eq_lseries_mul_gamma_mul_eval_of_mem_level :
    ∀ (N : ℕ), 0 < N → ∀ (e : ℕ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous (2 * e) → ∀ s : ℂ, 4 < s.re → ∀ k ∈ KK ℚ, k ∈ SS N →
        ∀ t : ℝ, re (k 1 0) = Real.sin t → re (k 1 1) = Real.cos t →
        Zr N p s k = (cT N : ℂ) * LSeries (sqN N) s * ((Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e)) *
          MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p := by
  intro N hN e p hp s hs k hK hS t hsin hcos
  obtain ⟨ζ, hζU, hζ⟩ := UpperTheory.exists_idele_correcting_lowerRight_entry N hN k hK hS
  have hs0 : 0 < s.re := by linarith
  have hs1 : 1 < s.re := by linarith
  set ρ : ℂ := MvPolynomial.eval ![(Real.sin t : ℂ), (Real.cos t : ℂ)] p with hρ
  let f0 : IdeleGroup ℚ → ℂ := fun z => (PhiN N p fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab z : ℝ) : ℂ) ^ (2 * s)
  let f : IdeleGroup ℚ → ℂ := fun y => f0 (y * ζ)
  have hshift : Zr N p s k = ∫ y, f y ∂(ideleMeasure ℚ) := (integral_mul_right_eq_self f0 ζ).symm
  have habU : ∀ τ ∈ UU, ∀ y : (A ℚ)ˣ, ab (y * τ) = ab y := fun τ hτ y => by
    rw [ab_mul', (UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles).2.2.1 τ hτ, mul_one]
  have hreU : ∀ τ : (A ℚ)ˣ, τ ∈ UU → ∀ y : (A ℚ)ˣ, re ((y * τ : (A ℚ)ˣ) : A ℚ) = re (y : A ℚ) := fun τ hτ y => by
    rw [Units.val_mul, re_mul', re_UU hτ, mul_one]
  have hf : ∀ y : (A ℚ)ˣ, f y = if ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1) then
      ((re (y : A ℚ) : ℝ) : ℂ) ^ (2 * e) * ρ * Complex.exp (-(Real.pi : ℂ) * ((re (y : A ℚ) ^ 2 : ℝ) : ℂ)) * ((ab y : ℝ) : ℂ) ^ (2 * s) else 0 := by
    intro y
    have hre : ∀ j, re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k j) = re (y : A ℚ) * re (k 1 j) := fun j => by
      rw [re_mul', hreU ζ hζU y]; rfl
    have hc := UpperTheory.bottomRow_congruence_iff_idele_congruence N hN k hK hS ζ hζU hζ y
    have hfun : (fun i => ((re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k i) : ℝ) : ℂ)) =
        ![((re (y : A ℚ) : ℝ) : ℂ) * (Real.sin t : ℂ), ((re (y : A ℚ) : ℝ) : ℂ) * (Real.cos t : ℂ)] := by
      funext i
      fin_cases i
      · show ((re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 0) : ℝ) : ℂ) = ((re (y : A ℚ) : ℝ) : ℂ) * (Real.sin t : ℂ)
        rw [hre, hsin, Complex.ofReal_mul]
      · show ((re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 1) : ℝ) : ℂ) = ((re (y : A ℚ) : ℝ) : ℂ) * (Real.cos t : ℂ)
        rw [hre, hcos, Complex.ofReal_mul]
    have hsq : re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 0) ^ 2 + re (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 1) ^ 2 = re (y : A ℚ) ^ 2 := by
      rw [hre, hre, hsin, hcos]
      have := Real.sin_sq_add_cos_sq t
      calc _ = re (y : A ℚ) ^ 2 * (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
        _ = _ := by rw [this, mul_one]
    show (PhiN N p fun j => ((y * ζ : (A ℚ)ˣ) : A ℚ) * row k j) * ((ab (y * ζ) : ℝ) : ℂ) ^ (2 * s) = _
    rw [habU ζ hζU y]
    by_cases hq : ((∀ v, Bad N v → Dv N v (((y : (A ℚ)ˣ) : A ℚ) - 1)) ∧ ∀ v : H.P ℚ, Valued.v (H.cp v ((y : (A ℚ)ˣ) : A ℚ)) ≤ 1)
    · have hq' : ∀ v, Dv N v (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 0) ∧ Dv N v (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 1 - 1) := by
        exact hc.mpr hq
      rw [if_pos hq, PhiN, if_pos hq', hfun, homog hp, hsq]
    · have hq' : ¬ ∀ v, Dv N v (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 0) ∧ Dv N v (((y * ζ : (A ℚ)ˣ) : A ℚ) * row k 1 - 1) := by
        intro h
        exact hq (hc.mp h)
      rw [if_neg hq, PhiN, if_neg hq', zero_mul]
  have hinv : ∀ τ ∈ TT N, ∀ y : IdeleGroup ℚ, f (y * τ) = f y := by
    intro τ hτ y
    rw [hf, hf, hreU τ hτ.1 y, habU τ hτ.1 y]
    simp only [UpperTheory.ideleCongruenceCondition_mul_congruenceUnit_iff N hN τ hτ y]
  have hsupp : ∀ y : IdeleGroup ℚ, f y ≠ 0 → ∃ (n : ℕ) (r : ℝ) (τ : (A ℚ)ˣ), 0 < n ∧ n.Coprime N ∧ r ≠ 0 ∧ τ ∈ TT N ∧ y = iy r * pin n * τ := by
    intro y hy
    refine UpperTheory.exists_archIdele_natIdele_congruenceUnit_factorization N hN y ?_
    by_contra h
    exact hy (by rw [hf, if_neg h])
  let J : ℝ → ℂ := fun r => (r : ℂ) ^ (2 * e) * Complex.exp (-(Real.pi : ℂ) * ((r ^ 2 : ℝ) : ℂ)) * ((|r| : ℝ) : ℂ) ^ (2 * s - 1)
  have hJ := UpperTheory.integral_even_power_gaussian_mul_abs_rpow e s hs0
  have hval : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, ∀ r : ℝ, r ≠ 0 →
      f (iy r * pin n) / ((|r| : ℝ) : ℂ) = (ρ * ((n : ℕ) : ℂ) ^ (-(2 * s))) * J r := by
    intro n r hr
    have hab : ab (iy r * pin n) = |r| * ((n : ℕ) : ℝ)⁻¹ := by
      rw [ab_mul', (UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles).1 r hr, (UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles).2.1 n n.2.1]
    rw [hf, if_pos (UpperTheory.ideleCongruence_archIdele_mul_finiteNatIdele N hN n r n.2.1 n.2.2 hr), (UpperTheory.ratIdeleAbs_realIdele_natIdele_unitIdeles).2.2.2 r n hr n.2.1, hab, mul_div_assoc,
      cpow_split r hr n n.2.1 s]
    simp only [J]
    ring
  have hae : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, (fun r : ℝ => f (iy r * pin n) / ((|r| : ℝ) : ℂ)) =ᵐ[volume]
      fun r => (ρ * ((n : ℕ) : ℂ) ^ (-(2 * s))) * J r := by
    intro n
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with r hr
    exact hval n r hr
  have hint : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, Integrable (fun r : ℝ => f (iy r * pin n) / ((|r| : ℝ) : ℂ)) :=
    fun n => (hJ.1.const_mul _).congr (hae n).symm
  have hS0 := UpperTheory.hasSum_coprime_inv_pow_two_mul_eq_LSeries N s hN hs1
  have hnorm : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, ∫ r : ℝ, ‖f (iy r * pin n) / ((|r| : ℝ) : ℂ)‖ =
      ‖ρ‖ * ‖((n : ℕ) : ℂ) ^ (-(2 * s))‖ * ∫ r : ℝ, ‖J r‖ := by
    intro n
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae n] with r hr
    rw [hr, norm_mul, norm_mul]
  have hsm : Summable (fun n : {n : ℕ // 0 < n ∧ n.Coprime N} => ∫ r : ℝ, ‖f (iy r * pin n) / ((|r| : ℝ) : ℂ)‖) := by
    simp only [hnorm]
    exact (hS0.summable.norm.mul_left ‖ρ‖).mul_right _
  have hmain := (UpperTheory.hasSum_coprime_integral_eq_idele_integral) N N hN f hinv hsupp hint hsm
  have hterm : ∀ n : {n : ℕ // 0 < n ∧ n.Coprime N}, (cT N : ℂ) * ∫ r : ℝ, f (iy r * pin n) / ((|r| : ℝ) : ℂ) =
      ((cT N : ℂ) * ρ * ((Real.pi : ℂ) ^ (-(s + e)) * Complex.Gamma (s + e))) * ((n : ℕ) : ℂ) ^ (-(2 * s)) := by
    intro n
    rw [integral_congr_ae (hae n), integral_const_mul, hJ.2]
    ring
  simp only [hterm] at hmain
  rw [hshift, hmain.unique (hS0.mul_left _)]
  ring
end
end
