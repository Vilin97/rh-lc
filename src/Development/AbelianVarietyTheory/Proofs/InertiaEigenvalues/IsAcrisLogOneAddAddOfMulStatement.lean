module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisEqZeroOfForallDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalLogDefect
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAcrisLogOneAdd
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Nat.Choose.Sum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddMulDerivativeTrunc
import Mathlib.RingTheory.MvPolynomial.Ideal

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialTruncatedLogAdditivityDefectCoeffDvd

section

@[expose] public section

open GlobalTheory.LogU MvPolynomial Finset

namespace GlobalTheory.LogUIntg

lemma single_add_single_eq_iff {i j i' j' : ℕ} :
    (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j = Finsupp.single 0 i' + Finsupp.single 1 j') ↔
      (i = i' ∧ j = j') := by
  constructor
  · intro h
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma coeff_monomial_two (i j p q : ℕ) (c : ℤ) :
    AddMonoidAlgebra.coeff (monomial (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) c)
        (Finsupp.single 0 i + Finsupp.single 1 j) =
      if p = i ∧ q = j then c else 0 := by
  rw [coeff_monomial]
  simp only [single_add_single_eq_iff]

lemma monomial_two_eq (p q : ℕ) (c : ℤ) :
    monomial (Finsupp.single (0 : Fin 2) p + Finsupp.single 1 q) c = C c * X 0 ^ p * X 1 ^ q := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, C_mul_monomial, monomial_mul]
  simp

lemma factorial_dvd_term (n K s a : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) (hs : s ≤ K) (ha : a ≤ K - s)
    (hn : n ≤ (s + a) + (s + (K - s - a))) :
    n.factorial * ((n - 1) / 2).factorial ∣
      (s + a).factorial * (s + (K - s - a)).factorial *
        (n.factorial / K * (K.choose s * (K - s).choose a)) := by
  have e1 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s a)
  rw [Nat.add_sub_cancel_left] at e1
  have e2 := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right s (K - s - a))
  rw [Nat.add_sub_cancel_left] at e2
  have e3 := Nat.choose_mul_factorial_mul_factorial ha
  have e4 := Nat.choose_mul_factorial_mul_factorial hs
  have e5 : n.factorial / K * K.factorial = n.factorial * (K - 1).factorial := by
    rw [← Nat.mul_factorial_pred (by omega : K ≠ 0), ← mul_assoc,
      Nat.div_mul_cancel (Nat.dvd_factorial (by omega) hKn)]
  rw [← e1, ← e2]
  have key : (s + a).choose s * s.factorial * a.factorial *
      ((s + (K - s - a)).choose s * s.factorial * (K - s - a).factorial) *
        (n.factorial / K * (K.choose s * (K - s).choose a)) =
      n.factorial * ((K - 1).factorial * ((s + a).choose s * (s + (K - s - a)).choose s * s.factorial)) := by
    calc _ = (s + a).choose s * (s + (K - s - a)).choose s * s.factorial *
          ((K.choose s * s.factorial * ((K - s).choose a * a.factorial * (K - s - a).factorial)) *
            (n.factorial / K)) := by ring
      _ = (s + a).choose s * (s + (K - s - a)).choose s * s.factorial *
          (n.factorial / K * K.factorial) := by rw [e3, e4]; ring
      _ = _ := by rw [e5]; ring
  rw [key]
  exact mul_dvd_mul (dvd_refl _)
    (dvd_mul_of_dvd_left (Nat.factorial_dvd_factorial (by omega)) _)

def Good (n : ℕ) (f : MvPolynomial (Fin 2) ℤ) : Prop :=
  ∀ i j : ℕ, n ≤ i + j → ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) ∣
    ((i.factorial * j.factorial : ℕ) : ℤ) * AddMonoidAlgebra.coeff f (Finsupp.single 0 i + Finsupp.single 1 j)

lemma good_sub {n : ℕ} {f g : MvPolynomial (Fin 2) ℤ} (hf : Good n f) (hg : Good n g) :
    Good n (f - g) := by
  intro i j h
  rw [MvPolynomial.coeff_sub, mul_sub]
  exact dvd_sub (hf i j h) (hg i j h)

lemma good_sum {n : ℕ} {ι : Type} (t : Finset ι) (f : ι → MvPolynomial (Fin 2) ℤ)
    (hf : ∀ x ∈ t, Good n (f x)) : Good n (∑ x ∈ t, f x) := by
  intro i j h
  rw [coeff_sum, Finset.mul_sum]
  exact Finset.dvd_sum fun x hx => hf x hx i j h

lemma good_C_mul {n : ℕ} (c : ℤ) {f : MvPolynomial (Fin 2) ℤ} (hf : Good n f) :
    Good n (C c * f) := by
  intro i j h
  rw [coeff_C_mul, mul_left_comm]
  exact Dvd.dvd.mul_left (hf i j h) c

lemma good_atom (n K s a : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) (hs : s ≤ K) (ha : a ≤ K - s) :
    Good n (monomial (Finsupp.single (0 : Fin 2) (s + a) + Finsupp.single 1 (s + (K - s - a)))
      ((n.factorial / K * (K.choose s * (K - s).choose a) : ℕ) : ℤ)) := by
  intro i j h
  rw [coeff_monomial_two]
  split_ifs with hij
  · obtain ⟨rfl, rfl⟩ := hij
    rw [← Nat.cast_mul]
    exact Int.natCast_dvd_natCast.mpr (factorial_dvd_term n K s a hK1 hKn hs ha h)
  · simp

lemma C_mul_pow_u (m K : ℕ) :
    C (m : ℤ) * (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ^ K =
      ∑ s ∈ range (K + 1), ∑ a ∈ range (K - s + 1),
        monomial (Finsupp.single (0 : Fin 2) (s + a) + Finsupp.single 1 (s + (K - s - a)))
          ((m * (K.choose s * (K - s).choose a) : ℕ) : ℤ) := by
  rw [show (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) = X 0 * X 1 + (X 0 + X 1) by ring,
    add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [add_pow]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [monomial_two_eq]
  simp only [Nat.cast_mul, map_mul, map_natCast]
  ring

lemma good_C_mul_pow_u (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 0 + X 1 + X 0 * X 1 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  rw [C_mul_pow_u]
  refine good_sum _ _ fun s hs => good_sum _ _ fun a ha => ?_
  rw [Finset.mem_range] at hs ha
  exact good_atom n K s a hK1 hKn (by omega) (by omega)

lemma logPolynomialDefectDivisible_C_mul_X_zero_pow (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 0 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  have h := good_atom n K 0 K hK1 hKn (by omega) (by omega)
  rw [monomial_two_eq] at h
  simpa using h

lemma logPolynomialDefectDivisible_C_mul_X_one_pow (n K : ℕ) (hK1 : 1 ≤ K) (hKn : K ≤ n) :
    Good n (C ((n.factorial / K : ℕ) : ℤ) * (X 1 : MvPolynomial (Fin 2) ℤ) ^ K) := by
  have h := good_atom n K 0 0 hK1 hKn (by omega) (by omega)
  rw [monomial_two_eq] at h
  simpa using h

lemma good_truncLogF (n : ℕ) (u : MvPolynomial (Fin 2) ℤ)
    (hu : ∀ K, 1 ≤ K → K ≤ n → Good n (C ((n.factorial / K : ℕ) : ℤ) * u ^ K)) :
    Good n (truncLogF n u) := by
  unfold truncLogF
  refine good_sum _ _ fun k hk => ?_
  rw [Finset.mem_range] at hk
  have e : ((-1 : MvPolynomial (Fin 2) ℤ) ^ k * ((n.factorial / (k + 1) : ℕ) : MvPolynomial (Fin 2) ℤ) *
      u ^ (k + 1)) = C ((-1) ^ k) * (C ((n.factorial / (k + 1) : ℕ) : ℤ) * u ^ (k + 1)) := by
    simp only [map_pow, map_neg, map_one, map_natCast]; ring
  rw [e]
  exact good_C_mul _ (hu (k + 1) (by omega) (by omega))

theorem good_logDefect (n : ℕ) : Good n (logDefect n) := by
  unfold logDefect
  refine good_sub (good_sub ?_ ?_) ?_
  · exact good_truncLogF n _ fun K h1 h2 => good_C_mul_pow_u n K h1 h2
  · exact good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_zero_pow n K h1 h2
  · exact good_truncLogF n _ fun K h1 h2 => logPolynomialDefectDivisible_C_mul_X_one_pow n K h1 h2

theorem logDefect_coeff_dvd : ∀ (n i j : ℕ), n ≤ i + j → ∃ d : ℤ,
    ((i.factorial * j.factorial : ℕ) : ℤ) *
        AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) =
      ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * d := by
  intro n i j h
  exact good_logDefect n i j h

end GlobalTheory.LogUIntg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorialTruncatedLogAdditivityDefectCoeffDvdStatement

section

@[expose] public section

open GlobalTheory.LogU

theorem _root_.GlobalTheory.T.factorialTruncatedLogAdditivityDefect_coeff_dvd : ∀ (n i j : ℕ), n ≤ i + j → ∃ d : ℤ, ((i.factorial * j.factorial : ℕ) : ℤ) * AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * d := by
  first | exact @GlobalTheory.LogUIntg.logDefect_coeff_dvd | exact GlobalTheory.LogUIntg.logDefect_coeff_dvd | (intros; apply GlobalTheory.LogUIntg.logDefect_coeff_dvd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogDefectCoeffEqZero

section

@[expose] public section

open GlobalTheory.LogU

namespace GlobalTheory.LogU

open MvPolynomial

theorem logDefect_coeff_eq_zero : ∀ (n i j : ℕ), i + j < n →
    AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = 0 := by
  intro n i j hij
  let J : Ideal (MvPolynomial (Fin 2) ℚ) := MvPolynomial.idealOfVars (Fin 2) ℚ
  let q : MvPolynomial (Fin 2) ℚ →+* MvPolynomial (Fin 2) ℚ ⧸ J ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : MvPolynomial (Fin 2) ℚ ⧸ J ^ n) := fun m hm => by
    have hu : IsUnit ((m : ℚ)) := (Nat.cast_ne_zero.2 hm).isUnit
    simpa using hu.map (q.comp MvPolynomial.C)
  have hI : (J.map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]; exact Ideal.map_quotient_self _
  have hXJ : ∀ k, (X k : MvPolynomial (Fin 2) ℚ) ∈ J := fun k =>
    Ideal.subset_span (Set.mem_range_self k)
  have key := GlobalTheory.MemLoc.LogAdd.trunc_add hR n _ hI (q (X 0)) (q (X 1))
    (Ideal.mem_map_of_mem q (hXJ 0)) (Ideal.mem_map_of_mem q (hXJ 1))
  have h0 : MvPolynomial.aeval ![q (X 0), q (X 1)] (logDefect n) = 0 := by
    refine (aeval_logDefect n (q (X 0)) (q (X 1))).trans ?_
    simp only [truncLogF]; rw [key]; ring
  have hcomp : q.comp (MvPolynomial.map (Int.castRingHom ℚ)) =
      (MvPolynomial.aeval (R := ℤ) ![q (X 0), q (X 1)]).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro k; fin_cases k <;> simp
  have hφ : q (MvPolynomial.map (Int.castRingHom ℚ) (logDefect n)) = 0 := by
    have := RingHom.congr_fun hcomp (logDefect n)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at this
    rw [this, h0]
  rw [Ideal.Quotient.eq_zero_iff_mem, mem_pow_idealOfVars_iff'] at hφ
  have hd : (Finsupp.single (0 : Fin 2) i + Finsupp.single 1 j).degree < n := by
    first
      | simpa [Finsupp.degree_single] using hij
      | simpa [Finsupp.degree, Finsupp.support_single_ne_zero] using hij
  have := hφ _ hd
  rw [MvPolynomial.coeff_map] at this
  simpa using this

end GlobalTheory.LogU
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LogDefectCoeffEqZeroStatement

section

@[expose] public section

open GlobalTheory.LogU

theorem _root_.GlobalTheory.T.coeff_logDefect_eq_zero_of_add_lt : ∀ (n i j : ℕ), i + j < n → AddMonoidAlgebra.coeff (GlobalTheory.LogU.logDefect n) (Finsupp.single 0 i + Finsupp.single 1 j) = 0 := by
  first | (exact @GlobalTheory.LogU.logDefect_coeff_eq_zero) | (exact GlobalTheory.LogU.logDefect_coeff_eq_zero) | (intros; apply GlobalTheory.LogU.logDefect_coeff_eq_zero  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAcrisLogOneAddAddOfMul

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.LogU

theorem defect_mem {R : Type} [CommRing R] (S : Subring R) (a b : R)
    (ha : ∀ i : ℕ, ∃ g ∈ S, ((i.factorial : ℕ) : R) * g = a ^ i)
    (hb : ∀ j : ℕ, ∃ g ∈ S, ((j.factorial : ℕ) : R) * g = b ^ j) (n : ℕ) :
    ∃ e ∈ S, truncLogF n (a + b + a * b) - truncLogF n a - truncLogF n b =
      ((n.factorial * ((n - 1) / 2).factorial : ℕ) : R) * e := by
  choose A hAS hA using ha
  choose B hBS hB using hb
  have hD : ∀ d : Fin 2 →₀ ℕ, ∃ D : ℤ, (((d 0).factorial * (d 1).factorial : ℕ) : ℤ) *
      AddMonoidAlgebra.coeff (logDefect n) d = ((n.factorial * ((n - 1) / 2).factorial : ℕ) : ℤ) * D := by
    intro d
    have hd : Finsupp.single 0 (d 0) + Finsupp.single 1 (d 1) = d := by
      ext x; fin_cases x <;> simp
    by_cases h : d 0 + d 1 < n
    · have := GlobalTheory.T.coeff_logDefect_eq_zero_of_add_lt n (d 0) (d 1) h
      rw [hd] at this
      exact ⟨0, by rw [this]; simp⟩
    · obtain ⟨D, hD⟩ := GlobalTheory.T.factorialTruncatedLogAdditivityDefect_coeff_dvd n (d 0) (d 1) (by omega)
      rw [hd] at hD
      exact ⟨D, hD⟩
  choose D hD using hD
  refine ⟨∑ d ∈ (logDefect n).support, (D d : R) * (A (d 0) * B (d 1)),
    Subring.sum_mem _ fun d _ => Subring.mul_mem _ (intCast_mem S _)
      (Subring.mul_mem _ (hAS _) (hBS _)), ?_⟩
  rw [← aeval_logDefect, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have hc := congrArg (Int.cast : ℤ → R) (hD d)
  push_cast at hc
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, eq_intCast]
  rw [← hA, ← hB]
  push_cast
  linear_combination (A (d 0) * B (d 1)) * hc

theorem isLogJ_add : ∀ (l : ℕ) [Fact l.Prime] (a b : Per.Ainf l) (y y' : Per.Acris l), GlobalTheory.LogU.InJ a →
    GlobalTheory.LogU.InJ b → GlobalTheory.LogU.IsLogJ a y → GlobalTheory.LogU.IsLogJ b y' → GlobalTheory.LogU.IsLogJ (a + b + a * b) (y + y') := by
  intro l _ a b y y' ha hb hy hy' r
  have hl : l.Prime := Fact.out
  obtain ⟨N1, hN1⟩ := hy r
  obtain ⟨N2, hN2⟩ := hy' r
  refine ⟨max (max N1 N2) (2 * l ^ r + 1), fun n hn => ?_⟩
  obtain ⟨sa, hsa, za, hza⟩ := hN1 n (le_of_max_le_left (le_of_max_le_left hn))
  obtain ⟨sb, hsb, zb, hzb⟩ := hN2 n (le_of_max_le_right (le_of_max_le_left hn))
  have hn' : 2 * l ^ r + 1 ≤ n := le_of_max_le_right hn
  have hA : ∀ i : ℕ, ∃ g ∈ (Per.Acris0 l).toSubring, ((i.factorial : ℕ) : Per.AinfP l) * g =
      algebraMap (Per.Ainf l) (Per.AinfP l) a ^ i := fun i => by
    obtain ⟨g, hg⟩ := exists_divPow ha i
    exact ⟨g, g.2, hg⟩
  have hB : ∀ i : ℕ, ∃ g ∈ (Per.Acris0 l).toSubring, ((i.factorial : ℕ) : Per.AinfP l) * g =
      algebraMap (Per.Ainf l) (Per.AinfP l) b ^ i := fun i => by
    obtain ⟨g, hg⟩ := exists_divPow hb i
    exact ⟨g, g.2, hg⟩
  obtain ⟨e, he, hE⟩ := defect_mem _ _ _ hA hB n
  have hdvd : l ^ r ∣ ((n - 1) / 2).factorial := by
    refine Nat.dvd_factorial (pow_pos hl.pos r) ?_
    generalize l ^ r = L at hn' ⊢
    omega
  obtain ⟨q, hq⟩ := hdvd
  let E : Per.Acris0 l := ⟨e, he⟩
  refine ⟨sa + sb + ((l ^ r * q : ℕ) : Per.Acris0 l) * E, ?_,
    za + zb - (q : Per.Acris l) * algebraMap (Per.Acris0 l) (Per.Acris l) E, ?_⟩
  · rw [hq] at hE
    simp only [truncLogF] at hE
    have hEe : ((E : Per.Acris0 l) : Per.AinfP l) = e := rfl
    have hc : (((sa + sb + ((l ^ r * q : ℕ) : Per.Acris0 l) * E : Per.Acris0 l)) : Per.AinfP l) =
        (sa : Per.AinfP l) + (sb : Per.AinfP l) + ((l ^ r * q : ℕ) : Per.AinfP l) * e := by
      simp [hEe]
    rw [hc]
    simp only [map_add (f := _), map_mul]
    push_cast at hE ⊢
    linear_combination hsa + hsb - hE
  · set_option synthInstance.maxHeartbeats 200000 in
    simp only [map_add (f := algebraMap (Per.Acris0 l) (Per.Acris l)), map_mul, map_natCast]
    push_cast
    linear_combination hza + hzb

end GlobalTheory.LogU
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAcrisLogOneAddAddOfMulStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.isAcrisLogOneAdd_add_of_mul : ∀ (l : ℕ) [Fact l.Prime] (a b : Per.Ainf l) (y y' : Per.Acris l), GlobalTheory.LogU.InJ a → GlobalTheory.LogU.InJ b → GlobalTheory.LogU.IsLogJ a y → GlobalTheory.LogU.IsLogJ b y' → GlobalTheory.LogU.IsLogJ (a + b + a * b) (y + y') := by
  first | (exact @GlobalTheory.LogU.isLogJ_add) | (exact GlobalTheory.LogU.isLogJ_add) | (intros; apply GlobalTheory.LogU.isLogJ_add  <;> assumption)
end
end
