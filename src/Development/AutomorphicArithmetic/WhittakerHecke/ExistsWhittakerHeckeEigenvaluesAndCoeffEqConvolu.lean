module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.FacDefs
public import Development.AutomorphicArithmetic.WhittakerHecke.EqConvolutionSquareIndicatorOfEulerFactors
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.WhittakerHecke.HeightOneSpectrumRatCorrespondPrimes
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
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerHeckeEigenvaluesAtInertPlace
public import Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerHeckeEigenvaluesAtSplitPlace
import Development.AutomorphicArithmetic.WhittakerHecke.HeightOneSpectrumRatCorrespondPrimes
public import Development.AutomorphicArithmetic.WhittakerHecke.InertOrSplitOfGoodDeltaRat
public import Development.AutomorphicArithmetic.WhittakerHecke.KAtDiagIdeleOfNatMulRotationOfNotDvd
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.ExistsMultiplicativeOfPrimePowerValues

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_multiplicative_of_prime_power_values :
    ∀ M : H.P ℚ → ℕ → ℂ, (∀ v, M v 0 = 1) → ∃ μ : ℕ → ℂ, μ 1 = 1 ∧
          (∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → μ (m * n) = μ m * μ n) ∧
          ∀ (v : H.P ℚ) (k : ℕ), μ (normV v ^ k) = M v k := by
  intro M hM
  obtain ⟨hp, -, hinj, -⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  let f : ℕ → ℕ → ℂ := fun p k =>
    if h : ∃ v : H.P ℚ, normV v = p then M h.choose k else 1
  have hf : ∀ (v : H.P ℚ) (k : ℕ), f (normV v) k = M v k := by
    intro v k
    have h : ∃ w : H.P ℚ, normV w = normV v := ⟨v, rfl⟩
    have h2 : h.choose = v := hinj _ _ h.choose_spec
    simp only [f]
    rw [dite_eq_left h, h2]
  refine ⟨fun n => n.factorization.prod f, by simp, ?_, ?_⟩
  · intro m n hm hn hmn
    show (m * n).factorization.prod f = m.factorization.prod f * n.factorization.prod f
    rw [Nat.factorization_mul hm.ne' hn.ne']
    exact Finsupp.prod_add_index_of_disjoint
      (by simpa using hmn.disjoint_primeFactors) f
  · intro v k
    show (normV v ^ k).factorization.prod f = M v k
    rw [(hp v).factorization_pow, Finsupp.prod_single_index (by rw [hf, hM]), hf]
end
end

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.IdeleOfNatMulAndPrimePow

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.ideleOfNat_mul_and_prime_pow :
    (∀ m n : ℕ, 0 < m → 0 < n → pin (m * n) = pin m * pin n) ∧ (∀ (v : H.P ℚ) (k : ℕ), pin (normV v ^ k) = pv v ^ k) := by
  obtain ⟨hp, -, hinj, -⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  have hfin : ∀ n : ℕ, (Function.mulSupport fun v : H.P ℚ => pv v ^ (n.factorization (normV v))).Finite := by
    intro n
    have h1 : ((fun v : H.P ℚ => normV v) ⁻¹' (n.factorization.support : Set ℕ)).Finite :=
      Set.Finite.preimage (fun a _ b _ h => hinj a b h) (Finset.finite_toSet _)
    refine h1.subset fun v hv => ?_
    simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    exact hv (by simp only [h0, pow_zero])
  refine ⟨fun m n hm hn => ?_, fun v k => ?_⟩
  · unfold pin
    rw [← finprod_mul_distrib (hfin m) (hfin n), Nat.factorization_mul hm.ne' hn.ne']
    exact finprod_congr fun v => by rw [Finsupp.add_apply, pow_add]
  · unfold pin
    rw [(hp v).factorization_pow, finprod_eq_single _ v]
    · rw [Finsupp.single_eq_same]
    · intro w hw
      rw [Finsupp.single_eq_of_ne (fun h => hw (hinj _ _ h)), pow_zero]
end
end

-- Source module: Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerHeckeEigenvaluesAndCoeffEqConvolu

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem aE_mul' {K : Type} [Field K] [NumberField K] (x y : (A K)ˣ) : aE (x * y) = aE x * aE y := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aE, Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.exists_whittaker_hecke_eigenvalues_and_coeff_eq_convolution :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
        CenN P ω → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ), ChOk χ L → ∀ φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a → ∃ μ : ℕ → ℂ,
        (∀ n, 0 < n → n.Coprime N → ∀ r t : ℝ, r ≠ 0 →
          Wo D φ (em E (aE (iy r * pin n) * rot t)) = μ n * Wo D φ (em E (aE (iy r) * rot t))) ∧
        ((∃ r t : ℝ, r ≠ 0 ∧ Wo D φ (em E (aE (iy r) * rot t)) ≠ 0) → ∀ n, n ≠ 0 → a n = LSeries.convolution (bN N χ μ) (sqN N) n) := by
  intro E _ _ _ D P ω χ hCen hU hχω L N hχ φ hA hG a hIs
  obtain ⟨hpr, hex, hinj, hbad⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  obtain ⟨pmul, ppow⟩ := UpperTheory.ideleOfNat_mul_and_prime_pow
  have pin1 : pin 1 = 1 := by
    have := pmul 1 1 one_pos one_pos
    rw [one_mul] at this
    exact mul_eq_left.1 this.symm
  have pack : ∀ v : H.P ℚ, ¬ Bad N v → ∃ m : ℕ → ℂ, m 0 = 1 ∧ (∀ (k : ℕ) g, (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.KAt w g) → Wo D φ (em E (aE (pv v ^ k)) * g) = m k * Wo D φ g) ∧ ((∃ h, Wo D φ h ≠ 0) → (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) = PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k * m k) := fun v hv => by
    rcases UpperTheory.inert_or_split_of_good_delta_rat E D v (hG.pl v hv) with ⟨w, hw, hI⟩ | ⟨w, w', hne, hw, hw', hs, hs', hall⟩
    · exact UpperTheory.exists_whittaker_heckeEigenvalues_at_inert_place E D P ω χ hCen hχω L N φ hA hG a hIs v hv w hw hI
    · exact UpperTheory.exists_whittaker_heckeEigenvalues_at_split_place E D P ω χ hCen hχω L N φ hA hG a hIs v hv w w' hne hw hw' hs hs' hall
  choose! M hM0 hM1 hM2 using pack
  obtain ⟨μ, hμ1, hμm, hμp⟩ := UpperTheory.exists_multiplicative_of_prime_power_values (fun v k => if Bad N v then 1 else M v k) (fun v => by
    by_cases h : Bad N v
    · simp [h]
    · simp [h, hM0 v h])
  have hpN : ∀ v : H.P ℚ, ¬ normV v ∣ N → ¬ Bad N v := fun v h hb => h ((hbad N v).1 hb)
  have hμv : ∀ (v : H.P ℚ) (k : ℕ), ¬ Bad N v → μ (normV v ^ k) = M v k := fun v k h => by
    have := hμp v k
    simpa [h] using this
  refine ⟨μ, ?_, ?_⟩
  · intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hc r t hr
      by_cases h1 : n = 1
      · subst h1
        rw [pin1, mul_one, hμ1, one_mul]
      have hp : n.minFac.Prime := Nat.minFac_prime h1
      obtain ⟨k, m, hnd, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' n.minFac hp.ne_one
      obtain ⟨v, hv⟩ := hex _ hp
      have hk : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hnm
        exact hnd (hnm ▸ Nat.minFac_dvd n)
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by
        rintro rfl
        simp at hnm
        omega)
      have hmlt : m < n := by
        have h2 : 2 ≤ n.minFac ^ k := by
          calc 2 ≤ n.minFac := hp.two_le
            _ = n.minFac ^ 1 := (pow_one _).symm
            _ ≤ n.minFac ^ k := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero hk)
        nlinarith
      have hmc : m.Coprime N := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ hnm.symm) hc
      have hvb : ¬ Bad N v := hpN v fun h =>
        Nat.not_coprime_of_dvd_of_dvd hp.one_lt (Nat.minFac_dvd n) (hv ▸ h) hc
      have hcop : (normV v ^ k).Coprime m :=
        Nat.Coprime.pow_left k (by rw [hv]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
      have hpin : pin n = pv v ^ k * pin m := by
        rw [hnm, ← hv, pmul _ _ (pow_pos (hpr v).pos k) hm0, ppow]
      have hg : em E (aE (iy r * pin n) * rot t) = em E (aE (pv v ^ k)) * em E (aE (iy r * pin m) * rot t) := by
        rw [hpin, mul_left_comm, aE_mul', map_mul, map_mul, map_mul, mul_assoc]
      have hnv : n = normV v ^ k * m := by rw [hv]; exact hnm
      rw [hg, hM1 v hvb k _ (fun w hw => UpperTheory.kAt_diag_ideleOfNat_mul_rotation_of_not_dvd E v m r t hm0 (by rw [hv]; exact hnd) w hw), ih m hmlt hm0 hmc r t hr,
        ← mul_assoc, ← hμv v k hvb, ← hμm _ _ (pow_pos (hpr v).pos k) hm0 hcop, ← hnv]
  · rintro ⟨r, t, hr, hne⟩ n hn
    refine UpperTheory.eq_convolution_squareIndicator_of_euler_factors N a (bN N χ μ) hG.pos hIs.one hIs.mul hIs.bad ?_ ?_ ?_ ?_ n hn
    · simp [bN, pin1, hμ1]
    · intro x y hx hy hxy
      simp only [bN, Nat.coprime_mul_iff_left]
      by_cases h1 : x.Coprime N
      · by_cases h2 : y.Coprime N
        · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, pmul x y hx hy, hμm x y hx hy hxy, map_mul, Units.val_mul]
          push_cast
          ring
        · rw [if_neg fun h => h2 h.2, if_neg h2, mul_zero]
      · rw [if_neg fun h => h1 h.1, if_neg h1, zero_mul]
    · intro x hx
      simp only [bN]
      rw [if_neg hx]
    · intro p hp hpn
      obtain ⟨v, rfl⟩ := hex p hp
      have hvb := hpN v hpn
      rw [hM2 v hvb ⟨_, hne⟩]
      congr 1
      funext k
      have hc : (normV v ^ k).Coprime N := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
      simp only [bN, if_pos hc]
      rw [ppow, map_pow, Units.val_pow_eq_pow_val, hμv v k hvb]
      rfl
end
end
