module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsEvenPositiveDefiniteIntMatrixDetSq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesHolomorphicQExpansionOfBoundedCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSlashEighthRootOfSquareDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsFiniteRepsScaledLatticeCardNorm
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherMore
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HasQExpansionAffineTranslateCoeff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashRationalMatrixProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertSlashUnnormalizedConstMul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.HilbertThetaSeriesPeriodicInversionFormula
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntMatrixIsometryPrimeOrderLatticeStability
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntegralTestFunctionFiniteFourierTransformOfOddP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPosGramFormIntegralLatticeProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IsDelNeZeroCoprimeDenominatorsDifferentGenerator
import Mathlib.Tactic.Linter.Style
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesCongrOneModPOfIsometry
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaSeriesTranslationTwistsCoefficients

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.GenByTranslationsInversions

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.GeneratorMatrix

theorem matId {F : Type} [Field F] (a b c d δ τ e s : F) (hδ : δ ≠ 0) (hs : s ≠ 0) (he : e ≠ 0)
    (hc : c = s - τ * δ * a) (hdet : a * d - b * c = e) :
    !![a, b; c, d] = !![0, -δ⁻¹; δ, 0] * !![1, τ / δ; 0, 1] * !![0, -(-δ)⁻¹; -δ, 0] * !![1, a / s; 0, 1]
      * !![0, -(s / e)⁻¹; s / e, 0] * !![1, (d + τ * δ * b) * e / s; 0, 1] * !![e, 0; 0, 1] := by
  subst hc
  simp only [Matrix.mul_fin_two]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> field_simp
  all_goals first | ring1 | linear_combination -hdet | linear_combination δ * τ * hdet

variable {F : Type} [Field F] [NumberField F]

theorem exists_place (p : ℕ) (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk8.exists_place p hp

theorem ne_zero_of_pUnit {p : ℕ} {w : HeightOneSpectrum (𝓞 F)} (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) {x : F}
    (h : PUnit p x) : x ≠ 0 := by
  intro hx; have := h w hw; rw [hx, map_zero] at this; exact zero_ne_one this

theorem val_wm (c : Fˣ) : ((wm c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -(c : F)⁻¹; (c : F), 0] := by
  simp [wm]

theorem val_aff (y : Fˣ) (x : F) : ((aff y x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(y : F), x; 0, 1] := rfl

end GlobalTheory.HilbertThetaSeries.GeneratorMatrix

namespace GlobalTheory.HilbertThetaSeries


open GlobalTheory.HilbertThetaSeries.GeneratorMatrix in
theorem gen_by_translations_inversions : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∀ γ : GL (Fin 2) F, InG p δ γ → ∃ (b₁ b₂ b₃ : F) (c₁ c₂ c₃ ε : Fˣ), PInt p (δ * b₁) ∧ PInt p (δ * b₂) ∧ PInt p (δ * b₃) ∧ PUnit p (c₁ / δ) ∧ PUnit p (c₂ / δ) ∧ PUnit p (c₃ / δ) ∧ TP (ε : F) ∧ γ = wm c₁ * aff 1 b₁ * wm c₂ * aff 1 b₂ * wm c₃ * aff 1 b₃ * aff ε 0 := by
  intro F _ _ _ p hp δ hδ γ hγ
  classical
  obtain ⟨hA, hB, hC, hD, hE, hT⟩ := hγ
  obtain ⟨w₀, hw₀⟩ := exists_place (F := F) p hp
  have hδ0 : δ ≠ 0 := by
    intro h; have := hδ w₀ hw₀; rw [h, map_zero] at this; exact WithZero.exp_ne_zero this.symm
  have hdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = γ.val.det := (Matrix.det_fin_two _).symm
  have he0 : γ.val.det ≠ 0 := ne_zero_of_pUnit hw₀ hE
  have hI : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set S := (Ideal.finite_factors hI).toFinset with hS
  have hmem : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → w ∈ S := by
    intro w hw
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
    exact hw
  obtain ⟨τ, hτ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun w => w.asIdeal) (fun _ => 1)
    (fun w _ => w.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if w.1.valuation F (γ.val 1 0 / δ) = 1 then 0 else 1)
  set a := γ.val 0 0 with ha
  set b := γ.val 0 1 with hb
  set c := γ.val 1 0 with hc
  set d := γ.val 1 1 with hd
  set e := γ.val.det with he
  set t : F := algebraMap (𝓞 F) F τ with ht
  set s := c + t * δ * a with hs
  have hsd : s / δ = c / δ + t * a := by rw [hs]; field_simp
  have hu : PUnit p (s / δ) := by
    intro w hw
    have hτw := hτ w (hmem w hw)
    simp only [pow_one] at hτw
    rw [hsd]
    by_cases h1 : w.valuation F (c / δ) = 1
    · rw [if_pos h1, sub_zero] at hτw
      have htlt : w.valuation F t < 1 := (w.valuation_lt_one_iff_mem τ).mpr hτw
      have : w.valuation F (t * a) < 1 := by
        rw [map_mul]
        calc w.valuation F t * w.valuation F a ≤ w.valuation F t * 1 := mul_le_mul' le_rfl (hA w hw)
          _ < 1 := by rw [mul_one]; exact htlt
      rw [Valuation.map_add_eq_of_lt_left _ (h1 ▸ this), h1]
    · rw [if_neg h1] at hτw
      have hclt : w.valuation F (c / δ) < 1 := lt_of_le_of_ne (hC w hw) h1
      have hav : w.valuation F a = 1 := by
        by_contra hne
        have halt : w.valuation F a < 1 := lt_of_le_of_ne (hA w hw) hne
        have hE' := hE w hw
        have hx : e = a * d - (δ * b) * (c / δ) := by rw [← hdet]; field_simp
        have h1' : w.valuation F (a * d) < 1 := by
          rw [map_mul]
          calc w.valuation F a * w.valuation F d ≤ w.valuation F a * 1 := mul_le_mul' le_rfl (hD w hw)
            _ < 1 := by rw [mul_one]; exact halt
        have h2' : w.valuation F ((δ * b) * (c / δ)) < 1 := by
          rw [map_mul]
          calc w.valuation F (δ * b) * w.valuation F (c / δ) ≤ 1 * w.valuation F (c / δ) := mul_le_mul' (hB w hw) le_rfl
            _ < 1 := by rw [one_mul]; exact hclt
        have : w.valuation F e < 1 := by
          rw [hx]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1' h2')
        rw [hE'] at this; exact lt_irrefl _ this
      have htm : w.valuation F (t - 1) < 1 := by
        have := (w.valuation_lt_one_iff_mem (K := F) (τ - 1)).mpr hτw
        simpa [ht] using this
      have htv : w.valuation F t = 1 := by
        have : t = 1 + (t - 1) := by ring
        rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact htm), map_one]
      have hta : w.valuation F (t * a) = 1 := by rw [map_mul, htv, hav, mul_one]
      rw [Valuation.map_add_eq_of_lt_right _ (hta ▸ hclt), hta]
  have hs0 : s ≠ 0 := by
    intro h0; exact ne_zero_of_pUnit hw₀ hu (by rw [h0, zero_div])
  refine ⟨t / δ, a / s, (d + t * δ * b) * e / s, Units.mk0 δ hδ0, -Units.mk0 δ hδ0,
    Units.mk0 (s / e) (div_ne_zero hs0 he0), Units.mk0 e he0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; rw [mul_div_cancel₀ _ hδ0]; exact w.valuation_le_one τ
  · intro w hw
    have : δ * (a / s) = a / (s / δ) := by field_simp
    rw [this, map_div₀, hu w hw, div_one]; exact hA w hw
  · intro w hw
    have : δ * ((d + t * δ * b) * e / s) = (d + t * (δ * b)) * e / (s / δ) := by field_simp
    rw [this, map_div₀, hu w hw, div_one, map_mul, hE w hw, mul_one]
    refine Valuation.map_add_le _ (hD w hw) ?_
    rw [map_mul]
    calc w.valuation F t * w.valuation F (δ * b) ≤ 1 * 1 :=
          mul_le_mul' (w.valuation_le_one τ) (hB w hw)
      _ = 1 := one_mul 1
  · intro w hw; rw [Units.val_mk0, div_self hδ0, map_one]
  · intro w hw; rw [Units.val_neg, Units.val_mk0, neg_div, div_self hδ0, Valuation.map_neg, map_one]
  · intro w hw
    have : s / e / δ = s / δ / e := by ring
    rw [Units.val_mk0, this, map_div₀, hu w hw, hE w hw, div_one]
  · rw [Units.val_mk0]; exact hT
  · refine Units.ext ?_
    simp only [Units.val_mul, val_wm, val_aff, Units.val_neg, Units.val_mk0, Units.val_one]
    rw [Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) F)]
    exact matId a b c d δ t e s hδ0 hs0 he0 (by rw [hs]; ring) hdet

end GlobalTheory.HilbertThetaSeries
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.IntegralTestFunctionMulTraceCharacterQuadFormOfD

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem et_pow_den_eq_one {F : Type} [Field F] [NumberField F] (y : F) :
    et y ^ (Algebra.trace ℚ F y).den = 1 := by
  unfold et
  set q : ℚ := Algebra.trace ℚ F y
  rw [← Complex.exp_nat_mul]
  have h : ((q.den : ℕ) : ℂ) * (q : ℂ) = (q.num : ℂ) := by
    have := Rat.den_mul_eq_num q
    exact_mod_cast congrArg (Rat.cast : ℚ → ℂ) this
  have : ((q.den : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (q : ℂ)) = (q.num : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [← h]; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem padic_norm_et_eq_one {F : Type} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (y : F) :
    ‖ι.symm (et y)‖ = 1 := by
  have h := congrArg (fun z => ‖ι.symm z‖) (et_pow_den_eq_one y)
  simp only [map_pow, norm_pow, map_one, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (Rat.den_nz _)).1 h

theorem QF_mulVec_of_iso {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {G S : Matrix κ κ ℤ} (h : Sᵀ * G * S = G) (x : κ → F) :
    QF G (S.map (Int.cast : ℤ → F) *ᵥ x) = QF G x := by
  have h' : (S.map (Int.cast : ℤ → F))ᵀ * G.map (Int.cast : ℤ → F) * S.map (Int.cast : ℤ → F)
      = G.map (Int.cast : ℤ → F) := by
    have := congrArg (fun A : Matrix κ κ ℤ => A.map (Int.castRingHom F)) h
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    exact this
  unfold QF BF
  congr 1
  conv_rhs => rw [← h']
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x,
    Matrix.vecMul_transpose]

theorem good_mul_et_QF : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (δ : F), IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → ∀ b : F, PInt p (δ * b) → Good ι S fun x => Φ x * et (b * QF G x) := by
  intro F _ _ p hp ι δ hδ κ _ _ G S t hL Φ hΦ b hb
  obtain ⟨⟨N, hN, hNp, hsupp, hper⟩, hS, hint, h0⟩ := hΦ
  obtain ⟨M, hM, hMp, htr⟩ := (GlobalTheory.HilbertThetaSeries.denominators_prime_to F p hp.out δ hδ).2.2.1 b hb
  obtain ⟨hadd, hsmul, -, hI, hLL, haL, het, -⟩ := GlobalTheory.HilbertThetaSeries.formLatticeProps F κ G hL.pos
  have hN' : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have hM' : (M : F) ≠ 0 := by exact_mod_cast hM.ne'
  have hnat : ∀ (n : ℕ) (l : κ → F), l ∈ LL F κ → (n : F) • l ∈ LL F κ := by
    intro n l hl
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hl n
  refine ⟨⟨N * N * M, by positivity, Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hNp) hMp, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨l, hl, rfl⟩ := (haL _ _).1 (hsupp x (left_ne_zero_of_mul hx))
    refine (haL _ _).2 ⟨_, hnat (N * M) l hl, ?_⟩
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  · intro x l' hl'
    obtain ⟨l, hl, rfl⟩ := (haL _ _).1 hl'
    have h1 : Φ (x + ((N * N * M : ℕ) : F) • l) = Φ x := by
      refine hper x _ ((haL _ _).2 ⟨_, hnat (N * M) l hl, ?_⟩)
      rw [smul_smul]
      congr 1
      push_cast
      ring
    show Φ _ * _ = Φ x * _
    rw [h1]
    by_cases hx : Φ x = 0
    · simp [hx]
    obtain ⟨y, hy, rfl⟩ := (haL _ _).1 (hsupp x hx)
    congr 1
    have hz : IsIntegral ℤ ((N : F) * BF G y l + ((N * N * N * N * M : ℕ) : F) * QF G l) :=
      ((isIntegral_natCast N).mul ((hI y hy).2 l hl)).add ((isIntegral_natCast _).mul (hI l hl).1)
    have h2 : b * QF G ((N : F)⁻¹ • y + ((N * N * M : ℕ) : F) • l) = b * QF G ((N : F)⁻¹ • y) +
        (M : F) * b * ((N : F) * BF G y l + ((N * N * N * N * M : ℕ) : F) * QF G l) := by
      rw [(hadd _ _).2, (hsmul _ y _).1, (hadd y _).1, (hsmul _ l y).1, (hsmul _ l y).2.1, (hadd l y).1]
      push_cast
      field_simp
      ring
    rw [h2, (het _ _).1, (het _ 0).2.2.1.2 (htr _ hz), mul_one]
  · intro x
    show Φ _ * _ = Φ x * _
    rw [hS, QF_mulVec_of_iso hL.iso]
  · intro x
    show ‖ι.symm (Φ x * _)‖ ≤ 1
    rw [map_mul, norm_mul, padic_norm_et_eq_one, mul_one]
    exact hint x
  · show ‖ι.symm (Φ 0 * _) - 1‖ ≤ _
    have : et (b * QF G (0 : κ → F)) = 1 := by simp [et, QF, BF]
    rw [this, mul_one]
    exact h0

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.integral_test_function_mul_trace_character_quad_form_of_delta_integral : ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ) (δ : F), IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ Φ : (κ → F) → ℂ, Good ι S Φ → ∀ b : F, PInt p (δ * b) → Good ι S fun x => Φ x * et (b * QF G x) := by
  first | exact @GlobalTheory.HilbertThetaSeries.good_mul_et_QF | exact GlobalTheory.HilbertThetaSeries.good_mul_et_QF | (intros; apply GlobalTheory.HilbertThetaSeries.good_mul_et_QF <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ThetaTranslateIntegralCongruentOneModPrime

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem theta_translates_integral_one : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ γ : GL (Fin 2) F, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ) (th G oneL) - 1) := by
  intro F _ _ _ p _ ι hp2 δ hδ κ _ _ G S t hL γ hγ

  have hPos : ∀ g : GL (Fin 2) F, TP g.val.det → Pos (toInf g) := fun g hg =>
    ((GlobalTheory.HilbertThetaSeries.RatSlash.rat_slash F (p - 1) (th G oneL)).2.1 g).1.2 hg
  have hTP1 : TP (1 : F) := fun v => by simp [reAt]
  have hdetw : ∀ c : Fˣ, (wm c).val.det = 1 := fun c => by
    simp [wm, Matrix.det_fin_two]
  have hdeta : ∀ (e : Fˣ) (b : F), (aff e b).val.det = e := fun e b => by
    simp [aff, Matrix.det_fin_two]
  have hPw : ∀ c : Fˣ, Pos (toInf (wm c)) := fun c => hPos _ (by rw [hdetw]; exact hTP1)
  have hPa : ∀ b : F, Pos (toInf (aff 1 b)) := fun b => hPos _ (by rw [hdeta]; simpa using hTP1)

  have haL1 : ∀ x : κ → F, x ∈ aL κ (1 : F) ↔ x ∈ LL F κ := fun x => by
    simp [aL, AddSubgroup.mem_map]
  have hone : ∀ x y : κ → F, (x ∈ LL F κ ↔ y ∈ LL F κ) → oneL x = oneL y := fun x y h => by
    by_cases hy : y ∈ LL F κ
    · rw [oneL, oneL, if_pos hy, if_pos (h.2 hy)]
    · rw [oneL, oneL, if_neg hy, if_neg fun hx => hy (h.1 hx)]

  have hgood1 : Good ι S (oneL (F := F) (κ := κ)) := by
    have hS := (GlobalTheory.HilbertThetaSeries.IsoP.isometry_order_p F p Fact.out κ G S t hL).2.1
    refine ⟨⟨1, one_pos, Nat.coprime_one_left p, ?_, ?_⟩, ?_, ?_, ?_⟩
    · intro x hx
      have hx' : x ∈ LL F κ := by
        by_contra h; exact hx (by simp [oneL, h])
      simpa [haL1] using hx'
    · intro x l hl
      have hl' : l ∈ LL F κ := by simpa [haL1] using hl
      exact hone _ _ ((LL F κ).add_mem_cancel_right hl')
    · intro x
      have h1 := ((hS x).2.2.2 1)
      rw [haL1, haL1] at h1
      exact hone _ _ h1
    · intro x
      unfold oneL; split_ifs <;> simp
    · have h0 : (0 : κ → F) ∈ LL F κ := (LL F κ).zero_mem
      simp only [oneL, h0, if_true, map_one, sub_self, norm_zero]
      positivity

  have hW : ∀ (c : Fˣ) (Φ : (κ → F) → ℂ), Good ι S Φ → PUnit p ((c : F) / δ) →
      ∃ Ψ, Good ι S Ψ ∧ sl0 (p - 1) (toInf (wm c)) (th G Φ) = th G Ψ := by
    intro c Φ hΦ hc
    obtain ⟨N, hN, hNp, hSB⟩ := hΦ.1
    have hNF : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
    have hint : IsIntegral ℤ ((N : F) / (N : F)⁻¹) := by
      rw [div_inv_eq_mul, ← Nat.cast_mul]
      simpa using isIntegral_algebraMap (R := ℤ) (A := F) (x := ((N * N : ℕ) : ℤ))
    obtain ⟨T, hT, h0T, hle, -⟩ := GlobalTheory.HilbertThetaSeries.exists_isReps_aL F κ (N : F) (N : F)⁻¹ hNF (inv_ne_zero hNF) hint
    refine ⟨_, GlobalTheory.T.integral_test_function_finite_fourier_transform_of_odd_prime F p ι hp2 δ hδ κ G S t hL Φ N T c hΦ hN hNp hSB hT h0T hc, ?_⟩
    exact GlobalTheory.T.hilbertThetaSeries_periodic_inversion_formula F κ G hL.pos t hL.det (p - 1) hL.card (N : F) (N : F)⁻¹ c T Φ hNF (inv_ne_zero hNF) hle hT hSB.1 hSB.2

  have hA : ∀ (b : F) (Φ : (κ → F) → ℂ), Good ι S Φ → PInt p (δ * b) →
      ∃ Ψ, Good ι S Ψ ∧ sl0 (p - 1) (toInf (aff 1 b)) (th G Φ) = th G Ψ := fun b Φ hΦ hb =>
    ⟨_, GlobalTheory.T.integral_test_function_mul_trace_character_quad_form_of_delta_integral F p ι δ hδ κ G S t hL Φ hΦ b hb, GlobalTheory.HilbertThetaSeries.th_translate F κ G (p - 1) b Φ⟩

  let P : GL (Fin 2) F → Prop := fun g => Pos (toInf g) ∧
    ∃ Ψ, Good ι S Ψ ∧ sl0 (p - 1) (toInf g) (th G oneL) = th G Ψ
  have step : ∀ g g' : GL (Fin 2) F, P g → Pos (toInf g') →
      (∀ Ψ, Good ι S Ψ → ∃ Ψ', Good ι S Ψ' ∧ sl0 (p - 1) (toInf g') (th G Ψ) = th G Ψ') → P (g * g') := by
    intro g g' ⟨hg, Ψ, hΨ, he⟩ hg' hstep
    have hc := SlashCocycle.slash_cocycle F (p - 1) (toInf g) (toInf g') (th G oneL) hg hg'
    obtain ⟨Ψ', hΨ', he'⟩ := hstep Ψ hΨ
    refine ⟨by rw [map_mul]; exact hc.1, Ψ', hΨ', ?_⟩
    rw [map_mul, hc.2.2.1, he, he']
  obtain ⟨b₁, b₂, b₃, c₁, c₂, c₃, ε, hb₁, hb₂, hb₃, hc₁, hc₂, hc₃, hε, hγe⟩ := GlobalTheory.HilbertThetaSeries.gen_by_translations_inversions F p Fact.out δ hδ γ hγ
  have P1 : P (wm c₁) := by
    refine ⟨hPw c₁, ?_⟩
    exact hW c₁ oneL hgood1 hc₁
  have P6 := step _ _ (step _ _ (step _ _ (step _ _ (step _ _ P1 (hPa b₁) (fun Ψ h => hA b₁ Ψ h hb₁))
    (hPw c₂) (fun Ψ h => hW c₂ Ψ h hc₂)) (hPa b₂) (fun Ψ h => hA b₂ Ψ h hb₂))
    (hPw c₃) (fun Ψ h => hW c₃ Ψ h hc₃)) (hPa b₃) (fun Ψ h => hA b₃ Ψ h hb₃)
  obtain ⟨hX, Ψ, hΨ, hXe⟩ := P6
  have hE : Pos (toInf (aff ε 0)) := hPos _ (by rw [hdeta]; exact hε)
  have hc := SlashCocycle.slash_cocycle F (p - 1) (toInf (wm c₁ * aff 1 b₁ * wm c₂ * aff 1 b₂ * wm c₃ * aff 1 b₃)) (toInf (aff ε 0)) (th G oneL) hX hE
  rw [hγe, map_mul, hc.2.2.1, hXe]

  have hden : ∀ z : Hn F, (∏ v, UpperHalfPlane.denom (cmp v (toInf (aff ε 0))) (z v)) = 1 := by
    intro z
    refine Finset.prod_eq_one fun v _ => ?_
    simp [UpperHalfPlane.denom, cmp, toInf, aff, Matrix.GeneralLinearGroup.map]
  have hsub : sl0 (p - 1) (toInf (aff ε 0)) (th G Ψ - 1) = sl0 (p - 1) (toInf (aff ε 0)) (th G Ψ) - 1 := by
    funext z
    simp [sl0, hden]
  rw [← hsub]
  obtain ⟨a, hQ, hbd⟩ := GlobalTheory.T.thetaSeries_congr_one_mod_p_of_isometry F p ι κ G S t hL Ψ hΨ
  refine ⟨_, GlobalTheory.T.hasQExpansion_affineTranslate_coeff F (p - 1) (th G Ψ - 1) a ε 0 hε hQ, fun ξ => ?_⟩
  simpa [et] using hbd (ξ / ε)

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.theta_translate_integral_congruent_one_mod_prime : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (G S : Matrix κ κ ℤ) (t : ℕ), LatD p G S t → ∀ γ : GL (Fin 2) F, InG p δ γ → Small ι (p : ℝ)⁻¹ (sl0 (p - 1) (toInf γ) (th G oneL) - 1) := by
  first | exact @GlobalTheory.HilbertThetaSeries.theta_translates_integral_one | exact GlobalTheory.HilbertThetaSeries.theta_translates_integral_one | (intros; apply GlobalTheory.HilbertThetaSeries.theta_translates_integral_one <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.ExistsSeedThetaLatticeFixedPointFree

section

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem seed_exists : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∃ θ : Hn F → ℂ, Seed ι δ θ := by
  intro F _ _ _ p hp ι hp2 δ hδ
  obtain ⟨G, S, t, hL⟩ := GlobalTheory.T.exists_evenPositiveDefinite_intMatrix_det_sq p hp.out hp2
  have hsupp : ∀ x : (Fin (p - 1) ⊕ Fin (p - 1)) → F, (oneL x : ℂ) ≠ 0 → x ∈ aL (Fin (p - 1) ⊕ Fin (p - 1)) (1 : F) := by
    intro x hx
    have hx' : x ∈ LL F (Fin (p - 1) ⊕ Fin (p - 1)) := by
      by_contra h
      exact hx (by simp [oneL, h])
    exact ⟨x, hx', by simp⟩
  have hbd : ∀ x : (Fin (p - 1) ⊕ Fin (p - 1)) → F, ‖(oneL x : ℂ)‖ ≤ 1 := by
    intro x
    unfold oneL
    split_ifs <;> simp
  obtain ⟨-, hhol, hgr, -⟩ := GlobalTheory.T.thetaSeries_holomorphic_qExpansion_of_bounded_coeff F _ G hL.pos (1 : F) oneL 1 hsupp hbd
  obtain ⟨N, hN, hlev⟩ := GlobalTheory.T.theta_slash_eighth_root_of_square_det F _ G hL.pos t hL.det (p - 1) hL.card
  exact ⟨th G oneL, hhol, hgr, fun γ hγ => GlobalTheory.T.theta_translate_integral_congruent_one_mod_prime F p ι hp2 δ hδ _ G S t hL γ hγ, N, hN, hlev⟩

end GlobalTheory.HilbertThetaSeries

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

theorem _root_.GlobalTheory.T.exists_seed_theta_lattice_fixedPointFree : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ) [Fact p.Prime] (ι : Qbar p ≃+* ℂ), p ≠ 2 → ∀ δ : F, IsDel p δ → ∃ θ : Hn F → ℂ, Seed ι δ θ := by
  first | exact @GlobalTheory.HilbertThetaSeries.seed_exists | exact GlobalTheory.HilbertThetaSeries.seed_exists | (intros; apply GlobalTheory.HilbertThetaSeries.seed_exists <;> assumption)
end
end
