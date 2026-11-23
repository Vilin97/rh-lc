module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90Statement
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSupersetMemSUnits
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitValuationEqOfAdm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.GaloisPlacesTransitive
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.KummerGalois
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationUnramifiedKummerOfCoprimeUnit

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem IsKum.sum_conj_eq {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (a : ℕ → F) (k : ℕ) (hk : k < p) :
    ∑ j ∈ Finset.range p, algebraMap F E (((ζ ^ k)⁻¹) ^ j) *
        (σ ^ j) (∑ i ∈ Finset.range p, a i • θ ^ i) = (p : E) * (a k • θ ^ k) := by
  have hζ : ζ ≠ 0 := h.root.ne_zero h.prime.ne_zero
  have h1 : ∀ j, algebraMap F E (((ζ ^ k)⁻¹) ^ j) * (σ ^ j) (∑ i ∈ Finset.range p, a i • θ ^ i)
      = ∑ i ∈ Finset.range p, ((ζ ^ i / ζ ^ k) ^ j) • (a i • θ ^ i) := by
    intro j

    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_pow, map_pow (σ ^ j), h.pow_apply, div_eq_mul_inv]
    simp only [Algebra.smul_def, mul_pow, map_mul, map_pow]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single k]
  · rw [div_self (pow_ne_zero _ hζ)]
    simp [Algebra.smul_def]
  · intro i hi hik
    have hne : ζ ^ i / ζ ^ k ≠ 1 := by
      intro h0
      rw [div_eq_one_iff_eq (pow_ne_zero _ hζ)] at h0
      exact hik (h.root.pow_inj (Finset.mem_range.1 hi) hk h0)
    have hp : (ζ ^ i / ζ ^ k) ^ p = 1 := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm k, pow_mul, pow_mul,
        h.root.pow_eq_one, one_pow, one_pow, div_one]
    rw [geom_sum_eq hne, hp, sub_self, zero_div, zero_smul]
  · intro h0
    exact absurd (Finset.mem_range.2 hk) h0

theorem exists_uniformizer_lt_one (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (T : Finset (HeightOneSpectrum (𝓞 E))) (hw : w ∈ T) :
    ∃ y : E, w.valuation E y = WithZero.exp (-1) ∧ ∀ w' ∈ T, w'.valuation E y < 1 := by
  classical
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) (fun _ => 2) (fun v _ => v.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun v => if v.1 = w then π else 0)
  have h1 : w.intValuation y = WithZero.exp (-1) := by
    have h2 := hy w hw
    simp only [if_true] at h2
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem] at h2
    have h3 : w.intValuation (y - π) < w.intValuation π := by
      rw [hπ]
      exact h2.trans_lt (WithZero.exp_lt_exp.2 (by norm_num))
    have := w.intValuation.map_add_eq_of_lt_right h3
    rwa [sub_add_cancel, hπ] at this
  refine ⟨(y : E), by rw [HeightOneSpectrum.valuation_of_algebraMap, h1], fun w' hw' => ?_⟩
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  by_cases hww : w' = w
  · rw [hww, h1, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.2 (by norm_num)
  · have h2 := hy w' hw'
    simp only [if_neg hww, sub_zero] at h2
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem] at h2
    rw [← WithZero.exp_zero]
    exact h2.trans_lt (WithZero.exp_lt_exp.2 (by norm_num))

theorem kummer_valuation_unramified : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 F)).valuation F (p : F) = 1 → (w.under (𝓞 F)).valuation F δ = 1 → ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x := by
  intro p F E _ _ _ _ _ ζ δ θ σ h w hp hδ
  obtain ⟨e, he, hw⟩ := (places_over F E).2.2 w
  obtain ⟨-, -, hgal, -⟩ := kummer_galois p F E ζ δ θ σ h
  have hp0 := h.prime.ne_zero
  obtain ⟨y, hy1, hy2⟩ := exists_uniformizer_lt_one E w
    (finite_places_over F E (w.under (𝓞 F))).toFinset (by simp)
  have hconj : ∀ τ : E ≃ₐ[F] E, w.valuation E (τ y) < 1 := by
    intro τ
    obtain ⟨w', h1, h2⟩ := (galois_places_transitive F E).1 τ w
    rw [← h2]
    exact hy2 w' (by simpa using h1)
  have hint : IsIntegral F θ :=
    ⟨X ^ p - C δ, monic_X_pow_sub_C δ hp0, by simp [h.pow]⟩
  let pb : PowerBasis F E := PowerBasis.ofAdjoinEqTop hint h.gen
  have hgen : pb.gen = θ := PowerBasis.ofAdjoinEqTop_gen hint h.gen
  have hdim : pb.dim = p := by
    rw [← pb.natDegree_minpoly, hgen, h.minpoly_eq, natDegree_X_pow_sub_C _]
  obtain ⟨f, hf, hyf⟩ := pb.exists_eq_aeval y
  rw [hdim] at hf
  rw [hgen, Polynomial.aeval_eq_sum_range' hf] at hyf
  have hpE : w.valuation E (p : E) = 1 := by
    have := hw (p : F)
    rwa [map_natCast, hp, one_pow] at this
  have hθ : w.valuation E θ = 1 := by
    have := hw δ
    rw [hδ, one_pow, ← h.pow, map_pow] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hp0).1 this
  have hζ : w.valuation E (algebraMap F E ζ) = 1 := by
    have : w.valuation E (algebraMap F E ζ) ^ p = 1 := by
      rw [← map_pow, ← map_pow, h.root.pow_eq_one, map_one, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le hp0).1 this
  have hco : ∀ k ∈ Finset.range p,
      w.valuation E (f.coeff k • θ ^ k) ≤ WithZero.exp (-1 : ℤ) ^ e := by
    intro k hk
    have h1 := h.sum_conj_eq f.coeff k (Finset.mem_range.1 hk)
    rw [← hyf] at h1
    have h2 : w.valuation E ((p : E) * (f.coeff k • θ ^ k)) < 1 := by
      rw [← h1]
      refine (w.valuation E).map_sum_lt one_ne_zero fun j _ => ?_
      rw [map_mul, map_pow, map_inv₀, map_pow, map_pow, map_inv₀, map_pow, hζ]
      simpa using hconj (σ ^ j)
    rw [map_mul, hpE, one_mul] at h2
    rw [Algebra.smul_def, map_mul, map_pow, hθ, one_pow, mul_one, hw] at h2 ⊢
    have h3 : (w.under (𝓞 F)).valuation F (f.coeff k) < 1 := by
      by_contra h4
      exact absurd h2 (not_lt.2 (one_le_pow₀ (not_lt.1 h4)))
    have h5 : (w.under (𝓞 F)).valuation F (f.coeff k) ≤ WithZero.exp (-1 : ℤ) := by
      rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
      simpa using h3
    exact pow_le_pow_left₀ zero_le h5 e
  have h6 : w.valuation E y ≤ WithZero.exp (-1 : ℤ) ^ e := by
    rw [hyf]
    exact (w.valuation E).map_sum_le hco
  rw [hy1, ← WithZero.exp_nsmul, WithZero.exp_le_exp, nsmul_eq_mul] at h6
  have h7 : e = 1 := by omega
  intro x
  rw [hw, h7, pow_one]

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ValuationUnramifiedKummerOfCoprimeUnitStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.valuation_unramified_kummer_of_coprime_unit : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 F)).valuation F (p : F) = 1 → (w.under (𝓞 F)).valuation F δ = 1 → ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x := by
  first | exact @GlobalTheory.CNorm.kummer_valuation_unramified | exact GlobalTheory.CNorm.kummer_valuation_unramified | (intros; apply GlobalTheory.CNorm.kummer_valuation_unramified <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90SUnitsKummer

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem hilbert90_sUnits_kummer : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → AdmP p F S → (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ sUnits E SE → ∏ i ∈ Finset.range p, σ^[i] (u : E) = 1 → ∃ y : Eˣ, y ∈ sUnits E SE ∧ (u : E) = σ y / y := by
  classical
  intro p F E _ _ _ _ _ ζ δ θ σ hq S SE hSE hadm hδ u hu hN
  obtain ⟨hfd, -, hgal, -, hgen, -⟩ := kummer_galois p F E ζ δ θ σ hq
  obtain ⟨y, hy0, hy⟩ := (GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p F E ζ δ θ σ hq).2.2.2.2.1 (u : E) hN
  obtain ⟨hact, htrans⟩ := galois_places_transitive F E
  rw [mem_sUnits] at hu
  have hval : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE → w.valuation E (σ y) = w.valuation E y := by
    intro w hw
    have h1 := hu w hw
    rw [hy, map_div₀, div_eq_one_iff_eq (by simpa only [ne_eq, map_eq_zero] using hy0)] at h1
    exact h1
  have hpow : ∀ (k : ℕ) (w : HeightOneSpectrum (𝓞 E)), w ∉ SE →
      w.valuation E ((σ ^ k) y) = w.valuation E y := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      obtain ⟨w', hw', hv'⟩ := hact (σ ^ k) w
      have hw'' : w' ∉ SE := fun h => hw ((hSE w).2 (hw' ▸ (hSE w').1 h))
      rw [pow_succ, AlgEquiv.mul_apply, ← hv', hval w' hw'', hv', ih]
  have hall : ∀ (τ : E ≃ₐ[F] E) (w : HeightOneSpectrum (𝓞 E)), w ∉ SE →
      w.valuation E (τ y) = w.valuation E y := by
    intro τ w hw
    obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.2 (hgen τ)
    exact hpow k w hw
  choose up hup using (places_over F E).2.1
  obtain ⟨T, -, hT⟩ := exists_superset_mem_sUnits E {Units.mk0 y hy0} ∅
  have hT' := (mem_sUnits E T _).1 (hT T subset_rfl _ (Finset.mem_singleton_self _))
  obtain ⟨a, ha⟩ := exists_unit_valuation_eq_of_adm F S (T.image fun w => w.under (𝓞 F))
    (fun v => -WithZero.log ((up v).valuation E y)) hadm.1 (by
      intro v hv
      have : up v ∉ T := fun h => hv (Finset.mem_image.2 ⟨_, h, hup v⟩)
      have h2 : (up v).valuation E y = 1 := hT' _ this
      simp [h2])
  have ha0 : algebraMap F E (a : F) ≠ 0 := by simp
  refine ⟨Units.mk0 (algebraMap F E a * y) (mul_ne_zero ha0 hy0), ?_, ?_⟩
  · rw [mem_sUnits]
    intro w hw
    have hv : w.under (𝓞 F) ∉ S := fun h => hw ((hSE w).2 h)
    have h3 : (up (w.under (𝓞 F))).valuation E y = w.valuation E y := by
      obtain ⟨τ, hτ⟩ := htrans w (up (w.under (𝓞 F))) (hup _)
      rw [hτ, hall τ w hw]
    have h4 : w.valuation E y ≠ 0 := by simpa only [ne_eq, map_eq_zero] using hy0
    rw [Units.val_mk0, map_mul,
      GlobalTheory.T.valuation_unramified_kummer_of_coprime_unit p F E ζ δ θ σ hq w (hadm.2 _ hv) (hδ _ hv), ha _ hv]
    simp only [h3]
    rw [WithZero.exp_neg, WithZero.exp_log h4, inv_mul_cancel₀ h4]
  · rw [Units.val_mk0, map_mul, AlgEquiv.commutes, hy, mul_div_mul_left _ _ ha0]

end GlobalTheory.CNorm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Hilbert90SUnitsKummerStatement

section

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.hilbert90_sUnits_kummer' : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))), (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → AdmP p F S → (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ sUnits E SE → ∏ i ∈ Finset.range p, σ^[i] (u : E) = 1 → ∃ y : Eˣ, y ∈ sUnits E SE ∧ (u : E) = σ y / y := by
  first | exact @GlobalTheory.CNorm.hilbert90_sUnits_kummer | exact GlobalTheory.CNorm.hilbert90_sUnits_kummer | (intros; apply GlobalTheory.CNorm.hilbert90_sUnits_kummer <;> assumption)
end
end
