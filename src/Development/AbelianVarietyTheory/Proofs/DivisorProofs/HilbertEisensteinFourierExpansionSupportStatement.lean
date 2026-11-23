module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
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
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumNatCastEq

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors
open GlobalTheory.LatVal GlobalTheory.LatJet

namespace GlobalTheory.PairFourier

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem tsum_natCast_eq {ι : Type} (n : ι → ℕ) (h : Summable (fun i ↦ (n i : ℂ))) :
    ∃ m : ℕ, ∑' i, (n i : ℂ) = m := by
  have hfin : (Function.support n).Finite := by
    have ht := h.tendsto_cofinite_zero
    have hev : ∀ᶠ i in Filter.cofinite, ‖(n i : ℂ)‖ < 1 := by
      have := ht.norm
      simp only [norm_zero] at this
      exact this.eventually (gt_mem_nhds (by norm_num))
    refine (Filter.eventually_cofinite.1 hev).subset ?_
    intro i hi
    simp only [Function.mem_support] at hi
    simp only [Set.mem_setOf_eq, not_lt]
    have : (1 : ℝ) ≤ n i := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hi
    simpa [Complex.norm_natCast] using this
  refine ⟨∑ i ∈ hfin.toFinset, n i, ?_⟩
  rw [tsum_eq_sum (s := hfin.toFinset)]
  · push_cast; rfl
  · intro i hi
    simp only [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hi
    simp [hi]

variable {F : Type} [Field F] [NumberField F]

theorem norm_div_eq_nat (𝔞 : Frac F) {ν : F} (hν : ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)) :
    ∃ m : ℕ, |((Algebra.norm ℚ ν : ℚ) : ℝ)| / nrm 𝔞 = m := by
  set J : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.spanSingleton (𝓞 F)⁰ ν * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) with hJdef
  have hle : J ≤ 1 := by
    have h1 : FractionalIdeal.spanSingleton (𝓞 F)⁰ ν ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) :=
      FractionalIdeal.spanSingleton_le_iff_mem.2 hν
    calc J ≤ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) * ((𝔞⁻¹ : Frac F) : FractionalIdeal (𝓞 F)⁰ F) :=
          mul_le_mul_left h1 _
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hJa : J * (𝔞 : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ ν := by
    rw [hJdef, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  have hn := congrArg FractionalIdeal.absNorm hJa
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, ← hI, FractionalIdeal.coeIdeal_absNorm] at hn
  have h0 : (FractionalIdeal.absNorm (𝔞 : FractionalIdeal (𝓞 F)⁰ F) : ℚ) ≠ 0 := by
    rw [Ne, FractionalIdeal.absNorm_eq_zero_iff]
    exact Units.ne_zero 𝔞
  refine ⟨Ideal.absNorm I, ?_⟩
  unfold nrm
  rw [div_eq_iff (by exact_mod_cast h0)]
  have := congrArg (fun q : ℚ ↦ (q : ℝ)) hn
  simp only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_abs] at this
  rw [← this]

variable [IsTotallyReal F]

def pairPt (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : GlobalTheory.RealMult.FracId.elt (𝔞 * 𝔟) :=
  ⟨c.out.1.1 * c.out.1.2, by
    show _ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F)
    rw [Units.val_mul]
    exact FractionalIdeal.mul_mem_mul c.out.2.1 c.out.2.2.1⟩

def pairCoef (𝔞 𝔟 : Frac F) (k : ℕ) (c : Quotient (qRel 𝔞 𝔟)) : ℕ :=
  (norm_div_eq_nat 𝔞 c.out.2.1).choose ^ (k - 1)

theorem qClass_eq (𝔞 𝔟 : Frac F) (k : ℕ) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) :
    qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * GlobalTheory.RealMult.qPower ((pairPt 𝔞 𝔟 c : F)) z := by
  unfold qClass qTerm pairCoef pairPt
  have hs := (norm_div_eq_nat 𝔞 c.out.2.1).choose_spec
  generalize (norm_div_eq_nat 𝔞 c.out.2.1).choose = m at hs ⊢
  rw [hs]
  push_cast
  rfl

theorem pairPt_ne_zero (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) : pairPt 𝔞 𝔟 c ≠ 0 := by
  intro h
  have h' : c.out.1.1 * c.out.1.2 = 0 := congrArg Subtype.val h
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have hr : NumberField.ComplexEmbedding.IsReal φ := IsTotallyReal.complexEmbedding_isReal φ
  have := c.out.2.2.2 hr.embedding
  rw [h', map_zero] at this
  exact lt_irrefl _ this

end GlobalTheory.PairFourier
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinFourierExpansionSupport

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion qClass qRel)
open GlobalTheory.PairFourier (pairPt pairCoef qClass_eq tsum_natCast_eq pairPt_ne_zero)

namespace GlobalTheory.HilbFam

theorem fourier_with_support :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ),
      HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧
        a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ (∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n) ∧
        (∀ ξ, ξ ≠ 0 → a ξ ≠ 0 → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : Emb F, 0 < i ξ) ∧
        ∀ w ∈ upperHalf F, HasSum (fun ξ : F ↦ a ξ * qPow ξ w)
          ((cK F k : ℂ) * G w / (omegaFactor 𝔞 : ℂ) ^ k) := by
  classical
  intro F _ _ _ k 𝔞 𝔟 G hG
  obtain ⟨Z, hZ, hE⟩ := hG
  set C : ℂ := (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) with hC
  let p : Quotient (qRel 𝔞 𝔟) → F := fun c ↦ (pairPt 𝔞 𝔟 c : F)
  let a' : F → ℂ := fun ξ ↦ ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ)
  have ha' : ∀ ξ, a' ξ = ∑' c : p ⁻¹' {ξ}, (pairCoef 𝔞 𝔟 k c : ℂ) := fun _ ↦ rfl
  have hfib : ∀ (z : Emb F → ℂ) (ξ : F) (c : p ⁻¹' {ξ}),
      qClass 𝔞 𝔟 k z c = (pairCoef 𝔞 𝔟 k c : ℂ) * qPow ξ z := by
    rintro z ξ ⟨c, hc⟩
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc
    subst hc
    exact qClass_eq 𝔞 𝔟 k z c
  refine ⟨Z, fun ξ ↦ a' ξ + if ξ = 0 then C else 0, hZ, ?_, ?_, ?_, ?_⟩
  · show a' 0 + (if (0 : F) = 0 then C else 0) = C
    rw [if_pos rfl]
    have : IsEmpty (p ⁻¹' {0}) :=
      ⟨fun ⟨c, hc⟩ ↦ pairPt_ne_zero 𝔞 𝔟 c
        (Subtype.ext (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hc)))⟩
    rw [ha']
    simp only [tsum_empty, zero_add]
  · intro ξ hξ
    set z₀ : Emb F → ℂ := fun _ ↦ Complex.I
    have hz₀ : z₀ ∈ upperHalf F := fun _ ↦ by simp [z₀]
    have hq : qPow ξ z₀ ≠ 0 := Complex.exp_ne_zero _
    have hsum : Summable (fun c : p ⁻¹' {ξ} ↦ (pairCoef 𝔞 𝔟 k c : ℂ)) := by
      have := ((hE z₀ hz₀).1.subtype (fun c ↦ c ∈ p ⁻¹' {ξ})).mul_right (qPow ξ z₀)⁻¹
      refine this.congr fun c ↦ ?_
      simp only [Function.comp_apply]
      rw [hfib z₀ ξ c, mul_assoc, mul_inv_cancel₀ hq, mul_one]
    obtain ⟨m, hm⟩ := tsum_natCast_eq _ hsum
    refine ⟨m, ?_⟩
    show a' ξ + (if ξ = 0 then C else 0) = _
    rw [if_neg hξ, add_zero, ha']
    simp only [hm]
    simp
  · intro ξ hξ hne
    have hne' : a' ξ ≠ 0 := by
      intro h
      apply hne
      show a' ξ + (if ξ = 0 then C else 0) = 0
      rw [if_neg hξ, h, add_zero]
    by_cases hem : IsEmpty (p ⁻¹' {ξ})
    · exact absurd (by rw [ha']; exact tsum_empty) hne'
    obtain ⟨c, hc⟩ := not_isEmpty_iff.1 hem
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hc
    subst hc
    exact ⟨(pairPt 𝔞 𝔟 c).2, c.out.2.2.2⟩
  · intro z hz
    obtain ⟨hs, heq⟩ := hE z hz
    have h1 := hs.hasSum.tsum_fiberwise p
    have h2 : (fun ξ ↦ ∑' c : p ⁻¹' {ξ}, qClass 𝔞 𝔟 k z c) = fun ξ ↦ a' ξ * qPow ξ z := by
      funext ξ
      rw [ha', ← tsum_mul_right]
      exact tsum_congr (hfib z ξ)
    rw [h2] at h1
    have h3 : HasSum (fun ξ : F ↦ (if ξ = 0 then C else 0) * qPow ξ z) C := by
      convert hasSum_ite_eq (0 : F) C using 1
      funext ξ
      split_ifs with h
      · subst h; simp [qPow]
      · simp
    have hv : (cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k =
        (∑' c, qClass 𝔞 𝔟 k z c) + C := by rw [heq]; ring
    show HasSum (fun ξ : F ↦ (a' ξ + if ξ = 0 then C else 0) * qPow ξ z)
      ((cK F k : ℂ) * G z / (omegaFactor 𝔞 : ℂ) ^ k)
    rw [hv]
    simp only [add_mul]
    exact h1.add h3

end GlobalTheory.HilbFam
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinFourierExpansionSupportStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

theorem _root_.GlobalTheory.T.hilbertEisenstein_fourier_expansion_support : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (G : (Emb F → ℂ) → ℂ), HasExpansion 𝔞 𝔟 k G → ∃ (Z : ℂ → ℂ) (a : F → ℂ), IsPartialZeta (ClassGroup.mk F 𝔞)⁻¹ Z ∧ a 0 = (2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - (k : ℂ)) ∧ (∀ ξ, ξ ≠ 0 → ∃ n : ℤ, a ξ = n) ∧ (∀ ξ, ξ ≠ 0 → a ξ ≠ 0 → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) ∧ ∀ i : Emb F, 0 < i ξ) ∧ ∀ w ∈ upperHalf F, HasSum (fun ξ : F ↦ a ξ * qPow ξ w) ((cK F k : ℂ) * G w / (omegaFactor 𝔞 : ℂ) ^ k) := by
  first | exact @GlobalTheory.HilbFam.fourier_with_support | exact GlobalTheory.HilbFam.fourier_with_support | (intros; apply GlobalTheory.HilbFam.fourier_with_support <;> assumption)
end
end
