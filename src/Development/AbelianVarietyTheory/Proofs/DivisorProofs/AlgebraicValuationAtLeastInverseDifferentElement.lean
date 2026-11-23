module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.Different
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.DefiningCoordinates
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealPowFinrankEqSpanDiscr

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.GalDiff

open scoped Pointwise

variable (E : Type) [Field E] [NumberField E]

theorem mem_differentIdeal_iff_one (x : 𝓞 E) :
    x ∈ differentIdeal ℤ (𝓞 E) ↔
      ∀ y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E), (x : E) * y ∈ (1 : Submodule (𝓞 E) E) := by
  rw [← Submodule.mem_div_iff_forall_mul_mem, ← coeSubmodule_differentIdeal ℤ ℚ (L := E) (𝓞 E),
    IsLocalization.mem_coeSubmodule]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, h⟩
    have : y = x := FaithfulSMul.algebraMap_injective (𝓞 E) E h
    exact this ▸ hy

theorem galois_smul_mem_differentIdeal (σ : E ≃ₐ[ℚ] E) {x : 𝓞 E}
    (hx : x ∈ differentIdeal ℤ (𝓞 E)) : σ • x ∈ differentIdeal ℤ (𝓞 E) := by
  have hone : ∀ (τ : E ≃ₐ[ℚ] E) (a : E), a ∈ (1 : Submodule (𝓞 E) E) →
      τ a ∈ (1 : Submodule (𝓞 E) E) := by
    intro τ a ha
    rw [Submodule.mem_one] at ha ⊢
    obtain ⟨b, rfl⟩ := ha
    exact ⟨τ • b, rfl⟩
  rw [mem_differentIdeal_iff_one] at hx ⊢
  intro y hy
  have hy' : σ.symm y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual] at hy ⊢
    intro a ha
    have := hy (σ a) (hone σ a ha)
    rw [Algebra.traceForm_apply] at this ⊢
    rw [← Algebra.trace_eq_of_algEquiv σ, map_mul, AlgEquiv.apply_symm_apply]
    exact this
  have := hone σ _ (hx _ hy')
  rw [map_mul, AlgEquiv.apply_symm_apply] at this
  exact this

theorem differentIdeal_pow_finrank_eq_span_discr :
    ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F],
      differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by
  intro E _ _ _
  classical
  have hmap : Ideal.span {((discr E : ℤ) : 𝓞 E)} = (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) := by
    rw [Ideal.map_span, Set.image_singleton, eq_intCast]
  rw [hmap]
  set D := differentIdeal ℤ (𝓞 E) with hD
  have hN : Ideal.absNorm D = (discr E).natAbs := absNorm_differentIdeal E (𝓞 E)
  have hrel : Ideal.relNorm ℤ D = Ideal.span {discr E} := by
    rw [Ideal.relNorm_int, hN, Ideal.span_singleton_eq_span_singleton]
    exact (Int.associated_natAbs _).symm
  have hle : (Ideal.span {discr E}).map (algebraMap ℤ (𝓞 E)) ≤ D ^ Module.finrank ℚ E := by
    rw [← hrel, Ideal.map_le_iff_le_comap, Ideal.relNorm_apply, Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have h1 : algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) = ∏ σ : E ≃ₐ[ℚ] E, σ • x := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ ℚ E,
        Algebra.algebraMap_intNorm (L := E), Algebra.norm_eq_prod_automorphisms, map_prod]
      rfl
    change algebraMap ℤ (𝓞 E) (Algebra.intNorm ℤ (𝓞 E) x) ∈ D ^ Module.finrank ℚ E
    rw [h1, ← IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, ← Finset.card_univ,
      ← Finset.prod_const]
    exact Ideal.prod_mem_prod fun σ _ => galois_smul_mem_differentIdeal E σ hx
  obtain ⟨L, hL⟩ := Ideal.dvd_iff_le.mpr hle
  have h2 := congrArg Ideal.absNorm hL
  rw [Ideal.absNorm_algebraMap, map_mul, map_pow, hN, RingOfIntegers.rank,
    Ideal.absNorm_span_singleton, Algebra.norm_self] at h2
  have h0 : (discr E).natAbs ^ Module.finrank ℚ E ≠ 0 :=
    pow_ne_zero _ (Int.natAbs_ne_zero.mpr (discr_ne_zero E))
  have h3 : Ideal.absNorm L = 1 := by
    apply mul_left_cancel₀ h0
    rw [mul_one]
    exact h2.symm
  rw [hL, Ideal.absNorm_eq_one_iff.mp h3, Ideal.mul_top]

end GlobalTheory.GalDiff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentIdealPowFinrankEqSpanDiscrStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.differentIdeal_pow_finrank_eq_span_discr' : ∀ (F : Type) [Field F] [NumberField F] [IsGalois ℚ F], differentIdeal ℤ (𝓞 F) ^ Module.finrank ℚ F = Ideal.span {((discr F : ℤ) : 𝓞 F)} := by
  first | exact @GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | exact GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr | (intros; apply GlobalTheory.GalDiff.differentIdeal_pow_finrank_eq_span_discr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastInverseDifferentElement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

noncomputable section

namespace GlobalTheory.DiffSize

theorem norm_le_one_of_isIntegral {p : ℕ} [Fact p.Prime] {x : ℂ_[p]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[p])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[p]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_intCast (p : ℕ) [Fact p.Prime] (m : ℤ) (hm : m ≠ 0) :
    ‖((m : ℤ) : ℂ_[p])‖ = (p : ℝ) ^ (-(padicValInt p m : ℤ)) := by
  have e : ((m : ℤ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((m : ℚ) : ℚ_[p]) := by
    rw [Rat.cast_intCast, map_intCast]
  rw [e]
  refine (PadicComplex.norm_extends' (p := p) _).trans ?_
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hm),
    padicValRat.of_int]
  push_cast; rfl

theorem pow_mem {K : Type} [Field K] [NumberField K] {I : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ I) (k : ℕ) :
    x ^ k ∈ I ^ k := by
  induction k with
  | zero => simpa using FractionalIdeal.one_mem_one (R := 𝓞 K) (K := K)
  | succ k ih => rw [pow_succ, pow_succ]; exact FractionalIdeal.mul_mem_mul ih hx

theorem exists_int_mul_pow {F : Type} [Field F] [NumberField F] [IsGalois ℚ F] {y : F}
    (hy : y ∈ latM (1 : Frac F)) : ∃ c : 𝓞 F, (c : F) = (discr F : F) * y ^ Module.finrank ℚ F := by
  have hd : (discr F : F) ≠ 0 := by exact_mod_cast discr_ne_zero F
  have h1 : latM (1 : Frac F) = ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F)⁻¹ := by
    simp [latM]
  rw [h1] at hy
  have h2 := pow_mem hy (Module.finrank ℚ F)
  rw [inv_pow, ← FractionalIdeal.coeIdeal_pow, GlobalTheory.T.differentIdeal_pow_finrank_eq_span_discr' F, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.spanSingleton_inv] at h2
  obtain ⟨c, hc⟩ := (FractionalIdeal.mem_spanSingleton _).1 h2
  refine ⟨c, ?_⟩
  rw [Algebra.smul_def, map_intCast] at hc
  rw [← hc]; field_simp

theorem sz_invDiff : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] [IsGalois ℚ F] (y : F) (i : Emb F), y ∈ latM (1 : Frac F) → Sz l lam ((padicValInt l (discr F) : ℝ) / Module.finrank ℚ F) ((i y : ℝ) : ℂ) := by
  intro l _ lam F _ _ _ _ y i hy
  obtain ⟨c, hc⟩ := exists_int_mul_pow hy
  let φ : F →+* ℂ := Complex.ofRealHom.comp i
  have hmem : ∀ x : F, φ x ∈ algebraicClosure ℚ ℂ := fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic x).algHom φ.toRatAlgHom
  let ψ : F →+* algebraicClosure ℚ ℂ := φ.codRestrict (algebraicClosure ℚ ℂ) hmem
  let χ : F →+* ℂ_[l] := lam.comp ψ
  refine ⟨hmem y, ?_⟩
  change ‖χ y‖ ≤ _
  have hd0 : discr F ≠ 0 := discr_ne_zero F
  have hcint : ‖χ (c : F)‖ ≤ 1 :=
    norm_le_one_of_isIntegral (by convert map_isIntegral_int χ (RingOfIntegers.isIntegral_coe c); exact Subsingleton.elim _ _)
  have hdn : ‖χ (discr F : F)‖ = (l : ℝ) ^ (-(padicValInt l (discr F) : ℤ)) := by
    rw [map_intCast]; exact norm_intCast l _ hd0
  set n := Module.finrank ℚ F
  set v := padicValInt l (discr F)
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hkey : ‖χ y‖ ^ n * (l : ℝ) ^ (-(v : ℤ)) ≤ 1 := by
    rw [← hdn, ← norm_pow, ← norm_mul, ← map_pow, ← map_mul, mul_comm, ← hc]; exact hcint
  have hpow : ‖χ y‖ ^ n ≤ (l : ℝ) ^ (v : ℝ) := by
    have hpos : (0 : ℝ) < (l : ℝ) ^ (-(v : ℤ)) := zpow_pos hl0 _
    have := (le_div_iff₀ hpos).2 hkey
    rw [one_div, ← zpow_neg, neg_neg, zpow_natCast] at this
    rwa [Real.rpow_natCast]
  have hn : 0 < n := Module.finrank_pos
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  calc ‖χ y‖ = (‖χ y‖ ^ n) ^ ((n : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast (norm_nonneg _) hn.ne').symm
    _ ≤ ((l : ℝ) ^ (v : ℝ)) ^ ((n : ℝ)⁻¹) := Real.rpow_le_rpow (by positivity) hpow (by positivity)
    _ = (l : ℝ) ^ ((v : ℝ) / n) := by rw [← Real.rpow_mul hl0.le, div_eq_mul_inv]

end GlobalTheory.DiffSize
end
end
end
