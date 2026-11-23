module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFactorPowTwoMul
import Mathlib.Tactic.Lemma

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLatticeLevelTraceDenominator

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem exists_int_mul_trace_of_hasLevel {F : Type} [Field F] [NumberField F] {N : ℕ} {𝔞 𝔟 : Frac F} {x : F}
    (h : HasLevel N (split 𝔞 𝔟 x)) {ν c : F} (hν : ν ∈ (𝔞 : FractionalIdeal (𝓞 F)⁰ F))
    (hc : c ∈ (1 : Submodule (𝓞 F) F)) : ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ν * c) = n := by
  have h1 : (![0, c] : Fin 2 → F) ∈ stdLat F := by
    intro i _
    fin_cases i
    · exact Submodule.zero_mem _
    · exact hc
  have h2 := (h.1 _ h1).2
  have h3 : ((N : 𝓞 F) • (![0, c] : Fin 2 → F)) 1 - ((N : 𝓞 F) • (![0, c] : Fin 2 → F)) 0 * x = (N : F) * c := by
    simp [Algebra.smul_def]
  rw [h3, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual, FractionalIdeal.mem_dual 𝔞.ne_zero] at h2
  obtain ⟨n, hn⟩ := h2 ν hν
  refine ⟨n, ?_⟩
  have h4 : (N : F) * c * ν = (N : ℚ) • (ν * c) := by
    rw [Algebra.smul_def, map_natCast]; ring
  rw [Algebra.traceForm_apply, h4, map_smul, smul_eq_mul] at hn
  simpa using hn.symm

theorem trace_denominator_of_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x ξ : F), HasLevel N (split 𝔞 𝔟 x) → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧ ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n := by
  intro F _ _ _ N 𝔞 𝔟 x ξ h hξ
  rw [Units.val_mul] at hξ
  refine FractionalIdeal.mul_induction_on hξ (C := fun ξ ↦ (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧
    ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n) ?_ ?_
  · intro ν hν β hβ
    have h1 : (![β, β * x] : Fin 2 → F) ∈ split 𝔞 𝔟 x := by
      refine ⟨hβ, ?_⟩
      have : (![β, β * x] : Fin 2 → F) 1 - (![β, β * x] : Fin 2 → F) 0 * x = 0 := by simp
      rw [this]
      exact Submodule.zero_mem (latM 𝔞 : Submodule (𝓞 F) F)
    have h2 := h.2 h1
    refine ⟨exists_int_mul_trace_of_hasLevel h hν (h2 0 trivial), ?_⟩
    rw [mul_assoc]
    exact exists_int_mul_trace_of_hasLevel h hν (h2 1 trivial)
  · rintro a b ⟨⟨m, hm⟩, m', hm'⟩ ⟨⟨n, hn⟩, n', hn'⟩
    refine ⟨⟨m + n, ?_⟩, m' + n', ?_⟩
    · rw [map_add (f := _), mul_add, hm, hn]; push_cast; ring
    · rw [add_mul, map_add (f := _), mul_add, hm', hn']; push_cast; ring

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLatticeLevelTraceDenominatorStatement

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

theorem _root_.GlobalTheory.T.splitLattice_level_trace_denominator : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x ξ : F), HasLevel N (split 𝔞 𝔟 x) → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧ ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n := by
  first | exact @GlobalTheory.HilbFam.trace_denominator_of_hasLevel | exact GlobalTheory.HilbFam.trace_denominator_of_hasLevel | (intros; apply GlobalTheory.HilbFam.trace_denominator_of_hasLevel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinFourierCoeffRingEquivConj

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem ecoef_ringEquiv : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (Emb F)) (μ : Emb F → ℕ) (n : ℕ), 0 < N → IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → HasLevel N (split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (ecoef N a x μ n) = ecoef N a (m * x) (fun j ↦ μ (π.symm j)) n := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x N g m π μ n hN hco hg0 hlev hζ hemb
  obtain ⟨h0, hint, hsupp, -⟩ := hco
  have hmap : ∀ {ι : Sort _} (f : ι → ℂ), g (∑ᶠ i, f i) = ∑ᶠ i, g (f i) :=
    fun f ↦ AddEquiv.map_finsum g.toAddEquiv f
  have hmapP : ∀ {p : Prop} (f : p → ℂ), g (∑ᶠ i, f i) = ∑ᶠ i, g (f i) :=
    fun f ↦ AddEquiv.map_finsum g.toAddEquiv f
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'

  have hprod : ∀ ξ : F, g (∏ i : Emb F, ((i ξ : ℝ) : ℂ) ^ μ i) = ∏ j : Emb F, ((j ξ : ℝ) : ℂ) ^ μ (π.symm j) := by
    intro ξ
    rw [map_prod]
    simp only [map_pow, hemb]
    exact Equiv.prod_comp π (fun j ↦ ((j ξ : ℝ) : ℂ) ^ μ (π.symm j)) |>.symm ▸ by
      simp only [Equiv.symm_apply_apply]

  have hchar : ∀ ξ : F, ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → g (eTr (ξ * x)) = eTr (ξ * ((m : F) * x)) := by
    intro ξ hξ
    obtain ⟨r, hr⟩ := (GlobalTheory.T.splitLattice_level_trace_denominator F N 𝔞 𝔟 x ξ hlev hξ).2
    have ht : Algebra.trace ℚ F (ξ * x) = (r : ℚ) / N := by
      rw [eq_div_iff hNq, mul_comm]; exact hr
    have hsm : ξ * ((m : F) * x) = (m : ℚ) • (ξ * x) := by
      rw [Algebra.smul_def, map_intCast]; ring
    have ht' : Algebra.trace ℚ F (ξ * ((m : F) * x)) = (m : ℚ) * ((r : ℚ) / N) := by
      rw [hsm, LinearMap.map_smul, smul_eq_mul, ht]
    have e1 : eTr (ξ * x) = Complex.exp ((2 * Real.pi * Complex.I) / N) ^ r := by
      rw [eTr, ht, ← Complex.exp_int_mul]; congr 1; push_cast; ring
    rw [e1, map_zpow₀, hζ, ← Complex.exp_int_mul, eTr, ht']
    congr 1; push_cast; ring
  have key : ∀ ξ : F, g (a ξ * eTr (ξ * x) * ∏ i : Emb F, ((i ξ : ℝ) : ℂ) ^ μ i) =
      a ξ * eTr (ξ * ((m : F) * x)) * ∏ j : Emb F, ((j ξ : ℝ) : ℂ) ^ μ (π.symm j) := by
    intro ξ
    by_cases ha : a ξ = 0
    · simp [ha]
    have hga : g (a ξ) = a ξ := by
      by_cases hξ0 : ξ = 0
      · subst hξ0; rw [h0]; exact hg0
      · obtain ⟨z, hz⟩ := hint ξ hξ0; rw [hz, map_intCast]
    have hmem : ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
      by_cases hξ0 : ξ = 0
      · subst hξ0; exact Submodule.zero_mem _
      · exact (hsupp ξ hξ0 ha).1
    rw [map_mul, map_mul, hga, hchar ξ hmem, hprod]
  unfold ecoef
  rw [hmap]
  refine finsum_congr fun ξ ↦ ?_
  rw [hmapP]
  refine finsum_congr fun _ ↦ ?_
  exact key ξ

end GlobalTheory.HilbFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesRingEquivConj

section

@[expose] public section

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma powerSeries_map_mk' (g : ℂ ≃+* ℂ) (c : ℕ → ℂ) :
    PowerSeries.map (g : ℂ →+* ℂ) (PowerSeries.mk c) = PowerSeries.mk fun n ↦ g (c n) := by
  ext n
  simp

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hser_conj : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F)) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → 0 < N → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) = PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a (m * x) (fun j ↦ κ (π.symm j)) (fun n ↦ g (c n))) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x s N g m π κ c n hk hN ha hga hlev hexp hemb
  have htr : ∀ μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ,
      PowerSeries.map (g : ℂ →+* ℂ) (PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ)) =
        PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a (m * x) fun j ↦ μ (π.symm j)) := by
    intro μ
    rw [powerSeries_map_mk']
    congr 1
    funext j
    exact _root_.GlobalTheory.HilbFam.ecoef_ringEquiv F k 𝔞 𝔟 a₀ a x N g m π μ j hN ha hga hlev
      hexp hemb
  unfold _root_.GlobalTheory.HilbFam.hser
  subst hk

  simp only [map_smul, map_sum, smul_eq_mul, _root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]

  rw [map_mul, map_ratCast, map_sum]
  congr 1
  refine Finset.sum_nbij' (fun μ j ↦ μ (π.symm j)) (fun μ i ↦ μ (π i)) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [Finset.mem_coe, Finset.mem_Iic] at hμ ⊢
    exact fun j ↦ hμ (π.symm j)
  · intro μ hμ
    simp only [Finset.mem_coe, Finset.mem_Iic] at hμ ⊢
    intro i
    simpa using hμ (π i)
  · intro μ _
    funext i
    simp
  · intro μ _
    funext j
    simp
  · intro μ _
    have hcoeff : ∀ φ : PowerSeries ℂ,
        g (PowerSeries.coeff n φ) = PowerSeries.coeff n (PowerSeries.map (g : ℂ →+* ℂ) φ) :=
      fun φ ↦ by
        rw [PowerSeries.coeff_map]
        rfl
    rw [map_mul, map_intCast, hcoeff, map_mul, map_pow, powerSeries_map_mk', htr]
    rw [Equiv.prod_comp π.symm fun i ↦
        _root_.GlobalTheory.HilbFam.rco (2 * s) (κ i) (μ i) * (-1) ^ μ i,
      Equiv.sum_comp π.symm fun i ↦ κ i - μ i]

end GlobalTheory.HilbFam
end
end
