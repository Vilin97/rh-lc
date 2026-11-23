module

public import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HermitianCodeWordWeilElementMemQuadraticField
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Definitions.Foundations.TupleConstantsNeZero
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.PairingDivisors.PairingDivisorProofs.SumValuationNat
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCompLeSumOfInjOn

section

@[expose] public section

open NumberField IsDedekindDomain Finset GlobalTheory.Square
open Formalism.DivisionValues (vw conjPl)
open Formalism.PairingDivisionLocalBalance (Pl wt)

namespace GlobalTheory.Square

theorem sum_comp_le_sum_of_injOn {ι : Type*} (T : Finset ι) (S : Finset ℤ) (f : ι → ℤ)
    (g : ℤ → ℝ) (hf : Set.InjOn f T) (hS : ∀ t ∈ T, f t ∈ S) (hg : ∀ s ∈ S, 0 ≤ g s) :
    ∑ t ∈ T, g (f t) ≤ ∑ s ∈ S, g s := by
  rw [← Finset.sum_image (g := f) (f := g) hf]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun s hs _ => hg s hs)
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hs
  exact hS t ht

theorem sum_le_sum_add_card_mul {ι : Type*} (T : Finset ι) (S : Finset ℤ) (f : ι → ℤ)
    (g : ℤ → ℝ) (u : ι → ℝ) (c : ℝ) (hf : Set.InjOn f T) (hS : ∀ t ∈ T, f t ∈ S)
    (hg : ∀ s ∈ S, 0 ≤ g s) (hu : ∀ t ∈ T, u t ≤ g (f t) + c) :
    ∑ t ∈ T, u t ≤ ∑ s ∈ S, g s + (T.card : ℝ) * c := by
  have h1 := Finset.sum_le_sum hu
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 := sum_comp_le_sum_of_injOn T S f g hf hS hg
  linarith

theorem count_factors : ∀ (e p q e0 h0 : ℕ), e0 + p = e + q → e0 ≤ h0 → ∀ (v a n0 : ℤ → ℝ) (er : ℝ), 0 ≤ er → (∀ s : ℤ, 1 ≤ s → s ≤ (h0 : ℤ) + p + q → 0 ≤ a s ∧ 0 ≤ n0 s ∧ v s ≤ a s + er ∧ -(v s) ≤ a s + n0 s) → (∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → v s = v (1 - s)) → (∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), v s) + (∑ k ∈ range p, v ((e : ℤ) + q - k)) - (∑ k ∈ range q, v ((e : ℤ) + k + 1)) ≤ 4 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), a s) + 5 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), n0 s) + ((2 * (h0 + p + q) : ℕ) : ℝ) * er := by
  intro e p q e0 h0 he hle v a n0 er her H hsym
  set S : Finset ℤ := Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ) with hS
  have hmem : ∀ s : ℤ, s ∈ S ↔ 1 ≤ s ∧ s ≤ (h0 : ℤ) + p + q := by
    intro s; simp [hS]
  have ha : ∀ s ∈ S, 0 ≤ a s := fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).1
  have hn : ∀ s ∈ S, 0 ≤ n0 s := fun s hs => (H s ((hmem s).1 hs).1 ((hmem s).1 hs).2).2.1
  have hsplit : ∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), v s
      = ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s + ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s := by
    rw [← Finset.sum_union]
    · congr 1
      ext s
      simp only [mem_union, mem_Icc]
      omega
    · rw [Finset.disjoint_left]
      intro s h1 h2
      simp only [mem_Icc] at h1 h2
      omega
  have b1 : ∑ s ∈ Icc (1 - (e0 : ℤ)) 0, v s ≤ ∑ s ∈ S, a s + (e0 : ℝ) * er := by
    have := sum_le_sum_add_card_mul (Icc (1 - (e0 : ℤ)) 0) S (fun s => 1 - s) a v er
      (fun x _ y _ h => by simpa using h)
      (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha
      (fun t ht => by
        simp only [mem_Icc] at ht
        rw [hsym t ht.1 ht.2]
        exact (H _ (by omega) (by omega)).2.2.1)
    have hc : (Icc (1 - (e0 : ℤ)) 0).card = e0 := by
      rw [Int.card_Icc]; omega
    rwa [hc] at this
  have b2 : ∑ s ∈ Icc (1 : ℤ) (h0 : ℤ), v s ≤ ∑ s ∈ S, a s + (h0 : ℝ) * er := by
    have := sum_le_sum_add_card_mul (Icc (1 : ℤ) (h0 : ℤ)) S (fun s => s) a v er
      (fun x _ y _ h => h)
      (fun t ht => by rw [hmem]; simp only [mem_Icc] at ht; omega) ha
      (fun t ht => by
        simp only [mem_Icc] at ht
        exact (H _ (by omega) (by omega)).2.2.1)
    have hc : (Icc (1 : ℤ) (h0 : ℤ)).card = h0 := by
      rw [Int.card_Icc]; omega
    rwa [hc] at this
  have b3 : ∑ k ∈ range p, v ((e : ℤ) + q - k) ≤ ∑ s ∈ S, a s + (p : ℝ) * er := by
    have := sum_le_sum_add_card_mul (range p) S (fun k : ℕ => (e : ℤ) + q - k) a
      (fun k : ℕ => v ((e : ℤ) + q - k)) er
      (fun x _ y _ h => by simp only at h; omega)
      (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega) ha
      (fun t ht => by
        simp only [mem_range] at ht
        exact (H _ (by omega) (by omega)).2.2.1)
    rwa [card_range] at this
  have b4 : ∑ k ∈ range q, -v ((e : ℤ) + k + 1) ≤ ∑ s ∈ S, (a s + n0 s) + (q : ℝ) * 0 := by
    have := sum_le_sum_add_card_mul (range q) S (fun k : ℕ => (e : ℤ) + k + 1)
      (fun s => a s + n0 s) (fun k : ℕ => -v ((e : ℤ) + k + 1)) 0
      (fun x _ y _ h => by simp only at h; omega)
      (fun t ht => by rw [hmem]; simp only [mem_range] at ht; omega)
      (fun s hs => add_nonneg (ha s hs) (hn s hs))
      (fun t ht => by
        simp only [mem_range] at ht
        rw [add_zero]
        exact (H _ (by omega) (by omega)).2.2.2)
    rwa [card_range] at this
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at b4
  have hN : 0 ≤ ∑ s ∈ S, n0 s := Finset.sum_nonneg hn
  have hA : 0 ≤ ∑ s ∈ S, a s := Finset.sum_nonneg ha
  have hcount : ((e0 : ℝ) + h0 + p) * er ≤ ((2 * (h0 + p + q) : ℕ) : ℝ) * er := by
    refine mul_le_mul_of_nonneg_right ?_ her
    have : e0 + h0 + p ≤ 2 * (h0 + p + q) := by omega
    exact_mod_cast this
  rw [hsplit]
  linarith

end GlobalTheory.Square
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneSqStOfClaims

section

@[expose] public section

open NumberField IsDedekindDomain Finset
open Formalism.DivisionValues (vw)

noncomputable section

namespace GlobalTheory.SqTop.OneSqProof

theorem vw_ratio_le {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) (e p q e0 h0 : ℕ)
    (he : e0 + p = e + q) (hle : e0 ≤ h0) (rq ζ γ zA zA' : K) (tk : Fin (p + q) → K) (ρ : ℤ → K) (a n0 : ℤ → ℝ)
    (er dl B : ℝ)
    (heq : rq * ∏ k ∈ range q, ρ ((e : ℤ) + k + 1) = ζ * (∏ k, tk k) * γ * ∏ k ∈ range p, ρ ((e : ℤ) + q - k))
    (hρ0 : ∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ (h0 : ℤ) + p + q → ρ s ≠ 0)
    (hζ : ζ ≠ 0 ∧ vw w ζ = 0) (ht : ∀ k, tk k ≠ 0 ∧ |(vw w (tk k) : ℝ)| ≤ B) (hγ : γ ≠ 0) (hzA : zA ≠ 0)
    (hγv : (vw w γ : ℝ) ≤ vw w (zA * ∏ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), ρ s) + vw w zA' + 6 * dl)
    (her : 0 ≤ er)
    (hs : ∀ s : ℤ, 1 ≤ s → s ≤ (h0 : ℤ) + p + q →
      0 ≤ a s ∧ 0 ≤ n0 s ∧ (vw w (ρ s) : ℝ) ≤ a s + er ∧ -(vw w (ρ s) : ℝ) ≤ a s + n0 s)
    (hsym : ∀ s : ℤ, 1 - (e0 : ℤ) ≤ s → s ≤ 0 → vw w (ρ s) = vw w (ρ (1 - s))) :
    rq ≠ 0 ∧ (vw w rq : ℝ) ≤ |(vw w zA : ℝ)| + |(vw w zA' : ℝ)| +
      4 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), a s) + 5 * (∑ s ∈ Icc (1 : ℤ) ((h0 + p + q : ℕ) : ℤ), n0 s) +
      ((2 * (h0 + p + q) : ℕ) : ℝ) * er + 6 * dl + ((p + q : ℕ) : ℝ) * B := by
  have hq0 : ∀ k ∈ range q, ρ ((e : ℤ) + k + 1) ≠ 0 := fun k hk => by
    rw [mem_range] at hk; exact hρ0 _ (by omega) (by omega)
  have hp0 : ∀ k ∈ range p, ρ ((e : ℤ) + q - k) ≠ 0 := fun k hk => by
    rw [mem_range] at hk; exact hρ0 _ (by omega) (by omega)
  have hI0 : ∀ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), ρ s ≠ 0 := fun s hs => by
    rw [mem_Icc] at hs; exact hρ0 _ hs.1 (by omega)
  have hT : ∀ k ∈ (univ : Finset (Fin (p + q))), tk k ≠ 0 := fun k _ => (ht k).1
  have hPq := prod_ne_zero_iff.2 hq0
  have hPp := prod_ne_zero_iff.2 hp0
  have hPT := prod_ne_zero_iff.2 hT
  have hPI := prod_ne_zero_iff.2 hI0
  have hR : ζ * (∏ k, tk k) * γ * ∏ k ∈ range p, ρ ((e : ℤ) + q - k) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hζ.1 hPT) hγ) hPp
  have hrq : rq ≠ 0 := by
    rintro rfl; rw [zero_mul] at heq; exact hR heq.symm
  refine ⟨hrq, ?_⟩
  have hv := congrArg (vw w) heq
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hrq hPq, Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hq0,
    Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero (mul_ne_zero hζ.1 hPT) hγ) hPp,
    Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero hζ.1 hPT) hγ, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hζ.1 hPT,
    Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hT, Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hp0, hζ.2] at hv
  have hz := Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hzA hPI
  rw [Formalism.PairingDivisionLocalBalance.vw_prod w _ _ hI0] at hz
  rw [hz] at hγv
  have hc := GlobalTheory.Square.count_factors e p q e0 h0 he hle (fun s => (vw w (ρ s) : ℝ)) a n0 er her
    (fun s h1 h2 => hs s h1 h2) (fun s h1 h2 => by simp only [hsym s h1 h2])
  have hvR : (vw w rq : ℝ) + ∑ k ∈ range q, (vw w (ρ ((e : ℤ) + k + 1)) : ℝ) =
      (∑ k, (vw w (tk k) : ℝ)) + vw w γ + ∑ k ∈ range p, (vw w (ρ ((e : ℤ) + q - k)) : ℝ) := by
    have := congrArg (fun x : ℤ => (x : ℝ)) hv
    push_cast at this
    linarith
  have hTB : (∑ k, (vw w (tk k) : ℝ)) ≤ ((p + q : ℕ) : ℝ) * B := by
    calc (∑ k, (vw w (tk k) : ℝ)) ≤ ∑ _k : Fin (p + q), B :=
          sum_le_sum fun k _ => (le_abs_self _).trans (ht k).2
      _ = ((p + q : ℕ) : ℝ) * B := by simp
  have hIc : ((∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), vw w (ρ s) : ℤ) : ℝ) =
      ∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), (vw w (ρ s) : ℝ) := by push_cast; rfl
  have hγv' : (vw w γ : ℝ) ≤ vw w zA + (∑ s ∈ Icc (1 - (e0 : ℤ)) (h0 : ℤ), (vw w (ρ s) : ℝ)) + vw w zA' + 6 * dl := by
    have := hγv; push_cast at this; linarith
  have a1 := le_abs_self (vw w zA : ℝ)
  have a2 := le_abs_self (vw w zA' : ℝ)
  linarith

end GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqProof

theorem wt_at {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {S : Finset ℕ} {c : ℕ → ℝ} {l : ℕ}
    (hS : ∀ l' ∈ S, l'.Prime) (hl : l.Prime) (hw : (l : 𝓞 K) ∈ w.asIdeal) (hc : l ∉ S → c l = 0) :
    Formalism.PairingDivisionLocalBalance.wt S c w = c l * (vw w (l : K) : ℝ) := by
  unfold Formalism.PairingDivisionLocalBalance.wt
  by_cases h : l ∈ S
  · refine sum_eq_single_of_mem l h fun l' hl' hne => ?_
    have hn : (l' : 𝓞 K) ∉ w.asIdeal := fun h' => hne (GlobalTheory.FunObj.SqNum.prime_unique (hS l' hl') hl h' hw)
    have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
    simp only [map_natCast] at this
    rw [this]; simp
  · rw [hc h, zero_mul]
    refine sum_eq_zero fun l' hl' => ?_
    have hne : l' ≠ l := fun e => h (e ▸ hl')
    have hn : (l' : 𝓞 K) ∉ w.asIdeal := fun h' => hne (GlobalTheory.FunObj.SqNum.prime_unique (hS l' hl') hl h' hw)
    have := GlobalTheory.Square.vw_eq_zero_of_notMem w hn
    simp only [map_natCast] at this
    rw [this]; simp

theorem wt_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) {S : Finset ℕ} {c : ℕ → ℝ}
    (hc : ∀ l ∈ S, 0 ≤ c l) : 0 ≤ Formalism.PairingDivisionLocalBalance.wt S c w :=
  sum_nonneg fun l hl => mul_nonneg (hc l hl) (GlobalTheory.Square.TwoStep.vw_natCast_nonneg w l)

end GlobalTheory.SqTop.OneSqProof

namespace GlobalTheory.SqTop.OneSqProof

theorem exists_prime_mem' {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ w.asIdeal := by
  have := w.isMaximal
  have : Finite (𝓞 K ⧸ w.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ w.ne_bot
  letI := Ideal.Quotient.field w.asIdeal
  refine ⟨ringChar (𝓞 K ⧸ w.asIdeal), CharP.char_is_prime (𝓞 K ⧸ w.asIdeal) _, ?_⟩
  exact Ideal.Quotient.eq_zero_iff_mem.1 (by simpa using CharP.cast_eq_zero (𝓞 K ⧸ w.asIdeal) (ringChar _))

end GlobalTheory.SqTop.OneSqProof

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.PairingDivisionLocalBalance (wt HtLe)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL IsValChar beta)
open GlobalTheory.SqTop

namespace GlobalTheory.SqTop.OneSqProof

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.SqTop.OneSqProof
end
end
end
