module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLe
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
public import Mathlib.FieldTheory.Galois.Infinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGeomSumGaloisLeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_sum_pow_apply_le_and_norm_pow_prime_sub_le : ∀ (l : ℕ) [Fact l.Prime] (σ : GQ l) (S : AddSubgroup (Om l)) (s : ℝ), 0 ≤ s → s ≤ 1 → (∀ x ∈ S, σ x ∈ S) → (∀ x ∈ S, ‖σ x - x‖ ≤ s * ‖x‖) → ∀ x ∈ S, ‖∑ i ∈ Finset.range l, (σ ^ i) x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * ‖x‖ ∧ ‖(σ ^ l) x - x‖ ≤ max (s ^ (l - 1)) ‖((l : ℕ) : Om l)‖ * s * ‖x‖ := by
  first | exact @GlobalTheory.MemLoc.norm_geom_sum_galois_le | exact GlobalTheory.MemLoc.norm_geom_sum_galois_le | (intros; apply GlobalTheory.MemLoc.norm_geom_sum_galois_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowIndexLeOfFixed

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Per

theorem norm_pow_index_le_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup (GQ l)), H.index ≠ 0 → ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖x‖ < 1 → ‖x‖ ^ H.index ≤ ‖((l : ℕ) : Om l)‖ := by
  intro l _ H hidx x hx hx1
  have hfin : Fintype (GQ l ⧸ H) := Subgroup.fintypeOfIndexNeZero hidx
  have fout : ∀ g : GQ l, (g : GQ l ⧸ H).out x = g x := fun g => by
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
    rw [hh, AlgEquiv.mul_apply, hx h h.2]
  have hfix : ∀ g : GQ l, g (∏ q : GQ l ⧸ H, q.out x) = ∏ q : GQ l ⧸ H, q.out x := fun g => by
    rw [map_prod, ← Equiv.prod_comp (MulAction.toPerm g) fun q : GQ l ⧸ H => q.out x]
    refine Finset.prod_congr rfl fun q _ => ?_
    have e : MulAction.toPerm g q = ((g * q.out : GQ l) : GQ l ⧸ H) := by
      rw [MulAction.toPerm_apply, ← smul_eq_mul, MulAction.Quotient.mk_smul_out]
    rw [e, fout, AlgEquiv.mul_apply]
  obtain ⟨c, hc⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  have hn : ‖c‖ = ‖x‖ ^ H.index := by
    rw [← norm_algebraMap' (Om l) c, hc, norm_prod]
    refine (Finset.prod_congr rfl fun q _ => GlobalTheory.RingBasics.norm_gal (Quotient.out q) x).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
    rfl
  have hc1 : ‖c‖ < 1 := hn ▸ pow_lt_one₀ (norm_nonneg x) hx1 hidx
  have h2 : ‖c‖ ≤ (l : ℝ) ^ (-1 : ℤ) := by
    rw [Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    simpa using hc1
  rw [← hn, ← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_p]
  simpa using h2

end GlobalTheory.Per
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormInertiaPowPrimePowSubLe

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.InertiaMove

theorem fixed_apply {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal) (σ : GQ l)
    {x : Om l} (hx : ∀ g ∈ H, g x = x) : ∀ g ∈ H, g (σ x) = σ x := by
  intro g hg
  have h := hx _ (hH.conj_mem' g hg σ)
  have h2 : σ ((σ⁻¹ * g * σ) x) = g (σ x) := by
    rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply]
    congr 1
    group
  rw [← h2, h]

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add (f := _), ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

theorem norm_natCast_le_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ ≤ 1 :=
  IsUltrametricDist.norm_natCast_le_one _ _

theorem norm_pow_sub_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : Subgroup (GQ l)), H.Normal → H.index ≠ 0 → ∀ m n : ℕ, H.index ≤ l ^ m → γ ^ l ^ n ∈ H → ∀ j ≤ m, ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖(γ ^ l ^ j) x - x‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (m - j)) * ‖x‖ := by
  intro l hl γ hγ H hH hi m n hm hn j
  have hτ0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have hτ1 := norm_natCast_le_one l
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hlR : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hτpos : 0 < ‖((l : ℕ) : Om l)‖ := by
    rw [norm_pos_iff]
    exact_mod_cast hl0
  induction j with
  | zero =>
    intro _ x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx0
    have hlt := GlobalTheory.WildMove.norm_sub_lt l γ hγ n x hx0 (hx _ hn)
    set z : Om l := (γ x - x) / x with hz
    have hzfix : ∀ g ∈ H, g z = z := by
      intro g hg
      rw [hz, map_div₀, map_sub, fixed_apply hH γ hx g hg, hx g hg]
    have hzn : ‖z‖ = ‖γ x - x‖ / ‖x‖ := norm_div _ _
    have hz1 : ‖z‖ < 1 := by rw [hzn, div_lt_one hxpos]; exact hlt
    have hv := GlobalTheory.Per.norm_pow_index_le_of_fixed l H hi z hzfix hz1
    have h1 : ‖z‖ ^ (l ^ m) ≤ ‖((l : ℕ) : Om l)‖ :=
      (pow_le_pow_of_le_one (norm_nonneg _) hz1.le hm).trans hv
    have h2 : ‖z‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ m) := by
      have h3 := Real.rpow_le_rpow (by positivity) h1
        (show (0 : ℝ) ≤ ((l ^ m : ℕ) : ℝ)⁻¹ by positivity)
      rw [Real.pow_rpow_inv_natCast (norm_nonneg _) (pow_ne_zero _ hl0)] at h3
      rw [one_div]
      exact_mod_cast h3
    rw [hzn, div_le_iff₀ hxpos] at h2
    simpa using h2
  | succ j ih =>
    intro hj x hx
    have ih' := ih (by omega)
    obtain ⟨k, hk⟩ : ∃ k, m - j = k + 1 := ⟨m - j - 1, by omega⟩
    have hk' : m - (j + 1) = k := by omega
    rw [hk] at ih'
    rw [hk']
    set s : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hs
    have hs0 : 0 ≤ s := Real.rpow_nonneg hτ0 _
    have hs1 : s ≤ 1 := Real.rpow_le_one hτ0 hτ1 (by positivity)
    have h := (GlobalTheory.MemLoc.norm_geom_sum_galois_le l (γ ^ l ^ j) (fixedAdd H) s hs0 hs1
      (fun y hy => fixed_apply hH _ hy) (fun y hy => ih' y hy) x hx).2
    rw [← pow_mul, ← pow_succ] at h
    have hsl : s ^ l = ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ k) := by
      rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hτ0]
      congr 1
      field_simp
      ring
    have hτs : ‖((l : ℕ) : Om l)‖ ≤ s ^ (l - 1) := by
      have h1 : s ^ l ≤ s ^ (l - 1) := pow_le_pow_of_le_one hs0 hs1 (by omega)
      refine le_trans ?_ h1
      rw [hsl]
      have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.pos
      have h2 : (1 : ℝ) / (l : ℝ) ^ k ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact one_le_pow₀ hl1
      have h3 := Real.rpow_le_rpow_of_exponent_ge hτpos hτ1 h2
      rwa [Real.rpow_one] at h3
    rw [max_eq_left hτs, ← pow_succ, Nat.sub_add_cancel hl.out.pos, hsl] at h
    exact h

end GlobalTheory.InertiaMove
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormInertiaPowPrimePowSubLeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_inertia_pow_prime_pow_sub_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : Subgroup (GQ l)), H.Normal → H.index ≠ 0 → ∀ m n : ℕ, H.index ≤ l ^ m → γ ^ l ^ n ∈ H → ∀ j ≤ m, ∀ x : Om l, (∀ g ∈ H, g x = x) → ‖(γ ^ l ^ j) x - x‖ ≤ ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (m - j)) * ‖x‖ := by
  first | exact @GlobalTheory.InertiaMove.norm_pow_sub_le | exact GlobalTheory.InertiaMove.norm_pow_sub_le | (intros; apply GlobalTheory.InertiaMove.norm_pow_sub_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormInertiaPartialTraceGeometricLe

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.PartialTraceGain

theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (a b : ℕ) :
    ∑ i ∈ Finset.range (a * b), f i = ∑ i ∈ Finset.range a, ∑ j ∈ Finset.range b, f (i + a * j) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_range_succ, add_comm (a * b) i]

theorem norm_natCast_lt_one (l : ℕ) [Fact l.Prime] : ‖((l : ℕ) : Om l)‖ < 1 := by
  have h : ((l : ℕ) : Om l) = algebraMap ℚ_[l] (Om l) (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

def fixedAdd {l : ℕ} [Fact l.Prime] (H : Subgroup (GQ l)) : AddSubgroup (Om l) where
  carrier := {x | ∀ g ∈ H, g x = x}
  add_mem' := fun {a b} ha hb g hg => by rw [map_add (f := _), ha g hg, hb g hg]
  zero_mem' := fun g _ => map_zero g
  neg_mem' := fun {a} ha g hg => by rw [map_neg, ha g hg]

theorem apply_mem_fixedAdd {l : ℕ} [Fact l.Prime] {H : Subgroup (GQ l)} (hH : H.Normal)
    (σ : GQ l) {x : Om l} (hx : x ∈ fixedAdd H) : σ x ∈ fixedAdd H := by
  intro g hg
  have h1 := hx _ (hH.conj_mem' g hg σ)
  have h2 : g * σ = σ * (σ⁻¹ * g * σ) := by group
  calc g (σ x) = (g * σ) x := rfl
    _ = σ ((σ⁻¹ * g * σ) x) := by rw [h2]; rfl
    _ = σ x := by rw [h1]

theorem apply_sum_pow {l : ℕ} [Fact l.Prime] (σ : GQ l) (m : ℕ) {x : Om l}
    (hx : (σ ^ m) x = x) :
    σ (∑ j ∈ Finset.range m, (σ ^ j) x) = ∑ j ∈ Finset.range m, (σ ^ j) x := by
  have h1 : σ (∑ j ∈ Finset.range m, (σ ^ j) x) = ∑ j ∈ Finset.range m, (σ ^ (j + 1)) x := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pow_succ']; rfl
  have h2 := Finset.sum_range_succ' (fun j => (σ ^ j) x) m
  rw [Finset.sum_range_succ, hx] at h2
  rw [h1]
  simpa using h2.symm

theorem pow_apply_of_fixed {l : ℕ} [Fact l.Prime] (σ : GQ l) {y : Om l} (hy : σ y = y) (i : ℕ) :
    (σ ^ i) y = y := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ]
    change (σ ^ i) (σ y) = y
    rw [hy, ih]

theorem norm_sum_pow_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : ℕ → Subgroup (GQ l)) (k : ℕ), (∀ n, (H n).Normal) → (∀ n, (H n).index ≠ 0) → (∀ n, (H n).index ≤ l ^ (k + n)) → (∀ n, γ ^ l ^ n ∈ H n) → (∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1)) → ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : Om l), (∀ g ∈ H n, g x = x) → ‖∑ i ∈ Finset.range (l ^ n), (γ ^ i) x‖ ≤ ρ ^ n * ‖x‖ := by
  intro l hl γ hγ H k hN hI hIle hpow hgen
  have hp : l.Prime := hl.out
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hp.one_le
  have ha0 : 0 ≤ ‖((l : ℕ) : Om l)‖ := norm_nonneg _
  have ha1 := norm_natCast_lt_one l
  have hpk : (1 : ℝ) ≤ (l : ℝ) ^ (k + 1) := one_le_pow₀ hl1
  have he0 : (0 : ℝ) < (1 : ℝ) / (l : ℝ) ^ (k + 1) := by positivity
  have he1 : (1 : ℝ) / (l : ℝ) ^ (k + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact hpk
  set ρ : ℝ := ‖((l : ℕ) : Om l)‖ ^ ((1 : ℝ) / (l : ℝ) ^ (k + 1)) with hρ
  have hρ0 : 0 ≤ ρ := Real.rpow_nonneg ha0 _
  have hρ1 : ρ < 1 := Real.rpow_lt_one ha0 ha1 he0
  have haρ : ‖((l : ℕ) : Om l)‖ ≤ ρ := by
    have := Real.rpow_le_rpow_of_exponent_ge' ha0 ha1.le he0.le he1
    rwa [Real.rpow_one] at this
  have hmax : max (ρ ^ (l - 1)) ‖((l : ℕ) : Om l)‖ ≤ ρ := by
    refine max_le ?_ haρ
    have h2 := hp.two_le
    exact pow_le_of_le_one hρ0 hρ1.le (by omega)
  refine ⟨ρ, hρ0, hρ1, fun n => ?_⟩
  induction n with
  | zero => intro x _; simp
  | succ n ih =>
    intro x hx
    set σ : GQ l := γ ^ l ^ n with hσ
    have hσl : σ ^ l = γ ^ l ^ (n + 1) := by rw [hσ, ← pow_mul, ← pow_succ]
    have hxS : x ∈ fixedAdd (H (n + 1)) := hx
    set y : Om l := ∑ j ∈ Finset.range l, (σ ^ j) x with hy
    have hyS : y ∈ fixedAdd (H (n + 1)) :=
      sum_mem fun j _ => apply_mem_fixedAdd (hN _) _ hxS
    have hσy : σ y = y := apply_sum_pow σ l (by rw [hσl]; exact hx _ (hpow _))
    have hyH : ∀ g ∈ H n, g y = y := by
      intro g hg
      obtain ⟨i, hi⟩ := hgen n g hg
      have h1 := hyS _ hi
      have h2 : g = σ ^ i * ((σ ^ i)⁻¹ * g) := by group
      calc g y = (σ ^ i) (((σ ^ i)⁻¹ * g) y) := by
            conv_lhs => rw [h2]
            rfl
        _ = y := by rw [h1, pow_apply_of_fixed σ hσy]
    have hmove : ∀ z ∈ fixedAdd (H (n + 1)), ‖σ z - z‖ ≤ ρ * ‖z‖ := by
      intro z hz
      have := GlobalTheory.T.norm_inertia_pow_prime_pow_sub_le l γ hγ (H (n + 1)) (hN _) (hI _) (k + (n + 1)) (n + 1) (hIle _)
        (hpow _) n (by omega) z hz
      rwa [show k + (n + 1) - n = k + 1 by omega] at this
    have hyn : ‖y‖ ≤ ρ * ‖x‖ :=
      (GlobalTheory.T.norm_sum_pow_apply_le_and_norm_pow_prime_sub_le l σ (fixedAdd (H (n + 1))) ρ hρ0 hρ1.le
        (fun z hz => apply_mem_fixedAdd (hN _) σ hz) hmove x hxS).1.trans
        (mul_le_mul_of_nonneg_right hmax (norm_nonneg _))
    have hsum : ∑ i ∈ Finset.range (l ^ (n + 1)), (γ ^ i) x
        = ∑ i ∈ Finset.range (l ^ n), (γ ^ i) y := by
      rw [pow_succ, sum_range_mul_eq]
      refine Finset.sum_congr rfl fun i _ => ?_

      rw [hy, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [pow_add, pow_mul]; rfl
    rw [hsum]
    calc _ ≤ ρ ^ n * ‖y‖ := ih y hyH
      _ ≤ ρ ^ n * (ρ * ‖x‖) := mul_le_mul_of_nonneg_left hyn (pow_nonneg hρ0 _)
      _ = ρ ^ (n + 1) * ‖x‖ := by ring

end GlobalTheory.PartialTraceGain
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormInertiaPartialTraceGeometricLeStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.norm_inertia_partialTrace_geometric_le : ∀ (l : ℕ) [Fact l.Prime] (γ : GQ l), γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup → ∀ (H : ℕ → Subgroup (GQ l)) (k : ℕ), (∀ n, (H n).Normal) → (∀ n, (H n).index ≠ 0) → (∀ n, (H n).index ≤ l ^ (k + n)) → (∀ n, γ ^ l ^ n ∈ H n) → (∀ n, ∀ h ∈ H n, ∃ i : ℕ, ((γ ^ l ^ n) ^ i)⁻¹ * h ∈ H (n + 1)) → ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (n : ℕ) (x : Om l), (∀ g ∈ H n, g x = x) → ‖∑ i ∈ Finset.range (l ^ n), (γ ^ i) x‖ ≤ ρ ^ n * ‖x‖ := by
  first | exact @GlobalTheory.PartialTraceGain.norm_sum_pow_le | exact GlobalTheory.PartialTraceGain.norm_sum_pow_le | (intros; apply GlobalTheory.PartialTraceGain.norm_sum_pow_le <;> assumption)
end
end
