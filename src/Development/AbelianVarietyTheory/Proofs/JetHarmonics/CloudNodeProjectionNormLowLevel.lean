module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterFinBounds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CardFilterLeSuccAndSqSumLePow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevSubspaceMono
public import Mathlib.Analysis.Complex.Basic
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormSumEigenprojectorLeOfResolventBound
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasEigenvalueSummand
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirOffDiagonalNormSqLeOfLevelStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightNearDiagonalOperatorsBounds
import Mathlib.Algebra.Order.Star.Real
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlModuleProjComponentsLevelAddTwoStatement
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormEigenLePowMulNormSum

section

@[expose] public section

open Finset
open scoped InnerProductSpace

namespace GlobalTheory

theorem norm_eigen_le_pow_mul_norm_sum {H κ : Type} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [DecidableEq κ] (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (lam : κ → ℂ) (s : κ) (Bd : ℝ)
    (hBd : 0 ≤ Bd) (E : Finset κ) :
    (∀ j ∈ E, 1 ≤ ‖lam s - lam j‖) → (∀ j ∈ E, ∀ x ∈ VV, ‖T x - lam j • x‖ ≤ Bd * ‖x‖) →
    ∀ v : κ → H, (∀ i, v i ∈ VV ∧ T (v i) = lam i • v i) →
      ‖v s‖ ≤ Bd ^ E.card * ‖v s + ∑ i ∈ E, v i‖ := by
  induction E using Finset.induction_on with
  | empty => intro _ _ v _; simp
  | insert j E hj ih =>
    intro h1 h2 v hv
    have hw : ∀ i, (lam i - lam j) • v i ∈ VV ∧
        T ((lam i - lam j) • v i) = lam i • (lam i - lam j) • v i := fun i =>
      ⟨VV.smul_mem _ (hv i).1, by rw [map_smul, (hv i).2, smul_comm]⟩
    have hih := ih (fun k hk => h1 k (mem_insert_of_mem hk))
      (fun k hk => h2 k (mem_insert_of_mem hk)) (fun i => (lam i - lam j) • v i) hw
    have hy : v s + ∑ i ∈ insert j E, v i ∈ VV :=
      VV.add_mem (hv s).1 (VV.sum_mem fun i _ => (hv i).1)
    have hT := h2 j (mem_insert_self j E) _ hy
    have heq : T (v s + ∑ i ∈ insert j E, v i) - lam j • (v s + ∑ i ∈ insert j E, v i)
        = (lam s - lam j) • v s + ∑ i ∈ E, (lam i - lam j) • v i := by
      rw [sum_insert hj]

      simp only [map_add (f := _), map_sum, (hv _).2, smul_add, smul_sum, sub_smul, sum_sub_distrib]
      abel
    rw [heq] at hT
    have hs : ‖v s‖ ≤ ‖(lam s - lam j) • v s‖ := by
      rw [norm_smul]
      exact le_mul_of_one_le_left (norm_nonneg _) (h1 j (mem_insert_self j E))
    rw [card_insert_of_notMem hj, pow_succ, mul_assoc]
    exact hs.trans (hih.trans (mul_le_mul_of_nonneg_left hT (pow_nonneg hBd _)))

theorem norm_node_projector_le :
    ∀ (H κ : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [Fintype κ] [DecidableEq κ] (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : κ → H →ₗ[ℂ] H) (lam : κ → ℂ) (Nd : Finset κ) (s : κ) (Bd Cn : ℝ), s ∈ Nd → 0 ≤ Bd → (∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = lam i • p i x) → (∀ x ∈ VV, T x ∈ VV) → (∀ j ∈ Nd.erase s, 1 ≤ ‖lam s - lam j‖) → (∀ j ∈ Nd.erase s, ∀ x ∈ VV, ‖T x - lam j • x‖ ≤ Bd * ‖x‖) → (∀ x ∈ VV, ‖∑ i ∈ Nd, p i x‖ ≤ Cn * ‖x‖) → ∀ x ∈ VV, ‖p s x‖ ≤ Cn * Bd ^ (Nd.erase s).card * ‖x‖ := by
  intro H κ _ _ _ _ VV T p lam Nd s Bd Cn hs hBd hp _ h1 h2 hC x hx
  have h := norm_eigen_le_pow_mul_norm_sum VV T lam s Bd hBd (Nd.erase s) h1 h2
    (fun i => p i x) (fun i => hp i x hx)
  have hsum : p s x + ∑ i ∈ Nd.erase s, p i x = ∑ i ∈ Nd, p i x :=
    add_sum_erase Nd (fun i => p i x) hs
  rw [hsum] at h
  calc ‖p s x‖ ≤ Bd ^ (Nd.erase s).card * ‖∑ i ∈ Nd, p i x‖ := h
    _ ≤ Bd ^ (Nd.erase s).card * (Cn * ‖x‖) :=
        mul_le_mul_of_nonneg_left (hC x hx) (pow_nonneg hBd _)
    _ = Cn * Bd ^ (Nd.erase s).card * ‖x‖ := by ring

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirResolventCircleBounds

section

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem splitCasRes_norm_sq_le_weighted {M : Type} [NormedAddCommGroup M] (u v : M) :
    ‖u‖ ^ 2 ≤ 15 / 13 * ‖u + v‖ ^ 2 + 15 / 2 * ‖v‖ ^ 2 := by
  have htri : ‖u‖ ≤ ‖u + v‖ + ‖v‖ := by
    calc ‖u‖ = ‖(u + v) - v‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖u + v‖ + ‖v‖ := norm_sub_le _ _
  have hsq : ‖u‖ ^ 2 ≤ (‖u + v‖ + ‖v‖) ^ 2 := by gcongr
  nlinarith [sq_nonneg (2 * ‖u + v‖ - 13 * ‖v‖)]

theorem splitCasRes_norm_add_sq_le {M : Type} [NormedAddCommGroup M] (u v : M) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hsq : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 := by
    gcongr
    exact norm_add_le u v
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

theorem splitCasRes_circle_dist (b t : ℝ) (ζ : ℂ) (hζ : ‖ζ + ((b / 16 : ℝ) : ℂ)‖ = 9 * b / 16)
    (ht : (-b / 8 - b / 32 ≤ -t ∧ -t ≤ b / 32) ∨ b - b / 32 ≤ -t) :
    15 * b / 32 ≤ ‖ζ + (t : ℂ)‖ := by
  have hb : 0 ≤ b := by
    have := norm_nonneg (ζ + ((b / 16 : ℝ) : ℂ))
    linarith
  have hsplit : ζ + (t : ℂ) = (ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ) := by
    push_cast
    ring
  have hshift : ‖((t - b / 16 : ℝ) : ℂ)‖ = |t - b / 16| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hsplit]
  rcases ht with ⟨h1, h2⟩ | h3
  ·
    have hclose : |t - b / 16| ≤ 3 * b / 32 := by
      rw [abs_le]
      constructor <;> linarith
    have key := norm_sub_le ((ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ)) ((t - b / 16 : ℝ) : ℂ)
    rw [add_sub_cancel_right, hζ, hshift] at key
    linarith
  ·
    have hfar : 33 * b / 32 ≤ |t - b / 16| := by
      have := neg_le_abs (t - b / 16)
      linarith
    have key := norm_sub_le ((ζ + ((b / 16 : ℝ) : ℂ)) + ((t - b / 16 : ℝ) : ℂ)) (ζ + ((b / 16 : ℝ) : ℂ))
    rw [add_sub_cancel_left, hζ, hshift] at key
    linarith

theorem splitCas_resolvent_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → (∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → (13 * bv / 32) ^ 2 * ∑ c, ‖x c‖ ^ 2 ≤ ∑ c, ‖ζ • x c - splitCas E x c‖ ^ 2) ∧ ∑ c, ‖splitCas E x c‖ ^ 2 ≤ (3 * bv) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  intro M _ _ n ε E μ kk j bv x hmod hshape hj hlev
  obtain ⟨hbv, hω, -⟩ := shape_position n kk j ε μ bv hshape hj
  have hun : IsUnitary ε E := hmod.2.1
  have hoff : ∑ b, ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ (bv / 16) ^ 2 * ∑ c, ‖x c‖ ^ 2 :=
    GlobalTheory.T.splitCasimir_offDiagonal_norm_sq_le_of_level M n ε E μ kk j bv x hmod hshape hj hlev
  have hsplit : ∀ b, splitCas E x b = -(E b b (x b) + ∑ c ∈ univ.erase b, E b c (x c)) := by
    intro b
    simp only [splitCas]
    congr 1
    exact (Finset.add_sum_erase univ (fun c => E b c (x c)) (Finset.mem_univ b)).symm
  have hdiag := fun c => wtNear_diag_bounds M n ε E (lowK ε μ) (j : ℝ) (x c) hun (hlev c).2
  have hS : 0 ≤ ∑ c, ‖x c‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
  constructor
  · intro ζ hζ
    have hlow : ∀ b, (15 * bv / 32) ^ 2 * ‖x b‖ ^ 2 ≤ ‖ζ • x b + E b b (x b)‖ ^ 2 := by
      intro b
      refine (hdiag b).2.1 b ζ (15 * bv / 32) (by positivity) ?_
      intro ω hωn
      apply splitCasRes_circle_dist bv (ω b) ζ hζ
      obtain ⟨h1, h2⟩ := hω ω hωn b
      by_cases hb : b.val + 1 < kk
      · exact Or.inl (h1 hb)
      · exact Or.inr (h2 (by omega)).1
    have hper : ∀ b, 13 / 15 * (15 * bv / 32) ^ 2 * ‖x b‖ ^ 2
        - 13 / 2 * ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 ≤ ‖ζ • x b - splitCas E x b‖ ^ 2 := by
      intro b
      have hw := splitCasRes_norm_sq_le_weighted (ζ • x b + E b b (x b)) (∑ c ∈ univ.erase b, E b c (x c))
      have he : ζ • x b - splitCas E x b
          = (ζ • x b + E b b (x b)) + ∑ c ∈ univ.erase b, E b c (x c) := by
        rw [hsplit]
        abel
      rw [he]
      nlinarith [hlow b]
    have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin n))) => hper b)
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    nlinarith [hoff, hsum, mul_nonneg (sq_nonneg bv) hS]
  · have hD : ∀ b, ‖E b b (x b)‖ ^ 2 ≤ (65 * bv / 32) ^ 2 * ‖x b‖ ^ 2 := by
      intro b
      refine (hdiag b).2.2 b (65 * bv / 32) ?_
      intro ω hωn
      obtain ⟨h1, h2⟩ := hω ω hωn b
      rw [abs_le]
      by_cases hb : b.val + 1 < kk
      · obtain ⟨a1, a2⟩ := h1 hb
        constructor <;> linarith
      · obtain ⟨a1, a2⟩ := h2 (by omega)
        constructor <;> linarith
    have hper : ∀ b, ‖splitCas E x b‖ ^ 2
        ≤ 2 * (65 * bv / 32) ^ 2 * ‖x b‖ ^ 2 + 2 * ‖∑ c ∈ univ.erase b, E b c (x c)‖ ^ 2 := by
      intro b
      rw [hsplit, norm_neg]
      have ha := splitCasRes_norm_add_sq_le (E b b (x b)) (∑ c ∈ univ.erase b, E b c (x c))
      nlinarith [hD b]
    have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (univ : Finset (Fin n))) => hper b)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    nlinarith [hoff, hsum, mul_nonneg (sq_nonneg bv) hS]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirResolventCircleBoundsStatement

section

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.splitCasimir_resolvent_circle_bounds : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → (∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → (13 * bv / 32) ^ 2 * ∑ c, ‖x c‖ ^ 2 ≤ ∑ c, ‖ζ • x c - splitCas E x c‖ ^ 2) ∧ ∑ c, ‖splitCas E x c‖ ^ 2 ≤ (3 * bv) ^ 2 * ∑ c, ‖x c‖ ^ 2 := by
  first | exact @GlobalTheory.splitCas_resolvent_bounds | exact GlobalTheory.splitCas_resolvent_bounds | (intros; apply GlobalTheory.splitCas_resolvent_bounds <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudNodeProjectionNormLowLevel

section

@[expose] public section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem cloud_node_projector_bound (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (n kk : ℕ) (bv : ℝ)
    (VV : Submodule ℂ H) (T : H →ₗ[ℂ] H) (p : Fin n → H →ₗ[ℂ] H) (lam : Fin n → ℝ)
    (hfd : FiniteDimensional ℂ VV) (hb : 0 < bv)
    (hsum : ∀ x, ∑ i, p i x = x)
    (hp : ∀ i, ∀ x ∈ VV, p i x ∈ VV ∧ T (p i x) = (lam i : ℂ) • p i x)
    (hpos : ∀ a : Fin n, (a.val + 1 < kk → -bv / 8 - bv / 32 ≤ lam a ∧ lam a ≤ bv / 32) ∧
      (kk ≤ a.val + 1 → bv - bv / 32 ≤ lam a ∧ lam a ≤ 2 * bv + bv / 32))
    (hgap : ∀ a c : Fin n, a ≠ c → 1 ≤ |lam a - lam c|)
    (hcard : (univ.filter fun a : Fin n => kk ≤ a.val + 1).card = n + 1 - kk)
    (hres : ∀ ζ : ℂ, ‖ζ + ((bv / 16 : ℝ) : ℂ)‖ = 9 * bv / 16 → ∀ x ∈ VV, 13 * bv / 32 * ‖x‖ ≤ ‖ζ • x - T x‖)
    (hT : ∀ x ∈ VV, ‖T x‖ ≤ 3 * bv * ‖x‖) :
    ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖ ∧
      ∀ s : Fin n, kk ≤ s.val + 1 → ‖p s x‖ ≤ 3 * (6 * bv) ^ (n - kk) * ‖x‖ := by
  have h1 : ∀ x ∈ VV, ‖∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s x‖ ≤ 18 / 13 * ‖x‖ := by
    intro x hx
    have hnorm : ∀ i, ‖(lam i : ℂ) - (-((bv / 16 : ℝ) : ℂ))‖ = |lam i + bv / 16| := by
      intro i
      rw [sub_neg_eq_add, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
    have := GlobalTheory.norm_sum_eigenprojector_le_of_resolvent_bound H (Fin n) VV T p (fun i => (lam i : ℂ)) (univ.filter (fun a : Fin n => a.val + 1 < kk))
      (-((bv / 16 : ℝ) : ℂ)) (9 * bv / 16) (32 / (13 * bv)) hfd (by positivity) (by positivity)
      (fun x _ => hsum x) hp ?_ ?_ ?_ x hx
    · have e : 9 * bv / 16 * (32 / (13 * bv)) = 18 / 13 := by field_simp; norm_num
      rwa [e] at this
    · intro i hi
      have := (hpos i).1 (mem_filter.1 hi).2
      rw [hnorm, abs_lt]
      constructor <;> linarith [this.1, this.2]
    · intro i hi
      have hi' : kk ≤ i.val + 1 := by
        by_contra h
        exact hi (mem_filter.2 ⟨mem_univ _, not_le.1 h⟩)
      have := (hpos i).2 hi'
      rw [hnorm, lt_abs]
      left
      linarith [this.1, this.2]
    · intro ζ hζ y hy
      rw [sub_neg_eq_add] at hζ
      have h := hres ζ hζ y hy
      have e : ‖y‖ = 32 / (13 * bv) * (13 * bv / 32 * ‖y‖) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left h (by positivity)
  intro x hx
  refine ⟨h1 x hx, fun s hs => ?_⟩
  have hsN : s ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1) := mem_filter.2 ⟨mem_univ _, hs⟩
  have := GlobalTheory.norm_node_projector_le H (Fin n) VV T p (fun i => (lam i : ℂ))
    (univ.filter (fun a : Fin n => kk ≤ a.val + 1)) s (6 * bv) 3 hsN (by positivity) hp ?_ ?_ ?_ ?_ x hx
  · rw [card_erase_of_mem hsN, hcard] at this
    have e : n + 1 - kk - 1 = n - kk := by omega
    rwa [e] at this
  · intro y hy

    rw [← hsum y, map_sum]
    exact VV.sum_mem fun i _ => by rw [(hp i y hy).2]; exact VV.smul_mem _ (hp i y hy).1
  · intro i hi
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hgap s i (ne_of_mem_erase hi).symm
  · intro i hi y hy
    have hi' := (hpos i).2 (mem_filter.1 (mem_of_mem_erase hi)).2
    have h2 : |lam i| ≤ 3 * bv := by
      rw [abs_le]; constructor <;> linarith [hi'.1, hi'.2]
    calc ‖T y - (lam i : ℂ) • y‖ ≤ ‖T y‖ + ‖(lam i : ℂ) • y‖ := norm_sub_le _ _
      _ ≤ 3 * bv * ‖y‖ + 3 * bv * ‖y‖ := by
          refine add_le_add (hT y hy) ?_
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = 6 * bv * ‖y‖ := by ring
  · intro y hy
    have h3 := sum_filter_add_sum_filter_not univ (fun a : Fin n => a.val + 1 < kk) (fun i => p i y)
    rw [hsum y] at h3
    simp only [not_lt] at h3
    have h4 : ∑ i ∈ univ.filter (fun a : Fin n => kk ≤ a.val + 1), p i y =
        y - ∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y := by
      rw [eq_sub_iff_add_eq, add_comm]; exact h3
    rw [h4]
    have := h1 y hy
    have h5 := norm_sub_le y (∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), p s y)
    linarith [norm_nonneg y]

theorem cloud_node_projection_norm : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ d, ‖(∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), io s (pr s (Pi.single c w))) d‖ ^ 2 ≤ (18 / 13) ^ 2 * ‖w‖ ^ 2 ∧ ∀ s : Fin n, kk ≤ s.val + 1 → ∑ d, ‖io s (pr s (Pi.single c w)) d‖ ^ 2 ≤ (3 * (6 * bv) ^ (n - kk)) ^ 2 * ‖w‖ ^ 2 := by
  intro M _ _ n ε E N _ _ F io pr μ kk j bv w hM hF hA hS hj hw c
  obtain ⟨hb, -, hpos⟩ := GlobalTheory.shape_position n kk j ε μ bv hS (by omega)
  obtain ⟨L0, Ladd, Lsmul, -⟩ := GlobalTheory.lev_subspace_mono M n ε E μ hM.1 hM.2.1
  have hcomp := GlobalTheory.T.unitary_glModule_proj_components_level_add_two M n ε E N F io pr μ j w hM.2.1 (fun s => (hF s).2.1) hA hw
  have heig := GlobalTheory.splitCas_eigenvalue_summand M n ε E N F io pr μ hM hF hA
  have hnb : (n : ℝ) ≤ bv := by
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (by have := hS.2.1; omega : 1 ≤ n)
    have h2 : (n : ℝ) ≤ (n : ℝ) ^ 7 := le_self_pow₀ h1 (by norm_num)
    have h3 := hS.2.2.2.2.2
    have h4 : (0 : ℝ) ≤ (n : ℝ) ^ 7 := by positivity
    linarith
  have hcard := (GlobalTheory.card_filter_le_succ_and_sq_sum_le_pow n kk bv hS.1 hS.2.1 hnb).1
  let e : PiLp 2 (fun _ : Fin n => M) ≃ₗ[ℂ] (Fin n → M) := WithLp.linearEquiv 2 ℂ (Fin n → M)
  have hn : ∀ x : PiLp 2 (fun _ : Fin n => M), ‖x‖ ^ 2 = ∑ d, ‖e x d‖ ^ 2 := fun x => PiLp.norm_sq_eq_of_L2 _ x
  let T0 : (Fin n → M) →ₗ[ℂ] (Fin n → M) :=
    LinearMap.pi fun b => -∑ a, (E b a) ∘ₗ (LinearMap.proj a : (Fin n → M) →ₗ[ℂ] M)
  have hT0 : ∀ x, T0 x = splitCas E x := by
    intro x
    funext b
    simp [T0, splitCas]
  let T : PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M) := e.symm.toLinearMap ∘ₗ T0 ∘ₗ e.toLinearMap
  have hT : ∀ x, e (T x) = splitCas E (e x) := by
    intro x
    rw [← hT0]
    exact e.apply_symm_apply _
  let p : Fin n → PiLp 2 (fun _ : Fin n => M) →ₗ[ℂ] PiLp 2 (fun _ : Fin n => M) := fun s =>
    e.symm.toLinearMap ∘ₗ io s ∘ₗ pr s ∘ₗ e.toLinearMap
  have hp : ∀ s x, e (p s x) = io s (pr s (e x)) := fun s x => e.apply_symm_apply _
  let x₀ : PiLp 2 (fun _ : Fin n => M) := e.symm (Pi.single c w)
  have hx₀ : e x₀ = Pi.single c w := e.apply_symm_apply _
  have hx₀n : ‖x₀‖ ^ 2 = ‖w‖ ^ 2 := by
    rw [hn, hx₀, Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      simp [hd]
    · simp
  let VV : Submodule ℂ (PiLp 2 (fun _ : Fin n => M)) := Submodule.span ℂ (Set.range fun s => p s x₀)
  have hfd : FiniteDimensional ℂ VV := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hsum : ∀ x, ∑ i, p i x = x := by
    intro x
    apply e.injective

    rw [map_sum]
    simp only [hp]
    exact hA.sum_io_pr _
  have hx₀V : x₀ ∈ VV := by
    rw [← hsum x₀]
    exact VV.sum_mem fun i _ => Submodule.subset_span ⟨i, rfl⟩
  have hpV : ∀ i, ∀ x ∈ VV, p i x ∈ VV := by
    intro i x hx
    have : VV ≤ VV.comap (p i) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨s, rfl⟩
      show p i (p s x₀) ∈ VV
      by_cases h : i = s
      · subst h
        have : p i (p i x₀) = p i x₀ := by
          apply e.injective
          rw [hp, hp, hA.pr_io]
        rw [this]
        exact Submodule.subset_span ⟨i, rfl⟩
      · have : p i (p s x₀) = 0 := by
          apply e.injective
          rw [hp, hp, hA.pr_io_ne i s h, map_zero, map_zero]
        rw [this]
        exact VV.zero_mem
    exact this hx
  have hlev : ∀ x ∈ VV, ∀ d, Lev ε E μ (j + 2) (e x d) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      intro d
      rw [hp, hx₀]
      exact hcomp s c d
    | zero => intro d; rw [map_zero]; exact L0 _
    | add x y _ _ hx hy => intro d; rw [map_add (f := _)]; exact Ladd _ _ _ (hx d) (hy d)
    | smul a x _ hx => intro d; rw [map_smul]; exact Lsmul _ _ _ (hx d)
  have hres := fun x (hx : x ∈ VV) =>
    GlobalTheory.T.splitCasimir_resolvent_circle_bounds M n ε E μ kk (j + 2) bv (e x) hM hS (by omega) (hlev x hx)
  have key := cloud_node_projector_bound (PiLp 2 (fun _ : Fin n => M)) n kk bv VV T p
    (fun s => -μ s + (1 - (n : ℝ)) / 2) hfd hb hsum ?_ hpos ?_ hcard ?_ ?_ x₀ hx₀V
  · refine ⟨?_, fun s hs => ?_⟩
    · have h := pow_le_pow_left₀ (norm_nonneg _) key.1 2

      rw [mul_pow, hx₀n, hn, map_sum] at h
      simp only [hp, hx₀] at h
      exact h
    · have h := pow_le_pow_left₀ (norm_nonneg _) (key.2 s hs) 2
      rw [mul_pow, hx₀n, hn, hp, hx₀] at h
      exact h
  · intro i x hx
    refine ⟨hpV i x hx, ?_⟩
    apply e.injective
    rw [hT, map_smul, hp, heig]
  · intro a b hab
    rw [le_abs]
    rcases lt_or_gt_of_ne hab with h | h
    · right
      have := hS.2.2.1 a b h
      linarith
    · left
      have := hS.2.2.1 b a h
      linarith
  · intro ζ hζ x hx
    have h := (hres x hx).1 ζ hζ
    refine (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 ?_
    rw [mul_pow, hn, hn, map_sub, map_smul, hT]
    exact h
  · intro x hx
    have h := (hres x hx).2
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [mul_pow, hn, hn, hT]
    exact h

end GlobalTheory
end
end
