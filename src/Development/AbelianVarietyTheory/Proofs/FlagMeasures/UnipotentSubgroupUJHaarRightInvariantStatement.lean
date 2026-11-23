module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Mathlib.MeasureTheory.Group.ModularCharacter
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarMeasureOfSigmaFinite
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJHaarEntryBoundedPolynomialGrowth

section

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped Matrix

namespace GlobalTheory.UJGrowth

variable {n : ℕ} {ε : Fin n → Bool}

def ent (g : Formalism.REAL.UJ ε) : Fin n → Fin n → ℂ := Matrix.of.symm (Formalism.MainNotions.S.uMat g)

theorem ent_closedEmb : Topology.IsClosedEmbedding (ent (ε := ε)) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1

theorem mem_closedBall_iff_entries {x y : Fin n → Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ closedBall y R ↔ ∀ i j, ‖x i j - y i j‖ ≤ R := by
  rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hR]
  exact forall_congr' fun i => pi_norm_le_iff_of_nonneg hR

theorem mem_closedBall_zero_iff_entries {x : Fin n → Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ closedBall 0 R ↔ ∀ i j, ‖x i j‖ ≤ R := by
  rw [mem_closedBall_iff_entries hR]
  simp

theorem uMat_inv_mul' (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  rw [← show Formalism.MainNotions.S.uMat (g⁻¹ * g) = Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g from rfl, inv_mul_cancel]
  rfl

theorem uMat_mul_inv' (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  rw [← show Formalism.MainNotions.S.uMat (g * g⁻¹) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ from rfl, mul_inv_cancel]
  rfl

theorem uMat_inv_eq (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g⁻¹ = Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hf : (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : (Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε) * Formalism.MainNotions.S.uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.MainNotions.S.uMat g)ᴴ, hf,
      Formalism.REAL.Jm_mul_self]
  calc Formalism.MainNotions.S.uMat g⁻¹
      = ((Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε) * Formalism.MainNotions.S.uMat g) * Formalism.MainNotions.S.uMat g⁻¹ := by
        rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, uMat_mul_inv', Matrix.mul_one]

theorem norm_inv_entry (g : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖Formalism.MainNotions.S.uMat g⁻¹ i j‖ = ‖Formalism.MainNotions.S.uMat g j i‖ := by
  rw [uMat_inv_eq]
  unfold Formalism.REAL.Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem small_ball {S : Subgroup (Formalism.REAL.UJ ε)} {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (h : (n : ℝ) * (R * (2 * δ)) ≤ 1) (x : Fin n → Fin n → ℂ) :
    μ (ent ⁻¹' (closedBall 0 R ∩ closedBall x δ)) ≤
      μ (ent ⁻¹' closedBall (ent (1 : Formalism.REAL.UJ ε)) 1) := by
  by_cases hex : ∃ s ∈ ent ⁻¹' (closedBall 0 R ∩ closedBall x δ), s ∈ S
  · obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := hex
    have hme : MeasurableEmbedding (fun t : Formalism.REAL.UJ ε => s * t) :=
      (Homeomorph.mulLeft s).isClosedEmbedding.measurableEmbedding
    conv_lhs => rw [← hμ.2.2.2 s hs]
    rw [hme.map_apply]
    refine measure_mono fun t ht => ?_
    have ht2 : ent (s * t) ∈ closedBall x δ := ht.2
    have h1 : ent (s * t) ∈ closedBall (ent s) (2 * δ) := by
      have := dist_triangle_right (ent (s * t)) (ent s) x
      rw [mem_closedBall]
      linarith [mem_closedBall.1 ht2, mem_closedBall.1 hs2]
    rw [Set.mem_preimage, mem_closedBall_iff_entries zero_le_one]
    intro i j
    have e : Formalism.MainNotions.S.uMat t = Formalism.MainNotions.S.uMat s⁻¹ * Formalism.MainNotions.S.uMat (s * t) := by
      rw [show Formalism.MainNotions.S.uMat (s * t) = Formalism.MainNotions.S.uMat s * Formalism.MainNotions.S.uMat t from rfl, ← Matrix.mul_assoc,
        uMat_inv_mul', Matrix.one_mul]
    have e2 : Formalism.MainNotions.S.uMat t - 1 =
        Formalism.MainNotions.S.uMat s⁻¹ * (Formalism.MainNotions.S.uMat (s * t) - Formalism.MainNotions.S.uMat s) := by
      rw [Matrix.mul_sub, ← e, uMat_inv_mul']
    have e3 : ent t i j - ent (1 : Formalism.REAL.UJ ε) i j = (Formalism.MainNotions.S.uMat t - 1) i j := rfl
    rw [e3, e2, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ l ∈ (Finset.univ : Finset (Fin n)),
        ‖Formalism.MainNotions.S.uMat s⁻¹ i l * (Formalism.MainNotions.S.uMat (s * t) - Formalism.MainNotions.S.uMat s) l j‖ ≤ R * (2 * δ) :=
      fun l _ => by
        rw [norm_mul]
        refine mul_le_mul ?_ ?_ (norm_nonneg _) hR
        · rw [norm_inv_entry]
          exact (mem_closedBall_zero_iff_entries hR).1 hs1 l i
        · exact (mem_closedBall_iff_entries (by linarith)).1 h1 l j
    refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
    simpa using h
  · rw [measure_mono_null (t := (S : Set (Formalism.REAL.UJ ε))ᶜ) (fun s hs hS => hex ⟨s, hs, hS⟩) hμ.2.2.1]
    exact zero_le

end GlobalTheory.UJGrowth

namespace GlobalTheory.UJGrowth

theorem growth : ∀ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)),
    IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε),
    Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → IsFiniteMeasureOnCompacts μ →
    ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R →
      μ {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  intro n ε S _ μ hμ hfin
  haveI := hμ.1
  have hemb : Topology.IsClosedEmbedding (ent (ε := ε)) := ent_closedEmb
  let ν : Measure (Fin n → Fin n → ℂ) := μ.map ent
  have hνA : ∀ A, MeasurableSet A → ν A = μ (ent ⁻¹' A) := fun A hA =>
    Measure.map_apply hemb.continuous.measurable hA
  have hcpt : ∀ y r, μ (ent ⁻¹' closedBall y r) < ⊤ := fun y r =>
    (hemb.isCompact_preimage (isCompact_closedBall y r)).measure_lt_top
  haveI : SigmaFinite ν := hemb.measurableEmbedding.sigmaFinite_map
  set M := μ (ent ⁻¹' closedBall (ent (1 : Formalism.REAL.UJ ε)) 1) with hM
  have hMf : M ≠ ⊤ := (hcpt _ _).ne
  set N : ℝ := (n : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by rw [hN]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set d := Module.finrank ℝ (Fin n → Fin n → ℂ)
  let lam : Measure (Fin n → Fin n → ℂ) := Measure.addHaar
  refine ⟨M.toReal * (4 * N) ^ d, 2 * d, fun R hR => ?_⟩
  set δ := (2 * N * R)⁻¹ with hδ
  have hp : 1 ≤ 2 * N * R := by nlinarith
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ hp
  have hcond : (n : ℝ) * (R * (2 * δ)) ≤ 1 := by
    have e : (n : ℝ) * (R * (2 * δ)) = n / N := by
      rw [hδ]; field_simp
    rw [e, div_le_one (by linarith)]
    linarith
  have hsb : ∀ x, ν (closedBall 0 R ∩ closedBall x δ) ≤ M := fun x => by
    rw [hνA _ (measurableSet_closedBall.inter measurableSet_closedBall)]
    exact small_ball hμ (by linarith) hδ0.le hcond x
  have hset : {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} = ent ⁻¹' closedBall 0 R := by
    ext g
    rw [Set.mem_preimage, mem_closedBall_zero_iff_entries (by linarith)]
    rfl
  rw [hset, ← hνA _ measurableSet_closedBall]
  let W : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) := {p | p.1 ∈ closedBall 0 R ∧ dist p.1 p.2 ≤ δ}
  have hW : MeasurableSet W :=
    ((isClosed_closedBall.preimage continuous_fst).inter
      (isClosed_le continuous_dist continuous_const)).measurableSet
  have e1 : (ν.prod lam) W = lam (closedBall 0 δ) * ν (closedBall 0 R) := by
    rw [Measure.prod_apply hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ closedBall (0 : Fin n → Fin n → ℂ) R
    · rw [Set.indicator_of_mem hs, ← Measure.addHaar_closedBall_center lam s]
      congr 1
      ext x
      exact ⟨fun h => mem_closedBall'.2 h.2, fun h => ⟨hs, mem_closedBall'.1 h⟩⟩
    · rw [Set.indicator_of_notMem hs]
      have : Prod.mk s ⁻¹' W = ∅ := by
        ext x
        simp only [W, Set.mem_preimage, Set.mem_setOf_eq, hs, false_and, Set.mem_empty_iff_false]
      rw [this, measure_empty]
  have e2 : (ν.prod lam) W ≤ M * lam (closedBall 0 (2 * R)) := by
    rw [Measure.prod_apply_symm hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall (0 : Fin n → Fin n → ℂ) (2 * R)
    · rw [Set.indicator_of_mem hx]
      exact hsb x
    · have : (fun s => (s, x)) ⁻¹' W = ∅ := by
        ext s
        simp only [W, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, mem_closedBall]
        rintro ⟨h1, h2⟩
        apply hx
        have := dist_triangle_left x 0 s
        rw [mem_closedBall]; linarith
      simp [this]
  rw [e1, Measure.addHaar_closedBall lam _ hδ0.le, Measure.addHaar_closedBall lam _ (by linarith)] at e2
  have hb0 : 0 < (lam (ball 0 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos lam _ one_pos).ne' measure_ball_lt_top.ne
  have e3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hMf
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)) e2
  simp only [ENNReal.toReal_mul] at e3
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at e3
  have e4 : δ ^ d * (ν (closedBall 0 R)).toReal ≤ M.toReal * (2 * R) ^ d := by
    refine le_of_mul_le_mul_right ?_ hb0
    calc _ = δ ^ d * (lam (ball 0 1)).toReal * (ν (closedBall 0 R)).toReal := by ring
      _ ≤ _ := e3
      _ = _ := by ring
  have e5 : M.toReal * (2 * R) ^ d = δ ^ d * (M.toReal * (4 * N) ^ d * R ^ (2 * d)) := by
    have : 2 * R = δ * (4 * N) * R ^ 2 := by rw [hδ]; field_simp; ring
    rw [this, mul_pow, mul_pow, pow_mul]; ring
  rw [e5] at e4
  have e6 := le_of_mul_le_mul_left e4 (by positivity)
  have hνf : ν (closedBall 0 R) ≠ ⊤ := by
    rw [hνA _ measurableSet_closedBall]; exact (hcpt _ _).ne
  rw [← ENNReal.ofReal_toReal hνf]
  exact ENNReal.ofReal_le_ofReal e6

end GlobalTheory.UJGrowth
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJHaarEntryBoundedPolynomialGrowthStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.unitaryJ_haar_entryBounded_polynomial_growth : ∀ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → IsFiniteMeasureOnCompacts μ → ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R → μ {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  first | exact @GlobalTheory.UJGrowth.growth | exact GlobalTheory.UJGrowth.growth | (intros; apply GlobalTheory.UJGrowth.growth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupUJHaarRightInvariant

section

@[expose] public section

open MeasureTheory

noncomputable section

open scoped ENNReal NNReal

namespace GlobalTheory.UJUnimod

variable {n : ℕ}

def Bd (a : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) : Prop := ∀ i j, ‖a i j‖ ≤ R

theorem Bd.mul {a b : Matrix (Fin n) (Fin n) ℂ} {R R' : ℝ} (ha : Bd a R) (hb : Bd b R') :
    Bd (a * b) ((n : ℝ) * (R * R')) := by
  intro i j
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ (Finset.univ : Finset (Fin n)), ‖a i l * b l j‖ ≤ R * R' := fun l _ => by
    rw [norm_mul]
    exact mul_le_mul (ha i l) (hb l j) (norm_nonneg _) ((norm_nonneg _).trans (ha i l))
  simpa using Finset.sum_le_card_nsmul _ _ _ this

theorem bd_pow {g : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} (hg : (g - 1) ^ m = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, Bd (g ^ j) (B * ((j : ℝ) + 1) ^ (m + 1)) := by
  set X := g - 1 with hX
  have e : g = X + 1 := by simp [hX]
  refine ⟨∑ l ∈ Finset.range m, ∑ i, ∑ j, ‖(X ^ l) i j‖, by positivity, fun p i j => ?_⟩
  set B := ∑ l ∈ Finset.range m, ∑ i, ∑ j, ‖(X ^ l) i j‖ with hB
  have hB0 : 0 ≤ B := by positivity
  rw [e, (Commute.one_right X).add_pow, Matrix.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ Finset.range (p + 1), ‖(X ^ l * 1 ^ (p - l) * (p.choose l : Matrix (Fin n) (Fin n) ℂ)) i j‖ ≤
      B * ((p : ℝ) + 1) ^ m := fun l _ => by
    by_cases hl : l < m
    · have h1 : ‖(X ^ l) i j‖ ≤ B :=
        ((Finset.single_le_sum (f := fun j => ‖(X ^ l) i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i => ∑ j, ‖(X ^ l) i j‖) (fun _ _ => by positivity)
            (Finset.mem_univ i))).trans
          (Finset.single_le_sum (f := fun l => ∑ i, ∑ j, ‖(X ^ l) i j‖) (fun _ _ => by positivity)
            (Finset.mem_range.2 hl))
      have h2 : (p.choose l : ℝ) ≤ ((p : ℝ) + 1) ^ m := by
        have h3 : (p.choose l : ℝ) ≤ (p : ℝ) ^ l := by exact_mod_cast Nat.choose_le_pow p l
        have h4 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        exact h3.trans ((pow_le_pow_left₀ h4 (by linarith) l).trans (pow_le_pow_right₀ (by linarith) hl.le))
      rw [one_pow, mul_one, ← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul, norm_mul, Complex.norm_natCast,
        mul_comm]
      exact mul_le_mul h1 h2 (Nat.cast_nonneg _) hB0
    · rw [pow_eq_zero_of_le (not_lt.1 hl) hg]
      simp only [zero_mul, Matrix.zero_apply, norm_zero]
      positivity
  refine (Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)
  simp only [Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.UJUnimod

namespace GlobalTheory.UJUnimod

theorem unimodular_of_unipotent : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ) (S : Subgroup (Formalism.REAL.UJ ε)),
    IsClosed (S : Set (Formalism.REAL.UJ ε)) → (∀ g ∈ S, (Formalism.MainNotions.S.uMat g - 1) ^ m = 0) →
    ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ →
    ∀ s ∈ S, μ.map (fun x => x * s) = μ := by
  intro n ε m S hS hu μ hμ
  obtain ⟨hσ, h0, hc, hl⟩ := hμ
  have hce : Topology.IsClosedEmbedding S.subtype := hS.isClosedEmbedding_subtypeVal
  have hφ : MeasurableEmbedding S.subtype := hce.measurableEmbedding
  haveI : LocallyCompactSpace S := hce.locallyCompactSpace
  haveI : SecondCountableTopology S := hce.isEmbedding.secondCountableTopology
  have h2 : (μ.comap S.subtype).map S.subtype = μ := by
    rw [hφ.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : Set.range S.subtype = (S : Set (Formalism.REAL.UJ ε)) := Subtype.range_coe
    rw [this]
    exact hc
  set ν : Measure S := μ.comap S.subtype with hν
  haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : Formalism.REAL.UJ ε => (g : Formalism.REAL.UJ ε) * x := measurable_const_mul _
    rw [Measure.map_map hφ.measurable (measurable_const_mul g), h2]
    conv_rhs => rw [← hl g g.2, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsHaarMeasure :=
    GlobalTheory.SnMass.ProdQuot.isHaarMeasure_of_sigmaFinite ν fun h => h0 (by rw [← h2, h, Measure.map_zero])
  have hfin : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [← h2, hφ.map_apply]
    exact (hce.isCompact_preimage hK).measure_lt_top⟩

  have hmod : ∀ s : S, μ.map (fun x => x * (s : Formalism.REAL.UJ ε)) =
      (Measure.modularCharacter s : ℝ≥0∞) • μ := by
    intro s
    have e1 : ν.map (· * s) = (Measure.modularCharacter s : ℝ≥0∞) • ν := by
      rw [show (Measure.modularCharacter s : ℝ≥0) = Measure.modularCharacterFun s from rfl,
        Measure.modularCharacterFun_eq_haarScalarFactor ν s]
      exact Measure.isMulLeftInvariant_eq_smul _ ν
    conv_lhs => rw [← h2]
    rw [Measure.map_map (measurable_mul_const _) hφ.measurable]
    have : (fun x : Formalism.REAL.UJ ε => x * (s : Formalism.REAL.UJ ε)) ∘ S.subtype = S.subtype ∘ (· * s) := by
      funext x; rfl
    rw [this, ← Measure.map_map hφ.measurable (measurable_mul_const _), e1, Measure.map_smul, h2]
    exact hφ.measurable.aemeasurable

  have key : ∀ s : S, Measure.modularCharacter s ≤ 1 := by
    intro s
    set Δ := Measure.modularCharacter s with hΔ
    obtain ⟨C, D, hgr⟩ := GlobalTheory.T.unitaryJ_haar_entryBounded_polynomial_growth ε S hS μ ⟨hσ, h0, hc, hl⟩ hfin
    obtain ⟨B, hB, hpow⟩ := bd_pow (hu _ (S.inv_mem s.2))
    let Bx : ℝ → Set (Formalism.REAL.UJ ε) := fun R => {g | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R}
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, μ (Bx ((ρ : ℝ) + 1)) ≠ 0 := by
      by_contra! h
      apply h0
      rw [← Measure.measure_univ_eq_zero]
      have : (Set.univ : Set (Formalism.REAL.UJ ε)) = ⋃ ρ : ℕ, Bx ((ρ : ℝ) + 1) := by
        ext g
        simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
        obtain ⟨N, hN⟩ := exists_nat_ge (∑ i, ∑ j, ‖Formalism.MainNotions.S.uMat g i j‖)
        refine ⟨N, fun i j => ?_⟩
        have := (Finset.single_le_sum (f := fun j => ‖Formalism.MainNotions.S.uMat g i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖Formalism.MainNotions.S.uMat g i j‖)
          (fun _ _ => by positivity) (Finset.mem_univ i))
        linarith
      rw [this]
      exact measure_iUnion_null h
    set ρ' : ℝ := (ρ : ℝ) + 1 with hρ'
    have hρ1 : 1 ≤ ρ' := by rw [hρ']; linarith [Nat.cast_nonneg (α := ℝ) ρ]
    obtain ⟨C', hC', hgr'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ R : ℝ, 1 ≤ R → (μ (Bx R)).toReal ≤ C' * R ^ D ∧ μ (Bx R) < ⊤ := by
      refine ⟨max C 0, le_max_right _ _, fun R hR => ?_⟩
      have h1 : μ (Bx R) ≤ ENNReal.ofReal (max C 0 * R ^ D) :=
        (hgr R hR).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
      refine ⟨?_, h1.trans_lt ENNReal.ofReal_lt_top⟩
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hv : 0 < (μ (Bx ρ')).toReal := ENNReal.toReal_pos hρ (hgr' ρ' hρ1).2.ne
    set K : ℝ := ((n : ℝ) + 1) * ρ' * (B + 1) with hK
    have hK1 : 1 ≤ K := by
      rw [hK]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have h2 : (1 : ℝ) ≤ B + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    have hU : ∀ (a : Formalism.REAL.UJ ε) (j : ℕ), Formalism.MainNotions.S.uMat (a ^ j) = Formalism.MainNotions.S.uMat a ^ j := fun a j =>
      map_pow ((Units.coeHom (Matrix (Fin n) (Fin n) ℂ)).comp (Formalism.REAL.UJ ε).subtype) a j
    have em : ∀ j : ℕ, μ.map (fun x => x * ((s : Formalism.REAL.UJ ε) ^ j)) = ((Δ : ℝ≥0∞) ^ j) • μ := by
      intro j
      have := hmod (s ^ j)
      rw [map_pow] at this
      simpa using this
    have key2 : ∀ j : ℕ, (Δ : ℝ) ^ j * (μ (Bx ρ')).toReal ≤ C' * K ^ D * ((j : ℝ) + 1) ^ ((m + 1) * D) := by
      intro j
      have ht : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ (m + 1) := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])
      have hme : MeasurableEmbedding (fun x : Formalism.REAL.UJ ε => x * ((s : Formalism.REAL.UJ ε) ^ j)) :=
        (Homeomorph.mulRight ((s : Formalism.REAL.UJ ε) ^ j)).measurableEmbedding
      have h1 : (((Δ : ℝ≥0∞) ^ j) • μ) (Bx ρ') ≤ μ (Bx (K * ((j : ℝ) + 1) ^ (m + 1))) := by
        rw [← em, hme.map_apply]
        refine measure_mono fun x hx => ?_
        have hx' : x = (x * (s : Formalism.REAL.UJ ε) ^ j) * ((s : Formalism.REAL.UJ ε)⁻¹) ^ j := by
          rw [mul_assoc, inv_pow, mul_inv_cancel, mul_one]
        have h2 := (show Bd (Formalism.MainNotions.S.uMat (x * (s : Formalism.REAL.UJ ε) ^ j)) ρ' from hx).mul (hpow j)
        have h3 : Formalism.MainNotions.S.uMat x = Formalism.MainNotions.S.uMat (x * (s : Formalism.REAL.UJ ε) ^ j) *
            Formalism.MainNotions.S.uMat (((s : S)⁻¹ : S) : Formalism.REAL.UJ ε) ^ j := by
          rw [← hU]
          conv_lhs => rw [hx']
          rfl
        intro i k
        rw [h3]
        refine (h2 i k).trans ?_
        rw [hK]
        have hB' : B ≤ B + 1 := by linarith
        have hn' : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
        have h0ρ : 0 ≤ ρ' := by linarith
        calc (n : ℝ) * (ρ' * (B * ((j : ℝ) + 1) ^ (m + 1))) = (n : ℝ) * ρ' * B * ((j : ℝ) + 1) ^ (m + 1) := by ring
          _ ≤ ((n : ℝ) + 1) * ρ' * (B + 1) * ((j : ℝ) + 1) ^ (m + 1) := by gcongr
      have hR1 : 1 ≤ K * ((j : ℝ) + 1) ^ (m + 1) := by nlinarith
      have h2 := (ENNReal.toReal_mono (hgr' _ hR1).2.ne h1).trans (hgr' _ hR1).1
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, mul_pow, ← pow_mul,
        ← mul_assoc] at h2
      simpa using h2
    by_contra! h1
    have h2 : 1 < (Δ : ℝ) := by exact_mod_cast h1
    have h3 := ((tendsto_pow_const_div_const_pow_of_one_lt ((m + 1) * D) h2).comp
      (Filter.tendsto_add_atTop_nat 1)).const_mul (C' * K ^ D * (Δ : ℝ))
    rw [mul_zero] at h3
    obtain ⟨j, hj⟩ := (h3.eventually (gt_mem_nhds hv)).exists
    have h4 := key2 j
    have h5 : 0 < (Δ : ℝ) ^ j := by positivity
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hj
    have h6 : C' * K ^ D * (Δ : ℝ) * (((j : ℝ) + 1) ^ ((m + 1) * D) / (Δ : ℝ) ^ (j + 1)) =
        C' * K ^ D * ((j : ℝ) + 1) ^ ((m + 1) * D) / (Δ : ℝ) ^ j := by
      have : (Δ : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [h6, div_lt_iff₀ h5] at hj
    linarith
  intro s hs
  have e1 := key ⟨s, hs⟩
  have e2 := key (⟨s, hs⟩ : S)⁻¹
  have e3 : Measure.modularCharacter (⟨s, hs⟩ : S) = 1 := by
    have := map_mul Measure.modularCharacter (⟨s, hs⟩ : S) (⟨s, hs⟩ : S)⁻¹
    rw [mul_inv_cancel, map_one] at this
    refine le_antisymm e1 ?_
    calc (1 : ℝ≥0) = _ := this
      _ ≤ Measure.modularCharacter (⟨s, hs⟩ : S) * 1 := mul_le_mul_of_nonneg_left e2 zero_le
      _ = _ := mul_one _
  have := hmod ⟨s, hs⟩
  rw [e3] at this
  simpa using this

end GlobalTheory.UJUnimod
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupUJHaarRightInvariantStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.unipotent_subgroup_UJ_haar_right_invariant : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → (∀ g ∈ S, (Formalism.MainNotions.S.uMat g - 1) ^ m = 0) → ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → ∀ s ∈ S, μ.map (fun x => x * s) = μ := by
  first | exact @GlobalTheory.UJUnimod.unimodular_of_unipotent | exact GlobalTheory.UJUnimod.unimodular_of_unipotent | (intros; apply GlobalTheory.UJUnimod.unimodular_of_unipotent <;> assumption)
end
end
