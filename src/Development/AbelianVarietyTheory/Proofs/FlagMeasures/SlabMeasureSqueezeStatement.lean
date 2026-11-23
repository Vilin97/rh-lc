module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNearestPointCosetOrthogonalLieAlgebra
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNearOneCompactNearLeviIntersection
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutOutSubgroupTangentSecondOrderHilbertSchmidtStatement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNearestPointCosetOrthogonalLieAlgebraStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.exists_nearest_point_coset_orthogonal_lieAlgebra : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → S ⊆ maxK ε → (∀ i, (E i)ᴴ = -E i) → ∀ k ∈ maxK ε, ∃ l ∈ S, crd E (uMat (l * k) - 1) = 0 ∧ ∀ l' ∈ S, nrm (uMat (l * k) - 1) ≤ nrm (uMat (l' * k) - 1) := by
  first | exact @GlobalTheory.IwConstMin.exists_nearest | exact GlobalTheory.IwConstMin.exists_nearest | (intros; apply GlobalTheory.IwConstMin.exists_nearest <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaNearOneCompactNearLeviIntersectionStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.iwasawa_near_one_compact_near_levi_intersection : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ t : ℝ, 0 < t → ∃ r : ℝ, 0 < r ∧ ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, nrm (uMat (u * m * k) - 1) ≤ r → ∃ l ∈ maxK ε ∩ flagM ε W, nrm (uMat (l * k) - 1) < t := by
  first | exact @GlobalTheory.IwConst.CloseLevi.close_levi | exact GlobalTheory.IwConst.CloseLevi.close_levi | (intros; apply GlobalTheory.IwConst.CloseLevi.close_levi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaSlabSqueezedBetweenBalls

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem slab_arith_lower {a s r t η u v : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (hst : s < t) (hrt : r < t)
    (ht : t ≤ 1 / 24) (hη : 0 < η) (htη : 3 * t * (1 + η) ≤ η) (h1 : a < 1 / 8 + s + a * s)
    (h2 : a ≤ u + a ^ 2) (h3 : u ≤ v + a * s) (h4 : v ≤ r) : a ≤ (1 + η) * r := by

  have hs24 : s < 1 / 24 := lt_of_lt_of_le hst ht
  have hA : a < 4 / 23 := by nlinarith [mul_nonneg ha (sub_nonneg.2 hs24.le)]
  have hkey : a * (1 - s - a) ≤ r := by nlinarith
  have hgap : 433 / 552 ≤ 1 - s - a := by linarith
  have hat : a * (433 / 552) < t := by nlinarith [mul_le_mul_of_nonneg_left hgap ha]
  have hsum : (1 + η) * (s + a) ≤ η := by
    nlinarith [mul_le_mul_of_nonneg_left (show s + a ≤ 3 * t by linarith) (show (0 : ℝ) ≤ 1 + η by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ 1 + η by linarith),
    mul_le_mul_of_nonneg_left hsum ha]

theorem slab_squeeze : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η →
    ∃ t : ℝ, 0 < t ∧ ∀ r : ℝ, 0 < r → r < t → ∀ k : Formalism.REAL.UJ ε, nrm (uMat k - 1) < t →
      crd E (uMat k - 1) = 0 → ∀ l ∈ S, (l ∈ hsBall ε (r / (1 + η)) → l * k ∈ slab ε E ρ r) ∧
        (l * k ∈ slab ε E ρ r → l ∈ hsBall ε ((1 + η) * r)) := by
  intro n ε S d E hS ρ η hρ hρ8 hη
  have hON := hS.isON
  obtain ⟨t, ht0, ht24, htη, htρ⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 24 ∧ 3 * t * (1 + η) ≤ η ∧ 3 * t ≤ ρ := by
    refine ⟨min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)),
      lt_min (by norm_num) (lt_min (by positivity) (by positivity)), min_le_left _ _, ?_, ?_⟩
    · have h : min (1 / 24) (min (η / (3 * (1 + η))) (ρ / 3)) * (3 * (1 + η)) ≤ η :=
        (le_div_iff₀ (by positivity)).1 (le_trans (min_le_right _ _) (min_le_left _ _))
      linarith
    · have h := le_trans (min_le_right (1 / 24 : ℝ) _) (min_le_right (η / (3 * (1 + η))) (ρ / 3))
      linarith
  refine ⟨t, ht0, ?_⟩
  intro r hr hrt k hk hk0 l hl

  have hmul : uMat (l * k) - 1 = (uMat l - 1) + (uMat k - 1) + (uMat l - 1) * (uMat k - 1) := by
    have e : uMat (l * k) = uMat l * uMat k := rfl
    rw [e]; noncomm_ring
  have hXY : nrm ((uMat l - 1) * (uMat k - 1)) ≤ nrm (uMat l - 1) * nrm (uMat k - 1) := nrm_mul_le _ _
  have ha0 := nrm_nonneg (uMat l - 1)
  have hs0 := nrm_nonneg (uMat k - 1)
  have htle : t ≤ η := by nlinarith
  constructor
  · intro hlB
    have ha : nrm (uMat l - 1) ≤ r / (1 + η) := hlB
    have ha' : nrm (uMat l - 1) * (1 + η) ≤ r := (le_div_iff₀ (by positivity)).1 ha
    refine ⟨?_, ?_⟩
    ·
      have h1 : nrm (uMat (l * k) - 1) ≤ nrm (uMat l - 1) + nrm (uMat k - 1) + nrm ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul]
        exact le_trans (nrm_add_le _ _) (by linarith [nrm_add_le (uMat l - 1) (uMat k - 1)])
      have hat : nrm (uMat l - 1) < t := by nlinarith
      have hprod : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ t * t := by
        exact mul_le_mul hat.le hk.le hs0 ht0.le
      nlinarith
    ·
      have hc : crd E (uMat (l * k) - 1) = crd E (uMat l - 1) + crd E ((uMat l - 1) * (uMat k - 1)) := by
        rw [hmul, crd_add, crd_add, hk0, add_zero]
      have hlen : len (crd E (uMat (l * k) - 1)) ≤ nrm (uMat l - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
        rw [hc]
        exact le_trans (len_add_le _ _)
          (add_le_add (len_crd_le hON _) (le_trans (len_crd_le hON _) hXY))
      have hsη : nrm (uMat l - 1) * nrm (uMat k - 1) ≤ nrm (uMat l - 1) * η :=
        mul_le_mul_of_nonneg_left (by linarith) ha0
      show len (crd E (uMat (l * k) - 1)) ≤ r
      nlinarith
  · intro hslab
    obtain ⟨hZ, hv⟩ := hslab
    show nrm (uMat l - 1) ≤ (1 + η) * r
    have hX : uMat l - 1 = (uMat (l * k) - 1) - (uMat k - 1) - (uMat l - 1) * (uMat k - 1) := by
      rw [hmul]; abel

    have h1 : nrm (uMat l - 1) < 1 / 8 + nrm (uMat k - 1) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have e := nrm_sub_le ((uMat (l * k) - 1) - (uMat k - 1)) ((uMat l - 1) * (uMat k - 1))
      have e' := nrm_sub_le (uMat (l * k) - 1) (uMat k - 1)
      rw [← hX] at e
      linarith

    have h2 : nrm (uMat l - 1) ≤ len (crd E (uMat l - 1)) + nrm (uMat l - 1) ^ 2 := by
      have hp := GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt n ε S d E hS l hl
      have e := nrm_add_le (cmb E (crd E (uMat l - 1))) (uMat l - 1 - cmb E (crd E (uMat l - 1)))
      rw [add_sub_cancel, nrm_cmb hON] at e
      linarith

    have h3 : len (crd E (uMat l - 1)) ≤ len (crd E (uMat (l * k) - 1)) + nrm (uMat l - 1) * nrm (uMat k - 1) := by
      have hc : crd E (uMat l - 1) = crd E (uMat (l * k) - 1) + -crd E ((uMat l - 1) * (uMat k - 1)) := by
        conv_lhs => rw [hX]
        rw [crd_sub, crd_sub, hk0, sub_zero, sub_eq_add_neg]
      rw [hc]
      refine le_trans (len_add_le _ _) (add_le_add le_rfl ?_)
      rw [len_neg]
      exact le_trans (len_crd_le hON _) hXY
    exact slab_arith_lower ha0 hs0 hk hrt ht24 hη htη (by linarith) h2 h3 hv

end GlobalTheory.IwConst
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaSlabSqueezedBetweenBallsStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.iwasawa_slab_squeezed_between_balls : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η → ∃ t : ℝ, 0 < t ∧ ∀ r : ℝ, 0 < r → r < t → ∀ k : Formalism.REAL.UJ ε, nrm (uMat k - 1) < t → crd E (uMat k - 1) = 0 → ∀ l ∈ S, (l ∈ hsBall ε (r / (1 + η)) → l * k ∈ slab ε E ρ r) ∧ (l * k ∈ slab ε E ρ r → l ∈ hsBall ε ((1 + η) * r)) := by
  first | exact @GlobalTheory.IwConst.slab_squeeze | exact GlobalTheory.IwConst.slab_squeeze | (intros; apply GlobalTheory.IwConst.slab_squeeze <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SlabMeasureSqueeze

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem slab_measure_squeeze : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε (maxK ε ∩ flagM ε W) E → (∀ i, (E i)ᴴ = -E i) → ∀ ν : Measure (Formalism.REAL.UJ ε), ν (maxK ε ∩ flagM ε W)ᶜ = 0 → (∀ l ∈ maxK ε ∩ flagM ε W, ν.map (fun g => g * l) = ν) → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η → ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, u * m * k ∈ hsBall ε r → ν (hsBall ε (r / (1 + η))) ≤ ν {l | l * k ∈ slab ε E ρ r} ∧ ν {l | l * k ∈ slab ε E ρ r} ≤ ν (hsBall ε ((1 + η) * r)) := by
  intro n ε a j W hW d E hcut hskew ν hν hinv ρ η hρ hρ8 hη
  set S := maxK ε ∩ flagM ε W with hS
  obtain ⟨t, ht, hsq⟩ := GlobalTheory.T.iwasawa_slab_squeezed_between_balls n ε S d E hcut ρ η hρ hρ8 hη
  obtain ⟨r0, hr0, hnear⟩ := GlobalTheory.T.iwasawa_near_one_compact_near_levi_intersection n ε a j W hW t ht
  have hmem : Set.Iio (min t r0) ∈ nhds (0 : ℝ) := Iio_mem_nhds (lt_min ht hr0)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hmem] with r hr hr' u hu m hm k hk hball
  have hrpos : (0 : ℝ) < r := hr
  have hrlt : r < min t r0 := hr'
  have hrt : r < t := lt_of_lt_of_le hrlt (min_le_left _ _)
  have hrr0 : r < r0 := lt_of_lt_of_le hrlt (min_le_right _ _)

  have hb : nrm (uMat (u * m * k) - 1) ≤ r := hball
  obtain ⟨l0, hl0S, hl0⟩ := hnear u hu m hm k hk (le_trans hb hrr0.le)

  obtain ⟨l1, hl1S, hcrd, hmin⟩ := GlobalTheory.T.exists_nearest_point_coset_orthogonal_lieAlgebra n ε S d E hcut (fun x hx => hx.1) hskew k hk
  have hnrm : nrm (uMat (l1 * k) - 1) < t := lt_of_le_of_lt (hmin l0 hl0S) hl0
  have key := fun l (hl : l ∈ S) => hsq r hrpos hrt (l1 * k) hnrm hcrd l hl

  have hA : ν {l | l * k ∈ slab ε E ρ r} = ν {l | l * (l1 * k) ∈ slab ε E ρ r} := by
    calc ν {l | l * k ∈ slab ε E ρ r}
        = (ν.map (fun g => g * l1)) {l | l * k ∈ slab ε E ρ r} := by rw [hinv l1 hl1S]
      _ = ν ((fun g => g * l1) ⁻¹' {l | l * k ∈ slab ε E ρ r}) :=
          (Homeomorph.mulRight l1).toMeasurableEquiv.map_apply _
      _ = ν {l | l * (l1 * k) ∈ slab ε E ρ r} := by
          congr 1
          ext l
          simp only [Set.mem_preimage, Set.mem_setOf_eq, mul_assoc]
  rw [hA]
  constructor
  · calc ν (hsBall ε (r / (1 + η)))
        ≤ ν (hsBall ε (r / (1 + η)) ∩ S ∪ Sᶜ) := by
          apply measure_mono
          intro l hl
          by_cases h : l ∈ S
          · exact Or.inl ⟨hl, h⟩
          · exact Or.inr h
      _ ≤ ν (hsBall ε (r / (1 + η)) ∩ S) + ν Sᶜ := measure_union_le _ _
      _ = ν (hsBall ε (r / (1 + η)) ∩ S) := by rw [hν, add_zero]
      _ ≤ ν {l | l * (l1 * k) ∈ slab ε E ρ r} :=
          measure_mono (fun l hl => (key l hl.2).1 hl.1)
  · calc ν {l | l * (l1 * k) ∈ slab ε E ρ r}
        ≤ ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S ∪ Sᶜ) := by
          apply measure_mono
          intro l hl
          by_cases h : l ∈ S
          · exact Or.inl ⟨hl, h⟩
          · exact Or.inr h
      _ ≤ ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S) + ν Sᶜ := measure_union_le _ _
      _ = ν ({l | l * (l1 * k) ∈ slab ε E ρ r} ∩ S) := by rw [hν, add_zero]
      _ ≤ ν (hsBall ε ((1 + η) * r)) :=
          measure_mono (fun l hl => (key l hl.2).2 hl.1)

end GlobalTheory.IwConst
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SlabMeasureSqueezeStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.slab_measure_squeeze' : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε (maxK ε ∩ flagM ε W) E → (∀ i, (E i)ᴴ = -E i) → ∀ ν : Measure (Formalism.REAL.UJ ε), ν (maxK ε ∩ flagM ε W)ᶜ = 0 → (∀ l ∈ maxK ε ∩ flagM ε W, ν.map (fun g => g * l) = ν) → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η → ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, u * m * k ∈ hsBall ε r → ν (hsBall ε (r / (1 + η))) ≤ ν {l | l * k ∈ slab ε E ρ r} ∧ ν {l | l * k ∈ slab ε E ρ r} ≤ ν (hsBall ε ((1 + η) * r)) := by
  first | exact @GlobalTheory.IwConst.slab_measure_squeeze | exact GlobalTheory.IwConst.slab_measure_squeeze | (intros; apply GlobalTheory.IwConst.slab_measure_squeeze <;> assumption)
end
end
