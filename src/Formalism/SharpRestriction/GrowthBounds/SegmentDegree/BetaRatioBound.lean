module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.TauDegreeOnPathBound
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DiscriminantNonzeroModUniformiser
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.DistAddTwoLeOfSameVec
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FourHundredSixteenLeA
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.FrameZeroStrictMono
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.PsiCutSupported
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ReflectionMemGlevCastSucc
import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.StrictMonoIntExists
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementN

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def Consequences : Prop :=
  ∀ (r K Ns p E0 mS : ℕ) (a Y Q : ℝ), 2 ≤ r → 4 * r ≤ Ns → 13 ≤ p → 1 ≤ Y → 1 ≤ Q →
    1088 * (Ns : ℝ) ^ 2 * Real.log a ≤ ((r + K : ℕ) : ℝ) →
    32 * p * Y * ((r + K : ℕ) : ℝ) ^ 2 * Ns * Q ^ 2 * ((E0 : ℝ) + mS + 1) ≤ a →
    8 ≤ Ns ∧ 416 ≤ a ∧ 1 ≤ Real.log a ∧ 1088 * Ns ^ 2 ≤ r + K ∧
    160 * (Ns : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * Y ∧ 5 * Ns ≤ r + K ∧ 32 * Y ≤ a ∧ 8 * (Ns : ℝ) ≤ a ∧
    32 * (E0 : ℝ) ≤ a ∧ r + K ≤ 2 * (K - 2 * Ns) ∧ Ns + r ≤ K

def PowMulFloorDivLe : Prop :=
  ∀ (p k Dt Do ao : ℕ) (a Y : ℝ), 1 ≤ p → 1 ≤ k → 0 < Y → Dt ≤ Do → (ao : ℝ) ≤ 2 * a →
    (p : ℝ) ^ Dt * (⌊((ao : ℝ) / (p : ℝ) ^ Do) / ((k : ℝ) ^ 2 * Y)⌋₊ : ℝ) ≤ 2 * a / ((k : ℝ) ^ 2 * Y)

def ReducedDegree : Prop :=
  ∀ (k Ns : ℕ) (a Y at' E' E0 Et : ℝ), 0 < Y → 1 ≤ k → 0 ≤ a → E' ≤ E0 → 32 * E0 ≤ a →
    Et ≤ 4 * Ns * a / ((k : ℝ) ^ 2 * Y) → 160 * (Ns : ℝ) ≤ (k : ℝ) ^ 2 * Y → a ≤ at' →
    (9 / 10 : ℝ) * at' ≤ at' - E' - Et

def GeomDistinct : Prop :=
  ∀ (p m0 : ℕ) (s : Finset ℕ), 2 ≤ p → (∀ D ∈ s, m0 ≤ D) → ∑ D ∈ s, (1 / (p : ℝ) ^ D) ≤ 2 / (p : ℝ) ^ m0

def AdmissibleSmallRatio : Prop :=
  ∀ (p k Ns D1 L1 R R' : ℕ) (a Y Qn be : ℝ), 2 ≤ p → 1 ≤ k → 1 ≤ Ns → 1 ≤ Y → 0 < a → 0 < Qn → 1 ≤ L1 →
    be ≤ 4 * a / (p : ℝ) ^ (R + D1 + L1 + 1) →
    a / (8 * p * Y * (k : ℝ) ^ 2 * Ns * ((p : ℝ) ^ D1 * Qn)) < (p : ℝ) ^ R' →
    128 * (k : ℝ) ^ 2 * Ns * Y ^ 2 ≤ (p : ℝ) ^ (L1 - 1) →
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) < 32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ∧
    32 * Y * (k : ℝ) ^ 2 * Ns / (p : ℝ) ^ L1 ≤ 1 / (4 * p * Y) ∧
    be / (Qn * (p : ℝ) ^ R' / (p : ℝ) ^ R) ≤ 1 / (4 * Y)

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end
end

-- Source module: Formalism.ThetaLogCoordinates.ResidueClassEstimates.VandermondeRankEstimates.AdmissibleSmallRatio

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

theorem geom_range_le (p m0 n : ℕ) (hp : 2 ≤ p) :
    ∑ i ∈ Finset.range n, (1 / (p : ℝ) ^ (m0 + i)) ≤ 2 / (p : ℝ) ^ m0 - 2 / (p : ℝ) ^ (m0 + n) := by
  have hP : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0:ℝ) < p := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hx : (0:ℝ) < (p:ℝ)^(m0+n) := pow_pos hP0 _
    have e : (2:ℝ) / (p:ℝ)^(m0+(n+1)) ≤ 1 / (p:ℝ)^(m0+n) := by
      rw [← add_assoc, pow_succ, div_le_div_iff₀ (by positivity) hx]
      nlinarith
    have e2 : (2:ℝ) / (p:ℝ)^(m0+n) = 2 * (1 / (p:ℝ)^(m0+n)) := by ring
    linarith

theorem geometricSumDistinct : GeomDistinct := by
  intro p m0 s hp hs
  have hP0 : (0:ℝ) < p := by
    have : (2:ℝ) ≤ p := by exact_mod_cast hp
    linarith
  obtain ⟨n, hn⟩ : ∃ n, ∀ D ∈ s, D < m0 + n :=
    ⟨s.sup (fun x => x) + 1, fun D hD => by
      have := Finset.le_sup (f := fun x => x) hD
      omega⟩
  have hsub : s ⊆ (Finset.range n).image (fun i => m0 + i) := by
    intro D hD
    simp only [Finset.mem_image, Finset.mem_range]
    have h1 := hn D hD
    have h2 := hs D hD
    exact ⟨D - m0, by omega, by omega⟩
  calc ∑ D ∈ s, (1 / (p:ℝ)^D)
      ≤ ∑ D ∈ (Finset.range n).image (fun i => m0 + i), (1 / (p:ℝ)^D) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = ∑ i ∈ Finset.range n, (1 / (p:ℝ)^(m0+i)) := by
        rw [Finset.sum_image (fun x _ y _ h => by simpa using h)]
    _ ≤ 2 / (p:ℝ)^m0 - 2 / (p:ℝ)^(m0+n) := geom_range_le p m0 n hp
    _ ≤ 2 / (p:ℝ)^m0 := by
        have : (0:ℝ) ≤ 2 / (p:ℝ)^(m0+n) := by positivity
        linarith

theorem admissibleSmallRatio : AdmissibleSmallRatio := by
  intro p k Ns D1 L1 R R' a Y Qn be hp hk hNs hY ha hQn hL1 hbe h7 h8
  have hP : (2:ℝ) ≤ p := by exact_mod_cast hp
  have hP0 : (0:ℝ) < p := by linarith
  have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hNs' : (1:ℝ) ≤ Ns := by exact_mod_cast hNs
  have hY0 : (0:ℝ) < Y := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hNs0 : (0:ℝ) < Ns := by linarith
  have hR : (0:ℝ) < (p:ℝ)^R := pow_pos hP0 _
  have hR' : (0:ℝ) < (p:ℝ)^R' := pow_pos hP0 _
  have hD1 : (0:ℝ) < (p:ℝ)^D1 := pow_pos hP0 _
  have hL : (0:ℝ) < (p:ℝ)^L1 := pow_pos hP0 _
  have hT : (0:ℝ) < Qn * (p:ℝ)^R' / (p:ℝ)^R := by positivity
  have sA : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) ≤
      (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R) :=
    div_le_div_of_nonneg_right hbe hT.le
  have sB : (4 * a / (p:ℝ)^(R+D1+L1+1)) / (Qn * (p:ℝ)^R' / (p:ℝ)^R) =
      4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R')) := by
    rw [show R+D1+L1+1 = R + D1 + L1 + 1 from rfl, pow_succ, pow_add, pow_add]
    field_simp
  have ha7 : a < (p:ℝ)^R' * (8 * p * Y * (k:ℝ)^2 * Ns * ((p:ℝ)^D1 * Qn)) := by
    rwa [div_lt_iff₀ (by positivity)] at h7
  have sC : 4 * a / ((p:ℝ)^D1 * (p:ℝ)^L1 * p * (Qn * (p:ℝ)^R')) <
      32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 := by
    rw [div_lt_div_iff₀ (by positivity) hL]
    have := mul_lt_mul_of_pos_left ha7 (show (0:ℝ) < 4 * (p:ℝ)^L1 by positivity)
    nlinarith
  have hPL : (p:ℝ)^L1 = (p:ℝ)^(L1-1) * p := by
    rw [← pow_succ]
    congr 1
    omega
  have s2 : 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 ≤ 1 / (4 * p * Y) := by
    rw [div_le_div_iff₀ hL (by positivity), hPL]
    have := mul_le_mul_of_nonneg_right h8 hP0.le
    nlinarith
  have s1 : be / (Qn * (p:ℝ)^R' / (p:ℝ)^R) < 32 * Y * (k:ℝ)^2 * Ns / (p:ℝ)^L1 := by
    rw [sB] at sA
    exact lt_of_le_of_lt sA sC
  have s3 : 1 / (4 * p * Y) ≤ 1 / (4 * Y) :=
    one_div_le_one_div_of_le (by positivity) (by nlinarith)
  exact ⟨s1, s2, by linarith⟩

end Formalism.InvariantFactorPaths.BranchingDimensions
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.SegmentDegree.BetaRatioBound

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem beta_ratio_bound : BetaRatioBound 1088 := by
  intro p n' r K _ _ _ X hX hLa hk j b hA
  classical
  have hV := hX.valid
  have B := basics hX
  have hr : 0 < r := NeZero.pos r
  have hp0 : (0 : ℝ) < p := by linarith [B.p1]
  have hp2 : 2 ≤ p := hX.prime.two_le
  have h41 := (top_count_lower_bounds 1088 (by norm_num) p n' r K X hX hLa hk).1
  have ha0 : 0 < X.a := by have := TE.four_hundred_sixteen_le_a hX; linarith

  have hL1 : 1 ≤ X.L₁ := by
    by_contra h
    have h0 : X.L₁ = 0 := by omega
    have hP2 := hX.P2
    rw [h0] at hP2
    have e1 : (p : ℝ) ^ (((0 : ℕ) : ℤ) - 1) = (p : ℝ)⁻¹ := by simp
    rw [e1] at hP2
    have e2 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ B.p1
    have e3 : (1 : ℝ) ≤ 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 := by
      have k5 := B.k5
      unfold Dat.k at k5
      have a1 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 := by nlinarith
      have a2 : (1 : ℝ) ≤ X.Y ^ 2 := by nlinarith [B.Y1]
      have a3 := B.Ns1
      have a4 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) := by nlinarith
      nlinarith
    linarith
  have hP2 : 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 ≤ (p : ℝ) ^ (X.L₁ - 1) := by
    have h := hX.P2
    have e : ((X.L₁ : ℤ) - 1) = ((X.L₁ - 1 : ℕ) : ℤ) := by omega
    rw [e, zpow_natCast] at h
    exact h
  set D1 := X.F.dist j (X.F.fr j 0) with hD1
  set s := (X.F.letters j).filter (· < X.F.fr j 0) with hs
  have hfr0 : X.F.fr j 0 ∈ X.F.letters j := k_fr_mem_letters X.F hV j hr
  have hD1c := TE.dist_cast hfr0

  have hU1 : ∀ x ∈ s, D1 + X.L₁ + 1 ≤ X.F.dist j x := by
    intro x hx
    have hne : s.Nonempty := ⟨x, hx⟩
    have hmax := Finset.max'_mem s hne
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hmax
    have hgap := hV.2.2.2.2.2.2.1 j |>.2.2 (s.max' hne) hm1 hm2 (fun z hz hzlt =>
      Finset.le_max' s z (Finset.mem_filter.mpr ⟨hz, hzlt⟩))
    have hle := Finset.le_max' s x hx
    have hxc := TE.dist_cast (Finset.mem_filter.mp hx).1
    omega

  have hA1 : (X.beS p K j (X.restr j b) : ℝ) ≤ 4 * X.a / (p : ℝ) ^ (X.Rj p K j + D1 + X.L₁ + 1) := by
    unfold Dat.beS
    push_cast
    have h1 : ∀ x ∈ s, (X.Bdeg p K j (X.restr j b) x : ℝ) ≤
        2 * X.a / (p : ℝ) ^ X.Rj p K j * (1 / (p : ℝ) ^ X.F.dist j x) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
      have b1 := (TE.Bdeg_bounds hX hk h41 j b hA x hx1 hx2).2
      have b2 := (TE.c_bounds hX h41 j x hx1).2.2
      refine le_trans b1 ?_
      rw [pow_add]
      have hq1 : (0 : ℝ) < (p : ℝ) ^ X.F.dist j x := by positivity
      have hq2 : (0 : ℝ) < (p : ℝ) ^ X.Rj p K j := by positivity
      rw [div_mul_div_comm, mul_one, mul_comm ((p : ℝ) ^ X.Rj p K j)]
      exact div_le_div_of_nonneg_right b2 (by positivity)
    refine le_trans (Finset.sum_le_sum h1) ?_
    rw [← Finset.mul_sum]
    have hinj : Set.InjOn (X.F.dist j) (s : Set ℤ) := by
      intro x hx y hy hxy
      have c1 := TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).1
      have c2 := TE.dist_cast (Finset.mem_filter.mp (Finset.mem_coe.mp hy)).1
      have : (X.F.dist j x : ℤ) = (X.F.dist j y : ℤ) := by exact_mod_cast hxy
      omega
    have h2 : ∑ x ∈ s, (1 / (p : ℝ) ^ X.F.dist j x) = ∑ D ∈ s.image (X.F.dist j), (1 / (p : ℝ) ^ D) :=
      (Finset.sum_image (f := fun D : ℕ => 1 / (p : ℝ) ^ D) hinj).symm
    have h3 := Formalism.InvariantFactorPaths.BranchingDimensions.geometricSumDistinct p (D1 + X.L₁ + 1) (s.image (X.F.dist j)) hp2 (by
      intro D hD
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hD
      exact hU1 x hx)
    rw [h2]
    have hc : 0 ≤ 2 * X.a / (p : ℝ) ^ X.Rj p K j := by positivity
    refine le_trans (mul_le_mul_of_nonneg_left h3 hc) ?_
    rw [div_mul_div_comm, ← pow_add]
    have e : X.Rj p K j + (D1 + X.L₁ + 1) = X.Rj p K j + D1 + X.L₁ + 1 := by ring
    rw [e]
    apply le_of_eq
    ring

  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) := by
    have hm : X.F.fr j (r - 1) < X.F.fr (j + 1) (r - 1) := eFr_strictMono hV (by omega : j < j + 1)
    exact ⟨(X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hdist : X.F.dist (j + 1) (X.F.fr j 0) = D1 + d := by
    have : ((X.F.dist (j + 1) (X.F.fr j 0) : ℕ) : ℤ) = X.F.fr (j + 1) (r - 1) - X.F.fr j 0 := by
      unfold Frames.dist
      exact Int.toNat_of_nonneg (by omega)
    omega
  have hB1 : X.a / (8 * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) <
      (p : ℝ) ^ X.Rj p K (j + 1) := by
    have h := lt_pow_Rj hX (j + 1)
    unfold Tj at h
    rw [add_sub_cancel_right, hdist, pow_add ((p : ℝ)) D1 d, pow_succ ((p : ℝ)) (X.Rj p K (j + 1))] at h
    unfold Dat.k at h
    have hden : 0 < 8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) := by
      have k5 := B.k5
      unfold Dat.k at k5
      have := B.Ns1
      have := B.Y1
      positivity
    rw [div_lt_iff₀ hden] at h
    have hden2 : 0 < 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) := by
      have e : 8 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * ((p : ℝ) ^ D1 * (p : ℝ) ^ d) =
          (p : ℝ) * (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) := by ring
      rw [e]; exact mul_pos hp0 hden
    rw [div_lt_iff₀ hden2]
    calc X.a < (p : ℝ) ^ X.Rj p K (j + 1) * (p : ℝ) *
          (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D1 * (p : ℝ) ^ d)) := h
      _ = _ := by ring
  have hcore := (Formalism.InvariantFactorPaths.BranchingDimensions.admissibleSmallRatio p (r + K) X.Ns D1 X.L₁ (X.Rj p K j) (X.Rj p K (j + 1)) X.a X.Y
    ((p : ℝ) ^ d) (X.beS p K j (X.restr j b) : ℝ) hp2 (by omega)
    (by have := B.Ns1; exact_mod_cast this) B.Y1 ha0 (by positivity) hL1 hA1 hB1 hP2).2.2

  have hexp := Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ hX j
  have hmono : X.F.fr (j - 1) 0 ≤ X.F.fr j 0 := (mem_letters_bounds hfr0).1
  have hQ : ((X.Qc p K j : ℕ) : ℝ) = (p : ℝ) ^ d * (p : ℝ) ^ X.Rj p K (j + 1) / (p : ℝ) ^ X.Rj p K j := by
    unfold Dat.Qc
    rw [eq_div_iff (by positivity)]
    push_cast
    rw [← pow_add, ← pow_add]
    congr 1
    have : (((X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ)).toNat : ℕ) : ℤ) =
        X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ) :=
      Int.toNat_of_nonneg (by omega)
    omega
  rw [← hQ] at hcore
  have hQpos : (0 : ℝ) < ((X.Qc p K j : ℕ) : ℝ) := by
    rw [hQ]; positivity
  rw [div_le_div_iff₀ hQpos (by have := B.Y1; positivity)] at hcore
  linarith

end Formalism.MainNotions.SelectionLemmas.Pf
end
end
end
