module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Formalism.LatticeSlopes.Statement
public import Formalism.LatticeSlopes.LatticeSlopesProofs.DegQuot
public import Formalism.LatticeSlopes.LatticeSlopesProofs.SaturationProperties
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqCovolume
import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolEqGram
public import Formalism.LatticeSlopes.LatticeSlopesProofs.CovolPos
public import Formalism.LatticeSlopes.LatticeSlopesProofs.ShortVector
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.LatticeSlopes.CovolAntiSameRank
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.ENatToNat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

-- Source module: Formalism.NormUnitaryBounds.DetPolynomialWeights.ExistsNeZeroNormLeRankDivOfDualMinimum

section

@[expose] public section

open Module Submodule

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem discreteTopology_of_norm_ge (L : Submodule ℤ E) {ε : ℝ} (hε : 0 < ε)
    (h : ∀ x ∈ L, x ≠ 0 → ε ≤ ‖x‖) : DiscreteTopology L := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  have hball : ({0} : Set L) = Metric.ball (0 : L) ε := by
    ext x
    simp only [Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro rfl
      simpa using hε
    · intro hx
      by_contra hne
      have hx0 : (x : E) ≠ 0 := fun h0 => hne (Subtype.ext h0)
      have := h x x.2 hx0
      rw [Submodule.coe_norm] at hx
      linarith
  rw [hball]
  exact Metric.isOpen_ball

theorem exists_ne_zero_norm_le_rank_div_of_dualMinimum (Q : Submodule ℤ E) [hQd : DiscreteTopology Q] (hQ : Q ≠ ⊥) {l : ℝ}
    (hl : 0 < l)
    (hdual : ∀ y ∈ span ℝ (Q : Set E), y ≠ 0 →
      (∀ x ∈ Q, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖) :
    ∃ q ∈ Q, q ≠ 0 ∧ ‖q‖ ≤ (Formalism.F.rk Q : ℝ) / l := by
  classical
  set k := Module.finrank ℤ Q with hk
  let b := Module.finBasis ℤ Q
  let v : Fin k → E := fun i => (b i : E)
  let G := Matrix.gram ℝ v
  have hcovQ : Formalism.F.covol Q = Real.sqrt G.det := Formalism.F.covol_eq_gram E Q (Fin k) b
  have hpos : 0 < Formalism.F.covol Q := Formalism.F.covol_pos' E Q hQd
  have hdet : 0 < G.det := Real.sqrt_pos.mp (hcovQ ▸ hpos)
  have hdetu : IsUnit G.det := hdet.ne'.isUnit
  let P := G⁻¹
  let w : Fin k → E := fun j => ∑ i, P i j • v i
  have hGP : G * P = 1 := Matrix.mul_nonsing_inv G hdetu
  have hbi : ∀ l j, inner ℝ (v l) (w j) = if l = j then 1 else 0 := by
    intro l j
    have h1 : inner ℝ (v l) (w j) = (G * P) l j := by
      simp only [w, inner_sum, real_inner_smul_right, Matrix.mul_apply, G, Matrix.gram_apply]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    rw [h1, hGP, Matrix.one_apply]
  have hQv : ∀ x ∈ Q, ∃ a : Fin k → ℤ, x = ∑ i, (a i : ℝ) • v i := by
    intro x hx
    refine ⟨fun i => b.repr ⟨x, hx⟩ i, ?_⟩
    have h1 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    have h2 : ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : E) = x := h1
    calc x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : E) := h2.symm
      _ = _ := by
        simp only [Int.cast_smul_eq_zsmul, v]
        try rfl
  let D := Submodule.span ℤ (Set.range w)
  have hint : ∀ y ∈ D, ∀ x ∈ Q, ∃ z : ℤ, inner ℝ x y = (z : ℝ) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro x hx
      obtain ⟨a, rfl⟩ := hQv x hx
      refine ⟨a j, ?_⟩
      simp only [sum_inner, real_inner_smul_left, hbi]
      simp
    | zero => exact fun x _ => ⟨0, by simp⟩
    | add y y' _ _ h1 h2 =>
      intro x hx
      obtain ⟨z1, e1⟩ := h1 x hx
      obtain ⟨z2, e2⟩ := h2 x hx
      exact ⟨z1 + z2, by rw [inner_add_right, e1, e2]; push_cast; ring⟩
    | smul c y _ h1 =>
      intro x hx
      obtain ⟨z1, e1⟩ := h1 x hx
      exact ⟨c * z1, by rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, e1]; push_cast; ring⟩
  have hDV : ∀ y ∈ D, y ∈ span ℝ (Q : Set E) := by
    intro y hy
    have hle : D ≤ (span ℝ (Q : Set E)).restrictScalars ℤ := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (b i).2))
    exact hle hy
  have hDl : ∀ y ∈ D, y ≠ 0 → l ≤ ‖y‖ := fun y hy hy0 => hdual y (hDV y hy) hy0 (hint y hy)
  have hDd : DiscreteTopology D := discreteTopology_of_norm_ge D hl hDl
  have hli : LinearIndependent ℤ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have h1 := congrArg (fun y => inner ℝ (v l) y) hg
    simp only [inner_sum, inner_zero_right] at h1
    simp only [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right, hbi, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
    exact_mod_cast h1
  let bw := Basis.span hli
  have hcovD : Formalism.F.covol D = Real.sqrt (Matrix.gram ℝ w).det := by
    rw [Formalism.F.covol_eq_gram E D (Fin k) bw]
    congr 3
    funext i
    exact congrArg Subtype.val (Basis.span_apply hli i)
  have hgw : Matrix.gram ℝ w = P.transpose * G * P := Formalism.F.gram_sum_smul_eq_transpose_mul v P
  have hdetw : (Matrix.gram ℝ w).det = G.det⁻¹ := by
    rw [hgw, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv']
    field_simp
  have hrkD : Formalism.F.rk D = k := by
    simp only [Formalism.F.rk]
    rw [Module.finrank_eq_card_basis bw, Fintype.card_fin]
  have hrkQ : Formalism.F.rk Q = k := rfl
  have hkpos : 0 < k := by
    have : Nontrivial Q := Submodule.nontrivial_iff_ne_bot.mpr hQ
    exact Module.finrank_pos
  have hD0 : D ≠ ⊥ := by
    intro h
    have hw0 : w ⟨0, hkpos⟩ ∈ D := Submodule.subset_span ⟨_, rfl⟩
    rw [h, Submodule.mem_bot] at hw0
    have h2 := hbi ⟨0, hkpos⟩ ⟨0, hkpos⟩
    rw [hw0, inner_zero_right] at h2
    simp at h2
  obtain ⟨q, hqQ, hq0, hqn⟩ := Formalism.F.shortVector_of Formalism.F.covol_eq_covolume' E Q hQd hQ
  obtain ⟨y, hyD, hy0, hyn⟩ := Formalism.F.shortVector_of Formalism.F.covol_eq_covolume' E D hDd hD0
  refine ⟨q, hqQ, hq0, ?_⟩
  have hly := hDl y hyD hy0
  rw [hrkD, hcovD, hdetw, Real.sqrt_inv, ← hcovQ] at hyn
  rw [hrkQ] at hqn ⊢
  have ht : 0 < Formalism.F.covol Q ^ ((1 : ℝ) / k) := Real.rpow_pos_of_pos hpos _
  rw [Real.inv_rpow hpos.le] at hyn
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
  have h1 : l * Formalism.F.covol Q ^ ((1 : ℝ) / k) ≤ Real.sqrt k := by
    have h2 := hly.trans hyn
    calc l * Formalism.F.covol Q ^ ((1 : ℝ) / k)
        ≤ Real.sqrt k * (Formalism.F.covol Q ^ ((1 : ℝ) / k))⁻¹ * Formalism.F.covol Q ^ ((1 : ℝ) / k) :=
          mul_le_mul_of_nonneg_right h2 ht.le
      _ = Real.sqrt k := by field_simp
  rw [le_div_iff₀ hl]
  calc ‖q‖ * l ≤ Real.sqrt k * Formalism.F.covol Q ^ ((1 : ℝ) / k) * l :=
        mul_le_mul_of_nonneg_right hqn hl.le
    _ = Real.sqrt k * (l * Formalism.F.covol Q ^ ((1 : ℝ) / k)) := by ring
    _ ≤ Real.sqrt k * Real.sqrt k := mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = k := hsk

end Formalism.NormUnitaryCountingLemmas
end
end
end

-- Source module: Formalism.NormUnitaryBounds.DetPolynomialWeights.ShortIndependentVectorsOfDualMinimum

section

@[expose] public section

open Module Submodule

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_starProjection_ne_zero_norm_le_of_dualMinimum (M : Submodule ℤ E) [hMd : DiscreteTopology M]
    (hspan : span ℝ (M : Set E) = ⊤) {l : ℝ} (hl : 0 < l)
    (hdual : ∀ y : E, y ≠ 0 → (∀ x ∈ M, ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖)
    (W : Submodule ℝ E) (N : Submodule ℤ E) (hNM : N ≤ M) (hNW : span ℝ (N : Set E) = W)
    (hW : W ≠ ⊤) :
    ∃ m ∈ M, Wᗮ.starProjection m ≠ 0 ∧
      ‖Wᗮ.starProjection m‖ ≤ (finrank ℝ E : ℝ) / l := by
  classical
  obtain ⟨hSat, hNS, -⟩ := Formalism.F.saturation_properties E M N hMd hNM
  obtain ⟨hQd, hrk, -⟩ := Formalism.F.degree_quotient E M (Formalism.F.satur M N) hMd hSat
  have hSW : span ℝ ((Formalism.F.satur M N : Submodule ℤ E) : Set E) = W := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      rw [← hNW]
      exact (Submodule.mem_inf.mp hx).2
    · rw [← hNW]
      exact Submodule.span_mono (show (N : Set E) ⊆ Formalism.F.satur M N from hNS)
  have hQeq : ∀ q, q ∈ Formalism.F.quot M (Formalism.F.satur M N) ↔ ∃ m ∈ M, Wᗮ.starProjection m = q := by
    intro q
    simp [Formalism.F.quot, hSW, Submodule.mem_map]
  haveI := hQd
  have hPzero : ∀ x ∈ W, Wᗮ.starProjection x = 0 := by
    intro x hx
    have h1 := Submodule.starProjection_add_starProjection_orthogonal (K := W) x
    rw [Submodule.starProjection_eq_self_iff.mpr hx] at h1
    simpa using h1
  have hsubW : ∀ m : E, m - Wᗮ.starProjection m ∈ W := by
    intro m
    have h1 := Submodule.sub_starProjection_mem_orthogonal (K := Wᗮ) m
    rwa [Submodule.orthogonal_orthogonal] at h1
  have hQne : Formalism.F.quot M (Formalism.F.satur M N) ≠ ⊥ := by
    intro hQ0
    apply hW
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro m hm
    have hq : Wᗮ.starProjection m ∈ Formalism.F.quot M (Formalism.F.satur M N) := (hQeq _).mpr ⟨m, hm, rfl⟩
    rw [hQ0, Submodule.mem_bot] at hq
    have h1 := hsubW m
    rw [hq, sub_zero] at h1
    exact h1
  have hdual' : ∀ y ∈ span ℝ ((Formalism.F.quot M (Formalism.F.satur M N) : Submodule ℤ E) : Set E), y ≠ 0 →
      (∀ x ∈ Formalism.F.quot M (Formalism.F.satur M N), ∃ z : ℤ, inner ℝ x y = (z : ℝ)) → l ≤ ‖y‖ := by
    intro y hy hy0 hint
    apply hdual y hy0
    intro x hx
    obtain ⟨z, hz⟩ := hint _ ((hQeq _).mpr ⟨x, hx, rfl⟩)
    refine ⟨z, ?_⟩
    have hyW : y ∈ Wᗮ := by
      refine (Submodule.span_le.mpr ?_) hy
      intro q hq
      obtain ⟨m, -, rfl⟩ := (hQeq q).mp hq
      exact Submodule.starProjection_apply_mem _ _
    rw [← hz, Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hyW]
  obtain ⟨q, hqQ, hq0, hqle⟩ := exists_ne_zero_norm_le_rank_div_of_dualMinimum (Formalism.F.quot M (Formalism.F.satur M N)) hQne hl hdual'
  obtain ⟨m, hm, rfl⟩ := (hQeq q).mp hqQ
  refine ⟨m, hm, hq0, le_trans hqle ?_⟩
  have hMrk : Formalism.F.rk M = finrank ℝ E := by
    haveI : IsZLattice ℝ M := ⟨hspan⟩
    exact ZLattice.rank ℝ M
  have hle : Formalism.F.rk (Formalism.F.quot M (Formalism.F.satur M N)) ≤ finrank ℝ E := by
    rw [← hMrk, hrk]
    exact Nat.le_add_left _ _
  exact div_le_div_of_nonneg_right (by exact_mod_cast hle) hl.le

end Formalism.NormUnitaryCountingLemmas
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIndependentLeOfDualMin

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem exists_independent_le_of_dual_min :
    ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
      (L : Submodule ℤ V) [DiscreteTopology L] [IsZLattice ℝ L] (μ : ℝ), 0 < μ →
      (∀ y : V, y ≠ 0 → (∀ x ∈ L, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) → μ ≤ ‖y‖) →
      ∃ b : Fin (Module.finrank ℝ V) → V, (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧
        ∀ i, ‖b i‖ ≤ (Module.finrank ℝ V : ℝ) ^ (3 / 2 : ℝ) / μ := by
  intro V _ _ _ L _ _ μ hμ hdual
  set n := Module.finrank ℝ V with hn
  set c : ℝ := (n : ℝ) / μ with hc
  have hc0 : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) hμ.le
  have hspan : Submodule.span ℝ (L : Set V) = ⊤ := IsZLattice.span_top
  have main : ∀ k, k ≤ n → ∃ b : Fin k → V, (∀ i, b i ∈ L) ∧ LinearIndependent ℝ b ∧
      (∀ i, ‖b i‖ ^ 2 ≤ n * c ^ 2) ∧
      (∀ w ∈ Submodule.span ℝ (Set.range b), ∃ z ∈ Submodule.span ℤ (Set.range b),
        ‖w - z‖ ^ 2 ≤ k * c ^ 2 / 4) := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨Fin.elim0, fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0, ?_⟩
      intro w hw
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      have hw0 : w = 0 := by
        rw [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] at hw
        exact hw
      simp [hw0]
    | succ k ih =>
      intro hk
      obtain ⟨b, hbL, hbli, hbn, hcov⟩ := ih (by omega)
      set W := Submodule.span ℝ (Set.range b) with hW
      set N := Submodule.span ℤ (Set.range b) with hN
      have hNL : N ≤ L := Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hbL i)
      have hNW : Submodule.span ℝ (N : Set V) = W := Submodule.span_span_of_tower ℤ ℝ (Set.range b)
      have hWtop : W ≠ ⊤ := by
        intro h
        have h1 : Module.finrank ℝ W = k := by rw [hW, finrank_span_eq_card hbli, Fintype.card_fin]
        rw [h, finrank_top] at h1
        omega
      have hNsubW : ∀ y ∈ N, y ∈ W := fun y hy => by rw [← hNW]; exact Submodule.subset_span hy
      obtain ⟨m, hmL, hp0, hpn⟩ := Formalism.NormUnitaryCountingLemmas.exists_starProjection_ne_zero_norm_le_of_dualMinimum L hspan hμ hdual W N hNL hNW hWtop
      set p := Wᗮ.starProjection m with hp
      have hpW : p ∈ Wᗮ := Wᗮ.starProjection_apply_mem m
      have hwW : m - p ∈ W := by
        have := Wᗮ.sub_starProjection_mem_orthogonal m
        rwa [Submodule.orthogonal_orthogonal] at this
      obtain ⟨z, hzN, hz⟩ := hcov (m - p) hwW
      have hzW : z ∈ W := hNsubW z hzN
      set v := m - z with hv
      have hvdec : v = (m - p - z) + p := by rw [hv]; abel
      have hvL : v ∈ L := L.sub_mem hmL (hNL hzN)
      have hp2 : ‖p‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpn 2
      have pyth : ∀ a ∈ W, ∀ q ∈ Wᗮ, ‖a + q‖ ^ 2 = ‖a‖ ^ 2 + ‖q‖ ^ 2 := by
        intro a ha q hq
        have h0 : ⟪a, q⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal ha hq
        rw [sq, sq, sq, norm_add_sq_eq_norm_sq_add_norm_sq_real h0]
      have hvW : v ∉ W := by
        intro h
        apply hp0
        have hmW : m ∈ W := by
          have e : m = v + z := by rw [hv]; abel
          rw [e]
          exact W.add_mem h hzW
        have hm' : m ∈ Wᗮᗮ := by rwa [Submodule.orthogonal_orthogonal]
        exact Wᗮ.starProjection_apply_eq_zero_iff.mpr hm'
      have hsub : m - p - z ∈ W := W.sub_mem hwW hzW
      refine ⟨Fin.cons v b, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hvL
        · simpa using hbL j
      · exact linearIndependent_finCons.mpr ⟨hbli, hvW⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp only [Fin.cons_zero]
          rw [hvdec, pyth _ hsub _ hpW]
          have hkn : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk
          nlinarith [sq_nonneg c, mul_le_mul_of_nonneg_right hkn (sq_nonneg c)]
        · simpa using hbn j
      · intro w' hw'
        rw [Fin.range_cons, Submodule.mem_span_insert] at hw'
        obtain ⟨t, u, hu, rfl⟩ := hw'
        set s := t - round t with hs
        have hs2 : s ^ 2 ≤ 1 / 4 := by
          have h := abs_sub_round t
          rw [← hs] at h
          nlinarith [abs_nonneg s, sq_abs s]
        have hq : s • (m - p - z) + u ∈ W := W.add_mem (W.smul_mem _ hsub) hu
        obtain ⟨z', hz'N, hz'⟩ := hcov (s • (m - p - z) + u) hq
        refine ⟨(round t : ℤ) • v + z', ?_, ?_⟩
        · rw [Fin.range_cons, Submodule.mem_span_insert]
          exact ⟨round t, z', hz'N, rfl⟩
        · have e : t • v + u - ((round t : ℤ) • v + z') = (s • (m - p - z) + u - z') + s • p := by
            rw [← Int.cast_smul_eq_zsmul ℝ, hs, hvdec]
            module
          rw [e, pyth _ (W.sub_mem hq (hNsubW z' hz'N)) _ (Wᗮ.smul_mem _ hpW), norm_smul,
            mul_pow, Real.norm_eq_abs, sq_abs]
          have h4 := mul_le_mul hs2 hp2 (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
          push_cast
          nlinarith [h4, hz']
  obtain ⟨b, hbL, hbli, hbn, -⟩ := main n le_rfl
  refine ⟨b, hbL, hbli, fun i => ?_⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast i.pos
  have key : (n : ℝ) ^ (3 / 2 : ℝ) / μ = Real.sqrt (n * c ^ 2) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hc0, hc, Real.sqrt_eq_rpow, ← mul_div_assoc,
      ← Real.rpow_add_one hnR.ne']
    norm_num
  rw [key]
  calc ‖b i‖ = Real.sqrt (‖b i‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt (hbn i)

end GlobalTheory.CompanionTheory.Ar.Cusp
end
end
