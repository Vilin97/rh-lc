module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RationalWeightIntegralCoeffsStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelArithIntersectionFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelCurveDegreeNefStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelPointHeightDegreeStatement
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelSemipositiveConjStatement
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangLowerBoundRational

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem zhang_lower_bound_root_model : SuccessiveMinimaLowerBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ), IsRatWt lam →
      M.Semipos t lam s → M.NefFib lam s → (∀ W, M.IsPt W → e ≤ M.ht II t lam s W) →
      ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) ≤
        M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  intro hZ1 II hII Ψ _ N M t lam s e hrat hsemi hnef hpts
  obtain ⟨q, n, hq, hn⟩ := GlobalTheory.T.rational_weight_integral_coeffs Ψ N M lam s hrat
  have hp := GlobalTheory.T.root_model_semipositive_conj Ψ N M t lam s q n hn hsemi
  have hnf := (GlobalTheory.T.root_model_curve_degree_nef Ψ N M t lam s q n hn).2 hnef
  have hW : ∀ W, IsArithVar W 1 → M.P ≤ W →
      ((q : ℝ) * e) * degC W ≤ II M.K M.ι W 1 ![combLine (M.line t) n] := by
    intro W h1 h2
    have hpt : M.IsPt W := ⟨h1, h2⟩
    obtain ⟨hd, hI⟩ := GlobalTheory.T.root_model_point_height_degree II hII Ψ N M t lam s q n W hn hpt
    rw [hI]
    have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hd' : (0 : ℝ) ≤ degC W := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpts W hpt) hq') hd'
  have key := hZ1 M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) II hII.1 M.arith le_rfl
    hp.1 hnf hp.2 hW
  have hgeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      (M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have := GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n) (fun _ j => hn j)
    simpa [geomDeg, Finset.prod_const] using this
  rw [hgeo, GlobalTheory.T.root_model_arith_intersection_formula II hII Ψ N M t lam s q n hn] at key
  have hδ : (0 : ℝ) < M.δ := by exact_mod_cast M.δ_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : (0 : ℝ) < (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) := by positivity
  refine le_of_mul_le_mul_left ?_ hc
  calc (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) * (((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N))
      = ((dimFl Ψ N + 1 : ℕ) : ℝ) * ((q : ℝ) * e) *
          ((M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N)) := by
        push_cast; ring
    _ ≤ _ := key

end GlobalTheory.CompanionTheory.Ar.Top
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangLowerBoundRationalStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.zhang_lower_bound_rational : SuccessiveMinimaLowerBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → (∀ W, M.IsPt W → e ≤ M.ht II t lam s W) → ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) ≤ M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.zhang_lower_bound_root_model | exact GlobalTheory.CompanionTheory.Ar.Top.zhang_lower_bound_root_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.zhang_lower_bound_root_model <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangUpperBoundDensePoints

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem zhang_upper_bound_root_model : SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ) (F : Set (Ideal (MRing M.ι))), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → IsZariskiDense M.P F → (∀ W ∈ F, M.IsPt W ∧ M.ht II t lam s W ≤ e) → M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) ≤ ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) := by
  intro hZ II hII Ψ _ N M t lam s e F hrat hsp hnef hF hpt
  obtain ⟨q, n, hq, hn⟩ := GlobalTheory.T.rational_weight_integral_coeffs Ψ N M lam s hrat
  have hsemi := GlobalTheory.T.root_model_semipositive_conj Ψ N M t lam s q n hn hsp
  have hnf := (GlobalTheory.T.root_model_curve_degree_nef Ψ N M t lam s q n hn).2 hnef
  have hA := GlobalTheory.T.root_model_arith_intersection_formula II hII Ψ N M t lam s q n hn
  have hG := GlobalTheory.T.root_model_log_integral_formula II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n)
    (fun _ j => hn j)
  have hGeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      M.δ * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have hprod : (∏ _k : Fin (dimFl Ψ N), linA lam (s : ℝ)) = linA lam s ^ dimFl Ψ N := by
      simp
    rw [hprod] at hG
    exact hG
  have key := hZ M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) F II hII.1
    M.arith le_rfl hsemi.1 hnf hsemi.2
    (by
      intro W hW
      obtain ⟨hp, hle⟩ := hpt W hW
      obtain ⟨-, hI⟩ := GlobalTheory.T.root_model_point_height_degree II hII Ψ N M t lam s q n W hn hp
      refine ⟨hp.1, hp.2, ?_⟩
      rw [hI]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg q))
        (Nat.cast_nonneg _))
    hF
  rw [hA, hGeo] at key
  have hqR : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hδ : (0 : ℝ) < M.δ := Nat.cast_pos.mpr M.δ_pos
  have hpos : (0 : ℝ) < M.δ * (q : ℝ) ^ (dimFl Ψ N + 1) := mul_pos hδ (pow_pos hqR _)
  refine le_of_mul_le_mul_left ?_ hpos
  calc _ ≤ _ := key
    _ = _ := by push_cast; ring

end GlobalTheory.CompanionTheory.Ar.Top
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ZhangUpperBoundDensePointsStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.zhang_upper_bound_dense_points : SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ) (F : Set (Ideal (MRing M.ι))), IsRatWt lam → M.Semipos t lam s → M.NefFib lam s → IsZariskiDense M.P F → (∀ W ∈ F, M.IsPt W ∧ M.ht II t lam s W ≤ e) → M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) ≤ ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.zhang_upper_bound_root_model | exact GlobalTheory.CompanionTheory.Ar.Top.zhang_upper_bound_root_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.zhang_upper_bound_root_model <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerGapHeightUniformBound

section

@[expose] public section

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem l1_le_card_mul_of_norm_le_one {Ψ : Type} [Fintype Ψ] {N : ℕ} (lam : Wt Ψ N) (h : ‖lam‖ ≤ 1) :
    l1 lam ≤ (Fintype.card Ψ : ℝ) * N := by
  have hb : ∀ τ i, |lam τ i| ≤ 1 := fun τ i => by
    have h1 : ‖lam τ‖ ≤ ‖lam‖ := norm_le_pi_norm lam τ
    have h2 : ‖lam τ i‖ ≤ ‖lam τ‖ := norm_le_pi_norm (lam τ) i
    rw [← Real.norm_eq_abs]; linarith
  unfold l1
  calc ∑ τ, ∑ i, |lam τ i| ≤ ∑ _τ : Ψ, ∑ _i : Fin N, (1 : ℝ) :=
        Finset.sum_le_sum fun τ _ => Finset.sum_le_sum fun i _ => hb τ i
    _ = (Fintype.card Ψ : ℝ) * N := by simp

theorem RootTower.isRatWt_lamS {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N) {lam : Wt Ψ N}
    (s : ℚ) (h : IsRatWt lam) : IsRatWt (T.lamS lam s) := by
  intro τ i
  obtain ⟨q1, h1⟩ := h τ i
  obtain ⟨q2, h2⟩ := T.nu_rat τ i
  refine ⟨q1 - s * q2, ?_⟩
  simp only [RootTower.lamS, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
  push_cast; ring

theorem mbarTop_squeeze : SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.I3 → T.I5 II → T.I6 II →
    ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, 2 ≤ B → ∀ (c : T.Comp) (lam : Wt Ψ N) (θ : ℝ) (s : ℚ),
      IsRatWt lam → ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) →
      CompactGapsGE T.j c₀ lam → Dominant (T.lamS lam s) → NefThreshold T.j B (T.lamS lam s) →
      0 ≤ T.mDeg B c lam s →
      |T.mbarTop II B c lam s| ≤ C * Real.log (B / (s : ℝ)) * T.mDeg B c lam s := by
  intro hZ1 hZ2 II hII Ψ _ _ N T hI3 hI5 hI6 c₀ hc₀
  obtain ⟨s₀, hs₀, h3⟩ := hI3 ((Fintype.card Ψ : ℝ) * N)
  obtain ⟨θ₅, hθ₅, C₅, h5⟩ := hI5 c₀ hc₀
  obtain ⟨θ₆, hθ₆, C₆, h6⟩ := hI6 c₀ hc₀
  have hD : (0 : ℝ) ≤ (dimFl Ψ N : ℝ) + 1 := by positivity
  refine ⟨min (min θ₅ θ₆) (min 1 s₀), lt_min (lt_min hθ₅ hθ₆) (lt_min one_pos hs₀),
    ((dimFl Ψ N : ℝ) + 1) * (max C₅ 0 + max C₆ 0),
    mul_nonneg hD (add_nonneg (le_max_right _ _) (le_max_right _ _)), ?_⟩
  intro B hB c lam θ s hrat hnorm hθ hθ₀ hs hgap hcg hdom hnef hdeg
  have hθ1 : θ ≤ 1 := le_trans hθ₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hθs : θ ≤ s₀ := le_trans hθ₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hθ5 : θ ≤ θ₅ := le_trans hθ₀ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hθ6 : θ ≤ θ₆ := le_trans hθ₀ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hspos : (0 : ℝ) < s := by rw [hs]; positivity
  have hs1 : (s : ℝ) ≤ 1 := by rw [hs]; nlinarith
  have hss₀ : (s : ℝ) ≤ s₀ := by rw [hs]; nlinarith
  have hl1 : l1 lam ≤ (Fintype.card Ψ : ℝ) * N := l1_le_card_mul_of_norm_le_one lam hnorm
  obtain ⟨hNef, hSemi⟩ := h3 B hB c lam (s : ℝ) hl1 hspos hss₀ hdom hnef
  have hrat' : IsRatWt (T.lamS lam s) := RootTower.isRatWt_lamS T s hrat
  have hlow := h5 B hB c lam θ s hrat hnorm hθ hθ5 hs hgap hcg
  obtain ⟨F, hF, hFpt⟩ := h6 B hB c lam θ s hrat hnorm hθ hθ6 hs hgap hcg
  have hL : ((dimFl Ψ N : ℝ) + 1) * (-(C₅ * Real.log (B / (s : ℝ)))) * T.mDeg B c lam s ≤
      T.mbarTop II B c lam s :=
    GlobalTheory.T.zhang_lower_bound_rational hZ1 II hII Ψ N (T.M B c) (scale s) (T.lamS lam s) s (-(C₅ * Real.log (B / (s : ℝ))))
      hrat' hSemi hNef (fun W hW => hlow W hW)
  have hU : T.mbarTop II B c lam s ≤
      ((dimFl Ψ N : ℝ) + 1) * (C₆ * Real.log B) * T.mDeg B c lam s :=
    GlobalTheory.T.zhang_upper_bound_dense_points hZ2 II hII Ψ N (T.M B c) (scale s) (T.lamS lam s) s (C₆ * Real.log B) F
      hrat' hSemi hNef hF (fun W hW => hFpt W hW)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ B))
  have hlogBs : Real.log B ≤ Real.log (B / (s : ℝ)) :=
    Real.log_le_log hBpos (by rw [le_div_iff₀ hspos]; nlinarith)
  have hLg : 0 ≤ Real.log (B / (s : ℝ)) := le_trans hlogB hlogBs
  have hP : 0 ≤ ((dimFl Ψ N : ℝ) + 1) * Real.log (B / (s : ℝ)) * T.mDeg B c lam s :=
    mul_nonneg (mul_nonneg hD hLg) hdeg
  have hQ : 0 ≤ ((dimFl Ψ N : ℝ) + 1) * Real.log B * T.mDeg B c lam s :=
    mul_nonneg (mul_nonneg hD hlogB) hdeg
  have hQP : ((dimFl Ψ N : ℝ) + 1) * Real.log B * T.mDeg B c lam s ≤
      ((dimFl Ψ N : ℝ) + 1) * Real.log (B / (s : ℝ)) * T.mDeg B c lam s :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogBs hD) hdeg
  have k1 := mul_le_mul_of_nonneg_right
    (show C₅ ≤ max C₅ 0 + max C₆ 0 by linarith [le_max_left C₅ 0, le_max_right C₆ 0]) hP
  have k2 := mul_le_mul_of_nonneg_right (le_max_left C₆ 0) hQ
  have k3 := mul_le_mul_of_nonneg_left hQP (le_max_right C₆ 0)
  have k4 := mul_le_mul_of_nonneg_right
    (show max C₆ 0 ≤ max C₅ 0 + max C₆ 0 by linarith [le_max_right C₅ 0]) hP
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end GlobalTheory.CompanionTheory.Ar.Top
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TowerGapHeightUniformBoundStatement

section

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

theorem _root_.GlobalTheory.T.tower_gap_height_uniform_bound : SuccessiveMinimaLowerBound → SuccessiveMinimaUpperBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N), T.I3 → T.I5 II → T.I6 II → ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ B : ℕ, 2 ≤ B → ∀ (c : T.Comp) (lam : Wt Ψ N) (θ : ℝ) (s : ℚ), IsRatWt lam → ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) → CompactGapsGE T.j c₀ lam → Dominant (T.lamS lam s) → NefThreshold T.j B (T.lamS lam s) → 0 ≤ T.mDeg B c lam s → |T.mbarTop II B c lam s| ≤ C * Real.log (B / (s : ℝ)) * T.mDeg B c lam s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.mbarTop_squeeze | exact GlobalTheory.CompanionTheory.Ar.Top.mbarTop_squeeze | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.mbarTop_squeeze <;> assumption)
end
end
