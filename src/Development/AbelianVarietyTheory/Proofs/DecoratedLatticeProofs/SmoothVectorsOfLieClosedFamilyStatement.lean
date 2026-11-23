module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVectorsSubspaceStableSobolevFormDeriv
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Matrix.Normed
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
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianCurvature.StatementI
import Formalism.RealPlaceAnalysis.StatementA
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.CkDefs

section

@[expose] public section

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.JCC.Ck

def PartialsContinuousDifferentiable : Prop :=
  ∀ (d : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (V : Set (Fin d → ℝ))
    (F : (Fin d → ℝ) → E) (D : Fin d → (Fin d → ℝ) → E),
    IsOpen V → (∀ i, ContinuousOn (D i) V) →
    (∀ y ∈ V, ∀ i, HasDerivAt (fun t : ℝ => F (y + t • Pi.single i (1 : ℝ))) (D i y) 0) →
    ∀ y ∈ V, HasFDerivAt F (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (D i y)) y

end PI.UnitaryGroupMassFormula.JCC.Ck
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JacobianCommutation.PCkPartials

section

@[expose] public section

open Filter Topology Asymptotics

noncomputable section

namespace PI.UnitaryGroupMassFormula.JCC.Ck

section partials

variable {d : ℕ}

def psum (y h : Fin d → ℝ) (m : ℕ) : Fin d → ℝ := fun l => y l + if l.val < m then h l else 0

theorem psum_zero (y h : Fin d → ℝ) : psum y h 0 = y := by
  funext l
  simp [psum]

theorem psum_d (y h : Fin d → ℝ) : psum y h d = y + h := by
  funext l
  simp [psum, l.isLt]

theorem psum_succ (y h : Fin d → ℝ) (i : Fin d) :
    psum y h (i.val + 1) = psum y h i.val + h i • Pi.single i (1 : ℝ) := by
  funext l
  simp only [psum, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hl : l = i
  · subst hl
    simp
  · have hne : l.val ≠ i.val := fun e => hl (Fin.ext e)
    rw [Pi.single_eq_of_ne hl, mul_zero, add_zero]
    by_cases hlt : l.val < i.val
    · rw [if_pos hlt, if_pos (by omega)]
    · rw [if_neg hlt, if_neg (by omega)]

theorem psum_seg_norm (y h : Fin d → ℝ) (i : Fin d) {s : ℝ} (hs : |s| ≤ |h i|) :
    ‖psum y h i.val + s • Pi.single i (1 : ℝ) - y‖ ≤ ‖h‖ := by
  have hv : ∀ l, ((psum y h i.val + s • Pi.single i (1 : ℝ) - y : Fin d → ℝ) l) =
      (if l.val < i.val then h l else 0) + s * ((Pi.single i (1 : ℝ) : Fin d → ℝ) l) := by
    intro l
    simp only [psum, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg h)).mpr (fun l => ?_)
  rw [hv l]
  by_cases hl : l = i
  · subst hl
    rw [if_neg (lt_irrefl _), Pi.single_eq_same, zero_add, mul_one, Real.norm_eq_abs]
    exact hs.trans (by simpa [Real.norm_eq_abs] using norm_le_pi_norm h l)
  · rw [Pi.single_eq_of_ne hl, mul_zero, add_zero]
    split_ifs
    · exact norm_le_pi_norm h l
    · rw [norm_zero]
      exact norm_nonneg h

theorem abs_le_of_mem_uIcc {a s : ℝ} (hs : s ∈ Set.uIcc 0 a) : |s| ≤ |a| := by
  rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact abs_le.mpr ⟨by linarith [abs_nonneg a], h2.trans (le_abs_self a)⟩
  · exact abs_le.mpr ⟨(neg_abs_le a).trans h1, h2.trans (abs_nonneg a)⟩

end partials

theorem partials_continuous_differentiable : PartialsContinuousDifferentiable := by
  intro d E _ _ V F D hV hD hF y hy
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro c hc
  set c' : ℝ := c / (d + 1) with hc'
  have hc'pos : 0 < c' := by positivity
  have hev : ∀ᶠ z in 𝓝 y, z ∈ V ∧ ∀ i, ‖D i z - D i y‖ ≤ c' := by
    refine (hV.eventually_mem hy).and (Filter.eventually_all.mpr (fun i => ?_))
    have hcont : ContinuousAt (D i) y := (hD i).continuousAt (hV.mem_nhds hy)
    filter_upwards [hcont (Metric.closedBall_mem_nhds (D i y) hc'pos)] with z hz
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  rw [Metric.eventually_nhds_iff_ball]
  refine ⟨δ, hδ, fun h hh => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hh
  have hstep : ∀ i : Fin d, ‖F (psum y h i.val + h i • Pi.single i (1 : ℝ)) - F (psum y h i.val) - h i • D i y‖
      ≤ c' * ‖h‖ := by
    intro i
    set p := psum y h i.val with hp
    have hmem : ∀ t ∈ Set.uIcc 0 (h i), p + t • Pi.single i (1 : ℝ) ∈ Metric.ball y δ := by
      intro t ht
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_le_of_lt (psum_seg_norm y h i (abs_le_of_mem_uIcc ht)) hh
    have hderiv : ∀ t ∈ Set.uIcc 0 (h i),
        HasDerivWithinAt (fun s : ℝ => F (p + s • Pi.single i (1 : ℝ)) - s • D i y)
          (D i (p + t • Pi.single i (1 : ℝ)) - D i y) (Set.uIcc 0 (h i)) t := by
      intro t ht
      have h0 := hF _ (hball _ (hmem t ht)).1 i
      have h0' : HasDerivAt (fun u : ℝ => F (p + t • Pi.single i (1 : ℝ) + u • Pi.single i (1 : ℝ)))
          (D i (p + t • Pi.single i (1 : ℝ))) (t - t) := by
        rw [sub_self]
        exact h0
      have h4 := HasDerivAt.comp_sub_const t t h0'
      have hfun : (fun s : ℝ => F (p + s • Pi.single i (1 : ℝ))) =
          fun s => F (p + t • Pi.single i (1 : ℝ) + (s - t) • Pi.single i (1 : ℝ)) := by
        funext s
        congr 1
        ext j
        simp only [Pi.add_apply, Pi.smul_apply, Pi.single_apply]
        split_ifs <;> ring
      have h3 : HasDerivAt (fun s : ℝ => F (p + s • Pi.single i (1 : ℝ)))
          (D i (p + t • Pi.single i (1 : ℝ))) t := by
        rw [hfun]
        exact h4
      have h2 : HasDerivAt (fun s : ℝ => s • D i y) (D i y) t := by
        simpa using (hasDerivAt_id t).smul_const (D i y)
      exact (h3.sub h2).hasDerivWithinAt
    have hbound : ∀ t ∈ Set.uIcc 0 (h i), ‖D i (p + t • Pi.single i (1 : ℝ)) - D i y‖ ≤ c' :=
      fun t ht => (hball _ (hmem t ht)).2 i
    have hmvt := (convex_uIcc (0 : ℝ) (h i)).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
      Set.left_mem_uIcc Set.right_mem_uIcc
    have hg : (F (p + h i • Pi.single i (1 : ℝ)) - h i • D i y) - (F (p + (0 : ℝ) • Pi.single i (1 : ℝ)) - (0 : ℝ) • D i y)
        = F (p + h i • Pi.single i (1 : ℝ)) - F p - h i • D i y := by
      rw [zero_smul, zero_smul, add_zero, sub_zero]
      abel
    rw [hg, sub_zero] at hmvt
    calc _ ≤ c' * ‖h i‖ := hmvt
      _ ≤ c' * ‖h‖ := mul_le_mul_of_nonneg_left (norm_le_pi_norm h i) hc'pos.le
  have htel : ∑ i : Fin d, (F (psum y h i.val + h i • Pi.single i (1 : ℝ)) - F (psum y h i.val) - h i • D i y)
      = F (y + h) - F y - (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (D i y)) h := by
    rw [Finset.sum_sub_distrib]
    have hs : ∀ i : Fin d, F (psum y h i.val + h i • Pi.single i (1 : ℝ)) = F (psum y h (i.val + 1)) :=
      fun i => by rw [psum_succ]
    simp only [hs]
    have hr := Fin.sum_univ_eq_sum_range (fun k => F (psum y h (k + 1)) - F (psum y h k)) d
    rw [hr, Finset.sum_range_sub (fun k => F (psum y h k)) d, psum_d, psum_zero, ContinuousLinearMap.sum_apply]
    first
    | rfl
    | simp
  rw [← htel]
  calc ‖∑ i : Fin d, (F (psum y h i.val + h i • Pi.single i (1 : ℝ)) - F (psum y h i.val) - h i • D i y)‖
      ≤ ∑ i : Fin d, c' * ‖h‖ := norm_sum_le_of_le _ (fun i _ => hstep i)
    _ = d * c' * ‖h‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ c * ‖h‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg h)
        rw [hc', ← mul_div_assoc, div_le_iff₀ (by positivity)]
        nlinarith

end PI.UnitaryGroupMassFormula.JCC.Ck
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothVectorsOfLieClosedFamily

section

@[expose] public section

open Matrix
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SmoothCrit

open GlobalTheory.UnitarySmVec GlobalTheory.HolDict

section Mat
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ}

theorem contDiff_expM : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
  contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt

theorem contDiff_init {k : ℕ} : ContDiff ℝ ∞ fun t : Fin (k + 1) → ℝ => Fin.init t :=
  contDiff_pi.2 fun j => contDiff_apply ℝ (fun _ => ℝ) (Fin.castSucc j)

theorem contDiff_pr : ∀ {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ), ContDiff ℝ ∞ (pr Xs)
  | 0, Xs => by
    have e : pr Xs = fun _ => 1 := funext (pr_zero Xs)
    rw [e]
    exact contDiff_const
  | k + 1, Xs => by
    have e : pr Xs = fun t => pr (Fin.init Xs) (Fin.init t) * NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k)) :=
      funext (pr_succ Xs)
    rw [e]
    exact ((contDiff_pr (Fin.init Xs)).comp contDiff_init).mul
      (contDiff_expM.comp ((contDiff_apply ℝ (fun _ => ℝ) (Fin.last k)).smul contDiff_const))

theorem coord {Hm : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit Hm.det) : ∀ {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ),
    (∀ j, Xs j ∈ lieH Hm) → ∀ m : Fin k, ∃ Y : (Fin k → ℝ) → Matrix (Fin n) (Fin n) ℂ, ContDiff ℝ ∞ Y ∧
      (∀ t, Y t ∈ lieH Hm) ∧
      ∀ (t : Fin k → ℝ) (s : ℝ), pr Xs (t + s • Pi.single m 1) = pr Xs t * NormedSpace.exp (s • Y t) := by
  intro k
  induction k with
  | zero => exact fun _ _ m => m.elim0
  | succ k ih =>
    intro Xs hX m
    refine Fin.lastCases ?_ (fun m' => ?_) m
    · refine ⟨fun _ => Xs (Fin.last k), contDiff_const, fun _ => hX _, fun t s => ?_⟩
      have e1 : Fin.init (t + s • Pi.single (Fin.last k) (1:ℝ)) = Fin.init t := by
        funext j
        simp [Fin.init, Fin.castSucc_ne_last]
      have e2 : (t + s • Pi.single (Fin.last k) (1:ℝ) : Fin (k + 1) → ℝ) (Fin.last k) = t (Fin.last k) + s := by simp
      rw [pr_succ, pr_succ Xs t, e1, e2, add_smul,
        Matrix.exp_add_of_commute _ _ (((Commute.refl (Xs (Fin.last k))).smul_left _).smul_right _), mul_assoc]
    · obtain ⟨Y', hY', hYl, hYe⟩ := ih (Fin.init Xs) (fun j => hX (Fin.castSucc j)) m'
      refine ⟨fun t => NormedSpace.exp (-(t (Fin.last k) • Xs (Fin.last k))) * Y' (Fin.init t) *
        NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k)), ?_, ?_, ?_⟩
      · have hl : ContDiff ℝ ∞ fun t : Fin (k+1) → ℝ => t (Fin.last k) • Xs (Fin.last k) :=
          (contDiff_apply ℝ (fun _ => ℝ) (Fin.last k)).smul contDiff_const
        exact ((contDiff_expM.comp hl.neg).mul (hY'.comp contDiff_init)).mul (contDiff_expM.comp hl)
      · intro t
        have hg := exp_mem hu (hX (Fin.last k)) (t (Fin.last k))
        have := lie_conj hu (hYl (Fin.init t)) hg
        simpa only [Matrix.exp_neg] using this
      · intro t s
        have e1 : Fin.init (t + s • Pi.single (Fin.castSucc m') (1:ℝ)) = Fin.init t + s • Pi.single m' 1 := by
          funext j
          simp [Fin.init, Pi.single_apply]
        have e2 : (t + s • Pi.single (Fin.castSucc m') (1:ℝ) : Fin (k + 1) → ℝ) (Fin.last k) = t (Fin.last k) := by
          simp [(Fin.castSucc_lt_last m').ne']
        rw [pr_succ, pr_succ Xs t, e1, e2, hYe]
        beta_reduce
        rw [Matrix.exp_neg]
        have hgd : IsUnit (NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k))).det :=
          det_unit hu (exp_mem hu (hX (Fin.last k)) (t (Fin.last k)))
        have hgu : IsUnit (NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k))) := (isUnit_iff_isUnit_det _).2 hgd
        set g := NormedSpace.exp (t (Fin.last k) • Xs (Fin.last k))
        rw [show s • (g⁻¹ * Y' (Fin.init t) * g) = g⁻¹ * (s • Y' (Fin.init t)) * g by
            rw [Matrix.mul_smul, Matrix.smul_mul], Matrix.exp_conj' _ _ hgu, mul_assoc, mul_assoc, mul_assoc,
          ← mul_assoc g, mul_nonsing_inv _ hgd, one_mul]

end Mat

section Main
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable {n : ℕ} {Hm : Matrix (Fin n) (Fin n) ℂ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ι : Type} {v : ι → H} {δ : Matrix (Fin n) (Fin n) ℂ → ι → ι}

theorem v_zero (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) (i : ι) : v (δ 0 i) = 0 := by
  simpa using hs i 0 0

theorem v_sum (ha : ∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i))
    (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) {β : Type} (s : Finset β)
    (f : β → Matrix (Fin n) (Fin n) ℂ) (i : ι) : v (δ (∑ b ∈ s, f b) i) = ∑ b ∈ s, v (δ (f b) i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using v_zero hs i
  | insert b s hb ih => rw [Finset.sum_insert hb, Finset.sum_insert hb, ha, ih]

theorem v_expand (ha : ∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i))
    (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) (Y : Matrix (Fin n) (Fin n) ℂ) (i : ι) :
    v (δ Y i) = ∑ a, ∑ c, (((Y a c).re : ℂ) • v (δ (single a c 1) i) +
      ((Y a c).im : ℂ) • v (δ (Complex.I • single a c 1) i)) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Y]
  rw [v_sum ha hs]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [v_sum ha hs]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e : single a c (Y a c) = ((Y a c).re : ℂ) • single a c 1 + ((Y a c).im : ℂ) • (Complex.I • single a c 1) := by
    rw [smul_smul, ← add_smul, Matrix.smul_single, smul_eq_mul, mul_one, Complex.re_add_im]
  rw [e, ha, hs, hs]

theorem crit_nat (hu : IsUnit Hm.det) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ)
    (ha : ∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i))
    (hs : ∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i))
    (hd : ∀ X, Xᴴ * Hm + Hm * X = 0 → ∀ i, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (v i)) (v (δ X i)) 0)
    {k : ℕ} (Xs : Fin k → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ j, Xs j ∈ lieH Hm) (N : ℕ) :
    ∀ i, ContDiff ℝ N fun t => σ (pr Xs t) (v i) := by
  choose Y hY hYl hYe using coord hu Xs hX
  induction N with
  | zero =>
    intro i
    simp only [Nat.cast_zero, contDiff_zero]
    exact (hσ.2.2 (v i)).comp_continuous (contDiff_pr Xs).continuous fun t => pr_mem hu Xs hX t
  | succ N ih =>
    intro i
    let D : Fin k → (Fin k → ℝ) → H := fun m t => ∑ a, ∑ c,
      ((Y m t a c).re • σ (pr Xs t) (v (δ (single a c 1) i)) +
        (Y m t a c).im • σ (pr Xs t) (v (δ (Complex.I • single a c 1) i)))
    have hD : ∀ m, ContDiff ℝ N (D m) := by
      intro m
      have he : ∀ a c, ContDiff ℝ ∞ fun t => Y m t a c := fun a c =>
        (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a c)).contDiff.comp (hY m)
      refine ContDiff.sum fun a _ => ContDiff.sum fun c _ => ?_
      exact ((contDiff_infty.1 (Complex.reCLM.contDiff.comp (he a c)) N).smul (ih _)).add
        ((contDiff_infty.1 (Complex.imCLM.contDiff.comp (he a c)) N).smul (ih _))
    have hpart : ∀ y m, HasDerivAt (fun s : ℝ => σ (pr Xs (y + s • Pi.single m (1:ℝ))) (v i)) (D m y) 0 := by
      intro y m
      have e : (fun s : ℝ => σ (pr Xs (y + s • Pi.single m (1:ℝ))) (v i)) =
          fun s => σ (pr Xs y) (σ (NormedSpace.exp (s • Y m y)) (v i)) := by
        funext s
        rw [hYe, hσ.1.2 _ (pr_mem hu Xs hX y) _ (exp_mem hu (hYl m y) s)]
        rfl
      rw [e]
      have h1 : HasDerivAt (fun s : ℝ => σ (pr Xs y) (σ (NormedSpace.exp (s • Y m y)) (v i)))
          (σ (pr Xs y) (v (δ (Y m y) i))) 0 :=
        ((σ (pr Xs y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hd _ (hYl m y) i)
      convert h1 using 1
      show _ = σ (pr Xs y) (v (δ (Y m y) i))

      rw [v_expand ha hs (Y m y) i, map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_

      rw [map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_add (f := _), map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]
    rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun y => ∑ m, (ContinuousLinearMap.proj m : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (D m y), ?_, fun y => ?_⟩
    · exact ContDiff.sum fun m _ => contDiff_const.smulRight (hD m)
    · exact PI.UnitaryGroupMassFormula.JCC.Ck.partials_continuous_differentiable k H Set.univ _ D isOpen_univ (fun m => (hD m).continuous.continuousOn)
        (fun y _ m => hpart y m) y trivial

end Main

theorem smoothVec_of_closed_family : ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : Type) (v : ι → H) (δ : Matrix (Fin n) (Fin n) ℂ → ι → ι), Hm.det ≠ 0 → Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → (∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i)) → (∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) → (∀ X, Xᴴ * Hm + Hm * X = 0 → ∀ i, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (v i)) (v (δ X i)) 0) → ∀ i, Formalism.L2.Theta.SmoothVec {X | Xᴴ * Hm + Hm * X = 0} σ (v i) := by
  intro n Hm H _ _ σ ι v δ hdet hσ ha hs hd i k Xs hX
  have hu : IsUnit Hm.det := isUnit_iff_ne_zero.2 hdet
  exact contDiff_infty.2 fun N => crit_nat hu hσ ha hs hd Xs hX N i

end GlobalTheory.SmoothCrit
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothVectorsOfLieClosedFamilyStatement

section

@[expose] public section

open Matrix
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.smoothVectors_of_lie_closed_family : ∀ (n : ℕ) (Hm : Matrix (Fin n) (Fin n) ℂ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (ι : Type) (v : ι → H) (δ : Matrix (Fin n) (Fin n) ℂ → ι → ι), Hm.det ≠ 0 → Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → (∀ i X Y, v (δ (X + Y) i) = v (δ X i) + v (δ Y i)) → (∀ i (c : ℝ) X, v (δ ((c : ℂ) • X) i) = (c : ℂ) • v (δ X i)) → (∀ X, Xᴴ * Hm + Hm * X = 0 → ∀ i, HasDerivAt (fun t : ℝ => σ (NormedSpace.exp (t • X)) (v i)) (v (δ X i)) 0) → ∀ i, Formalism.L2.Theta.SmoothVec {X | Xᴴ * Hm + Hm * X = 0} σ (v i) := by
  first | exact @GlobalTheory.SmoothCrit.smoothVec_of_closed_family | exact GlobalTheory.SmoothCrit.smoothVec_of_closed_family | (intros; apply GlobalTheory.SmoothCrit.smoothVec_of_closed_family <;> assumption)
end
end
