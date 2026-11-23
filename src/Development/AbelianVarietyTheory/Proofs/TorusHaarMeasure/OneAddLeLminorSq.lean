module

public import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantOrthogonality
public import ReciprocityTheory.SemistableReduction.ShareBallB
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneLeMinorOfIsOrth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ENatToNat
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.SumBoundStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DetSubUpper
public import ReciprocityTheory.SemistableReduction.ShareSt
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import ReciprocityTheory.SemistableReduction.ShareBallA
public import ReciprocityTheory.SemistableReduction.ShareBallC
import ReciprocityTheory.SemistableReduction.ShareBallA
import ReciprocityTheory.SemistableReduction.ShareBallC

-- Source module: ReciprocityTheory.SemistableReduction.ShareBall

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField
open scoped ComplexOrder

theorem boundedBall_holds : BoundedBallStatement := by
  intro r p H s hH hJ hs0 hs1 hP u
  have hHh : Hᴴ = H := hH.isHermitian
  have hsurj := sb_setup hH hJ hP
  have hTT : ∀ v, signMat p r *ᵥ (H *ᵥ (signMat p r *ᵥ (H *ᵥ v))) = v := fun v => by
    rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc H, hJ, sb_J_mul_J, one_mulVec]
  have hHx : ∀ x, signMat p r *ᵥ (H *ᵥ x) = x → H *ᵥ x = signMat p r *ᵥ x := fun x hx => by
    calc H *ᵥ x = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ x)) := by
          rw [mulVec_mulVec, sb_J_mul_J, one_mulVec]
      _ = _ := by rw [hx]
  have hHy : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → H *ᵥ y = -(signMat p r *ᵥ y) := fun y hy => by
    calc H *ᵥ y = signMat p r *ᵥ (signMat p r *ᵥ (H *ᵥ y)) := by
          rw [mulVec_mulVec, sb_J_mul_J, one_mulVec]
      _ = _ := by rw [hy, mulVec_neg]
  have horth : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y →
      star x ⬝ᵥ (signMat p r *ᵥ y) = 0 := by
    intro x y hx hy
    have e := sb_herm_swap hHh x y
    rw [hHy y hy, hHx x hx, dotProduct_neg, ← sb_herm_swap (sb_J_herm p r)] at e
    linear_combination (-1 / 2 : ℂ) * e
  have horth' : ∀ x y, signMat p r *ᵥ (H *ᵥ x) = x → signMat p r *ᵥ (H *ᵥ y) = -y →
      star y ⬝ᵥ (signMat p r *ᵥ x) = 0 := by
    intro x y hx hy
    have e := sb_herm_swap hHh y x
    rw [hHx x hx, hHy y hy, star_neg, neg_dotProduct, ← sb_herm_swap (sb_J_herm p r)] at e
    linear_combination (1 / 2 : ℂ) * e
  have hNprop : ∀ y, signMat p r *ᵥ (H *ᵥ y) = -y → posSq p y ≤ s ^ 2 * negSq p y := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := hsurj y
    have o := horth x y hx hy
    rw [sb_dot_J, sub_eq_zero, hxy] at o
    have hA : posSq p y = (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re := by
      rw [← o, sb_re_star_dot, sb_posSq_eq]
    have cs := sb_cs (sbDn p r *ᵥ x) (sbDn p r *ᵥ y)
    rw [← hA, ← sb_negSq_eq, ← sb_negSq_eq] at cs
    have hx' := hP x hx
    have hpx : posSq p x = posSq p y := by rw [sb_posSq_eq, sb_posSq_eq, hxy]
    have hA0 : 0 ≤ posSq p y := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
    have hD0 : 0 ≤ negSq p y := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
    rw [hpx] at hx'
    rcases hA0.eq_or_lt with h | h
    · rw [← h]; positivity
    · have h2 := mul_le_mul_of_nonneg_right hx' hD0
      exact le_of_mul_le_mul_left (by nlinarith : posSq p y * posSq p y ≤
        posSq p y * (s ^ 2 * negSq p y)) h
  have hdec : ∃ x y, signMat p r *ᵥ (H *ᵥ x) = x ∧ signMat p r *ᵥ (H *ᵥ y) = -y ∧ x + y = u :=
    ⟨(1 / 2 : ℂ) • (u + signMat p r *ᵥ (H *ᵥ u)), (1 / 2 : ℂ) • (u - signMat p r *ᵥ (H *ᵥ u)),
      by rw [mulVec_smul, mulVec_smul, mulVec_add, mulVec_add, hTT, add_comm],
      by rw [mulVec_smul, mulVec_smul, mulVec_sub, mulVec_sub, hTT, ← smul_neg, neg_sub],
      by ext k; simp; ring⟩
  obtain ⟨x, y, hx, hy, rfl⟩ := hdec
  have hPx := hP x hx
  have hPy := hNprop y hy
  set t := (star (sbDp p r *ᵥ x) ⬝ᵥ (sbDp p r *ᵥ y)).re with htdef
  have ht2 : (star (sbDn p r *ᵥ x) ⬝ᵥ (sbDn p r *ᵥ y)).re = t := by
    have o := horth x y hx hy
    rw [sb_dot_J, sub_eq_zero] at o
    rw [htdef, o]
  have hq_eq : hq H (x + y) = posSq p x - negSq p x - posSq p y + negSq p y := by
    have e1 := sb_re_dot_J p x
    have e2 := sb_re_dot_J p y
    rw [hq, mulVec_add, hHx x hx, hHy y hy, star_add]
    simp only [add_dotProduct, dotProduct_add, dotProduct_neg]
    rw [horth x y hx hy, horth' x y hx hy]
    simp only [Complex.add_re, Complex.neg_re, Complex.zero_re]
    linarith
  have hn_eq : normSq (x + y) =
      posSq p x + negSq p x + posSq p y + negSq p y + 4 * t := by
    have a3 : (star x ⬝ᵥ y).re = 2 * t := by rw [sb_dot_split p, Complex.add_re, ht2]; ring
    have a4 : (star y ⬝ᵥ x).re = 2 * t := by rw [sb_re_dot_comm, a3]
    rw [← sb_re_star_dot, star_add]
    simp only [add_dotProduct, dotProduct_add, Complex.add_re]
    rw [a3, a4, sb_re_star_dot, sb_re_star_dot, sb_normSq_split p x, sb_normSq_split p y]
    ring
  have hA0 : 0 ≤ posSq p x := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
  have hB0 : 0 ≤ negSq p x := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
  have hC0 : 0 ≤ posSq p y := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
  have hD0 : 0 ≤ negSq p y := by rw [sb_negSq_eq]; exact sb_normSq_nonneg _
  have hts1 : t ^ 2 ≤ posSq p x * posSq p y := by
    rw [sb_posSq_eq, sb_posSq_eq]; exact sb_cs _ _
  have hts2 : t ^ 2 ≤ negSq p x * negSq p y := by
    rw [← ht2, sb_negSq_eq, sb_negSq_eq]; exact sb_cs _ _
  have hsq : ∀ z : ℝ, 0 ≤ z → Real.sqrt (s ^ 2 * z) = s * Real.sqrt z := fun z hz => by
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]
  have hb : Real.sqrt (negSq p x) ≤ s * Real.sqrt (posSq p x) :=
    (Real.sqrt_le_sqrt hPx).trans (le_of_eq (hsq _ hA0))
  have hc : Real.sqrt (posSq p y) ≤ s * Real.sqrt (negSq p y) :=
    (Real.sqrt_le_sqrt hPy).trans (le_of_eq (hsq _ hD0))
  have h1 : |t| ≤ Real.sqrt (posSq p x) * Real.sqrt (posSq p y) := by
    rw [← Real.sqrt_mul hA0]; exact Real.abs_le_sqrt hts1
  have h2 : |t| ≤ Real.sqrt (negSq p x) * Real.sqrt (negSq p y) := by
    rw [← Real.sqrt_mul hB0]; exact Real.abs_le_sqrt hts2
  obtain ⟨hU, hL⟩ := sb_real_bounds _ _ _ _ s t (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hs0 hs1 hb hc h1 h2
  rw [Real.sq_sqrt hA0, Real.sq_sqrt hB0, Real.sq_sqrt hC0, Real.sq_sqrt hD0] at hU hL
  have h1s : 0 < 1 - s := by linarith
  rw [hq_eq, hn_eq]
  constructor
  · rw [div_mul_eq_mul_div, le_div_iff₀ h1s]; nlinarith
  · rw [div_mul_eq_mul_div, le_div_iff₀ h1s]; nlinarith

end ReciprocityTheory.MultiplicativeHeights
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneAddLeLminorSq

section

@[expose] public section

namespace GlobalTheory.Up.BallExPf

section Mat
open Matrix ReciprocityTheory.MultiplicativeHeights
open scoped ComplexOrder MatrixOrder

theorem exists_unitary_diag {r p : ℕ} {H : Matrix (Fin r) (Fin r) ℂ} (hH : H.PosDef)
    (hJ : H * signMat p r * H = signMat p r) :
    ∃ g : Matrix (Fin r) (Fin r) ℂ, gᴴ * signMat p r * g = signMat p r ∧ gᴴ * H * g = 1 := by
  set J := signMat p r with hJdef
  have hJJ : J * J = 1 := sb_J_mul_J p r
  have hJh : Jᴴ = J := sb_J_herm p r
  set S := CFC.sqrt H with hS
  have hSS : S * S = H := CFC.sqrt_mul_sqrt_self H hH.posSemidef.nonneg
  have hSp : S.PosSemidef := Matrix.nonneg_iff_posSemidef.1 (CFC.sqrt_nonneg H)
  have hSh : Sᴴ = S := hSp.1
  have hSu : IsUnit S.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have := hH.det_pos
    rw [← hSS, det_mul, h0, mul_zero] at this
    exact lt_irrefl _ this
  have h1 : (J * S * J).PosSemidef := by
    have := hSp.conjTranspose_mul_mul_same J
    rwa [hJh] at this
  have h2 : (S⁻¹).PosSemidef := hSp.inv
  have hsq1 : (J * S * J) * (J * S * J) = J * H * J := by
    calc (J * S * J) * (J * S * J) = J * S * (J * J) * S * J := by simp only [Matrix.mul_assoc]
      _ = J * H * J := by rw [hJJ, Matrix.mul_one, ← hSS]; simp only [Matrix.mul_assoc]
  have hsq2 : S⁻¹ * S⁻¹ = J * H * J := by
    rw [← Matrix.mul_inv_rev, hSS]
    apply Matrix.inv_eq_right_inv
    calc H * (J * H * J) = (H * J * H) * J := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hJ, hJJ]
  have he : J * S * J = S⁻¹ := by
    rw [← CFC.sqrt_unique hsq1 h1.nonneg, ← CFC.sqrt_unique hsq2 h2.nonneg]
  have hih : (S⁻¹)ᴴ = S⁻¹ := h2.1
  refine ⟨S⁻¹, ?_, ?_⟩
  · rw [hih]
    conv_lhs => rw [show S⁻¹ * J * S⁻¹ = (J * S * J) * J * S⁻¹ by rw [he]]
    calc J * S * J * J * S⁻¹ = J * S * (J * J) * S⁻¹ := by simp only [Matrix.mul_assoc]
      _ = J := by rw [hJJ, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_right _ _ hSu]
  · rw [hih, ← hSS, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hSu, Matrix.one_mul,
      Matrix.mul_nonsing_inv _ hSu]

theorem exists_frame {r p : ℕ} {H A P : Matrix (Fin r) (Fin r) ℂ} (hH : H.PosDef)
    (hA : H * A⁻¹ * H = A) (hP : P.det ≠ 0) (hPA : Pᴴ * A * P = signMat p r) :
    ∃ x : Matrix (Fin r) (Fin r) ℂ, xᴴ * A * x = signMat p r ∧ xᴴ * H * x = 1 := by
  have hJJ := sb_J_mul_J p r
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have hH' : (Pᴴ * H * P).PosDef := hH.conjTranspose_mul_mul_same
    (Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hPu))
  have hAi : A⁻¹ = P * signMat p r * Pᴴ := by
    apply Matrix.inv_eq_left_inv
    have : signMat p r * (Pᴴ * A * P) = 1 := by rw [hPA, hJJ]
    calc P * signMat p r * Pᴴ * A = P * (signMat p r * (Pᴴ * A * P)) * P⁻¹ := by
          simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPu, Matrix.mul_one]
      _ = 1 := by rw [this, Matrix.mul_one, Matrix.mul_nonsing_inv _ hPu]
  obtain ⟨g, hg1, hg2⟩ := exists_unitary_diag (p := p) hH' (by
    calc Pᴴ * H * P * signMat p r * (Pᴴ * H * P) = Pᴴ * (H * (P * signMat p r * Pᴴ) * H) * P := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [← hAi, hA, hPA])
  refine ⟨P * g, ?_, ?_⟩
  · rw [← hg1, ← hPA, conjTranspose_mul]; simp only [Matrix.mul_assoc]
  · rw [← hg2, conjTranspose_mul]; simp only [Matrix.mul_assoc]

theorem hq_ct_mul {r : ℕ} (Q : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    hq (Qᴴ * Q) u = normSq (Q *ᵥ u) := by
  rw [hq, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose, star_star, sb_re_star_dot]

theorem one_add_le_lminor_sq {n p : ℕ} (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᴴ * signMat p n * g = signMat p n) :
    1 + ∑ a, ∑ b, ‖(sbDn p n * g * sbDp p n) a b‖ ^ 2 ≤
      ‖ReciprocityTheory.ChartRestriction.G.FD.lminor g ⟨p, Nat.lt_succ_of_le h⟩‖ ^ 2 := by
  set A : Matrix (Fin p) (Fin p) ℂ := g.submatrix (Fin.castLE h) (Fin.castLE h) with hA
  set C : Matrix (Fin n) (Fin p) ℂ :=
    Matrix.of fun k a => if (k : ℕ) < p then 0 else g k (Fin.castLE h a) with hC
  have key : Aᴴ * A = 1 + Cᴴ * C := by
    ext a b
    have e := congrFun (congrFun hg (Fin.castLE h a)) (Fin.castLE h b)
    rw [Matrix.mul_apply] at e
    simp only [signMat, Matrix.mul_diagonal, Matrix.conjTranspose_apply,
      Matrix.diagonal_apply, Fin.castLE_inj] at e
    have e1 : (1 : Matrix (Fin p) (Fin p) ℂ) a b =
        ∑ k, star (g k (Fin.castLE h a)) * sgn p k * g k (Fin.castLE h b) := by
      rw [e, Matrix.one_apply]
      by_cases hab : a = b
      · subst hab; simp [sgn]
      · rw [if_neg hab, if_neg hab]
    have e2 : (Aᴴ * A) a b = ∑ k : Fin n, if (k : ℕ) < p then
        starRingEnd ℂ (g k (Fin.castLE h a)) * g k (Fin.castLE h b) else 0 := by
      rw [Matrix.mul_apply]
      refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_)
        (fun k => ?_)
      · rw [if_neg]
        intro hlt
        exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
      · simp [hA, Matrix.conjTranspose_apply]
    rw [e2, Matrix.add_apply, e1, Matrix.mul_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < p
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply]
    · simp [hC, sgn, hk, Matrix.conjTranspose_apply]
  have h1 := ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_det_one_add_ge (Matrix.posSemidef_conjTranspose_mul_self C)
  rw [← key, ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_normSq_det, ReciprocityTheory.ChartRestriction.G.AR.Up.sumBd_trace_ctm] at h1
  have h2 : ∑ a, ∑ b, ‖(sbDn p n * g * sbDp p n) a b‖ ^ 2 = ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdFsq C := by
    unfold ReciprocityTheory.ChartRestriction.G.AR.Up.sumBdFsq
    refine Finset.sum_congr rfl fun k _ => ?_
    symm
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun b hb => ?_)
      (fun b => ?_)
    · have : ¬ (b : ℕ) < p := fun hlt => hb ⟨⟨b, hlt⟩, Fin.ext rfl⟩
      simp [sbDn, sbDp, Matrix.mul_diagonal, this]
    · by_cases hk : (k : ℕ) < p <;>
        simp [sbDn, sbDp, Matrix.mul_diagonal, Matrix.diagonal_mul, hC, hk, Complex.normSq_eq_norm_sq]
  rw [h2, ← Complex.normSq_eq_norm_sq]
  exact h1

theorem norm_bound {n p : ℕ} (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ)
    (hg : gᴴ * signMat p n * g = signMat p n) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hl : -Real.log (1 / ‖ReciprocityTheory.ChartRestriction.G.FD.lminor g ⟨p, Nat.lt_succ_of_le h⟩‖ ^ 2) ≤ s ^ 2)
    (u : Fin n → ℂ) :
    normSq (g⁻¹ *ᵥ u) ≤ (1 + s) / (1 - s) * normSq u ∧
      normSq (g *ᵥ u) ≤ (1 + s) / (1 - s) * normSq u := by
  set J := signMat p n with hJdef
  have hJJ : J * J = 1 := sb_J_mul_J p n
  have hJh : Jᴴ = J := sb_J_herm p n
  have hinv : g⁻¹ = J * gᴴ * J := by
    apply Matrix.inv_eq_left_inv
    calc J * gᴴ * J * g = J * (gᴴ * J * g) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, hJJ]
  have hgu : IsUnit g.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    have e := congrArg det hg
    have e2 := congrArg det hJJ
    rw [det_mul, h0, mul_zero] at e
    rw [det_mul, ← e, det_one] at e2
    simp at e2
  have hinvH : (g⁻¹)ᴴ = J * g * J := by
    rw [hinv, conjTranspose_mul, conjTranspose_mul, hJh, conjTranspose_conjTranspose, Matrix.mul_assoc]
  set c := ∑ a, ∑ b, ‖(sbDn p n * g * sbDp p n) a b‖ ^ 2 with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hc1 := one_add_le_lminor_sq h g hg
  rw [← hc] at hc1
  have hcs : c ≤ s ^ 2 * (1 + c) := by
    rw [one_div, Real.log_inv, neg_neg] at hl
    have a1 : Real.log (1 + c) ≤ s ^ 2 := (Real.log_le_log (by linarith) hc1).trans hl
    have a2 := Real.one_sub_inv_le_log_of_pos (show 0 < 1 + c by linarith)
    have a3 : 1 - (1 + c)⁻¹ = c / (1 + c) := by field_simp; ring
    rw [a3] at a2
    exact (div_le_iff₀ (by linarith)).1 (a2.trans a1)
  have hB := boundedBall_holds n p ((g⁻¹)ᴴ * g⁻¹) s
    (Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _ hgu))))
    (by
      rw [← hJdef, hinvH]
      calc J * g * J * g⁻¹ * J * (J * g * J * g⁻¹) = J * g * J * g⁻¹ * (J * J) * g * J * g⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = J * g * (J * J) * g⁻¹ := by
            rw [hJJ, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_right _ _ hgu]
            simp only [Matrix.mul_assoc, hJJ]
        _ = J := by rw [hJJ, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_right _ _ hgu])
    hs0 hs1 (by
      intro v hv
      set w := g⁻¹ *ᵥ v with hw
      have hvw : g *ᵥ w = v := by rw [hw, mulVec_mulVec, Matrix.mul_nonsing_inv _ hgu, one_mulVec]
      have hJw : J *ᵥ w = w := by
        rw [← hJdef, ← mulVec_mulVec, ← hw, hinvH, mulVec_mulVec, ← Matrix.mul_assoc,
          ← Matrix.mul_assoc, hJJ, Matrix.one_mul] at hv
        have := congrArg (fun y => g⁻¹ *ᵥ y) hv
        simpa only [mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_left _ _ hgu, ← hw] using this
      have hDw : sbDp p n *ᵥ w = w := by
        funext k
        have := congrFun hJw k
        simp only [hJdef, signMat, mulVec_diagonal, sgn, sbDp] at this ⊢
        split_ifs at this ⊢
        · simp
        · linear_combination (1 / 2 : ℂ) * this
      have b1 : negSq p v ≤ c * normSq w := by
        rw [sb_negSq_eq, ← hvw]
        conv_lhs => rw [← hDw, mulVec_mulVec, mulVec_mulVec]
        exact sb_normSq_mulVec_le _ _
      have b2 : posSq p v - negSq p v = normSq w := by
        rw [← sb_re_dot_J, ← hJdef, ← sb_re_star_dot]
        conv_rhs => rw [show star w ⬝ᵥ w = star w ⬝ᵥ ((gᴴ * J * g) *ᵥ w) by rw [hg, hJw]]
        rw [← mulVec_mulVec, ← mulVec_mulVec, hvw, dotProduct_mulVec (star w), vecMul_conjTranspose,
          star_star, hvw]
      have b3 : 0 ≤ normSq w := sb_normSq_nonneg w
      have b4 : 0 ≤ posSq p v := by rw [sb_posSq_eq]; exact sb_normSq_nonneg _
      have b5 : negSq p v * (1 + c) ≤ s ^ 2 * posSq p v * (1 + c) := by
        have := mul_le_mul_of_nonneg_right hcs b4
        rw [← b2] at b1
        nlinarith
      exact le_of_mul_le_mul_right b5 (by linarith))
  refine ⟨?_, ?_⟩
  · have := (hB u).1
    rwa [hq_ct_mul] at this
  · have := (hB (g *ᵥ u)).2
    rwa [hq_ct_mul, mulVec_mulVec, Matrix.nonsing_inv_mul _ hgu, one_mulVec] at this

theorem hq_conj {r : ℕ} (H : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    hq (H.map (starRingEnd ℂ)) (star u) = hq H u := by
  unfold hq
  rw [← Complex.conj_re (star u ⬝ᵥ _)]
  congr 1

  simp [dotProduct, mulVec, map_sum]

end Mat

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_iff (X : Data E r) (τ : E →+* ℂ) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ X.Gm M = (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) ↔
      Mᴴ * (MajorantOrthogonality.pform X).G.map τ * M = ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r := by
  have e1 : (gram τ X.Gm M)ᵀ = Mᴴ * (MajorantOrthogonality.pform X).G.map τ * M := by
    rw [FrameDegreeData.gram_eq, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
    rfl
  have e2 : (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))ᵀ =
      ReciprocityTheory.MultiplicativeHeights.signMat X.p0 r := by
    rw [Matrix.diagonal_transpose, ReciprocityTheory.MultiplicativeHeights.signMat]
    congr 1
    funext k
    simp [ReciprocityTheory.ChartRestriction.G.FD.sgn,
      ReciprocityTheory.MultiplicativeHeights.sgn]
    split_ifs <;> simp
  rw [← e1, ← e2, Matrix.transpose_inj]

theorem frame_bound (hr : 0 < r) (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0)
    (h1 : IsOrth X x1) (hρ : rhX X x0 x1 < 1 / (49 * (r : ℝ) ^ 2)) (τ : X.Ψ) (u : Fin r → ℂ) :
    ReciprocityTheory.MultiplicativeHeights.normSq (((mat x0 τ)⁻¹ * mat x1 τ)⁻¹ *ᵥ u) ≤
        ReciprocityTheory.MultiplicativeHeights.ballRatio r * ReciprocityTheory.MultiplicativeHeights.normSq u ∧
      ReciprocityTheory.MultiplicativeHeights.normSq (((mat x0 τ)⁻¹ * mat x1 τ) *ᵥ u) ≤
        ReciprocityTheory.MultiplicativeHeights.ballRatio r * ReciprocityTheory.MultiplicativeHeights.normSq u := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hu : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x0 h0 τ)
  refine norm_bound X.p0_le _ ?_ (by positivity) ?_ ?_ u
  · have a0 := (gram_iff X τ.1 _).1 (h0 τ)
    have a1 := (gram_iff X τ.1 _).1 (h1 τ)
    conv_lhs => rw [← a0]
    rw [← a1]
    conv_rhs => rw [← Matrix.mul_nonsing_inv_cancel_left _ (mat x1 τ) hu, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  · rw [div_lt_one (by positivity)]; linarith
  · have := neg_log_factor_le_rhX h0 (IW.orth_mem_dom X x1 h1) τ
    rw [FramePotential.norm_dmin_of_isOrth X h1] at this
    refine this.trans (hρ.le.trans (le_of_eq ?_))
    field_simp
    norm_num

end GlobalTheory.Up.BallExPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.Up
open BallExPf

end GlobalTheory.Up
end
end
