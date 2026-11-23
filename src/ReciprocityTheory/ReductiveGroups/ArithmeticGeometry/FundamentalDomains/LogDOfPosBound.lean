module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LminorSubmatrixCastSucc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BfSubRight
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SignTypeCancelIdentity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LowBlock
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NsqMulVecLeOpN

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PivotNeg

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma Bf_single (Z : X.Coord) (τ : X.Ψ) (j k : Fin r) :
    Bf X Z τ (Pi.single j 1) (Pi.single k 1) = Gp X Z τ j k := by
  unfold Bf
  simp [Pi.single_apply]

lemma Bf_split (Z : X.Coord) (τ : X.Ψ) (v t : Fin r → ℂ) (h1 : Bf X Z τ v t = 0) :
    Bf X Z τ v v = Bf X Z τ (v - t) (v - t) - Bf X Z τ t t := by
  have h2 : Bf X Z τ t v = 0 := by rw [Bf_conj, h1, map_zero]
  simp only [Bf_sub_left, Bf_sub_right]
  rw [h1, h2]
  ring

lemma blk_Gp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (c : Fin r) : (blk (Gp X Z τ) c).det ≠ 0 := by
  rw [← gram_xZ X ho Z τ]
  exact blk_det X (xZ_mem_dom X hx ho hZ) τ c

lemma dOf_eq {x : Frame X.Ψ r} (ho : X.IsOrtho x) (Z : X.Coord) (τ : X.Ψ) (k : Fin r) :
    dOf X (X.xZ x Z) τ k = Bf X Z τ (fun a => uMat (Gp X Z τ) a k) (fun a => uMat (Gp X Z τ) a k) := by
  have hG : gram τ.1 X.Gm (mat (X.xZ x Z) τ) = Gp X Z τ := gram_xZ X ho Z τ
  unfold dOf uOf
  rw [hG]
  set M := mat (X.xZ x Z) τ with hM
  set U := uMat (Gp X Z τ) with hU
  have hcol : col (M * U) k = ∑ a, U a k • col M a := by
    funext i
    simp [col, Matrix.mul_apply, Finset.sum_apply, mul_comm]
  show hermC τ.1 X.Gm (col (M * U) k) (col (M * U) k) = _
  rw [hcol, hermC_quad]
  unfold Bf
  rw [← hG]
  rfl

lemma pivot_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (k : Fin r) (hk : (k : ℕ) < X.p0) :
    1 - X.zN Z ^ 2 ≤ (dOf X (X.xZ x Z) τ k).re ∧ (dOf X (X.xZ x Z) τ k).re ≤ 1 := by
  have hdet := blk_Gp X hx ho hZ τ
  have hz0 : 0 ≤ X.zN Z := Real.iSup_nonneg fun τ => opN_nonneg _
  have hz1 : 0 ≤ 1 - X.zN Z ^ 2 := by nlinarith
  rw [dOf_eq X ho Z τ k]
  set v : Fin r → ℂ := fun a => uMat (Gp X Z τ) a k with hv
  have hvk : v k = 1 := by simp [hv, uMat]
  have hvgt : ∀ b, k < b → v b = 0 := by
    intro b hb
    simp [hv, uMat, hb.ne', not_lt.mpr hb.le]
  set t : Fin r → ℂ := fun b => if b < k then v b else 0 with ht
  have ht0 : ∀ b, k ≤ b → t b = 0 := fun b hb => by simp [ht, not_lt.mpr hb]
  have hvt : Bf X Z τ v t = 0 := Bf_gv_zero X Z τ hdet k t ht0
  have hsplit := Bf_split X Z τ v t hvt
  have hsingle : v - t = Pi.single k 1 := by
    funext b
    rcases lt_trichotomy b k with hb | hb | hb
    · simp [ht, hb, hb.ne]
    · rw [hb]
      simp [ht, hvk]
    · simp [ht, not_lt.mpr hb.le, hvgt b hb, hb.ne']
  rw [hsingle, Bf_single] at hsplit
  have hvn : ∀ m, v (nI X m) = 0 := fun m => hvgt _ (by
    rw [Fin.lt_def]
    simp [nI]
    omega)
  have hlow := Bf_pos_ge X Z τ v hvn
  have hkk : Fin.castLE X.p0_le (⟨k, hk⟩ : Fin X.p0) = k := Fin.ext rfl
  have hnsq : 1 ≤ nsq (Pv X v) := by
    unfold nsq Pv
    have := Finset.single_le_sum (f := fun j : Fin X.p0 => ‖v (Fin.castLE X.p0_le j)‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ (⟨k, hk⟩ : Fin X.p0))
    simp only [hkk, hvk, norm_one, one_pow] at this
    exact this
  have htn : ∀ m, t (nI X m) = 0 := fun m => ht0 _ (by
    rw [Fin.le_def]
    simp [nI]
    omega)
  have htpos := Bf_pos_ge X Z τ t htn
  have hnsqt : 0 ≤ nsq (Pv X t) := Finset.sum_nonneg fun j _ => by positivity
  have hGkk : (Gp X Z τ k k).re ≤ 1 := by
    rw [← hkk, Gp_pp]
    simp only [if_true, Complex.sub_re, Complex.one_re, Complex.re_sum]
    have : 0 ≤ ∑ m, (Z τ m ⟨k, hk⟩ * conj (Z τ m ⟨k, hk⟩)).re :=
      Finset.sum_nonneg fun m _ => by
        rw [Complex.mul_conj]
        simp [Complex.normSq_nonneg]
    linarith
  constructor
  · nlinarith
  · rw [hsplit, Complex.sub_re]
    nlinarith

lemma pivot_neg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (m0 : Fin (r - X.p0)) : (dOf X (X.xZ x Z) τ (nI X m0)).re ≤ -1 := by
  have hdet := blk_Gp X hx ho hZ τ
  have hz0 : 0 ≤ X.zN Z := Real.iSup_nonneg fun τ => opN_nonneg _
  have hz1 : 0 ≤ 1 - X.zN Z ^ 2 := by nlinarith
  rw [dOf_eq X ho Z τ (nI X m0)]
  set k := nI X m0 with hkdef
  set v : Fin r → ℂ := fun a => uMat (Gp X Z τ) a k with hv
  have hvk : v k = 1 := by simp [hv, uMat]
  set t : Fin r → ℂ := fun b => if (b : ℕ) < X.p0 then v b else 0 with ht
  have ht0 : ∀ b, k ≤ b → t b = 0 := fun b hb => by
    have hb' : ¬ ((b : ℕ) < X.p0) := by
      rw [Fin.le_def] at hb
      simp [hkdef, nI] at hb
      omega
    simp [ht, hb']
  have hvt : Bf X Z τ v t = 0 := Bf_gv_zero X Z τ hdet k t ht0
  have hsplit := Bf_split X Z τ v t hvt
  have htn : ∀ m, t (nI X m) = 0 := fun m => by simp [ht, nI]
  have htpos := Bf_pos_ge X Z τ t htn
  have hnsqt : 0 ≤ nsq (Pv X t) := Finset.sum_nonneg fun j _ => by positivity
  have hre := Bf_self_re X Z τ (v - t)
  have hP0 : Pv X (v - t) = 0 := by
    funext a
    have ha : ((Fin.castLE X.p0_le a : Fin r) : ℕ) < X.p0 := by simp [Fin.coe_castLE]
    simp [Pv, ht, ha]
  have hNm : Nv X Z τ (v - t) m0 = 1 := by
    have h1 : ∀ c : Fin X.p0, (v - t) (Fin.castLE X.p0_le c) = 0 := fun c => congrFun hP0 c
    simp only [Nv, h1, mul_zero, Finset.sum_const_zero, add_zero]
    rw [Pi.sub_apply, ← hkdef, hvk, ht0 k le_rfl, sub_zero]
  have hN : 1 ≤ nsq (Nv X Z τ (v - t)) := by
    unfold nsq
    have := Finset.single_le_sum (f := fun j => ‖Nv X Z τ (v - t) j‖ ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ m0)
    simp only [hNm, norm_one, one_pow] at this
    exact this
  have hn0 : nsq (0 : Fin X.p0 → ℂ) = 0 := by simp [nsq]
  rw [hsplit, Complex.sub_re, hre, hP0, hn0]
  nlinarith

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LogDOfPosBound

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds

open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate

noncomputable section

lemma spread_bound {n : ℕ} (f Δ : Fin n → ℝ) (h0 : ∑ k, Δ k = 0) :
    |∑ k, f k * Δ k| ≤ ((⨆ k, f k) - ⨅ k, f k) * ∑ k, |Δ k| := by
  have hb : BddAbove (Set.range f) := (Set.finite_range f).bddAbove
  have hb' : BddBelow (Set.range f) := (Set.finite_range f).bddBelow
  have hc : ∑ k, (⨅ j, f j) * Δ k = 0 := by rw [← Finset.mul_sum, h0, mul_zero]
  have key : ∑ k, f k * Δ k = ∑ k, (f k - ⨅ j, f j) * Δ k := by
    simp only [sub_mul, Finset.sum_sub_distrib, hc, sub_zero]
  rw [key, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  have h1 : f k ≤ ⨆ j, f j := le_ciSup hb k
  have h2 : ⨅ j, f j ≤ f k := ciInf_le hb' k
  have h3 : |f k - ⨅ j, f j| ≤ (⨆ j, f j) - ⨅ j, f j := by
    rw [abs_of_nonneg (sub_nonneg.mpr h2)]
    linarith
  exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

lemma norm_dOf {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    ‖dOf X y τ k‖ = |(dOf X y τ k).re| := by
  have h : dOf X y τ k = ((dOf X y τ k).re : ℂ) := by
    apply Complex.ext <;> simp [dOf_real X hy τ k]
  rw [h, Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]

lemma ratio_eq {y : Frame X.Ψ r} (hy : y ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    dmin X.Gm y τ k.succ / dmin X.Gm y τ k.castSucc = dOf X y τ k := by
  have hd0 : dmin X.Gm y τ k.castSucc ≠ 0 := by
    intro h0; have h := (hy τ).2 k.castSucc; rw [h0] at h; simp at h
  rw [dmin_succ X hy τ k]
  field_simp

lemma nfac_log {y : Frame X.Ψ r} (hy : y ∈ X.dom) (la : Wt X.Ψ r) :
    Real.log (X.nfac la y) = ∑ τ, ∑ k : Fin r, (-(la τ k : ℝ) / 2) * Real.log ‖dOf X y τ k‖ := by
  unfold Data.nfac
  have hpos : ∀ τ k, 0 < ‖dOf X y τ k‖ := fun τ k => by
    rw [norm_dOf X hy τ k]
    apply abs_pos.2
    have h := sgn_dOf_pos X hy τ k
    intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun k _ => Real.rpow_pos_of_pos (by
      rw [ratio_eq X hy τ k]; exact hpos τ k) _).ne')]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun k _ => (Real.rpow_pos_of_pos (by rw [ratio_eq X hy τ k]; exact hpos τ k) _).ne')]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ratio_eq X hy τ k, Real.log_rpow (hpos τ k)]

lemma sum_log_dOf {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) : ∑ k : Fin r, Real.log ‖dOf X (X.xZ x Z) τ k‖ = 0 := by
  have hy := xZ_mem_dom X hx ho hZ
  have hpos : ∀ k, ‖dOf X (X.xZ x Z) τ k‖ ≠ 0 := fun k => by
    rw [norm_dOf X hy τ k]
    apply (abs_pos.2 _).ne'
    have h := sgn_dOf_pos X hy τ k
    intro h0; rw [h0, mul_zero] at h; exact lt_irrefl _ h
  rw [← Real.log_prod (fun k _ => hpos k), ← norm_prod]
  have hp : ∏ k : Fin r, dOf X (X.xZ x Z) τ k = dmin X.Gm (X.xZ x Z) τ (Fin.last r) := by
    rw [dmin_prod X hy τ (Fin.last r)]
    rfl
  rw [hp]
  unfold dmin
  rw [gram_xZ X ho Z τ, lminor_last]
  unfold Gp
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_lowBlock, Matrix.det_diagonal, one_mul]
  rw [show ((X.lowBlock Z τ).map (starRingEnd ℂ)).det = (starRingEnd ℂ) (X.lowBlock Z τ).det from
    (RingHom.map_det _ _).symm, det_lowBlock, map_one, mul_one, norm_prod]
  rw [Finset.prod_eq_one fun k _ => ?_, Real.log_one]
  unfold sgn
  split_ifs <;> simp

lemma log_dOf_pos_bound {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (k : Fin r) (hk : (k : ℕ) < X.p0) :
    Real.log ‖dOf X (X.xZ x Z) τ k‖ ≤ 0 ∧
      -Real.log ‖dOf X (X.xZ x Z) τ k‖ ≤ X.zN Z ^ 2 / (1 - X.zN Z ^ 2) := by
  have hy := xZ_mem_dom X hx ho hZ
  obtain ⟨h1, h2⟩ := pivot_pos X hx ho hZ τ k hk
  have h0 : 0 ≤ X.zN Z := le_trans (opN_nonneg _) (opN_le_zN X Z τ)
  have hu : X.zN Z ^ 2 < 1 := by nlinarith
  have htpos : 0 < (dOf X (X.xZ x Z) τ k).re := by linarith
  rw [norm_dOf X hy τ k, abs_of_pos htpos]
  refine ⟨Real.log_nonpos htpos.le h2, ?_⟩
  rw [← Real.log_inv]
  have h3 := Real.log_le_sub_one_of_pos (inv_pos.2 htpos)
  have h4 : (dOf X (X.xZ x Z) τ k).re⁻¹ ≤ (1 - X.zN Z ^ 2)⁻¹ := inv_anti₀ (by linarith) h1
  have hne : (1 - X.zN Z ^ 2) ≠ 0 := (by linarith : (0:ℝ) < 1 - X.zN Z ^ 2).ne'
  have h5 : (1 - X.zN Z ^ 2)⁻¹ - 1 = X.zN Z ^ 2 / (1 - X.zN Z ^ 2) := by
    field_simp
    ring
  linarith

lemma log_dOf_neg {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {Z : X.Coord} (hZ : X.zN Z < 1)
    (τ : X.Ψ) (k : Fin r) (hk : X.p0 ≤ (k : ℕ)) : 0 ≤ Real.log ‖dOf X (X.xZ x Z) τ k‖ := by
  have hy := xZ_mem_dom X hx ho hZ
  have hk' : k = nI X ⟨(k : ℕ) - X.p0, by have := k.isLt; omega⟩ := by
    apply Fin.ext; simp only [nI]; omega
  have h := pivot_neg X hx ho hZ τ ⟨(k : ℕ) - X.p0, by have := k.isLt; omega⟩
  rw [← hk'] at h
  rw [norm_dOf X hy τ k, abs_of_neg (by linarith)]
  exact Real.log_nonneg (by linarith)

lemma spread_nonneg (la : Wt X.Ψ r) (τ : X.Ψ) : 0 ≤ X.spread la τ := by
  unfold Data.spread
  rcases isEmpty_or_nonempty (Fin r) with h | h
  · simp [Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]
  · exact sub_nonneg.mpr (ciInf_le_ciSup (Set.finite_range _).bddBelow (Set.finite_range _).bddAbove)

theorem nfac_xZ {x : Frame X.Ψ r} (hx : x ∈ X.dom) (ho : X.IsOrtho x) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ ≤ 1 / 10)
    {Z : X.Coord} (hZ : X.zN Z ≤ ρ) (la : Wt X.Ψ r) (w : ℝ) (hw : (∑ τ, X.spread la τ) ≤ w) :
    |Real.log (X.nfac la (X.xZ x Z)) - Real.log (X.nfac la x)| ≤ 4 * w * r * X.zN Z ^ 2 := by
  have hZ1 : X.zN Z < 1 := by linarith
  have hy := xZ_mem_dom X hx ho hZ1

  have hx1 : Real.log (X.nfac la x) = 0 := by
    have hn : ∀ τ (i : Fin (r + 1)), ‖dmin X.Gm x τ i‖ = 1 := by
      intro τ i
      unfold dmin
      rw [ho τ, lminor_diagonal, norm_prod]
      refine Finset.prod_eq_one fun j _ => ?_
      unfold sgn
      split_ifs <;> simp
    unfold Data.nfac
    rw [Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => by rw [norm_div, hn, hn, div_one,
      Real.one_rpow], Real.log_one]
  rw [hx1, sub_zero, nfac_log X hy la]
  set s := X.zN Z with hs
  have hs0 : 0 ≤ s := by
    rw [hs]
    unfold Data.zN
    exact Real.iSup_nonneg fun τ => opN_nonneg _
  have hu : s ^ 2 ≤ 1 / 100 := by nlinarith
  have hq : s ^ 2 / (1 - s ^ 2) ≤ 2 * s ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith

  have hτ : ∀ τ : X.Ψ, |∑ k : Fin r, (la τ k : ℝ) * Real.log ‖dOf X (X.xZ x Z) τ k‖| ≤
      X.spread la τ * (4 * r * s ^ 2) := by
    intro τ
    refine (spread_bound _ _ (sum_log_dOf X hx ho hZ1 τ)).trans ?_
    have hsp := spread_nonneg X la τ
    refine mul_le_mul_of_nonneg_left ?_ hsp

    have hsplit : ∑ k : Fin r, |Real.log ‖dOf X (X.xZ x Z) τ k‖| =
        ∑ k : Fin r, (if (k : ℕ) < X.p0 then -2 * Real.log ‖dOf X (X.xZ x Z) τ k‖ else 0) +
          ∑ k : Fin r, Real.log ‖dOf X (X.xZ x Z) τ k‖ := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : (k : ℕ) < X.p0
      · rw [if_pos hk, abs_of_nonpos (log_dOf_pos_bound X hx ho hZ1 τ k hk).1]
        ring
      · rw [if_neg hk, abs_of_nonneg (log_dOf_neg X hx ho hZ1 τ k (not_lt.1 hk)), zero_add]
    rw [hsplit, sum_log_dOf X hx ho hZ1 τ, add_zero]
    calc ∑ k : Fin r, (if (k : ℕ) < X.p0 then -2 * Real.log ‖dOf X (X.xZ x Z) τ k‖ else 0)
        ≤ ∑ _k : Fin r, 2 * (2 * s ^ 2) := Finset.sum_le_sum fun k _ => by
          by_cases hk : (k : ℕ) < X.p0
          · rw [if_pos hk]
            have := (log_dOf_pos_bound X hx ho hZ1 τ k hk).2
            nlinarith
          · rw [if_neg hk]; positivity
      _ = 4 * r * s ^ 2 := by simp [Finset.card_univ]; ring
  have hsum : |∑ τ, ∑ k : Fin r, (-(la τ k : ℝ) / 2) * Real.log ‖dOf X (X.xZ x Z) τ k‖| ≤
      ∑ τ, X.spread la τ * (4 * r * s ^ 2) / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    have e : ∑ k : Fin r, (-(la τ k : ℝ) / 2) * Real.log ‖dOf X (X.xZ x Z) τ k‖ =
        -(1 / 2) * ∑ k : Fin r, (la τ k : ℝ) * Real.log ‖dOf X (X.xZ x Z) τ k‖ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [hτ τ]
  refine hsum.trans ?_
  rw [← Finset.sum_div, ← Finset.sum_mul]
  have hw0 : (0 : ℝ) ≤ 4 * r * s ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_right hw hw0
  have hw1 : 0 ≤ w := le_trans (Finset.sum_nonneg fun τ _ => spread_nonneg X la τ) hw
  have hw2 : 0 ≤ w * (4 * r * s ^ 2) := mul_nonneg hw1 hw0
  nlinarith

end

end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
end
end
