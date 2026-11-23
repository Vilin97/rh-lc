module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.SumSqGe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.InstLCSL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.SubLeSumAbsConsecutiveDiff
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.StabDirectedSystem
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.SubLeSumAbsConsecutiveDiff
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.OfSInvCoe

section

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem mt_mul (x y : Sp L N) (w : InfinitePlace L) :
    mt (x * y) w = mt x w * mt y w := rfl

theorem mt_one (w : InfinitePlace L) : mt (1 : Sp L N) w = 1 := rfl

theorem mt_inv_mul (x : Sp L N) (w : InfinitePlace L) : mt x⁻¹ w * mt x w = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem mt_mul_inv (x : Sp L N) (w : InfinitePlace L) : mt x w * mt x⁻¹ w = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

theorem ofS_inv_coe (x : Sp L N) (w : InfinitePlace L) :
    ((((ofS L N x) w)⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = mt x⁻¹ w := by
  rw [← Pi.inv_apply, ← map_inv]
  rfl

theorem mat_one (w : InfinitePlace L) : mat (one L N).1 w = 1 := rfl

theorem q_actL (x : Sp L N) (y : Lat L N) :
    q (actL (ofS L N x) (one L N).1) y = ∑ w, ∑ i, ‖(mt x⁻¹ w *ᵥ toR y w) i‖ ^ 2 := by
  simp only [q, qR]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w := by
    simp only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]
  rw [hm, re_quad]

theorem q_dual (x : Sp L N) (y : Lat L N) :
    q (dualH (actL (ofS L N x) (one L N).1)) y =
      ∑ w, ∑ i, ‖((mt x w)ᵀ *ᵥ toR y w) i‖ ^ 2 := by
  simp only [q, qR]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hBM : mt x⁻¹ w * mt x w = 1 := mt_inv_mul x w
  have hMB : mt x w * mt x⁻¹ w = 1 := mt_mul_inv x w
  have hm : mat (actL (ofS L N x) (one L N).1) w = (mt x⁻¹ w)ᴴ * mt x⁻¹ w := by
    simp only [actL, LinearMap.coe_toContinuousLinearMap', actM, LinearMap.coe_mk, AddHom.coe_mk, mat_mkHS, mat_one, Matrix.mul_one, ofS_inv_coe]
  have hinv : (mat (actL (ofS L N x) (one L N).1) w)⁻¹ = mt x w * (mt x w)ᴴ := by
    rw [hm]
    refine Matrix.inv_eq_left_inv ?_
    calc mt x w * (mt x w)ᴴ * ((mt x⁻¹ w)ᴴ * mt x⁻¹ w)
        = mt x w * (mt x⁻¹ w * mt x w)ᴴ * mt x⁻¹ w := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hBM, Matrix.conjTranspose_one, Matrix.mul_one, hMB]
  have hd : mat (dualH (actL (ofS L N x) (one L N).1)) w =
      ((mt x w)ᵀ)ᴴ * (mt x w)ᵀ := by
    simp only [dualH, mat_mkHS]
    rw [hinv, Matrix.transpose_mul]
    rfl
  rw [hd, re_quad]

theorem lam_ge (hN : 1 ≤ N) {h : HS L N} {κ : ℝ} (hκ : ∀ y : Lat L N, y ≠ 0 → κ ≤ q h y) : κ ≤ lam h := by
  have hne : Nonempty {y : Lat L N // y ≠ 0} := by
    refine ⟨⟨fun _ => 1, fun h0 => ?_⟩⟩
    have := congrFun h0 ⟨0, hN⟩
    exact one_ne_zero this
  unfold lam
  exact le_ciInf fun y => hκ y.1 y.2

end PositivityTheory.KB.MomentRationality.Ht
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.OneLeAbsNorm

section

@[expose] public section

open NumberField

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type*} [Field L] [NumberField L]

theorem exists_den (s : Finset L) : ∃ d : ℤ, d ≠ 0 ∧ ∀ x ∈ s, IsIntegral ℤ ((d : L) * x) := by
  obtain ⟨d, hd, h⟩ := exists_integral_multiples ℤ ℚ s
  refine ⟨d, hd, fun x hx => ?_⟩
  have := h x hx
  rwa [zsmul_eq_mul] at this

end PositivityTheory.KB.MomentRationality.Ht
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.MomentEntryBounds.PrimalPlace

section

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem primal_place (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding)
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    (y : Lat L N) {i0 : Fin N} (hgt : ∀ j, i0 < j → (gi g *ᵥ toL y) j = 0) (w : InfinitePlace L) :
    (Real.exp (-s i0) * M⁻¹ * (‖z w‖⁻¹ * ‖w.embedding ((gi g *ᵥ toL y) i0)‖)) ^ 2 ≤
      ∑ i, ‖(mt (c * (p * dg L N s hs * k))⁻¹ w *ᵥ toR y w) i‖ ^ 2 := by
  have mt_mul (x y : Sp L N) (v : InfinitePlace L) :
      mt (x * y) v = mt x v * mt y v := rfl
  have mt_inv_mul (x : Sp L N) (v : InfinitePlace L) : mt x⁻¹ v * mt x v = 1 := by
    rw [← mt_mul, inv_mul_cancel]
    rfl
  have cinv_vec : mt c⁻¹ w *ᵥ toR y w = (z w)⁻¹ •
      (fun a => w.embedding ((gi g *ᵥ toL y) a)) := by
    have hz : z w ≠ 0 := by
      intro h
      have h1 := hc w
      rw [h, zero_smul] at h1
      have h2 : (mt c w).det = 1 := (c w).prop
      haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
      rw [h1, Matrix.det_zero] at h2
      exact zero_ne_one h2
    have hgg : (g : Matrix (Fin N) (Fin N) L) * gi g = 1 := g.mul_inv
    have hx : toR y w = mt c w *ᵥ ((z w)⁻¹ •
        (fun a => w.embedding ((gi g *ᵥ toL y) a))) := by
      rw [hc w, Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hz, one_smul]
      funext a
      change toR y w a = ((g : Matrix (Fin N) (Fin N) L).map w.embedding *ᵥ (w.embedding ∘ (gi g *ᵥ toL y))) a
      rw [← RingHom.map_mulVec, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
      rfl
    rw [hx, Matrix.mulVec_mulVec, mt_inv_mul, Matrix.one_mulVec]
  obtain ⟨hpu, hpM, -, -⟩ := hp
  have hPp : mt p⁻¹ w * mt p w = 1 := mt_inv_mul p w
  obtain ⟨hPu, hPd⟩ := inv_upper (hpu w) hPp
  have hD : mt (dg L N s hs)⁻¹ w = diagonal fun i => ((Real.exp (-s i) : ℝ) : ℂ) := by
    have h1 := mt_inv_mul (dg L N s hs) w
    have h2 : mt (dg L N s hs) w = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ) := rfl
    rw [h2] at h1
    have h3 : (diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ)) * (diagonal fun i => ((Real.exp (-s i) : ℝ) : ℂ)) = 1 := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1
      funext i
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    calc mt (dg L N s hs)⁻¹ w
        = mt (dg L N s hs)⁻¹ w * ((diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ)) *
            (diagonal fun i => ((Real.exp (-s i) : ℝ) : ℂ))) := by rw [h3, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hK : mt k⁻¹ w ∈ unitaryGroup (Fin N) ℂ := by
    have hU := hk w
    have h1 : mt k⁻¹ w * mt k w = 1 := mt_inv_mul k w
    have h2 : mt k⁻¹ w = star (mt k w) := by
      calc mt k⁻¹ w = mt k⁻¹ w * (mt k w * star (mt k w)) := by
            rw [Unitary.mul_star_self_of_mem hU, Matrix.mul_one]
        _ = star (mt k w) := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [h2]
    exact Unitary.star_mem hU
  have hQ : mt (c * (p * dg L N s hs * k))⁻¹ w *ᵥ toR y w =
      mt k⁻¹ w *ᵥ (mt (dg L N s hs)⁻¹ w *ᵥ (mt p⁻¹ w *ᵥ (mt c⁻¹ w *ᵥ toR y w))) := by
    simp only [_root_.mul_inv_rev, mt_mul, mulVec_mulVec, Matrix.mul_assoc]
  rw [hQ, sum_norm_unitary hK]
  refine le_trans ?_ (single_le_sum_sq _ i0)
  have hzero : ∀ j, i0 < j → ((z w)⁻¹ • fun a => w.embedding ((gi g *ᵥ toL y) a)) j = 0 := by
    intro j hj
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hgt j hj, map_zero, mul_zero]
  rw [cinv_vec, hD, mulVec_diagonal, mulVec_upper hPu hzero]
  have hne : mt p w i0 i0 ≠ 0 := by
    intro h
    have h1 := hPd i0
    rw [h, mul_zero] at h1
    exact zero_ne_one h1
  have hpos : 0 < ‖mt p w i0 i0‖ := norm_pos_iff.2 hne
  have hM : 0 < M := lt_of_lt_of_le hpos (hpM w i0 i0)
  have hPi : M⁻¹ ≤ ‖mt p⁻¹ w i0 i0‖ := by
    have h3 : ‖mt p⁻¹ w i0 i0‖ * ‖mt p w i0 i0‖ = 1 := by rw [← norm_mul, hPd i0, norm_one]
    rw [eq_inv_of_mul_eq_one_left h3]
    exact inv_anti₀ hpos (hpM w i0 i0)
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_inv]
  have hM' : 0 ≤ M⁻¹ := inv_nonneg.2 hM.le
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [mul_assoc]
  gcongr

theorem dual_place {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding)
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    (y : Lat L N) {i1 : Fin N} (hlt : ∀ j, j < i1 → ((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) j = 0)
    (w : InfinitePlace L) :
    (Real.exp (s i1) * M⁻¹ * (‖z w‖ * ‖w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) i1)‖)) ^ 2 ≤
      ∑ i, ‖((mt (c * (p * dg L N s hs * k)) w)ᵀ *ᵥ toR y w) i‖ ^ 2 := by
  have mt_mul (x y : Sp L N) (v : InfinitePlace L) :
      mt (x * y) v = mt x v * mt y v := rfl
  have cT_vec : (mt c w)ᵀ *ᵥ toR y w = z w •
      (fun a => w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) a)) := by
    rw [hc w, transpose_smul, smul_mulVec, ← transpose_map]
    congr 1
    ext a
    have := RingHom.map_mulVec w.embedding (g : Matrix (Fin N) (Fin N) L)ᵀ (toL y) a
    rw [this]
    rfl
  obtain ⟨hpu, hpM, hpm, -⟩ := hp
  have hKT : (mt k w)ᵀ ∈ unitaryGroup (Fin N) ℂ := by
    rw [mem_unitaryGroup_iff]
    have h1 : star (mt k w) * mt k w = 1 := Unitary.star_mul_self_of_mem (hk w)
    have h2 : star ((mt k w)ᵀ) = (star (mt k w))ᵀ := by
      ext i j
      simp [star_eq_conjTranspose]
    rw [h2, ← transpose_mul, h1, transpose_one]
  have hQ : (mt (c * (p * dg L N s hs * k)) w)ᵀ *ᵥ toR y w =
      (mt k w)ᵀ *ᵥ ((mt (dg L N s hs) w)ᵀ *ᵥ ((mt p w)ᵀ *ᵥ ((mt c w)ᵀ *ᵥ toR y w))) := by
    simp only [mt_mul, transpose_mul, mulVec_mulVec, Matrix.mul_assoc]
  have hD : (mt (dg L N s hs) w)ᵀ = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ) := by
    rw [show mt (dg L N s hs) w = diagonal fun i => ((Real.exp (s i) : ℝ) : ℂ) from rfl,
      diagonal_transpose]
  have hlow : ∀ a b : Fin N, a < b → (mt p w)ᵀ a b = 0 := fun a b hab => by
    rw [transpose_apply]
    exact hpu w hab
  have hzero : ∀ j, j < i1 → (z w • fun a => w.embedding (((g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y) a)) j = 0 := by
    intro j hj
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hlt j hj, map_zero, mul_zero]
  rw [hQ, sum_norm_unitary hKT]
  refine le_trans ?_ (single_le_sum_sq _ i1)
  rw [cT_vec, hD, mulVec_diagonal, mulVec_lower hlow hzero, transpose_apply]
  have hM : 0 ≤ M := (norm_nonneg _).trans (hpM w i1 i1)
  have hM' : 0 ≤ M⁻¹ := inv_nonneg.2 hM
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  refine pow_le_pow_left₀ (by positivity) ?_ 2
  rw [mul_assoc]
  gcongr
  exact hpm w i1

end PositivityTheory.KB.MomentRationality.Ht
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.IntegralMomentReduction.PrimalY

section

@[expose] public section

noncomputable section

open NumberField NumberField.InfinitePlace Matrix MeasureTheory UpperTheory.V.KT UpperTheory.V.KL

namespace PositivityTheory.KB.TwSMInt2

open MomentRationality MomentRationality.Ht

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem primal_y (hL : IsTotallyComplex L) (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, MomentRationality.mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) {d : ℤ} (hd : d ≠ 0)
    (hdi : ∀ i j, IsIntegral ℤ ((d : L) * gi g i j))
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    {imax : Fin N} (himax : ∀ i, s i ≤ s imax) (y : Lat L N) (hy : y ≠ 0) :
    (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (-s imax) ^ 2 ≤
      q (actL (ofS L N (c * (p * dg L N s hs * k))) (one L N).1) y := by
  classical
  rw [q_actL]
  set v := gi g *ᵥ toL y with hv
  have hv0 : v ≠ 0 := gi_ne g hy
  have hne : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra hcon
    apply hv0
    funext i
    by_contra hi
    exact hcon ⟨i, by simpa using hi⟩
  have hi0mem : v ((Finset.univ.filter fun i => v i ≠ 0).max' hne) ≠ 0 := by
    have := Finset.max'_mem _ hne
    simpa using this
  set i0 := (Finset.univ.filter fun i => v i ≠ 0).max' hne with hi0
  have hzero : ∀ j, i0 < j → v j = 0 := by
    intro j hj
    by_contra hjne
    have : j ≤ i0 := Finset.le_max' _ j (by simpa using hjne)
    exact absurd hj (not_lt.mpr this)
  have hplace := fun w => primal_place hN hc hp hs hk y hzero w
  set Z := ∑ w : InfinitePlace L, ‖z w‖ ^ 2 + 1 with hZdef
  have hZ : 0 < Z := by positivity
  have hsum := sum_sq_ge hL hd hi0mem (int_d hdi y i0)
  have he : Real.exp (-s imax) ≤ Real.exp (-s i0) := Real.exp_le_exp.mpr (by linarith [himax i0])
  have hterm : ∀ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ‖w.embedding (v i0)‖ ^ 2 ≤
      ∑ i, ‖(MomentRationality.mt (c * (p * dg L N s hs * k))⁻¹ w *ᵥ toR y w) i‖ ^ 2 := by
    intro w
    refine le_trans ?_ (hplace w)
    have hzpos : 0 < ‖z w‖ := norm_pos_iff.mpr (z_ne hN hc w)
    have hzle : ‖z w‖ ^ 2 ≤ Z := by
      have := Finset.single_le_sum (f := fun w => ‖z w‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ w)
      linarith
    have hZinv : Z⁻¹ ≤ (‖z w‖⁻¹) ^ 2 := by
      rw [inv_pow]
      exact inv_anti₀ (by positivity) hzle
    calc (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ‖w.embedding (v i0)‖ ^ 2
        ≤ (M⁻¹) ^ 2 * (‖z w‖⁻¹) ^ 2 * Real.exp (-s i0) ^ 2 * ‖w.embedding (v i0)‖ ^ 2 := by
          gcongr
      _ = _ := by ring
  have hA : 0 ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 := by positivity
  calc (M⁻¹) ^ 2 * Z⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (-s imax) ^ 2
      = (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ((d : ℝ) ^ 2)⁻¹ := by ring
    _ ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ∑ w : InfinitePlace L, ‖w.embedding (v i0)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsum hA
    _ = ∑ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (-s imax) ^ 2 * ‖w.embedding (v i0)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun w _ => hterm w

theorem dual_y (hL : IsTotallyComplex L) (hN : 1 ≤ N) {g : GL (Fin N) L} {z : InfinitePlace L → ℂ} {c : Sp L N}
    (hc : ∀ w, MomentRationality.mt c w = z w • (g : Matrix (Fin N) (Fin N) L).map w.embedding) {d : ℤ} (hd : d ≠ 0)
    (hdg : ∀ i j, IsIntegral ℤ ((d : L) * ((g : Matrix (Fin N) (Fin N) L)ᵀ) i j))
    {M : ℝ} {p : Sp L N} (hp : p ∈ Om L N M) {s : Fin N → ℝ} (hs : ∑ i, s i = 0) {k : Sp L N} (hk : k ∈ KS L N)
    {imin : Fin N} (himin : ∀ i, s imin ≤ s i) (y : Lat L N) (hy : y ≠ 0) :
    (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖⁻¹ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (s imin) ^ 2 ≤
      q (dualH (actL (ofS L N (c * (p * dg L N s hs * k))) (one L N).1)) y := by
  classical
  rw [q_dual]
  set v := (g : Matrix (Fin N) (Fin N) L)ᵀ *ᵥ toL y with hv
  have hv0 : v ≠ 0 := gT_ne g hy
  have hne : (Finset.univ.filter fun i => v i ≠ 0).Nonempty := by
    by_contra hcon
    apply hv0
    funext i
    by_contra hi
    exact hcon ⟨i, by simpa using hi⟩
  have hi1mem : v ((Finset.univ.filter fun i => v i ≠ 0).min' hne) ≠ 0 := by
    have := Finset.min'_mem _ hne
    simpa using this
  set i1 := (Finset.univ.filter fun i => v i ≠ 0).min' hne with hi1
  have hzero : ∀ j, j < i1 → v j = 0 := by
    intro j hj
    by_contra hjne
    have : i1 ≤ j := Finset.min'_le _ j (by simpa using hjne)
    exact absurd hj (not_lt.mpr this)
  have hplace := fun w => dual_place hc hp hs hk y hzero w
  set Z := ∑ w : InfinitePlace L, ‖z w‖⁻¹ ^ 2 + 1 with hZdef
  have hZ : 0 < Z := by positivity
  have hsum := sum_sq_ge hL hd hi1mem (int_d hdg y i1)
  have he : Real.exp (s imin) ≤ Real.exp (s i1) := Real.exp_le_exp.mpr (himin i1)
  have hterm : ∀ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ‖w.embedding (v i1)‖ ^ 2 ≤
      ∑ i, ‖((MomentRationality.mt (c * (p * dg L N s hs * k)) w)ᵀ *ᵥ toR y w) i‖ ^ 2 := by
    intro w
    refine le_trans ?_ (hplace w)
    have hzpos : 0 < ‖z w‖ := norm_pos_iff.mpr (z_ne hN hc w)
    have hzle : ‖z w‖⁻¹ ^ 2 ≤ Z := by
      have := Finset.single_le_sum (f := fun w => ‖z w‖⁻¹ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ w)
      linarith
    have hZinv : Z⁻¹ ≤ ‖z w‖ ^ 2 := by
      have := inv_anti₀ (by positivity) hzle
      rwa [inv_pow, inv_inv] at this
    calc (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ‖w.embedding (v i1)‖ ^ 2
        ≤ (M⁻¹) ^ 2 * ‖z w‖ ^ 2 * Real.exp (s i1) ^ 2 * ‖w.embedding (v i1)‖ ^ 2 := by
          gcongr
      _ = _ := by ring
  have hA : 0 ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 := by positivity
  calc (M⁻¹) ^ 2 * Z⁻¹ * ((d : ℝ) ^ 2)⁻¹ * Real.exp (s imin) ^ 2
      = (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ((d : ℝ) ^ 2)⁻¹ := by ring
    _ ≤ (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ∑ w : InfinitePlace L, ‖w.embedding (v i1)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsum hA
    _ = ∑ w, (M⁻¹) ^ 2 * Z⁻¹ * Real.exp (s imin) ^ 2 * ‖w.embedding (v i1)‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum fun w _ => hterm w

theorem sHtB : SHtB := by
  intro L _ _ hL N hN c hrat M
  obtain ⟨g, z, hc⟩ := hrat
  classical
  obtain ⟨d, hd, hint⟩ := exists_den
    ((Finset.univ.image fun ij : Fin N × Fin N => gi g ij.1 ij.2) ∪
      (Finset.univ.image fun ij : Fin N × Fin N => ((g : Matrix (Fin N) (Fin N) L)ᵀ) ij.1 ij.2))
  have hdi : ∀ i j, IsIntegral ℤ ((d : L) * gi g i j) := fun i j =>
    hint _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hdg : ∀ i j, IsIntegral ℤ ((d : L) * ((g : Matrix (Fin N) (Fin N) L)ᵀ) i j) := fun i j =>
    hint _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
  set A1 := (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ with hA1def
  set A2 := (M⁻¹) ^ 2 * (∑ w : InfinitePlace L, ‖z w‖⁻¹ ^ 2 + 1)⁻¹ * ((d : ℝ) ^ 2)⁻¹ with hA2def
  refine ⟨(A1 * A2)⁻¹, ?_⟩
  intro p hp s hs k hk
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  obtain ⟨imax, himax⟩ := Finite.exists_max s
  obtain ⟨imin, himin⟩ := Finite.exists_min s
  have hM : M ≠ 0 := by
    rintro rfl
    obtain ⟨w0⟩ := (inferInstance : Nonempty (InfinitePlace L))
    have h1 := hp.2.2.2 ⟨0, hN⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ w0)] at h1
    · exact zero_ne_one h1
    · exact le_antisymm (hp.2.1 w0 _ _) (norm_nonneg _)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have hA1 : 0 < A1 := by positivity
  have hA2 : 0 < A2 := by positivity
  have h1 := lam_ge hN (fun y hy => primal_y hL hN hc hd hdi hp hs hk himax y hy)
  have h2 := lam_ge hN (fun y hy => dual_y hL hN hc hd hdg hp hs hk himin y hy)
  set e1 := Real.exp (-s imax) ^ 2
  set e2 := Real.exp (s imin) ^ 2
  set X := Real.exp (2 * (s imax - s imin))
  have he1 : 0 < e1 := by positivity
  have he2 : 0 < e2 := by positivity
  have hprod : e1 * e2 * X = 1 := by
    simp only [e1, e2, X, sq, ← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hX : X = (e1 * e2)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hprod)
  show (lam _ * lam _)⁻¹ ≤ _
  calc (lam _ * lam _)⁻¹ ≤ (A1 * e1 * (A2 * e2))⁻¹ := by
        apply inv_anti₀ (by positivity)
        exact mul_le_mul h1 h2 (by positivity) (le_trans (by positivity) h1)
    _ = (A1 * A2)⁻¹ * X := by rw [hX]; ring
    _ ≤ (A1 * A2)⁻¹ * Real.exp (2 * W s) := by
        gcongr
        show Real.exp (2 * (s imax - s imin)) ≤ Real.exp (2 * W s)
        apply Real.exp_le_exp.mpr
        have hW := sub_le_sum_abs_consecutive_diff s imax imin
        unfold W
        linarith

end PositivityTheory.KB.TwSMInt2
end
end
end
