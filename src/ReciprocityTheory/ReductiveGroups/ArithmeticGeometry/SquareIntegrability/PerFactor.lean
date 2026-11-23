module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GaussianTailBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.DimStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofSpanCondition
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.QuotientTorusMinimumBound
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.OneLeKappaMulPhase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ShortVectorBoundLeKappa
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SupRatioLeOfPhaseZero
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofFinrankIRLe
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZmMem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ZmNorm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.IKDiscrete
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SupRatioLeOfPhaseZero

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofUMapSqSmul

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

def PerFactor {X : PT E} {DF : ℕ} (P : Par X DF) (I : Submodule ℤ (Vsp X.dim))
    (s : (Fin 1 → Vsp X.dim) → ℂ) : Prop :=
  ∀ w : Vsp X.dim, ∃ y ∈ X.L, Real.sqrt (X.ptN2 1 s fun _ => w) / Real.sqrt (X.l2 1 s) ≤
    Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) *
      (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) *
        Real.exp (-(Real.pi / 2) * ‖uMap I w - uMap I y‖ ^ 2)

theorem Par_ka0_nonneg {X : PT E} {DF : ℕ} (P : Par X DF) : 0 ≤ P.ka0 := by
  have h : (0 : ℝ) ≤ PT.rd E := by linarith [P.hrd]
  have hR : (0 : ℝ) ≤ RR (E := E) := by
    unfold RR
    exact pow_nonneg h 7
  unfold Par.ka0
  exact mul_nonneg (mul_nonneg (by norm_num) hR) (sq_nonneg _)

theorem tof_uMap_sq_smul {dim : (E →+* ℂ) → ℕ} (I : Submodule ℤ (Vsp dim)) (r1 : ℕ) (a y : Vsp dim) :
    ‖uMap I (((r1 : ℂ) ^ 2) • a - ((r1 : ℂ) ^ 2) • y)‖ ^ 2 =
      (r1 : ℝ) ^ 4 * ‖uMap I a - uMap I y‖ ^ 2 := by
  have h : ((r1 : ℂ) ^ 2) • a - ((r1 : ℂ) ^ 2) • y = ((r1 : ℝ) ^ 2) • (a - y) := by
    first
    | (rw [← smul_sub, ← Complex.coe_smul, Complex.ofReal_pow, Complex.ofReal_natCast])
    | (rw [← smul_sub]; norm_cast)
    | (rw [← smul_sub, ← Complex.coe_smul]; push_cast; rfl)
  rw [h, map_smul, map_sub, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  ring

theorem t_assemble [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) {s : (Fin 1 → Vsp X.dim) → ℂ} (hpf : PerFactor P I s)
    (r1 : ℕ) (hr1 : 2 ≤ r1) (a : Fin X.r → Vsp X.dim) (ha : ∀ j, ((r1 : ℂ) ^ 2) • a j ∈ X.L)
    (hgen : ∀ x ∈ X.L, ∃ c : Fin X.r → 𝓞 E, ∃ y ∈ X.L,
      x = ∑ j, act (c j) (((r1 : ℂ) ^ 2) • a j) + (r1 : ℂ) • y) (hph : 0 < P.ph) :
    ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
      Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) *
        Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) := by
  choose y hyL hb using fun j => hpf (a j)
  set C : ℝ := Real.exp (P.p1 + P.p2 + dstar (E := E) P.m) *
      (P.ka0 * P.ph) ^ ((dstar (E := E) P.m : ℝ) / 4) with hC
  set D : Fin X.r → ℝ := fun j => ‖uMap I (a j) - uMap I (y j)‖ ^ 2 with hD
  have hkp : 0 ≤ P.ka0 * P.ph := mul_nonneg (Par_ka0_nonneg P) hph.le
  have h1 : ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s) ≤
      ∏ j, (C * Real.exp (-(Real.pi / 2) * D j)) :=
    Finset.prod_le_prod₀ (fun j _ => by positivity) (fun j _ => hb j)
  have h2 : ∏ j, (C * Real.exp (-(Real.pi / 2) * D j)) =
      C ^ X.r * Real.exp (-(Real.pi / 2) * ∑ j, D j) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← Real.exp_sum, Finset.mul_sum]
  have h3 : C ^ X.r = Real.exp P.p3 * (P.ka0 * P.ph) ^ ((X.r * dstar (E := E) P.m : ℝ) / 4) := by
    rw [hC, mul_pow, ← Real.exp_nat_mul, ← Real.rpow_natCast ((P.ka0 * P.ph) ^ _),
      ← Real.rpow_mul hkp, Par.p3]
    congr 2; ring

  set xb : Fin X.r → Vsp X.dim := fun j => ((r1 : ℂ) ^ 2) • a j - ((r1 : ℂ) ^ 2) • y j with hxb
  have hxL : ∀ j, xb j ∈ X.L ∧ IsU I (xb j) (uMap I (xb j)) := by
    intro j
    refine ⟨X.L.sub_mem (ha j) ?_, isU_uMap I _⟩
    have : ((r1 : ℂ) ^ 2) • y j = (r1 ^ 2 : ℕ) • y j := by
      rw [← Nat.cast_smul_eq_nsmul ℂ]; push_cast; rfl
    rw [this]; exact X.L.nsmul_mem (hyL j) _
  have hspan := tof_span_condition (X := X) I r1 hr1 a y hyL hgen
  have hu2 := hI.u2 X.r xb (fun j => uMap I (xb j)) hxL hspan
  have hsum : ∑ j, ‖uMap I (xb j)‖ ^ 2 / 2 = (r1 : ℝ) ^ 4 / 2 * ∑ j, D j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hxb]; dsimp only
    rw [tof_uMap_sq_smul]; ring
  rw [hsum] at hu2
  have hr4 : (0 : ℝ) < (r1 : ℝ) ^ 4 := by
    have : (0 : ℝ) < r1 := by exact_mod_cast (by omega : 0 < r1)
    positivity
  have h4 : Real.exp (-(Real.pi / 2) * ∑ j, D j) ≤ Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) := by
    apply Real.exp_le_exp.2
    have : Real.pi * P.ph / (r1 : ℝ) ^ 4 ≤ Real.pi / 2 * ∑ j, D j := by
      rw [div_le_iff₀ hr4]
      have := mul_le_mul_of_nonneg_left hu2 Real.pi_pos.le
      nlinarith
    linarith
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ C ^ X.r * Real.exp (-(Real.pi * P.ph / (r1 : ℝ) ^ 4)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by rw [h3]

end

end ReciprocityTheory.ChartRestriction.G.I2
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TofCovolLb

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem tof_covol_lb [IsCMField E] {X : PT E} {DF : ℕ} (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hG : Ext.GHadamard)
    (ob : OrthonormalBasis (Fin (Module.finrank ℝ (IR I))) ℝ (IR I))
    (a : Fin (Module.finrank ℝ (IR I)) → IR I) (ha : ∀ i, (a i : Vsp X.dim) ∈ I)
    (hdet : ob.toBasis.det a ≠ 0) :
    1 ≤ |ob.toBasis.det a| * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph /
      (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
  unfold Ext.GHadamard at hG
  obtain ⟨x, u, hxu, hli, hnorm⟩ := hI.u1
  let u' : Fin (Module.finrank ℝ (IR I)) → IR I := fun j => ⟨u j, (hxu j).2.1⟩
  have hli' : LinearIndependent ℝ u' := LinearIndependent.of_comp (IR I).subtype (by exact hli)
  have hU : IsUnit (ob.toBasis.det u') := by
    rcases isEmpty_or_nonempty (Fin (Module.finrank ℝ (IR I))) with hE | hN
    · rw [Module.Basis.det_apply, Matrix.det_isEmpty]
      exact isUnit_one
    · have hspan : Submodule.span ℝ (Set.range u') = ⊤ :=
        hli'.span_eq_top_of_card_eq_finrank (by simp)
      have hU' := ob.toBasis.isUnit_det (Module.Basis.mk hli' hspan.ge)
      rwa [Module.Basis.coe_mk] at hU'
  have hint : ∀ j k, ∃ m : ℤ, (Hf (x j) (a k : Vsp X.dim)).im = m := fun j k =>
    X.integral _ _ (hxu j).1 (hI.le (ha k))
  let Gz : Matrix (Fin (Module.finrank ℝ (IR I))) (Fin (Module.finrank ℝ (IR I))) ℤ :=
    fun j k => (hint j k).choose
  have hGjk : ∀ j k, inner ℝ (u' j) (a k) = (Gz j k : ℝ) := fun j k => by
    show _ = (((hint j k).choose : ℤ) : ℝ)
    rw [← (hint j k).choose_spec]
    exact (hxu j).2.2 _ (a k).2
  have hmat : Matrix.transpose (ob.toBasis.toMatrix u') * ob.toBasis.toMatrix a = Gz.map (fun m : ℤ => (m : ℝ)) := by
    ext j k
    rw [Matrix.mul_apply, Matrix.map_apply, ← hGjk j k]
    simp only [Matrix.transpose_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    rw [← OrthonormalBasis.sum_inner_mul_inner ob]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm (u' j) (ob i)]
  have hdetG : ob.toBasis.det u' * ob.toBasis.det a = ((Gz.det : ℤ) : ℝ) := by
    rw [Module.Basis.det_apply, Module.Basis.det_apply, ← Matrix.det_transpose (ob.toBasis.toMatrix u'),
      ← Matrix.det_mul, hmat]
    first
      | exact (Int.cast_det Gz).symm
      | exact (RingHom.map_det (Int.castRingHom ℝ) Gz).symm
      | simp [Int.cast_det]
  have hGz : Gz.det ≠ 0 := by
    intro h0
    have h00 : ob.toBasis.det u' * ob.toBasis.det a = 0 := by rw [hdetG, h0, Int.cast_zero]
    rcases mul_eq_zero.mp h00 with h | h
    · exact hU.ne_zero h
    · exact hdet h
  have h1 : (1 : ℝ) ≤ |ob.toBasis.det u'| * |ob.toBasis.det a| := by
    rw [← abs_mul, hdetG]
    exact_mod_cast Int.one_le_abs hGz
  have hH := hG (Module.finrank ℝ (IR I)) (ob.toBasis.toMatrix u')
  rw [← Module.Basis.det_apply] at hH
  have hcol : ∀ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2) ≤ Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) := fun j => by
    apply Real.sqrt_le_sqrt
    have hn : ∑ i, ob.toBasis.toMatrix u' i j ^ 2 = ‖u j‖ ^ 2 := by
      have hu : ‖u j‖ = ‖u' j‖ := rfl
      simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply]
      rw [hu, ← ob.repr.norm_map (u' j), EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hn]
    exact hnorm j
  have hprod : ∏ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2) ≤
      Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
    calc ∏ j, Real.sqrt (∑ i, ob.toBasis.toMatrix u' i j ^ 2)
        ≤ ∏ _j : Fin (Module.finrank ℝ (IR I)), Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) :=
          Finset.prod_le_prod₀ (fun j _ => Real.sqrt_nonneg _) (fun j _ => hcol j)
      _ = Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc (1 : ℝ) ≤ |ob.toBasis.det u'| * |ob.toBasis.det a| := h1
    _ ≤ Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) * |ob.toBasis.det a| :=
      mul_le_mul_of_nonneg_right (hH.trans hprod) (abs_nonneg _)
    _ = |ob.toBasis.det a| * Real.sqrt (PT.rd E ^ 2 * (dstar (E := E) P.m : ℝ) ^ 4 * P.ph / (2 * PT.f E)) ^ Module.finrank ℝ (IR I) := mul_comm _ _

end

end ReciprocityTheory.ChartRestriction.G.I2
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NonnegGT

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E]

theorem l2_nonneg_GT {ι : Type} [Fintype ι] (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) :
    0 ≤ Y.l2 q F := by
  unfold GT.l2
  rw [MeasureTheory.setAverage_eq]
  refine smul_nonneg (inv_nonneg.2 ENNReal.toReal_nonneg) (MeasureTheory.integral_nonneg fun v => ?_)
  unfold GT.ptN2
  exact mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem zeroMode [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    ∃ β ∈ (Col.YB hI hP 1).Sec 1,
      (∀ w : Vsp X.dim, ∀ T M : ℝ, (∀ F : Finset (Vsp X.dim), (∀ y ∈ F, ∃ x ∈ X.L, y = uMap I x) →
          ∑ y ∈ F, Real.exp (-Real.pi * ‖uMap I w - y‖ ^ 2) ≤ T) →
        (∀ t, (Col.YB hI hP 1).ptN2 1 β t ≤ M) →
        Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.sqrt M * T) ∧
      ∃ a : Fin (Module.finrank ℝ (IR I)) → IR I, (∀ i, (a i : Vsp X.dim) ∈ I) ∧
        (Col.ob (IR I)).toBasis.det a ≠ 0 ∧
        |(Col.ob (IR I)).toBasis.det a| * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) *
          (Col.YB hI hP 1).l2 1 β ≤ X.l2 1 s :=
  ⟨ZM.zmB hI s, zm_mem hI hP hs, fun w T M hT hM => zm_pt hI hP hs w T M hT hM, ZM.Ib hI,
    ZM.Ib_mem hI, ZM.Ib_det_ne hI, zm_norm hI hP hs⟩

theorem tof_yb_sup [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF} {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hP : Ext.PackingCount) (hS : GSupStatement) {β : EuclideanSpace ℂ
    (Fin (Col.gB (IR I))) → ℂ} (hβ : β ∈ (Col.YB hI hP 1).Sec 1) (t : EuclideanSpace ℂ (Fin (Col.gB (IR I)))) :
    (Col.YB hI hP 1).ptN2 1 β t ≤ Real.exp P.p1 ^ 2 * (Col.YB hI hP 1).l2 1 β := by
  set Y := Col.YB hI hP 1 with hY
  have key := hS (Fin (Col.gB (IR I))) Y 1 le_rfl β hβ t
  rw [Fintype.card_fin] at key
  set g : ℕ := X.gA with hg
  have hgbg : (Col.gB (IR I)) ≤ g := by
    have h1 := Submodule.finrank_le (Col.V2 (IR I))
    rw [finrank_euclideanSpace, X.card_idx] at h1
    exact h1
  have hg2 : 2 ≤ g := P.hfr
  have hgpos : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have hq : (0 : ℝ) < P.q := by exact_mod_cast P.hq
  have hqth := one_le_sqrt_q_th P
  have hth := Col.th_pos P
  set y : ℝ := 1 + 6 * Real.sqrt (g * P.q) with hy
  have hy1 : 1 ≤ y := by have := Real.sqrt_nonneg (g * P.q); linarith
  have hl0 := l2_nonneg_GT Y 1 β
  have hbase : 1 + 4 * Real.sqrt (2 * (Col.gB (IR I))) / (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1) ≤ y := by
    rcases Nat.eq_zero_or_pos (Col.gB (IR I)) with h0 | hpos
    · have h00 : Real.sqrt (2 * ((Col.gB (IR I)) : ℝ)) = 0 := by rw [h0]; simp
      rw [h00]; simp; linarith
    · have hla : P.th ≤ Y.la1 := by
        apply le_csInf
        · refine ⟨‖Y.b ⟨0, by rw [Fintype.card_fin]; omega⟩‖, Y.b ⟨0, by rw [Fintype.card_fin]; omega⟩, Submodule.subset_span ⟨_, rfl⟩,
            Y.b.ne_zero _, rfl⟩
        · rintro _ ⟨x, hx, hne, rfl⟩
          exact Col.GB_norm hI ((Col.YB_lat hI hP 1).1 hx) hne
      have hla0 : 0 < Y.la1 := lt_of_lt_of_le hth hla
      have hpi : 1 ≤ Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) := by
        rw [Nat.cast_one, one_mul, Real.one_le_sqrt]; linarith [Real.pi_gt_three]
      have hden : 0 < Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1 := by positivity
      have hA : 4 * Real.sqrt (2 * (Col.gB (IR I))) / (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1) ≤
          6 * Real.sqrt (g * P.q) := by
        rw [div_le_iff₀ hden]
        have hgb' : Real.sqrt (2 * ((Col.gB (IR I)) : ℝ)) ≤ Real.sqrt (2 * g) := by
          apply Real.sqrt_le_sqrt; have : ((Col.gB (IR I)) : ℝ) ≤ g := by exact_mod_cast hgbg
          linarith
        rw [Real.sqrt_mul (by norm_num) (g : ℝ), Real.sqrt_mul hgpos.le] at *
        have hs2 : Real.sqrt 2 ≤ 1.5 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        have hsg := Real.sqrt_pos.2 hgpos
        have hsq := Real.sqrt_nonneg (P.q : ℝ)
        have h1 : 1 ≤ Real.sqrt P.q * Y.la1 :=
          le_trans hqth (mul_le_mul_of_nonneg_left hla hsq)
        have h2 : 1 ≤ Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * (Real.sqrt P.q * Y.la1) := by
          nlinarith
        nlinarith
      rw [hy]; linarith
  have hB : 2 * ((1 : ℕ) : ℝ) ^ (Col.gB (IR I)) * (1 + 4 * Real.sqrt (2 * (Col.gB (IR I))) /
      (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1)) ^ (2 * (Col.gB (IR I))) ≤ Real.exp P.p1 ^ 2 := by
    have hp : Real.exp P.p1 ^ 2 = Real.exp 2 * y ^ (2 * g) := by
      rw [← Real.exp_nat_mul, Par.p1, ← hg, ← hy]
      rw [show ((2 : ℕ) : ℝ) * (1 + g * Real.log y) = 2 + ((2 * g : ℕ) : ℝ) * Real.log y by
        push_cast; ring]
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (by linarith)]
    rw [hp]
    have h2e : (2 : ℝ) ≤ Real.exp 2 := by
      have := Real.add_one_le_exp (2 : ℝ); linarith
    have h0 : 0 ≤ 4 * Real.sqrt (2 * (Col.gB (IR I))) / (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1) := by
      apply div_nonneg (by positivity)
      apply mul_nonneg (Real.sqrt_nonneg _)
      rw [GT.la1]; apply Real.sInf_nonneg; rintro _ ⟨x, -, -, rfl⟩; exact norm_nonneg _
    have hb : (1 + 4 * Real.sqrt (2 * (Col.gB (IR I))) /
        (Real.sqrt (((1 : ℕ) : ℝ) * Real.pi) * Y.la1)) ^ (2 * (Col.gB (IR I))) ≤ y ^ (2 * g) := by
      calc _ ≤ y ^ (2 * (Col.gB (IR I))) := pow_le_pow_left₀ (by linarith) hbase _
        _ ≤ y ^ (2 * g) := pow_le_pow_right₀ hy1 (by omega)
    exact mul_le_mul (by rw [Nat.cast_one, one_pow, mul_one]; exact h2e) hb
      (pow_nonneg (by linarith) _) (by positivity)
  exact le_trans key (mul_le_mul_of_nonneg_right hB hl0)

theorem perFactor_of [IsCMField E] (hx : Ext.All) (hS : GSupStatement) {X : PT E} {DF : ℕ}
    (P : Par X DF) {I : Submodule ℤ (Vsp X.dim)}
    (hI : IsSplit P I) (hph : 0 < P.ph) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1) :
    PerFactor P I s := by
  have hP : Ext.PackingCount := hx.1
  have hG : Ext.GHadamard := hx.2.2.2.1
  obtain ⟨β, hβ, hpt, a, haI, hdet, hl2⟩ := zeroMode hI hP hs
  set Y := Col.YB hI hP 1 with hY
  have hLS := tof_yb_sup hI hP hS hβ
  have hl0 := l2_nonneg_GT Y 1 β
  intro w
  obtain ⟨y0, hy0, hsum⟩ := tof_gauss_min_sum P hI hP (uMap I w) (isU_uMap I w).1
  refine ⟨y0, hy0, ?_⟩
  set d := dstar (E := E) P.m with hd
  set Eg := Real.exp (-(Real.pi / 2) * ‖uMap I w - uMap I y0‖ ^ 2) with hEg
  set T := 2 * (3 * (d : ℝ)) ^ d * Eg with hT
  have hpw := hpt w T (Real.exp P.p1 ^ 2 * Y.l2 1 β) hsum hLS
  have hp2 : Real.exp P.p2 = 2 * (3 * (d : ℝ)) ^ d := by
    rw [Par.p2, Real.exp_log]
    have h := tof_two_le_dstar P
    have : (2 : ℝ) ≤ d := by exact_mod_cast h
    exact mul_pos two_pos (pow_pos (by linarith) _)
  have hRHS : 0 ≤ Real.exp (P.p1 + P.p2 + d) * (P.ka0 * P.ph) ^ ((d : ℝ) / 4) * Eg :=
    mul_nonneg (mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (mul_nonneg (Par_ka0_nonneg P) hph.le) _)) (Real.exp_pos _).le
  rcases hl0.lt_or_eq with hlpos | hleq
  · set c := |(Col.ob (IR I)).toBasis.det a| with hc
    have hcpos : 0 < c := abs_pos.2 hdet
    have h2pos : 0 < (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
    have hcl : 0 < c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2) := mul_pos hcpos h2pos
    have hsl : 0 < X.l2 1 s := lt_of_lt_of_le (by positivity) hl2
    have hcov := tof_covol_lb P hI hG (Col.ob (IR I)) a haI hdet
    have hinv := tof_inv_sqrt_le P hph (Module.finrank ℝ (IR I)) (tof_finrank_IR_le P hI) c hcpos hcov
    have hden : Real.sqrt (c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2)) * Real.sqrt (Y.l2 1 β) ≤
        Real.sqrt (X.l2 1 s) := by
      rw [← Real.sqrt_mul hcl.le]; exact Real.sqrt_le_sqrt hl2
    have hnum : Real.sqrt (X.ptN2 1 s fun _ => w) ≤
        Real.exp P.p1 * Real.sqrt (Y.l2 1 β) * T := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (Real.exp_pos _).le] at hpw
      exact hpw
    have hsc := Real.sqrt_pos.2 hcl
    have hsb := Real.sqrt_pos.2 hlpos
    rw [div_le_iff₀ (Real.sqrt_pos.2 hsl)]
    calc Real.sqrt (X.ptN2 1 s fun _ => w) ≤ Real.exp P.p1 * Real.sqrt (Y.l2 1 β) * T := hnum
      _ = Real.exp P.p1 * T * (1 / Real.sqrt (c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2))) *
            (Real.sqrt (c * (2 : ℝ) ^ (-(Module.finrank ℝ (IR I) : ℝ) / 2)) * Real.sqrt (Y.l2 1 β)) := by
          field_simp
      _ ≤ Real.exp P.p1 * T * (Real.exp d * (P.ka0 * P.ph) ^ ((d : ℝ) / 4)) *
            Real.sqrt (X.l2 1 s) := by
          have hTn : 0 ≤ T := by
            rw [hT]
            have h := tof_two_le_dstar P
            have : (2 : ℝ) ≤ d := by exact_mod_cast h
            exact mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg (by linarith) _))
              (Real.exp_pos _).le
          have hA : 0 ≤ Real.exp P.p1 * T := mul_nonneg (Real.exp_pos _).le hTn
          exact mul_le_mul (mul_le_mul_of_nonneg_left hinv hA) hden (by positivity)
            (mul_nonneg hA (mul_nonneg (Real.exp_pos _).le
              (Real.rpow_nonneg (mul_nonneg (Par_ka0_nonneg P) hph.le) _)))
      _ = Real.exp (P.p1 + P.p2 + d) * (P.ka0 * P.ph) ^ ((d : ℝ) / 4) * Eg *
            Real.sqrt (X.l2 1 s) := by
          rw [hT, ← hp2, Real.exp_add, Real.exp_add]; ring
  · rw [← hleq, mul_zero, Real.sqrt_zero, zero_mul] at hpw
    have : Real.sqrt (X.ptN2 1 s fun _ => w) = 0 := le_antisymm hpw (Real.sqrt_nonneg _)
    rw [this, zero_div]; exact hRHS

end

end ReciprocityTheory.ChartRestriction.G.I2
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PerFactor

section

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex NumberField

theorem tOf (hx : Ext.All) (hs : SplitStatement) (hS : GSupStatement) (hd : DimStatement) :
    TStatement := by
  intro E _ _ _ X DF P r1 hr1 a ha hgen s hsmem hs0
  refine ⟨fun hph => ?_, fun h0 => ?_⟩
  · obtain ⟨I, hI⟩ := hs E X DF P
    exact t_assemble P hI (perFactor_of hx hS P hI hph hsmem) r1 hr1 a ha hgen hph
  · calc ∏ j, Real.sqrt (X.ptN2 1 s fun _ => a j) / Real.sqrt (X.l2 1 s)
        ≤ ∏ _j : Fin X.r, Real.exp P.p1 :=
          Finset.prod_le_prod₀ (fun j _ => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (fun j _ => sup_ratio_le_of_phase_zero P hS hsmem h0 (a j))
      _ = Real.exp (X.r * P.p1) := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]

end ReciprocityTheory.ChartRestriction.G.I2
end
end
