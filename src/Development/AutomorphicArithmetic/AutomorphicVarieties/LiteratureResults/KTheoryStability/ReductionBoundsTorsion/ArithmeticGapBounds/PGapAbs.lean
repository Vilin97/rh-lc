module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AEConst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.AeEqCosetAvgOfMemInvariantSubspace
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PGapAvg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PGapAng

section

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap.PGap

theorem pt_bound {z p q t : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (ht : 0 < t) (h : z ^ 2 ≤ 1 / 25 * (p * q)) :
    |z| ≤ (t * p + q / t) / 10 := by
  have hts : t * (q / t) = q := by field_simp
  have hw : 0 ≤ (t * p + q / t) / 10 := by positivity
  have h4 : z ^ 2 ≤ ((t * p + q / t) / 10) ^ 2 := by
    nlinarith [sq_nonneg (t * p - q / t)]
  exact abs_le_of_sq_le_sq' h4 hw |> fun h => abs_le.mpr h

section Ang

variable {Λ S : Type} [Group Λ] [Countable Λ] [Group S] [MeasurableSpace S] [MeasurableMul S]
  {μ : Measure S} [μ.IsMulLeftInvariant] {j : Λ →* S}
  (hU : Unfold) (hj : Function.Injective j) {B : Subgroup Λ} {DB : Set S}
  (hDB : IsFundamentalDomain (B.map j) DB μ)

include hU hj hDB

theorem perp_avg {K : Subgroup Λ} (hBK : B ≤ K) (hiK : (B.subgroupOf K).index ≠ 0) {DK : Set S}
    (hDK : IsFundamentalDomain (K.map j) DK μ) {a : S → ℝ} (ha : Good j B μ DB a)
    (hperp : cls j B μ DB a ∈ (W j B μ DB K)ᗮ) : cls j B μ DB (avg j B K a) = 0 := by
  have hm := good_avg hU hj hDB hBK hiK hDK ha
  have hmK : LInv j K (avg j B K a) := u_inv μ hU hj hBK hiK ha.2.1
  have hmW := mem_W_of_inv hU hj hDB hBK hiK hDK hm hmK
  have h0 := Submodule.inner_right_of_mem_orthogonal hmW hperp
  rw [cls_inner hm ha] at h0
  have key : ∫ x in DB, avg j B K a x ^ 2 ∂μ = ∫ x in DB, avg j B K a x * a x ∂μ := by
    have e : (fun x => avg j B K a x ^ 2) = fun x => avg j B K a x * avg j B K a x := by
      funext x; ring
    rw [e, u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => avg j B K a x * avg j B K a x) (hm.1.mul hm.1) (linv_mul j hm.2.1 hm.2.1)
        (integrableOn_mul hm.2.2 hm.2.2),
      u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => avg j B K a x * a x) (hm.1.mul ha.1) (linv_mul j hm.2.1 ha.2.1)
        (integrableOn_mul hm.2.2 ha.2.2)]
    congr 2; funext x
    rw [avg_mul_left j hmK, avg_mul_left j hmK, u_id μ hU hj hBK hiK hmK]
  have hn : ‖cls j B μ DB (avg j B K a)‖ ^ 2 = 0 := by rw [cls_norm_sq hm, key, h0]
  exact norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 hn)

theorem core (hD : Design) {E E' K : Subgroup Λ} (hB : B = E ⊓ E') (hEK : E ≤ K) (hE'K : E' ≤ K)
    (hiK : (B.subgroupOf K).index ≠ 0) (htwo : TwoTr E K) (hbig : 25 ≤ (B.subgroupOf E').index)
    {DK : Set S} (hDK : IsFundamentalDomain (K.map j) DK μ) {a b : S → ℝ} (ha : Good j B μ DB a)
    (haE : LInv j E a) (hz : ∀ x, avg j B K a x = 0) (hb : Good j B μ DB b) (hbE : LInv j E' b) :
    |∫ x in DB, a x * b x ∂μ| ≤
      1 / 5 * (Real.sqrt (∫ x in DB, a x ^ 2 ∂μ) * Real.sqrt (∫ x in DB, b x ^ 2 ∂μ)) := by
  have hBK : B ≤ K := hB ▸ inf_le_left.trans hEK
  have hab := integrableOn_mul ha.2.2 hb.2.2
  have haa := integrableOn_mul ha.2.2 ha.2.2
  have hbb := integrableOn_mul hb.2.2 hb.2.2
  have sa : (fun x => a x ^ 2) = fun x => a x * a x := by funext x; ring
  have sb : (fun x => b x ^ 2) = fun x => b x * b x := by funext x; ring
  rw [sa, sb]
  rw [u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => a x * b x) (ha.1.mul hb.1) (linv_mul j ha.2.1 hb.2.1) hab,
    u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => a x * a x) (ha.1.mul ha.1) (linv_mul j ha.2.1 ha.2.1) haa,
    u_int_eq μ hU hj hBK hiK hDK hDB (u := fun x => b x * b x) (hb.1.mul hb.1) (linv_mul j hb.2.1 hb.2.1) hbb]
  have iab := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => a x * b x) (ha.1.mul hb.1) (linv_mul j ha.2.1 hb.2.1) hab
  have iaa := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => a x * a x) (ha.1.mul ha.1) (linv_mul j ha.2.1 ha.2.1) haa
  have ibb := u_int_avg μ hU hj hBK hiK hDK hDB (u := fun x => b x * b x) (hb.1.mul hb.1) (linv_mul j hb.2.1 hb.2.1) hbb
  set n : ℝ := ((B.subgroupOf K).index : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast Nat.pos_of_ne_zero hiK
  set I := ∫ x in DK, avg j B K (fun y => a y * b y) x ∂μ
  set X := ∫ x in DK, avg j B K (fun y => a y * a y) x ∂μ
  set Y := ∫ x in DK, avg j B K (fun y => b y * b y) x ∂μ
  have pa : ∀ x, 0 ≤ avg j B K (fun y => a y * a y) x := fun x => avg_nonneg j (fun y => mul_self_nonneg _) x
  have pb : ∀ x, 0 ≤ avg j B K (fun y => b y * b y) x := fun x => avg_nonneg j (fun y => mul_self_nonneg _) x
  have hX : 0 ≤ X := integral_nonneg pa
  have hY : 0 ≤ Y := integral_nonneg pb
  have hpt : ∀ x, avg j B K (fun y => a y * b y) x ^ 2 ≤
      1 / 25 * (avg j B K (fun y => a y * a y) x * avg j B K (fun y => b y * b y) x) := by
    intro x
    have := hD Λ S j B E E' K hB hEK hE'K hiK htwo hbig a b haE hbE x (hz x)
    simpa only [sq] using this
  have ht : ∀ t : ℝ, 0 < t → |I| ≤ (t * X + Y / t) / 10 := by
    intro t ht
    calc |I| ≤ ∫ x in DK, |avg j B K (fun y => a y * b y) x| ∂μ := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ.restrict DK)
            (fun x => avg j B K (fun y => a y * b y) x)
      _ ≤ ∫ x in DK, (t * avg j B K (fun y => a y * a y) x + avg j B K (fun y => b y * b y) x / t) / 10 ∂μ :=
          integral_mono iab.abs (((iaa.const_mul t).add (ibb.div_const t)).div_const 10)
            fun x => pt_bound (pa x) (pb x) ht (hpt x)
      _ = (t * X + Y / t) / 10 := by
          rw [integral_div, integral_add (iaa.const_mul t) (ibb.div_const t), integral_const_mul,
            integral_div]
  have h1 := t_trick hX hY ht
  rw [abs_mul, abs_of_pos hn0, Real.sqrt_mul hn0.le, Real.sqrt_mul hn0.le]
  have hs : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  calc n * |I| ≤ n * (1 / 5 * (Real.sqrt X * Real.sqrt Y)) := mul_le_mul_of_nonneg_left h1 hn0.le
    _ = 1 / 5 * (Real.sqrt n * Real.sqrt X * (Real.sqrt n * Real.sqrt Y)) := by
      linear_combination (-(1 / 5 * (Real.sqrt X * Real.sqrt Y))) * hs

theorem angle (hD : Design) {E E' K : Subgroup Λ} (hB : B = E ⊓ E') (hEK : E ≤ K) (hE'K : E' ≤ K)
    (hiK : (B.subgroupOf K).index ≠ 0) (htwo : TwoTr E K) (hbig : 25 ≤ (B.subgroupOf E').index)
    {DK DE DE' : Set S} (hDK : IsFundamentalDomain (K.map j) DK μ)
    (hDE : IsFundamentalDomain (E.map j) DE μ) (hDE' : IsFundamentalDomain (E'.map j) DE' μ) :
    ∀ u ∈ W j B μ DB E, u ∈ (W j B μ DB K)ᗮ → ∀ u' ∈ W j B μ DB E',
      |⟪u, u'⟫_ℝ| ≤ 1 / 5 * (‖u‖ * ‖u'‖) := by
  intro u hu hperp u' hu'
  have hBE : B ≤ E := hB ▸ inf_le_left
  have hBE' : B ≤ E' := hB ▸ inf_le_right
  have hBK : B ≤ K := hBE.trans hEK
  have hiE := (idx_ne hBE hEK hiK).1
  have hiE' := (idx_ne hBE' hE'K hiK).1
  obtain ⟨a, ha, rfl⟩ := cls_surj u
  obtain ⟨b, hb, rfl⟩ := cls_surj u'
  have ha1 := good_avg hU hj hDB hBE hiE hDE ha
  have ha1E : LInv j E (avg j B E a) := u_inv μ hU hj hBE hiE ha.2.1
  have e1 : cls j B μ DB a = cls j B μ DB (avg j B E a) :=
    (cls_eq_iff ha ha1).2 (ae_eq_cosetAvg_of_mem_invariantSubspace hU hj hDB hBE hiE hDE ha hu)
  have hb1 := good_avg hU hj hDB hBE' hiE' hDE' hb
  have hb1E : LInv j E' (avg j B E' b) := u_inv μ hU hj hBE' hiE' hb.2.1
  have e2 : cls j B μ DB b = cls j B μ DB (avg j B E' b) :=
    (cls_eq_iff hb hb1).2 (ae_eq_cosetAvg_of_mem_invariantSubspace hU hj hDB hBE' hiE' hDE' hb hu')
  rw [e1] at hperp ⊢
  rw [e2]
  have hm := good_avg hU hj hDB hBK hiK hDK ha1
  have hmK : LInv j K (avg j B K (avg j B E a)) := u_inv μ hU hj hBK hiK ha1.2.1
  have h0 := perp_avg hU hj hDB hBK hiK hDK ha1 hperp
  have ha2 := good_sub ha1 hm
  have e3 : cls j B μ DB (avg j B E a) =
      cls j B μ DB (fun x => avg j B E a x - avg j B K (avg j B E a) x) := by
    rw [cls_sub ha1 hm, h0, sub_zero]
  rw [e3]
  have ha2E : LInv j E (fun x => avg j B E a x - avg j B K (avg j B E a) x) :=
    linv_sub j ha1E (linv_mono j hEK hmK)
  have hz : ∀ x, avg j B K (fun x => avg j B E a x - avg j B K (avg j B E a) x) x = 0 := by
    intro x
    rw [avg_sub j hiK, u_id μ hU hj hBK hiK hmK, sub_self]
  rw [cls_inner ha2 hb1, ← Real.sqrt_sq (norm_nonneg (cls j B μ DB _)),
    ← Real.sqrt_sq (norm_nonneg (cls j B μ DB (avg j B E' b))), cls_norm_sq ha2, cls_norm_sq hb1]
  exact core hU hj hDB hD hB hEK hE'K hiK htwo hbig hDK ha2 ha2E hz hb1 hb1E

end Ang

end PositivityTheory.KB.SpectralGap.PGap

end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PGapAbs

section

@[expose] public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace PositivityTheory.KB.SpectralGap

open PGap

theorem gapAbs_of : Hilb → Design → Unfold → AEConst → GapAbs := by
  intro hH hD hU hA Λ S _ _ _ _ _ _ _ _ _ _ μ _ j hj K₀ K₁ K₂ hT hdense D₀ D₁ D₂ hD₀ hD₁ hD₂ hfin h01
    w hwm hwi hw2 hw0
  set B := K₀ ⊓ K₁ ⊓ K₂ with hBdef
  have hBE1 : B ≤ K₀ ⊓ K₁ := inf_le_left
  have hBE2 : B ≤ K₀ ⊓ K₂ := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hBE3 : B ≤ K₁ ⊓ K₂ := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hE1K0 : K₀ ⊓ K₁ ≤ K₀ := inf_le_left
  have hE1K1 : K₀ ⊓ K₁ ≤ K₁ := inf_le_right
  have hE2K0 : K₀ ⊓ K₂ ≤ K₀ := inf_le_left
  have hE2K2 : K₀ ⊓ K₂ ≤ K₂ := inf_le_right
  have hE3K1 : K₁ ⊓ K₂ ≤ K₁ := inf_le_left
  have hE3K2 : K₁ ⊓ K₂ ≤ K₂ := inf_le_right
  have hBK0 : B ≤ K₀ := hBE1.trans hE1K0
  have hBK1 : B ≤ K₁ := hBE1.trans hE1K1
  have i0 : (B.subgroupOf K₀).index ≠ 0 := hT.fin₀
  have i1 : (B.subgroupOf K₁).index ≠ 0 := hT.fin₁
  have i2 : (B.subgroupOf K₂).index ≠ 0 := hT.fin₂
  have iBE1 := (idx_ne hBE1 hE1K0 i0).1
  have iE1K0 := (idx_ne hBE1 hE1K0 i0).2
  have iE1K1 := (idx_ne hBE1 hE1K1 i1).2
  have iBE2 := (idx_ne hBE2 hE2K0 i0).1
  have iE2K0 := (idx_ne hBE2 hE2K0 i0).2
  have iBE3 := (idx_ne hBE3 hE3K1 i1).1
  have iE3K1 := (idx_ne hBE3 hE3K1 i1).2
  obtain ⟨DB, hDB⟩ := u_dom μ hU hj hBK0 i0 hD₀
  obtain ⟨DE1, hDE1⟩ := u_dom μ hU hj hE1K0 iE1K0 hD₀
  obtain ⟨DE2, hDE2⟩ := u_dom μ hU hj hE2K0 iE2K0 hD₀
  obtain ⟨DE3, hDE3⟩ := u_dom μ hU hj hE3K1 iE3K1 hD₁

  have hm0 := u_measure μ hU hj hBK0 i0 hD₀ hDB
  have hm1 := u_measure μ hU hj hBK1 i1 hD₁ hDB
  have : Countable (K₀.map j) := countable_map
  have hD0ne : μ D₀ ≠ 0 := hD₀.measure_ne_zero (NeZero.ne μ)
  have hidx : (B.subgroupOf K₀).index = (B.subgroupOf K₁).index := by
    have h : ((B.subgroupOf K₀).index : ENNReal) * μ D₀ = (B.subgroupOf K₁).index * μ D₀ := by
      rw [← hm0, hm1, h01]
    exact_mod_cast (ENNReal.mul_left_inj hD0ne hfin.ne).1 h
  have hDBfin : μ DB < ⊤ := by
    rw [hm0]; exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hfin
  have : IsFiniteMeasure (μ.restrict DB) := isFiniteMeasure_restrict.2 hDBfin.ne
  have : IsFiniteMeasure (μ.restrict D₁) := isFiniteMeasure_restrict.2 (h01 ▸ hfin).ne

  have hwB : LInv j B w := linv_mono j hBK1 hwi
  have hw2B : IntegrableOn (fun x => w x ^ 2) DB μ :=
    (int_iff_inv μ hU hj hBK1 i1 hD₁ hDB (hwm.pow_const 2) (linv_sq j hwi)).2 hw2
  have hwG : Good j B μ DB w := (good_iff hwm hwB).2 hw2B

  set v := avg j (K₀ ⊓ K₁) K₀ w with hv
  have hvm : Measurable v := u_meas μ hU hj hE1K0 iE1K0 hwm
  have hvK : LInv j K₀ v := u_inv μ hU hj hE1K0 iE1K0 (linv_mono j hE1K1 hwi)
  have hv2 : IntegrableOn (fun x => v x ^ 2) D₀ μ := by
    have h1 : IntegrableOn (fun x => w x ^ 2) DE1 μ :=
      (int_iff_inv μ hU hj hE1K1 iE1K1 hD₁ hDE1 (hwm.pow_const 2) (linv_sq j hwi)).2 hw2
    rw [u_int_iff μ hU hj hE1K0 iE1K0 hD₀ hDE1 (hwm.pow_const 2)
      (linv_sq j (linv_mono j hE1K1 hwi))] at h1
    have e : (avg j (K₀ ⊓ K₁) K₀ fun y => |w y ^ 2|) = avg j (K₀ ⊓ K₁) K₀ fun y => w y ^ 2 := by
      congr 1; funext y; exact abs_of_nonneg (sq_nonneg _)
    rw [e] at h1
    refine h1.mono' (hvm.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact avg_sq_le j iE1K0 w x
  have hv2B : IntegrableOn (fun x => v x ^ 2) DB μ :=
    (int_iff_inv μ hU hj hBK0 i0 hD₀ hDB (hvm.pow_const 2) (linv_sq j hvK)).2 hv2
  have hvG : Good j B μ DB v := (good_iff hvm (linv_mono j hBK0 hvK)).2 hv2B

  have hwint1 : IntegrableOn w D₁ μ :=
    ((memLp_two_iff_integrable_sq hwm.aestronglyMeasurable).2 hw2).integrable (by norm_num)
  have hwE1 : IntegrableOn w DE1 μ := (int_iff_inv μ hU hj hE1K1 iE1K1 hD₁ hDE1 hwm hwi).2 hwint1
  have hv0 : ∫ x in D₀, v x ∂μ = 0 := by
    have e1 := int_eq_inv μ hU hj hE1K1 iE1K1 hD₁ hDE1 hwm hwi hwE1
    have e2 := u_int_eq μ hU hj hE1K0 iE1K0 hD₀ hDE1 hwm (linv_mono j hE1K1 hwi) hwE1
    rw [hw0, mul_zero] at e1
    rw [e1] at e2
    have hne : (((K₀ ⊓ K₁).subgroupOf K₀).index : ℝ) ≠ 0 := by exact_mod_cast iE1K0
    exact (mul_eq_zero.1 e2.symm).resolve_left hne

  have hker : cls j B μ DB v ∈
      (W j B μ DB (K₀ ⊓ K₁) ⊓ W j B μ DB (K₀ ⊓ K₂) ⊓ W j B μ DB (K₁ ⊓ K₂))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro f hf
    obtain ⟨F, hF, rfl⟩ := cls_surj f
    rw [Submodule.mem_inf, Submodule.mem_inf] at hf
    obtain ⟨⟨h1, h2⟩, h3⟩ := hf
    have inv : ∀ {E : Subgroup Λ}, B ≤ E → (B.subgroupOf E).index ≠ 0 → ∀ {DE : Set S},
        IsFundamentalDomain (E.map j) DE μ → cls j B μ DB F ∈ W j B μ DB E →
        ∀ γ ∈ E, (fun x => F (j γ * x)) =ᵐ[μ] F := by
      intro E hBE hiE DE hDE hW γ hγ
      have hae := ae_eq_cosetAvg_of_mem_invariantSubspace hU hj hDB hBE hiE hDE hF hW
      have hG := good_avg hU hj hDB hBE hiE hDE hF
      have hsp := ae_spread hDB hF.1 hG.1 hF.2.1 hG.2.1 hae
      have hinv := u_inv μ hU hj hBE hiE hF.2.1
      have e : (fun x => avg j B E F (j γ * x)) = avg j B E F := funext fun x => hinv γ hγ x
      exact ((ae_translate (j γ) hsp).trans (Filter.EventuallyEq.of_eq e)).trans hsp.symm
    let G : Subgroup Λ :=
      { carrier := {γ | (fun x => F (j γ * x)) =ᵐ[μ] F}
        one_mem' := by
          simp only [Set.mem_ofPred_eq, map_one, one_mul]; exact Filter.EventuallyEq.rfl
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_ofPred_eq, map_mul, mul_assoc] at ha hb ⊢
          exact (ae_translate (j b) ha).trans hb
        inv_mem' := by
          intro a ha
          simp only [Set.mem_ofPred_eq, map_inv] at ha ⊢
          have := ae_translate (j a)⁻¹ ha
          simp only [mul_inv_cancel_left] at this
          exact this.symm }
    have hE1G : K₀ ⊓ K₁ ≤ G := fun γ hγ => inv hBE1 iBE1 hDE1 h1 γ hγ
    have hE2G : K₀ ⊓ K₂ ≤ G := fun γ hγ => inv hBE2 iBE2 hDE2 h2 γ hγ
    have hE3G : K₁ ⊓ K₂ ≤ G := fun γ hγ => inv hBE3 iBE3 hDE3 h3 γ hγ
    obtain ⟨g, hg, hgB⟩ := exists_not_mem hT.big₀₂
    have hgE1 : g ∉ K₀ ⊓ K₁ := fun h => hgB (Subgroup.mem_inf.2 ⟨h, (Subgroup.mem_inf.1 hg).2⟩)
    have hK0 : K₀ ≤ G := twoTr_le hT.two₀ hE1G (Subgroup.mem_inf.1 hg).1 hgE1 (hE2G hg)
    obtain ⟨g', hg', hg'B⟩ := exists_not_mem hT.big₀₁
    have hg'E3 : g' ∉ K₁ ⊓ K₂ := fun h =>
      hg'B (Subgroup.mem_inf.2 ⟨hg', (Subgroup.mem_inf.1 h).2⟩)
    have hK1 : K₁ ≤ G := twoTr_le hT.two₁ hE3G (Subgroup.mem_inf.1 hg').2 hg'E3 (hE1G hg')
    have hsup : K₀ ⊔ K₁ ≤ G := sup_le hK0 hK1
    obtain ⟨c, hc⟩ := hA S μ ((K₀ ⊔ K₁).map j) hdense F hF.1 (by
      rintro _ ⟨γ, hγ, rfl⟩
      exact hsup hγ)
    rw [cls_inner hF hvG]
    have hFc : (fun x => F x * v x) =ᵐ[μ.restrict DB] fun x => c * v x :=
      (ae_restrict_of_ae hc).mono fun x hx => by dsimp only; rw [hx]
    have hvint : IntegrableOn v DB μ := hvG.2.2.integrable (by norm_num)
    rw [integral_congr_ae hFc, integral_const_mul,
      int_eq_inv μ hU hj hBK0 i0 hD₀ hDB hvm hvK hvint, hv0, mul_zero, mul_zero]

  have hB1 : B = (K₀ ⊓ K₁) ⊓ (K₀ ⊓ K₂) := by
    rw [hBdef]; ext x; simp only [Subgroup.mem_inf]; tauto
  have hB2 : B = (K₁ ⊓ K₂) ⊓ (K₀ ⊓ K₁) := by
    rw [hBdef]; ext x; simp only [Subgroup.mem_inf]; tauto
  have hB3 : B = (K₁ ⊓ K₂) ⊓ (K₀ ⊓ K₂) := by
    rw [hBdef]; ext x; simp only [Subgroup.mem_inf]; tauto
  have a1 := angle hU hj hDB hD hB1 hE1K0 hE2K0 i0 hT.two₀ hT.big₀₂ hD₀ hDE1 hDE2
  have a2 := angle hU hj hDB hD hB2 hE3K1 hE1K1 i1 hT.two₁ hT.big₀₁ hD₁ hDE3 hDE1
  have a3 := angle hU hj hDB hD hB3 hE3K2 hE2K2 i2 hT.two₂ hT.big₀₂ hD₂ hDE3 hDE2
  have le12 := le_inf (W_anti hU hj hDB hBE1 hE1K0 i0 hDE1 hD₀) (W_anti hU hj hDB hBE2 hE2K0 i0 hDE2 hD₀)
  have le13 := le_inf (W_anti hU hj hDB hBE1 hE1K1 i1 hDE1 hD₁) (W_anti hU hj hDB hBE3 hE3K1 i1 hDE3 hD₁)
  have le23 := le_inf (W_anti hU hj hDB hBE2 hE2K2 i2 hDE2 hD₂) (W_anti hU hj hDB hBE3 hE3K2 i2 hDE3 hD₂)
  have hvmem : cls j B μ DB v ∈ W j B μ DB (K₀ ⊓ K₁) ⊓ W j B μ DB (K₀ ⊓ K₂) :=
    Submodule.mem_inf.2 ⟨mem_W_of_inv hU hj hDB hBE1 iBE1 hDE1 hvG (linv_mono j hE1K0 hvK),
      mem_W_of_inv hU hj hDB hBE2 iBE2 hDE2 hvG (linv_mono j hE2K0 hvK)⟩
  have hwmem : cls j B μ DB w ∈ W j B μ DB (K₀ ⊓ K₁) ⊓ W j B μ DB (K₁ ⊓ K₂) :=
    Submodule.mem_inf.2 ⟨mem_W_of_inv hU hj hDB hBE1 iBE1 hDE1 hwG (linv_mono j hE1K1 hwi),
      mem_W_of_inv hU hj hDB hBE3 iBE3 hDE3 hwG (linv_mono j hE3K1 hwi)⟩
  have hmain := hH (HL j B μ DB) (W j B μ DB (K₀ ⊓ K₁)) (W j B μ DB (K₀ ⊓ K₂))
    (W j B μ DB (K₁ ⊓ K₂)) (W j B μ DB K₀) (W j B μ DB K₁) (W j B μ DB K₂)
    (W_closed _ _ _ _ _) (W_closed _ _ _ _ _) (W_closed _ _ _ _ _) (W_closed _ _ _ _ _)
    (W_closed _ _ _ _ _) (W_closed _ _ _ _ _) le12 le13 le23 a1 a2 a3 _ hvmem hker _ hwmem

  have hBw : avg j B K₀ w = v := by
    rw [← u_trans μ hU hj hBK0 i0 hBE1 hE1K0 hwB,
      u_id μ hU hj hBE1 iBE1 (linv_mono j hE1K1 hwi)]
  have hin : ⟪cls j B μ DB v, cls j B μ DB w⟫_ℝ =
      (B.subgroupOf K₀).index * ∫ x in D₀, v x ^ 2 ∂μ := by
    rw [cls_inner hvG hwG, u_int_eq μ hU hj hBK0 i0 hD₀ hDB (u := fun x => v x * w x) (hvm.mul hwm)
      (linv_mul j (linv_mono j hBK0 hvK) hwB) (integrableOn_mul hvG.2.2 hwG.2.2)]
    congr 2; funext x
    rw [avg_mul_left j hvK, hBw, sq]
  have hnv : ‖cls j B μ DB v‖ ^ 2 = (B.subgroupOf K₀).index * ∫ x in D₀, v x ^ 2 ∂μ := by
    rw [cls_norm_sq hvG, int_eq_inv μ hU hj hBK0 i0 hD₀ hDB (u := fun x => v x ^ 2) (hvm.pow_const 2)
      (linv_sq j hvK) hv2B]
  have hnw : ‖cls j B μ DB w‖ ^ 2 = (B.subgroupOf K₀).index * ∫ x in D₁, w x ^ 2 ∂μ := by
    rw [cls_norm_sq hwG, int_eq_inv μ hU hj hBK1 i1 hD₁ hDB (u := fun x => w x ^ 2) (hwm.pow_const 2)
      (linv_sq j hwi) hw2B, hidx]
  refine ⟨hv2, hv0, ?_⟩
  set n : ℝ := ((B.subgroupOf K₀).index : ℝ)
  have hn0 : 0 < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero i0)
  set P := ∫ x in D₀, v x ^ 2 ∂μ
  set Q := ∫ x in D₁, w x ^ 2 ∂μ
  set a := ‖cls j B μ DB v‖
  set b := ‖cls j B μ DB w‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  rw [hin] at hmain
  have h1 : a ^ 2 ≤ 2 / 5 * (a * b) := by rw [hnv]; exact (le_abs_self _).trans hmain
  have h2 : a ^ 2 ≤ (2 / 5) ^ 2 * b ^ 2 := by
    rcases ha.lt_or_eq with ha' | ha'
    · have : a ≤ 2 / 5 * b := by nlinarith
      nlinarith
    · rw [← ha']; nlinarith [sq_nonneg b]
  rw [hnv, hnw] at h2
  have : n * P ≤ n * ((2 / 5) ^ 2 * Q) := by linarith
  exact le_of_mul_le_mul_left this hn0

end PositivityTheory.KB.SpectralGap

end
end
end
