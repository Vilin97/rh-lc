module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.IsIntegralOfRoot
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFacSer
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModFrobSer
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmForm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmQ
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffRescaleExpandOfNotDvd
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModKronSer

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def Cg (p : ℕ) (f g : PowerSeries ℂ) : Prop :=
  CoeffIn (Rm p) g ∧ ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧ f = g + PowerSeries.C (1 - zetaC p) * w

theorem CoeffIn.ksC {R : Subring ℂ} {c : ℂ} (hc : c ∈ R) : CoeffIn R (PowerSeries.C c) := by
  intro n
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact hc
  · exact R.zero_mem

theorem CoeffIn.ksZero (R : Subring ℂ) : CoeffIn R 0 := by
  intro n
  rw [map_zero]
  exact R.zero_mem

theorem CoeffIn.ksNeg {R : Subring ℂ} {f : PowerSeries ℂ} (hf : CoeffIn R f) : CoeffIn R (-f) := by
  intro n
  rw [map_neg]
  exact R.neg_mem (hf n)

theorem ks_one_sub_zetaC_mem (p : ℕ) : 1 - zetaC p ∈ Rm p := by
  exact (Rm p).sub_mem (Rm p).one_mem (zetaC_mem p)

theorem Cg.left {p : ℕ} {f g : PowerSeries ℂ} (h : Cg p f g) : CoeffIn (Rm p) f := by
  obtain ⟨hg, w, hw, rfl⟩ := h
  exact hg.add ((CoeffIn.ksC (ks_one_sub_zetaC_mem p)).mul hw)

theorem Cg.refl {p : ℕ} {f : PowerSeries ℂ} (hf : CoeffIn (Rm p) f) : Cg p f f := by
  exact ⟨hf, 0, CoeffIn.ksZero _, by simp⟩

theorem Cg.symm {p : ℕ} {f g : PowerSeries ℂ} (h : Cg p f g) : Cg p g f := by
  obtain ⟨hg, w, hw, rfl⟩ := h
  exact ⟨hg.add ((CoeffIn.ksC (ks_one_sub_zetaC_mem p)).mul hw), -w, hw.ksNeg, by ring⟩

theorem Cg.trans {p : ℕ} {f g h : PowerSeries ℂ} (h1 : Cg p f g) (h2 : Cg p g h) : Cg p f h := by
  obtain ⟨hg, w₁, hw₁, rfl⟩ := h1
  obtain ⟨hh, w₂, hw₂, rfl⟩ := h2
  exact ⟨hh, w₂ + w₁, hw₂.add hw₁, by ring⟩

theorem Cg.mul {p : ℕ} {f g f' g' : PowerSeries ℂ} (h1 : Cg p f g) (h2 : Cg p f' g') :
    Cg p (f * f') (g * g') := by
  obtain ⟨hg, w, hw, rfl⟩ := h1
  obtain ⟨hg', w', hw', rfl⟩ := h2
  have hε := CoeffIn.ksC (ks_one_sub_zetaC_mem p)
  refine ⟨hg.mul hg', w * g' + g * w' + PowerSeries.C (1 - zetaC p) * w * w', ?_, by ring⟩
  exact ((hw.mul hg').add (hg.mul hw')).add ((hε.mul hw).mul hw')

theorem Cg.sub {p : ℕ} {f g f' g' : PowerSeries ℂ} (h1 : Cg p f g) (h2 : Cg p f' g') :
    Cg p (f - f') (g - g') := by
  obtain ⟨hg, w, hw, rfl⟩ := h1
  obtain ⟨hg', w', hw', rfl⟩ := h2
  exact ⟨hg.sub hg', w - w', hw.sub hw', by ring⟩

theorem Cg.xp {p : ℕ} {f g : PowerSeries ℂ} (h1 : Cg p f g) (k : ℕ) : Cg p (xp k f) (xp k g) := by
  obtain ⟨hg, w, hw, rfl⟩ := h1
  exact ⟨hg.xp k, ReciprocityTheory.ChartRestriction.L1.xp k w, hw.xp k, by rw [xp_add, xp_C_mul]⟩

theorem Cg.prod {p : ℕ} {α : Type*} (s : Finset α) (f g : α → PowerSeries ℂ)
    (h : ∀ t ∈ s, Cg p (f t) (g t)) : Cg p (∏ t ∈ s, f t) (∏ t ∈ s, g t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact Cg.refl (CoeffIn.one _)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun t ht => h t (Finset.mem_insert_of_mem ht))

theorem Cg.of_int {p : ℕ} (hp : p.Prime) {F G W : PowerSeries ℤ} (h : F = G + PowerSeries.C (p : ℤ) * W) :
    Cg p (F.map (Int.castRingHom ℂ)) (G.map (Int.castRingHom ℂ)) := by
  obtain ⟨r, hr, hpr⟩ := p_mem_span hp
  refine ⟨CoeffIn.map_int _ G, PowerSeries.C r * W.map (Int.castRingHom ℂ),
    (CoeffIn.ksC hr).mul (CoeffIn.map_int _ W), ?_⟩
  rw [h, map_add (f := _), map_mul, PowerSeries.map_C]
  have hc : (Int.castRingHom ℂ) (p : ℤ) = (1 - zetaC p) * r := by
    rw [eq_intCast, Int.cast_natCast, hpr]
  rw [hc, map_mul]
  ring

theorem ks_coeffIn_aC (R : Subring ℂ) : CoeffIn R aC := CoeffIn.map_int R aZ

theorem ks_coeffIn_dC (R : Subring ℂ) : CoeffIn R dC := CoeffIn.map_int R dZ

theorem Cg.xp_map_int {p : ℕ} (hp : p.Prime) (F : PowerSeries ℤ) :
    Cg p (ReciprocityTheory.ChartRestriction.L1.xp p (F.map (Int.castRingHom ℂ))) (F.map (Int.castRingHom ℂ) ^ p) := by
  obtain ⟨g, hg⟩ := xp_congr hp F
  have h := Cg.of_int hp hg
  rwa [← xp_map, map_pow] at h

theorem ks_xp_one {R : Type*} [CommRing R] (f : PowerSeries R) : xp 1 f = f := by
  ext n
  rw [coeff_xp]
  simp

theorem ks_xp_xp {R : Type*} [CommRing R] {k : ℕ} (hk : k ≠ 0) (f : PowerSeries R) :
    xp (k ^ 2) f = xp k (xp k f) := by
  ext n
  rw [coeff_xp, coeff_xp, coeff_xp]
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  by_cases h1 : k ∣ n
  · obtain ⟨m, rfl⟩ := h1
    rw [if_pos (dvd_mul_right k m), Nat.mul_div_cancel_left m hk0]
    by_cases h2 : k ∣ m
    · obtain ⟨j, rfl⟩ := h2
      rw [if_pos (dvd_mul_right k j), if_pos ⟨j, by ring⟩, Nat.mul_div_cancel_left j hk0,
        show k * (k * j) = k ^ 2 * j by ring, Nat.mul_div_cancel_left j (by positivity)]
    · rw [if_neg h2, if_neg]
      rintro ⟨j, hj⟩
      exact h2 ⟨j, Nat.eq_of_mul_eq_mul_left hk0 (by rw [hj]; ring)⟩
  · rw [if_neg h1, if_neg]
    exact fun h => h1 (dvd_trans (dvd_pow_self k two_ne_zero) h)

theorem Tm_prime {p : ℕ} (hp : p.Prime) :
    Tm p = insert (p, 0, 1) ((Finset.range p).image fun b => (1, b, p)) := by
  ext ⟨a, b, e⟩
  rw [mem_Tm hp.pos, Finset.mem_insert, Finset.mem_image]
  simp only [Finset.mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨hae, hbe⟩
    have ha : a ∣ p := ⟨e, hae.symm⟩
    rcases hp.eq_one_or_self_of_dvd a ha with rfl | rfl
    · right
      exact ⟨b, by omega, rfl, rfl, by omega⟩
    · left
      have he : e = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (hae.trans (mul_one a).symm)
      subst he
      exact ⟨rfl, by omega, rfl⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨c, hc, rfl, rfl, rfl⟩)
    · exact ⟨mul_one _, Nat.zero_lt_one⟩
    · exact ⟨one_mul _, hc⟩

theorem Tm_prime_notMem {p : ℕ} (hp : p.Prime) :
    ((p, 0, 1) : ℕ × ℕ × ℕ) ∉ (Finset.range p).image fun b => ((1, b, p) : ℕ × ℕ × ℕ) := by
  intro h
  obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h
  simp only [Prod.mk.injEq] at hb
  exact hp.one_lt.ne hb.1

theorem Tm_prime_inj (p : ℕ) : Function.Injective fun b : ℕ => ((1, b, p) : ℕ × ℕ × ℕ) := by
  intro b b' h
  simp only [Prod.mk.injEq] at h
  exact h.2.1

theorem card_Tm_prime {p : ℕ} (hp : p.Prime) : (Tm p).card = p + 1 := by
  rw [Tm_prime hp, Finset.card_insert_of_notMem (Tm_prime_notMem hp),
    Finset.card_image_of_injective _ (Tm_prime_inj p), Finset.card_range]

theorem facSer_Cg_a {p : ℕ} (hp : p.Prime) :
    Cg p (facSer p (p, 0, 1)) (xp p (aC * dC ^ p - aC ^ p * dC)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hsub : ∀ f : PowerSeries ℂ,
      sub1 (zetaC ((p, 0, 1) : ℕ × ℕ × ℕ).2.2 ^ ((p, 0, 1) : ℕ × ℕ × ℕ).2.1)
        (((p, 0, 1) : ℕ × ℕ × ℕ).1 ^ 2) f = xp p (xp p f) := by
    intro f
    simp only [sub1, pow_zero, PowerSeries.rescale_one, RingHom.id_apply]
    exact ks_xp_xp hp0 f
  have hfac : facSer p (p, 0, 1) = xp p (aC * xp p dC - xp p aC * dC) := by
    rw [facSer, hsub, hsub, xp_sub, xp_mul hp0, xp_mul hp0]
  rw [hfac]
  have hd : Cg p (xp p dC) (dC ^ p) := Cg.xp_map_int hp dZ
  have ha : Cg p (xp p aC) (aC ^ p) := Cg.xp_map_int hp aZ
  exact (((Cg.refl (ks_coeffIn_aC _)).mul hd).sub (ha.mul (Cg.refl (ks_coeffIn_dC _)))).xp p

theorem Cg.rescale_map_int {p : ℕ} (hp : 0 < p) (b : ℕ) (F : PowerSeries ℤ) :
    Cg p (PowerSeries.rescale (zetaC p ^ b) (F.map (Int.castRingHom ℂ))) (F.map (Int.castRingHom ℂ)) := ⟨CoeffIn.map_int _ F, rescale_congr hp b F⟩

theorem facSer_Cg_b {p : ℕ} (hp : p.Prime) (b : ℕ) :
    Cg p (facSer p (1, b, p)) (xp p aC * dC - aC * xp p dC) := by
  have hsub : ∀ f : PowerSeries ℂ,
      sub1 (zetaC ((1, b, p) : ℕ × ℕ × ℕ).2.2 ^ ((1, b, p) : ℕ × ℕ × ℕ).2.1)
        (((1, b, p) : ℕ × ℕ × ℕ).1 ^ 2) f = PowerSeries.rescale (zetaC p ^ b) f := by
    intro f
    simp only [sub1, one_pow]
    exact ks_xp_one _
  rw [facSer, hsub, hsub]
  have hd : Cg p (PowerSeries.rescale (zetaC p ^ b) dC) dC := Cg.rescale_map_int hp.pos b dZ
  have ha : Cg p (PowerSeries.rescale (zetaC p ^ b) aC) aC := Cg.rescale_map_int hp.pos b aZ
  exact ((Cg.refl ((ks_coeffIn_aC _).xp p)).mul hd).sub (ha.mul (Cg.refl ((ks_coeffIn_dC _).xp p)))

theorem pow_Cg {p : ℕ} (hp : p.Prime) :
    Cg p ((xp p aC * dC - aC * xp p dC) ^ p) (- xp p (aC * dC ^ p - aC ^ p * dC)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have haR : CoeffIn (Rm p) aC := ks_coeffIn_aC _
  have hdR : CoeffIn (Rm p) dC := ks_coeffIn_dC _
  obtain ⟨w, hw⟩ := sub_pow_congr hp (xp p aZ * dZ) (aZ * xp p dZ)
  have h1 := Cg.of_int hp hw
  simp only [map_pow, map_sub, map_mul, ← xp_map] at h1
  have ha : Cg p (xp p aC) (aC ^ p) := Cg.xp_map_int hp aZ
  have hd : Cg p (xp p dC) (dC ^ p) := Cg.xp_map_int hp dZ
  have h2 : Cg p ((xp p aC * dC) ^ p - (aC * xp p dC) ^ p)
      (xp p (aC ^ p * dC) - xp p (aC * dC ^ p)) := by
    rw [mul_pow, mul_pow, xp_mul hp0, xp_mul hp0, xp_pow hp0, xp_pow hp0]
    exact ((Cg.refl ((haR.xp p).pow p)).mul hd.symm).sub (ha.symm.mul (Cg.refl ((hdR.xp p).pow p)))
  have h3 : xp p (aC ^ p * dC) - xp p (aC * dC ^ p) = - xp p (aC * dC ^ p - aC ^ p * dC) := by
    rw [xp_sub]
    ring
  rw [← h3]
  exact h1.trans h2

theorem kronSer {p : ℕ} (hp : p.Prime) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧
      prodSer p + xp p ((aC * dC ^ p - aC ^ p * dC) ^ 2) = PowerSeries.C (1 - zetaC p) * w := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hprod : prodSer p = facSer p (p, 0, 1) * ∏ b ∈ Finset.range p, facSer p (1, b, p) := by
    rw [prodSer, Tm_prime hp, Finset.prod_insert (Tm_prime_notMem hp),
      Finset.prod_image (fun b _ b' _ h => Tm_prime_inj p h)]
  have hB : Cg p (∏ b ∈ Finset.range p, facSer p (1, b, p))
      (∏ _b ∈ Finset.range p, (xp p aC * dC - aC * xp p dC)) :=
    Cg.prod _ _ _ fun b _ => facSer_Cg_b hp b
  rw [Finset.prod_const, Finset.card_range] at hB
  have hC := (facSer_Cg_a hp).mul (hB.trans (pow_Cg hp))
  rw [← hprod] at hC
  obtain ⟨-, w, hw, hwe⟩ := hC
  refine ⟨w, hw, ?_⟩
  rw [hwe, xp_pow hp0]
  ring

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQExpEq

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem IsMF.qExp_eq {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) {s : PowerSeries ℂ} (hs : Conv s)
    (h : ∀ τ, ev s (qm 1 τ) = f τ) : qExpansion 1 f = s := by
  have hq : ∀ x : ℂ, 0 < ‖x‖ → ‖x‖ < 1 → ∃ τ : ℍ, qm 1 τ = x := by
    intro x hx0 hx1
    have hx : x ≠ 0 := norm_pos_iff.mp hx0
    refine ⟨⟨Function.Periodic.invQParam 1 x,
      Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hx1 hx⟩, ?_⟩
    have h1 := Function.Periodic.qParam_right_inv one_ne_zero hx
    unfold Function.Periodic.qParam at h1
    unfold qm
    simpa using h1
  have hsum : ∀ τ : ℍ, HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) (f τ) :=
    fun τ => hf.hasSum τ
  have hconv : Conv (qExpansion 1 f) := by
    intro x hx
    obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (‖x‖ + 1) / 2 := ⟨_, rfl⟩
    have hy0 : 0 < y := by rw [hy]; positivity
    have hy1 : y < 1 := by linarith
    have hxy : ‖x‖ < y := by linarith
    have hyn : ‖(y : ℂ)‖ = y := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy0]
    obtain ⟨τ, hτ⟩ := hq (y : ℂ) (by rw [hyn]; exact hy0) (by rw [hyn]; exact hy1)
    have hs := hsum τ
    rw [hτ] at hs
    have ht : Filter.Tendsto (fun n => ‖PowerSeries.coeff n (qExpansion 1 f) * (y : ℂ) ^ n‖)
        Filter.atTop (nhds 0) := by
      simpa using hs.summable.tendsto_atTop_zero.norm
    obtain ⟨C, hC⟩ := ht.bddAbove_range
    have hr0 : 0 ≤ ‖x‖ / y := by positivity
    have hr1 : ‖x‖ / y < 1 := (div_lt_one hy0).mpr hxy
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
    have hb := hC ⟨n, rfl⟩
    have he : ‖PowerSeries.coeff n (qExpansion 1 f)‖ * ‖x‖ ^ n =
        ‖PowerSeries.coeff n (qExpansion 1 f) * (y : ℂ) ^ n‖ * (‖x‖ / y) ^ n := by
      rw [norm_mul, norm_pow, hyn, div_pow]
      field_simp <;> ring
    rw [he]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  refine eq_of_ev_eq hconv hs fun x hx0 hx1 => ?_
  obtain ⟨τ, rfl⟩ := hq x hx0 hx1
  rw [h τ]
  exact (hsum τ).tsum_eq

end ReciprocityTheory.ChartRestriction.L1
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModKronPt

section

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

def kronFun (p : ℕ) (τ : ℍ) : ℂ := Gm p τ + (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2

theorem kronSq_isMF (p : ℕ) :
    IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (fun τ => (AA τ * DD τ ^ p - AA τ ^ p * DD τ) ^ 2) := by
  have h1 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ * DD τ ^ p) := isMF_AA.mul (isMF_DD.pow p)
  have h2 : IsMF (12 + ((p : ℕ) : ℤ) * 12) (fun τ => AA τ ^ p * DD τ) :=
    ((isMF_AA.pow p).mul isMF_DD).congr_weight (by ring)
  have h3 := (h1.sub h2).pow 2
  exact h3.congr_weight (by push_cast; ring)

theorem Gm_isMF' {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (Gm p) := (gmForm hp.pos).congr_weight (by rw [card_Tm_prime hp]; push_cast; ring)

theorem kronFun_isMF {p : ℕ} (hp : p.Prime) : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) (kronFun p) := (Gm_isMF' hp).add (kronSq_isMF p)

theorem aC_conv : Conv aC := convergesOnDisk_eisensteinFourCubeSeries
theorem dC_conv : Conv dC := convergesOnDisk_discriminantSeries
theorem aC_ev (τ : ℍ) : ev aC (qm 1 τ) = AA τ := by
  exact evalSeries_eisensteinFourCubeSeries τ
theorem dC_ev (τ : ℍ) : ev dC (qm 1 τ) = DD τ := by
  exact evalSeries_discriminantSeries τ

theorem kronFun_qExp {p : ℕ} (hp : p.Prime) :
    qExpansion 1 (kronFun p) = qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2 := by
  have hq : ∀ τ : ℍ, ‖qm 1 τ‖ < 1 := fun τ => by
    rw [qm_one_eq]
    simpa using UpperHalfPlane.norm_qParam_lt_one 1 τ
  have hG := Gm_isMF' hp
  have c1 : Conv (aC * dC ^ p) := aC_conv.mul (dC_conv.pow p)
  have c2 : Conv (aC ^ p * dC) := (aC_conv.pow p).mul dC_conv
  have c3 : Conv (aC * dC ^ p - aC ^ p * dC) := c1.sub c2
  apply (kronFun_isMF hp).qExp_eq (hG.conv.add (c3.pow 2))
  intro τ
  rw [ev_add hG.conv (c3.pow 2) (hq τ), hG.ev_eq τ, ev_pow c3 2 (hq τ), ev_sub c1 c2 (hq τ),
    ev_mul aC_conv (dC_conv.pow p) (hq τ), ev_pow dC_conv p (hq τ), ev_mul (aC_conv.pow p) dC_conv (hq τ),
    ev_pow aC_conv p (hq τ), aC_ev, dC_ev]
  rfl

theorem kronFun_div {p : ℕ} (hp : p.Prime) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧ qExpansion 1 (kronFun p) = PowerSeries.C (1 - zetaC p) * w := by
  obtain ⟨w, hw, hk⟩ := kronSer hp
  have hp0 : 0 < p := hp.pos
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (p * n) w, fun n => by simpa using hw (p * n), ?_⟩
  rw [kronFun_qExp hp]
  ext n
  have key : PowerSeries.coeff (p * n) (xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2)) =
      PowerSeries.coeff n (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    simp [xp, PowerSeries.coeff_mk, Nat.mul_div_cancel_left n hp0]
  have hsum : xp p (qExpansion 1 (Gm p) + (aC * dC ^ p - aC ^ p * dC) ^ 2) =
      prodSer p + xp p ((aC * dC ^ p - aC ^ p * dC) ^ 2) := by
    rw [← gmQ_xp hp0]
    ext m
    simp only [xp, PowerSeries.coeff_mk, map_add (f := _)]
    split_ifs <;> simp
  rw [← key, hsum, hk]
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]

theorem kronFun_poly {p : ℕ} (hp : p.Prime) :
    ∃ Q : Polynomial ℂ, (∀ i, Q.coeff i ∈ Rm p) ∧
      ∀ τ, kronFun p τ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * Q.eval (jT τ)) := by
  obtain ⟨w, hw, hqe⟩ := kronFun_div hp
  have hc0 : (1 - zetaC p) ≠ 0 := one_sub_zeta_ne_zero hp
  have hK := kronFun_isMF hp
  let f : ℍ → ℂ := fun τ => (1 - zetaC p)⁻¹ * kronFun p τ
  have hf : IsMF (12 * ((2 * (p + 1) : ℕ) : ℤ)) f := hK.const_mul (1 - zetaC p)⁻¹
  have hwq : qExpansion 1 f = w := by
    apply hf.qExp_eq
    · have e : w = PowerSeries.C (1 - zetaC p)⁻¹ * qExpansion 1 (kronFun p) := by
        rw [hqe, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc0, map_one, one_mul]
      rw [e]
      exact hK.conv.C_mul _
    · intro τ
      have hs := (hK.hasSum τ).mul_left (1 - zetaC p)⁻¹
      have hw' : ∀ n, PowerSeries.coeff n w * qm 1 τ ^ n =
          (1 - zetaC p)⁻¹ * (PowerSeries.coeff n (qExpansion 1 (kronFun p)) * qm 1 τ ^ n) := by
        intro n
        rw [hqe, PowerSeries.coeff_C_mul]
        field_simp
      unfold ev
      simp_rw [hw']
      exact hs.tsum_eq
  obtain ⟨P, hPc, -, hPe⟩ := qPrin (Rm p) (2 * (p + 1)) f hf (by rw [hwq]; exact hw)
  refine ⟨P, hPc, fun τ => ?_⟩
  calc kronFun p τ = (1 - zetaC p) * f τ := by
        rw [show f τ = (1 - zetaC p)⁻¹ * kronFun p τ from rfl, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    _ = (1 - zetaC p) * (DD τ ^ (2 * (p + 1)) * P.eval (jT τ)) := by rw [hPe τ]

theorem kronPt {p : ℕ} (hp : p.Prime) {τ : ℍ} (h : Gm p τ = 0) :
    ∃ r : ℂ, IsIntegral ℤ r ∧ (jT τ ^ p - jT τ) ^ 2 = (1 - zetaC p) * r := by
  obtain ⟨Q, hQ, hK⟩ := kronFun_poly hp
  have hD := DD_ne_zero τ
  have hsq : ¬ IsSquare p := Irreducible.not_isSquare hp
  have hj := jT_isIntegral hp.pos hsq h
  have hint : IsIntegral ℤ (Q.eval (jT τ)) := by
    rw [Polynomial.eval_eq_sum_range]
    exact IsIntegral.sum _ fun i _ => (Rm_isIntegral hp.pos (hQ i)).mul (hj.pow i)
  refine ⟨Q.eval (jT τ), hint, ?_⟩
  have e1 := hK τ
  unfold kronFun at e1
  rw [h, zero_add] at e1
  have hA : AA τ = jT τ * DD τ := by rw [jT, div_mul_cancel₀ _ hD]
  rw [hA] at e1
  have e2 : (jT τ ^ p - jT τ) ^ 2 * DD τ ^ (2 * (p + 1)) =
      (1 - zetaC p) * Q.eval (jT τ) * DD τ ^ (2 * (p + 1)) := by
    linear_combination e1
  exact mul_right_cancel₀ (pow_ne_zero _ hD) e2

end ReciprocityTheory.ChartRestriction.L1
end
end
end
