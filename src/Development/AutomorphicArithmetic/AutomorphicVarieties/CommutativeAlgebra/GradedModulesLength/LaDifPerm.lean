module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityExactSequence
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerIndependenceOfOrder
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityDegreeZero
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerAdditivityInSection
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIso
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleShift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Linter.Style
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
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleFin
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleGr
import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleIso
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleNzd
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RulePos
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerRuleProductZero

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter


open E7 in
theorem euler_char_product_eventually_add (hE1 : EulerAdditivityExactSequence) (hGr : RuleGr) {k : ℕ} (X : HidaSetting k)
    (ts : List (Deg k × X.R)) (F : X.Mod) (d d' : Deg k) (s s' : X.R)
    (hV : Valid X.𝒜 ((d, s) :: (d', s') :: ts)) (hF : F.IsGr X.𝒜)
    (hA : admitted X.𝒜 ((d + d', s * s') :: ts) F.Ann) :
    ∀ᶠ m in atTop, chi ((d + d', s * s') :: ts) F m =
      chi ((d, s) :: ts) F m + chi ((d', s') :: ts) (F.shift d) m := by
  have hs : 0 ≤ d ∧ s ∈ X.𝒜 d := hV (d, s) List.mem_cons_self
  have hs' : 0 ≤ d' ∧ s' ∈ X.𝒜 d' := hV (d', s') (List.mem_cons_of_mem _ List.mem_cons_self)
  have hVt : Valid X.𝒜 ts :=
    fun p hp => hV p (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
  have hss : s * s' ∈ X.𝒜 (d + d') := SetLike.mul_mem_graded hs.2 hs'.2
  have hFd := (hGr k X F hF).2.1 d
  have hP14 := (hGr k X _ hFd).2.2 d' s' hs'.2
  have hP25 := (hGr k X F hF).2.2 (d + d') (s * s') hss
  have hP36 := (hGr k X F hF).2.2 d s hs.2
  have g2 := product_kernel_to_kernel_isGraded X.𝒜 F s s' d d' hF hs'.2
  have g3 := kernel_to_shift_quotient_isGraded F s s' d
  have g4 := quotient_to_product_quotient_isGraded X.𝒜 F s s' d hF hs.2
  have hI2 := ((hGr k X _ hP36.2).1 _ (g2.range_hom hP25.2.internal)).1
  have hI3 := ((hGr k X _ hP14.1).1 _ (g3.range_hom hP36.2.internal)).1
  have hI4 := ((hGr k X _ hP25.1).1 _ (g4.range_hom hP14.1.internal)).1
  have a2 : admitted X.𝒜 ts (F.ann (s * s') (d + d')).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_sub F _) (mul_mem_annihilator_product_kernel F s s' d d')
  have a3 : admitted X.𝒜 ts (F.ann s d).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_sub F _) (mul_mem_annihilator_kernel F s s' d)
  have a4 : admitted X.𝒜 ts ((F.shift d).quot s').Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_quo (F.shift d) _) (mul_mem_annihilator_shift_quotient F s s' d)
  have a5 : admitted X.𝒜 ts (F.quot (s * s')).Ann :=
    admissible_tail_of_cons_mem_ideal X.𝒜 hA (ann_le_quo F _) (mul_mem_annihilator_product_quotient F s s')
  have e2 := hE1 k X ts _ _ _ hVt hP14.2 hP25.2 hI2
    (sesOfExact (phi1 F s s' d d') (phi2 F s s' d d') (kernel_inclusion_product_injective F s s' d d')
      (kernel_inclusion_product_exact F s s' d d') (kernel_inclusion_grading_comap F s s' d d') g2 hP25.2.internal hP36.2.internal) a2
  have e3 := hE1 k X ts _ _ _ hVt hI2 hP36.2 hI3
    (sesOfKer _ (phi3 F s s' d) (ker3 F s s' d d') g3 hP36.2.internal hP14.1.internal) a3
  have e4 := hE1 k X ts _ _ _ hVt hI3 hP14.1 hI4
    (sesOfKer _ (phi4 F s s' d) (ker4 F s s' d) g4 hP14.1.internal hP25.1.internal) a4
  have e5 := hE1 k X ts _ _ _ hVt hI4 hP25.1 hP36.1 (ses5 F s s' d) a5
  filter_upwards [e2, e3, e4, e5] with m h2 h3 h4 h5
  show chi ts (F.quot (s * s')) m - chi ts (F.ann (s * s') (d + d')) m =
    (chi ts (F.quot s) m - chi ts (F.ann s d) m) +
      (chi ts ((F.shift d).quot s') m - chi ts ((F.shift d).ann s' d') m)
  linarith

theorem euler_rule_product_zero : EulerAdditivityDegreeZero := by
  intro k X ts F d s s' hV hF hA
  have hA' : admitted X.𝒜 ((0 + d, s * s') :: ts) F.Ann := by rwa [zero_add]
  have h := euler_char_product_eventually_add (euler_additivity_of_rules ruleGr ruleFin ruleIso) ruleGr X ts F 0 d s s' hV hF hA'
  rw [zero_add] at h
  filter_upwards [h] with m hm
  rw [hm, chi_shift, sub_zero]

end Formalism.MainNotions.V.Pf.V2.Calc
end
end
end

-- Source module: Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.SumPowersetFinSucc

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open Finset

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

theorem sum_powerset_fin_succ {n : ℕ} (f : Finset (Fin (n + 1)) → ℤ) :
    ∑ I ∈ (univ : Finset (Fin (n + 1))).powerset, f I =
      ∑ J ∈ (univ : Finset (Fin n)).powerset, f (J.image Fin.succ) +
        ∑ J ∈ (univ : Finset (Fin n)).powerset, f (insert 0 (J.image Fin.succ)) := by
  have hu : (univ : Finset (Fin (n + 1))) = insert 0 ((univ : Finset (Fin n)).image Fin.succ) := by
    ext i
    simp only [mem_univ, mem_insert, mem_image, true_and, true_iff]
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, h.symm⟩
  have h0 : (0 : Fin (n + 1)) ∉ (univ : Finset (Fin n)).image Fin.succ := by
    simp only [mem_image, mem_univ, true_and, not_exists]
    exact fun j => Fin.succ_ne_zero j
  have hinj : Function.Injective (fun J : Finset (Fin n) => J.image Fin.succ) :=
    Finset.image_injective (Fin.succ_injective n)
  rw [hu, Finset.sum_powerset_insert h0, Finset.powerset_image,
    Finset.sum_image (fun a _ b _ hab => hinj hab), Finset.sum_image (fun a _ b _ hab => hinj hab)]

end Formalism.MainNotions.V.Pf.V2.Calc
end
end
end

-- Source module: Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.RuleSmall

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter Finset

namespace Sm

section Gen

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]

def hdiff (ts : List (Deg k × R)) (F : GMod B R k) (m : Deg k) : ℤ :=
  ∑ I ∈ (Finset.univ : Finset (Fin ts.length)).powerset,
    (-1 : ℤ) ^ I.card * ((Module.length B (F.gr (m - ∑ i ∈ I, (ts.get i).1))).toNat : ℤ)

theorem hdiff_nil (F : GMod B R k) (m : Deg k) :
    hdiff ([] : List (Deg k × R)) F m = ((Module.length B (F.gr m)).toNat : ℤ) := by
  have : (Finset.univ : Finset (Fin ([] : List (Deg k × R)).length)) = ∅ := rfl
  rw [hdiff, this, Finset.powerset_empty, Finset.sum_singleton, Finset.sum_empty, sub_zero,
    Finset.card_empty, pow_zero, one_mul]

theorem hdiff_cons (d : Deg k) (s : R) (ts : List (Deg k × R)) (F : GMod B R k) (m : Deg k) :
    hdiff ((d, s) :: ts) F m = hdiff ts F m - hdiff ts F (m - d) := by
  show ∑ I ∈ (Finset.univ : Finset (Fin (ts.length + 1))).powerset,
        (-1 : ℤ) ^ I.card *
          ((Module.length B (F.gr (m - ∑ i ∈ I, (((d, s) :: ts).get i).1))).toNat : ℤ) = _
  rw [hdiff, hdiff, sum_powerset_fin_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  have hsum : ∀ J : Finset (Fin ts.length),
      ∑ i ∈ J.image Fin.succ, (((d, s) :: ts).get i).1 = ∑ j ∈ J, (ts.get j).1 := fun J => by
    rw [Finset.sum_image (fun a _ b _ hab => Fin.succ_injective _ hab)]
    rfl
  have h0 : ∀ J : Finset (Fin ts.length), (0 : Fin (ts.length + 1)) ∉ J.image Fin.succ :=
    fun J => by
      simp only [mem_image, not_exists, not_and]
      exact fun j _ => Fin.succ_ne_zero j
  congr 1
  · refine Finset.sum_congr rfl fun J _ => ?_
    rw [hsum, Finset.card_image_of_injective _ (Fin.succ_injective _)]
  · refine Finset.sum_congr rfl fun J _ => ?_
    rw [Finset.sum_insert (h0 J), Finset.card_insert_of_notMem (h0 J), hsum,
      Finset.card_image_of_injective _ (Fin.succ_injective _), pow_succ]
    have : m - d - ∑ j ∈ J, (ts.get j).1
        = m - ((((d, s) :: ts).get (0 : Fin (ts.length + 1))).1 + ∑ j ∈ J, (ts.get j).1) := by
      show _ = m - (d + _)
      rw [sub_sub]
    rw [this]
    ring

theorem ev_shift {p : Deg k → Prop} (d : Deg k) (h : ∀ᶠ m in atTop, p m) :
    ∀ᶠ m in atTop, p (m - d) := by
  rw [eventually_atTop] at h ⊢
  obtain ⟨a, ha⟩ := h
  exact ⟨a + d, fun b hb => ha _ (le_sub_iff_add_le.mpr hb)⟩

theorem admissible_of_admissible_nil [IsLocalRing B] (𝒜 : Deg k → Submodule B R) {J : Ideal R}
    (ts : List (Deg k × R)) (h : admitted 𝒜 [] J) : admitted 𝒜 ts J := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le_sup_left ?_ _)⟩
  rw [secs, Ideal.span_le]
  rintro x ⟨d, hd⟩
  exact absurd hd List.not_mem_nil

def sesSubQuo (F : GMod B R k) (N : Submodule R F.M) : SES (F.sub N) F (F.quo N) where
  f := N.subtype
  g := N.mkQ
  inj := N.injective_subtype
  surj := N.mkQ_surjective
  exact y := by
    constructor
    · intro h
      exact ⟨⟨y, (Submodule.Quotient.mk_eq_zero N).1 h⟩, rfl⟩
    · rintro ⟨x, rfl⟩
      exact (Submodule.Quotient.mk_eq_zero N).2 x.2
  f_gr _ := rfl
  g_gr _ := rfl

def mulS (F : GMod B R k) (s : R) (d : Deg k) : (F.shift d).M →ₗ[R] F.M := LinearMap.lsmul R F.M s

theorem mulS_gr (𝒜 : Deg k → Submodule B R) {F : GMod B R k} (hF : F.IsGr 𝒜) {s : R} {d : Deg k}
    (hs : s ∈ 𝒜 d) : E7.IsGrHom (F.shift d) F (mulS F s d) := by
  intro m x hx
  have hx' : x ∈ F.gr (m - d) := hx
  have h := hF.smul_mem hs hx'
  rwa [show d + (m - d) = m by abel] at h

end Gen

theorem step (hE1 : EulerAdditivityExactSequence) (hGr : RuleGr) {k : ℕ} (X : HidaSetting k) (ts : List (Deg k × X.R))
    (F : X.Mod) (d : Deg k) (s : X.R) (hV : Valid X.𝒜 ts) (hs : s ∈ X.𝒜 d) (hF : F.IsGr X.𝒜)
    (hA : admitted X.𝒜 [] F.Ann) :
    ∀ᶠ m in atTop, chi ((d, s) :: ts) F m = chi ts F m - chi ts F (m - d) := by
  have hFd := (hGr k X F hF).2.1 d
  obtain ⟨hq, ha⟩ := (hGr k X F hF).2.2 d s hs
  have g := mulS_gr X.𝒜 hF hs
  have hI := ((hGr k X F hF).1 _ (g.range_hom hFd.internal)).1
  have hAt : admitted X.𝒜 ts F.Ann := admissible_of_admissible_nil X.𝒜 ts hA
  have e1 := hE1 k X ts (F.ann s d) (F.shift d) _ hV ha hFd hI
    (E7.sesOfKer (G := F.shift d) (H := F) (LinearMap.ker (LinearMap.lsmul X.R F.M s)) (mulS F s d)
      (fun _ => Iff.rfl) g hFd.internal hF.internal) hAt
  have e2 := hE1 k X ts _ F (F.quot s) hV hI hF hq
    (sesSubQuo F (LinearMap.range (LinearMap.lsmul X.R F.M s))) hAt
  filter_upwards [e1, e2] with m h1 h2
  rw [chi_shift] at h1
  show chi ts (F.quot s) m - chi ts (F.ann s d) m = _
  have h2' : chi ts F m = chi ts (F.sub (LinearMap.range (mulS F s d))) m + chi ts (F.quot s) m := h2
  linarith

end Sm


open Sm in
theorem ruleSmall : RuleSmall := by
  intro k X ts
  induction ts with
  | nil =>
    intro F _ _ _
    refine Eventually.of_forall fun m => ?_
    exact (hdiff_nil F m).symm
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro F hV hF hA
    have hs : s ∈ X.𝒜 d := (hV (d, s) List.mem_cons_self).2
    have hV' : Valid X.𝒜 ts := fun p hp => hV p (List.mem_cons_of_mem _ hp)
    have h0 : ∀ᶠ m in atTop, chi ts F m = hdiff ts F m := ih F hV' hF hA
    filter_upwards [step (euler_additivity_of_rules ruleGr ruleFin ruleIso) ruleGr X ts F d s hV' hs hF hA, h0,
      ev_shift d h0] with m h1 h2 h3
    rw [h1, h2, h3]
    exact (hdiff_cons d s ts F m).symm

end Formalism.MainNotions.V.Pf.V2.Calc
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.LaDifPerm

section

@[expose] public section

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem la_dif_perm {k : ℕ} {l l' : List (Deg k)} (h : l.Perm l') (f : Deg k → ℤ) :
    ∀ m, dif l f m = dif l' f m := by
  induction h with
  | nil => intro m; rfl
  | cons a _ ih => intro m; simp only [dif, ih]
  | swap a b l =>
    intro m
    simp only [dif]
    rw [sub_right_comm m a b]
    ring
  | trans _ _ ih1 ih2 => intro m; rw [ih1, ih2]

private theorem la_hdiff {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (ts : List (Deg k × R)) (G : GMod B R k) :
    ∀ m, Sm.hdiff ts G m = dif (ts.map Prod.fst) (hilb G) m := by
  induction ts with
  | nil => intro m; rw [Sm.hdiff_nil]; rfl
  | cons p ts ih =>
    obtain ⟨d, s⟩ := p
    intro m
    rw [Sm.hdiff_cons, ih, ih]
    rfl

private theorem la_adm {k : ℕ} (X : HidaSetting k) (J : Ideal X.R) (d : Deg k) (a y : X.R)
    (ts : List (Deg k × X.R)) (h : admitted X.𝒜 ((d, a * y) :: ts) J) : admitted X.𝒜 ((d, y) :: ts) J := by
  obtain ⟨N, hN⟩ := h
  refine ⟨N, hN.trans (sup_le_sup_left ?_ _)⟩
  rw [secs, Ideal.span_le]
  rintro x ⟨e, he⟩
  rcases List.mem_cons.1 he with h | h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨_, List.mem_cons_self⟩)
  · exact Ideal.subset_span ⟨e, List.mem_cons_of_mem _ h⟩

private theorem la_mem {k : ℕ} (X : HidaSetting k) (β : X.B) (c : ℕ) {d : Deg k} {y : X.R} (hy : y ∈ X.𝒜 d) :
    algebraMap X.B X.R β ^ c * y ∈ X.𝒜 d := by
  rw [← map_pow, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ hy

private theorem la_peel {k : ℕ} (X : HidaSetting k) (F : X.Mod) (hF : F.IsGr X.𝒜) (β : X.B)
    (hβ : ∀ y : F.M, algebraMap X.B X.R β • y = 0 → y = 0)
    (hA : admitted X.𝒜 [] (F.quot (algebraMap X.B X.R β)).Ann) (d : Deg k) (hd : 0 ≤ d) (y : X.R)
    (hy : y ∈ X.𝒜 d) (ts : List (Deg k × X.R)) (hV : Valid X.𝒜 ts) (c : ℕ) :
    admitted X.𝒜 ((d, algebraMap X.B X.R β ^ c * y) :: ts) F.Ann →
    ∀ᶠ m in atTop, chi ((d, algebraMap X.B X.R β ^ c * y) :: ts) F m =
      (c : ℤ) * dif (ts.map Prod.fst) (hilb (F.quot (algebraMap X.B X.R β))) m + chi ((d, y) :: ts) F m := by
  have hb : algebraMap X.B X.R β ∈ X.𝒜 0 := by
    rw [X.std.zero]; exact ⟨β, rfl⟩
  have hs := ruleSmall k X ts _ hV ((ruleGr k X F hF).2.2 0 _ hb).1 hA
  induction c with
  | zero => intro _; simp
  | succ c ih =>
    intro h
    rw [pow_succ', mul_assoc] at h ⊢
    have hV' : Valid X.𝒜 ((0, algebraMap X.B X.R β) :: (d, algebraMap X.B X.R β ^ c * y) :: ts) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨le_rfl, hb⟩
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hd, la_mem X β c hy⟩
      · exact hV p hp
    filter_upwards [euler_rule_product_zero k X ts F d _ _ hV' hF h, ih (la_adm X _ d _ _ ts h), hs] with m h1 h2 h3
    have h4 : chi ts (F.quot (algebraMap X.B X.R β)) m = _ := h3.trans (la_hdiff ts _ m)
    rw [h1, h2, ruleNzd k X ts F 0 _ hβ m, h4]
    push_cast
    ring

theorem UpperTheory.V.Alg.M.la_holds :
    ∀ (k : ℕ) (X : HidaSetting k) (F : X.Mod), F.IsGr X.𝒜 → ∀ β : X.B, (∀ y : F.M, algebraMap X.B X.R β • y = 0 → y = 0) →
      admitted X.𝒜 [] (F.quot (algebraMap X.B X.R β)).Ann → ∀ (d : Deg k), 0 ≤ d → ∀ (n : ℕ) (y : Fin n → X.R) (c : Fin n → ℕ),
      (∀ i, y i ∈ X.𝒜 d) → ∀ us : List (Deg k × X.R), Valid X.𝒜 us →
      admitted X.𝒜 ((List.ofFn fun i => (d, algebraMap X.B X.R β ^ c i * y i)) ++ us) F.Ann →
      ∀ᶠ m in atTop, ((∑ i, c i : ℕ) : ℤ) * dif (List.replicate (n - 1) d ++ us.map Prod.fst) (hilb (F.quot (algebraMap X.B X.R β))) m ≤
        chi ((List.ofFn fun i => (d, algebraMap X.B X.R β ^ c i * y i)) ++ us) F m := by
  intro k X F hF β hβ hA d hd n
  induction n with
  | zero =>
    intro y c _ us hV h
    simpa using rulePos k X us F hV hF (by simpa using h)
  | succ n ih =>
    intro y c hy us hV h
    rw [List.ofFn_succ, List.cons_append] at h ⊢
    set L := (List.ofFn fun i : Fin n => (d, algebraMap X.B X.R β ^ c i.succ * y i.succ)) with hL
    have hVL : Valid X.𝒜 (L ++ us) := by
      intro p hp
      rcases List.mem_append.1 hp with hp | hp
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
        exact ⟨hd, la_mem X β _ (hy _)⟩
      · exact hV p hp
    have hc : ∀ l, Valid X.𝒜 l → Valid X.𝒜 ((d, y 0) :: l) := by
      intro l hl p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hd, hy 0⟩
      · exact hl p hp
    have hP : ((d, y 0) :: (L ++ us)).Perm (L ++ (d, y 0) :: us) := List.perm_middle.symm
    have h' := la_adm X _ d _ _ _ h
    have h'' : admitted X.𝒜 (L ++ (d, y 0) :: us) F.Ann := by
      unfold admitted at h' ⊢
      rwa [← E2.secs_perm hP]
    have hfst : (L ++ us).map Prod.fst = List.replicate n d ++ us.map Prod.fst := by
      rw [List.map_append, hL, List.map_ofFn]
      congr 1
      exact List.ofFn_const n d
    filter_upwards [la_peel X F hF β hβ hA d hd (y 0) (hy 0) _ hVL (c 0) h,
      euler_rule_two_of_graded_finite_iso ruleGr ruleFin ruleIso (euler_additivity_of_rules ruleGr ruleFin ruleIso) k X _ _ F (hc _ hVL) hP hF h',
      ih (fun i => y i.succ) (fun i => c i.succ) (fun i => hy _) _ (hc _ hV) h''] with m h1 h2 h3
    rw [h1, h2, hfst, Fin.sum_univ_succ, Nat.add_sub_cancel, Nat.cast_add, add_mul]
    refine add_le_add le_rfl (le_trans (le_of_eq ?_) h3)
    cases n with
    | zero => simp
    | succ n =>
      congr 1
      refine la_dif_perm ?_ _ m
      rw [Nat.add_sub_cancel, List.replicate_succ, List.map_cons, List.cons_append]
      exact List.perm_middle.symm
end
end
