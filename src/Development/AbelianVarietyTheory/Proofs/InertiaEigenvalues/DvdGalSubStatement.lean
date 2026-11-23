module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDvdOfClosedDiscDvdEisensteinPow
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaussNormCoeffWittDisc
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRings
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfDvdOfClosedDiscDvdEisensteinPowStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.ainf_dvd_of_closed_disc_dvd_eisenstein_pow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), (∀ m : ℕ, bk.iS bk.E ^ m ∣ bk.iA a → bk.ev bk.E ^ m ∣ a) ∧ (bk.iS X ∣ bk.iA a → bk.ev X ∣ a) := by
  first | exact @GlobalTheory.BSP.ainf_dvd_of_disc_dvd | exact GlobalTheory.BSP.ainf_dvd_of_disc_dvd | (intros; apply GlobalTheory.BSP.ainf_dvd_of_disc_dvd; all_goals assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscExistsConstAddXMul

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.DiscSer

variable (l : ℕ) {W : Type} [CommRing W] (ρ : ℝ≥0)

def shiftX (s : W⟦X⟧) : W⟦X⟧ := PowerSeries.mk fun n => coeff (n + 1) s

theorem coeff_shiftX (s : W⟦X⟧) (n : ℕ) : coeff n (shiftX s) = coeff (n + 1) s := coeff_mk _ _

theorem X_mul_shiftX (s : W⟦X⟧) : X * shiftX s = s - C (coeff 0 s) := by
  ext n
  rcases n with _ | n
  · simp
  · rw [coeff_succ_X_mul, coeff_shiftX, map_sub, coeff_C]; simp

theorem eq_zero_of_X_mul_eq_zero {t : W⟦X⟧} (h : X * t = 0) : t = 0 := by
  ext n
  have := congrArg (coeff (n + 1)) h
  rwa [coeff_succ_X_mul, map_zero] at this

theorem exists_rep (y : PreDisc l (X : W⟦X⟧) ρ) : ∃ (c : ℕ) (s : W⟦X⟧),
    y = algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c := by
  obtain ⟨c, s, hs⟩ := IsLocalization.Away.surj (l : W⟦X⟧) y
  exact ⟨c, s, by rw [← hs, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]⟩

theorem aPre_rep (n c : ℕ) (s : W⟦X⟧) :
    aPre l ρ n (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) s *
      IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
      algebraMap W (PreDisc l (0 : W) 1) (coeff n s) *
        IsLocalization.Away.invSelf (S := PreDisc l (0 : W) 1) (l : W) ^ c := by
  rw [aPre_apply, map_mul, phi_alg, map_pow, phi_inv, ← map_pow, coeff_mul_C, coeff_map]

theorem eq_zero_of_X_mul (z : PreDisc l (X : W⟦X⟧) ρ)
    (h : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * z = 0) : z = 0 := by
  obtain ⟨c, t, rfl⟩ := exists_rep l ρ z
  have hu : IsUnit (IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧)) :=
    IsUnit.of_mul_eq_one_right (algebraMap _ _ (l : W⟦X⟧)) (IsLocalization.Away.mul_invSelf _)
  rw [← mul_assoc, ← map_mul] at h
  have h2 : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X * t) = 0 := (hu.pow c).mul_left_eq_zero.1 h
  obtain ⟨⟨m, hm⟩, hm'⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (l : W⟦X⟧)) _ _).1 h2
  obtain ⟨k, rfl⟩ := hm
  have h3 : (l : W⟦X⟧) ^ k * t = 0 :=
    eq_zero_of_X_mul_eq_zero (by rw [mul_left_comm]; exact hm')
  have h4 : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) t = 0 := by
    have h5 := congrArg (algebraMap _ (PreDisc l (X : W⟦X⟧) ρ)) h3
    rw [map_mul, map_zero] at h5
    rw [map_pow] at h5
    exact ((IsLocalization.Away.algebraMap_isUnit (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧)).pow k).mul_right_eq_zero.1 h5
  rw [h4, zero_mul]

abbrev c0 (y : PreDisc l (X : W⟦X⟧) ρ) : PreDisc l (X : W⟦X⟧) ρ :=
  preMap l (0 : W) 1 (X : W⟦X⟧) ρ C (aPre l ρ 0 y)

theorem X_mul_rep (c : ℕ) (s : W⟦X⟧) :
    algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * (algebraMap _ _ (shiftX s) *
      IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
    algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c -
      c0 l ρ (algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) := by
  rw [c0, aPre_rep, map_mul, preMap_alg, map_pow, preMap_inv, ← mul_assoc, ← map_mul, X_mul_shiftX, map_sub,
    sub_mul]

def dFun (y : PreDisc l (X : W⟦X⟧) ρ) : PreDisc l (X : W⟦X⟧) ρ :=
  algebraMap _ _ (shiftX (exists_rep l ρ y).choose_spec.choose) *
    IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ (exists_rep l ρ y).choose

theorem X_mul_dFun (y : PreDisc l (X : W⟦X⟧) ρ) :
    algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * dFun l ρ y = y - c0 l ρ y := by
  have hy := (exists_rep l ρ y).choose_spec.choose_spec
  rw [dFun, X_mul_rep, ← hy]

theorem dFun_eq (y z : PreDisc l (X : W⟦X⟧) ρ)
    (h : algebraMap _ (PreDisc l (X : W⟦X⟧) ρ) (X : W⟦X⟧) * z = y - c0 l ρ y) : dFun l ρ y = z :=
  sub_eq_zero.1 (eq_zero_of_X_mul l ρ _ (by rw [mul_sub, X_mul_dFun, h, sub_self]))

theorem dFun_rep (c : ℕ) (s : W⟦X⟧) :
    dFun l ρ (algebraMap _ _ s * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c) =
      algebraMap _ _ (shiftX s) * IsLocalization.Away.invSelf (S := PreDisc l (X : W⟦X⟧) ρ) (l : W⟦X⟧) ^ c :=
  dFun_eq l ρ _ _ (X_mul_rep l ρ c s)

def DPre : PreDisc l (X : W⟦X⟧) ρ →+ PreDisc l (X : W⟦X⟧) ρ :=
  AddMonoidHom.mk' (dFun l ρ) fun y z => dFun_eq l ρ _ _ (by
    rw [mul_add, X_mul_dFun, X_mul_dFun, c0, c0, c0, map_add (f := _), map_add (f := _)]; abel)

theorem DPre_apply (y : PreDisc l (X : W⟦X⟧) ρ) : DPre l ρ y = dFun l ρ y := rfl

theorem aPre_DPre (n : ℕ) (y : PreDisc l (X : W⟦X⟧) ρ) : aPre l ρ n (DPre l ρ y) = aPre l ρ (n + 1) y := by
  obtain ⟨c, s, rfl⟩ := exists_rep l ρ y
  rw [DPre_apply, dFun_rep, aPre_rep, aPre_rep, coeff_shiftX]

theorem norm_DPre_le [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (y : PreDisc l (X : W⟦X⟧) ρ) :
    ‖DPre l ρ y‖ ≤ (ρ : ℝ)⁻¹ * ‖y‖ := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hρ : (0 : ℝ) < ρ := by exact_mod_cast hρ0
  refine norm_le_of_aPre l ρ hρ0 hρ1 _ _ (by positivity) fun n => ?_
  rw [aPre_DPre, inv_mul_eq_div, le_div_iff₀ hρ, mul_assoc, ← pow_succ]
  exact norm_aPre_le l ρ hl hρ1.le y (n + 1)

theorem continuous_DPre [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Continuous (DPre l ρ (W := W)) :=
  AddMonoidHomClass.continuous_of_bound _ _ (norm_DPre_le l ρ hρ0 hρ1)

theorem exists_const_add_X_mul [Fact l.Prime] (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (κ : Disc l (0 : W) 1 →+* Disc l (X : W⟦X⟧) ρ) (hκ : IsDiscMap (l := _) (u := _) (ρ := _) (C : W →+* W⟦X⟧) κ)
    (x : Disc l (X : W⟦X⟧) ρ) :
    ∃ (c : Disc l (0 : W) 1) (x₁ : Disc l (X : W⟦X⟧) ρ), x = κ c + toDisc l (X : W⟦X⟧) ρ X * x₁ := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  let A0 := (aPre l ρ 0 (W := W)).completion (continuous_aPre l ρ hl hρ0 hρ1.le 0)
  let D := (DPre l ρ (W := W)).completion (continuous_DPre l ρ hρ0 hρ1)
  have hA : ∀ y, A0 (ofPre l (X : W⟦X⟧) ρ y) = ofPre l (0 : W) 1 (aPre l ρ 0 y) := fun y =>
    AddMonoidHom.completion_coe _ _ y
  have hD : ∀ y, D (ofPre l (X : W⟦X⟧) ρ y) = ofPre l (X : W⟦X⟧) ρ (DPre l ρ y) := fun y =>
    AddMonoidHom.completion_coe _ _ y
  have hκc : Continuous κ :=
    AddMonoidHomClass.continuous_of_bound _ 1 fun y => (hκ.norm_le y).trans (one_mul _).ge
  have e : κ.comp (ofPre l (0 : W) 1) = (ofPre l (X : W⟦X⟧) ρ).comp (preMap l (0 : W) 1 (X : W⟦X⟧) ρ C) :=
    IsLocalization.ringHom_ext (Submonoid.powers (l : W)) (RingHom.ext fun a => by
      simp only [RingHom.comp_apply]; rw [preMap_alg]; exact hκ.ext a)
  refine ⟨A0 x, D x, ?_⟩
  refine (denseRange_ofPre l (X : W⟦X⟧) ρ).induction_on x
    (isClosed_eq continuous_id ((hκc.comp (AddMonoidHom.continuous_completion _ _)).add
      (continuous_const.mul (AddMonoidHom.continuous_completion _ _)))) fun y => ?_
  rw [hA, hD, show κ (ofPre l (0 : W) 1 (aPre l ρ 0 y)) = _ from RingHom.congr_fun e _, RingHom.comp_apply,
    show toDisc l (X : W⟦X⟧) ρ X = ofPre l (X : W⟦X⟧) ρ (algebraMap _ _ X) from rfl, ← map_mul, ← map_add,
    DPre_apply, X_mul_dFun]
  congr 1
  abel

end GlobalTheory.BSP.DiscSer

namespace GlobalTheory.BSP

theorem exists_const_add_X_mul_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 →
    ∀ (κ : Disc l (0 : Wq l bk.a) 1 →+* bk.DS ρ), IsDiscMap (l := _) (u := _) (ρ := _) (C : Wq l bk.a →+* bk.S) κ →
    ∀ x : bk.DS ρ, ∃ (c : Disc l (0 : Wq l bk.a) 1) (x₁ : bk.DS ρ), x = κ c + toDisc l (X : bk.S) ρ X * x₁ :=
  fun l _ _ _ ρ hρ0 hρ1 κ hκ x => DiscSer.exists_const_add_X_mul l ρ hρ0 hρ1 κ hκ x

end GlobalTheory.BSP
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscExistsConstAddXMulStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.breuilKisinDisc_exists_const_add_X_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ (κ : Disc l (0 : Wq l bk.a) 1 →+* bk.DS ρ), IsDiscMap (l := _) (u := _) (ρ := _) (C : Wq l bk.a →+* bk.S) κ → ∀ x : bk.DS ρ, ∃ (c : Disc l (0 : Wq l bk.a) 1) (x₁ : bk.DS ρ), x = κ c + toDisc l (X : bk.S) ρ X * x₁ := by
  first | (exact @GlobalTheory.BSP.exists_const_add_X_mul_disc) | (exact GlobalTheory.BSP.exists_const_add_X_mul_disc) | (intros; apply GlobalTheory.BSP.exists_const_add_X_mul_disc  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdGalSub

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.CrPer

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem eq_const_add_X_mul (bk : BK K) (ρ : ℝ≥0) (h0 : 0 < ρ) (h1 : ρ < 1)
    (κ : Disc l (0 : Wq l bk.a) 1 →+* bk.DS ρ) (hκ : IsDiscMap (l := _) (u := _) (ρ := _) (C : Wq l bk.a →+* bk.S) κ) (x : bk.DS ρ) :
    ∃ (c : Disc l (0 : Wq l bk.a) 1) (x₁ : bk.DS ρ), x = κ c + toDisc l (X : bk.S) ρ X * x₁ :=
  GlobalTheory.T.breuilKisinDisc_exists_const_add_X_mul l K bk ρ h0 h1 κ hκ x

theorem isDiscMap_comp {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] {u : A} {u' : A'} {u'' : A''}
    {ρ ρ' ρ'' : ℝ≥0} {f : A →+* A'} {f' : A' →+* A''} {F : Disc l u ρ →+* Disc l u' ρ'}
    {F' : Disc l u' ρ' →+* Disc l u'' ρ''} (hF : IsDiscMap (l := _) (u := _) (ρ := _) f F) (hF' : IsDiscMap (l := _) (u := _) (ρ := _) f' F') :
    IsDiscMap (l := _) (u := _) (ρ := _) (f'.comp f) (F'.comp F) :=
  ⟨fun a => by simp [hF.ext, hF'.ext], fun x => (hF'.norm_le _).trans (hF.norm_le x)⟩

theorem dvd_gal_sub (bk : BK K) (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hG : IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G)
    (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (hi : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i) (x : bk.DS bk.ρ₀) :
    bk.iS X ∣ G (i x) - i x := by
  obtain ⟨hmap, -, -, hρ0, hρ1, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨κ, hκ⟩ := hmap (Wq l bk.a) bk.S C 0 X 1 bk.ρ₀ 0 hρ0 (by simp) (by simp)
  obtain ⟨c, x₁, rfl⟩ := eq_const_add_X_mul bk bk.ρ₀ hρ0 hρ1 κ hκ x
  have hc : G (i (κ c)) = i (κ c) := by
    have h1 : IsDiscMap (l := _) (u := _) (ρ := _) ((Per.σA (g : GQ l)).comp (bk.ev.comp C)) ((G.comp i).comp κ) :=
      isDiscMap_comp hκ (isDiscMap_comp hi hG)
    have h2 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp C) (i.comp κ) := isDiscMap_comp hκ hi
    have e : (Per.σA (g : GQ l)).comp (bk.ev.comp C) = bk.ev.comp C :=
      RingHom.ext fun w => by simp [bk.ev_C, bk.gal_w]
    rw [e] at h1
    exact RingHom.congr_fun (h1.unique h2) c
  obtain ⟨w, hw⟩ := (GlobalTheory.BSP.galois_discMap l K bk).1 (g : GQ l)
  have hX : i (toDisc l (X : bk.S) bk.ρ₀ X) = bk.iS X := hi.ext X
  have hGX : G (bk.iS X) = bk.iS X * bk.iA w := by
    show G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)) = _
    rw [hG.ext, hw, map_mul]; rfl
  rw [map_add i, map_mul i, hX, map_add G, map_mul G, hc, hGX]
  exact ⟨bk.iA w * G (i x₁) - i x₁, by ring⟩

end GlobalTheory.BKLim.CrPer


open GlobalTheory.BKLim.CrPer in
theorem GlobalTheory.BKLim.Frame.isCr_of_wSeed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → (∀ g, s.κ g = 1) → F.IsCr := by
  intro l _ K bk τ _ d ρ _ s N F Y Z _ hZ _ hG hκ g i j
  obtain ⟨hmap, hgal, -, hρ0, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨Gm, hGm⟩ := hgal bk.ρ₀ hρ0 (g : GQ l)
  obtain ⟨im, him⟩ := hmap bk.S (Ainf l) bk.ev X (bk.ev X) bk.ρ₀ bk.ρ₀ 1 hρ0 (by simp) (by simp)
  have key := hG g Gm im hGm him
  rw [hκ g, one_mul] at key
  set q := Ideal.Quotient.mk (Ideal.span {bk.iS X}) with hqdef
  have hq : ∀ x, q (Gm (im x)) = q (im x) := fun x =>
    Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (dvd_gal_sub bk _ Gm hGm im him x))
  have hqS : ∀ a : bk.S, q (Gm (bk.iS a)) = q (bk.iS a) := fun a => by
    have h := hq (toDisc l (X : bk.S) bk.ρ₀ a)
    rwa [him.ext] at h
  have hl : IsUnit ((l : bk.DA bk.ρ₀)) := isUnit_l_disc l (bk.ev X) bk.ρ₀
  have hu0 : q (bk.iS X) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hE : IsUnit (q (bk.iS bk.E)) := by
    obtain ⟨w, hw⟩ := bk.coeff_zero
    have e1 : bk.E = X * PowerSeries.mk (fun p => coeff (p + 1) bk.E) + C ((l : Wq l bk.a) * w) := by
      conv_lhs => rw [eq_X_mul_shift_add_const bk.E]
      rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hw]
    rw [e1]
    simp only [map_add (f := _), map_mul, map_natCast, hu0, zero_mul, zero_add]
    exact (hl.map q).mul ((w.isUnit.map (C : Wq l bk.a →+* bk.S)).map (q.comp bk.iS))
  have hsm : ∀ (c : bk.DA bk.ρ₀) (M : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), (c • M).map q = q c • M.map q :=
    fun c M => by ext a b; simp
  set P := s.X.map bk.iS * Z.map im with hPdef
  have hPG : (P.map Gm).map q = P.map q := by
    ext a b

    simp only [hPdef, Matrix.map_apply, Matrix.mul_apply, map_sum, map_mul, hq, hqS]
  have hPu : IsUnit (P.map q) := by
    rw [hPdef, Matrix.map_mul]
    refine IsUnit.mul ?_ ?_
    · have e : (s.X.map bk.iS).map q = (q.comp bk.iS).mapMatrix s.X := by ext; rfl
      rw [e, Matrix.isUnit_iff_isUnit_det, ← RingHom.map_det]
      have hd := congrArg Matrix.det s.X_mul
      rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hd
      have h2 : IsUnit ((q.comp bk.iS) (s.X.det * s.X'.det)) := by
        rw [hd]
        simp only [map_pow, map_mul, map_natCast, RingHom.comp_apply]
        exact ((((hl.map q).pow _).mul (hE.pow _)).pow _)
      rw [map_mul] at h2
      exact isUnit_of_mul_isUnit_left h2
    · have e : (Z.map im).map q = (q.comp im).mapMatrix Z := by ext; rfl
      rw [e]
      exact hZ.map _
  have k2 := congrArg (fun M => Matrix.map M q) key
  simp only [hsm, Matrix.map_mul, hqS] at k2
  rw [hPG] at k2
  simp only [map_pow, hqS] at k2
  have k3 : q (bk.iS bk.E) ^ s.N • (P.map q * (((F.ε g).map bk.iA).map q - 1)) = 0 := by
    rw [mul_sub, mul_one, smul_sub, k2, sub_self]
  rw [(hE.pow _).smul_eq_zero, hPu.mul_right_eq_zero, sub_eq_zero] at k3
  have k5 : q (bk.iA ((F.ε g - 1) i j)) = 0 := by
    have h := congrFun (congrFun k3 i) j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply] at h ⊢
    split_ifs at h ⊢ <;> simp [h]
  exact (GlobalTheory.T.ainf_dvd_of_closed_disc_dvd_eisenstein_pow l K bk _).2 (Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 k5))
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdGalSubStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.isCr_of_wSeed_alt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Frame bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → (∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G)) → (∀ g, s.κ g = 1) → F.IsCr := by
  first | (exact @GlobalTheory.BKLim.Frame.isCr_of_wSeed) | (exact GlobalTheory.BKLim.Frame.isCr_of_wSeed) | (intros; apply GlobalTheory.BKLim.Frame.isCr_of_wSeed  <;> assumption)
end
end
