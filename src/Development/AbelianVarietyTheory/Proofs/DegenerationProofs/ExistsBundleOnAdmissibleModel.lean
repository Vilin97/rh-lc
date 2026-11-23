module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AddHomExtSingle
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClassicalPointsAndLocalRegularity
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ComparisonFunctionRegular
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAtTestOfCen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisLatticeNear
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DivMemOfForallPowSuccDivPowMem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FFTTNeZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FfDivFfMemOfSpecializes
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsMaximalComapMaximalIdealOO
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreeOrthogonalSupportAndSupISpecializes
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemSupIIffAndHHEqKer
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormDividingWeightSumEqOfModelPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NsmulEqZeroOfCast
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecializesIsLocalization
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemNormWeightSumLeExpOfTest

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FFDivFFMemOOfValuationRing

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem ThetaSys.FF_div_FF_mem_O_of_valuationRing :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → ∀ x₀ ∈ S.supI M z, ∀ j : ℕ, 1 ≤ j → ∃ C : ℕ, (S.FF _ c' k' / S.th x₀) ^ (j + 1) * (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) ^ C / (S.FF _ c k / S.th x₀) ^ j ∈ M.O z) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → IsDomain (M.O ξ) → ValuationRing (M.O ξ) → IsNoetherianRing (M.O ξ) → S.FF _ c' k' / S.FF _ c k ∈ M.O ξ) := by
  intro o Ω _ _ _ _ S M U₀ hO _ H z ξ c c' k k' hz hs hc hk hk' _ hv hn
  obtain ⟨x₀, hx₀⟩ := hO.div z
  have hx₀' : M.Div S.th x₀ ξ := hx₀.of_specializes hs
  have h0 : S.th x₀ ≠ 0 := hx₀.1
  have hP : (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) ≠ 0 ∧ (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀)⁻¹ ∈ M.O ξ := by
    refine finprod_mem_induction (fun u : Ω => u ≠ 0 ∧ u⁻¹ ∈ M.O ξ) ⟨one_ne_zero, by simp⟩ ?_ ?_
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      exact ⟨mul_ne_zero ha hb, by rw [mul_inv]; exact mul_mem ha' hb'⟩
    · intro x hx
      have hx' : M.Div S.th x ξ := hx
      exact ⟨div_ne_zero hx'.1 h0, by rw [inv_div]; exact hx'.2 x₀⟩
  have hval : ∀ x : Ω, x ∈ (M.O ξ).toSubring ∨ x⁻¹ ∈ (M.O ξ).toSubring := by
    intro x
    rcases ValuationRing.isInteger_or_isInteger (M.O ξ) x with ⟨y, hy⟩ | ⟨y, hy⟩
    · exact Or.inl (hy ▸ y.2)
    · exact Or.inr (hy ▸ y.2)
  haveI : ValuationRing (M.O ξ).toSubring := hv
  haveI : IsNoetherianRing (M.O ξ).toSubring := hn
  have key := div_mem_of_forall_pow_succ_div_pow_mem Ω (M.O ξ).toSubring hval
    (S.FF _ c k / S.th x₀) (S.FF _ c' k' / S.th x₀) (div_ne_zero hk.1 h0) (div_ne_zero hk'.1 h0) (by
      intro j hj
      obtain ⟨C, hC⟩ := H z ξ c c' k k' hz hs hc hk hk' x₀ hx₀ j hj
      have h1 := mul_mem (RatModel.O_le_of_specializes hs hC) (pow_mem hP.2 C)
      have hP1 := hP.1
      generalize (∏ᶠ x ∈ S.supI M ξ, S.th x / S.th x₀) = P at h1 hP1
      rw [div_mul_eq_mul_div, _root_.mul_assoc, ← _root_.mul_pow, mul_inv_cancel₀ hP1, _root_.one_pow, _root_.mul_one] at h1
      exact h1)
  rw [div_div_div_cancel_right₀ h0] at key
  exact key

end GlobalTheory.ZH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsEEOfSpanWeightSpaces

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem ThetaSys.FF_mem_ring (S : ThetaSys o Ω) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (k : S.J × (T → ZMod ((S.r * S.N) ^ 2))) : S.FF T c k ∈ S.R := by
  unfold ThetaSys.FF
  refine finsum_induction (· ∈ S.R) (zero_mem _) (fun _ _ => add_mem) fun t => ?_
  exact mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

theorem RatModel.span_val_span {M : RatModel o Ω} {J : Type} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z}
    {z : M.Z} (h : y (cPt p) = z) (w : Sp (PadicAlgCl p)) (G : Set (J → Ω))
    (hG : ∀ v ∈ G, ∀ j, v j ∈ M.O ((gPt p ≫ y) w)) :
    Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' (Submodule.span (M.O z) G)) =
      Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' G) := by
  have hs : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨v, hv, rfl⟩
  suffices H : (∀ j, v j ∈ M.O ((gPt p ≫ y) w)) ∧ (fun j => M.val (gPt p ≫ y) (v j)) ∈
      Submodule.span (OO p) ((fun (v : J → Ω) j => M.val (gPt p ≫ y) (v j)) '' G) from H.2
  induction hv using Submodule.span_induction with
  | mem v hv => exact ⟨hG v hv, Submodule.subset_span ⟨v, hv, rfl⟩⟩
  | zero =>
    refine ⟨fun j => zero_mem _, ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((0 : J → Ω) j)) = 0 := funext fun j => RatModel.val_zero _
    rw [this]
    exact zero_mem _
  | add u v _ _ hu hv =>
    refine ⟨fun j => add_mem (hu.1 j) (hv.1 j), ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((u + v) j)) =
        (fun j => M.val (gPt p ≫ y) (u j)) + fun j => M.val (gPt p ≫ y) (v j) :=
      funext fun j => RatModel.val_add hs (hu.1 j) (hv.1 j)
    rw [this]
    exact add_mem hu.2 hv.2
  | smul a v _ hv =>
    have ha : (a : Ω) ∈ M.O ((gPt p ≫ y) w) := RatModel.O_le_of_specializes (RatModel.gPt_specializes h w) a.2
    refine ⟨fun j => mul_mem ha (hv.1 j), ?_⟩
    have : (fun j => M.val (gPt p ≫ y) ((a • v) j)) =
        (⟨M.val (gPt p ≫ y) a, (mem_OO_iff _).2 (RatModel.norm_val_le_one h a.2)⟩ : OO p) •
          fun j => M.val (gPt p ≫ y) (v j) :=
      funext fun j => RatModel.val_mul hs ha (hv.1 j)
    rw [this]
    exact Submodule.smul_mem _ _ hv.2

theorem RatModel.val_div_mul {M : RatModel o Ω} {K : Type} [Field K] {y : Sp K ⟶ M.Z} {z : M.Z}
    (h : ∀ w, y w ⤳ z) {a b c : Ω} (ha : a ∈ M.O z) (hb : b ∈ M.O z) (hb0 : b ≠ 0) (hb' : b⁻¹ ∈ M.O z)
    (hc : c ∈ M.O z) : M.val y (a / b * c) = M.val y a / M.val y b * M.val y c := by
  have h1 : M.val y b⁻¹ = (M.val y b)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← RatModel.val_mul h hb hb', mul_inv_cancel₀ hb0, RatModel.val_one]
  rw [div_eq_mul_inv, RatModel.val_mul h (mul_mem ha hb') hc, RatModel.val_mul h ha hb', h1, div_eq_mul_inv]

theorem ThetaSys.span_val_eq_testLattice (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens)
    (hA : S.admitted M U₀) {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}
    (τ : S.Test p y₀) (hC : M.Cen U₀ z y) (hAt : S.At M y y₀)
    (hI : ∀ x ∈ S.supI M z, ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ)
    (T : AddSubgroup S.Gam) (hT : T = S.perp τ.yy.ker) (hF : ∀ c : T →+ ZMod S.N, S.FF T c ≠ 0)
    (hα : ∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c)
    (hv : ∀ (c : T →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF T c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) →
      (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) →
      ‖M.val (gPt p ≫ y) (S.FF T c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) :
    Submodule.span (OO p) ((fun (v : S.J → Ω) j => M.val (gPt p ≫ y) (v j)) '' (Submodule.span (M.O z)
      {v | ∃ (c : T →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF T c) k z ∧ x₀ ∈ S.supI M z ∧
        v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)})) = τ.E := by
  subst hT
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hC.2 ⟨w, rfl⟩
  have hs : ∀ w', (gPt p ≫ y) w' ⤳ (gPt p ≫ y) w :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ w)
  have hR : S.R ≤ M.O ((gPt p ≫ y) w) := hA.1.le.trans (RatModel.ringOn_le_O hw)
  have hinv : ∀ c k, M.Div (S.FF (S.perp τ.yy.ker) c) k z → (S.FF _ c k)⁻¹ ∈ M.O ((gPt p ≫ y) w) :=
    fun c k hk => RatModel.ringOn_le_O hw (hA.1.FF_unit _ c k τ.isoFree hk.1)
  have hval : ∀ c k x₀ i, M.Div (S.FF (S.perp τ.yy.ker) c) k z →
      (fun j => M.val (gPt p ≫ y) (S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i))) =
      fun j => M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ c k) *
        y₀ (algebraMap o S.R (S.proj _ c j i)) := by
    intro c k x₀ i hk
    funext j
    rw [RatModel.val_div_mul hs (hR (S.th_mem _)) (hR (S.FF_mem_ring _ _ _)) hk.1 (hinv c k hk)
      (Subalgebra.algebraMap_mem _ _), hAt]
    rfl
  have hnorm : ∀ α k x₀, M.Div (S.FF (S.perp τ.yy.ker) (τ.wt α)) k z → x₀ ∈ S.supI M z →
      (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) →
      ‖M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k)‖ = Real.exp (τ.q α / S.N) := by
    intro α k x₀ hk hx hm
    rw [norm_div, hI x₀ hx, hv _ k α hk hm fun _ _ _ => rfl, Real.exp_neg]
    have := τ.δ_pos.ne'
    have := (Real.exp_pos (τ.q α / S.N)).ne'
    field_simp
  rw [RatModel.span_val_span hC.1 w]
  · refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨_, ⟨c, k, x₀, i, hk, hx, rfl⟩, rfl⟩
      obtain ⟨α, hm, rfl⟩ := hα c
      exact ⟨α, _, i, hm, (hnorm α k x₀ hk hx hm).le, hval _ k x₀ i hk⟩
    · rintro _ ⟨α, l, i, hm, hl, rfl⟩
      obtain ⟨k, hk⟩ := hA.2 _ (τ.wt α) τ.isoFree (hF _) z
      obtain ⟨x₀, hx⟩ := hA.1.div z
      have hn := hnorm α k x₀ hk hx hm
      have hv' := hval _ k x₀ i hk
      generalize M.val (gPt p ≫ y) (S.th x₀) / M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k) = l₀ at hn hv'
      have hpos : 0 < ‖l₀‖ := hn ▸ Real.exp_pos _
      have h0 : l₀ ≠ 0 := norm_pos_iff.1 hpos
      have hq : l / l₀ ∈ OO p := by
        rw [mem_OO_iff, norm_div, div_le_one hpos, hn]
        exact hl
      have : (fun j => l * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i))) =
          (⟨l / l₀, hq⟩ : OO p) • fun j => l₀ * y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) := by
        funext j
        show _ = l / l₀ * (l₀ * _)
        rw [← _root_.mul_assoc, div_mul_cancel₀ _ h0]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨_, k, x₀, i, hk, hx, rfl⟩, hv'⟩)
  · rintro _ ⟨c, k, x₀, i, hk, -, rfl⟩ j
    rw [div_eq_mul_inv]
    exact mul_mem (mul_mem (hR (S.th_mem _)) (hinv c k hk)) (Subalgebra.algebraMap_mem _ _)

theorem isEE_of_span_weightSpaces : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → (∀ z ∈ U₀, EE.E z = Submodule.span (M.O z) (Set.range fun i => Pi.single i (1 : Ω))) → S.IsEE M U₀ EE := by
  intro o Ω _ _ _ hb S M U₀ EE hA h0 _ hF hα hv hE hU
  refine ⟨hU, fun z p _ y y₀ τ hC hAt => ?_⟩
  rw [hE z (hC.1 ▸ isClosed_singleton_cPt y)]
  obtain ⟨hI, hH⟩ := h0 z p y y₀ τ hC hAt
  exact S.span_val_eq_testLattice M U₀ hA τ hC hAt (fun x hx => (hI x).1 hx) _ (congrArg S.perp hH) (hF z)
    (hα p y₀ τ).1 (hv z p y y₀ τ hC hAt)

end GlobalTheory.ZH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanLatticeEqOfValuationRing

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem span_lattice_eq_of_valuationRing :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → S.FF _ c k / S.FF _ c' k' ∈ M.O ξ) → (∀ (z ξ : M.Z) (c : S.TT M z →+ ZMod S.N) (c' : S.TT M ξ →+ ZMod S.N) (k : _) (k' : _), IsClosed ({z} : Set M.Z) → ξ ⤳ z → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ), c ⟨t, h₁⟩ = c' ⟨t, h₂⟩) → M.Div (S.FF (S.TT M z) c) k z → M.Div (S.FF (S.TT M ξ) c') k' ξ → IsDomain (M.O ξ) → ValuationRing (M.O ξ) → IsNoetherianRing (M.O ξ) → S.FF _ c' k' / S.FF _ c k ∈ M.O ξ) → (∀ z ξ : M.Z, IsClosed ({z} : Set M.Z) → ξ ⤳ z → ValuationRing (M.O ξ) → Submodule.span (M.O ξ) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)} = Submodule.span (M.O ξ) {v | ∃ (c : S.TT M ξ →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M ξ) c) k ξ ∧ x₀ ∈ S.supI M ξ ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) := by
  intro o Ω _ _ _ hA S M U₀ hAdm h0 hne hge hle z ξ hz hs hval
  haveI : IsDomain o := hA.inj.isDomain
  haveI := hA.ded
  have hnoeth : IsNoetherianRing (M.O ξ) := (normalModel_height_le_one o Ω M hAdm.1.normal ξ).2.1
  have hT := (h0.1 z).1
  have hT' := (h0.1 ξ).1
  have hsup := h0.2.1 ξ z hs
  have h : S.TT M ξ ≤ S.TT M z := fun a ha x hx => ha x (AddSubgroup.closure_mono hsup hx)
  haveI := FreeNear.finite_char S (S.TT M z)
  haveI := Fintype.ofFinite (S.TT M z →+ ZMod S.N)
  have hmul := (FreeNear.proj_orthogonal S _ hT).1
  have hsum : ∀ c' : S.TT M ξ →+ ZMod S.N, S.proj _ c' =
      ∑ c ∈ Finset.univ.filter fun c : S.TT M z →+ ZMod S.N => c.comp (AddSubgroup.inclusion h) = c',
        S.proj _ c := fun c' => by
    rw [(GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.2 _ _ h hT hT' c', ← finsum_mem_coe_finset]
    simp
  have hcomp : ∀ (c : S.TT M z →+ ZMod S.N) (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.TT M ξ),
      c ⟨t, h₁⟩ = c.comp (AddSubgroup.inclusion h) ⟨t, h₂⟩ := fun _ _ _ _ => rfl
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨c, k, x₀, i, hk, hx, rfl⟩
    obtain ⟨k', hk'⟩ := hAdm.2 _ (c.comp (AddSubgroup.inclusion h)) hT' (hne ξ _) ξ
    have hu := hle z ξ c _ k k' hz hs (hcomp c) hk hk' inferInstance hval hnoeth
    have hp : S.proj _ (c.comp (AddSubgroup.inclusion h)) * S.proj _ c = S.proj _ c := by
      rw [hsum, Finset.sum_mul, Finset.sum_eq_single c]
      · rw [hmul, if_pos rfl]
      · intro b _ hb
        rw [hmul, if_neg hb]
      · simp
    have e : (fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)) =
        ∑ l, ((⟨_, hu⟩ : M.O ξ) * algebraMap o (M.O ξ) (S.proj _ c l i)) •
          fun j => S.th x₀ / S.FF _ (c.comp (AddSubgroup.inclusion h)) k' *
            algebraMap o Ω (S.proj _ (c.comp (AddSubgroup.inclusion h)) j l) := by
      funext j

      conv_lhs => rw [← hp, Matrix.mul_apply, map_sum, Finset.mul_sum]
      rw [Finset.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      have h1 := hk.1
      have h2 := hk'.1
      simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul, MulMemClass.coe_mul,
        Subalgebra.coe_algebraMap, map_mul]
      field_simp
    rw [SetLike.mem_coe, e]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, k', x₀, l, hk', hsup hx, rfl⟩)
  · rintro _ ⟨c', k', x', i, hk', hx', rfl⟩
    obtain ⟨x₀, hx₀⟩ := hAdm.1.div z
    choose k hk using fun c : S.TT M z →+ ZMod S.N => hAdm.2 _ c hT (hne z c) z
    have e : (fun j => S.th x' / S.FF _ c' k' * algebraMap o Ω (S.proj _ c' j i)) =
        ∑ c ∈ Finset.univ.filter fun c : S.TT M z →+ ZMod S.N => c.comp (AddSubgroup.inclusion h) = c',
          fun j => S.th x' / S.FF _ c' k' * algebraMap o Ω (S.proj _ c j i) := by
      funext j

      rw [Finset.sum_apply, hsum, Matrix.sum_apply, map_sum, Finset.mul_sum]
    rw [SetLike.mem_coe, e]
    refine Submodule.sum_mem _ fun c hc => ?_
    obtain rfl := (Finset.mem_filter.1 hc).2
    have hu := mul_mem ((hsup hx₀).2 x') (hge z ξ c _ (k c) k' hz hs (hcomp c) (hk c) hk')
    have e' : (fun j => S.th x' / S.FF _ (c.comp (AddSubgroup.inclusion h)) k' * algebraMap o Ω (S.proj _ c j i)) =
        (⟨_, hu⟩ : M.O ξ) • fun j => S.th x₀ / S.FF _ c (k c) * algebraMap o Ω (S.proj _ c j i) := by
      funext j
      have h1 := (hk c).1
      have h2 := hk'.1
      have h3 := hx₀.1
      simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul]
      field_simp
    rw [e']
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, k c, x₀, i, hk c, hx₀, rfl⟩)

end GlobalTheory.ZH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBundleOnAdmissibleModel

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem exists_isEE_of_adm : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.HasTests → S.admitted M U₀ → ∃ EE : M.Lat S.J, S.IsEE M U₀ EE ∧ (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) := by
  intro o Ω _ _ _ hb S M U₀ hT hA
  have hO : S.Over₀ M U₀ := hA.1
  haveI := hb.ft
  haveI := hb.char
  have hll := @GlobalTheory.ZH.classical_points_and_local_regularity o Ω _ _ _ _ _ M U₀ hO.normal
  have hte := @GlobalTheory.ZH.exists_at_test_of_cen o Ω _ _ _ _ S M U₀ hT hO
  have hwt := @GlobalTheory.ZH.test_weights o Ω _ _ _ _ S
  have h0a := @GlobalTheory.ZH.ThetaSys.mem_supI_iff_and_HH_eq_ker o Ω _ _ _ _ S M U₀ hO
  have h0b := @GlobalTheory.ZH.isoFree_TT_and_supI_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a
  have h11 := @GlobalTheory.thetaSys_norm_FF_le_exp o Ω _ _ _ _ S hwt
  have h12 := @GlobalTheory.norm_val_FF_eq_of_div o Ω _ _ _ _ S M U₀ hO h0a h11 hte
  have hne := @GlobalTheory.ZH.FF_TT_ne_zero o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt
  have h2g := @GlobalTheory.ZH.comparison_function_regular o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt h11 h12
  have h2ge := @GlobalTheory.ZH.FirstIneq.ff_div_ff_mem_of_specializes o Ω _ _ _ _ S M U₀ hO hll hte h0a h0b hwt h11 h12
  have h2le := @GlobalTheory.ZH.ThetaSys.FF_div_FF_mem_O_of_valuationRing o Ω _ _ _ _ S M U₀ hO h0b h2g
  have h3h := @GlobalTheory.ZH.span_lattice_eq_of_valuationRing o Ω _ _ _ _ S M U₀ hA h0b hne h2ge h2le
  have h3b := @GlobalTheory.ZH.exists_basis_lattice_near o Ω _ _ _ _ S M U₀ hA h0b hne
  obtain ⟨EE, hE₁, hE₂⟩ := @GlobalTheory.ZH.WeightBundle.exists_lat o Ω _ _ _ _ S M U₀ hA hll.2 h0b hne h3h h3b
  exact ⟨EE, @GlobalTheory.ZH.isEE_of_span_weightSpaces o Ω _ _ _ _ S M U₀ EE hA h0a h0b hne hwt h12 hE₁ hE₂, hE₁⟩

end GlobalTheory.ZH
end
end
