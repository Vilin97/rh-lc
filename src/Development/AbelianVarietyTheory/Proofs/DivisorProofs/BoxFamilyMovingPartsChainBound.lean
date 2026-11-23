module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanHeightNefOfIsNefStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfIntersectionMonoOfIsNefStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFubiniStudyOfTotallyOrderedRatFnFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyBundleIsNefOfNonnegWeightsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLBLeBySmallSectionIffLocalQuotientsStatement
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundleIsNefShiftOfNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFubiniStudyBoxFamilyStatement
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudySubfamilyLeShiftFubiniStudyFamily

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

variable {X : Scheme.{0}} [IsIntegral X]

theorem unitAt_ne_zero {x : X} {h : X.functionField} (hh : UnitAt x h) : h ≠ 0 := by
  obtain ⟨b, hb, rfl⟩ := hh
  intro e
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField (b * ↑hb.unit⁻¹) = 1 := by
    rw [IsUnit.mul_val_inv, map_one]
  rw [map_mul, e, zero_mul] at h1
  exact zero_ne_one h1

theorem regAt_div_unitAt {x : X} {g h : X.functionField} (hg : RegAt x g) (hh : UnitAt x h) :
    RegAt x (g / h) := by
  obtain ⟨a, ha⟩ := hg
  obtain ⟨b, hb, hbh⟩ := hh
  refine ⟨a * ↑hb.unit⁻¹, ?_⟩
  have h1 : algebraMap (X.presheaf.stalk x) X.functionField b *
      algebraMap (X.presheaf.stalk x) X.functionField ↑hb.unit⁻¹ = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  rw [map_mul, ha, div_eq_mul_inv, ← hbh, eq_inv_of_mul_eq_one_right h1]

theorem le_shift_of_isFS_sub : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k),
    ∀ (M M' : HermLB p) (J J' : Type) [Fintype J] [Fintype J'] (f : J → X.functionField) (w : J → ℝ)
      (w' : J' → ℝ) (ι : J' → J) (Δ : ℝ), Function.Injective ι → IsFS M f w → IsFS M' (f ∘ ι) w' →
      (∀ j, w' j + Δ ≤ w (ι j)) → Le (M'.shift (fun _ => Δ) fun _ => rfl) M := by
  intro k _ X _ p M M' J J' _ _ f w w' ι Δ hι hM hM' hw
  rw [GlobalTheory.T.hermLBLeBySmallSection_iff_localQuotients]
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hM
  obtain ⟨ρ', hρ', hreg', hφ'⟩ := hM'
  simp only [Function.comp_apply] at hreg' hφ'

  have hq : ∀ (x : X) c d (j' : J'), UnitAt x (f (ι j') * (ρ' d : X.functionField)) →
      (ρ c : X.functionField) / (ρ' d : X.functionField) =
        f (ι j') * (ρ c : X.functionField) / (f (ι j') * (ρ' d : X.functionField)) := by
    intro x c d j' hu
    have hf : f (ι j') ≠ 0 := left_ne_zero_of_mul (unitAt_ne_zero hu)
    rw [mul_div_mul_left _ _ hf]
  have hτ : ∀ (x : X) c d, x ∈ M.B.U c → x ∈ M'.B.U d →
      RegAt x ((ρ c : X.functionField) / (ρ' d : X.functionField)) := by
    intro x c d hc hd
    obtain ⟨-, j', hj'⟩ := hreg' x d hd
    rw [hq x c d j' hj']
    exact regAt_div_unitAt ((hreg x c hc).1 (ι j')) hj'
  refine ⟨ρ, ρ', hρ, hρ', hτ, ?_⟩
  intro σ y c d hc hd
  have hc' := mem_ptsIn.1 hc
  have hd' := mem_ptsIn.1 hd
  set τ : X.functionField := (ρ c : X.functionField) / (ρ' d : X.functionField) with hτdef
  have hτr : RegAt (under y) τ := hτ _ c d hc' hd'

  have hval : ∀ j' : J', ratVal (f (ι j') * (ρ c : X.functionField)) y =
      ratVal τ y * ratVal (f (ι j') * (ρ' d : X.functionField)) y := by
    intro j'
    have e : f (ι j') * (ρ c : X.functionField) = τ * (f (ι j') * (ρ' d : X.functionField)) := by
      rw [hτdef]; field_simp
    rw [e, ratVal_mul hτr ((hreg' _ d hd').1 j')]
  set S : ℝ := ∑ j, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) with hS
  set S' : ℝ := ∑ j', ‖ratVal (f (ι j') * (ρ' d : X.functionField)) y‖ ^ 2 * Real.exp (2 * w' j') with hS'
  have e1 : (M.φ σ).φ c y = Real.log S := hφ σ y c hc
  have e2 : ((M'.shift (fun _ => Δ) fun _ => rfl).φ σ).φ d y = Real.log S' + 2 * Δ := by
    change (M'.φ σ).φ d y + 2 * Δ = _
    rw [hφ' σ y d hd]
  have hS'pos : 0 < S' := by
    obtain ⟨-, j₀, hj₀⟩ := hreg' _ d hd'
    refine Finset.sum_pos' (fun j _ => by positivity) ⟨j₀, Finset.mem_univ _, ?_⟩
    have : ratVal (f (ι j₀) * (ρ' d : X.functionField)) y ≠ 0 := ratVal_ne_zero hj₀
    have : 0 < ‖ratVal (f (ι j₀) * (ρ' d : X.functionField)) y‖ := norm_pos_iff.2 this
    positivity
  set t : ℝ := ‖ratVal τ y‖ with ht
  have hineq : t ^ 2 * Real.exp (2 * Δ) * S' ≤ S := by
    classical
    calc t ^ 2 * Real.exp (2 * Δ) * S'
        = ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * (w' j' + Δ)) := by
          rw [hS', Finset.mul_sum]
          refine Finset.sum_congr rfl fun j' _ => ?_
          rw [hval, norm_mul, ← ht, mul_add, Real.exp_add]; ring
      _ ≤ ∑ j', ‖ratVal (f (ι j') * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w (ι j')) := by
          refine Finset.sum_le_sum fun j' _ => ?_
          gcongr
          exact hw j'
      _ = ∑ j ∈ Finset.univ.image ι, ‖ratVal (f j * (ρ c : X.functionField)) y‖ ^ 2 * Real.exp (2 * w j) :=
          by rw [Finset.sum_image (fun a _ b _ h => hι h)]
      _ ≤ S := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => by positivity
  rw [e1, e2]
  have ht0 : 0 ≤ t := norm_nonneg _
  rcases ht0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact zero_le_one
  have hSpos : 0 < S := lt_of_lt_of_le (by positivity) hineq
  have hE : Real.exp (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) ^ 2 = S' * Real.exp (2 * Δ) / S := by
    rw [← Real.exp_nat_mul]
    have : ((2 : ℕ) : ℝ) * (-(Real.log S - (Real.log S' + 2 * Δ)) / 2) = (Real.log S' + 2 * Δ) - Real.log S := by
      push_cast; ring
    rw [this, Real.exp_sub, Real.exp_add, Real.exp_log hS'pos, Real.exp_log hSpos]
  rw [← sq_le_one_iff₀ (by positivity), mul_pow, hE]
  rw [← mul_div_assoc, div_le_one hSpos]
  linarith [hineq]

end GlobalTheory.HSNef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudySubfamilyLeShiftFubiniStudyFamilyStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (M M' : HermLB p) (J J' : Type) [Fintype J] [Fintype J'] (f : J → X.functionField) (w : J → ℝ) (w' : J' → ℝ) (ι : J' → J) (Δ : ℝ), Function.Injective ι → IsFS M f w → IsFS M' (f ∘ ι) w' → (∀ j, w' j + Δ ≤ w (ι j)) → Le (M'.shift (fun _ => Δ) fun _ => rfl) M := by
  first | exact @GlobalTheory.HSNef.le_shift_of_isFS_sub | exact GlobalTheory.HSNef.le_shift_of_isFS_sub | (intros; apply GlobalTheory.HSNef.le_shift_of_isFS_sub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyMovingPartsChainBound

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem Total.comp {X : Scheme.{0}} [IsIntegral X] {J J' : Type} {f : J → X.functionField} (h : Total f)
    (ι : J' → J) : Total (f ∘ ι) :=
  ⟨fun j => h.1 (ι j), fun x j l => h.2 x (ι j) (ι l)⟩

theorem selfInter_nonneg_of_isFS (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) {k : Type} [CommRing k]
    {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {M : HermLB p} {J : Type} [Fintype J]
    {f : J → X.functionField} {w : J → ℝ} (hM : IsFS M f w) (hw : ∀ j, 0 ≤ w j) {μ : ℝ} (hμ : M.IsSelfInter μ) :
    0 ≤ μ := by
  have hnef := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M J f w hM hw
  have hht := (GlobalTheory.T.arithKleiman_heightNef_of_isNef hC hA hS k X p D hX M hnef).2
  obtain ⟨h, hh, rfl⟩ := hμ
  exact hht h hh _

theorem levels_le_selfInter (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (x : Fin D → X.functionField) (Δ : ℝ)
    (hx : AlgebraicIndependent ℤ x) (hΔ : 0 < Δ) :
    ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ),
      LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) →
      M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ∑ j, (n j : ℝ) ≤ μ := by
  intro N
  induction N with
  | zero =>
    intro J _ e n M μ _ hn _ hM hμ
    have h0 : ∀ j, n j = 0 := fun j => Nat.le_zero.1 (hn j)
    simp only [h0, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
    exact selfInter_nonneg_of_isFS hC hA hS hX hM (fun c => by simp [h0]) hμ
  | succ N ih =>
    intro J _ e n M μ he hn ht hM hμ
    classical
    have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
    by_cases hJ : ∀ j, n j = 0
    · simp only [hJ, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
      exact selfInter_nonneg_of_isFS hC hA hS hX hM hw0 hμ
    push_neg at hJ
    obtain ⟨j₀, hj₀⟩ := hJ
    let J' := {j // 1 ≤ n j}
    let e' : J' → X.functionField := fun j => e j.1
    let n' : J' → ℕ := fun j => n j.1 - 1
    let ι : J' × Finset (Fin D) → J × Finset (Fin D) := fun c => (c.1.1, c.2)
    have hι : Function.Injective ι := by
      rintro ⟨⟨a, ha⟩, s⟩ ⟨⟨b, hb⟩, t⟩ h
      simp only [ι, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hbox : boxFam e' x = boxFam e x ∘ ι := rfl
    haveI : Nonempty (J' × Finset (Fin D)) := ⟨(⟨j₀, Nat.one_le_iff_ne_zero.2 hj₀⟩, ∅)⟩
    have ht' : Total (boxFam e' x) := hbox ▸ ht.comp ι
    obtain ⟨M', hM'⟩ := GlobalTheory.T.exists_fubiniStudy_of_totallyOrdered_ratFnFamily k X p (J' × Finset (Fin D)) (boxFam e' x) (fun c => (n' c.1 : ℝ) * Δ) ht'
    obtain ⟨h', hh'⟩ := (hC.arExists k X p D hX).1 M'
    have hμ' : M'.IsSelfInter (h' (genericPoint X)) := ⟨h', hh', rfl⟩
    have he' : LinearIndependent ℤ e' := he.comp _ Subtype.val_injective
    have hn' : ∀ j, n' j ≤ N := fun j => by
      have := hn j.1
      simp only [n']
      omega
    have IH := ih J' e' n' M' _ he' hn' ht' hM' hμ'
    have hw0' : ∀ c : J' × Finset (Fin D), 0 ≤ (n' c.1 : ℝ) * Δ := fun c => by positivity
    have hstep : ∀ c : J' × Finset (Fin D), (n' c.1 : ℝ) * Δ + Δ ≤ (n (ι c).1 : ℝ) * Δ := fun c => by
      have h1 := c.1.2
      simp only [n', ι]
      rw [Nat.cast_sub h1]
      push_cast
      linarith
    have hle : Le (M'.shift (fun _ => Δ) fun _ => rfl) M :=
      GlobalTheory.T.fubiniStudy_subfamily_le_shift_fubiniStudy_family k X p M M' (J × Finset (Fin D)) (J' × Finset (Fin D)) (boxFam e x) (fun c => (n c.1 : ℝ) * Δ)
        (fun c => (n' c.1 : ℝ) * Δ) ι Δ hι hM (hbox ▸ hM') hstep
    have hnefM := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M _ _ _ hM hw0
    have hnefM' := GlobalTheory.T.fubiniStudy_bundle_isNef_of_nonneg_weights hC k X p D hX M' _ _ _ hM' hw0'
    have hnefS := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX M' Δ hΔ.le hnefM'
    have hsh := hC.arShift k X p D hX M' _ Δ hμ'
    have hmono := GlobalTheory.T.arithSelfIntersection_mono_of_isNef hC hA hS k X p D hX M _ μ _ hnefM hnefS hle hμ hsh
    have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M' J' e' x (fun c => (n' c.1 : ℝ) * Δ) he' hx hw0' hM'
    have hsum : ∑ j, (n j : ℝ) = ∑ j : J', (n' j : ℝ) + Fintype.card J' := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => 1 ≤ n j) (fun j => (n j : ℝ))]
      have h2 : ∑ j : {j // ¬ 1 ≤ n j}, (n j.1 : ℝ) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          have := j.2
          have : n j.1 = 0 := by omega
          simp [this]
      rw [h2, add_zero]
      have h3 : ∀ j : J', (n j.1 : ℝ) = (n' j : ℝ) + 1 := fun j => by
        simp only [n']
        rw [Nat.cast_sub j.2]
        ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rfl
    have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J' ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := by
      calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J' = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J') := by
            rw [hf]; ring
        _ ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := mul_le_mul_of_nonneg_left hrk (by positivity)
    rw [hsum, mul_add]
    linarith

theorem chain_moving_parts : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ), LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) → M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ μ + ((D : ℝ) + 1) * Δ * gdeg M D := by
  intro hC hA hS k _ X _ p D hX x Δ hx hΔ N J _ e n M μ he hn ht hM hμ
  have key := levels_le_selfInter hC hA hS k X p D hX x Δ hx hΔ N J e n M μ he hn ht hM hμ
  have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
  have hrk := GlobalTheory.T.rank_le_fubiniStudy_boxFamily hC hA k X p D hX M J e x (fun c => (n c.1 : ℝ) * Δ) he hx hw0 hM
  have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J ≤ ((D : ℝ) + 1) * Δ * gdeg M D := by
    calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J) := by
          rw [hf]; ring
      _ ≤ ((D : ℝ) + 1) * Δ * gdeg M D := mul_le_mul_of_nonneg_left hrk (by positivity)
  have hsum : ((∑ j, (n j + 1) : ℕ) : ℝ) = ∑ j, (n j : ℝ) + Fintype.card J := by
    push_cast
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum, mul_add]
  linarith

end GlobalTheory.HSNef
end
end
end
