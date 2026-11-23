module

public import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightSubstNonneg
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CoeffLeafGaugeSubMainTermEqZeroOnFirstAxisStatement
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuation
public import Mathlib.Data.Nat.Factorization.Basic
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HPullWUpGTwoGroupEmbeddingEqRenameStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearSubstCoordinateWeightNonnegRadiusStatement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PderivLeafGaugeEqPairingAddIntegralStatement
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FactorizationLeFourFifteenths

section

@[expose] public section

open ReciprocityTheory.PGsh

namespace GlobalTheory

theorem factorization_le_four_fifteenths {l B : ℕ} (hl : 5 ≤ l) (hB : B ≠ 0) :
    (B.factorization l : ℝ) ≤ 4 / 15 * (B : ℝ) := by
  have h1 : l ^ B.factorization l ≤ B := Nat.ordProj_le l hB
  have h2 : 5 ^ B.factorization l ≤ l ^ B.factorization l := Nat.pow_le_pow_left hl _
  have h3 : ∀ k : ℕ, 4 * k + 1 ≤ 5 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ]; omega
  have h4 : 4 * B.factorization l + 1 ≤ B := le_trans (h3 _) (le_trans h2 h1)
  have h5 : (4 : ℝ) * (B.factorization l : ℝ) + 1 ≤ B := by exact_mod_cast h4
  have h6 : (0 : ℝ) ≤ (B.factorization l : ℝ) := Nat.cast_nonneg _
  linarith

theorem four_fifteenths_le_slope_gap {x : ℝ} (hx : 5 ≤ x) {i : ℕ} (hi : 1 ≤ i) :
    4 / 15 ≤ (1 / (x ^ 2 - 1) + 1 / 2 - 1 / (8 * x ^ i)) - 1 / (x - 1) := by
  have h1 : x ≤ x ^ i := by
    simpa using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ x) hi
  have h2 : 1 / (8 * x ^ i) ≤ 1 / 40 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hp : 0 < x ^ 2 - 1 := by nlinarith
  have hq : 0 < x - 1 := by linarith
  have h3 : 1 / (x - 1) - 1 / (x ^ 2 - 1) = x / (x ^ 2 - 1) := by
    have : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
    rw [this]
    have hr : 0 < x + 1 := by linarith
    field_simp
    ring
  have h4 : x / (x ^ 2 - 1) ≤ 5 / 24 := by
    rw [div_le_div_iff₀ hp (by norm_num)]
    nlinarith
  linarith

theorem weight_of_weight_pderiv :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → 5 ≤ l → ∀ (i : ℕ) (κ κ' : Type) [Fintype κ] [Fintype κ'] [DecidableEq κ] [DecidableEq κ'] (h₁ : MvPowerSeries (κ ⊕ κ') C), 1 ≤ i →
    (∀ α, MvPowerSeries.coeff α h₁ ≠ 0 → ∃ q, α (Sum.inr q) ≠ 0) → (∀ b, (∀ α, (((0) - α.sum (fun j e => Sum.elim (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)) (fun _ => 1 / ((l : ℝ) - 1)) j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (MvPowerSeries.pderiv (R := C) (Sum.inr b) h₁)))) →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => Sum.elim (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i)) (fun _ => 1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h₁)))) := by
  intro C _ _ v l hl hv h5 i κ κ' _ _ _ _ h₁ hi hsupp hder α
  by_cases h0 : MvPowerSeries.coeff α h₁ = 0
  · rw [h0, v.map_zero]; exact le_top
  obtain ⟨b, hb⟩ := hsupp α h0
  obtain ⟨β, rfl⟩ : ∃ β : κ ⊕ κ' →₀ ℕ, α = β + Finsupp.single (Sum.inr b) 1 := by
    refine ⟨α - Finsupp.single (Sum.inr b) 1, ?_⟩
    rw [tsub_add_cancel_of_le]
    exact Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hb)
  have h := hder b β
  have hc : ((β (Sum.inr b) : C) + 1) = ((β (Sum.inr b) + 1 : ℕ) : C) := by push_cast; rfl
  rw [MvPowerSeries.coeff_pderiv, hc, v.map_mul,
    ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hl hv (Nat.succ_ne_zero _)] at h
  have hf := factorization_le_four_fifteenths h5 (Nat.succ_ne_zero (β (Sum.inr b)))
  have hg := four_fifteenths_le_slope_gap (x := (l : ℝ)) (by exact_mod_cast h5) hi
  generalize v (MvPowerSeries.coeff (β + Finsupp.single (Sum.inr b) 1) h₁) = w at h ⊢
  induction w using WithTop.recTopCoe with
  | top => exact le_top
  | coe w =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h
    rw [WithTop.coe_le_coe]
    rw [Finsupp.sum_add_index' (by intro j; simp) (by intro j e e'; push_cast; ring),
      Finsupp.sum_single_index (by simp)]
    rw [Finsupp.sum_fintype _ _ (by intro j; simp), Fintype.sum_sum_type] at h ⊢
    simp only [Sum.elim_inl, Sum.elim_inr, ← Finset.mul_sum] at h ⊢
    have hJ : (β (Sum.inr b) : ℝ) ≤ ∑ q, (β (Sum.inr q) : ℝ) :=
      Finset.single_le_sum (f := fun q => (β (Sum.inr q) : ℝ))
        (fun q _ => Nat.cast_nonneg _) (Finset.mem_univ b)
    have hJ0 : (0 : ℝ) ≤ β (Sum.inr b) := Nat.cast_nonneg _
    push_cast at hf ⊢
    generalize (∑ q, (β (Sum.inr q) : ℝ)) = J at h hJ ⊢
    generalize (1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i)) = c' at hg ⊢
    generalize 1 / ((l : ℝ) - 1) = c at h hg ⊢
    have hm : 4 / 15 * (J + 1) ≤ (c' - c) * (J + 1) :=
      mul_le_mul_of_nonneg_right hg (by linarith)
    nlinarith

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightGaugeSubMainTermLeaf

section

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTermWeight

open GlobalTheory.WeightSubst

variable {C : Type} [Field C]

theorem wtNonneg_rename (v : AddValuation C (WithTop ℝ)) {σ τ : Type} [Finite σ] (f : σ ↪ τ) (ρ : τ → ℝ)
    (r : ℝ) (hr : ∀ s, ρ (f s) = r) (F : MvPowerSeries σ C)
    (hF : ∀ μ : σ →₀ ℕ, ((-((μ.degree : ℝ) * r) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff μ F)) :
    WtNonneg v ρ (MvPowerSeries.rename f F) := by
  intro α
  by_cases h : α ∈ Set.range (Finsupp.mapDomain f)
  · obtain ⟨μ, rfl⟩ := h
    rw [← Finsupp.embDomain_eq_mapDomain, MvPowerSeries.coeff_embDomain_rename, Finsupp.sum_embDomain]
    convert hF μ using 2
    simp only [hr, Finsupp.sum, Finsupp.degree_apply]
    push_cast
    rw [Finset.sum_mul, zero_sub]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · rw [MvPowerSeries.coeff_rename_eq_zero _ _ h]
    simp

theorem wtNonneg_add (v : AddValuation C (WithTop ℝ)) {τ : Type} (ρ : τ → ℝ) {F G : MvPowerSeries τ C}
    (hF : WtNonneg v ρ F) (hG : WtNonneg v ρ G) : WtNonneg v ρ (F + G) := by
  intro α
  rw [map_add (f := _)]
  exact v.map_le_add (hF α) (hG α)

theorem wtNonneg_sum (v : AddValuation C (WithTop ℝ)) {τ ι : Type} (ρ : τ → ℝ) (s : Finset ι)
    {F : ι → MvPowerSeries τ C} (hF : ∀ i ∈ s, WtNonneg v ρ (F i)) : WtNonneg v ρ (∑ i ∈ s, F i) := by
  intro α

  rw [map_sum]
  exact v.map_le_sum fun i hi => hF i hi α

theorem wtNonneg_smul (V : VF C) {τ : Type} (ρ : τ → ℝ) {c : C} (hc : V.Ge 0 c) {F : MvPowerSeries τ C}
    (hF : WtNonneg V.v ρ F) : WtNonneg V.v ρ (c • F) := by
  intro α
  rw [map_smul, smul_eq_mul]
  exact VF.Ge.mul_int hc (hF α)

theorem le_add_coe_iff (x : WithTop ℝ) (w r : ℝ) :
    (w : WithTop ℝ) ≤ x + (r : WithTop ℝ) ↔ ((w - r : ℝ) : WithTop ℝ) ≤ x := by
  induction x using WithTop.recTopCoe with
  | top => simp
  | coe t =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe, WithTop.coe_le_coe]
    exact sub_le_iff_le_add.symm

theorem radius_one (l i : ℕ) (hl : l ≠ 0) :
    r1 l i - del l i = 1 / ((l : ℝ) ^ 2 - 1) + 3 / (8 * (l : ℝ) ^ i) := by
  have : (l : ℝ) ≠ 0 := by exact_mod_cast hl
  unfold r1 del rho
  have h : 1 / (2 * (l : ℝ) ^ i) - 1 / (8 * (l : ℝ) ^ i) = 3 / (8 * (l : ℝ) ^ i) := by
    field_simp
    ring
  linarith

theorem radius_two (l i : ℕ) :
    r2 l - del l i = 1 / ((l : ℝ) ^ 2 - 1) + 1 / 2 - 1 / (8 * (l : ℝ) ^ i) := by
  unfold r2 del rho
  rfl

theorem constantCoeff_linPull {σ ι : Type} [Fintype σ] [Fintype ι] (e : ι → σ → C) (F : MvPowerSeries σ C)
    (hF : MvPowerSeries.constantCoeff F = 0) : MvPowerSeries.constantCoeff (linPull e F) = 0 := by
  have h0 : ∀ x : σ, MvPowerSeries.constantCoeff
      (∑ c : ι, e c x • (MvPowerSeries.X c : MvPowerSeries ι C)) = 0 := by
    intro x

    simp [map_sum]
  exact MvPowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.hasSubst_of_constantCoeff_zero h0) h0 hF

theorem pderiv_mainM (V : VF C) (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι'] (Φ : ι' → ι → C) (b : ι') :
    MvPowerSeries.pderiv (R := C) (Sum.inr b) (mainM V i Φ) =
      ((V.l : C) ^ expE V.l i)⁻¹ • ∑ c : ι,
        Φ b c • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C) ^ (V.l ^ i) := by
  unfold mainM

  rw [Derivation.map_smul, map_sum, Finset.sum_eq_single b]

  · rw [map_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X]
  · intro b' _ hb

    rw [map_sum]
    refine Finset.sum_eq_zero fun c _ => ?_
    simp [Derivation.leibniz, Derivation.leibniz_pow, MvPowerSeries.pderiv_X, hb]
  · simp

theorem weight_gauge_sub_main : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 5 ≤ V.l → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N M : ℕ) (e : Fin N → I g → C) (v' : Fin M → I (1 - g) → C) (Φt : Fin N → J g → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → (∀ c, WtGe1 V i 0 (linPull e (t g c))) → (∀ κ : J g, (X.G g).ty (Sum.inr κ) = a + (i : ZMod d) → WtGe1 V i 0 (linPull e ((S g).ze (t g) κ) - ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, Φt δ κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i))) → WtGe2 V i (1 / ((V.l : ℝ) - 1)) (X.hM g a i e v' - mainM V i (fun b c => ∑ κ : J g, ∑ k : I (1 - g), Φt c κ * X.pair g κ k * v' b k)) := by
  intro C _ V d _ I J _ _ X hA hl g a i hi hid S t ht N M e v' Φt he hv hv' hT hZ
  haveI := X.charZero
  have hl0 : V.l ≠ 0 := V.l_prime.ne_zero
  have hpull := GlobalTheory.T.hPullW_upG_twoGroupEmbedding_eq_rename C I g (Fin N) (Fin M) e v'
  have key := GlobalTheory.weight_of_weight_pderiv C V.v V.l V.l_prime V.v_l hl i (Fin N) (Fin M)
    (X.hM g a i e v' - mainM V i (fun b c => ∑ κ : J g, ∑ k : I (1 - g), Φt c κ * X.pair g κ k * v' b k))
    hi.pos ?_ ?_
  · intro μ
    rw [le_add_coe_iff]
    convert key μ using 3
    rw [Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sum_type, radius_one _ _ hl0, radius_two]
    simp only [Sum.elim_inl, Sum.elim_inr]
    push_cast
    rw [Finset.sum_mul, Finset.sum_mul]
    congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  · intro α hα
    by_contra hn
    push Not at hn
    exact hα (GlobalTheory.T.coeff_leafGauge_sub_mainTerm_eq_zero_on_first_axis C V d I J X g a i _ _ e v' _ α hn)
  · intro b
    set ρ : Fin N ⊕ Fin M → ℝ := Sum.elim (fun _ => 1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i))
      (fun _ => 1 / ((V.l : ℝ) - 1)) with hρ
    have hinl : ∀ F : MvPowerSeries (Fin N) C, WtGe1 V i 0 F →
        WtNonneg V.v ρ (MvPowerSeries.rename (Sum.inl : Fin N → Fin N ⊕ Fin M) F) := by
      intro F hF
      refine wtNonneg_rename V.v Function.Embedding.inl ρ
        (1 / ((V.l : ℝ) ^ 2 - 1) + 3 / (8 * (V.l : ℝ) ^ i)) (fun _ => rfl) F fun μ => ?_
      have := hF μ
      rw [le_add_coe_iff, radius_one _ _ hl0, zero_sub] at this
      exact this
    obtain ⟨γ, hγ, hd⟩ := GlobalTheory.T.pderiv_leafGauge_eq_pairing_add_integral C V d I J X hA g a i hi hid S t ht (Fin N) (Fin M) e v' he hv hv' b
    have hE : MvPowerSeries.pderiv (R := C) (Sum.inr b)
        (X.hM g a i e v' - mainM V i (fun b c => ∑ κ : J g, ∑ k : I (1 - g), Φt c κ * X.pair g κ k * v' b k)) =
        MvPowerSeries.subst (fun w : WV I => hPullW (upG w.1 (t w.1 w.2)) (fun c => toW g (e c))
          (fun b => toW (1 - g) (v' b))) γ + ∑ κ : J g, (∑ k, X.pair g κ k * v' b k) •
          MvPowerSeries.rename (Sum.inl : Fin N → Fin N ⊕ Fin M) (linPull e ((S g).ze (t g) κ) -
            ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N,
              Φt δ κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i)) := by
      rw [map_sub, hd, pderiv_mainM, add_sub_assoc]
      congr 1

      simp only [hpull.1, map_sub, smul_sub, Finset.sum_sub_distrib, map_smul, map_sum, map_pow,
      MvPowerSeries.rename_X]
      congr 1
      simp only [Finset.smul_sum, smul_smul]
      conv_rhs => rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [← Finset.sum_smul, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    change WtNonneg V.v ρ _
    rw [hE]
    have hw : ∀ g' : Fin 2, g' = g ∨ g' = 1 - g := by
      have : ∀ g g' : Fin 2, g' = g ∨ g' = 1 - g := by decide
      exact this g
    refine wtNonneg_add _ _ ?_ (wtNonneg_sum _ _ _ fun κ _ => ?_)
    · refine weight_subst_nonneg C V.v _ _ ρ γ _ hγ ?_ ?_
      · rintro ⟨g', x⟩
        rcases hw g' with rfl | rfl
        · simp only [hpull.1, MvPowerSeries.constantCoeff_rename]
          exact constantCoeff_linPull _ _ ((ht _).1 x)
        · simp only [hpull.2, MvPowerSeries.constantCoeff_rename]
          exact constantCoeff_linPull _ _ ((ht _).1 x)
      · rintro ⟨g', x⟩
        rcases hw g' with rfl | rfl
        · simp only [hpull.1]
          exact hinl _ (hT x)
        · simp only [hpull.2]
          refine wtNonneg_rename V.v Function.Embedding.inr ρ (1 / ((V.l : ℝ) - 1)) (fun _ => rfl) _ fun μ => ?_
          have := GlobalTheory.T.linearSubst_coordinate_weight_nonneg_radius C V d _ _ (X.G (1 - g)) (S _) (t _) (ht _) M v' hv x μ
          unfold VF.Ge at this
          rw [mul_one_div]
          exact this
    · by_cases hκ : (X.G g).ty (Sum.inr κ) = a + (i : ZMod d)
      · exact wtNonneg_smul V ρ (VF.Ge.sum fun k _ => (X.pair_int g κ k).mul_int (hv b k))
          (hinl _ (hZ κ hκ))
      · have : ∑ k, X.pair g κ k * v' b k = 0 := by
          refine Finset.sum_eq_zero fun k _ => ?_
          by_cases hk : (X.G (1 - g)).ty (Sum.inl k) = a + (i : ZMod d)
          · rw [X.pair_type g κ k (by rw [hk]; exact hκ), zero_mul]
          · rw [hv' b k hk, mul_zero]
        rw [this, zero_smul]
        intro α
        simp

end GlobalTheory.MainTermWeight
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightGaugeSubMainTermLeafStatement

section

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

theorem _root_.GlobalTheory.T.weight_gauge_sub_mainTerm_leaf : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J), X.Alt → 5 ≤ V.l → ∀ (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → ∀ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) → ∀ (N M : ℕ) (e : Fin N → I g → C) (v' : Fin M → I (1 - g) → C) (Φt : Fin N → J g → C), (∀ c x, (X.G g).ty (Sum.inl x) ≠ a → e c x = 0) → (∀ b k, V.Ge 0 (v' b k)) → (∀ b k, (X.G (1 - g)).ty (Sum.inl k) ≠ a + (i : ZMod d) → v' b k = 0) → (∀ c, WtGe1 V i 0 (linPull e (t g c))) → (∀ κ : J g, (X.G g).ty (Sum.inr κ) = a + (i : ZMod d) → WtGe1 V i 0 (linPull e ((S g).ze (t g) κ) - ((V.l : C) ^ expE V.l i)⁻¹ • ∑ δ : Fin N, Φt δ κ • (MvPowerSeries.X δ : MvPowerSeries (Fin N) C) ^ (V.l ^ i))) → WtGe2 V i (1 / ((V.l : ℝ) - 1)) (X.hM g a i e v' - mainM V i (fun b c => ∑ κ : J g, ∑ k : I (1 - g), Φt c κ * X.pair g κ k * v' b k)) := by
  first | exact @GlobalTheory.MainTermWeight.weight_gauge_sub_main | exact GlobalTheory.MainTermWeight.weight_gauge_sub_main | (intros; apply GlobalTheory.MainTermWeight.weight_gauge_sub_main <;> assumption)
end
end
