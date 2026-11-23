module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Ser
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqOfIsMinInClassTwoOfSameClassFour
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReducedBasisOfLinearIndependent
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsShiftedLtClassMin

section

@[expose] public section

noncomputable section

namespace GlobalTheory.ClassMin

open QuadraticMap Module
open scoped Pointwise

section Class

variable {X : Type*} [AddCommGroup X]

variable {Q : QuadraticMap ℤ X ℝ} {N : ℤ}

theorem shifted_zsmul (hN : N ≠ 0) (ν : X →+ ℝ) (μ : X) :
    Q (N • μ) / N + ν (N • μ) = N * (Q μ + ν μ) := by
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN
  rw [QuadraticMap.map_smul, map_zsmul, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  field_simp

theorem shifted_zsmul_nonneg (hN : 0 < N) {ν : X →+ ℝ} (h : ∀ μ, 0 ≤ Q μ + ν μ) (μ : X) :
    0 ≤ Q (N • μ) / N + ν (N • μ) := by
  rw [shifted_zsmul hN.ne']
  exact mul_nonneg (by exact_mod_cast hN.le) (h μ)

theorem shifted_lt_add_zsmul {c : ℝ} (hc : 0 ≤ c) (hN : 1 + 2 * c < N) {ν : X →+ ℝ} {e μ : X}
    (hμ : 0 < Q μ) (hF : 0 ≤ Q μ / N + ν μ) (h : |polar Q e μ| ≤ c * polar Q μ μ) :
    Q e / N + ν e < Q (e + N • μ) / N + ν (e + N • μ) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have e1 : Q (e + N • μ) / N + ν (e + N • μ) = Q e / N + ν e +
      (polar Q e μ + (N - 1) * Q μ + N * (Q μ / N + ν μ)) := by
    rw [map_add_zsmul, map_add (f := _), map_zsmul, zsmul_eq_mul]
    field_simp
    ring
  rw [polar_self, two_smul, abs_le] at h
  have h1 := mul_pos (sub_pos.2 hN) hμ
  have h2 := mul_nonneg hN0.le hF
  rw [e1]
  nlinarith [h.1]

theorem exists_basis_neg {ι : Type*} (e : Basis ι ℤ X) {ν : X →+ ℝ} (hν : ν ≠ 0) :
    ∃ i, ν (e i) < 0 ∨ ν (-e i) < 0 := by
  by_contra h
  push Not at h
  refine hν (AddMonoidHom.toIntLinearMap_injective (e.ext fun i => ?_))
  have h2 := (h i).2
  rw [map_neg] at h2
  simpa using le_antisymm (by linarith) (h i).1

theorem realExtension_eq_realExt (Q : QuadraticMap ℤ X ℝ) : realExtension Q = realExt Q :=
  eq_realExt Q _ (realExtension_one_tmul Q)

end Class

section Main

variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ} {N : ℤ} {d : ℕ}

theorem exists_shifted_lt (hd : finrank ℤ X = d) (hQ : (realExt Q).PosDef)
    (hN : 1 + 2 * d * (2 : ℝ) ^ ((d : ℝ) / 2) < N) {ν : X →+ ℝ} (hν : ν ≠ 0)
    (h : ∀ μ, 0 ≤ Q μ + ν μ) :
    ∃ α : X, (∀ w, α ≠ N • w) ∧
      (∀ w, w ≠ 0 → Q α / N + ν α < Q (α + N • w) / N + ν (α + N • w)) ∧
      ∀ w, Q α / N + ν α < Q (α + N • w) / N := by
  have hP := posDef_of_posDef_realExt hQ
  have hc : (0 : ℝ) ≤ d * (2 : ℝ) ^ ((d : ℝ) / 2) := by positivity
  rw [mul_assoc] at hN
  have hN1 : (1 : ℝ) < N := by linarith
  have hN2 : 2 ≤ N := by
    have : (1 : ℤ) < N := by exact_mod_cast hN1
    omega
  have hN0 : (0 : ℝ) < N := by linarith
  suffices H : ∃ α : X, (∀ w, w ≠ 0 → Q α / N + ν α < Q (α + N • w) / N + ν (α + N • w)) ∧
      ∀ w, Q α / N + ν α < Q (α + N • w) / N by
    obtain ⟨α, h1, h2⟩ := H
    refine ⟨α, ?_, h1, h2⟩
    rintro w rfl
    have h3 := h2 (-w)
    rw [smul_neg, add_neg_cancel, map_zero, zero_div] at h3
    exact h3.not_ge (shifted_zsmul_nonneg (by omega) h w)
  obtain ⟨a, ha⟩ := exists_global_min (realExtension_eq_realExt Q ▸ hQ) ν hN0
  by_cases hX : ∃ u, a = N • u
  · obtain ⟨u, rfl⟩ := hX
    have hF : ∀ x, 0 ≤ Q x / N + ν x := fun x => (shifted_zsmul_nonneg (by omega) h u).trans (ha x)
    obtain ⟨e, he, -⟩ := exists_reduced_basis_pairing_coord hd Q hQ
    obtain ⟨v, hv, hvp⟩ : ∃ v, ν v < 0 ∧
        ∀ μ, |polar Q v μ| ≤ d * (2 : ℝ) ^ ((d : ℝ) / 2) * polar Q μ μ := by
      obtain ⟨i, hi | hi⟩ := exists_basis_neg e hν
      · exact ⟨_, hi, he i⟩
      · exact ⟨_, hi, fun μ => by rw [polar_neg_left, abs_neg]; exact he i μ⟩
    refine ⟨v, fun w hw => shifted_lt_add_zsmul hc hN (hP w hw) (hF w) (hvp w), fun w => ?_⟩
    refine (add_lt_of_neg_right _ hv).trans_le (div_le_div_of_nonneg_right ?_ hN0.le)
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · exact (lt_add_smul_of_abs_polar_le Q hc (by linarith) (hP w hw) (hvp w)).1.le
  · refine ⟨a, fun w => lt_of_global_min hP ν hN2 ha, fun w => ?_⟩
    have h0 := ha 0
    rw [map_zero, map_zero, zero_div, add_zero] at h0
    refine h0.trans_lt (div_pos (hP _ fun hw => hX ⟨-w, ?_⟩) hN0)
    rw [smul_neg, eq_neg_iff_add_eq_zero, hw]

theorem exists_shifted_lt_of_le {g : ℕ} (hg : finrank ℤ X ≤ g) (hQ : (realExt Q).PosDef)
    (hN : 1 + 2 * g * (2 : ℝ) ^ ((g : ℝ) / 2) < N) {ν : X →+ ℝ} (hν : ν ≠ 0)
    (h : ∀ μ, 0 ≤ Q μ + ν μ) :
    ∃ α : X, (∀ w, α ≠ N • w) ∧
      (∀ w, w ≠ 0 → Q α / N + ν α < Q (α + N • w) / N + ν (α + N • w)) ∧
      ∀ w, Q α / N + ν α < Q (α + N • w) / N := by
  refine exists_shifted_lt rfl hQ (lt_of_le_of_lt ?_ hN) hν h
  have := pairing_const_mono hg
  rw [mul_assoc, mul_assoc]
  linarith

end Main

section Matrix

open ReciprocityTheory.ReducedBases (SameClass IsMinInClass IsUniqueMinInClass)

end Matrix

end GlobalTheory.ClassMin

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationEqPolarFormOfWeightZeroMax

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ValLat

theorem norm_le_of_hasSum {I C : Type} [NormedAddCommGroup C] [IsUltrametricDist C] {f : I → C} {a : C}
    (h : HasSum f a) {r : ℝ} (hr : 0 ≤ r) (hf : ∀ x, ‖f x‖ ≤ r) : ‖a‖ ≤ r := by
  rw [← h.tsum_eq]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr hf

theorem le_norm_of_hasSum {I C : Type} [NormedAddCommGroup C] [IsUltrametricDist C] {f : I → C} {a : C}
    (h : HasSum f a) {b : I} (hf : ∀ x, x ≠ b → ‖f x‖ < ‖f b‖) : ‖f b‖ ≤ ‖a‖ := by
  rcases (norm_nonneg (f b)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  obtain ⟨r, hr0, hrb, hr⟩ : ∃ r, 0 ≤ r ∧ r < ‖f b‖ ∧ ∀ x, x ≠ b → ‖f x‖ ≤ r := by
    have ht := (tendsto_zero_iff_norm_tendsto_zero.1 h.summable.tendsto_cofinite_zero).eventually
      (gt_mem_nhds (half_pos h0))
    have hfin : {x | x ≠ b ∧ ‖f b‖ / 2 ≤ ‖f x‖}.Finite :=
      (Filter.eventually_cofinite.1 ht).subset fun x hx => not_lt.2 hx.2
    rcases Set.eq_empty_or_nonempty {x | x ≠ b ∧ ‖f b‖ / 2 ≤ ‖f x‖} with he | he
    · refine ⟨‖f b‖ / 2, by positivity, half_lt_self h0, fun x hx => ?_⟩
      by_contra hc
      exact (Set.eq_empty_iff_forall_notMem.1 he x) ⟨hx, (not_le.1 hc).le⟩
    · obtain ⟨y, hy, hm⟩ := Set.exists_max_image _ (fun x => ‖f x‖) hfin he
      refine ⟨‖f y‖, norm_nonneg _, hf y hy.1, fun x hx => ?_⟩
      by_cases hc : ‖f b‖ / 2 ≤ ‖f x‖
      · exact hm x ⟨hx, hc⟩
      · exact (not_le.1 hc).le.trans hy.2
  have h1 := norm_le_of_hasSum (h.update b 0) hr0 fun x => by
    rcases eq_or_ne x b with rfl | hx
    · simpa using hr0
    · rw [Function.update_of_ne hx]; exact hr x hx
  by_contra hc
  have h2 := IsUltrametricDist.norm_add_le_max a (-(0 - f b + a))
  rw [norm_neg, show a + -(0 - f b + a) = f b by abel] at h2
  exact h2.not_gt (max_lt (not_le.1 hc) (h1.trans_lt hrb))

theorem main : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ) (g N : ℕ) (J : Type) (cls : J → X) (p : ℕ) [Fact p.Prime] (w : J → PadicAlgCl p) (ν : X →+ ℝ), Filter.Tendsto q Filter.cofinite Filter.atTop → Module.finrank ℤ X ≤ g → 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N → (∀ i, Short q N (cls i)) → Ser q N cls w ν → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ m, ∀ α, ν α = QuadraticMap.polar q m α := by
  intro X _ _ _ q g N J cls p _ w ν hq hg hN _ ⟨t, κ, hκ, hsum, hcls, hsz⟩ ⟨i₀, hi₀, hmax⟩
  have hQ := GlobalTheory.posDef_realExt_of_tendsto q hq
  have hN0 : (0 : ℝ) < N := lt_trans (by positivity) hN
  obtain ⟨m, hm⟩ := ClassMin.exists_global_min (ClassMin.realExtension_eq_realExt q ▸ hQ) ν one_pos
  simp only [div_one] at hm
  let ν' : X →+ ℝ := ν + (QuadraticMap.polarBilin q m).toAddMonoidHom
  have hν' : ∀ x, ν' x = ν x + QuadraticMap.polar q m x := fun x => rfl
  by_cases h0 : ν' = 0
  · refine ⟨-m, fun α => ?_⟩
    have := hν' α
    rw [h0] at this
    rw [QuadraticMap.polar_neg_left]
    simp only [AddMonoidHom.zero_apply] at this
    linarith
  exfalso
  obtain ⟨α, -, h1, h2⟩ := ClassMin.exists_shifted_lt_of_le (N := (N : ℤ)) hg hQ (by exact_mod_cast hN) h0
    fun y => by
      have := hm (m + y)
      rw [map_add ν] at this
      rw [hν', QuadraticMap.polar]
      linarith
  simp only [natCast_zsmul, Int.cast_natCast] at h1 h2
  have hshift : ∀ x, q (x + N • m) / N + ν (x + N • m) = q x / N + ν' x + N * (q m + ν m) := fun x => by
    have e := ClassMin.map_add_zsmul q x m (N : ℤ)
    rw [natCast_zsmul] at e
    rw [e, hν', map_add (f := _), map_nsmul, nsmul_eq_mul, QuadraticMap.polar_comm q m x]
    push_cast
    field_simp
    ring
  obtain ⟨i, hi⟩ := (hsz (α + N • m)).2
  obtain ⟨u, hu⟩ := hcls (α + N • m) i (by
    rw [← norm_pos_iff, hi]; positivity)
  have hA : ‖t (α + N • m) i‖ ≤ ‖w i‖ := le_norm_of_hasSum (f := fun x => t x i) (hsum i) fun x hx => by
    by_cases hz : t x i = 0
    · rw [hz, norm_zero, hi]; positivity
    obtain ⟨v, hv⟩ := hcls x i hz
    have e : x = α + N • (v - u) + N • m := by
      rw [hv, add_right_comm, hu, smul_sub]; abel
    have h3 := h1 (v - u) fun h => hx (by rw [e, h, smul_zero, add_zero])
    refine ((hsz x).1 i).trans_lt ?_
    rw [hi]
    refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) hκ
    have e1 := hshift (α + N • (v - u))
    rw [← e] at e1
    have e2 := hshift α
    rw [sub_div, sub_div]
    linarith
  have hB : ‖w i₀‖ ≤ κ * Real.exp (-(N * (q m + ν m))) := norm_le_of_hasSum (hsum i₀) (by positivity) fun x => by
    by_cases hz : t x i₀ = 0
    · rw [hz, norm_zero]; positivity
    obtain ⟨v, hv⟩ := hcls x i₀ hz
    refine ((hsz x).1 i₀).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hκ.le)
    have e := ClassMin.shifted_zsmul (Q := q) (N := (N : ℤ)) (by exact_mod_cast hN0.ne') ν v
    simp only [natCast_zsmul, Int.cast_natCast] at e
    rw [hv, hi₀, zero_add, map_zero, sub_zero, e]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (hm v) hN0.le)
  have hC := (hA.trans (hmax i)).trans hB
  rw [hi] at hC
  have hD := Real.exp_le_exp.1 (le_of_mul_le_mul_left hC hκ)
  have h3 := h2 (m - u)
  have e : α + N • (m - u) = cls i := by
    rw [smul_sub, ← add_sub_assoc, hu]; abel
  rw [e] at h3
  have e2 := hshift α
  rw [sub_div] at hD
  linarith

end GlobalTheory.ZH.ValLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationEqPolarFormOfWeightZeroMaxStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.valuation_eq_polarForm_of_weightZero_max : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ) (g N : ℕ) (J : Type) (cls : J → X) (p : ℕ) [Fact p.Prime] (w : J → PadicAlgCl p) (ν : X →+ ℝ), Filter.Tendsto q Filter.cofinite Filter.atTop → Module.finrank ℤ X ≤ g → 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N → (∀ i, Short q N (cls i)) → Ser q N cls w ν → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ m, ∀ α, ν α = QuadraticMap.polar q m α := by
  first | exact @GlobalTheory.ZH.ValLat.main | exact GlobalTheory.ZH.ValLat.main | (intros; apply GlobalTheory.ZH.ValLat.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegralOfWeightZeroCoordinateDominates

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

theorem Mod.integral_of_weight_zero_dominates : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (a : Sp (PadicAlgCl p) ⟶ G.left) (w : J → PadicAlgCl p), a ≫ G.hom = gPt p ≫ spMap j → Crd H σ a w → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ c : Sp (OO p) ⟶ G.left, c ≫ G.hom = spMap j ∧ gPt p ≫ c = a := by
  intro p _ V _ j G _ g N N' X _ q H J _ σ cls m hB a w ha hw hi
  obtain ⟨ν, hν, hc⟩ := m.ser a ha w hw
  apply hc
  let e : m.Φ.E.X ≃ₗ[ℤ] X := m.xe.toIntLinearEquiv
  have : Module.Free ℤ X := Module.Free.of_equiv e
  have : Module.Finite ℤ X := Module.Finite.equiv e
  have hq : ∀ x : X, (q.comp m.xe.toIntLinearEquiv.toLinearMap) (m.xe.symm x) = q x := by
    intro x
    rw [QuadraticMap.comp_apply]
    exact congrArg q (m.xe.apply_symm_apply x)
  refine GlobalTheory.T.valuation_eq_polarForm_of_weightZero_max X q g N J cls p w ν ?_ ?_ hB.lll ?_ hν hi
  · have h := m.good.pos.comp (m.xe.symm.injective.tendsto_cofinite)
    exact h.congr hq
  · exact e.finrank_eq.symm.le.trans ((Nat.le_add_left _ _).trans m.dim.le)
  · intro i n
    have h := m.good.short i (m.xe.symm n)
    rw [← map_nsmul, ← map_add (f := _), hq, hq] at h
    exact h

end GlobalTheory.ZH
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegralOfWeightZeroCoordinateDominatesStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.isIntegral_of_weightZeroCoordinate_dominates : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] (j : V →+* OO p) (G : Over (Sp V)) [GrpObj G] (g N N' : ℕ) (X : Type) [AddCommGroup X] (q : QuadraticMap ℤ X ℝ) (H : LB G.left) (J : Type) [Fintype J] (σ : J → H.Sec) (cls : J → X) (m : Mod p j G g N q H σ cls), Big g N N' → ∀ (a : Sp (PadicAlgCl p) ⟶ G.left) (w : J → PadicAlgCl p), a ≫ G.hom = gPt p ≫ spMap j → Crd H σ a w → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ c : Sp (OO p) ⟶ G.left, c ≫ G.hom = spMap j ∧ gPt p ≫ c = a := by
  first | exact @GlobalTheory.ZH.Mod.integral_of_weight_zero_dominates | exact GlobalTheory.ZH.Mod.integral_of_weight_zero_dominates | (intros; apply GlobalTheory.ZH.Mod.integral_of_weight_zero_dominates <;> assumption)
end
end
