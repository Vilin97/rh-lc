module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.ThStmt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Additive.CauchyDavenport
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideQuadraticFormIdentity
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometryOfNumbersLatticeEstimate
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianSpaceMomentIdentity
import Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.MomentBoundOfPointwiseMoments

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.GeometricSideComparison

section

@[expose] public section

open UpperTheory.V.Lit.Geo


theorem UpperTheory.geometric_side_comparison :
    MeanLow := by
  unfold MeanLow
  refine ⟨Real.exp (-Real.pi) / 16, by positivity, ?_⟩
  intro A V _ _ _ φ hinj hS hT h2
  classical
  haveI : IsAddTorsionFree V := by
    constructor
    intro n hn x y _ hxy
    have h : ((n : ℝ)) • x = ((n : ℝ)) • y := by simpa [Nat.cast_smul_eq_nsmul] using hxy
    exact smul_right_injective V (Nat.cast_ne_zero.mpr hn) h
  have hfin : {x : A | ‖φ x‖ < 1}.Finite := by
    have h := hS.tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos (-Real.pi)))
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    intro x (hx : ‖φ x‖ < 1)
    simp only [Set.mem_setOf_eq, not_lt]
    apply Real.exp_le_exp.mpr
    have ha2 : ‖φ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (φ x)]
    nlinarith [Real.pi_pos]
  have hfin2 : {x : A | ‖φ x‖ < 1 / 2}.Finite :=
    hfin.subset (fun x (hx : ‖φ x‖ < 1 / 2) => show ‖φ x‖ < 1 by linarith)
  set H := hfin.toFinset with hH
  set F := hfin2.toFinset with hF
  have hFH : F ⊆ H := by
    intro x hx
    simp only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx ⊢
    linarith
  have hcd : 2 * F.card - 1 ≤ H.card := by
    have h0 : (0 : A) ∈ F := by
      simp only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, map_zero, norm_zero]
      norm_num
    have hne : (F.image φ).Nonempty := ⟨φ 0, Finset.mem_image_of_mem _ h0⟩
    have hcdv := cauchy_davenport_of_isAddTorsionFree hne hne
    have hcard : (F.image φ).card = F.card := Finset.card_image_of_injective _ hinj
    open scoped Pointwise in
    have hsub : F.image φ + F.image φ ⊆ H.image φ := by
      intro v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp hv
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      refine Finset.mem_image.mpr ⟨x + y, ?_, map_add φ x y⟩
      simp only [hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hx hy ⊢
      rw [map_add (f := _)]
      calc ‖φ x + φ y‖ ≤ ‖φ x‖ + ‖φ y‖ := norm_add_le _ _
        _ < 1 := by linarith
    have hle := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ hinj] at hle
    rw [hcard] at hcdv
    omega
  have hsd := Finset.card_sdiff_add_card_eq_card hFH
  have hreal : (F.card : ℝ) ≤ ((H \ F).card : ℝ) + 1 := by
    have : F.card ≤ (H \ F).card + 1 := by omega
    exact_mod_cast this
  have hT2 : ((H \ F).card : ℝ) * (Real.exp (-Real.pi) / 4) ≤
      ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
    refine le_trans ?_ (hT.sum_le_tsum (H \ F) (fun x _ => by positivity))
    have hpt : ∀ x ∈ H \ F, Real.exp (-Real.pi) / 4 ≤ ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) := by
      intro x hx
      simp only [Finset.mem_sdiff, hF, hH, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx
      obtain ⟨h1, h3⟩ := hx
      have ha2 : ‖φ x‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (φ x)]
      have e1 : Real.exp (-Real.pi) ≤ Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
      have e2 : (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2 := by nlinarith
      have := Real.exp_pos (-Real.pi)
      nlinarith
    calc ((H \ F).card : ℝ) * (Real.exp (-Real.pi) / 4) = ∑ x ∈ H \ F, Real.exp (-Real.pi) / 4 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum hpt
  have hS1 : ∑' x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
      4 * ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) + F.card := by
    have hg : Summable (fun x => if x ∈ F then (1 : ℝ) else 0) :=
      summable_of_ne_finset_zero (s := F) (fun x hx => if_neg hx)
    have hsum : ∑' x, (if x ∈ F then (1 : ℝ) else 0) = F.card := by
      rw [tsum_eq_sum (s := F) (fun x hx => if_neg hx)]
      simp
    have hle : ∀ x, Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤
        4 * (‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) + (if x ∈ F then (1 : ℝ) else 0) := by
      intro x
      have hp := Real.exp_pos (-Real.pi * ‖φ x‖ ^ 2)
      by_cases hx : x ∈ F
      · rw [if_pos hx]
        have : Real.exp (-Real.pi * ‖φ x‖ ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, sq_nonneg ‖φ x‖])
        nlinarith [sq_nonneg ‖φ x‖]
      · rw [if_neg hx]
        simp only [hF, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hx
        have : (1 : ℝ) / 4 ≤ ‖φ x‖ ^ 2 := by nlinarith
        nlinarith
    calc _ ≤ ∑' x, (4 * (‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2)) + (if x ∈ F then (1 : ℝ) else 0)) :=
          Summable.tsum_le_tsum hle hS ((hT.mul_left 4).add hg)
      _ = _ := by rw [Summable.tsum_add (hT.mul_left 4) hg, tsum_mul_left, hsum]
  have hE := Real.exp_pos (-Real.pi)
  have hE1 : Real.exp (-Real.pi) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [Real.pi_pos])
  have hT0 : 0 ≤ ∑' x, ‖φ x‖ ^ 2 * Real.exp (-Real.pi * ‖φ x‖ ^ 2) :=
    tsum_nonneg (fun x => by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hS1 hE.le, mul_le_mul_of_nonneg_left hreal hE.le,
    mul_le_mul_of_nonneg_left h2 hE.le, mul_le_mul_of_nonneg_right hE1 hT0]
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.GeometricSideEstimates.HermitianPointEmbeddingInjective

section

@[expose] public section

open UpperTheory.V.Lit.Geo

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
private theorem pt_injective {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (g : GA E a) :
    Function.Injective (pt g) := by
  intro v v' h
  have hu : IsUnit (GeneralLinearGroup.map (pInf E) g).val := Units.isUnit _
  have h1 : vInf v = vInf v' := Matrix.vecMul_injective_of_isUnit hu h
  funext i
  have h2 : ((pInf E).comp (algebraMap E (Ad E))) (v i) = ((pInf E).comp (algebraMap E (Ad E))) (v' i) := congrFun h1 i
  exact ((pInf E).comp (algebraMap E (Ad E))).injective h2

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor in
theorem UpperTheory.hermitian_point_embedding_injective :
    GradA := by
  intro E _ _ _ a ha L hL
  obtain ⟨c, hc, hlow⟩ := UpperTheory.geometric_side_comparison
  obtain ⟨N, hN⟩ := UpperTheory.geometry_of_numbers_lattice_estimate E a ha L hL
  obtain ⟨C, -, hC⟩ := UpperTheory.moment_bound_of_pointwise_moments N 1
  have hD : (0 : ℝ) < (a : ℝ) * Fintype.card (InfinitePlace E) := by
    have h1 : (0 : ℝ) < a := by exact_mod_cast ha
    have h2 : (0 : ℝ) < Fintype.card (InfinitePlace E) := by exact_mod_cast Fintype.card_pos
    exact mul_pos h1 h2
  refine ⟨c / ((a : ℝ) * Fintype.card (InfinitePlace E)), div_pos hc hD, fun g hg => ?_⟩
  have hell : ell E a (toL (mom L g).1) = trF (mom L g).1 1 / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
    simp only [trF, mul_one, Matrix.trace, Matrix.diag, Finset.sum_apply, Complex.re_sum]
    rfl
  rw [hell]
  refine div_le_div_of_nonneg_right ?_ hD.le
  rw [UpperTheory.hermitian_space_moment_identity E a ha L hL g 1, le_div_iff₀ (by linarith)]
  simp only [(UpperTheory.geometric_side_quadraticForm_identity E a).1]
  let φ : lat L g →+ EuclideanSpace ℂ (Fin a × InfinitePlace E) :=
    ((euc (E := E) (a := a)).toLinearMap.toAddMonoidHom.comp (pt (rt g))).comp (lat L g).subtype
  have hφ : ∀ v : lat L g, ‖φ v‖ ^ 2 = qf (pt (rt g) v.1) := fun v => norm_euc_sq _
  have hinj : Function.Injective φ := fun v v' h =>
    Subtype.ext (pt_injective (rt g) ((euc (E := E) (a := a)).injective h))
  have hs0 : Summable fun v : lat L g => Real.exp (-Real.pi * qf (pt (rt g) v.1)) := by
    simpa only [one_mul] using ((hN g).2 1 1 one_pos le_rfl).1
  have hs1 : Summable fun v : lat L g => qf (pt (rt g) v.1) * Real.exp (-Real.pi * qf (pt (rt g) v.1)) := by
    refine ((hC _ _ (hN g)).1.sub hs0).congr fun v => ?_
    ring
  have := hlow (lat L g) _ φ hinj
  simp only [hφ] at this
  exact this hs0 hs1 hg
end
end
