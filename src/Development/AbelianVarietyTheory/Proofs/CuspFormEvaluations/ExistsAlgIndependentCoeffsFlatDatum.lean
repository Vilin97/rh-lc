module

public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeCoefficientsCommonZerosSimpleStatement
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeTranscendentalPointNonvanishing
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
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoordsNoHomogeneousRelationGenericHyperpla
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsNotSmallWhereCombinationsVanishStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MahlerCompactness
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.SumNormSqOrbit
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeTranscendentalPointNonvanishing

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeTranscendentalPointNonvanishingStatement

section

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.ae_transcendental_point_nonvanishing : ∀ (K : Type) [Field K] [Countable K] (σ : K →+* ℂ) (ι : Type) [Fintype ι], ∀ᵐ t : ι → ℂ, ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0 := by
  first | exact @GlobalTheory.ae_eval₂_ne_zero_of_countable | exact GlobalTheory.ae_eval₂_ne_zero_of_countable | (intros; apply GlobalTheory.ae_eval₂_ne_zero_of_countable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsCoordsNoHomogeneousRelationGenericHyperplaStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (m N : ℕ) (t : Fin m × Fin N → ℂ) (ζ : Fin N → ℂ), (∀ Q : MvPolynomial (Fin m × Fin N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → ζ ≠ 0 → (∀ i, ∑ j, t (i, j) * ζ j = 0) → ∃ jj : Fin (m + 1) → Fin N, ∀ (Q : MvPolynomial (Fin (m + 1)) K) (d : ℕ), Q ≠ 0 → Q.IsHomogeneous d → MvPolynomial.eval₂ σ (fun a => ζ (jj a)) Q ≠ 0 := by
  first | exact @GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero | exact GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero | (intros; apply GlobalTheory.exists_coordinates_no_homogeneous_relation_of_generic_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsBoundedByGenericCombinations

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

theorem cone_sum_sq_le {m N : ℕ} (t : Fin m × Fin N → ℂ) (Z : Set (Fin N → ℂ)) (hZ : IsClosed Z)
    (hc : ∀ (c : ℂ), ∀ ζ ∈ Z, c • ζ ∈ Z) (h0 : ∀ ζ ∈ Z, (∀ i, ∑ j, t (i, j) * ζ j = 0) → ζ = 0) :
    ∃ C : ℝ, ∀ ζ ∈ Z, ∑ k, ‖ζ k‖ ^ 2 ≤ C * ∑ i, ‖∑ j, t (i, j) * ζ j‖ ^ 2 := by
  set f : (Fin N → ℂ) → ℝ := fun ζ => ∑ i, ‖∑ j, t (i, j) * ζ j‖ ^ 2 with hf
  set g : (Fin N → ℂ) → ℝ := fun ζ => ∑ k, ‖ζ k‖ ^ 2 with hg
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hS : IsCompact (Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z) := (isCompact_sphere _ _).inter_right hZ
  have hfnn : ∀ ζ, 0 ≤ f ζ := fun ζ => Finset.sum_nonneg fun i _ => by positivity
  have hpos : ∀ ζ ∈ Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z, 0 < f ζ := by
    rintro ζ ⟨h1, h2⟩
    refine lt_of_le_of_ne (hfnn ζ) fun h => ?_
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h.symm
    have h4 : ζ = 0 := h0 ζ h2 fun i => by simpa using h3 i (Finset.mem_univ i)
    simp [h4] at h1
  obtain ⟨C, hC⟩ := hS.bddAbove_image (f := fun ζ => g ζ / f ζ)
    (hgc.continuousOn.div hfc.continuousOn fun ζ hζ => (hpos ζ hζ).ne')
  refine ⟨C, fun ζ hζ => ?_⟩
  by_cases hz : ζ = 0
  · simp [hz]
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hz
  set c : ℂ := ((‖ζ‖⁻¹ : ℝ) : ℂ) with hcdef
  have hcn : ‖c‖ = ‖ζ‖⁻¹ := by simp [hcdef]
  have hmem : c • ζ ∈ Metric.sphere (0 : Fin N → ℂ) 1 ∩ Z :=
    ⟨by rw [mem_sphere_zero_iff_norm, norm_smul, hcn, inv_mul_cancel₀ hn.ne'], hc c ζ hζ⟩
  have h1 : g (c • ζ) ≤ C * f (c • ζ) := (div_le_iff₀ (hpos _ hmem)).1 (hC ⟨_, hmem, rfl⟩)
  have h2 : g (c • ζ) = ‖c‖ ^ 2 * g ζ := by
    simp only [hg, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  have h3 : f (c • ζ) = ‖c‖ ^ 2 * f ζ := by
    simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_pow, ← norm_mul, Finset.mul_sum]
    congr 2
    exact Finset.sum_congr rfl fun j _ => by ring
  have h4 : 0 < ‖c‖ ^ 2 := by rw [hcn]; positivity
  rw [h2, h3, mul_left_comm] at h1
  exact le_of_mul_le_mul_left h1 h4

theorem eval₂_smul_of_isHomogeneous {K : Type} [Field K] (σ : K →+* ℂ) {n d : ℕ} {Q : MvPolynomial (Fin n) K}
    (hQ : Q.IsHomogeneous d) (c : ℂ) (z : Fin n → ℂ) :
    MvPolynomial.eval₂ σ (fun a => c * z a) Q = c ^ d * MvPolynomial.eval₂ σ z Q := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have h := hQ (MvPolynomial.mem_support_iff.1 hs)
  have h' : ∑ a, s a = d := by
    rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h']
  ring

theorem forms_le_generic_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖sf i x‖ ^ 2 := by
  intro E _ _ _ r X Xa K _ σ t ht hrel sf
  choose Q d hQ0 hQd hQ using hrel.1
  let Z : Set (Fin Xa.N → ℂ) := {ζ | ∀ jj, MvPolynomial.eval₂ σ (fun a => ζ (jj a)) (Q jj) = 0}
  have hZ : IsClosed Z := by
    simp only [Z, Set.setOf_forall]
    refine isClosed_iInter fun jj => isClosed_eq ?_ continuous_const
    simp only [MvPolynomial.eval₂_eq']
    fun_prop
  obtain ⟨C, hC⟩ := cone_sum_sq_le t Z hZ
    (fun c ζ hζ jj => by
      have := eval₂_smul_of_isHomogeneous σ (hQd jj) c fun a => ζ (jj a)
      rw [hζ jj, mul_zero] at this
      exact this)
    (fun ζ hζ h => by
      by_contra hz
      obtain ⟨jj, hjj⟩ := GlobalTheory.T.exists_coords_no_homogeneous_relation_generic_hyperplanes K σ _ _ t ζ ht hz h
      exact hjj _ _ (hQ0 jj) (hQd jj) (hζ jj))
  exact ⟨C, fun x hx => hC (fun k => Xa.w k x) fun jj => hQ jj x hx⟩

end GlobalTheory.Shares
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaFormsBoundedByGenericCombinationsStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.theta_forms_bounded_by_generic_combinations : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] (σ : K →+* ℂ) (t : Fin (nd X + 1) × Fin Xa.N → ℂ), (∀ Q : MvPolynomial (Fin (nd X + 1) × Fin Xa.N) K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0) → RelIn σ X Xa → let sf : Fin (nd X + 1) → Frame X.Ψ r → ℂ := fun i x => ∑ j, t (i, j) * Xa.w j x; ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖sf i x‖ ^ 2 := by
  first | exact @GlobalTheory.Shares.forms_le_generic_comb | exact GlobalTheory.Shares.forms_le_generic_comb | (intros; apply GlobalTheory.Shares.forms_le_generic_comb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeExistsFlatDatumLinearCombination

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GenericFlat

theorem ae_exists_flat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] [Countable K] (σ : K →+* ℂ), RelIn σ X Xa → ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, ∃ Fl : FlatM X Xa, (∀ x, Fl.w0 x = ∑ j, t (0, j) * Xa.w j x) ∧ ∀ k x, Fl.s k x = ∑ j, t (k.succ, j) * Xa.w j x := by
  intro E _ _ _ r X Xa K _ _ σ hR
  filter_upwards [GlobalTheory.T.ae_transcendental_point_nonvanishing K σ (Fin (nd X + 1) × Fin Xa.N), GlobalTheory.T.ae_coefficients_common_zeros_simple E r X Xa] with t hgen hsimple

  have hdom : ∃ C : ℝ, ∀ x ∈ X.dom, ∑ k, ‖Xa.w k x‖ ^ 2 ≤ C * ∑ i, ‖∑ j, t (i, j) * Xa.w j x‖ ^ 2 :=
    GlobalTheory.T.theta_forms_bounded_by_generic_combinations E r X Xa K σ t hgen hR
  have hlow : ∃ ε c0 : ℝ, 0 < ε ∧ 0 < c0 ∧ ∀ x ∈ X.dom,
      ∑ i : Fin (nd X), ‖∑ j, t (i.succ, j) * Xa.w j x‖ ^ 2 < ε * ‖∑ j, t (0, j) * Xa.w j x‖ ^ 2 →
        c0 ≤ ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 :=
    GlobalTheory.T.theta_forms_not_small_where_combinations_vanish E r X Xa K σ t hgen hR
  have hsim : ∀ x ∈ X.dom, ∑ j, t (0, j) * Xa.w j x ≠ 0 →
      (∀ k : Fin (nd X), ∑ j, t (k.succ, j) * Xa.w j x = 0) →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        (∑ j, t (k.succ, j) * Xa.w j (cpt X x z)) / ∑ j, t (0, j) * Xa.w j (cpt X x z) : V (nd X))) 0).det ≠ 0 :=
    hsimple
  obtain ⟨C, hC⟩ := hdom

  have hzero : ∀ x ∈ X.dom, (∀ k : Fin (nd X), ∑ j, t (k.succ, j) * Xa.w j x = 0) →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        (∑ j, t (k.succ, j) * Xa.w j (cpt X x z)) / ∑ j, t (0, j) * Xa.w j (cpt X x z) : V (nd X))) 0).det ≠ 0 := by
    intro x hx hs
    have hs0 : ∑ j, t (0, j) * Xa.w j x ≠ 0 := by
      intro h0
      obtain ⟨k, hk⟩ := Xa.w_nz x hx
      have hsum : ∑ i, ‖∑ j, t (i, j) * Xa.w j x‖ ^ 2 = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨m, rfl⟩
        · simp [h0]
        · simp [hs m]
      have hle := hC x hx
      rw [hsum, mul_zero] at hle
      have hk' : ‖Xa.w k x‖ ^ 2 ≤ ∑ k, ‖Xa.w k x‖ ^ 2 :=
        Finset.single_le_sum (f := fun k => ‖Xa.w k x‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ k)
      have h2 : ‖Xa.w k x‖ ^ 2 = 0 := le_antisymm (hk'.trans hle) (by positivity)
      exact hk (by simpa using h2)
    exact hsim x hx hs0 hs
  obtain ⟨Fl, h0, hs⟩ := GlobalTheory.FlatPoints.exists_flat GlobalTheory.ClosedDiscontinuity.firstMinimum_invariant_continuous_pos_on_frames
    GlobalTheory.FlagMahler.mahler_compactness r X Xa (fun i j => t (i, j)) ⟨C, hC⟩ hlow hzero
  exact ⟨Fl, fun x => congrFun h0 x, fun k x => congrFun (congrFun hs k) x⟩

end GlobalTheory.GenericFlat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.AeExistsFlatDatumLinearCombinationStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

theorem _root_.GlobalTheory.T.ae_exists_flat_datum_linearCombination : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (K : Type) [Field K] [Countable K] (σ : K →+* ℂ), RelIn σ X Xa → ∀ᵐ t : Fin (nd X + 1) × Fin Xa.N → ℂ, ∃ Fl : FlatM X Xa, (∀ x, Fl.w0 x = ∑ j, t (0, j) * Xa.w j x) ∧ ∀ k x, Fl.s k x = ∑ j, t (k.succ, j) * Xa.w j x := by
  first | exact @GlobalTheory.GenericFlat.ae_exists_flat | exact GlobalTheory.GenericFlat.ae_exists_flat | (intros; apply GlobalTheory.GenericFlat.ae_exists_flat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAlgIndependentCoeffsFlatDatum

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
open MeasureTheory

namespace GlobalTheory.GenericFlat

theorem ae_cast {a b n m : ℕ} (hab : a = b) (hnm : n = m) (P : (Fin (a + 1) × Fin n → ℂ) → Prop)
    (hP : ∀ᵐ t : Fin (a + 1) × Fin n → ℂ, P t) :
    ∀ᵐ t : Fin (b + 1) × Fin m → ℂ,
      P fun p => t (Fin.cast (congrArg (· + 1) hab) p.1, Fin.cast hnm p.2) := by
  subst hab hnm
  simpa using hP

theorem exists_generic_flatAt : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1), ∃ t : Idx D j N → ℂ, (∀ Q : MvPolynomial (Idx D j N) T.Q.c.F, Q ≠ 0 → MvPolynomial.eval₂ T.σ₀ t Q ≠ 0) ∧ Nonempty (FlatAt h j A t) := by
  intro D T h j _hj N wL wF w Tn c1 A
  have hC : Countable T.Q.c.F := (Module.finBasis ℚ T.Q.c.F).equivFun.injective.countable

  have hk : ∀ k : (T.U j T.σ₀).Comp, ∀ᵐ t : Fin (WeightFamilies.dimY D j + 1) × Fin N → ℂ,
      ∃ Fl : FlatM ((T.U j T.σ₀).X k) (A.Xa k),
        (∀ x, Fl.w0 x = ∑ i, t (0, i) * rdR h j (w i) k x) ∧
        ∀ a x, Fl.s a x = ∑ i, t ((Fin.cast (A.dim k) a).succ, i) * rdR h j (w i) k x := by
    intro k
    have H := GlobalTheory.T.ae_exists_flat_datum_linearCombination _ _ ((T.U j T.σ₀).X k) (A.Xa k) T.Q.c.F T.σ₀ (A.rel k)
    refine (ae_cast (A.dim k) (A.hN k) _ H).mono ?_
    rintro t ⟨Fl, h0, hs⟩
    refine ⟨Fl, fun x => ?_, fun a x => ?_⟩
    · rw [h0]
      refine Fintype.sum_equiv (finCongr (A.hN k)) _ _ fun i => ?_
      simp only [A.hw k i, finCongr_apply]
      congr 2
    · rw [hs]
      refine Fintype.sum_equiv (finCongr (A.hN k)) _ _ fun i => ?_
      simp only [A.hw k i, finCongr_apply]
      congr 2

  have hall := (ae_all_iff.2 hk).and
    (GlobalTheory.ae_eval₂_ne_zero_of_countable T.Q.c.F T.σ₀ (Fin (WeightFamilies.dimY D j + 1) × Fin N))
  obtain ⟨t, ht, hg⟩ := hall.exists
  choose Fl h0 hs using ht
  exact ⟨t, hg, ⟨⟨Fl, h0, hs⟩⟩⟩

end GlobalTheory.GenericFlat
end
end
