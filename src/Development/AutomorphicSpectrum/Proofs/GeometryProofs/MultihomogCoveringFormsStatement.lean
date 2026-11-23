module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MultihomogeneousEvalScale

section

@[expose] public section

open MvPolynomial

theorem PositivityTheory.Xgn.multihomogeneous_eval_scale : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (s : MvPolynomial (Σ k, ι k) ℤ) (a : K → ℕ) (c : K → ℂ) (z : ((Σ k, ι k) → ℂ)), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog s a → eval (fun p => c p.1 * z p) (MvPolynomial.map (Int.castRingHom ℂ) s) = (∏ k, c k ^ a k) * eval z (MvPolynomial.map (Int.castRingHom ℂ) s) := by
  intro K _ _ ι _ s a c z hs
  rw [eval_map, eval_map, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight ι) m = a :=
    hs (mem_support_iff.mp hm)
  have ha : ∀ k, a k = ∑ i : ι k, m ⟨k, i⟩ := by
    intro k
    rw [← hw, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
      Fintype.sum_sigma, Finset.sum_eq_single k]
    · simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight]
    · intro j _ hj
      simp [GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight, Pi.single_apply, hj, hj.symm]
    · simp
  have h1 : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [ha k, ← Finset.prod_pow_eq_pow_sum]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, h1]
  ring
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.PolynomialEvalComplexConjugate

section

@[expose] public section

open MvPolynomial

theorem PositivityTheory.Xgn.polynomial_eval_complex_conjugate : ∀ (σ : Type) (s : MvPolynomial σ ℤ) (z : σ → ℂ), eval (fun p => (starRingEnd ℂ) (z p)) (MvPolynomial.map (Int.castRingHom ℂ) s) = (starRingEnd ℂ) (eval z (MvPolynomial.map (Int.castRingHom ℂ) s)) := by
  intro σ s z
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_comp_left]
  congr 1
  exact RingHom.ext_int _ _
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.PolynomialNormSquareSmooth

section

@[expose] public section

open MvPolynomial

namespace PositivityTheory.Xgn.SmoothPolynomialNormSquare

theorem contDiff_eval (σ : Type) [Fintype σ] (p : MvPolynomial σ ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : σ → ℂ => MvPolynomial.eval z p) := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [MvPolynomial.eval_C]
    exact contDiff_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (contDiff_apply ℝ (fun _ => ℂ) i)

end PositivityTheory.Xgn.SmoothPolynomialNormSquare

theorem PositivityTheory.Xgn.polynomial_norm_square_smooth : ∀ (σ : Type) [Fintype σ] (s : MvPolynomial σ ℤ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : σ → ℂ => ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) s)‖ ^ 2) := by
  intro σ _ s
  exact (PositivityTheory.Xgn.SmoothPolynomialNormSquare.contDiff_eval σ _).norm_sq ℝ
end
end

-- Source module: Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.MultihomogeneousLineBundle

section

@[expose] public section

open MvPolynomial

namespace PositivityTheory.Xgn.MultihomogeneousLine

theorem sum_scale {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}
    (u : Fin n → MvPolynomial (Σ k, ι k) ℤ) (a : K → ℕ)
    (hu : ∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    ∑ j, ‖eval (fun p => c p.1 * z p) (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 =
      (∏ k, ‖c k‖ ^ a k) ^ 2 * ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PositivityTheory.Xgn.multihomogeneous_eval_scale K ι (u j) a c z (hu j), norm_mul, mul_pow, norm_prod]
  simp only [norm_pow]

theorem sum_pos {σ : Type} {n : ℕ} (u : Fin n → MvPolynomial σ ℤ) (z : σ → ℂ)
    (h : ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) :
    0 < ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2 := by
  obtain ⟨j, hj⟩ := h
  exact Finset.sum_pos' (fun i _ => sq_nonneg _)
    ⟨j, Finset.mem_univ j, pow_pos (norm_pos_iff.mpr hj) 2⟩

theorem sqrt_scale (x y N D : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt ((x ^ 2 * N) / (y ^ 2 * D)) = x / y * Real.sqrt (N / D) := by
  rw [mul_div_mul_comm, ← div_pow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hx hy)]

end PositivityTheory.Xgn.MultihomogeneousLine

theorem PositivityTheory.Xgn.multihomogeneous_line_bundle : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) := by
  intro K _ _ ι _ A a b n u v hu hv hu0 hv0 hsm hconj
  refine ⟨⟨fun k => A.a k + (a k : ℤ) - (b k : ℤ),
    fun z => A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) /
      (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)), ?_, ?_⟩, rfl, ?_, ?_, fun _ => rfl⟩
  · intro z hz
    exact mul_pos (A.pos z hz) (Real.sqrt_pos.mpr (div_pos
      (MultihomogeneousLine.sum_pos u z (hu0 z hz)) (MultihomogeneousLine.sum_pos v z (hv0 z hz))))
  · intro c z hc
    rw [A.smul c z hc, MultihomogeneousLine.sum_scale u a hu, MultihomogeneousLine.sum_scale v b hv,
      MultihomogeneousLine.sqrt_scale _ _ _ _
        (Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)
        (Finset.prod_nonneg fun k _ => pow_nonneg (norm_nonneg _) _)]
    have : ∀ k, ‖c k‖ ^ (A.a k + (a k : ℤ) - (b k : ℤ)) = ‖c k‖ ^ A.a k * ‖c k‖ ^ a k / ‖c k‖ ^ b k := by
      intro k
      have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
      rw [zpow_sub₀ h0, zpow_add₀ h0, zpow_natCast, zpow_natCast]
    simp only [this, Finset.prod_div_distrib, Finset.prod_mul_distrib]
    ring
  · have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ =>
        ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) :=
      ContDiff.sum fun j _ => PositivityTheory.Xgn.polynomial_norm_square_smooth _ (u j)
    have hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ =>
        ∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2) :=
      ContDiff.sum fun j _ => PositivityTheory.Xgn.polynomial_norm_square_smooth _ (v j)
    exact ContDiffOn.mul hsm (ContDiffOn.sqrt
      (hN.contDiffOn.div hD.contDiffOn fun z hz => (MultihomogeneousLine.sum_pos v z (hv0 z hz)).ne')
      fun z hz => (div_pos (MultihomogeneousLine.sum_pos u z (hu0 z hz))
        (MultihomogeneousLine.sum_pos v z (hv0 z hz))).ne')
  · intro z
    have := hconj z
    simp only [this, PositivityTheory.Xgn.polynomial_eval_complex_conjugate, RCLike.norm_conj]
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogCoveringForms

section

@[expose] public section

open MvPolynomial

namespace GlobalTheory.CompanionTheory.TwistLine

theorem twisted_hermitian_line : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) :=
  @PositivityTheory.Xgn.multihomogeneous_line_bundle

end GlobalTheory.CompanionTheory.TwistLine
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogCoveringFormsStatement

section

@[expose] public section

open MvPolynomial

theorem _root_.GlobalTheory.T.multihomog_covering_forms : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) := by
  first | exact @GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line | exact GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line | (intros; apply GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line <;> assumption)
end
end
