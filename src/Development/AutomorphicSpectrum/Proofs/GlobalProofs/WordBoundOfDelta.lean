module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditiveStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionCommutatorStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVectorStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianFormLieWordGrowthStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosedStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBoundStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspaceStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBound

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord

theorem sum_abs_coord_le_mnorm {n d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hli : LinearIndependent ℝ b) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i) := by
  let L : (Fin d → ℝ) →ₗ[ℝ] (Fin n → Fin n → ℂ) :=
    { toFun := fun r a c => ∑ i, r i • b i a c
      map_add' := fun r s => by
        funext a c
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun t r => by
        funext a c
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  have hL : ∀ r a c, L r a c = (∑ i, r i • b i) a c := by
    intro r a c
    simp [L, Matrix.sum_apply, Matrix.smul_apply]
  have hker : LinearMap.ker L = ⊥ := by
    refine LinearMap.ker_eq_bot'.mpr fun r hr => ?_
    have hsum : ∑ i, r i • b i = 0 := by
      ext a c
      have h := congrFun (congrFun hr a) c
      rw [hL] at h
      simpa using h
    funext i
    exact Fintype.linearIndependent_iff.mp hli r hsum i
  obtain ⟨K, -, hK⟩ := L.exists_antilipschitzWith hker
  refine ⟨(d : ℝ) * K, by positivity, fun r => ?_⟩
  have h1 : ‖r‖ ≤ K * ‖L r‖ := by
    have h := hK.le_mul_dist r 0
    simpa [dist_zero_right] using h
  have hN : 0 ≤ GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h2 : ‖L r‖ ≤ GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by
    refine (pi_norm_le_iff_of_nonneg hN).mpr fun a => ?_
    refine (pi_norm_le_iff_of_nonneg hN).mpr fun c => ?_
    rw [hL]
    unfold GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm
    calc ‖(∑ i, r i • b i) a c‖ ≤ ∑ c', ‖(∑ i, r i • b i) a c'‖ :=
          Finset.single_le_sum (f := fun c' => ‖(∑ i, r i • b i) a c'‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ c)
      _ ≤ ∑ a', ∑ c', ‖(∑ i, r i • b i) a' c'‖ :=
          Finset.single_le_sum (f := fun a' => ∑ c', ‖(∑ i, r i • b i) a' c'‖)
            (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)
  have h3 : ∑ i, |r i| ≤ d * ‖r‖ := by
    calc ∑ i, |r i| ≤ ∑ _i : Fin d, ‖r‖ :=
          Finset.sum_le_sum fun i _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm r i
      _ = d * ‖r‖ := by simp
  calc ∑ i, |r i| ≤ d * ‖r‖ := h3
    _ ≤ d * (K * ‖L r‖) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
    _ ≤ d * (K * GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 K.coe_nonneg) (Nat.cast_nonneg _)
    _ = d * K * GlobalTheory.CompanionTheory.Hypotheses₂.HCA.mnorm (∑ i, r i • b i) := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.LinearIndependentCoefficientNormBoundStatement

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.linearIndependent_coefficient_norm_bound : ∀ {n d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hli : LinearIndependent ℝ b), ∃ D : ℝ, 0 ≤ D ∧ ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.Coord.sum_abs_coord_le_mnorm <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowth

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem deriv_nonneg_of_nonneg_right {e : ℝ → ℝ} {e' : ℝ} (h : HasDerivAt e e' 0) (h0 : e 0 = 0)
    (hpos : ∀ t, 0 < t → 0 ≤ e t) : 0 ≤ e' := by
  refine ge_of_tendsto h.tendsto_slope_zero_right ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht)) (hpos t ht)

theorem isBoundedBilinearMap_re_form {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Q : H → H → ℂ) (Mb : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z)
    (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y))
    (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) :
    IsBoundedBilinearMap ℝ (fun p : H × H => (Q p.1 p.2).re) := by
  have hsmulR : ∀ (c : ℝ) (x y : H), Q x (c • y) = (c : ℂ) * Q x y := fun c x y => by
    rw [← hsmul, Complex.coe_smul]
  have haddL : ∀ x₁ x₂ y, Q (x₁ + x₂) y = Q x₁ y + Q x₂ y := fun x₁ x₂ y => by
    rw [hconj, hadd, star_add, ← hconj, ← hconj]
  have hsmulL : ∀ (c : ℝ) (x y : H), Q (c • x) y = (c : ℂ) * Q x y := fun c x y => by
    rw [hconj, hsmulR, star_mul', ← hconj, show star (c : ℂ) = c from Complex.conj_ofReal c]
  refine ⟨fun x₁ x₂ y => ?_, fun c x y => ?_, fun x y₁ y₂ => ?_, fun c x y => ?_, ?_⟩
  · simp only [haddL, Complex.add_re]
  · simp only [hsmulL, Complex.re_ofReal_mul, smul_eq_mul]
  · simp only [hadd, Complex.add_re]
  · simp only [hsmulR, Complex.re_ofReal_mul, smul_eq_mul]
  · refine ⟨max Mb 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x y => ?_⟩
    rw [Real.norm_eq_abs]
    calc |(Q x y).re| ≤ ‖Q x y‖ := Complex.abs_re_le_norm _
      _ ≤ Mb * ‖x‖ * ‖y‖ := hbd x y
      _ ≤ max Mb 1 * ‖x‖ * ‖y‖ := by gcongr; exact le_max_left _ _

theorem abs_two_re_form_dRep_le : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (Q : H → H → ℂ) (Mb a : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z) (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y)) (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) (hgrow : ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H), (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤ Real.exp (a * |t| * mnorm X) * (Q x x).re) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {x : H} (hx : IsSmoothVec G π x), |2 * (Q (dRep π X x) x).re| ≤ a * mnorm X * (Q x x).re := by
  intro n G H _ _ π hG hrep Q Mb a hadd hsmul hconj hbd hgrow X hX x hx
  have hB := isBoundedBilinearMap_re_form Q Mb hadd hsmul hconj hbd
  have hv : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) x) (dRep π X x) 0 :=
    (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hx hX).1
  have hv0 : π (NormedSpace.exp ((0 : ℝ) • X)) x = x := by
    rw [zero_smul, NormedSpace.exp_zero, hrep.1]
    rfl
  set d := dRep π X x with hd
  set f : ℝ → ℝ := fun t => (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re with hf_def
  have hf : HasDerivAt f (2 * (Q d x).re) 0 := by
    have h1 := (hB.hasFDerivAt (π (NormedSpace.exp ((0 : ℝ) • X)) x, π (NormedSpace.exp ((0 : ℝ) • X)) x)).comp_hasDerivAt
      (0 : ℝ) (hv.prodMk hv)
    rw [hB.deriv_apply] at h1
    simp only [hv0] at h1
    have e : (Q x d).re + (Q d x).re = 2 * (Q d x).re := by
      rw [hconj d x, Complex.star_def, Complex.conj_re]
      ring
    rw [e] at h1
    exact h1
  have hf0 : f 0 = (Q x x).re := by
    simp only [hf_def, hv0]
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (a * t * mnorm X) * (Q x x).re) (a * mnorm X * (Q x x).re) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => a * t * mnorm X) (a * 1 * mnorm X) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_mul a).mul_const (mnorm X)
    have h3 := (h2.exp).mul_const (Q x x).re
    simpa using h3
  have up : 2 * (Q d x).re ≤ a * mnorm X * (Q x x).re := by
    have := deriv_nonneg_of_nonneg_right (hexp.sub hf) (by simp [hf0]) (fun t ht => by
      have := hgrow X hX t x
      rw [abs_of_pos ht] at this
      simp only [hf_def, Pi.sub_apply]
      linarith)
    linarith
  have hfn : HasDerivAt (fun t : ℝ => f (-t)) (2 * (Q d x).re * -1) 0 := by
    have hf' : HasDerivAt f (2 * (Q d x).re) (-(0 : ℝ)) := by rwa [neg_zero]
    exact hf'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have low : -(a * mnorm X * (Q x x).re) ≤ 2 * (Q d x).re := by
    have := deriv_nonneg_of_nonneg_right (hexp.sub hfn) (by simp [hf0]) (fun t ht => by
      have := hgrow X hX (-t) x
      rw [abs_neg, abs_of_pos ht] at this
      simp only [hf_def, Pi.sub_apply]
      linarith)
    linarith
  rw [abs_le]
  exact ⟨low, up⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorHermitianFormGrowthStatement

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.smooth_vector_hermitian_form_growth : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (Q : H → H → ℂ) (Mb a : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z) (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y)) (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) (hgrow : ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H), (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤ Real.exp (a * |t| * mnorm X) * (Q x x).re) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {x : H} (hx : IsSmoothVec G π x), |2 * (Q (dRep π X x) x).re| ≤ a * mnorm X * (Q x x).re := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.abs_two_re_form_dRep_le <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.WordBoundOfDelta

section

@[expose] public section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta

theorem dRep_real_smul {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (r : ℝ) :
    dRep π (r • X) v = (r : ℂ) • dRep π X v := by
  have hrX : r • X ∈ HCSS.lieOf G := (GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.1 r X hX
  have h1 := (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hv hX).1
  have h2 := (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hv hrX).1
  have h3 : HasDerivAt (fun t : ℝ => r * t) r 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul r
  have h4 : HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((r * t) • X)) v) (r • dRep π X v) 0 := by
    have h1' : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) (dRep π X v) (r * 0) := by
      simpa using h1
    exact HasDerivAt.scomp (0 : ℝ) h1' h3
  have h5 : (fun t : ℝ => π (NormedSpace.exp (t • (r • X))) v) = fun t : ℝ => π (NormedSpace.exp ((r * t) • X)) v := by
    funext t
    rw [smul_smul, mul_comm]
  rw [h5] at h2
  rw [h2.unique h4]
  exact (Complex.coe_smul r _).symm

theorem dRep_sum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (r : Fin d → ℝ) {w : H} (hw : IsSmoothVec G π w) :
    dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w := by
  have hl := GlobalTheory.T.lie_algebra_of_linear_group_closed hG
  have key : ∀ s : Finset (Fin d), (∑ i ∈ s, r i • b i ∈ HCSS.lieOf G) ∧
      dRep π (∑ i ∈ s, r i • b i) w = ∑ i ∈ s, (r i : ℂ) • dRep π (b i) w := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨?_, ?_⟩
      · intro t
        simpa using hG.one_mem
      · simp [dRep]
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      have hri := hl.2.1 (r i) _ (hb i)
      refine ⟨hl.1 _ _ hri ih.1, ?_⟩
      rw [(GlobalTheory.T.derived_action_additive hG hrep hw hw hri ih.1).1, ih.2, dRep_real_smul hG hrep hw (hb i)]
  exact (key Finset.univ).2

theorem word_bound_of_delta : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (hc : ∀ v, ContinuousOn (fun g => π g v) G) (hQ : AlmostIsom G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hli : LinearIndependent ℝ b) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (Y : Submodule ℂ H) [FiniteDimensional ℂ Y] (hYs : ∀ y ∈ Y, IsSmoothVec G π y) (hYd : ∀ y ∈ Y, ∑ i, dRep π (b i) (dRep π (b i) y) ∈ Y), ∀ v ∈ Y, WordBound G π v := by
  intro n G H _ _ _ π hG hrep _ hQ d b hb hli hsp Y _ hYs hYd v hv
  obtain ⟨Q, m, Mb, a, hm, hMb, ha, hadd, hsmul, hconj, hpos, hbd, hgrow⟩ := hQ
  obtain ⟨hsadd, hssmul, -⟩ := GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep
  have hvs := hYs v hv
  let S : Submodule ℂ H :=
    { carrier := {x | IsSmoothVec G π x}
      add_mem' := fun {x y} hx hy => hsadd x y hx hy
      zero_mem' := by simpa using hssmul 0 v hvs
      smul_mem' := fun c x hx => hssmul c x hx }
  let Xf : Fin d → Module.End ℂ S := fun i =>
    { toFun := fun x => ⟨dRep π (b i) x, (GlobalTheory.T.derived_action_of_smooth_vector hG hrep x.2 (hb i)).2⟩
      map_add' := fun x y => Subtype.ext (GlobalTheory.T.derived_action_additive hG hrep x.2 y.2 (hb i) (hb i)).2.1
      map_smul' := fun c x => Subtype.ext ((GlobalTheory.T.derived_action_additive hG hrep x.2 x.2 (hb i) (hb i)).2.2 c) }
  have hXc : ∀ i (x : S), ((Xf i x : S) : H) = dRep π (b i) x := fun _ _ => rfl
  have hlie := GlobalTheory.T.lie_algebra_of_linear_group_closed hG
  choose r hr using fun (p : Fin d × Fin d) => hsp _ (hlie.2.2.1 (b p.1) (b p.2) (hb p.1) (hb p.2))
  have hcomm : ∀ i j, Xf i * Xf j - Xf j * Xf i = ∑ l, ((r (i, j) l : ℝ) : ℂ) • Xf l := by
    intro i j
    ext u
    have h1 := GlobalTheory.T.derived_action_commutator hG hrep u.2 (hb i) (hb j)
    rw [show b i * b j - b j * b i = _ from hr (i, j), dRep_sum hG hrep b hb _ u.2] at h1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, hXc]
    exact h1.symm
  have hQnn : ∀ x : H, 0 ≤ (Q x x).re := fun x =>
    le_trans (by positivity) (hpos x)
  let A : ℝ := a * ∑ i, mnorm (b i)
  have hmn : ∀ X : Matrix (Fin n) (Fin n) ℂ, 0 ≤ mnorm X := fun X =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hA : 0 ≤ A := mul_nonneg ha (Finset.sum_nonneg fun i _ => hmn _)
  have hs : ∀ i (x : S), |2 * (Q (Xf i x) x).re| ≤ A * (Q x x).re := by
    intro i x
    refine (GlobalTheory.T.smooth_vector_hermitian_form_growth hG hrep Q Mb a hadd hsmul hconj hbd hgrow (hb i) x.2).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (hQnn x)
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun i => mnorm (b i)) (fun i _ => hmn _) (Finset.mem_univ i)) ha
  let V : Submodule ℂ S := Y.comap S.subtype
  have hinj : Function.Injective (fun u : V => (⟨(u : S), u.2⟩ : Y)) := by
    intro u w h
    exact Subtype.ext (Subtype.ext (congrArg (fun y : Y => (y : H)) h))
  let f : V →ₗ[ℂ] Y :=
    { toFun := fun u => ⟨(u : S), u.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional ℂ V := FiniteDimensional.of_injective f hinj
  have hV : ∀ u ∈ V, (∑ i, Xf i * Xf i) u ∈ V := by
    intro u hu
    have h1 := hYd (u : H) hu
    change (((∑ i, Xf i * Xf i) u : S) : H) ∈ Y
    simpa only [LinearMap.sum_apply, Module.End.mul_apply, Submodule.coe_sum, hXc] using h1
  obtain ⟨C, hC, hN⟩ := GlobalTheory.T.hermitian_form_lie_word_growth (fun x y : S => Q x y)
    (fun x y z => hadd x y z) (fun c x y => hsmul c x y) (fun x y => hconj x y)
    (fun x hx => lt_of_lt_of_le (by
      have : (x : H) ≠ 0 := fun h => hx (Subtype.ext h)
      positivity) (hpos x))
    Xf (fun i j l => ((r (i, j) l : ℝ) : ℂ)) hcomm A hA hs V hV
  have hword : ∀ (l : List (Fin d)) (u : S),
      (((l.map Xf).prod u : S) : H) = l.foldr (fun i w => dRep π (b i) w) (u : H) := by
    intro l u
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, hXc, List.foldr_cons, ih]
  let vS : S := ⟨v, hvs⟩
  have hvV : vS ∈ V := hv
  let K : ℝ := Real.sqrt (Q v v).re / Real.sqrt m
  have hK : 0 ≤ K := by positivity
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  refine GlobalTheory.T.lie_basis_coordinate_growth_bound hG hrep b hb hsp _ (GlobalTheory.T.linearIndependent_coefficient_norm_bound b hli).choose_spec.1 (GlobalTheory.T.linearIndependent_coefficient_norm_bound b hli).choose_spec.2
    (fun r w hw => dRep_sum hG hrep b hb r hw) hvs (C * (K + 1)) (by positivity) ?_
  intro l
  have h1 := hN l vS hvV
  rw [show ((l.map Xf).prod vS : S) = ((l.map Xf).prod vS : S) from rfl] at h1
  set w : S := (l.map Xf).prod vS with hw
  have hwv : (w : H) = l.foldr (fun i w => dRep π (b i) w) v := hword l vS
  rw [← hwv]
  have h2 : Real.sqrt m * ‖(w : H)‖ ≤ Real.sqrt (Q w w).re := by
    apply Real.le_sqrt_of_sq_le
    rw [mul_pow, Real.sq_sqrt hm.le]
    exact hpos w
  have h3 : ‖(w : H)‖ ≤ C ^ (l.length + 1) * l.length.factorial * K := by
    have h4 : Real.sqrt m * ‖(w : H)‖ ≤ C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q v v).re := h2.trans h1
    have h5 : C ^ (l.length + 1) * l.length.factorial * K = (C ^ (l.length + 1) * l.length.factorial * Real.sqrt (Q v v).re) / Real.sqrt m := by
      simp only [K]; ring
    rw [h5, le_div_iff₀ hsm]
    linarith
  refine h3.trans ?_
  have h6 : K ≤ (K + 1) ^ (l.length + 1) := by
    have h7 : (K + 1) ^ 1 ≤ (K + 1) ^ (l.length + 1) := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  rw [mul_pow]
  have h8 : 0 ≤ C ^ (l.length + 1) * (l.length.factorial : ℝ) := by positivity
  calc C ^ (l.length + 1) * l.length.factorial * K ≤ C ^ (l.length + 1) * l.length.factorial * (K + 1) ^ (l.length + 1) :=
        mul_le_mul_of_nonneg_left h6 h8
    _ = C ^ (l.length + 1) * (K + 1) ^ (l.length + 1) * l.length.factorial := by ring

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordDelta

end
end
end
