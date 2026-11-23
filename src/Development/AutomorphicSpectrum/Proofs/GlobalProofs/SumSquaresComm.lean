module

public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSmoothVec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionAdditiveStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionOfSmoothVectorStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieAlgebraOfLinearGroupClosedStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SmoothVectorsInvariantSubspaceStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionConjugation

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem differentiableAt_entries_exp_smul {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    DifferentiableAt ℝ
      (fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ)) s := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hc : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X)) _ s :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) X s
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin n → Fin n → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  exact (L.hasFDerivAt.comp_hasDerivAt s hc).differentiableAt

theorem dRep_equivariant : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G), π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v) := by
  intro n G H _ _ π hG hrep v hv X hX g hg
  obtain ⟨F, hF, hFv⟩ := hv
  have hu : IsUnit g := hG.isUnit g hg
  have hgi : g⁻¹ ∈ G := hG.inv_mem g hg
  have hinv : g⁻¹ * g = 1 := Matrix.nonsing_inv_mul g ((Matrix.isUnit_iff_isUnit_det g).1 hu)
  have hd : DifferentiableAt ℝ (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0 := by
    have he : (fun t : ℝ => π (NormedSpace.exp (t • X)) v) =
        F ∘ fun t : ℝ => (Matrix.of.symm (NormedSpace.exp (t • X)) : Fin n → Fin n → ℂ) := by
      funext t
      exact hFv _ (hX t)
    rw [he]
    exact (hF.differentiable (by simp)).differentiableAt.comp 0
      (differentiableAt_entries_exp_smul X 0)
  have key : ∀ t : ℝ, π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v) =
      π g (π (NormedSpace.exp (t • X)) v) := by
    intro t
    have hconj : NormedSpace.exp (t • (g * X * g⁻¹)) = g * NormedSpace.exp (t • X) * g⁻¹ := by
      have : t • (g * X * g⁻¹) = g * (t • X) * g⁻¹ := by
        simp [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
      rw [this, Matrix.exp_conj _ _ hu]
    have hge : g * NormedSpace.exp (t • X) ∈ G := hG.mul_mem _ hg _ (hX t)
    have h1 : π (g * NormedSpace.exp (t • X) * g⁻¹ * g) =
        (π (g * NormedSpace.exp (t • X) * g⁻¹)).comp (π g) :=
      hrep.2 _ (hG.mul_mem _ hge _ hgi) _ hg
    have h2 : g * NormedSpace.exp (t • X) * g⁻¹ * g = g * NormedSpace.exp (t • X) := by
      rw [Matrix.mul_assoc _ g⁻¹ g, hinv, Matrix.mul_one]
    have h3 := hrep.2 _ hg _ (hX t)
    rw [hconj]
    rw [h2, h3] at h1
    exact (DFunLike.congr_fun h1 v).symm
  have h2 := ((π g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt
  have h3 : deriv (fun t : ℝ => π (NormedSpace.exp (t • (g * X * g⁻¹))) (π g v)) 0 =
      π g (deriv (fun t : ℝ => π (NormedSpace.exp (t • X)) v) 0) := by
    rw [funext key]
    exact h2.deriv
  exact h3.symm

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.DerivedActionConjugationStatement

section

@[expose] public section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.derived_action_conjugation : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hv : IsSmoothVec G π v) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ G), π g (dRep π X v) = dRep π (g * X * g⁻¹) (π g v) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.dRep_equivariant <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GlobalProofs.SumSquaresComm

section

@[expose] public section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem dRep_realSum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u : H} (hu : IsSmoothVec G π u) {ι : Type} (s : Finset ι)
    (c : ι → ℝ) (a : ι → Matrix (Fin n) (Fin n) ℂ) (ha : ∀ l, a l ∈ HCSS.lieOf G)
    (h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ HCSS.lieOf G) :
    (∑ l ∈ s, c l • a l) ∈ HCSS.lieOf G ∧
      dRep π (∑ l ∈ s, c l • a l) u = ∑ l ∈ s, c l • dRep π (a l) u := by
  classical
  obtain ⟨hadd, hsm, -, -⟩ := GlobalTheory.T.lie_algebra_of_linear_group_closed hG
  induction s using Finset.induction_on with
  | empty => simpa using ⟨h0, GlobalTheory.GKLie.dRep_zero π u⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 := hsm (c x) _ (ha x)
    refine ⟨hadd _ _ h1 ih.1, ?_⟩
    rw [(GlobalTheory.T.derived_action_additive hG hrep hu hu h1 ih.1).1, ih.2, GlobalTheory.GKLie.dRep_smul]

theorem dRep_vecSum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G)
    {ι : Type} (s : Finset ι) (c : ι → ℝ) (u : ι → H) (hu : ∀ l, IsSmoothVec G π (u l)) :
    IsSmoothVec G π (∑ l ∈ s, c l • u l) ∧
      dRep π X (∑ l ∈ s, c l • u l) = ∑ l ∈ s, c l • dRep π X (u l) := by
  classical
  obtain ⟨hadd, hsm, -⟩ := GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, by simp [dRep]⟩
    exact ⟨fun _ => 0, contDiff_const, fun z _ => by simp⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 : IsSmoothVec G π (c x • u x) := by
      rw [← Complex.coe_smul]
      exact hsm _ _ (hu x)
    refine ⟨hadd _ _ h1 ih.1, ?_⟩
    rw [(GlobalTheory.T.derived_action_additive hG hrep h1 ih.1 hX hX).2.1, ih.2, ← Complex.coe_smul,
      (GlobalTheory.T.derived_action_additive hG hrep (hu x) (hu x) hX hX).2.2, Complex.coe_smul]

theorem sumSquares_comm {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ G)
    (O : Matrix (Fin d) (Fin d) ℝ) (hO : Oᵀ * O = 1) (hkb : ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l)
    {v : H} (hv : IsSmoothVec G π v) :
    π k (∑ i, dRep π (b i) (dRep π (b i) v)) = ∑ i, dRep π (b i) (dRep π (b i) (π k v)) := by
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i0⟩⟩
  · simp [Finset.univ_eq_empty]
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ HCSS.lieOf G := by
    simpa using (GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.1 0 _ (hb i0)
  have hw : IsSmoothVec G π (π k v) := (GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep).2.2 k hk v hv
  have hT : ∀ m, IsSmoothVec G π (dRep π (b m) (π k v)) := fun m =>
    (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hw (hb m)).2
  have step : ∀ i, π k (dRep π (b i) (dRep π (b i) v)) =
      ∑ l, ∑ m, (O l i * O m i) • dRep π (b l) (dRep π (b m) (π k v)) := by
    intro i
    have hsm := (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hv (hb i)).2
    rw [GlobalTheory.T.derived_action_conjugation hG hrep hsm (hb i) hk, GlobalTheory.T.derived_action_conjugation hG hrep hv (hb i) hk, hkb i,
      (dRep_realSum hG hrep hw Finset.univ (fun m => O m i) b hb h0).2,
      (dRep_realSum hG hrep
        (dRep_vecSum hG hrep (hb i0) Finset.univ (fun m => O m i) _ hT).1
        Finset.univ (fun l => O l i) b hb h0).2]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(dRep_vecSum hG hrep (hb l) Finset.univ (fun m => O m i) _ hT).2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.1 hO
  have hdelta : ∀ l m, ∑ i, O l i * O m i = (1 : Matrix (Fin d) (Fin d) ℝ) l m := fun l m => by
    rw [← hOO]
    simp [Matrix.mul_apply]

  rw [map_sum, Finset.sum_congr rfl fun i _ => step i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hdelta, Matrix.one_apply]
  simp

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end
end
