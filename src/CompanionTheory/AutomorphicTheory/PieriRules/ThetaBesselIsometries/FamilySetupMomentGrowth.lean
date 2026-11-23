module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselFrameEntryRelationStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselLieTriangularVanishingStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorCayleyCompatibleStatement
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.QuantumDeterminantEigenvalueStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.SmoothVectorsDiscreteSeriesGlModuleStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalueStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameWConjMatrixUnitsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjectorEntryValueUnderLinearFunctionalStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueOnDualTensorSummandStatement
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.HaarEqSmul
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.TensorMomentEstimateStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AbsCoordLeOfLOneNormLe
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LoweringBound
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorBesselMoment

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace BesselProjectorValue

lemma star_Hpk (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    star (Formalism.QuantumDeterminants.Hpk k r i j) = Formalism.QuantumDeterminants.Hpk k r i j := by
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

lemma ev_flat {k r : ℕ} (R : Rep k r) (f : Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1) → R.H) :
    ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r f) x = ∑ j, f j • x j := by
  unfold ev
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h1 : ∀ i, star (flat k r f i) = ∑ p, f p * Formalism.QuantumDeterminants.Hpk k r p i := by
    intro i
    simp [flat, Formalism.QuantumDeterminants.herm, dotProduct, Matrix.mulVec_single_one, Matrix.col, star_Hpk]
  simp only [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h2 : ∀ p, ∑ i, f p * Formalism.QuantumDeterminants.Hpk k r p i * Formalism.QuantumDeterminants.Hpk k r i j = f p * (1 : Mx k r) p j := by
    intro p
    rw [← Formalism.QuantumDeterminants.GBasic.Hpk_sq k r, Matrix.mul_apply, Finset.mul_sum]
    simp only [mul_assoc]
  simp only [h2, Matrix.one_apply]
  simp

lemma sum_frame {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g)
    (f : Fin n → ℂ) (x : Fin n → V) :
    ∑ j, f j • x j = ∑ d, (g⁻¹ *ᵥ f) d • ∑ c, g c d • x c := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have : (g *ᵥ (g⁻¹ *ᵥ f)) j = f j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
  rw [← this]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

lemma sum_coframe {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g)
    (ω : Fin n → ℂ) (v : V) (c : Fin n) :
    ∑ d, g⁻¹ d c • ((gᵀ *ᵥ ω) d • v) = ω c • v := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  simp only [smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have : ((g⁻¹)ᵀ *ᵥ (gᵀ *ᵥ ω)) c = ω c := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.transpose_one,
      Matrix.one_mulVec]
  rw [← this]
  rfl

end BesselProjectorValue


open BesselProjectorValue in
theorem bessel_ev_projector_value : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (RI : Fin (2 * r + k + 1) → Rep k r) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp), 1 ≤ k → R.IsDG ε mu → (∀ s, (RI s).IsDG ε (mu - Pi.single s 1)) → TensRaw dualM R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π l → ∀ s, ∃ c : ℂ, ‖c‖ = Formalism.QuantumDeterminants.Tz k r z * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ v ∈ R.sm, l (ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (fun c' => io s c' (∑ d, pr s d (tm R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d)))) = c • l v := by
  intro hy k r ε mu R RI io pr Wp _ _ _ _ z π u μW μN μG νq l hk hR hRI hT hS hB s
  have hK : PI.KFinSmooth := hy.1.2.2.1
  obtain ⟨hz, hTz, ⟨u₀, hu₀⟩, hcap, -⟩ := hS
  have hπ1 : π 1 = 1 := (Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hTz hu₀).1
  obtain ⟨g, hg, -⟩ := hu₀
  obtain ⟨hgu, hN, ⟨hfr, hunit⟩, hf, hω⟩ := GlobalTheory.T.frameW_conj_matrix_units k r z g hz hTz hg
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hgu
  have hQ : IsUnit g⁻¹ := (Matrix.isUnit_nonsing_inv_iff).2 hgu
  have hgi : g⁻¹⁻¹ = g := Matrix.nonsing_inv_nonsing_inv g hd
  obtain ⟨E, hE, hEg⟩ := GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε mu R hR g⁻¹ hQ
  choose F hF hFg using fun t => GlobalTheory.T.smoothVectors_discreteSeries_glModule hK k r ε _ (RI t) (hRI t) g⁻¹ hQ
  obtain ⟨io', pr', hcomm, -, hsum, -, -, hio, hpr⟩ :=
    GlobalTheory.T.dual_tensor_cayley_compatible hK k r ε mu R hR RI _ io pr g⁻¹ E F hRI hT hQ hE hF
  have hn : 2 ≤ 2 * r + k + 1 := by omega
  have hqE := GlobalTheory.T.quantum_determinant_eigenvalue hy k r ε mu R hR g⁻¹ E hQ hE
  have hcE := GlobalTheory.T.casimir_scalar_of_capelliDeterminant_eigenvalue _ _ E mu hn hEg hqE
  have hcF := fun t => GlobalTheory.T.casimir_scalar_of_capelliDeterminant_eigenvalue _ _ (F t) _ hn (hFg t)
    (GlobalTheory.T.quantum_determinant_eigenvalue hy k r ε _ (RI t) (hRI t) g⁻¹ (F t) hQ (hF t))
  have hsp := fun t => GlobalTheory.T.splitCasimir_eigenvalue_on_dualTensor_summand _ _ _ E (F t) (io' t) mu t hcE (hcF t) (hcomm t)
  let L : R.smSub →ₗ[ℂ] Wp :=
    { toFun := fun v => l v
      map_add' := fun v w => hB.1 _ v.2 _ w.2
      map_smul' := fun c v => hB.2.1 c _ v.2 }
  have hL : ∀ v : R.smSub, L v = l v := fun _ => rfl
  have hE' : ∀ a b (v : R.smSub), ((E a b v : R.smSub) : R.H) = R.dC (g * Matrix.single a b 1 * g⁻¹) v := by
    intro a b v
    rw [hE a b v, hgi]
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.projector_entry_value_under_linear_functional R.smSub Wp k r E L
    (fun a b => Formalism.QuantumDeterminants.ell k r z (g * Matrix.single a b 1 * g⁻¹) - star (Formalism.QuantumDeterminants.ell k r z
      (-((Formalism.QuantumDeterminants.Hpk k r) * (g * Matrix.single a b (1 : ℂ) * g⁻¹)ᴴ * (Formalism.QuantumDeterminants.Hpk k r)))))
    (Real.sqrt (Formalism.QuantumDeterminants.Tz k r z)) hk hEg
    (fun a b hab hnot => ⟨fun v => by
      rw [hL, hL, hE']
      exact GlobalTheory.T.bessel_functional_lie_triangular_eq_character_smul hK k r ε mu R hR Wp z π l hz (fun x => by rw [hπ1]; rfl) hB _ (hN a b hab hnot).1 _ v.2,
      (hN a b hab hnot).2⟩)
    mu u (fun i j => Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r)
      (fun i : Fin k => g *ᵥ Pi.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) 1) i j))
    hR.1.1.injective hqE
    (fun i j v => by
      rw [hL, hL, hE', hunit]
      exact GlobalTheory.T.bessel_frame_entry_relation hK k r ε mu R hR Wp z π l g hz hTz hg hB i j _ v.2)
    (fun w x => hcap _ hfr w x) s
  set a : ℂ := (if r = 0 then -((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) else 1) with ha
  set b : ℂ := (if r = 0 then ((Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) : ℝ) : ℂ) else 1) with hb
  set i₀ : Fin (2 * r + k + 1) := (if r = 0 then Fin.last (2 * r + k) else 0) with hi₀
  have hf' : g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z 0 = b • Pi.single i₀ 1 := by
    rw [hf, hb, hi₀]
    split_ifs <;> simp
  refine ⟨b * c * a, ?_, fun v hv => ?_⟩
  · rw [norm_mul, norm_mul, hc, ha, hb]
    have hsq : Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) ^ 2 = Formalism.QuantumDeterminants.Tz k r z := Real.sq_sqrt hTz.le
    have hab : |Real.sqrt (Formalism.QuantumDeterminants.Tz k r z)| = Real.sqrt (Formalism.QuantumDeterminants.Tz k r z) :=
      abs_of_nonneg (Real.sqrt_nonneg _)
    split_ifs
    · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, hab]
      generalize ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) = P
      linear_combination P * hsq
    · rw [hsq, norm_one, one_mul, mul_one]
  · let v' : R.smSub := ⟨v, hv⟩
    let x : Fin (2 * r + k + 1) → R.smSub := Pi.single (Fin.last (2 * r + k)) (a • v')
    have hx : ∀ d, ((x d : R.smSub) : R.H) = (gᵀ *ᵥ flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) d • v := by
      intro d
      rw [hω]
      by_cases h : d = Fin.last (2 * r + k)
      · subst h; simp [x, v']
      · simp [x, Pi.single_eq_of_ne h]
    have hp : ((pr' s x : (RI s).smSub) : (RI s).H) =
        ∑ d, pr s d (tm R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d) := by
      rw [hpr]
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [hx]
      rw [sum_coframe g hgu]
      rfl
    have hmain := hcv (a • v') (fun t => io' t (pr' t x)) (fun t => hsp t _) (hsum x)
    rw [ev_flat, sum_frame g hgu, ← hp, hf']
    have h3 : ∀ d, ∑ c', g c' d • io s c' ((pr' s x : (RI s).smSub) : (RI s).H) =
        ((io' s (pr' s x) d : R.smSub) : R.H) := by
      intro d
      rw [hio, hgi]
    simp only [h3]
    rw [Finset.sum_eq_single i₀ (fun d _ hd => by simp [Pi.single_eq_of_ne hd]) (by simp)]
    have h4 : (b • Pi.single i₀ (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) i₀ = b := by simp
    rw [h4]
    have h5 : l (b • ((io' s (pr' s x) i₀ : R.smSub) : R.H)) = b • L (io' s (pr' s x) i₀) :=
      hB.2.1 b _ (io' s (pr' s x) i₀).2
    rw [h5, hmain, map_smul, hL, smul_smul, smul_smul]

end GlobalTheory
end Gp91
end
end

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DualTensorBesselMomentStatement

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.Gp91.GlobalTheory.T.dual_tensor_bessel_moment : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (RI : Fin (2 * r + k + 1) → Rep k r) (io : ∀ s, Fin (2 * r + k + 1) → (RI s).H → R.H) (pr : ∀ s, Fin (2 * r + k + 1) → R.H → (RI s).H) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp), 1 ≤ k → R.IsDG ε mu → (∀ s, (RI s).IsDG ε (mu - Pi.single s 1)) → TensRaw dualM R RI io pr → SideG k r z π u μW μN μG νq → IsBes R z π l → ∀ s, ∃ c : ℂ, ‖c‖ = Formalism.QuantumDeterminants.Tz k r z * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ v ∈ R.sm, l (ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (fun c' => io s c' (∑ d, pr s d (tm R (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d)))) = c • l v := by
  first | exact @GlobalTheory.bessel_ev_projector_value | exact GlobalTheory.bessel_ev_projector_value | (intros; apply GlobalTheory.bessel_ev_projector_value <;> assumption)
end Gp91
end
end

-- Source module: CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.FamilySetupMomentGrowth

section

@[expose] public section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.DualStepBound

theorem lOneNorm_sub_single_one_le {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) :
    n1 (ν - Pi.single s 1 : Fin n → ℤ) ≤ n1 ν + 1 := by
  unfold n1
  have h1 : ∑ i, ((Pi.single s 1 : Fin n → ℤ) i).natAbs = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => by
    simpa using Int.natAbs_sub_le (ν i) ((Pi.single s 1 : Fin n → ℤ) i)

theorem sum_mem_sm {k r : ℕ} (R : Rep k r) {ι : Type} [Fintype ι] (x : ι → R.H) (hx : ∀ c, x c ∈ R.sm) :
    ∑ c, x c ∈ R.sm :=
  R.smSub.sum_mem (fun c _ => hx c)

theorem dual_step_bound : HypsG → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ), SetupG lam u b bv ga h q0 z π μW μN μG νq R l dg → ∀ ν, n1 ν + 1 ≤ q0 → ∀ io pr ep, TensH dualM (Formalism.QuantumDeterminants.Hpk k r) (R ν) (fun s => R (ν - Pi.single s 1)) io pr ep → NzOn (R ν) (l ν) → ∀ (s : Fin (2 * r + k + 1)) (κ₀ : ℂ), (∀ v ∈ (R ν).sm, l (ν - Pi.single s 1) (∑ c, pr s c (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v c)) = κ₀ • l ν v) → ‖κ₀‖ ^ 2 * dg ν / dg (ν - Pi.single s 1) ≤ Formalism.QuantumDeterminants.Tz k r z * b ^ 4 := by
  intro hH k r Wp _ _ _ _ lam u b bv ga h q0 z π μW μN μG νq R l dg hS ν hν io pr ep hT hnz s κ₀ hκ
  obtain ⟨hNum, hFam, hSide, hSF⟩ := hS
  have hν0 : n1 ν ≤ q0 := by omega
  have hν1 : ∀ t, n1 (ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) ≤ q0 :=
    fun t => (lOneNorm_sub_single_one_le ν t).trans hν
  have hDS : (R ν).IsDG _ _ := hFam ν hν0
  have hDS1 : ∀ t, (R (ν - Pi.single t 1)).IsDG (PI.BesselPeriodGGP.eps48 k r)
      (fun a => lam a + ((ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ)) := fun t => hFam _ (hν1 t)
  have hpar : ∀ t, (fun a => lam a + ((ν - Pi.single t 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ))
      = (fun a => lam a + (ν a : ℝ)) - Pi.single t 1 := by
    intro t
    funext a
    by_cases hat : a = t
    · subst hat
      simp
      ring
    · simp [Pi.single_eq_of_ne hat]
  have hDS2 : ∀ t, (R (ν - Pi.single t 1)).IsDG (PI.BesselPeriodGGP.eps48 k r)
      ((fun a => lam a + (ν a : ℝ)) - Pi.single t 1) := fun t => hpar t ▸ hDS1 t
  obtain ⟨hBe, hdg, hdeg⟩ := hSF ν hν0
  obtain ⟨hBe1, hdg1, hdeg1⟩ := hSF _ (hν1 s)
  obtain ⟨c, hc, hcv⟩ := GlobalTheory.T.dual_tensor_bessel_moment hH k r _ _ (R ν) (fun s => R (ν - Pi.single s 1)) io pr Wp z π u
    μW μN μG νq (l ν) hNum.1 hDS hDS2 hT.raw hSide hBe.1 s
  have hdual := (GlobalTheory.T.bessel_tensor_projection_scalar_and_adjoint hH k r _ _ dualM (Formalism.QuantumDeterminants.Hpk k r) 1 (R ν) (fun s => R (ν - Pi.single s 1))
    io pr ep _ _ _ Wp z π u μW μN μG νq (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) (l ν) hDS hDS2
    (GlobalTheory.isFRep_dualM k r) hT hSide
    (fun g hg => (GlobalTheory.FlagFix.fixes_wedge_and_form k r z hSide.1 g hg).2) hBe hnz s
    (l (ν - Pi.single s 1)) hBe1).2 κ₀ hκ
  obtain ⟨v, hv, hv0⟩ := hnz
  have hy : ∑ d, pr s d (tm (R ν) (flat k r (Formalism.QuantumDeterminants.fvec k r z 0)) v d) ∈ (R (ν - Pi.single s 1)).sm :=
    sum_mem_sm _ _ fun d => (hT.raw.pr_sm s d).mem _ ((R ν).smSub.smul_mem _ hv)
  have e1 := hdual _ hy
  rw [hcv v hv, hκ v hv, smul_smul] at e1
  have e2 : c = (ep s : ℂ) * star κ₀ * κ₀ := smul_left_injective ℂ hv0 e1
  have hep : ‖(ep s : ℂ)‖ = 1 := by
    rcases hT.ep_sq s with h' | h' <;> simp [h']
  have e3 : ‖κ₀‖ ^ 2 = ‖c‖ := by
    rw [e2, norm_mul, norm_mul, hep, norm_star]; ring
  obtain ⟨c₀, hc₀, hdegs⟩ := GlobalTheory.BesselDegree.schur_fdeg hH k r (PI.BesselPeriodGGP.eps48 k r) μG
    hSide.2.2.2.2.2.2.1
  have hKS : PI.KFinSmooth := hH.1.2.2.1
  have d0 : dg ν = c₀ * Formalism.QuantumDeterminants.fdegHC (fun a => lam a + (ν a : ℝ)) := by
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hKS k r _ _ _ hDS).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    rw [← hdeg w hw0, (hdegs _ _ hDS).1 w hw0]
  have d1 : dg (ν - Pi.single s 1) = c₀ * Formalism.QuantumDeterminants.fdegHC
      (fun a => lam a + ((ν - Pi.single s 1 : Fin (2 * r + k + 1) → ℤ) a : ℝ)) := by
    obtain ⟨w, hw, -⟩ := (GlobalTheory.rep_basic_of_isDS hKS k r _ _ _ (hDS1 s)).2.2.2.2.2.2.2.1
    have hw0 : w ≠ 0 := by rintro rfl; simp at hw
    rw [← hdeg1 w hw0, (hdegs _ _ (hDS1 s)).1 w hw0]
  have hratio := (GlobalTheory.FamilyDegreeRatio.degree_ratios k r lam u b bv ga h q0 hNum ν hν0).2.2 s
  have hp7 := GlobalTheory.PieriBound.lowering_bound k r lam u b bv ga h q0 hNum ν hν0 s
  have hgap := ((GlobalTheory.NumFam.num_fam k r lam u b bv ga h q0 hNum).2 ν hν0).2.2.2
  have hB : (∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))|) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun t ht => abs_ne_zero.2 ?_
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ht) with h' | h'
    · have := hgap t s h'
      linarith
    · have := hgap s t h'
      linarith
  rw [Finset.prod_div_distrib] at hratio
  have hq : dg ν / dg (ν - Pi.single s 1)
      = (∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - (lam t + (ν t : ℝ))|) /
        ∏ t ∈ univ.erase s, |lam s + (ν s : ℝ) - 1 - (lam t + (ν t : ℝ))| := by
    rw [d0, d1, mul_div_mul_left _ _ hc₀.ne', ← inv_div, hratio, inv_div]
  rw [mul_div_assoc, hq, e3, hc, mul_assoc, div_mul_div_cancel₀ hB]
  exact mul_le_mul_of_nonneg_left hp7 hSide.2.1.le

end GlobalTheory.DualStepBound
end Gp91
end
end
