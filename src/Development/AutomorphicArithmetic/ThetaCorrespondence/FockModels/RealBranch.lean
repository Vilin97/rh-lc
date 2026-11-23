module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.BigProjP
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealInputOfBranching
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchInput
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigOfLow
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntegrableSquare
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
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.LipschitzEstimate
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.LowestKTypeModels.Models
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.HolomorphicMoments.MomentHigherEstimateHolds
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.SchurFiniteDimensionality.IsFdOfSchurK
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.Occ
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RowsBij
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.RightRegularIsometricMultiplicative
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntegrableSquareStatement

section

@[expose] public section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.matrix_coefficient_integrable_square : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ b : B,
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
    ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound | exact GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound | (intros; apply GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMatrixCoefficientIntertwiner

section

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods PositivityTheory.RgHe.A
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA.TMapPf

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {ρ : Γ → (A →L[ℂ] A)}

theorem isU_inner (hU : IsU ρ) (g : Γ) (x y : A) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (ρ g).toLinearMap (hU.norm g)).inner_map_map x y

theorem isU_apply_inv (hU : IsU ρ) (g : Γ) (x : A) : ρ g (ρ g⁻¹ x) = x := by
  have h := hU.mul g g⁻¹
  rw [mul_inv_cancel, hU.one] at h
  have h2 := congrArg (fun T : A →L[ℂ] A => T x) h
  simpa using h2.symm

theorem isU_inner_left (hU : IsU ρ) (k : Γ) (x y : A) : ⟪ρ k x, y⟫_ℂ = ⟪x, ρ k⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← isU_apply_inv hU k y]
  exact isU_inner hU k x _

end Unitary

theorem norm_integral_mul_sq_le {Γ : Type} [MeasurableSpace Γ] (ν : Measure Γ) (f g : Γ → ℂ) (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) : ‖∫ x, f x * g x ∂ν‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2 ∂ν) * ∫ x, ‖g x‖ ^ 2 ∂ν := by
  have h1 := integral_mul_norm_le_Lp_mul_Lq (μ := ν) (f := f) (g := g) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
  have h0 : ‖∫ x, f x * g x ∂ν‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂ν := by
    simpa using norm_integral_le_integral_norm (μ := ν) (fun x => f x * g x)
  simp only [Real.rpow_two] at h1
  have hP : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  have hQ : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  calc ‖∫ x, f x * g x ∂ν‖ ^ 2
      ≤ ((∫ x, ‖f x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ)) * (∫ x, ‖g x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h0.trans h1) 2
    _ = _ := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hP, Real.sq_sqrt hQ]

section Main

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
  [InnerProductSpace ℂ B] [CompleteSpace B] {σ : Γ → (A →L[ℂ] A)} {ρ : Γ → (B →L[ℂ] B)} {d : ℝ}


omit [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] [SecondCountableTopology Γ] [ν.IsHaarMeasure] [ν.IsMulRightInvariant] [CompleteSpace A] in
theorem coeff_sq (hσ : IsU σ) (hF : IsFd ν σ d) (w a : A) :
    MemLp (fun g => ⟪σ g w, a⟫_ℂ) 2 ν ∧ ∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν = ‖a‖ ^ 2 * ‖w‖ ^ 2 / d := by
  have key : ∀ g, ⟪a, σ g w⟫_ℂ * star ⟪a, σ g w⟫_ℂ = ((‖⟪σ g w, a⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inner_symm]
  obtain ⟨h1, h2⟩ := hF.2 w a w a
  simp only [key] at h1 h2
  have h3 : Integrable (fun g => ‖⟪σ g w, a⟫_ℂ‖ ^ 2) ν := by
    exact h1.re.congr (ae_of_all _ fun g => Complex.ofReal_re _)
  have hc : Continuous fun g => ⟪σ g w, a⟫_ℂ := (hσ.cont w).inner continuous_const
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 h3, ?_⟩
  have e : ∀ x : A, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [integral_complex_ofReal, e, e] at h2
  have h4 : ((∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖a‖ ^ 2 * ‖w‖ ^ 2 / d : ℝ) : ℂ) := by
    rw [h2]; push_cast; ring
  exact_mod_cast h4

omit [CompleteSpace A] in
theorem form_facts (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) (b : B) (a : A) :
    Integrable (fun g => ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) ν ∧
      ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ^ 2 ≤
        ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) * (‖a‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨hb1, hb2⟩ := GlobalTheory.T.matrix_coefficient_integrable_square ν ρ hρ v hv b
  have hc : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hφ : MemLp (fun g => ⟪b, ρ g v⟫_ℂ) 2 ν := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 hb1
  obtain ⟨hψ, hψ2⟩ := coeff_sq ν hσ hF w a
  refine ⟨hφ.integrable_mul hψ, ?_⟩
  refine (norm_integral_mul_sq_le ν _ _ hφ hψ).trans ?_
  rw [hψ2]
  exact mul_le_mul_of_nonneg_right hb2 (div_nonneg (by positivity) hF.1.le)

theorem exists_matrix_coefficient_intertwiner (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) :
    ∃ T : B →L[ℂ] A, ∀ b a, ⟪T b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := by
  have hint := fun b a => (form_facts ν hρ hσ hF hv w b a).1
  have hM : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨K, hK0, hbd⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ b a, ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ≤ K * ‖b‖ * ‖a‖ := by
    refine ⟨Real.sqrt ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d), Real.sqrt_nonneg _, fun b a => ?_⟩
    have hq : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d := div_nonneg (by positivity) hF.1.le
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    refine (form_facts ν hρ hσ hF hv w b a).2.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hq]
    ring
  let L : B → (A →L[ℂ] ℂ) := fun b => LinearMap.mkContinuous
    { toFun := fun a => ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν
      map_add' := fun a a' => by
        rw [← integral_add (hint b a) (hint b a')]
        congr 1; ext g; rw [inner_add_right, mul_add]
      map_smul' := fun t a => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; ext g; rw [inner_smul_right]; ring } (K * ‖b‖) (fun a => hbd b a)
  let Tf : B → A := fun b => (InnerProductSpace.toDual ℂ A).symm (L b)
  have hT : ∀ b a, ⟪Tf b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := fun b a => by
    simp only [Tf, InnerProductSpace.toDual_symm_apply]
    rfl
  have hTb : ∀ b, ‖Tf b‖ ≤ K * ‖b‖ := fun b => by
    have h1 := hbd b (Tf b)
    rw [← hT, inner_self_eq_norm_sq_to_K] at h1
    by_cases h0 : ‖Tf b‖ = 0
    · rw [h0]; positivity
    · have h2 : 0 < ‖Tf b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have h3 : ‖Tf b‖ * ‖Tf b‖ ≤ (K * ‖b‖) * ‖Tf b‖ := by
        simpa [sq] using h1
      exact le_of_mul_le_mul_right h3 h2
  refine ⟨LinearMap.mkContinuous
    { toFun := Tf
      map_add' := fun b b' => ext_inner_right ℂ fun a => by
        rw [inner_add_left, hT, hT, hT, ← integral_add (hint b a) (hint b' a)]
        congr 1; ext g; rw [inner_add_left, add_mul]
      map_smul' := fun t b => ext_inner_right ℂ fun a => by
        simp only [RingHom.id_apply]
        rw [inner_smul_left, hT, hT, ← integral_const_mul]
        congr 1; ext g; rw [inner_smul_left]; ring } K hTb, fun b a => ?_⟩
  exact hT b a

end Main

theorem tMap : TMap := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hF v hv w c hc h
  obtain ⟨T, hT⟩ := exists_matrix_coefficient_intertwiner ν hρ hσ hF hv w
  have hk : ∀ k b, T (ρ k b) = σ k (T b) := fun k b => ext_inner_right ℂ fun a => by
    rw [hT, isU_inner_left hσ k, hT]
    refine (integral_mul_left_eq_self (μ := ν) (fun g => ⟪ρ k b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) k).symm.trans
      (integral_congr_ae (ae_of_all _ fun g => ?_))
    simp only [hρ.mul, hσ.mul, ContinuousLinearMap.mul_apply]
    rw [isU_inner hρ, isU_inner_left hσ]
  have hv' : T v = (c : ℂ) • w := ext_inner_right ℂ fun a => by
    rw [hT, inner_smul_left, Complex.conj_ofReal]
    have h1 := congrArg (starRingEnd ℂ) (h a)
    rw [← integral_conj] at h1
    simp only [map_mul, inner_conj_symm, Complex.conj_ofReal, Complex.star_def] at h1
    exact h1
  refine ⟨(c : ℂ)⁻¹ • T, fun g x => ?_, ?_⟩
  · simp [hk]
  · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [ContinuousLinearMap.smul_apply, hv', smul_smul, inv_mul_cancel₀ hc', one_smul]

end GlobalTheory.CompanionTheory.RgHeA.TMapPf
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.SeedBaseCases.SeedBOf

section

@[expose] public section

namespace PositivityTheory.RgHe.A.Pf

theorem seedB_of : PositivityTheory.RgHe.Seed → PositivityTheory.RgHe.Occ → PositivityTheory.RgHe.A.SchurEigenProjectionExists := by
  intro hS hO n ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν hν hF hP hπ hσ hW
  have hG : PositivityTheory.RgHe.Gp ε lam ε' mu e :=
    ⟨hF, hP.two, hP.neg, hP.le, hP.hc, hP.hc', hP.gap, hP.gap'⟩
  have hj := hO n ε lam ε' mu e hG hW H H' π σ hπ hσ
  exact hS n ε lam ε' mu e hG H H' π σ ν hν hπ hσ hj

end PositivityTheory.RgHe.A.Pf
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.RealBranch

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal
open scoped InnerProductSpace

namespace UpperTheory.Lit.Branch

variable {n : ℕ}

def sumNum (e : Option (Fin n) ≃ Fin (n + 1)) : Fin n ⊕ Unit ≃ Fin (n + 1) := (Equiv.optionEquivSumPUnit (Fin n)).symm.trans e

theorem emb_sumNum (e : Option (Fin n) ≃ Fin (n + 1)) (h : Mat n) : GlobalTheory.CompanionTheory.PairingAnalysis.emb (sumNum e) h = embH e h := by
  ext a b
  simp only [GlobalTheory.CompanionTheory.PairingAnalysis.emb, embH, sumNum, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_trans_apply, Equiv.symm_symm]
  rcases e.symm a with _ | i <;> rcases e.symm b with _ | j <;> simp [Equiv.optionEquivSumPUnit]

variable {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool}
  {mu : Fin n → ℝ} {B : ℝ}

theorem fits_of (hP : Par e ε lam ε' mu B) : GlobalTheory.CompanionTheory.PairingAnalysis.Fits ε ε' (sumNum e) := by
  refine ⟨?_, fun a => ?_⟩
  · simpa [GlobalTheory.CompanionTheory.PairingAnalysis.zi, sumNum, Equiv.optionEquivSumPUnit] using hP.signs.1
  · simpa [sumNum, Equiv.optionEquivSumPUnit] using hP.signs.2 a

theorem par_of (hP : Par e ε lam ε' mu B) : GlobalTheory.CompanionTheory.PairingAnalysis.Par ε lam ε' mu B := by
  have hs := hP.signs
  refine ⟨by linarith [hP.three_le], ?_, ?_, hP.hlam, hP.hmu, hP.bound.1, hP.bound.2, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hP.neg
    exact ⟨e (some i), by rw [hs.2 i, hi]⟩
  · calc #{a | ε a = false} ≤ #{i | ε' i = false} := by
          refine Finset.card_le_card_of_surjOn (fun i => e (some i)) ?_
          intro a ha
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
          cases hsa : e.symm a with
          | none =>
            have : a = e none := by rw [← hsa, Equiv.apply_symm_apply]
            rw [this, hs.1] at ha
            exact absurd ha (by decide)
          | some i =>
            have : a = e (some i) := by rw [← hsa, Equiv.apply_symm_apply]
            refine ⟨i, ?_, this.symm⟩
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
            rw [← hs.2 i, ← this, ha]
      _ ≤ #{i | ε' i = true} := hP.pos
      _ ≤ #{a | ε a = true} := by
          refine Finset.card_le_card_of_injOn (fun i => e (some i)) ?_ ?_
          · intro i hi
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
            rw [hs.2 i, hi]
          · intro i _ j _ hij
            simpa using hij
  · intro a b hab
    have h1 := hP.gap a b hab
    have h2 : (0 : ℝ) ≤ (↑n + 1) ^ 3 := by positivity
    linarith
  · intro a b hab
    have h1 := hP.gap' a b hab
    have h2 : (0 : ℝ) ≤ (↑n + 1) ^ 3 := by positivity
    linarith

theorem heWord_of (hP : Par e ε lam ε' mu B) : GlobalTheory.CompanionTheory.PairingAnalysis.HeWord ε lam ε' mu := by
  intro x y hxy hz
  have h := hP.word x y hxy hz
  simp only [ne_eq] at h
  tauto

private theorem exists_uj_umat_eq_of_mem_UJset {m : ℕ} {ε : Fin m → Bool} {h : Mat m} (hh : h ∈ UJset ε) :
    ∃ g : UJ ε, umat g = h := by
  have hJ : Jm ε * Jm ε = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  have h1 : (Jm ε * hᴴ * Jm ε) * h = 1 := by
    calc (Jm ε * hᴴ * Jm ε) * h = Jm ε * (hᴴ * Jm ε * h) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hh', hJ]
  exact ⟨⟨⟨h, Jm ε * hᴴ * Jm ε, mul_eq_one_comm.mp h1, h1⟩, hh⟩, rfl⟩

private theorem embH_mem_UJset_of_signs {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool}
    {ε' : Fin n → Bool} (hs : Signs e ε ε') {h : Mat n} (hh : h ∈ UJset ε') : embH e h ∈ UJset ε := by
  have hJ : Jm ε = embH e (Jm ε') := by
    ext a b
    have ha := e.apply_symm_apply a
    have hb := e.apply_symm_apply b
    simp only [embH, Formalism.REAL.Jm, Matrix.diagonal_apply]
    rcases hA : e.symm a with _ | i <;> rcases hB : e.symm b with _ | j <;> rw [hA] at ha <;>
      rw [hB] at hb <;> subst ha <;> subst hb <;> simp [hs.1, hs.2]
  have hC : (embH e h)ᴴ = embH e hᴴ := by
    ext a b
    simp only [embH, Matrix.conjTranspose_apply]
    rcases e.symm a with _ | i <;> rcases e.symm b with _ | j <;> simp
  rw [GlobalTheory.SepReal.ProjSm.mem_iff] at hh ⊢
  rw [hC, hJ, ← embH_mul, ← embH_mul, hh]

private theorem isU_comp_umat_of_isURepOn {m : ℕ} {ε : Fin m → Bool} {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] {ρ : Mat m → K →L[ℂ] K} (hρ : IsURepOn (UJset ε) ρ) :
    GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsU (fun g : UJ ε => ρ (umat g)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ρ 1 = 1
    exact hρ.1.1
  · intro a b
    have h := hρ.1.2 _ (GlobalTheory.SepReal.RealAsm.umat_mem ε a) _ (GlobalTheory.SepReal.RealAsm.umat_mem ε b)
    show ρ (umat a * umat b) = _
    rw [h]
    rfl
  · intro g x
    exact hρ.2.1 _ (GlobalTheory.SepReal.RealAsm.umat_mem ε g) x
  · intro x
    exact (hρ.2.2 x).comp_continuous (GlobalTheory.SepReal.RealAsm.continuous_umat ε)
      (GlobalTheory.SepReal.RealAsm.umat_mem ε)

private theorem isURepOn_embH_of_signs {e : Option (Fin n) ≃ Fin (n + 1)} {ε : Fin (n + 1) → Bool}
    {ε' : Fin n → Bool} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (hs : Signs e ε ε') {π : Mat (n + 1) → K →L[ℂ] K} (hπ : IsURepOn (UJset ε) π) :
    IsURepOn (UJset ε') (fun h => π (embH e h)) := by
  have hc : Continuous (embH e) := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [embH]
    rcases e.symm a with _ | i <;> rcases e.symm b with _ | j <;> first | fun_prop | exact continuous_const
  refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg v => hπ.2.1 _ (embH_mem_UJset_of_signs hs hg) v,
    fun v => (hπ.2.2 v).comp hc.continuousOn (fun h hh => embH_mem_UJset_of_signs hs hh)⟩
  · simp only [embH_one]
    exact hπ.1.1
  · simp only [embH_mul]
    exact hπ.1.2 _ (embH_mem_UJset_of_signs hs ha) _ (embH_mem_UJset_of_signs hs hb)

theorem projLarge_of (hS : PositivityTheory.RgHe.A.SchurEigenProjectionExists) (hB : PositivityTheory.RgHe.A.BigProjP) : ProjLarge := by
  unfold ProjLarge ForPair
  intro n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ v₀ hv₀
  haveI : CompleteSpace H := hπ.1
  haveI : CompleteSpace H' := hσ.1
  obtain ⟨d, hd⟩ := Formalism.MainNotions.BridgeCSchur.fdeg_of_DS mu σ hσ
  have hK : PositivityTheory.RgHe.SchurK ε' σ (muG ε') d⁻¹ := by
    refine ⟨inv_pos.2 hd.1, fun v w v' w' => ⟨(hd.2 v w v' w').1, ?_⟩⟩
    refine (hd.2 v w v' w').2.trans ?_
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  obtain ⟨S, hKS⟩ := hσ.2.2.2.2.2.1
  obtain ⟨x, hxS, hx0, -⟩ := hKS.2.2.2.1
  have hxL : x ∈ lowKSub ε' mu σ := by
    unfold Formalism.MainNotions.S.lowKSub
    exact Submodule.mem_sSup_of_mem hKS hxS
  set w : H' := ((‖x‖ : ℂ)⁻¹) • x with hwdef
  have hwL : w ∈ lowKSub ε' mu σ := Submodule.smul_mem _ _ hxL
  have hw1 : ‖w‖ = 1 := by
    rw [hwdef, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hx0)]
  have hfit := fits_of hP
  have hpar := par_of hP
  obtain ⟨hint, i, η, hiso, hieq, hη, hηi, hηa⟩ := hS n ε lam ε' mu B (sumNum e) H H' π σ (muG ε')
    inferInstance hfit hpar hπ hσ (heWord_of hP) d⁻¹ hK w hwL hw1
  obtain ⟨g₀, hg₀s, hg₀⟩ := hB n ε lam ε' mu B (sumNum e) H H' π σ (muG ε') inferInstance hfit hpar
    hπ hσ d⁻¹ hK w hwL hw1 hint i η hiso hieq hη hηi hηa v₀ hv₀.2 hv₀.1
  have hB1 := GlobalTheory.SepReal.RealAsm.one_le_B hP
  have hn : (0 : ℝ) ≤ n := n.cast_nonneg
  have hX : 0 ≤ 8 * ((n : ℝ) + 1) * B := by nlinarith
  refine ⟨i, ContinuousLinearMap.adjoint i,
    ⟨?_, hiso, fun v y => (ContinuousLinearMap.adjoint_inner_right i y v).symm⟩,
    umat g₀, GlobalTheory.SepReal.RealAsm.umat_mem ε g₀, ?_, ?_⟩
  · intro h hh y
    obtain ⟨g, rfl⟩ := exists_uj_umat_eq_of_mem_UJset hh
    have h2 := hieq g y
    rwa [emb_sumNum] at h2
  · rw [show (10 : ℝ) * ((n : ℝ) + 1) = ((10 * (n + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    show Real.sqrt (Formalism.REAL.hs (umat g₀)) ≤ _
    rw [← Real.sqrt_sq (pow_nonneg hX (10 * (n + 1)))]
    apply Real.sqrt_le_sqrt
    rw [← pow_mul]
    convert hg₀s using 2 <;> ring
  · have hL : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_nonneg (by nlinarith)
    have h1 : 1 ≤ big 100 n B *
        Real.exp (-(100 * ((n : ℝ) + 1) ^ 3 * Real.log (8 * ((n : ℝ) + 1) * B))) := by
      unfold big
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have h3 : 100 * ((n : ℝ) + 1) ^ 4 * Real.log (8 * ((n : ℝ) + 1) * B) +
          -(100 * ((n : ℝ) + 1) ^ 3 * Real.log (8 * ((n : ℝ) + 1) * B)) =
          100 * (((n : ℝ) + 1) ^ 3 * (n : ℝ) * Real.log (8 * ((n : ℝ) + 1) * B)) := by ring
      rw [h3]
      exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (by positivity) hn) hL)
    exact h1.trans (mul_le_mul_of_nonneg_left hg₀ (GlobalTheory.SepReal.RealAsm.big_pos _ _ _).le)

theorem eigMap_of (hE : PositivityTheory.RgHe.A.EigA) (hT : PositivityTheory.RgHe.A.TMap) : EigMap := by
  unfold EigMap ForPair
  intro n e ε lam ε' mu B hP H H' _ _ _ _ π σ hπ hσ d hd w₀ hw₀ hint j P hjP v hv hPv
  haveI : CompleteSpace H := hπ.1
  haveI : CompleteSpace H' := hσ.1
  have hU' : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsU (fun g : UJ ε' => σ (umat g)) := isU_comp_umat_of_isURepOn hσ.2.2.1
  have hU : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsU (fun g : UJ ε' => π (embH e (umat g))) :=
    isU_comp_umat_of_isURepOn (ρ := fun h => π (embH e h)) (isURepOn_embH_of_signs hP.signs hπ.2.2.1)
  have hFd : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsFd (muG ε') (fun g : UJ ε' => σ (umat g)) d := hd
  have hiso : GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods.IsIsoMap (fun g : UJ ε' => σ (umat g)) (fun g => π (embH e (umat g))) j :=
    ⟨fun g x => hjP.1 _ (GlobalTheory.SepReal.RealAsm.umat_mem ε' g) x, hjP.2.1⟩
  have hadj : ContinuousLinearMap.adjoint j = P := by
    symm
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro x y
    rw [← inner_conj_symm, ← hjP.2.2 x y]
    exact inner_conj_symm _ _
  obtain ⟨w, c, hw0, hc, hb⟩ := hE (muG ε') (fun g : UJ ε' => σ (umat g))
    (fun g => π (embH e (umat g))) d hU' hU hFd w₀ hw₀ hint j hiso v hv
  rw [hadj] at hc
  have hcpos : 0 < c :=
    lt_of_lt_of_le (div_pos (pow_pos (norm_pos_iff.2 hPv) 2) (by linarith [hd.1])) hc
  obtain ⟨T, hT, hTv⟩ := hT (muG ε') (fun g : UJ ε' => σ (umat g)) (fun g => π (embH e (umat g))) d
    hU' hU hFd v hv w c hcpos.ne' (fun b => (hb b).2)
  refine ⟨w, c, T, hw0, hc, fun b => (hb b).2, ?_, hTv⟩
  intro h hh x
  obtain ⟨g, rfl⟩ := exists_uj_umat_eq_of_mem_UJset hh
  exact hT g x

end UpperTheory.Lit.Branch

end

namespace UpperTheory.Lit

theorem realInputE_holds : Branch.RealInputE :=
  Branch.realInputE
    (Branch.projLarge_of (PositivityTheory.RgHe.A.Pf.seedB_of PositivityTheory.RgHe.LowestKTypeModel.seed PositivityTheory.RgHe.occ)
      (PositivityTheory.RgHe.A.Pf.bigProjP PositivityTheory.RgHe.A.Pf.momentP CompanionTheory.Lime.T3.analytic_estimates))
    (Branch.eigMap_of GlobalTheory.CompanionTheory.RgHeA.eigA GlobalTheory.CompanionTheory.RgHeA.TMapPf.tMap)

end UpperTheory.Lit
end
end
