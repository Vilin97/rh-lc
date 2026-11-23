module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchDefs
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.TopfBasis
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoostDecompositionNormBoundOfEmbeddingLawsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLoweringWeightRatioLeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeLieWordNormBoundStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKtypeCoefficientExplicitPowerDecayStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeNormPowerIntegrableOfBallVolumeStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealInputOfBranching
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientDerivativeIntegralBoundsOfLaStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslateCoefficientIntegralBoundsOfUnitaryLawsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryStabiliserEmbeddingNormLawsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolumeOfBallBoundStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProjectionSmooth
public import Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchVol
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesLowestKTypeUnitUnitaryFormalDegree

section

@[expose] public section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

namespace GlobalTheory.RowLev

theorem isDS_lowUnit_unitary_fdegOf : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsLowUnit ε lam σ w) ∧ (∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ) ∧ ∀ (c : NNReal) (d : ℝ) (w : H), 0 < c → ‖w‖ = 1 → IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d → fdegOf (Formalism.REAL.muG ε) σ w = c * d := by
  intro n ε lam H _ _ σ h
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hvS, hv, -⟩ := hS.2.2.2.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · have hle : S ≤ lowKSub ε lam σ := le_sSup hS
      exact hle (S.smul_mem _ hvS)
  · intro x a b
    have hx : uMat x ∈ UJset ε := x.2
    let f : H →ₗᵢ[ℂ] H := ⟨(σ (uMat x) : H →ₗ[ℂ] H), hU.2.1 _ hx⟩
    exact f.inner_map_map a b
  · intro c d w hc hw hF
    obtain ⟨hd, hI⟩ := hF
    have h1 := (hI w w w w).2
    have hc' : (0 : ℝ) < (c : ℝ) := hc
    have hww : ⟪w, w⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, hw]; simp
    have hpt : (fun g : Formalism.REAL.UJ ε => coefOn σ w w g * star (coefOn σ w w g))
        = fun g => ((‖coefOn σ w w g‖ ^ 2 : ℝ) : ℂ) := by
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [hpt, integral_smul_measure, integral_complex_ofReal, hww, ENNReal.coe_toReal,
      Complex.real_smul] at h1
    have h2 : (c : ℝ) * ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 * 1 / d := by
      exact_mod_cast h1
    have h3 : ∫ g, ‖coefOn σ w w g‖ ^ 2 ∂(Formalism.REAL.muG ε) = 1 / ((c : ℝ) * d) := by
      field_simp at h2 ⊢
      linarith
    unfold fdegOf
    rw [h3, hw]
    simp

end GlobalTheory.RowLev
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscreteSeriesLowestKTypeUnitUnitaryFormalDegreeStatement

section

@[expose] public section

open MeasureTheory Formalism.MainNotions.S Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Classical

theorem _root_.GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → (∃ w, IsLowUnit ε lam σ w) ∧ (∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ) ∧ ∀ (c : NNReal) (d : ℝ) (w : H), 0 < c → ‖w‖ = 1 → IsFdeg ((c : ENNReal) • Formalism.REAL.muG ε) σ d → fdegOf (Formalism.REAL.muG ε) σ w = c * d := by
  first | exact @GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf | exact GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf | (intros; apply GlobalTheory.RowLev.isDS_lowUnit_unitary_fdegOf <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchSmooth

section

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal UpperTheory.Lit.Branch
open scoped InnerProductSpace

open GlobalTheory.SepReal.ProjSm in
theorem UpperTheory.Lit.Branch.mapSmooth :
    MapSmooth := by
  intro n e ε lam ε' mu B hpar H H' _ _ _ _ π σ hπ hσ T hT v hv
  obtain ⟨-, -, -, -, -, -, hlie, hexp, -⟩ := GlobalTheory.T.unitary_stabiliser_embedding_norm_laws n e ε ε' hpar.signs
  intro k Xs hXs
  have key : (fun t : Fin k → ℝ => σ ((List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod) (T v)) =
      fun t => T (π ((List.ofFn fun i => NormedSpace.exp (t i • embL e (Xs i))).prod) v) := by
    funext t
    rw [← hT _ (list_mem _ (by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact exp_mem (hXs i) (t i))), embH_list, List.map_ofFn]
    simp only [Function.comp_def, hexp]
  rw [key]
  exact (T.restrictScalars ℝ).contDiff.comp (hv k (fun i => embL e (Xs i)) fun i => hlie _ (hXs i))
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.RealBands.BranchInput

section

@[expose] public section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell GlobalTheory.SepReal UpperTheory.Lit.Branch
open scoped InnerProductSpace

private theorem two_le_big_one (n : ℕ) {B : ℝ} (hB : 1 ≤ B) : 2 ≤ big 1 n B := by
  unfold big
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have h8 : (2 : ℝ) ≤ 8 * ((n : ℝ) + 1) * B := by nlinarith
  have hlog : Real.log 2 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := Real.log_le_log (by norm_num) h8
  have hlog0 : 0 ≤ Real.log (8 * ((n : ℝ) + 1) * B) := le_trans (Real.log_nonneg (by norm_num)) hlog
  have hp : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 4 := one_le_pow₀ hn
  have hx : Real.log 2 ≤ 1 * ((n : ℝ) + 1) ^ 4 * Real.log (8 * ((n : ℝ) + 1) * B) := by
    rw [one_mul]
    nlinarith
  calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ _ := Real.exp_le_exp.2 hx

private theorem vol_arith {V d r c b₁ b₂ b₃ : ℝ} (hd : 0 < d) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂) (hb₃ : 2 ≤ b₃)
    (hV : V ≤ b₁ / d) (hr : 1 ≤ b₂ * r) (hc : r ^ 2 / (2 * d) ≤ c) : V ≤ b₁ * b₂ * b₂ * b₃ * c := by
  have hc0 : 0 ≤ c := le_trans (by positivity) hc
  have hr2 : 1 ≤ (b₂ * r) ^ 2 := one_le_pow₀ hr
  calc V ≤ b₁ / d := hV
    _ ≤ b₁ * (b₂ * r) ^ 2 / d := by
        apply div_le_div_of_nonneg_right _ hd.le
        exact le_mul_of_one_le_right hb₁.le hr2
    _ = b₁ * b₂ * b₂ * 2 * (r ^ 2 / (2 * d)) := by
        field_simp
    _ ≤ b₁ * b₂ * b₂ * b₃ * c := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hb₃ (by positivity)) hc (by positivity)
        have : (0 : ℝ) ≤ b₃ := by linarith
        positivity

open GlobalTheory.SepReal.RealAsm in
theorem UpperTheory.Lit.Branch.realInputE :
    ProjLarge → EigMap → RealInputE := by
  intro hPL hEM
  unfold ProjLarge at hPL
  unfold EigMap at hEM
  obtain ⟨C1, hC1, hIB⟩ := GlobalTheory.T.translateCoefficientIntegralBounds_of_unitary_laws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws (GlobalTheory.T.boostDecompositionNormBound_of_embeddingLaws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws)
    (GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume GlobalTheory.T.volume_of_ball_bound) GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay 10 (by norm_num)
  obtain ⟨C3, hC3, hDB⟩ := GlobalTheory.T.translateCoefficientDerivativeIntegralBounds_of_laws GlobalTheory.T.unitary_stabiliser_embedding_norm_laws (GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume GlobalTheory.T.volume_of_ball_bound)
    GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay GlobalTheory.T.lowestKType_lieWord_normBound 10 (by norm_num)
  obtain ⟨C2, hC2, hVD⟩ := volDeg
  have hDR := GlobalTheory.T.formalDegree_loweringWeight_ratio_le
  have hMS := mapSmooth
  have hLBall := GlobalTheory.T.lowestKType_lieWord_normBound
  unfold ForPair at hPL hEM hIB hDB hVD hMS hDR
  unfold DegRatio at hDR
  unfold MapSmooth at hMS
  unfold LieBound ForDS at hLBall
  unfold RealInputE ForPair
  refine ⟨C1 + C3 + C2 + 201, by linarith, ?_⟩
  intro n e ε lam ε' mu B hpar H H' _ _ _ _ π σ hπ hσ
  have hB : 1 ≤ B := one_le_B hpar
  obtain ⟨⟨v₀, hv₀⟩, -, -⟩ := GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree (n + 1) ε lam H π hπ
  obtain ⟨j, P, hjP, g₀, hg₀, hg₀n, hbig⟩ := hPL n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀
  obtain ⟨d', hd'⟩ := (hDR n e ε lam ε' mu B hpar H H' π σ hπ hσ).1
  obtain ⟨⟨w₀, hw₀⟩, -, -⟩ := GlobalTheory.T.discreteSeries_lowestKType_unit_unitary_formalDegree n ε' mu H' σ hσ
  have hnn : (n : ℝ) ^ 3 ≤ ((n : ℝ) + 1) ^ 3 := by
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    gcongr
    linarith
  have hgap' : GapAtLeast ε' mu (1000 * (n : ℝ) ^ 3) := gap_mono (by linarith) hpar.gap'
  have hw₀int := integrable_low_coef GlobalTheory.T.lowest_Ktype_coefficient_explicit_power_decay (GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume GlobalTheory.T.volume_of_ball_bound) ε' mu B hpar.three_le
    hpar.hmu hgap' hpar.bound.2 σ hσ w₀ hw₀
  have hIBv := hIB n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀ g₀ hg₀ hg₀n
  have hvint : Integrable (fun h => ⟪π g₀ v₀, π (embH e (umat h)) (π g₀ v₀)⟫_ℂ) (muG ε') := by
    have hi := (hIBv.1 1 (one_mem ε)).1
    simpa using hi
  have hPv : P (π g₀ v₀) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at hbig
    linarith
  obtain ⟨w, c, T, hw0, hcP, hcoef, hT, hTv⟩ :=
    hEM n e ε lam ε' mu B hpar H H' π σ hπ hσ d' hd' w₀ hw₀.1 hw₀int j P hjP (π g₀ v₀) hvint hPv
  have hd'pos : 0 < d' := hd'.1
  have hPvpos : 0 < ‖P (π g₀ v₀)‖ := norm_pos_iff.2 hPv
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hcP
  have hLB := hLBall (n + 1) ε lam B (by have := hpar.three_le; omega) hpar.hlam
    (by push_cast; exact hpar.gap) hpar.bound.1 H π hπ v₀ hv₀
  have hsmv : SmV (GlobalTheory.Ell.lieOf (Jm ε)) π (π g₀ v₀) := smV_translate hπ hg₀ hLB.1
  have hsmw : SmV (GlobalTheory.Ell.lieOf (Jm ε')) σ w := by
    rw [← hTv]
    exact hMS n e ε lam ε' mu B hpar H H' π σ hπ hσ T hT (π g₀ v₀) hsmv
  have hwn : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hw'n : ‖((‖w‖ : ℂ)⁻¹) • w‖ = 1 := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hwn.le, inv_mul_cancel₀ hwn.ne']
  have hw'w' : ⟪((‖w‖ : ℂ)⁻¹) • w, ((‖w‖ : ℂ)⁻¹) • w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw'n]
    simp
  have hVb : ((muG ε') (nbh ε' (1 / 4))).toReal ≤ c * big (C2 + 100 + 100 + 1) n B := by
    have h1 := hVD n e ε lam ε' mu B hpar H H' π σ hπ hσ d' hd'
    have h2 := vol_arith hd'pos (big_pos C2 n B) (big_pos 100 n B) (two_le_big_one n hB) h1 hbig hcP
    rw [big_mul, big_mul, big_mul, mul_comm] at h2
    exact h2
  refine ⟨v₀, π g₀ v₀, g₀, ((‖w‖ : ℂ)⁻¹) • w, c, hv₀, hg₀, rfl, hsmv, smV_const_smul _ hsmw, hw'n, hcpos,
    ?_, ?_, ?_, hIBv.2⟩
  · intro b
    have hin : ∀ h : ↥(UJ ε'), ⟪b, σ (umat h) (((‖w‖ : ℂ)⁻¹) • w)⟫_ℂ = (‖w‖ : ℂ)⁻¹ * ⟪b, σ (umat h) w⟫_ℂ := by
      intro h
      rw [map_smul, inner_smul_right]
    simp_rw [hin, mul_left_comm _ ((‖w‖ : ℂ)⁻¹)]
    rw [integral_const_mul, hcoef b, hw'w', inner_smul_right]
    ring
  · intro g hg
    obtain ⟨hint, hle⟩ := hIBv.1 g hg
    refine ⟨hint, hle.trans ?_⟩
    have hcl : 0 ≤ colLen e g := by
      unfold colLen
      positivity
    have hX : 0 ≤ colLen e g ^ (-(2 * (n : ℝ) + 7)) := by
      first
        | exact Real.rpow_nonneg hcl _
        | exact zpow_nonneg hcl _
        | positivity
    apply mul_le_mul_of_nonneg_right _ hX
    calc ((muG ε') (nbh ε' (1 / 4))).toReal * big C1 n B
        ≤ c * big (C2 + 100 + 100 + 1) n B * big C1 n B :=
          mul_le_mul_of_nonneg_right hVb (big_pos _ _ _).le
      _ = c * big (C2 + 100 + 100 + 1 + C1) n B := by rw [mul_assoc, big_mul]
      _ ≤ c * big (C1 + C3 + C2 + 201) n B :=
          mul_le_mul_of_nonneg_left (big_mono (by linarith) n hB) hcpos.le
  · intro X hX hXn
    obtain ⟨hint, hle⟩ := hDB n e ε lam ε' mu B hpar H H' π σ hπ hσ v₀ hv₀ g₀ hg₀ hg₀n X hX hXn
    refine ⟨hint, hle.trans ?_⟩
    calc ((muG ε') (nbh ε' (1 / 4))).toReal * big C3 n B
        ≤ c * big (C2 + 100 + 100 + 1) n B * big C3 n B :=
          mul_le_mul_of_nonneg_right hVb (big_pos _ _ _).le
      _ = c * big (C2 + 100 + 100 + 1 + C3) n B := by rw [mul_assoc, big_mul]
      _ ≤ c * big (C1 + C3 + C2 + 201) n B :=
          mul_le_mul_of_nonneg_left (big_mono (by linarith) n hB) hcpos.le
end
end
