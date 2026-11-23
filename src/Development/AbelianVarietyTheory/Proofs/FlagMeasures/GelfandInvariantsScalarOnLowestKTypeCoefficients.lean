module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContDiffExtensionOfIsClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.LocallyConvex.Barrelled
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslation
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KMapLowestKTypeSubspaceEqScalar
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativesCoefficientsConvolutionFixedVector

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff Topology Pointwise

namespace GlobalTheory.DerivConv

theorem exists_weak_deriv {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (c : ℝ → H) (hc : ∀ u, DifferentiableAt ℝ (fun t => ⟪u, c t⟫_ℂ) 0) :
    ∃ v : H, ∀ u, deriv (fun t => ⟪u, c t⟫_ℂ) 0 = ⟪u, v⟫_ℂ := by
  have h : Filter.Tendsto (fun (t : ℝ) (u : H) => innerSL ℂ (slope c 0 t) u) (𝓝[≠] 0)
      (𝓝 fun u => (starRingEnd ℂ) (deriv (fun t => ⟪u, c t⟫_ℂ) 0)) := by
    refine tendsto_pi_nhds.2 fun u => ?_
    have h1 := (Complex.continuous_conj.tendsto _).comp (hc u).hasDerivAt.tendsto_slope
    refine h1.congr fun t => ?_
    simp only [Function.comp, innerSL_apply_apply]
    rw [← inner_conj_symm (slope c 0 t) u]
    congr 1
    simp only [slope_def_module, inner_sub_right, ← Complex.coe_smul, inner_smul_right, smul_eq_mul]
  let L : H →L[ℂ] ℂ := continuousLinearMapOfTendsto (fun t : ℝ => innerSL ℂ (slope c 0 t)) h
  refine ⟨(InnerProductSpace.toDual ℂ H).symm L, fun u => ?_⟩
  rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
  exact (Complex.conj_conj _).symm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

theorem differentiableAt_curve {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    DifferentiableAt ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) 0 := by
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  obtain ⟨U, F, hU, hg, hF, hfF⟩ := hf 1 h1
  have hγ := hasDerivAt_mul_exp_smul_zero 1 X
  simp only [Matrix.one_mul] at hγ
  have hγ0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F 1 :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.differentiableAt.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
  filter_upwards [hmem] with t ht
  exact hfF _ ht (exp_indefinite_unitary_holds n ε X hX t)

theorem smooth_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (h : ∀ g, inUJ ε g → f g = f' g) : SmoothOnG ε f' := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  exact ⟨U, F, hU, hgU, hF, fun x hx hxJ => (h x hxJ).symm.trans (e x hx hxJ)⟩

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_Rd (hσ : IsURepOn (UJset ε) σ) {s : H} (hs : ∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    ∃ v : H, ∀ u, ∀ g, inUJ ε g → Rd X (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g v⟫_ℂ := by
  obtain ⟨v, hv⟩ := exists_weak_deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) s)
    fun u => differentiableAt_curve (hs u) hX
  refine ⟨v, fun u g hg => ?_⟩
  rw [← ContinuousLinearMap.adjoint_inner_left, ← hv]
  unfold Rd
  congr 1
  funext t
  beta_reduce
  rw [hσ.1.2 g hg _ (exp_indefinite_unitary_holds n ε X hX t), ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem exists_Eword (hσ : IsURepOn (UJset ε) σ) {s : H} (hs : ∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ))
    (w : List (Fin n × Fin n)) :
    ∃ s' : H, (∀ u, SmoothOnG ε (fun g => ⟪u, σ g s'⟫_ℂ)) ∧
      ∀ u, ∀ g, inUJ ε g → Eword ε w (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
  induction w with
  | nil => exact ⟨s, hs, fun _ _ _ => rfl⟩
  | cons p w ih =>
    obtain ⟨s', hs', e⟩ := ih
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    obtain ⟨v₁, h₁⟩ := exists_Rd hσ hs' hc.1
    obtain ⟨v₂, h₂⟩ := exists_Rd hσ hs' hc.2.1
    refine ⟨v₁ + Complex.I • v₂, fun u g hg => ?_, fun u g hg => ?_⟩
    · obtain ⟨U, F, hU, hgU, hF, e⟩ := smooth_congr (rdSmooth_of right_derivative_extends n ε _ _ (hs' u) hc.1) (h₁ u) g hg
      obtain ⟨U', F', hU', hgU', hF', e'⟩ :=
        smooth_congr (rdSmooth_of right_derivative_extends n ε _ _ (hs' u) hc.2.1) (h₂ u) g hg
      refine ⟨U ∩ U', fun h => F h + Complex.I * F' h, hU.inter hU', ⟨hgU, hgU'⟩,
        (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right)), ?_⟩
      intro x hx hxJ
      simp only [← e x hx.1 hxJ, ← e' x hx.2 hxJ, map_add (f := _), map_smul, inner_add_right, inner_smul_right]
    · refine (Eword_congr ε (e u) [p] g hg).trans ?_
      simp only [Eword, Eab, Ec, id, h₁ u g hg, h₂ u g hg, map_add (f := _), map_smul, inner_add_right, inner_smul_right]

theorem smooth_coef (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} {s : H}
    (hα : SmoothOnG ε α) (hαc : HasCompactSupport (fun g : UJ ε => α (umat g)))
    (hfix : ∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ) (u : H) :
    SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := isClosedEmbeddingMatrix n ε
  obtain ⟨F, hF, hFα⟩ := GlobalTheory.smoothOnG_exists_contDiff_extension n ε α hα
  have hmem : ∀ g : UJ ε, inUJ ε (umat g) := fun g => g.2
  have hu : Continuous fun g : UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : UJ ε => ⟪u, σ (umat g) s⟫_ℂ :=
    continuous_const.inner ((hcont s).comp_continuous hu hmem)
  have hlift : ∀ x, inUJ ε x → ∃ z : UJ ε, umat z = x := fun x hx => by
    have : x ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [show Set.range (fun g : UJ ε => umat g) = _ from hrange]; exact hx
    exact this
  have hinv : ∀ z : UJ ε, Jm ε * (umat z)ᴴ * Jm ε = umat z⁻¹ := fun z => by
    have h : (umat z)ᴴ * Jm ε * umat z = Jm ε := hmem z
    have i2 : umat z * umat z⁻¹ = 1 := Units.mul_inv _
    calc Jm ε * (umat z)ᴴ * Jm ε = Jm ε * (umat z)ᴴ * Jm ε * (umat z * umat z⁻¹) := by rw [i2, Matrix.mul_one]
      _ = Jm ε * ((umat z)ᴴ * Jm ε * umat z) * umat z⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Jm_mul_self, Matrix.one_mul]
  have hform : ∀ z : UJ ε, ⟪u, σ (umat z) s⟫_ℂ
      = ∫ g : UJ ε, α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro z
    rw [← ContinuousLinearMap.adjoint_inner_left, ← hfix,
      ← integral_mul_left_eq_self (fun g : UJ ε => α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : umat (z * g) = umat z * umat g := rfl
    simp only [inv_mul_cancel_left, e]
    rw [hmul _ (hmem z) _ (hmem g), ContinuousLinearMap.adjoint_inner_left]
    rfl
  intro g₀ hg₀
  have hC : IsCompact ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) :=
    hemb.isCompact_preimage (isCompact_closedBall g₀ 1)
  have hK := hC.mul hαc
  set K := ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) * tsupport (fun g : UJ ε => α (umat g))
  have hΨ : ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
      F (fun i j => (Jm ε * z.1ᴴ * Jm ε * z.2.1) i j) * z.2.2 := by
    refine ContDiff.mul (hF.comp ?_) (contDiff_snd.comp contDiff_snd)
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    have e1 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        star (z.1 a b) := fun a b =>
      Complex.conjCLE.contDiff.comp ((contDiff_apply_apply (𝕜 := ℝ) a b).comp contDiff_fst)
    have e2 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        z.2.1 a b := fun a b =>
      (contDiff_apply_apply (𝕜 := ℝ) a b).comp (contDiff_fst.comp contDiff_snd)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact ContDiff.sum fun a _ => (ContDiff.sum fun b _ => (ContDiff.sum fun c _ =>
      contDiff_const.mul (e1 _ _)).mul contDiff_const).mul (e2 _ _)
  refine ⟨Metric.ball g₀ 1, fun x => ∫ g in K, F (fun i j => (Jm ε * xᴴ * Jm ε * umat g) i j) *
    ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε), Metric.isOpen_ball, Metric.mem_ball_self one_pos, ?_, ?_⟩
  · exact (contDiff_infty.2 fun m =>
      GlobalTheory.GardingVec.contDiff_setIntegral_nat (muG ε) hK (hu.prodMk hb) m _ hΨ).contDiffOn
  · intro x hx hxJ
    obtain ⟨z, rfl⟩ := hlift x hxJ
    have e : ∀ g : UJ ε, F (fun i j => (Jm ε * (umat z)ᴴ * Jm ε * umat g) i j) = α (umat (z⁻¹ * g)) := fun g => by
      rw [hinv]; exact hFα _ (hmem (z⁻¹ * g))
    simp only [e]
    rw [hform z]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra hne
    exact hg ⟨z, Metric.ball_subset_closedBall hx, z⁻¹ * g,
      subset_tsupport _ fun h => hne (by rw [show α (umat (z⁻¹ * g)) = 0 from h, zero_mul]),
      mul_inv_cancel_left z g⟩

theorem derivConv : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ) → (∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ)) ∧ ∀ w : List (Fin n × Fin n), ∃ s' : H, ∀ u, ∀ g ∈ UJset ε, Eword ε w (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
  intro n ε H _ _ _ σ α s hσ hα hαc hfix
  have hs := smooth_coef hσ hα hαc hfix
  refine ⟨hs, fun w => ?_⟩
  obtain ⟨s', -, h⟩ := exists_Eword hσ hs w
  exact ⟨s', h⟩

end GlobalTheory.DerivConv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativesCoefficientsConvolutionFixedVectorStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.derivatives_coefficients_convolutionFixed_vector : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ) → (∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ)) ∧ ∀ w : List (Fin n × Fin n), ∃ s' : H, ∀ u, ∀ g ∈ UJset ε, Eword ε w (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
  first | exact @GlobalTheory.DerivConv.derivConv | exact GlobalTheory.DerivConv.derivConv | (intros; apply GlobalTheory.DerivConv.derivConv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKTypeStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.exists_smooth_compactSupport_fix_lowestKType : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ α : Matrix (Fin n) (Fin n) ℂ → ℂ, SmoothOnG ε α ∧ HasCompactSupport (fun g : UJ ε => α (umat g)) ∧ ∀ s ∈ lowKSub ε lam σ, ∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ := by
  first | exact @GlobalTheory.exists_smooth_fix_lowKSub | exact GlobalTheory.exists_smooth_fix_lowKSub | (intros; apply GlobalTheory.exists_smooth_fix_lowKSub <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantCommRightTranslationStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.gelfandInvariant_comm_rightTranslation : ∀ (n : ℕ) (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) (k g : Matrix (Fin n) (Fin n) ℂ), SmoothOnG ε f → k ∈ UJset ε → g ∈ UJset ε → gelf ε m (fun x => f (x * k)) g = gelf ε m f (g * k) := by
  first | exact @GlobalTheory.Dec.GelfAd.gelf_right | exact GlobalTheory.Dec.GelfAd.gelf_right | (intros; apply GlobalTheory.Dec.GelfAd.gelf_right <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.KMapLowestKTypeSubspaceEqScalarStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

theorem _root_.GlobalTheory.T.kMap_lowestKTypeSubspace_eq_scalar : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∀ T : lowKSub ε lam σ →ₗ[ℂ] H, (∀ k ∈ Kset ε, ∀ s s' : lowKSub ε lam σ, (s' : H) = σ k s → T s' = σ k (T s)) → ∃ c : ℂ, ∀ s, T s = c • (s : H) := by
  first | exact @GlobalTheory.KMapInto.kMap_lowKSub_scalar | exact GlobalTheory.KMapInto.kMap_lowKSub_scalar | (intros; apply GlobalTheory.KMapInto.kMap_lowKSub_scalar <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.GelfandInvariantsScalarOnLowestKTypeCoefficients

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.CentreLow

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem smooth_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') : SmoothOnG ε (fun h => f h + c * f' h) := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  obtain ⟨U', F', hU', hgU', hF', e'⟩ := hf' g hg
  refine ⟨U ∩ U', fun h => F h + c * F' h, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right)), ?_⟩
  intro x hx hxJ
  simp only [e x hx.1 hxJ, e' x hx.2 hxJ]

theorem smooth_word {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (w : List (Fin n × Fin n)) : SmoothOnG ε (Eword ε w f) := by
  induction w with
  | nil => exact hf
  | cons p w ih =>
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    exact smooth_comb Complex.I (rdSmooth_of right_derivative_extends n ε _ _ ih hc.1)
      (rdSmooth_of right_derivative_extends n ε _ _ ih hc.2.1)

theorem word_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (w : List (Fin n × Fin n)) :
    ∀ g, inUJ ε g → Eword ε w (fun h => f h + c * f' h) g = Eword ε w f g + c * Eword ε w f' g := by
  induction w with
  | nil => intro g _; rfl
  | cons p w ih =>
    intro g hg
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    have h1 := Eword_congr ε ih [p] g hg
    have h2 := fun X hX => (right_derivative_linear n ε _ _ X X 0 c g (smooth_word hf w) (smooth_word hf' w) hX hX hg).2.2
    refine Eq.trans h1 ?_
    simp only [Eword, Eab, Ec, id, h2 _ hc.1, h2 _ hc.2.1]
    ring

theorem gelf_comb {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ)
    (hf : SmoothOnG ε f) (hf' : SmoothOnG ε f') (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    gelf ε m (fun h => f h + c * f' h) g = gelf ε m f g + c * gelf ε m f' g := by
  simp only [gelf, word_comb c hf hf' _ g hg, Finset.sum_add_distrib, Finset.mul_sum]

theorem gelf_congr {ε : Fin n → Bool} {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g, inUJ ε g → f g = f' g) (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    gelf ε m f g = gelf ε m f' g :=
  Finset.sum_congr rfl fun _ _ => Eword_congr ε h _ g hg

theorem centre_scalar_low : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → ∃ c : ℕ → ℂ, ∀ s ∈ lowKSub ε lam σ, ∀ u : H, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) ∧ ∀ m, ∀ g ∈ UJset ε, gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) g = c m * ⟪u, σ g s⟫_ℂ := by
  intro n ε lam H _ _ _ σ hσ hK
  obtain ⟨α, hα, hαc, hfix⟩ := GlobalTheory.T.exists_smooth_compactSupport_fix_lowestKType n ε lam H σ hσ hK
  have hD := fun (s : lowKSub ε lam σ) => GlobalTheory.T.derivatives_coefficients_convolutionFixed_vector n ε H σ α s hσ hα hαc (hfix s s.2)
  have hsm : ∀ (s : lowKSub ε lam σ) (u : H), SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) := fun s => (hD s).1
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by simp [UJset, inUJ]
  have hone : ∀ v, σ 1 v = v := fun v => by rw [hσ.1.1]; rfl
  have hmul : ∀ a ∈ UJset ε, ∀ b ∈ UJset ε, ∀ v, σ (a * b) v = σ a (σ b v) := fun a ha b hb v => by
    rw [hσ.1.2 a ha b hb]; rfl
  have hC : ∀ (m : ℕ) (s : lowKSub ε lam σ), ∃ s' : H, ∀ u, ∀ g ∈ UJset ε,
      gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
    intro m s
    choose v hv using (hD s).2
    refine ⟨∑ a : Fin (m + 1) → Fin n, v (cycWord a), fun u g hg => ?_⟩

    simp only [gelf, hv _ u g hg, map_sum, inner_sum]
  choose C hC using hC
  have hC1 : ∀ (m : ℕ) (s : lowKSub ε lam σ) (u : H),
      ⟪u, C m s⟫_ℂ = gelf ε m (fun x => ⟪u, σ x s⟫_ℂ) 1 := fun m s u => by rw [hC m s u 1 h1, hone]
  have hlin : ∀ (m : ℕ) (c : ℂ) (s t : lowKSub ε lam σ), C m (s + c • t) = C m s + c • C m t := by
    intro m c s t
    refine ext_inner_left ℂ fun u => ?_
    rw [inner_add_right, inner_smul_right, hC1, hC1, hC1, ← gelf_comb c (hsm s u) (hsm t u) m 1 h1]
    simp [inner_add_right, inner_smul_right]
  have h0 : ∀ m, C m 0 = 0 := fun m => by simpa using hlin m 1 0 0
  have key : ∀ m, ∃ c : ℂ, ∀ s : lowKSub ε lam σ, C m s = c • (s : H) := by
    intro m
    refine GlobalTheory.T.kMap_lowestKTypeSubspace_eq_scalar n ε lam H σ hσ hK
      { toFun := C m
        map_add' := fun s t => by simpa using hlin m 1 s t
        map_smul' := fun c t => by simpa [h0] using hlin m c 0 t } ?_
    intro k hk s s' e
    have hkU : k ∈ UJset ε := (maximal_compact_facts n ε).1 k hk
    refine ext_inner_left ℂ fun u => ?_
    change ⟪u, C m s'⟫_ℂ = ⟪u, σ k (C m s)⟫_ℂ
    rw [hC1, ← hC m s u k hkU, ← Matrix.one_mul k,
      ← GlobalTheory.T.gelfandInvariant_comm_rightTranslation n ε m _ k 1 (hsm s u) hkU h1]
    refine gelf_congr (fun g hg => ?_) m 1 h1
    rw [e, hmul g hg k hkU]
  choose c hc using key
  refine ⟨c, fun s hs u => ⟨hsm ⟨s, hs⟩ u, fun m g hg => ?_⟩⟩
  rw [hC m ⟨s, hs⟩ u g hg, hc, map_smul, inner_smul_right]

end GlobalTheory.CentreLow
end
end
