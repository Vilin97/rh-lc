module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandCLMInfApply
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import GroundTheory.AutomorphicForms.RealGroupsHaar
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanModerateGrowthMatrixSmoothingIntegr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArchimedeanRapidKernelOperatorFinsetSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralBoundSmoothStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralArchimedeanMatricesLeftMulJacobian

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf

theorem integral_eq_integral_mulLeft_matrixInf (E : Type) [Field E] [NumberField E] (n : ℕ)
    (A : GL (Fin n) (Cinf E)) (F : (Fin n → Fin n → Cinf E) → ℂ) :
    ∫ a, F a = ∫ h : (Fin n → Fin n → Cinf E), ((jacInf (A : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
      F (fun i j => ((A : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) := by
  set W := InfinitePlace E
  set M : Matrix (Fin n) (Fin n) (Cinf E) := (A : Matrix (Fin n) (Fin n) (Cinf E)) with hM
  set L : (Fin n → Fin n → Cinf E) →ₗ[ℝ] (Fin n → Fin n → Cinf E) :=
    { toFun := fun x i j => (M * Matrix.of x) i j
      map_add' := fun x y => by
        funext i j
        change (M * (Matrix.of x + Matrix.of y)) i j = (M * Matrix.of x) i j + (M * Matrix.of y) i j
        rw [mul_add, Matrix.add_apply]
      map_smul' := fun c x => by
        funext i j
        change (M * (c • Matrix.of x)) i j = c • (M * Matrix.of x) i j
        rw [Matrix.mul_smul, Matrix.smul_apply] } with hLdef
  have hL : ∀ h, L h = fun i j => (M * Matrix.of h) i j := fun h => rfl

  let e : (Fin n → Fin n → Cinf E) ≃ₗ[ℝ] (W → Fin n → Fin n → ℂ) :=
    { toFun := fun h w i j => h i j w
      invFun := fun g i j w => g w i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let Lw : W → (Fin n → Fin n → ℂ) →ₗ[ℝ] (Fin n → Fin n → ℂ) := fun w =>
    (LinearMap.mulLeft ℂ (M.map (fun z => z w))).restrictScalars ℝ
  have hconj : (e : _ →ₗ[ℝ] _) ∘ₗ L ∘ₗ (e.symm : _ →ₗ[ℝ] _) =
      LinearMap.pi (fun w => Lw w ∘ₗ LinearMap.proj w) := by
    apply LinearMap.ext; intro g; funext w i j
    change (M * Matrix.of (fun i j w => g w i j)) i j w = (M.map (fun z => z w) * Matrix.of (g w)) i j
    simp [Matrix.mul_apply, Finset.sum_apply, Matrix.map_apply]
  have hdetw : ∀ w, LinearMap.det (Lw w) = Complex.normSq (M.det w) ^ n := by
    intro w
    have := GroundTheory.Automorphic.det_restrictScalars_mulLeft (M.map (fun z => z w))
    rw [Fintype.card_fin, ← Complex.normSq_eq_norm_sq] at this
    show LinearMap.det ((LinearMap.mulLeft ℂ (M.map fun z => z w)).restrictScalars ℝ) = _
    rw [this]
    congr 2
    exact (RingHom.map_det (Pi.evalRingHom (fun _ : W => ℂ) w) M).symm
  have hdet : LinearMap.det L = jacInf M := by
    rw [← LinearMap.det_conj L e, hconj, LinearMap.det_pi]
    simp only [hdetw]
    rfl
  have hpos : 0 < jacInf M := by
    have hdA : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 A.isUnit).ne_zero
    refine Finset.prod_pos fun w _ => pow_pos (Complex.normSq_pos.2 ?_) n
    intro h0
    have hu : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det _).1 A.isUnit
    have : IsUnit (M.det w) := hu.map (Pi.evalRingHom (fun _ : W => ℂ) w)
    exact this.ne_zero h0
  have hd0 : LinearMap.det L ≠ 0 := by rw [hdet]; exact hpos.ne'
  have hmap : Measure.map L (volume : Measure (Fin n → Fin n → Cinf E)) =
      ENNReal.ofReal |(LinearMap.det L)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd0
  set Le : (Fin n → Fin n → Cinf E) ≃L[ℝ] (Fin n → Fin n → Cinf E) :=
    (LinearMap.equivOfDetNeZero L hd0).toContinuousLinearEquiv
  have hLe : (Le : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) = L := rfl
  have hemb : MeasurableEmbedding (L : (Fin n → Fin n → Cinf E) → (Fin n → Fin n → Cinf E)) := by
    rw [← hLe]; exact Le.toHomeomorph.measurableEmbedding
  simp_rw [← hL]
  rw [integral_const_mul, ← hemb.integral_map, hmap, integral_smul_measure, hdet,
    abs_of_pos (inv_pos.2 hpos), ENNReal.toReal_ofReal (inv_pos.2 hpos).le, Complex.real_smul, ← mul_assoc]
  push_cast
  rw [mul_inv_cancel₀ (by exact_mod_cast hpos.ne'), one_mul]

end GlobalTheory.JSW.MirCinf
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralArchimedeanMatricesLeftMulJacobianStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (A : GL (Fin n) (Cinf E)) (F : (Fin n → Fin n → Cinf E) → ℂ), ∫ a, F a = ∫ h : (Fin n → Fin n → Cinf E), ((jacInf (A : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) * F (fun i j => ((A : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) := by
  first | (exact @GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf) | (exact GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf) | (intros; apply GlobalTheory.JSW.MirCinf.integral_eq_integral_mulLeft_matrixInf  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingAffineFamilyEqIntegralKernel

section

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

namespace GlobalTheory.JSW.MirCinf.SecAffine

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem htInf_inv_eq (g : GL (Fin n) (Cinf E)) : htInf g⁻¹ = htInf g := by
  unfold htInf
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [map_inv, htGL_inv]

end GlobalTheory.JSW.MirCinf.SecAffine

namespace GlobalTheory.JSW.MirCinf

theorem smoothMatInf_affine_eq_integral_secKInf : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → (∀ z a, χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) * α a = ∫ x, κ x * (𝐞 (τ x (z, a)) : ℂ) ∂ν) → ∃ R : ℝ, ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → ∀ q z g, χ z * smoothMatInf α W (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹ * q) = ∫ p, secKInf R σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) := by
  classical
  intro E _ _ n Z _ _ _ σ₀ L χ α hχ hσ hα hαu X _ ν _ κ τ hκ hτ hmom hk
  obtain ⟨R1, hR1⟩ : ∃ R1 : ℝ, ∀ z ∈ tsupport χ, htInf (toGLInf (Matrix.of (σ₀ + L z))) ≤ R1 := by
    have hc : ContinuousOn (fun z => htInf (toGLInf (Matrix.of (σ₀ + L z)))) (tsupport χ) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.comp
        (by fun_prop : Continuous fun z => σ₀ + L z).continuousOn fun z hz => hσ z hz)
    obtain ⟨C, hC⟩ := hχ.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun z hz => (Real.le_norm_self _).trans (hC z hz)⟩
  obtain ⟨R2, hR2⟩ : ∃ R2 : ℝ, ∀ a ∈ tsupport α, htInf (toGLInf (Matrix.of a)) ≤ R2 := by
    have hc : ContinuousOn (fun a : Fin n → Fin n → Cinf E => htInf (toGLInf (Matrix.of a))) (tsupport α) :=
      SmoothGrowth.continuous_htInf.comp_continuousOn (SmoothGrowth.continuousOn_toGLInf.mono hαu)
    obtain ⟨C, hC⟩ := hα.isCompact.exists_bound_of_continuousOn hc
    exact ⟨C, fun a ha => (Real.le_norm_self _).trans (hC a ha)⟩
  refine ⟨R1 * R2, ?_⟩
  intro W hW q z g
  have hfam := GlobalTheory.T.schwartz_integral_bound_smooth E n Z X ν κ τ hκ hτ hmom (R1 * R2) σ₀ L
  have hrap : IsRapidFInf ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) (secKInf (R1 * R2) σ₀ κ τ q)
      (fun p => toGLInf (Matrix.of p.1)) (secEtaInf L τ q) := by
    obtain ⟨h1, h2, h3⟩ := hfam
    obtain ⟨m1, m2⟩ := h2 Unit (fun _ => q) (fun _ _ => measurable_const)
    refine ⟨m1.comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), h1,
      fun z => (m2 z).comp ((measurable_const (a := ()) : Measurable fun _ : (Fin n → Fin n → Cinf E) × X => ()).prodMk measurable_id), fun N => ?_⟩
    obtain ⟨C, M, hC⟩ := h3 N
    exact (hC q).1
  have hint : Integrable (fun p : (Fin n → Fin n → Cinf E) × X => secKInf (R1 * R2) σ₀ κ τ q p *
      (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))) ((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) :=
    hrap.integrable hW z g
  have hinner : ∀ h : Fin n → Fin n → Cinf E, ∫ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
      W (g * toGLInf (Matrix.of (h, x).1)) ∂ν =
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    intro h
    rw [hk z]
    by_cases hc : IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q
    · have hsum : ((0 : Z), sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) σ₀) +
          (z, sandCLMInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) (Matrix.of h) (L z)) =
          (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
        rw [Prod.mk_add_mk, zero_add]
        congr 1
        funext i j
        simp only [Pi.add_apply, sandCLMInf_apply]
        rw [← Matrix.add_apply, ← Matrix.add_mul, ← Matrix.mul_add]
        rfl
      have e : ∀ x, secKInf (R1 * R2) σ₀ κ τ q (h, x) * (𝐞 (secEtaInf L τ q (h, x) z) : ℂ) *
          W (g * toGLInf (Matrix.of (h, x).1)) =
          (((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) *
            W (g * toGLInf (Matrix.of h))) *
          (κ x * (𝐞 (τ x (z, fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
            Matrix.of (σ₀ + L z) * Matrix.of h) i j)) : ℂ)) := by
        intro x
        simp only [secKInf, secEtaInf, if_pos hc]
        rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.comp_apply, ← hsum, map_add, AddChar.map_add_eq_mul, Circle.coe_mul]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, if_pos hc]
      ring
    · simp [secKInf, if_neg hc]
  have hR : ∫ p, secKInf (R1 * R2) σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1))
      ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) = ∫ h : Fin n → Fin n → Cinf E,
      (if IsUnit (Matrix.of h) ∧ htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q then
        ((jacInf ((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) : ℝ) : ℂ) else 0) *
      (χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) *
        α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) *
      W (g * toGLInf (Matrix.of h)) := by
    rw [integral_prod _ hint]
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)
  rw [hR]
  by_cases hz : χ z = 0
  · simp [hz]
  have hzK : z ∈ tsupport χ := subset_tsupport _ hz
  have hu := hσ z hzK
  set σ' := toGLInf (Matrix.of (σ₀ + L z)) with hσ'
  have hσv : (σ' : Matrix (Fin n) (Fin n) (Cinf E)) = Matrix.of (σ₀ + L z) := val_toGLInf hu
  rw [smoothMatInf, GlobalTheory.T.integral_archimedeanMatrices_leftMul_jacobian E n (q⁻¹ * σ'), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only
  have hAh : Matrix.of (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      ((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := rfl
  have ha : (fun i j => (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) i j) =
      (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) := by
    rw [Units.val_mul, hσv]
  rw [hAh, ha]
  by_cases hαz : α (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j) = 0
  · rw [hαz]; ring
  have hmem := subset_tsupport _ hαz
  have hAu : IsUnit (Matrix.of (fun i j => (((q⁻¹ : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of (σ₀ + L z) * Matrix.of h) i j)) := hαu hmem
  rw [← ha] at hAu hmem
  rw [hAh] at hAu
  have hh : IsUnit (Matrix.of h) := (Units.isUnit_units_mul _ _).1 hAu
  have ht : toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (q⁻¹ * σ') * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf hAu, Units.val_mul (q⁻¹ * σ'), val_toGLInf hh])
  have hb1 := hR1 z hzK
  have hb2 : htInf (toGLInf (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h)) ≤ R2 := hR2 _ hmem
  rw [ht] at hb2
  have hb1' : htInf σ' ≤ R1 := hb1
  have hbound : htInf (toGLInf (Matrix.of h)) ≤ R1 * R2 * htInf q := by
    have e1 : toGLInf (Matrix.of h) = (q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by group
    have p1 := htInf_pos' σ'
    have p2 := htInf_pos' (q⁻¹ * σ' * toGLInf (Matrix.of h))
    have p3 := htInf_pos' q
    calc htInf (toGLInf (Matrix.of h)) = htInf ((q⁻¹ * σ')⁻¹ * (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [← e1]
      _ ≤ htInf ((q⁻¹ * σ')⁻¹) * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := htInf_mul_le _ _
      _ = htInf (q⁻¹ * σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) := by rw [SecAffine.htInf_inv_eq]
      _ ≤ (htInf q⁻¹ * htInf σ') * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h)) :=
          mul_le_mul_of_nonneg_right (htInf_mul_le _ _) p2.le
      _ = htInf q * (htInf σ' * htInf (q⁻¹ * σ' * toGLInf (Matrix.of h))) := by rw [SecAffine.htInf_inv_eq]; ring
      _ ≤ htInf q * (R1 * R2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hb1' hb2 p2.le (p1.le.trans hb1')) p3.le
      _ = R1 * R2 * htInf q := by ring
  rw [if_pos ⟨hh, hbound⟩]
  have hG : ((g * σ'⁻¹ * q : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) *
      (((q⁻¹ * σ' : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = (g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h := by
    rw [← Matrix.mul_assoc, ← Units.val_mul]
    congr 2
    group
  have hgt : toGLInf ((g : Matrix (Fin n) (Fin n) (Cinf E)) * Matrix.of h) = g * toGLInf (Matrix.of h) :=
    Units.ext (by rw [val_toGLInf (g.isUnit.mul hh), Units.val_mul, val_toGLInf hh])
  rw [hG, onMatInf_of_isUnit W (g.isUnit.mul hh), hgt, Units.val_mul, jacInf_mul, hσv]
  push_cast
  ring

end GlobalTheory.JSW.MirCinf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothingAffineFamilyEqIntegralKernelStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff

theorem _root_.GlobalTheory.T.smoothing_affine_family_eq_integral_kernel : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (σ₀ : Fin n → Fin n → Cinf E) (L : Z →L[ℝ] (Fin n → Fin n → Cinf E)) (χ : Z → ℂ) (α : (Fin n → Fin n → Cinf E) → ℂ), HasCompactSupport χ → (∀ z ∈ tsupport χ, IsUnit (Matrix.of (σ₀ + L z))) → HasCompactSupport α → tsupport α ⊆ {x | IsUnit (Matrix.of x)} → ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (κ : X → ℂ) (τ : X → (Z × (Fin n → Fin n → Cinf E)) →L[ℝ] ℝ), Measurable κ → (∀ z, Measurable fun x => τ x z) → (∀ N : ℕ, Integrable (fun x => ‖κ x‖ * (1 + ‖τ x‖) ^ N) ν) → (∀ z a, χ z * ((jacInf (Matrix.of (σ₀ + L z)) : ℝ) : ℂ) * α a = ∫ x, κ x * (𝐞 (τ x (z, a)) : ℂ) ∂ν) → ∃ R : ℝ, ∀ W : GL (Fin n) (Cinf E) → ℂ, IsModGrowthInf W → ∀ q z g, χ z * smoothMatInf α W (g * (toGLInf (Matrix.of (σ₀ + L z)))⁻¹ * q) = ∫ p, secKInf R σ₀ κ τ q p * (𝐞 (secEtaInf L τ q p z) : ℂ) * W (g * toGLInf (Matrix.of p.1)) ∂((volume : Measure (Fin n → Fin n → Cinf E)).prod ν) := by
  first | exact @GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf | exact GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf | (intros; apply GlobalTheory.JSW.MirCinf.smoothMatInf_affine_eq_integral_secKInf <;> assumption)
end
end
