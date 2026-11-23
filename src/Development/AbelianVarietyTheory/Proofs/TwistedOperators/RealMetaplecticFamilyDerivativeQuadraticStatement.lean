module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMatrixOneParameterGroupEqExpStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwiningSymplecticAndGroupLawStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymplecticLieAlgebraOfExpSmulMemSymplecticGroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamIsometryFamiliesDifferByCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinates
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MetaplecticOneParameterSchwartzIntertwining

section

@[expose] public section

noncomputable section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

namespace GlobalTheory.RealWeil

theorem integral_norm_sq_eq_norm_toLp_sq {l : Type} [Fintype l] (g : Sch l) :
    ∫ x, ‖g x‖ ^ 2 = ‖g.toLp 2 volume‖ ^ 2 := by
  rw [SchwartzMap.norm_toLp' (by simp) (by simp)]
  have h2 : (2 : ENNReal).toReal = 2 := by simp
  simp only [h2]
  have hn : 0 ≤ ∫ x, ‖g x‖ ^ (2 : ℝ) := integral_nonneg fun x => by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
  norm_num

theorem metaplectic_oneParam_schwartz : GlobalTheory.Published.RealMetaplecticRepresentation →
    ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ),
      X ∈ LieAlgebra.Symplectic.sp l ℝ → ∃ U : ℝ → Sch l →ₗ[ℂ] Sch l, (∀ s t f, U (s + t) f = U s (U t f)) ∧
        (∀ f, U 0 f = f) ∧
        (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (NormedSpace.exp (t • X) *ᵥ w) ⇑(U t f)) ∧
        (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧ ∀ f y, HasDerivAt (fun t => U t f y) (quad X f y) 0 := by
  intro hMp l _ _ _ X hX
  obtain ⟨G, _, _, _, pr, om, omS, -, -, h3, h4, h5, h6⟩ := hMp l
  obtain ⟨γ, -, h0, hadd, hpr, hd⟩ := h6 X hX
  refine ⟨fun t => (omS (γ t)).toLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro s t f
    simp only [ContinuousLinearMap.coe_coe, hadd, map_mul, ContinuousLinearMap.mul_apply]
  · intro f
    simp [h0]
  · intro t w f f₁ h
    simp only [ContinuousLinearMap.coe_coe]
    rw [← hpr t]
    have hL : f₁.toLp 2 = rho w (f.toLp 2) := by
      refine Lp.ext ((SchwartzMap.coeFn_toLp f₁ 2 volume).trans ?_)
      refine Filter.EventuallyEq.symm ((coeFn_rho w _).trans ?_)
      rw [h]
      exact rhoFun_congr w (SchwartzMap.coeFn_toLp f 2 volume)
    have key : (omS (γ t) f₁).toLp 2 =
        rho ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ((omS (γ t) f).toLp 2) := by
      rw [← h4, hL, h3, h4]
    have hae : ⇑(omS (γ t) f₁) =ᵐ[volume]
        rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f) := by
      refine (SchwartzMap.coeFn_toLp (omS (γ t) f₁) 2 volume).symm.trans ?_
      rw [key]
      refine (coeFn_rho _ _).trans ?_
      exact rhoFun_congr _ (SchwartzMap.coeFn_toLp (omS (γ t) f) 2 volume)
    have hc : Continuous (rhoFun ((pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) ⇑(omS (γ t) f)) :=
      (continuous_phase _).mul ((omS (γ t) f).continuous.comp (continuous_id.add continuous_const))
    exact (Continuous.ae_eq_iff_eq volume (omS (γ t) f₁).continuous hc).1 hae
  · intro t f
    simp only [ContinuousLinearMap.coe_coe]
    rw [integral_norm_sq_eq_norm_toLp_sq, integral_norm_sq_eq_norm_toLp_sq, ← h4, LinearIsometryEquiv.norm_map]
  · intro f y
    let lam : Sch l →L[ℂ] ℂ :=
      (BoundedContinuousFunction.evalCLM ℂ y).comp (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ)
    have hlam : ∀ g : Sch l, lam g = g y := fun g => rfl
    have := (metaplectic_schwartz_smooth h3 h4 h5).2.2 lam X hX γ h0 hpr hd f
    simpa only [hlam, ContinuousLinearMap.coe_coe] using this

end GlobalTheory.RealWeil

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MetaplecticOneParameterSchwartzIntertwiningStatement

section

@[expose] public section

open GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap Matrix

theorem _root_.GlobalTheory.T.metaplectic_oneParameter_schwartz_intertwining : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (l : Type) [Fintype l] [DecidableEq l] [Nonempty l] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ), X ∈ LieAlgebra.Symplectic.sp l ℝ → ∃ U : ℝ → Sch l →ₗ[ℂ] Sch l, (∀ s t f, U (s + t) f = U s (U t f)) ∧ (∀ f, U 0 f = f) ∧ (∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(U t f₁) = rhoFun (NormedSpace.exp (t • X) *ᵥ w) ⇑(U t f)) ∧ (∀ t f, ∫ x, ‖U t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) ∧ ∀ f y, HasDerivAt (fun t => U t f y) (quad X f y) 0 := by
  first | exact @GlobalTheory.RealWeil.metaplectic_oneParam_schwartz | exact GlobalTheory.RealWeil.metaplectic_oneParam_schwartz | (intros; apply GlobalTheory.RealWeil.metaplectic_oneParam_schwartz <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinatesStatement

section

@[expose] public section

open GlobalTheory.ArchUniq GlobalTheory.RealWeil MeasureTheory
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.realPairingSpace_result_of_schrodingerCoordinates : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P → ∀ n : ℕ, Module.finrank ℝ V = n →
    (∀ (A' : ℝ → (Fin n ⊕ Fin n → ℝ) →ₗ[ℝ] (Fin n ⊕ Fin n → ℝ)) (T' : ℝ → Sch (Fin n) →ₗ[ℂ] Sch (Fin n)),
      (∀ w, Continuous fun t => A' t w) → (∀ s t f, T' (s + t) f = T' s (T' t f)) → (∀ f, T' 0 f = f) →
      (∀ t w (f f₁ : Sch (Fin n)), ⇑f₁ = rhoFun w ⇑f → ⇑(T' t f₁) = rhoFun (A' t w) ⇑(T' t f)) →
      (∀ t f, ∫ x, ‖T' t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) → (∀ f y, Continuous fun t => T' t f y) →
      ∃ (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) (c : ℂ),
        ∀ f y, HasDerivAt (fun t => T' t f y) (quad X f y + c * f y) 0) →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  first | exact @GlobalTheory.ArchUniq.SchrTransport.transport | exact GlobalTheory.ArchUniq.SchrTransport.transport | (intros; apply GlobalTheory.ArchUniq.SchrTransport.transport <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealMetaplecticFamilyDerivativeQuadratic

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical Matrix

namespace GlobalTheory.QuadFam

open GlobalTheory.RealWeil

theorem coordAll (hP : GlobalTheory.Published.RealMetaplecticRepresentation) (l : Type) [Fintype l] [DecidableEq l]
    (A : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)) (T : ℝ → Sch l →ₗ[ℂ] Sch l)
    (hA : ∀ w, Continuous fun t => A t w) (hT : ∀ s t f, T (s + t) f = T s (T t f)) (hT0 : ∀ f, T 0 f = f)
    (hI : ∀ t w (f f₁ : Sch l), ⇑f₁ = rhoFun w ⇑f → ⇑(T t f₁) = rhoFun (A t w) ⇑(T t f))
    (hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2) (hpt : ∀ f y, Continuous fun t => T t f y) :
    ∃ (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (c : ℂ), ∀ f y, HasDerivAt (fun t => T t f y) (quad X f y + c * f y) 0 := by
  obtain ⟨hs, hgrp, h0⟩ := GlobalTheory.T.symplectic_and_flow_of_intertwining_unitary l A T hT hT0 hI hiso
  cases isEmpty_or_nonempty l with
  | inl hl =>
    have hq : ∀ f y, quad (0 : Matrix (l ⊕ l) (l ⊕ l) ℝ) f y = 0 := fun f y => by simp [quad]
    obtain ⟨c, hc⟩ := GlobalTheory.T.isometryFamilies_derivatives_differ_by_scalar_at_zero l (fun t w => A t w) T (fun _ => LinearMap.id) (fun f y => quad 0 f y) hT hT0
      (fun _ _ _ => rfl) (fun _ => rfl) hgrp h0 hI
      (fun t w f f₁ h => by
        rw [LinearMap.id_apply, LinearMap.id_apply, h, Subsingleton.elim (A t w) w]) hiso
      (fun _ _ => rfl) hpt (fun f y => by rw [hq]; exact hasDerivAt_const _ _)
    exact ⟨0, c, hc⟩
  | inr hl =>
    let M : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => LinearMap.toMatrix' (A t)
    have hM : ∀ t w, M t *ᵥ w = A t w := fun t w => LinearMap.toMatrix'_mulVec (A t) w
    have hMc : Continuous M := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [M, LinearMap.toMatrix'_apply]
      exact (continuous_apply i).comp (hA _)
    have hM0 : M 0 = 1 := by
      have : A 0 = LinearMap.id := LinearMap.ext h0
      simp only [M, this, LinearMap.toMatrix'_id]
    have hMm : ∀ s t, M (s + t) = M s * M t := by
      intro s t
      have : A (s + t) = (A s).comp (A t) := LinearMap.ext (hgrp s t)
      simp only [M, this, LinearMap.toMatrix'_comp]
    obtain ⟨X, hX⟩ := GlobalTheory.T.continuous_matrix_oneParameterGroup_eq_exp _ M hMc hM0 hMm
    have hsp : X ∈ LieAlgebra.Symplectic.sp l ℝ := by
      refine GlobalTheory.T.mem_symplecticLieAlgebra_of_exp_smul_mem_symplecticGroup l X fun t => ?_
      obtain ⟨N, hN⟩ := GlobalTheory.exists_symplecticGroup_of_sympl l (A t) (hs t)
      have e : Matrix.toLin' (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = A t := LinearMap.ext fun w => by
        rw [Matrix.toLin'_apply, hN]
      have e2 : (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) = M t := by
        simp only [M, ← e, LinearMap.toMatrix'_toLin']
      rw [← hX t, ← e2]
      exact N.2
    obtain ⟨U, hU, hU0, hUI, hUiso, hUd⟩ := GlobalTheory.T.metaplectic_oneParameter_schwartz_intertwining hP l X hsp
    have hB : ∀ t w, NormedSpace.exp (t • X) *ᵥ w = A t w := fun t w => by rw [← hX, hM]
    obtain ⟨c, hc⟩ := GlobalTheory.T.isometryFamilies_derivatives_differ_by_scalar_at_zero l (fun t w => A t w) T U (fun f y => quad X f y) hT hT0 hU hU0 hgrp h0 hI
      (fun t w f f₁ h => by rw [hUI t w f f₁ h, hB]) hiso hUiso hpt hUd
    exact ⟨X, c, hc⟩

theorem deriv_quad : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    (∀ f φ : 𝓢(V, ℂ), Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  intro hP V _ _ _ _ _ μ hμ P hp A T hA hT hT0 hI hiso hpt _
  exact GlobalTheory.T.realPairingSpace_result_of_schrodingerCoordinates V μ hμ P hp _ rfl (fun A' T' => coordAll hP (Fin _) A' T') A T hA hT hT0 hI hiso hpt

end GlobalTheory.QuadFam
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealMetaplecticFamilyDerivativeQuadraticStatement

section

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

theorem _root_.GlobalTheory.T.realMetaplectic_family_derivative_quadratic : GlobalTheory.Published.RealMetaplecticRepresentation → ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V), μ.IsAddHaarMeasure → ∀ (P : V → V → ℝ), IsPairing P →
    ∀ (A : ℝ → (V × V) →ₗ[ℝ] (V × V)) (T : ℝ → 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ)),
    (∀ v, Continuous fun t => A t v) →
    (∀ s t f, T (s + t) f = T s (T t f)) → (∀ f, T 0 f = f) →
    (∀ t v (f f₁ : 𝓢(V, ℂ)), ⇑f₁ = schrF P v ⇑f → ⇑(T t f₁) = schrF P (A t v) ⇑(T t f)) →
    (∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ) →
    (∀ f y, Continuous fun t => T t f y) →
    (∀ f φ : 𝓢(V, ℂ), Continuous fun t => ∫ x, T t f x * starRingEnd ℂ (φ x) ∂μ) →
    ∃ (m : ℕ) (a b : Fin m → V × V) (c : Fin m → ℂ) (c₀ : ℂ), ∀ (f : 𝓢(V, ℂ)) (g₁ g₂ : Fin m → 𝓢(V, ℂ)),
      (∀ i y, g₁ i y = fderiv ℝ (⇑f) y (b i).1 - 2 * Real.pi * Complex.I * (P y (b i).2 : ℂ) * f y) →
      (∀ i y, g₂ i y = fderiv ℝ (⇑(g₁ i)) y (a i).1 - 2 * Real.pi * Complex.I * (P y (a i).2 : ℂ) * g₁ i y) →
      ∀ y, HasDerivAt (fun t => T t f y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  first | exact @GlobalTheory.QuadFam.deriv_quad | exact GlobalTheory.QuadFam.deriv_quad | (intros; apply GlobalTheory.QuadFam.deriv_quad <;> assumption)
end
end
