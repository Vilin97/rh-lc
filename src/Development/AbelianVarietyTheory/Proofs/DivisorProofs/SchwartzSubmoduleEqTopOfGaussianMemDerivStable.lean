module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
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
import Mathlib.Analysis.Fourier.Notation
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAllGaussianWidthsOfFourierStableSchwartzStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureWideGaussianMulSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOfClosedSubmoduleGaussianConvolutionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NarrowGaussConvolutionDenseStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDensityTransportLinearEquivChirpStatement
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivEuclideanPiMulNormSqEqRe

section

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_equiv_euclidean_pi_mul_norm_sq_eq_re (V : Type) [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) :
    ∃ A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      ∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re := by
  classical
  let B : LinearMap.BilinForm ℝ V := LinearMap.mk₂ ℝ (fun x y => (Q x y).re)
    (by intros; simp) (by intros; simp) (by intros; simp) (by intros; simp)
  let q : QuadraticForm ℝ V := B.toQuadraticMap
  have hq : ∀ x, q x = (Q x x).re := fun x => rfl
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares q
  have he : ∀ x, ∑ i, w i * (e x i * e x i) = (Q x x).re := by
    intro x
    have := e.map_app x
    rw [QuadraticMap.weightedSumSquares_apply] at this
    simpa [hq] using this
  have hw : ∀ i, 0 < w i := by
    intro i
    have h1 := he (e.symm (Pi.single i 1))
    have h2 : e (e.symm (Pi.single i 1)) = Pi.single i 1 := e.toLinearEquiv.apply_symm_apply _
    have hne : e.symm (Pi.single i 1) ≠ 0 := by
      intro h
      rw [h, map_zero] at h2
      have := congrFun h2 i
      simp at this
    rw [h2, Finset.sum_eq_single i (by intro j _ hj; simp [hj]) (by simp)] at h1
    have h3 := hQ (e.symm (Pi.single i 1))
    have h4 : 0 < c * ‖e.symm (Pi.single i 1)‖ ^ 2 := by
      have := norm_pos_iff.mpr hne
      positivity
    simp at h1
    linarith
  have hs : ∀ i, Real.sqrt (w i / Real.pi) ≠ 0 := fun i =>
    (Real.sqrt_pos.mpr (div_pos (hw i) Real.pi_pos)).ne'
  let D : (Fin (Module.finrank ℝ V) → ℝ) ≃ₗ[ℝ] (Fin (Module.finrank ℝ V) → ℝ) :=
    LinearEquiv.piCongrRight fun i =>
      LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt (w i / Real.pi)) (hs i)
  let A : V ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    (e.toLinearEquiv.trans D).trans (WithLp.linearEquiv 2 ℝ _).symm
  have hA : ∀ x i, A x i = Real.sqrt (w i / Real.pi) * e x i := fun x i => rfl
  refine ⟨A.toContinuousLinearEquiv, fun x => ?_⟩
  rw [← he, EuclideanSpace.norm_sq_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (A.toContinuousLinearEquiv x) i = Real.sqrt (w i / Real.pi) * e x i := hA x i
  rw [this, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt (div_pos (hw i) Real.pi_pos).le]
  have := Real.pi_pos.ne'
  field_simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivEuclideanPiMulNormSqEqReStatement

section

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_euclidean_equiv_pi_mul_norm_sq_eq_re : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ∀ x, Real.pi * ‖A x‖ ^ 2 = (Q x x).re := by
  first | exact @GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re | exact GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re | (intros; apply GlobalTheory.exists_equiv_euclidean_pi_mul_norm_sq_eq_re <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierStableGaussianSubmodule

section

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem exists_fourier_stable_gaussian_submodule :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ W : Submodule ℂ (SchwartzMap E ℂ), W ≤ N ∧ G ∈ W ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) ∧
      (∀ f ∈ W, 𝓕 f ∈ W) := by
  intro E _ _ _ _ _ N G hG hGN hD hL
  let S : Set (Submodule ℂ (SchwartzMap E ℂ)) := {K | G ∈ K ∧
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ K) ∧
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ K → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ K)}
  have hWG : G ∈ sInf S := Submodule.mem_sInf.2 fun K hK => hK.1
  have hWD : ∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.1 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have hWL : ∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ sInf S →
      (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ sInf S := fun v f f₁ hf h =>
    Submodule.mem_sInf.2 fun K hK => hK.2.2 v f f₁ (Submodule.mem_sInf.1 hf K hK) h
  have htemp : ∀ m : E, Function.HasTemperateGrowth (fun x : E => inner ℝ x m) := by
    intro m
    have : (fun x : E => inner ℝ x m) = (innerSL ℝ m : E →L[ℝ] ℝ) := by
      funext x; simp [real_inner_comm]
    rw [this]; exact (innerSL ℝ m).hasTemperateGrowth
  have hFG : 𝓕 G = G := by
    ext w
    have h1 : (⇑G) = fun v : E => Complex.exp (-(Real.pi : ℂ) * (‖v‖ : ℂ) ^ 2) := by
      funext v; rw [hG]; congr 1; push_cast; ring
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    rw [SchwartzMap.fourier_coe, h1,
      fourier_gaussian_innerProductSpace (by simpa using Real.pi_pos), div_self hpi,
      Complex.one_cpow, one_mul]
    congr 1
    field_simp
  have hK : (sInf S).comap (SchwartzMap.fourierTransformCLM ℂ (V := E) (E := ℂ)).toLinearMap ∈ S := by
    refine ⟨?_, ?_, ?_⟩
    · show 𝓕 G ∈ sInf S
      rw [hFG]; exact hWG
    · intro v f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      have h1 : f₁ = LineDeriv.lineDerivOp v f := by
        ext x; rw [h, SchwartzMap.lineDerivOp_apply_eq_fderiv]
      rw [h1, SchwartzMap.fourier_lineDerivOp_eq]
      refine Submodule.smul_mem _ _ (hWL (innerSL ℝ v) _ _ hf' fun x => ?_)
      rw [SchwartzMap.smulLeftCLM_apply_apply (htemp v)]
      simp [real_inner_comm]
    · intro ℓ f f₁ hf h
      have hf' : 𝓕 f ∈ sInf S := hf
      show 𝓕 f₁ ∈ sInf S
      set u : E := (InnerProductSpace.toDual ℝ E).symm ℓ with hu
      have h1 : f₁ = SchwartzMap.smulLeftCLM ℂ (fun x => inner ℝ x u) f := by
        ext x
        rw [h, SchwartzMap.smulLeftCLM_apply_apply (htemp u), real_inner_comm, hu,
          InnerProductSpace.toDual_symm_apply]
        simp
      have h2 : LineDeriv.lineDerivOp u (𝓕 f) ∈ sInf S :=
        hWD u _ _ hf' fun x => SchwartzMap.lineDerivOp_apply_eq_fderiv _ _ _
      rw [SchwartzMap.lineDerivOp_fourier_eq, ← h1, ← SchwartzMap.fourierTransformCLM_apply ℂ,
        map_smul, SchwartzMap.fourierTransformCLM_apply] at h2
      have hc : (-(2 * (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
        simp [Real.pi_ne_zero]
      exact (Submodule.smul_mem_iff _ hc).1 h2
  exact ⟨sInf S, sInf_le ⟨hGN, hD, hL⟩, hWG, hWL, fun f hf => sInf_le hK hf⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFourierStableGaussianSubmoduleStatement

section

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_fourier_stable_submodule_containing_gaussian : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    ∃ W : Submodule ℂ (SchwartzMap E ℂ), W ≤ N ∧ G ∈ W ∧
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) ∧
      (∀ f ∈ W, 𝓕 f ∈ W) := by
  first | exact @GlobalTheory.exists_fourier_stable_gaussian_submodule | exact GlobalTheory.exists_fourier_stable_gaussian_submodule | (intros; apply GlobalTheory.exists_fourier_stable_gaussian_submodule <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzClosureStableLinearFormFourier

section

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory

theorem topologicalClosure_stable_of_continuousLinearMap {M : Type} [TopologicalSpace M] [AddCommGroup M]
    [Module ℂ M] [ContinuousSMul ℂ M] [ContinuousAdd M] (W : Submodule ℂ M) (T : M →L[ℂ] M)
    (hT : ∀ f ∈ W, T f ∈ W) : ∀ f ∈ W.topologicalClosure, T f ∈ W.topologicalClosure := by
  intro f hf
  have h1 : Submodule.map (T : M →ₗ[ℂ] M) W ≤ W := by
    rintro _ ⟨g, hg, rfl⟩
    exact hT g hg
  have h2 := Submodule.topologicalClosure_map T W
  exact Submodule.topologicalClosure_mono h1 (h2 ⟨f, hf, rfl⟩)

theorem schwartz_closure_stable_linearForm_fourier :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  intro E _ _ _ _ _ W hmul hF
  constructor
  · intro ℓ f f₁ hf hf₁
    have hg : Function.HasTemperateGrowth (fun x : E => ((ℓ x : ℝ) : ℂ)) :=
      (Complex.ofRealCLM.comp ℓ).hasTemperateGrowth
    set T : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
      SchwartzMap.smulLeftCLM ℂ (fun x : E => ((ℓ x : ℝ) : ℂ)) with hTdef
    have hTapp : ∀ g : SchwartzMap E ℂ, ∀ x, T g x = (ℓ x : ℂ) * g x := by
      intro g x
      rw [hTdef, SchwartzMap.smulLeftCLM_apply hg]
      rfl
    have hTW : ∀ g ∈ W, T g ∈ W := fun g hg' => hmul ℓ g (T g) hg' (hTapp g)
    have hf₁T : f₁ = T f := by
      ext x
      rw [hf₁ x, hTapp f x]
    rw [hf₁T]
    exact topologicalClosure_stable_of_continuousLinearMap W T hTW f hf
  · intro f hf
    have hTW : ∀ g ∈ W, SchwartzMap.fourierTransformCLM ℂ g ∈ W := by
      intro g hg
      rw [SchwartzMap.fourierTransformCLM_apply]
      exact hF g hg
    have := topologicalClosure_stable_of_continuousLinearMap W (SchwartzMap.fourierTransformCLM ℂ) hTW f hf
    rwa [SchwartzMap.fourierTransformCLM_apply] at this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzClosureStableLinearFormFourierStatement

section

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (W : Submodule ℂ (SchwartzMap E ℂ)),
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ W) →
    (∀ f ∈ W, 𝓕 f ∈ W) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ W.topologicalClosure → (∀ x, f₁ x = (ℓ x : ℂ) * f x) →
      f₁ ∈ W.topologicalClosure) ∧
    (∀ f ∈ W.topologicalClosure, 𝓕 f ∈ W.topologicalClosure) := by
  first | exact @GlobalTheory.schwartz_closure_stable_linearForm_fourier | exact GlobalTheory.schwartz_closure_stable_linearForm_fourier | (intros; apply GlobalTheory.schwartz_closure_stable_linearForm_fourier <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSubmoduleEqTopOfGaussianMemDerivStable

section

@[expose] public section

open FourierTransform MeasureTheory Filter Topology

namespace GlobalTheory.SchwartzGaussDense

theorem dense_of_stdGaussian_mem : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (N : Submodule ℂ (SchwartzMap E ℂ)) (G : SchwartzMap E ℂ),
    (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ N →
    (∀ (v : E) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap E ℂ)) := by
  intro E _ _ _ _ _ N G hG hGN hD hL
  obtain ⟨W, hWN, hGW, hLW, hFW⟩ := GlobalTheory.T.exists_fourier_stable_submodule_containing_gaussian E N G hG hGN hD hL
  obtain ⟨hLM, hFM⟩ := GlobalTheory.T.topologicalClosure_stable_linearForm_mul_and_fourier E W hLW hFW
  set M := W.topologicalClosure with hMdef
  have hcl : IsClosed (M : Set (SchwartzMap E ℂ)) := W.isClosed_topologicalClosure
  have hGM : G ∈ M := W.le_topologicalClosure hGW
  have hgauss := GlobalTheory.T.mem_all_gaussianWidths_of_fourierStable_schwartz E M hcl hLM hFM G hG hGM
  have key : ∀ (h f : SchwartzMap E ℂ), (∃ b : ℝ, 0 < b ∧ ∀ y, f y = Complex.exp (-((b * ‖y‖ ^ 2 : ℝ) : ℂ)) * h y) →
      f ∈ M := by
    rintro h f ⟨b, hb, hf⟩
    have hsub : {u : SchwartzMap E ℂ | ∃ (c : ℝ) (s : ℂ), 0 < c ∧
        ∀ y, u y = s * ∫ a, f a * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))} ⊆ (M : Set (SchwartzMap E ℂ)) := by
      rintro u ⟨c, s, hc, hu⟩
      by_cases hs : s = 0
      · have : u = 0 := by ext y; simp [hu y, hs]
        rw [this]; exact M.zero_mem
      · have hu' : ∀ y, (s⁻¹ • u) y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
            Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) := by
          intro y
          rw [SchwartzMap.smul_apply, hu y, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
          congr 1; funext a; rw [hf a]
        have hmem := GlobalTheory.T.mem_of_closedSubmodule_gaussian_convolution E M hcl hLM b c hb hc (hgauss c hc) h (s⁻¹ • u) hu'
        have : u = s • (s⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hs, one_smul]
        rw [this]; exact M.smul_mem s hmem
    exact closure_minimal hsub hcl (GlobalTheory.T.mem_closure_gaussian_convolutions E f)
  have hall : ∀ h : SchwartzMap E ℂ, h ∈ M := by
    intro h
    exact closure_minimal (fun f hf => key h f hf) hcl (GlobalTheory.T.mem_closure_wideGaussian_mul_schwartz E h)
  have htop : N.topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro h _
    exact Submodule.topologicalClosure_mono hWN (hall h)
  exact (Submodule.dense_iff_topologicalClosure_eq_top).2 htop

theorem dense_of_gaussian_mem : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (N : Submodule ℂ (SchwartzMap V ℂ))
    (g : SchwartzMap V ℂ) (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ), 0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    (∀ x, g x = Complex.exp (-(Q x x))) → g ∈ N →
    (∀ (v : V) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = fderiv ℝ (⇑f) x v) → f₁ ∈ N) →
    (∀ (ℓ : V →L[ℝ] ℝ) (f f₁ : SchwartzMap V ℂ), f ∈ N → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ N) →
    Dense (N : Set (SchwartzMap V ℂ)) := by
  intro V _ _ _ N g Q c hc hQ hg hgN hD hL
  obtain ⟨A, hA⟩ := GlobalTheory.T.exists_euclidean_equiv_pi_mul_norm_sq_eq_re V Q c hc hQ
  obtain ⟨N₂, hD₂, hL₂, hG₂, hdense⟩ := GlobalTheory.T.schwartz_density_transport_linearEquiv_chirp V _ A Q N hA hD hL
  apply hdense
  let G := GroundTheory.Global.gaussianSchwartz (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))
  have hG : ∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro y
    simp only [G, GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
    congr 1; push_cast; ring
  exact dense_of_stdGaussian_mem _ N₂ G hG (hG₂ g G hg hgN hG) hD₂ hL₂

end GlobalTheory.SchwartzGaussDense
end
end
