module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PolarCut
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Algebra.Module.FiniteDimension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SqChartCore
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExistsLocalSolutionContDiffAt

section

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open Topology Filter

theorem exists_local_solution_contDiffAt {V : Type} [AddCommGroup V] [TopologicalSpace V] {N : ℕ}
    (e : V ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y)
    (B : V → V → V) (hB1 : ∀ x x' y, B (x + x') y = B x y + B x' y)
    (hB2 : ∀ x y y', B x (y + y') = B x y + B x y')
    (hBc : Continuous (fun p : V × V => B p.1 p.2))
    (L : V → V) (hL : ∀ x y, L (x + y) = L x + L y) (hLc : Continuous L)
    (x0 : V) (hD : ∀ u, B x0 u + B u x0 + L u = u + u) :
    ∃ g : V → V, ContinuousAt g (B x0 x0 + L x0) ∧ g (B x0 x0 + L x0) = x0 ∧
      (∀ᶠ y in 𝓝 (B x0 x0 + L x0), B (g y) (g y) + L (g y) = y) ∧
      ContDiffAt ℝ 1 (fun y => e (g (e.symm y))) (e (B x0 x0 + L x0)) ∧
      HasFDerivAt (fun y => e (g (e.symm y))) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
        (e (B x0 x0 + L x0)) := by
  classical
  have hes : ∀ u w, e.symm (u + w) = e.symm u + e.symm w := by
    intro u w
    apply e.injective
    rw [he]
    simp
  let b : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) := fun u w => e (B (e.symm u) (e.symm w))
  let l : (Fin N → ℝ) → (Fin N → ℝ) := fun u => e (L (e.symm u))
  have hb1 : ∀ u u' w, b (u + u') w = b u w + b u' w := by
    intro u u' w
    simp only [b, hes, hB1, he]
  have hb2 : ∀ u w w', b u (w + w') = b u w + b u w' := by
    intro u w w'
    simp only [b, hes, hB2, he]
  have hl1 : ∀ u u', l (u + u') = l u + l u' := by
    intro u u'
    simp only [l, hes, hL, he]
  have hbc : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => b p.1 p.2) :=
    e.continuous.comp (hBc.comp ((e.symm.continuous.comp continuous_fst).prodMk
      (e.symm.continuous.comp continuous_snd)))
  have hlc : Continuous l := e.continuous.comp (hLc.comp e.symm.continuous)
  have hbs1 : ∀ (c : ℝ) u w, b (c • u) w = c • b u w := by
    intro c u w
    exact map_real_smul (AddMonoidHom.mk' (fun u => b u w) (fun u u' => hb1 u u' w))
      (hbc.comp (continuous_id.prodMk continuous_const)) c u
  have hbs2 : ∀ (c : ℝ) u w, b u (c • w) = c • b u w := by
    intro c u w
    exact map_real_smul (AddMonoidHom.mk' (fun w => b u w) (fun w w' => hb2 u w w'))
      (hbc.comp (continuous_const.prodMk continuous_id)) c w
  let b₂ : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) := LinearMap.mk₂ ℝ b hb1 hbs1 hb2 hbs2
  let bL : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : ((Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ)) ≃ₗ[ℝ]
        ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ))).toLinearMap ∘ₗ b₂)
  let lL : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (AddMonoidHom.mk' l hl1).toRealLinearMap hlc
  have hbL : ∀ u w, bL u w = b u w := fun u w => rfl
  have hlL : ∀ u, lL u = l u := fun u => rfl
  let Ft : (Fin N → ℝ) → (Fin N → ℝ) := fun u => bL u u + lL u
  have hFt : ∀ u, Ft u = e (B (e.symm u) (e.symm u) + L (e.symm u)) := by
    intro u
    simp only [Ft, hbL, hlL, b, l, he]
  set u0 := e x0 with hu0
  have hy0 : Ft u0 = e (B x0 x0 + L x0) := by rw [hFt, hu0, e.symm_apply_apply]
  have hTwo : ∀ w, bL u0 w + bL w u0 + lL w = (2 : ℝ) • w := by
    intro w
    have h := congrArg e (hD (e.symm w))
    rw [he, he, he, e.apply_symm_apply] at h
    rw [hbL, hbL, hlL, two_smul]
    simpa [b, l, hu0] using h
  let f₁ : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ)
  let f₂ : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) := (1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ)
  have h12 : Function.LeftInverse f₂ f₁ := fun w => by
    simp only [f₁, f₂, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    norm_num
  have h21 : Function.RightInverse f₂ f₁ := fun w => by
    simp only [f₁, f₂, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    norm_num
  let fe : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ) := ContinuousLinearEquiv.equivOfInverse f₁ f₂ h12 h21
  have hFs : HasStrictFDerivAt Ft (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) u0 := by
    have h0 := (bL.hasStrictFDerivAt_of_bilinear (hasStrictFDerivAt_id u0)
      (hasStrictFDerivAt_id u0)).add lL.hasStrictFDerivAt
    refine h0.congr_fderiv ?_
    ext1 w
    show bL u0 w + bL w u0 + lL w = (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) w
    rw [hTwo]
    rfl
  have hcd : ContDiffAt ℝ 1 Ft u0 :=
    ((bL.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)).add
      lL.contDiff).contDiffAt
  have hs : HasStrictFDerivAt Ft (fe : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) u0 :=
    hcd.hasStrictFDerivAt' hFs.hasFDerivAt one_ne_zero
  let G := hcd.localInverse hFs.hasFDerivAt one_ne_zero
  have hGc : ContinuousAt G (Ft u0) := hs.localInverse_continuousAt
  have hGa : G (Ft u0) = u0 := hs.localInverse_apply_image
  have hGr : ∀ᶠ w in 𝓝 (Ft u0), Ft (G w) = w := hs.eventually_right_inverse
  have hGd : ContDiffAt ℝ 1 G (Ft u0) := hcd.to_localInverse hFs.hasFDerivAt one_ne_zero
  have hGf : HasFDerivAt G ((fe.symm : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) (Ft u0) :=
    hs.to_localInverse.hasFDerivAt
  rw [hy0] at hGc hGa hGr hGd hGf
  refine ⟨fun y => e.symm (G (e y)), ?_, ?_, ?_, ?_, ?_⟩
  · exact e.symm.continuous.continuousAt.comp (hGc.comp e.continuous.continuousAt)
  · simp only [hGa, hu0, e.symm_apply_apply]
  · have ht : ∀ᶠ y in 𝓝 (B x0 x0 + L x0), Ft (G (e y)) = e y :=
      (e.continuous.tendsto (B x0 x0 + L x0)).eventually hGr
    filter_upwards [ht] with y hy
    rw [hFt] at hy
    exact e.injective (by rw [he]; simpa [he] using hy)
  · have hfun : (fun y => e (e.symm (G (e (e.symm y))))) = G := by
      funext y
      simp
    rw [hfun]
    exact hGd
  · have hfun : (fun y => e (e.symm (G (e (e.symm y))))) = G := by
      funext y
      simp
    rw [hfun]
    convert hGf using 1
    ext1 w
    rfl

end PI.AprimeInfW
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SquareChartC1Local

section

@[expose] public section

noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  Formalism.L2.SG.Sub Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct Matrix

theorem square_chart_c1_local {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {M m : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Y : Fin m → Fin M → E) (hT : ∀ i j, σ (gramE σ J Y j i) = gramE σ J Y i j) (hdet : (gramE σ J Y).det ≠ 0)
    {N : ℕ} (e : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) ≃ₜ (Fin N → ℝ)) (he : ∀ x y, e (x + y) = e x + e y) :
    ∃ (Ω : Set (HermR (Ainf F) σ m)) (a : HermR (Ainf F) σ m → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)),
      Ω ∈ 𝓝 (hermOf (Ainf F) σ (gramE σ J Y) hT) ∧ a (hermOf (Ainf F) σ (gramE σ J Y) hT) = 1 ∧
      ContinuousAt a (hermOf (Ainf F) σ (gramE σ J Y) hT) ∧
      (∀ T ∈ Ω, gramR (Ainf F) σ J (fun b i => ∑ c, a T c b * ratTup (Ainf F) Y c i) = (T : Matrix _ _ _)) ∧
      ∀ {η μ' : Type} [Fintype η] [Fintype μ'] (eH : HermR (Ainf F) σ m ≃ₜ EuclideanSpace ℝ η)
        (eM : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) ≃ₜ EuclideanSpace ℝ μ'),
        (∀ x y, eH (x + y) = eH x + eH y) → (∀ x y, eM (x + y) = eM x + eM y) →
        ContDiffAt ℝ 1 (fun z => eM (a (eH.symm z))) (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) ∧
        ∀ v, fderiv ℝ (fun z => eM (a (eH.symm z))) (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) v =
          (1 / 2 : ℝ) • eM ((gramE σ J Y)⁻¹.map (inclR (Ainf F)) *
            ((eH.symm v : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))) := by
  classical
  set G := gramE σ J Y with hG
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hdet
  set Tm : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := G.map (inclR (Ainf F)) with hTm
  set Ti : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := G⁻¹.map (inclR (Ainf F)) with hTi
  have hTTi : Tm * Ti = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.mul_nonsing_inv G hu, Matrix.map_one _ (map_zero _) (map_one _)]
  have hTiT : Ti * Tm = 1 := by
    rw [hTm, hTi, ← Matrix.map_mul, Matrix.nonsing_inv_mul G hu, Matrix.map_one _ (map_zero _) (map_one _)]
  set c : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) :=
    Formalism.UG.cT (sigR (Ainf F) σ) with hc
  have hsig := sq_sig_inv (Ainf F) σ hσ
  have hcc : ∀ P, c (c P) = P := by intro P; ext i j; simp [hc, Formalism.UG.cT, hsig]
  have hcadd : ∀ P Q, c (P + Q) = c P + c Q := by intro P Q; ext i j; simp [hc, Formalism.UG.cT]
  have hcsub : ∀ P Q, c (P - Q) = c P - c Q := by intro P Q; ext i j; simp [hc, Formalism.UG.cT]
  have hcmul : ∀ P Q, c (P * Q) = c Q * c P := fun P Q => Formalism.UG.cT_mul _ P Q
  have hc1 : c 1 = 1 := Formalism.UG.cT_one _
  have hcT : c Tm = Tm := by
    ext i j
    simp only [hc, Formalism.UG.cT, hTm, Matrix.transpose_apply, Matrix.map_apply]
    rw [← hT i j]
    simp [sigR, inclR]
  have hcTi : c Ti * Tm = 1 := by
    calc c Ti * Tm = c Ti * c Tm := by rw [hcT]
      _ = c (Tm * Ti) := (hcmul Tm Ti).symm
      _ = 1 := by rw [hTTi, hc1]
  have hcont_c : Continuous c := by
    show Continuous fun P : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) => (P.map (sigR (Ainf F) σ))ᵀ
    exact (continuous_id.matrix_map (continuous_sigRP (Ainf F) σ)).matrix_transpose
  set Bq : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) →
      Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) := fun h k => c (Ti * h) * Tm * (Ti * k) with hBq
  set Lq : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) → Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E) :=
    fun h => h - c h with hLq
  have hD : ∀ u, Bq Tm u + Bq u Tm + Lq u = u + u := by
    intro u
    simp only [hBq, hLq]
    rw [hTiT, hc1, Matrix.one_mul, Matrix.mul_one, ← Matrix.mul_assoc Tm Ti u, hTTi, Matrix.one_mul, hcmul Ti u,
      Matrix.mul_assoc (c u) (c Ti) Tm, hcTi, Matrix.mul_one]
    abel
  obtain ⟨g, hgc, hg0, hgev, hgcd, hgd⟩ := exists_local_solution_contDiffAt e he Bq
    (by intro x x' y; simp only [hBq, Matrix.mul_add, hcadd, Matrix.add_mul])
    (by intro x y y'; simp only [hBq, Matrix.mul_add])
    (((hcont_c.comp (continuous_const.matrix_mul continuous_fst)).matrix_mul continuous_const).matrix_mul
      (continuous_const.matrix_mul continuous_snd))
    Lq (by intro x y; simp only [hLq, hcadd]; abel) (continuous_id.sub hcont_c) Tm hD
  have hy0 : Bq Tm Tm + Lq Tm = Tm := by
    simp only [hBq, hLq]
    rw [hTiT, hc1, Matrix.one_mul, Matrix.mul_one, hcT, sub_self, add_zero]
  rw [hy0] at hgc hg0 hgev hgcd hgd
  refine ⟨Subtype.val ⁻¹' {y | Bq (g y) (g y) + Lq (g y) = y}, fun T => Ti * g T.val, ?_, ?_, ?_, ?_, ?_⟩
  · exact continuous_subtype_val.continuousAt.preimage_mem_nhds hgev
  · show Ti * g Tm = 1
    rw [hg0, hTiT]
  · exact (continuous_const.matrix_mul continuous_id).continuousAt.comp
      (ContinuousAt.comp_of_eq hgc continuous_subtype_val.continuousAt rfl)
  · intro T hT'
    have hT'' : Bq (g T.val) (g T.val) + Lq (g T.val) = T.val := hT'
    show gramR (Ainf F) σ J (fun b i => ∑ c, (Ti * g T.val) c b * ratTup (Ainf F) Y c i) = T.val
    rw [sq_gramR_rmul (Ainf F) σ J (Ti * g T.val) (ratTup (Ainf F) Y), gramR_ratTup]
    set h := g T.val
    have hP : c (Bq h h) = Bq h h := by
      simp only [hBq]
      rw [hcmul (c (Ti * h) * Tm) (Ti * h), hcmul (c (Ti * h)) Tm, hcc, hcT, Matrix.mul_assoc]
    have hTh : c T.val = T.val := by
      ext i j
      exact T.2 i j
    have hLL : c (Lq h) = -(Lq h) := by
      simp only [hLq]
      rw [hcsub, hcc]
      abel
    have h2 : Lq h + Lq h = 0 := by
      have e1 := congrArg c hT''
      rw [hcadd, hP, hLL, hTh] at e1
      have e2 := add_left_cancel (hT''.trans e1.symm)
      exact eq_neg_iff_add_eq_zero.mp e2
    have h0 : Lq h = 0 := by
      calc Lq h = ((1 / 2 : F) * 2) • Lq h := by norm_num
        _ = (1 / 2 : F) • (Lq h + Lq h) := by rw [mul_smul, two_smul]
        _ = 0 := by rw [h2, smul_zero]
    rw [h0, add_zero] at hT''
    exact hT''
  · intro η μ' _ _ eH eM heH heM
    have hHs : ∀ x y, eH.symm (x + y) = eH.symm x + eH.symm y := by
      intro x y; apply eH.injective; rw [heH]; simp
    have hes : ∀ x y, e.symm (x + y) = e.symm x + e.symm y := by
      intro x y; apply e.injective; rw [he]; simp
    let L₁ : EuclideanSpace ℝ η →L[ℝ] (Fin N → ℝ) :=
      (AddMonoidHom.mk' (fun z => e ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)))
        (by intro x y; simp only [hHs, AddSubgroup.coe_add, he])).toRealLinearMap
        (e.continuous.comp (continuous_subtype_val.comp eH.symm.continuous))
    let L₂ : (Fin N → ℝ) →L[ℝ] EuclideanSpace ℝ μ' :=
      (AddMonoidHom.mk' (fun y => eM (Ti * e.symm y)) (by intro x y; simp only [hes, Matrix.mul_add, heM])).toRealLinearMap
        (eM.continuous.comp ((continuous_const.matrix_mul continuous_id).comp e.symm.continuous))
    have hL₁ : ∀ z, L₁ z = e ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)) := fun z => rfl
    have hL₂ : ∀ y, L₂ y = eM (Ti * e.symm y) := fun y => rfl
    have hfun : (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E)))) =
        fun z => L₂ ((fun y => e (g (e.symm y))) (L₁ z)) := by
      funext z
      rw [hL₁, hL₂]
      simp only [Homeomorph.symm_apply_apply]
    have hpt : L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) = e Tm := by
      rw [hL₁, Homeomorph.symm_apply_apply]; rfl
    have hgcd' : ContDiffAt ℝ 1 (fun y => e (g (e.symm y))) (L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))) := by
      rw [hpt]; exact hgcd
    have hgd' : HasFDerivAt (fun y => e (g (e.symm y))) ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Fin N → ℝ))
        (L₁ (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))) := by
      rw [hpt]; exact hgd
    have hD := L₂.hasFDerivAt.comp (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) (hgd'.comp _ L₁.hasFDerivAt)
    refine ⟨?_, ?_⟩
    · show ContDiffAt ℝ 1 (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))))
        (eH (hermOf (Ainf F) σ (gramE σ J Y) hT))
      rw [hfun]
      exact L₂.contDiff.contDiffAt.comp _ (hgcd'.comp _ L₁.contDiff.contDiffAt)
    · intro v
      show fderiv ℝ (fun z => eM (Ti * g ((eH.symm z : HermR (Ainf F) σ m) : Matrix (Fin m) (Fin m) (Ainf F ⊗[F] E))))
        (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) v = _
      have hD' : HasFDerivAt (fun z => L₂ ((fun y => e (g (e.symm y))) (L₁ z))) _
          (eH (hermOf (Ainf F) σ (gramE σ J Y) hT)) := hD
      rw [hfun, hD'.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
        map_smul]
      rw [hL₂, hL₁, Homeomorph.symm_apply_apply]

def TinvI {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : MfI X :=
  (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')))⁻¹.map (inclR (Ainf X.B.I.F))

def SquareChartC1 : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∃ Ω a, IsChart X u' hT Ω a ∧
      ∀ {η μ' : Type} [Fintype η] [Fintype μ'] (eH : HmI X ≃ₜ EuclideanSpace ℝ η)
        (eM : MfI X ≃ₜ EuclideanSpace ℝ μ'),
        (∀ x y, eH (x + y) = eH x + eH y) → (∀ x y, eM (x + y) = eM x + eM y) →
        ContDiffAt ℝ 1 (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) ∧
        ∀ v, fderiv ℝ (fun z => eM (a (eH.symm z))) (eH (TI X u' hT)) v =
          (1 / 2 : ℝ) • eM (TinvI X u' * ((eH.symm v : HmI X) : Matrix _ _ _))

theorem square_chart_c1 : SquareChartC1 := by
  intro D X u' ψ hT μinf νinf fibInf hP
  haveI : IsTotallyReal X.B.I.F := X.B.I.cm.totReal
  haveI : FiniteDimensional X.B.I.F X.B.I.E :=
    Module.finite_of_finrank_pos (by rw [X.B.I.cm.deg2]; norm_num)
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => star_star x
  have hdet := detNZ_holds X u' ψ hT μinf νinf fibInf hP
  obtain ⟨k, eK, hK⟩ := sq_coord_tens X.B.I.F X.B.I.E
  obtain ⟨k1, e1, h1⟩ := sq_coord_pi eK hK (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨N, eM, hM⟩ := sq_coord_pi e1 h1 (Fin (D.R.rS + 1 + D.R.rS))
  obtain ⟨Ω, a, h1', h2', h3', h4', h5'⟩ :=
    square_chart_c1_local X.B.I.cm.sig hσ X.B.I.J (tupH (frameOf X u')) hT hdet eM hM
  exact ⟨Ω, a, ⟨h1', h2', h3', fun T hT' => h4' T hT'⟩, fun eH eM' heH heM => h5' eH eM' heH heM⟩

end PI.AprimeInfW
end
end
end
