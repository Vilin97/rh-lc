module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfD
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalTorusParametrisationOrthonormalFra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecialUnitarySectionLowerUnitriangularChaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarSpecialUnitaryProductChartFormula
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtMulCurvesMatrixGroupIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixGroupChartDensityAtIdentityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianMeasureLieAlgebraEqSmulMapChartLebesguStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryNearOneEqChartMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyRealDegreeAndChartDimensionEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityContinuousAtZeroEqOne

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

namespace GlobalTheory.DensOne

open ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq_mul (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * (G.map τ * x.map (starRingEnd ℂ)) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem det_ne_zero_of_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (τ : X.Ψ) :
    (mat x τ).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (hx τ)
  rw [gram_eq_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, Matrix.det_diagonal] at h1
  refine (Finset.prod_ne_zero_iff.2 fun a _ => ?_) h1.symm
  exact_mod_cast sgn_ne X.p0 (a : ℕ)

theorem densF_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) :
    densF X x = fun w => ∏ τ, ∏ i : Fin r, ‖lminor (Gw X w τ) i.castSucc‖ ^ (-2 : ℤ) := by
  funext w
  unfold densF
  simp only [dmin_cpt_orth X hx]

theorem dens_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r), IsOrth X x → ContinuousAt (densF X x) 0 ∧ densF X x 0 = 1 ∧
      ∀ τ, (mat x τ).det ≠ 0 := by
  intro E _ _ _ r X x hx
  refine ⟨?_, ?_, det_ne_zero_of_orth X hx⟩
  · rw [densF_orth X hx]
    refine tendsto_finsetProd _ fun τ _ => tendsto_finsetProd _ fun i _ => ?_
    refine ((cont_lminor X τ i.castSucc).norm.continuousAt).zpow₀ _ (Or.inl ?_)
    simp [norm_lminor_zero]
  · rw [densF_orth X hx]
    simp only [norm_lminor_zero, _root_.one_zpow, Finset.prod_const_one]

end GlobalTheory.DensOne
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDensityContinuousAtZeroEqOneStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.chartDensity_continuousAt_zero_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ContinuousAt (densF X x) 0 ∧ densF X x 0 = 1 ∧ ∀ τ, (mat x τ).det ≠ 0 := by
  first | exact @GlobalTheory.DensOne.dens_one | exact GlobalTheory.DensOne.dens_one | (intros; apply GlobalTheory.DensOne.dens_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalTorusParametrisationOrthonormalFraStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.exists_diagonalTorus_parametrisation_orthonormalFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → ∃ (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (Dt : (X.Ψ → Fin (r - 1) → ℝ) →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ)), (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) ∧ (∀ θ θ', t (θ + θ') = t θ * t θ') ∧ Continuous t ∧ HasStrictFDerivAt (fun θ => (fun τ a b => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b)) Dt 0 ∧ (∀ θ, Dt θ ∈ realLie X.Ψ X.Gm ∧ ∀ τ a b, inFrame x (Dt θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0) ∧ (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) := by
  first | exact @GlobalTheory.TorusFrame.torus_param | exact GlobalTheory.TorusFrame.torus_param | (intros; apply GlobalTheory.TorusFrame.torus_param <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarSpecialUnitaryProductChartFormulaStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.haar_specialUnitary_product_chart_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (ν : Measure (realSU X.Ψ X.Gm)) (σ : V (nd X) → realSU X.Ψ X.Gm) (t : (X.Ψ → Fin (r - 1) → ℝ) → realSU X.Ψ X.Gm) (ρ : ℝ), 1 ≤ r → IsOrth X x → ν.IsHaarMeasure → (∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) → ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν = ∫⁻ z, φ (cpt X x z) ∂muF X x) → 0 < ρ → ContinuousOn σ (Metric.ball 0 ρ) → (∀ z ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((σ z : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul (cpt X x z) b) → (∀ θ, X.lmulC (fun τ => ((((t θ : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x (phaseFrame θ)) → (∀ θ θ', t (θ + θ') = t θ * t θ') → Continuous t → (∀ g : realSU X.Ψ X.Gm, (∃ b ∈ Bor X.Ψ r, X.lmulC (fun τ => ((((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) x = rmul x b) → ∃ θ, g = t θ) → ∀ A : Set (ChartSp X), MeasurableSet A → A ⊆ Metric.ball 0 (min ρ Real.pi) → ν ((fun w : ChartSp X => σ w.1 * t w.2) '' A) = ∫⁻ w in A, ENNReal.ofReal (densF X x w.1 / (2 * Real.pi) ^ ((r - 1) * X.Ψ.card)) ∂(volume : Measure (ChartSp X)) := by
  first | exact @GlobalTheory.FibreVol.haar_chart_formula | exact GlobalTheory.FibreVol.haar_chart_formula | (intros; apply GlobalTheory.FibreVol.haar_chart_formula <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyRealDegreeAndChartDimensionEqStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem _root_.GlobalTheory.T.totallyRealDegree_and_chartDimension_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), fdeg E = X.Ψ.card ∧ nd X = X.Ψ.card * (r * (r - 1) / 2) := by
  first | exact @GlobalTheory.ChartCount.fdeg_and_nd | exact GlobalTheory.ChartCount.fdeg_and_nd | (intros; apply GlobalTheory.ChartCount.fdeg_and_nd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarSpecialUnitaryEqSmulHaar

section

@[expose] public section

open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

noncomputable section

namespace GlobalTheory.RiemConst

theorem riemHaar_eq_smul (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)]
    (ν : Measure (realSU X.Ψ X.Gm)) (hr : 1 ≤ r) (hx : IsOrth X x) (hν : ν.IsHaarMeasure)
    (hfib : ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) →
      ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν =
        ∫⁻ z, φ (cpt X x z) ∂muF X x) :
    riemHaar X.Ψ X.Gm x = ENNReal.ofReal
      (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) • ν := by
  obtain ⟨hdc, hd0, hdet⟩ := GlobalTheory.T.chartDensity_continuousAt_zero_eq_one E r X x hx
  obtain ⟨hf, hnd⟩ := GlobalTheory.T.totallyRealDegree_and_chartDimension_eq E r X
  obtain ⟨σ, ρ, D₁, hρ, hσ0, hσc, hσB, hσD, hD₁⟩ := GlobalTheory.T.exists_specialUnitary_section_lowerUnitriangular_chart E r X x hx
  obtain ⟨t, Dt, htx, htmul, htc, htD, hDt, hstab⟩ := GlobalTheory.T.exists_diagonalTorus_parametrisation_orthonormalFrame E r X x hx
  have ht0 : t 0 = 1 := by
    have h := congrArg (fun g => (t 0)⁻¹ * g) (htmul 0 0)
    simp only [add_zero, inv_mul_cancel, inv_mul_cancel_left] at h
    exact h.symm
  let D : ChartSp X →L[ℝ] (X.Ψ → Fin r → Fin r → ℂ) :=
    D₁.comp (ContinuousLinearMap.fst ℝ (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ)) +
      Dt.comp (ContinuousLinearMap.snd ℝ (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ))
  have hQD := GlobalTheory.T.hasStrictFDerivAt_mul_curves_matrixGroup_identity X.Ψ r (realSU X.Ψ X.Gm) (V (nd X)) (X.Ψ → Fin (r - 1) → ℝ) σ t D₁ Dt hσ0 ht0 hσD htD
  have hspec : ∀ w : ChartSp X, D w ∈ realLie X.Ψ X.Gm ∧
      (∀ τ a b, b < a → inFrame x (D w) τ a b = nmat X w.1 τ a b) ∧
        ∀ τ a, inFrame x (D w) τ a a = Complex.I * (angles (w.2 τ) a : ℂ) := by
    intro w
    have hDw : D w = D₁ w.1 + Dt w.2 := rfl
    have e : ∀ τ, inFrame x (D w) τ = inFrame x (D₁ w.1) τ + inFrame x (Dt w.2) τ := by
      intro τ
      simp only [inFrame, hDw]
      rw [show Matrix.of ((D₁ w.1 + Dt w.2) τ) = Matrix.of (D₁ w.1 τ) + Matrix.of (Dt w.2 τ) from rfl,
        Matrix.mul_add, Matrix.add_mul]
    obtain ⟨h1, h2, h3⟩ := hD₁ w.1
    obtain ⟨h4, h5⟩ := hDt w.2
    refine ⟨?_, fun τ a b hab => ?_, fun τ a => ?_⟩
    · rw [hDw]; exact (realLie X.Ψ X.Gm).add_mem h1 h4
    · rw [e, Matrix.add_apply, h2 τ a b hab, h5, if_neg (ne_of_gt hab), add_zero]
    · rw [e, Matrix.add_apply, h3, h5, if_pos rfl, zero_add]
  obtain ⟨hDinj, hriem⟩ := GlobalTheory.T.riemannianMeasure_lieAlgebra_eq_smul_map_chartLebesgue E r X x hr hx D hspec
  have hform := GlobalTheory.T.haar_specialUnitary_product_chart_formula E r X x ν σ t ρ hr hx hν hfib hρ hσc hσB htx htmul htc hstab
  have hsurj := GlobalTheory.T.specialUnitary_near_one_eq_chart_mul E r X x σ t ρ hx hρ hσ0 hσc hσB htx htmul htc hstab
  set m := (r - 1) * X.Ψ.card with hm
  set a : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * Real.pi) ^ m) with ha
  have hpi : 0 < (2 * Real.pi) ^ m := by positivity
  have ha0 : a ≠ 0 := by
    rw [ha, Ne, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hatop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have htend : Tendsto (fun w : ChartSp X => ENNReal.ofReal (densF X x w.1 / (2 * Real.pi) ^ m)) (𝓝 0) (𝓝 a) := by
    have h1 : ContinuousAt (fun w : ChartSp X => densF X x w.1) 0 :=
      ContinuousAt.comp (g := densF X x) (f := Prod.fst) (x := (0 : ChartSp X)) hdc continuous_fst.continuousAt
    have h2 := (ENNReal.continuous_ofReal.continuousAt).tendsto.comp ((h1.div_const ((2 * Real.pi) ^ m)).tendsto)
    rw [ha]
    simpa [Function.comp_def, hd0] using h2
  have hρ' : 0 < min ρ Real.pi := lt_min hρ Real.pi_pos
  have hQ0 : (fun w : ChartSp X => σ w.1 * t w.2) 0 = 1 := by simp [hσ0, ht0]
  haveI : (volume : Measure (X.Ψ → Fin (r - 1) → ℝ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (ChartSp X)).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (V (nd X))) (volume : Measure (X.Ψ → Fin (r - 1) → ℝ))
  have hlim := GlobalTheory.T.matrixGroup_chart_density_at_identity X.Ψ r (realSU X.Ψ X.Gm) ν (ChartSp X) volume (fun w => σ w.1 * t w.2) D
    (fun w => ENNReal.ofReal (densF X x w.1 / (2 * Real.pi) ^ m)) a (min ρ Real.pi) hQD hQ0 hDinj hsurj htend
    ha0 hatop hρ' hform
  obtain ⟨hRH, hRdens⟩ := GlobalTheory.SUVol.DensOne.tangentHaar_riemLie X.Ψ X.Gm X.Gm_det x hdet
  have hRH' : (riemHaar X.Ψ X.Gm x).IsHaarMeasure := hRH
  set k := (riemHaar X.Ψ X.Gm x).haarScalarFactor ν with hkdef
  have hk : riemHaar X.Ψ X.Gm x = k • ν := Measure.isMulLeftInvariant_eq_smul _ _
  set K := ENNReal.ofReal (2 ^ nd X * Real.sqrt r ^ X.Ψ.card) with hKdef
  have hK0 : K ≠ 0 := by
    rw [hKdef, Ne, ENNReal.ofReal_eq_zero, not_le]
    have : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast hr)
    positivity
  have hKtop : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have h1 : Tendsto (fun ε : ℝ => (k : ℝ≥0∞) * (ν (grpBall (realSU X.Ψ X.Gm) ε) /
      ((volume : Measure (ChartSp X)).map D) (tanBall X.Ψ r ε)) * K⁻¹) (𝓝[>] 0) (𝓝 ((k : ℝ≥0∞) * a * K⁻¹)) :=
    ENNReal.Tendsto.mul_const (ENNReal.Tendsto.const_mul hlim (Or.inr ENNReal.coe_ne_top))
      (Or.inr (ENNReal.inv_ne_top.2 hK0))
  unfold HasDensityOne at hRdens
  have h2 : Tendsto (fun ε : ℝ => (k : ℝ≥0∞) * (ν (grpBall (realSU X.Ψ X.Gm) ε) /
      ((volume : Measure (ChartSp X)).map D) (tanBall X.Ψ r ε)) * K⁻¹) (𝓝[>] 0) (𝓝 1) := by
    refine hRdens.congr fun ε => ?_
    rw [show tangentHaar (realSU X.Ψ X.Gm) (riemLie X.Ψ X.Gm x) = riemHaar X.Ψ X.Gm x from rfl, hk, hriem]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hK0) (Or.inl hKtop)]
    ring
  have e := tendsto_nhds_unique h1 h2
  have hkval : (k : ℝ≥0∞) = ENNReal.ofReal
      (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) := by
    have e' : (k : ℝ≥0∞) * (a * K⁻¹) = 1 := by rw [← mul_assoc]; exact e
    have hai : a⁻¹ = ENNReal.ofReal ((2 * Real.pi) ^ m) := by
      rw [ha, ← ENNReal.ofReal_inv_of_pos (by positivity), one_div, inv_inv]
    rw [ENNReal.eq_inv_of_mul_eq_one_left e', ENNReal.mul_inv (Or.inl ha0) (Or.inl hatop), inv_inv, hai,
      hKdef, ← ENNReal.ofReal_mul hpi.le]
    congr 1
    rw [hf, hnd, hm]
    generalize r * (r - 1) / 2 = n1
    generalize r - 1 = n2
    ring
  rw [hk, ← hkval]
  ext s _
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

end GlobalTheory.RiemConst
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarSpecialUnitaryEqSmulHaarStatement

section

@[expose] public section

open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

theorem _root_.GlobalTheory.T.riemannianHaar_specialUnitary_eq_smul_haar : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (ν : Measure (realSU X.Ψ X.Gm)), 1 ≤ r → IsOrth X x → ν.IsHaarMeasure → (∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y) → ∫⁻ g, φ (X.lmulC (fun τ => (((g : realSU X.Ψ X.Gm) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x) ∂ν = ∫⁻ z, φ (cpt X x z) ∂muF X x) → riemHaar X.Ψ X.Gm x = ENNReal.ofReal (((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E) • ν := by
  first | exact @GlobalTheory.RiemConst.riemHaar_eq_smul | exact GlobalTheory.RiemConst.riemHaar_eq_smul | (intros; apply GlobalTheory.RiemConst.riemHaar_eq_smul <;> assumption)
end
end
