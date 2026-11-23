module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAffineNeighbourhoodExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureEqOfIsometricProj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackChartMetricBlockForm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
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
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicChartsGenericPointProjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernFormSignedPartMeasureComplOpenGenericP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedClosureOfPointProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericNeZeroEquidimensional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointNeZeroProjectiveSameDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleIsometryCalculus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TopSelfEqLengthOfSmooth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonKernelHessiansPullbackSmallerChart

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.HessKer

open ReciprocityTheory.L2DbarEstimates (V cHess bas)

theorem exists_vecMul_eq_zero {D D' : ℕ} (h : D' < D) (P : Matrix (Fin D) (Fin D') ℂ) :
    ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ Matrix.vecMul ξ P = 0 := by
  have hk : LinearMap.ker P.vecMulLinear ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using h)
  obtain ⟨ξ, hξ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  exact ⟨ξ, h0, by simpa using hξ⟩

theorem exists_common_kernel : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D D' : ℕ), D' < D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (c : AlgChart p σ D') (c' : AlgChart q σ D) (w : CxPts q σ), w ∈ c'.e.source → ptMap π hπ σ w ∈ c.e.source → ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ ∀ (A : MLine p σ) (i : (A.pull π hπ).B.ι), w ∈ ptsIn q σ ((A.pull π hπ).B.U i) → Matrix.vecMul ξ (c'.hess (A.pull π hπ).φ i w) = 0 := by
  intro k _ X Y p q σ D D' hD π hπ c c' y hy hy0
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  set F : V D → V D' := c.e ∘ m ∘ c'.e.symm with hFdef
  set U := c'.e.target ∩ c'.e.symm ⁻¹' (m ⁻¹' c.e.source)
  have hU : IsOpen U := isOpen_over c'.e (c.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c'.e y ∈ U := mem_over c'.e hy hy0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c' c
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c'.e y) = c.e (m y) := by
    simp only [hFdef, Function.comp_apply, c'.e.left_inv hy]
  obtain ⟨ξ, hξ, hP⟩ := exists_vecMul_eq_zero hD (Matrix.of fun j b => fderiv ℂ F (c'.e y) (bas D j) b)
  refine ⟨ξ, hξ, fun A i hi => ?_⟩
  have him : m y ∈ ptsIn p σ (A.B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hi PUnit.unit
  set g : V D' → ℂ := fun v => (A.φ.φ (i PUnit.unit) (c.e.symm v) : ℂ)
  have hg : ContDiffAt ℝ 2 g (F (c'.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (A.cInf.contDiffAt c hy0 him)
  have e : (fun v => ((A.pull π hπ).φ.φ i (c'.e.symm v) : ℂ)) =ᶠ[𝓝 (c'.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ A.φ π hπ i (c'.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c.e.left_inv hv.2]
    exact congrArg _ this
  have key : c'.hess (A.pull π hπ).φ i y =
      (Matrix.of fun j b => fderiv ℂ F (c'.e y) (bas D j) b) * (cHess D' g (F (c'.e y)) *
        Matrix.of fun a l => (starRingEnd ℂ) (fderiv ℂ F (c'.e y) (bas D l) a)) := by
    show cHess D _ (c'.e y) = _
    rw [ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e, ← Matrix.mul_assoc]
    ext j l
    rw [GlobalTheory.HessPull.cHess_comp_apply D D' g F U hU _ hyU hF hg j l, Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [key, ← Matrix.vecMul_vecMul, hP, Matrix.zero_vecMul]

end GlobalTheory.HessKer
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonKernelHessiansPullbackSmallerChartStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.exists_common_kernel_hessians_pullback_smaller_chart : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D D' : ℕ), D' < D → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (c : AlgChart p σ D') (c' : AlgChart q σ D) (w : CxPts q σ), w ∈ c'.e.source → ptMap π hπ σ w ∈ c.e.source → ∃ ξ : Fin D → ℂ, ξ ≠ 0 ∧ ∀ (A : MLine p σ) (i : (A.pull π hπ).B.ι), w ∈ ptsIn q σ ((A.pull π hπ).B.U i) → Matrix.vecMul ξ (c'.hess (A.pull π hπ).φ i w) = 0 := by
  exact @GlobalTheory.HessKer.exists_common_kernel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasurePullbackEqZeroOfLtDim

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixDrop

theorem part_pull_eq_zero : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D D' : ℕ), D' < D → IsProjOver p → topologicalKrullDim X = (D' : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (L : Fin D → MLine p σ) (ε : ℤˣ), part (fun i => (L i).pull π hπ) ε = 0 := by
  intro F _ X Y _ _ p q σ D D' hD hp hX hq π hπ hgen L ε
  have hLN : IsLocallyNoetherian X := by
    obtain ⟨N, ι, _, h⟩ := hp
    have : LocallyOfFiniteType p := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U, hU, hch⟩ := GlobalTheory.GenericCharts.exists_generic_charts F X p σ D' hp hX
  have hgU : genericPoint Y ∈ π ⁻¹ᵁ U := by
    show π (genericPoint Y) ∈ U
    rw [hgen]; exact hU
  have hnull := GlobalTheory.MixNull.part_compl_null F Y q σ σ.injective hq D (fun i => (L i).pull π hπ) ε (π ⁻¹ᵁ U) hgU
  have hz : ∀ (c : AlgChart q σ D) (w : CxPts q σ), w ∈ c.e.source → w ∈ ptsIn q σ (π ⁻¹ᵁ U) →
      dens (fun i => (L i).pull π hπ) c w = 0 := by
    intro c w hw hwU
    have hm : ptMap π hπ σ w ∈ ptsIn p σ U := by
      rw [mem_ptsIn] at hwU ⊢
      exact hwU
    obtain ⟨c0, hc0⟩ := hch _ hm
    obtain ⟨ξ, hξ, hker⟩ := GlobalTheory.T.exists_common_kernel_hessians_pullback_smaller_chart F X Y p q σ D D' hD π hπ c0 c w hw hc0
    have hdet : ∀ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
        c.hess ((L (τ l)).pull π hπ).φ (pick ((L (τ l)).pull π hπ).φ.isLB w) w j l).det = 0 := by
      intro τ
      refine (Matrix.exists_vecMul_eq_zero_iff).1 ⟨ξ, hξ, funext fun l => ?_⟩
      have h1 := congrFun (hker (L (τ l)) (pick ((L (τ l)).pull π hπ).φ.isLB w) (mem_pick _ w)) l
      simpa [Matrix.vecMul, dotProduct] using h1
    unfold dens
    simp only [hdet, Finset.sum_const_zero, Complex.zero_re, mul_zero]
  have hc : ∀ c : AlgChart q σ D, chartMeas c.e
      (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) = 0 := by
    intro c
    set S := ptsIn q σ (π ⁻¹ᵁ U) with hSdef
    have hS : MeasurableSet S := (isOpen_ptsIn _).measurableSet
    have h1 : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) S = 0 := by
      rw [chartMeas_apply c.e _ hS]
      refine (setLIntegral_congr_fun (measurableSet_image _ (c.e.open_source.measurableSet.inter hS)
        inter_subset_left) ?_).trans lintegral_zero
      rintro _ ⟨y, hy, rfl⟩
      show ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c (c.e.symm (c.e y))) = 0
      rw [c.e.left_inv hy.1, hz c y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero]
    have hle : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) ≤
        part (fun i => (L i).pull π hπ) ε :=
      le_iSup (fun c : AlgChart q σ D => chartMeas c.e
        (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y))) c
    have h2 := (Measure.le_iff'.1 hle Sᶜ).trans_eq hnull
    refine Measure.measure_univ_eq_zero.1 (le_antisymm ?_ bot_le)
    calc _ ≤ _ := measure_mono (show univ ⊆ S ∪ Sᶜ by simp)
      _ ≤ _ := measure_union_le _ _
      _ ≤ 0 := by rw [h1, zero_add]; exact h2
  show glueMeas _ _ = 0
  unfold glueMeas
  simp only [hc]
  exact le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)

end GlobalTheory.MixDrop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasurePullbackEqZeroOfLtDimStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernMeasure_pullback_eq_zero_of_lt_dim : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D D' : ℕ), D' < D → IsProjOver p → topologicalKrullDim X = (D' : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (L : Fin D → MLine p σ) (ε : ℤˣ), part (fun i => (L i).pull π hπ) ε = 0 := by
  first | exact @GlobalTheory.MixDrop.part_pull_eq_zero | exact GlobalTheory.MixDrop.part_pull_eq_zero | (intros; apply GlobalTheory.MixDrop.part_pull_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosurePullback

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.CycPush

theorem isProjOver_comp {k : Type} [CommRing k] {X Z : Scheme.{0}} {p : X ⟶ Sp k} (hp : IsProjOver p)
    (i : Z ⟶ X) [IsClosedImmersion i] : IsProjOver (i ≫ p) := by
  obtain ⟨N, j, hj, rfl⟩ := hp
  exact ⟨N, i ≫ j, inferInstance, by rw [Category.assoc]⟩

theorem pull_congr {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (A : MLine p σ) {a b : Y ⟶ X} (hab : a = b) (ha : a ≫ p = q) (hb : b ≫ p = q) :
    A.pull a ha = A.pull b hb := by
  subst hab; rfl

theorem dim_le_of_dominant : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X), π ≫ p = q → π (genericPoint Y) = genericPoint X → ∀ n : ℕ, topologicalKrullDim Y = n → ∃ m : ℕ, m ≤ n ∧ topologicalKrullDim X = m := by
  intro F _ W M _ _ p q hp hq f hπ hη n hM
  obtain ⟨N, i, hi, hcomp⟩ := hp
  obtain ⟨N', j, hj, hcomp'⟩ := hq
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : IsProper (PSpace.str F N') := isProper_str F N'
  haveI : IsProper p := by rw [← hcomp]; infer_instance
  haveI : IsProper (f ≫ p) := by rw [hπ, ← hcomp']; infer_instance
  haveI : IsProper f := IsProper.of_comp f p
  have hf : LocallyOfFiniteType f := inferInstance
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint W)) isOpen_univ
  have hV : IsAffineOpen V := hV
  have hx : f (genericPoint M) ∈ V := hη ▸ hxV
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, hUV⟩ := M.isBasis_affineOpens.exists_subset_of_mem_open
    (show genericPoint M ∈ f ⁻¹ᵁ V from hx) (f ⁻¹ᵁ V).isOpen
  have hU : IsAffineOpen U := hU
  haveI : Nonempty V := ⟨⟨_, hx⟩⟩
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  have e : U ≤ f ⁻¹ᵁ V := hUV
  let φ := Spec.preimage (hV.fromSpec ≫ p)
  have hφ : Spec.map φ = hV.fromSpec ≫ p := Spec.map_preimage _
  letI : Algebra F Γ(W, V) := φ.hom.toAlgebra
  have hftA : Algebra.FiniteType F Γ(W, V) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := φ)).mp (hφ ▸ inferInstance)
  letI : Algebra Γ(W, V) Γ(M, U) := (f.appLE V U e).hom.toAlgebra
  have hftB : Algebra.FiniteType Γ(W, V) Γ(M, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f hf ⟨V, hV⟩ ⟨U, hU⟩ e
  letI : Algebra F Γ(M, U) := (φ ≫ f.appLE V U e).hom.toAlgebra
  haveI : IsScalarTower F Γ(W, V) Γ(M, U) := IsScalarTower.of_algebraMap_eq' rfl
  have hftC : Algebra.FiniteType F Γ(M, U) := Algebra.FiniteType.trans hftA hftB
  obtain ⟨d, h₁, h₂⟩ := exists_ringKrullDim_eq_and_trdeg_eq F Γ(W, V)
  have hd : topologicalKrullDim (V : Set W) = d := by
    rw [← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
      hV.range_fromSpec
  rw [GlobalTheory.OpenDim.topologicalKrullDim_open F p V ⟨_, hx⟩] at hd
  have hB : Algebra.trdeg F Γ(M, U) = n := GlobalTheory.GenFinite.trdeg_affineOpen_eq F (f ≫ p) hU ⟨_, hy⟩ n hM
  letI := (W.evaluation V _ hx).hom.toAlgebra
  have nat : f.appLE V U e ≫ M.evaluation U _ hy =
      W.evaluation V _ hx ≫ f.residueFieldMap (genericPoint M) := by
    rw [Scheme.evaluation_naturality f _ hx, Scheme.Hom.appLE, Category.assoc]
    congr 1
    simp only [Scheme.evaluation]
    rw [← Category.assoc, TopCat.Presheaf.germ_res]
  haveI := GenFiniteEtale.isFractionRing_eval W hV hη hx
  have hinj : Function.Injective (IsScalarTower.toAlgHom F Γ(W, V) Γ(M, U)) := by
    have h₃ : Function.Injective (f.appLE V U e ≫ M.evaluation U _ hy).hom := by
      rw [nat]
      exact (f.residueFieldMap (genericPoint M)).hom.injective.comp
        (IsFractionRing.injective Γ(W, V) (W.residueField (f (genericPoint M))))
    exact Function.Injective.of_comp (f := (M.evaluation U _ hy).hom) h₃
  have hle := trdeg_le_of_injective _ hinj
  rw [h₂, hB] at hle
  exact ⟨d, by exact_mod_cast hle, hd⟩

theorem cycInt_pull : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (e : ℕ) (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∀ w : Y, topologicalKrullDim (closure ({w} : Set Y)) = e → (topologicalKrullDim (closure ({π w} : Set X)) = e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = π.residueDegree w * cycInt L f (π w)) ∧ (topologicalKrullDim (closure ({π w} : Set X)) ≠ e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = 0) := by
  intro F _ X Y p q σ hp hq π hπ e L f hf w hw
  obtain ⟨hIw, hgw, hdw, -⟩ := GlobalTheory.ClosFacts.clos_facts Y w
  obtain ⟨hIx, hgx, hdx, hfac⟩ := GlobalTheory.ClosFacts.clos_facts X (π w)
  have hη : (closι w ≫ π) (genericPoint (clos w)) = π w := by
    rw [Scheme.Hom.comp_apply, hgw]
  obtain ⟨g, hg, hgg, hgdeg, -⟩ := hfac (clos w) (closι w ≫ π) hη
  have hpX : IsProjOver (closι (π w) ≫ p) := isProjOver_comp hp _
  have hpY : IsProjOver (closι w ≫ q) := isProjOver_comp hq _
  have hgp : g ≫ closι (π w) ≫ p = closι w ≫ q := by
    rw [← Category.assoc, hg, Category.assoc, hπ]
  have hdY : topologicalKrullDim (clos w) = e := hdw.trans hw
  let L' : Fin e → MLine (closι (π w) ≫ p) σ := fun i => (L i).pull (closι (π w)) rfl
  let f' : CxPts (closι (π w) ≫ p) σ → ℝ := fun y => f (ptMap (closι (π w)) rfl σ y)
  have hf' : Measurable f' := hf.comp (PtsOver.continuous_map _ _ _).measurable

  have h1 : (closι w ≫ π) ≫ p = closι w ≫ q := by rw [Category.assoc, hπ]
  have h2 : (g ≫ closι (π w)) ≫ p = closι w ≫ q := by rw [Category.assoc, hgp]
  have hpart : ∀ ε : ℤˣ, part (fun i => ((L i).pull π hπ).pull (closι w) rfl) ε = part (fun i => (L' i).pull g hgp) ε := by
    intro ε
    have c1 := (GlobalTheory.Mix.isom_calculus F X Y p q σ π hπ).2.2.2.2.2 (clos w) (closι w ≫ q) (closι w) rfl h1
    have c2 := (GlobalTheory.Mix.isom_calculus F X (clos (π w)) p (closι (π w) ≫ p) σ (closι (π w)) rfl).2.2.2.2.2 (clos w)
      (closι w ≫ q) g hgp h2
    have e1 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c1 (L i)) ε
    have e2 := GlobalTheory.Mix.part_eq_of_isom F (clos w) (closι w ≫ q) σ hpY e _ _ (fun i => c2 (L i)) ε
    rw [e1, e2]
    congr 1
    funext i
    exact pull_congr _ hg.symm _ _
  have hfun : (fun y => (fun y => f (ptMap π hπ σ y)) (ptMap (closι w) rfl σ y)) = fun y => f' (ptMap g hgp σ y) := by
    funext y
    show f _ = f _
    congr 1
    apply Subtype.ext
    simp only [PtsOver.map_val, Category.assoc, hg]
  have hint : cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w =
      Mix.int (fun i => (L' i).pull g hgp) (fun y => f' (ptMap g hgp σ y)) := by
    simp only [cycInt, Mix.int]
    rw [hfun, hpart 1, hpart (-1)]
  refine ⟨fun hX => ?_, fun hX => ?_⟩
  · have hdX : topologicalKrullDim (clos (π w)) = e := hdx.trans hX
    have hne := GlobalTheory.DominantProjDegree.residueDegree_ne_zero_of_map_genericPoint F (clos (π w)) (clos w)
      (closι (π w) ≫ p) (closι w ≫ q) e hpX hpY hdX hdY g hgp hgg
    have hpush := (GlobalTheory.T.mixedIntegral_pullback_genericallyFinite F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e hpX hdX hpY g hgp
      hgg hne L' f' hf').2
    have hdeg : g.residueDegree (genericPoint (clos w)) = π.residueDegree w := by
      rw [hgdeg, GlobalTheory.CurveDegreesCompare.residueDegree_comp, GlobalTheory.ProperCut.residueDegree_of_isClosedImmersion (closι w),
        mul_one, hgw]
    rw [hint, hpush, hdeg]
    rfl
  · obtain ⟨m, hm, hdX⟩ := dim_le_of_dominant F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) hpX hpY g hgp
      hgg e hdY
    have hlt : m < e := lt_of_le_of_ne hm fun h => hX (by rw [← hdx, hdX, h])
    have h0 := GlobalTheory.T.mixedChernMeasure_pullback_eq_zero_of_lt_dim F (clos (π w)) (clos w) (closι (π w) ≫ p) (closι w ≫ q) σ e m hlt hpX hdX hpY g hgp hgg L'
    rw [hint]
    simp only [Mix.int, h0, integral_zero_measure, sub_zero]

end GlobalTheory.CycPush
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosurePullbackStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernIntegral_pointClosure_pullback : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ), IsProjOver p → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (e : ℕ) (L : Fin e → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → ∀ w : Y, topologicalKrullDim (closure ({w} : Set Y)) = e → (topologicalKrullDim (closure ({π w} : Set X)) = e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = π.residueDegree w * cycInt L f (π w)) ∧ (topologicalKrullDim (closure ({π w} : Set X)) ≠ e → cycInt (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) w = 0) := by
  first | exact @GlobalTheory.CycPush.cycInt_pull | exact GlobalTheory.CycPush.cycInt_pull | (intros; apply GlobalTheory.CycPush.cycInt_pull <;> assumption)
end
end
