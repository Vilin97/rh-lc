module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeMatrixCoefficientNormStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeSchurOrthogonality
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientOrthogonalityRelationStatement
import Development.WeilBound.CoreStatements.BranchingTraces.HilbertSchmidtTraces.UnitaryMatrixCoefficientDecay
public import GroundTheory.AutomorphicForms.CompactSelfAdjoint
public import GroundTheory.AutomorphicForms.HilbertSchmidtCompact
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicVectorIntertwinerDetermined

section

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

theorem lower_bound_of_cyclic_coef : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ), 0 < d → IsU σ → IsU ρ →
    ∀ (w₀ : A) (v : B) (i : A →L[ℂ] B), IsMap σ ρ i → (Submodule.span ℂ (Set.range fun x => σ x w₀)).topologicalClosure = ⊤ →
    ∀ (T : A →L[ℂ] A) (E : B →L[ℂ] B), (∀ x y, ⟪σ x w₀, T (σ y w₀)⟫_ℂ = star ⟪ρ x⁻¹ v, E (ρ y⁻¹ v)⟫_ℂ) →
    (∀ z, ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, E z⟫_ℂ).re) → ∀ a, ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re := by
  intro Γ _ _ A B _ _ _ _ _ _ σ ρ d hd hσ hρ w₀ v i hi hcyc T E hTE hE a
  obtain ⟨h1, hmul, hnorm, -⟩ := hρ
  have hρinner : ∀ (g : Γ) (x y : B), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    (LinearIsometry.mk (ρ g : B →ₗ[ℂ] B) (hnorm g)).inner_map_map x y
  have hadj : ∀ (g : Γ) (x y : B), ⟪ρ g⁻¹ x, y⟫_ℂ = ⟪x, ρ g y⟫_ℂ := by
    intro g x y
    rw [← hρinner g (ρ g⁻¹ x) y]
    congr 1
    rw [← ContinuousLinearMap.mul_apply, ← hmul, mul_inv_cancel, h1, ContinuousLinearMap.one_apply]
  have hi' : ∀ (g : Γ) (x : A), i (σ g x) = ρ g (i x) := hi
  have hTE' : ∀ x y, ⟪σ x w₀, T (σ y w₀)⟫_ℂ = starRingEnd ℂ ⟪ρ x⁻¹ v, E (ρ y⁻¹ v)⟫_ℂ :=
    fun x y => (hTE x y).trans (starRingEnd_apply _).symm
  have hclosed : IsClosed {a : A | ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re} := by
    apply isClosed_le
    · exact ((continuous_const.inner i.continuous).norm.pow 2).div_const d
    · exact Complex.continuous_re.comp (continuous_id.inner T.continuous)
  have hspan : (Submodule.span ℂ (Set.range fun x => σ x w₀) : Set A) ⊆
      {a : A | ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re} := by
    intro a ha
    rw [SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp] at ha
    obtain ⟨c, rfl⟩ := ha
    set z : B := c.sum fun y t => starRingEnd ℂ t • ρ y⁻¹ v with hz
    have h1' : ⟪v, i (c.sum fun x t => t • σ x w₀)⟫_ℂ = ⟪z, i w₀⟫_ℂ := by
      rw [hz]

      simp only [Finsupp.sum, map_sum, map_smul, inner_sum, sum_inner, inner_smul_right,
      inner_smul_left, hi', hadj, Complex.conj_conj, RCLike.conj_conj, starRingEnd_self_apply]
    have h2' : ⟪c.sum fun x t => t • σ x w₀, T (c.sum fun x t => t • σ x w₀)⟫_ℂ =
        starRingEnd ℂ ⟪z, E z⟫_ℂ := by
      rw [hz]

      simp only [Finsupp.sum, map_sum, map_smul, inner_sum, sum_inner, inner_smul_right,
      inner_smul_left, hTE', map_mul, Complex.conj_conj, RCLike.conj_conj, starRingEnd_self_apply]
    rw [Set.mem_setOf_eq, h1', h2', Complex.conj_re]
    exact hE z
  have ha : a ∈ closure (Submodule.span ℂ (Set.range fun x => σ x w₀) : Set A) := by
    rw [← Submodule.topologicalClosure_coe, hcyc]
    simp
  exact closure_minimal hspan hclosed ha

end GlobalTheory.CompanionTheory.RgHeA
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicVectorIntertwinerDeterminedStatement

section

@[expose] public section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

theorem _root_.GlobalTheory.T.cyclic_vector_intertwiner_determined : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ), 0 < d → IsU σ → IsU ρ →
    ∀ (w₀ : A) (v : B) (i : A →L[ℂ] B), IsMap σ ρ i → (Submodule.span ℂ (Set.range fun x => σ x w₀)).topologicalClosure = ⊤ →
    ∀ (T : A →L[ℂ] A) (E : B →L[ℂ] B), (∀ x y, ⟪σ x w₀, T (σ y w₀)⟫_ℂ = star ⟪ρ x⁻¹ v, E (ρ y⁻¹ v)⟫_ℂ) →
    (∀ z, ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, E z⟫_ℂ).re) → ∀ a, ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.lower_bound_of_cyclic_coef | exact GlobalTheory.CompanionTheory.RgHeA.lower_bound_of_cyclic_coef | (intros; apply GlobalTheory.CompanionTheory.RgHeA.lower_bound_of_cyclic_coef <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormalDegreeSchurOrthogonalityStatement

section

@[expose] public section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

theorem _root_.GlobalTheory.T.formal_degree_schur_lower_bound : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ) (hρ : IsU ρ), IsFd ν σ d →
    ∀ w₀ : A, ‖w₀‖ = 1 → ∀ (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (i : A →L[ℂ] B), IsIsoMap σ ρ i → ∀ z : B,
    ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc z⟫_ℂ).re := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.avg_conj_coef_ge | exact GlobalTheory.CompanionTheory.RgHeA.avg_conj_coef_ge | (intros; apply GlobalTheory.CompanionTheory.RgHeA.avg_conj_coef_ge <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntertwinerAdjoint

section

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA.TwPf

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {ρ : Γ → (A →L[ℂ] A)}

theorem inner_map_map (hU : IsU ρ) (g : Γ) (x y : A) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨_, _, hnorm, _⟩ := hU
  let L : A →ₗᵢ[ℂ] A := ⟨(ρ g : A →ₗ[ℂ] A), hnorm g⟩
  exact L.inner_map_map x y

theorem map_mul_apply (hU : IsU ρ) (g h : Γ) (x : A) : ρ (g * h) x = ρ g (ρ h x) := by
  obtain ⟨_, hmul, _, _⟩ := hU
  rw [hmul, ContinuousLinearMap.mul_apply]

theorem inner_translate (hU : IsU ρ) (a g b : Γ) (u : A) :
    ⟪ρ a u, ρ g (ρ b u)⟫_ℂ = ⟪u, ρ (a⁻¹ * g * b) u⟫_ℂ := by
  have h : ρ g (ρ b u) = ρ a (ρ (a⁻¹ * g * b) u) := by
    rw [← GlobalTheory.CompanionTheory.RgHeA.TwPf.map_mul_apply hU, ← GlobalTheory.CompanionTheory.RgHeA.TwPf.map_mul_apply hU, show a * (a⁻¹ * g * b) = g * b by group]
  rw [h, GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_map_map hU]

end Unitary

theorem coefOp_translate {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ) (hρ : IsU ρ) (w₀ : A) (v : B)
    (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) (x y : Γ) :
    ⟪σ x w₀, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm (σ y w₀)⟫_ℂ =
      star ⟪ρ x⁻¹ v, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc (ρ y⁻¹ v)⟫_ℂ := by
  rw [GlobalTheory.CompanionTheory.RgHeA.inner_coefOp, GlobalTheory.CompanionTheory.RgHeA.inner_coefOp]
  simp_rw [GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_translate hσ, GlobalTheory.CompanionTheory.RgHeA.TwPf.inner_translate hρ, inv_inv]
  have key : ∀ F : Γ → ℂ, ∫ g, F (x⁻¹ * g * y) ∂ν = ∫ g, F g ∂ν := fun F =>
    (integral_mul_left_eq_self (fun h => F (h * y)) x⁻¹).trans (integral_mul_right_eq_self F y)
  have hstar : star (∫ g, star ⟪w₀, σ g w₀⟫_ℂ * ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ ∂ν) =
      ∫ g, ⟪w₀, σ g w₀⟫_ℂ * star ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ ∂ν := by
    have h := (integral_conj (μ := ν)
      (f := fun g => star ⟪w₀, σ g w₀⟫_ℂ * ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ)).symm
    simpa [map_mul] using h
  rw [hstar, ← key (fun g => ⟪w₀, σ g w₀⟫_ℂ * star ⟪v, ρ (x * g * y⁻¹) v⟫_ℂ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [show x * (x⁻¹ * g * y) * y⁻¹ = g by group]
  exact mul_comm _ _

end GlobalTheory.CompanionTheory.RgHeA.TwPf
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatrixCoefficientIntertwinerAdjointStatement

section

@[expose] public section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

theorem _root_.GlobalTheory.T.matrix_coefficient_intertwiner_adjoint : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (hσ : IsU σ) (hρ : IsU ρ) (w₀ : A) (v : B)
    (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) (x y : Γ),
    ⟪σ x w₀, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm (σ y w₀)⟫_ℂ =
      star ⟪ρ x⁻¹ v, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc (ρ y⁻¹ v)⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.RgHeA.TwPf.coefOp_translate | exact GlobalTheory.CompanionTheory.RgHeA.TwPf.coefOp_translate | (intros; apply GlobalTheory.CompanionTheory.RgHeA.TwPf.coefOp_translate <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsEigOfLow

section

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods PositivityTheory.RgHe.A
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

theorem integrable_star' {Γ : Type} [MeasurableSpace Γ] {ν : Measure Γ} {f : Γ → ℂ} (h : Integrable f ν) :
    Integrable (fun g => star (f g)) ν :=
  h.norm.mono' (continuous_star.comp_aestronglyMeasurable h.1) (.of_forall fun g => by simp)

theorem exists_eig_of_low {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A]
    (T : A →L[ℂ] A) (hT : IsCompactOperator T) (hT' : IsSelfAdjoint T) (w₀ : A) (hw₀ : w₀ ≠ 0) (p : A) (d : ℝ) (hd : 0 < d)
    (h : ∀ a, ‖⟪p, a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re) :
    ∃ (w : A) (c : ℝ), w ≠ 0 ∧ ‖p‖ ^ 2 / (2 * d) ≤ c ∧ T w = (c : ℂ) • w := by
  obtain ⟨s, b, l, -, hTb0, hsum0, -⟩ := GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum hT hT'
  have hTb : ∀ i, T (b i) = ((l i : ℝ) : ℂ) • b i := hTb0
  have hsum : ∀ x, HasSum (fun i => (((l i : ℝ) : ℂ) * ⟪b i, x⟫_ℂ) • b i) (T x) := hsum0
  have hone : ∀ i, ⟪b i, b i⟫_ℂ = 1 := fun i => by
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]; simp
  have hli : ∀ i, 0 ≤ l i := fun i => by
    have h1 := h (b i)
    rw [hTb, inner_smul_right, hone, mul_one, Complex.ofReal_re] at h1
    exact le_trans (by positivity) h1
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ i, l i < ‖p‖ ^ 2 / (2 * d) := fun i => by
    by_contra hh
    push_neg at hh
    exact hcon _ _ (b.orthonormal.ne_zero i) hh (hTb i)
  obtain ⟨i0⟩ : Nonempty s := by
    by_contra hE
    rw [not_nonempty_iff] at hE
    exact hw₀ (inner_self_eq_zero.1 ((b.hasSum_inner_mul_inner w₀ w₀).unique hasSum_empty))
  have hC : 0 < ‖p‖ ^ 2 / (2 * d) := (hli i0).trans_lt (hlt i0)
  have key : ∀ i, ⟪p, b i⟫_ℂ * ⟪b i, p⟫_ℂ = ((‖⟪p, b i⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [← inner_conj_symm (b i) p, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have key2 : ∀ i, ((l i : ℝ) : ℂ) * ⟪b i, p⟫_ℂ * ⟪p, b i⟫_ℂ = ((l i * ‖⟪p, b i⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun i => by
    rw [mul_assoc, mul_comm ⟪b i, p⟫_ℂ, key]; push_cast; ring
  have e : (⟪p, p⟫_ℂ).re = ‖p‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) p
  have h1 : HasSum (fun i => ‖⟪p, b i⟫_ℂ‖ ^ 2) (‖p‖ ^ 2) := by
    have h0 := Complex.reCLM.hasSum (b.hasSum_inner_mul_inner p p)
    simp only [Complex.reCLM_apply, key, Complex.ofReal_re, e] at h0
    exact h0
  have h2 : HasSum (fun i => l i * ‖⟪p, b i⟫_ℂ‖ ^ 2) (⟪p, T p⟫_ℂ).re := by
    have h0 := Complex.reCLM.hasSum ((innerSL ℂ p).hasSum (hsum p))
    simp only [innerSL_apply_apply, inner_smul_right, Complex.reCLM_apply, key2, Complex.ofReal_re] at h0
    exact h0
  have h3 : (⟪p, T p⟫_ℂ).re ≤ ‖p‖ ^ 2 / (2 * d) * ‖p‖ ^ 2 :=
    hasSum_le (fun i => mul_le_mul_of_nonneg_right (hlt i).le (by positivity)) h2 (h1.mul_left (‖p‖ ^ 2 / (2 * d)))
  have h5 := h p
  have e2 : ‖⟪p, p⟫_ℂ‖ = ‖p‖ ^ 2 := by rw [inner_self_eq_norm_sq_to_K]; simp
  rw [e2] at h5
  have hP : 0 < ‖p‖ ^ 2 := by
    by_contra hh
    have : ‖p‖ ^ 2 = 0 := le_antisymm (not_lt.1 hh) (by positivity)
    rw [this] at hC
    simp at hC
  have e3 : ‖p‖ ^ 2 / (2 * d) * ‖p‖ ^ 2 = (‖p‖ ^ 2) ^ 2 / d / 2 := by field_simp
  have h6 : 0 < (‖p‖ ^ 2) ^ 2 / d := by positivity
  linarith

theorem eigA : EigA := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hd w₀ hw₀ hc0 i hi v hm0
  have hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν := integrable_star' hm0
  have hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν := integrable_star' hc0
  have hne : w₀ ≠ 0 := fun h => by simp [h] at hw₀
  have hdense : (Submodule.span ℂ (Set.range fun x => σ x w₀)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, eq_bot_iff]
    intro u hu
    refine PositivityTheory.UnitaryDecomposition.X4.eq_zero_of_orth hd hne fun g => ?_
    have hg : σ g w₀ ∈ Submodule.span ℂ (Set.range fun x => σ x w₀) := Submodule.subset_span ⟨g, rfl⟩
    exact Submodule.inner_left_of_mem_orthogonal hg hu
  have hlow := GlobalTheory.T.cyclic_vector_intertwiner_determined σ ρ d hd.1 hσ hρ w₀ v i hi.1 hdense
    (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) (coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc)
    (GlobalTheory.T.matrix_coefficient_intertwiner_adjoint ν σ ρ hσ hρ w₀ v hc hm) (GlobalTheory.T.formal_degree_schur_lower_bound ν σ ρ d hσ hρ hd w₀ hw₀ hc i hi)
  have hlow' : ∀ a, ‖⟪ContinuousLinearMap.adjoint i v, a⟫_ℂ‖ ^ 2 / d ≤
      (⟪a, coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm a⟫_ℂ).re := fun a => by
    rw [ContinuousLinearMap.adjoint_inner_left]
    exact hlow a
  obtain ⟨w, c, hw, hcb, hTw⟩ := exists_eig_of_low _ (GroundTheory.Automorphic.IsHilbertSchmidt.isCompactOperator
    (GlobalTheory.T.formal_degree_matrix_coefficient_norm ν σ ρ d hσ hρ hd v hm)) (GlobalTheory.T.matrix_coefficient_orthogonality_relation ν σ ρ hσ hρ v hm) w₀ hne _ d hd.1 hlow'
  refine ⟨w, c, hw, hcb, fun b => ⟨integrable_mul_inner hσ hm b w, ?_⟩⟩
  rw [← inner_coefOp ν σ hσ _ hm, hTw, inner_smul_right]

end GlobalTheory.CompanionTheory.RgHeA
end
end
end
