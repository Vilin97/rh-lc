module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactModLatticeStabiliserOfLeFirstMinimumStatement
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsCompactOrthBounded
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OrthonormalFramesBoundedOfDefinite
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
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DetNeZeroOfIsOrth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverOfDriftFunction
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsStabiliserImageSubgroup
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIntMulIntegral
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LiftFactorization
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Topology.Algebra.Group.Units
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousOnRmul
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsContinuousGramSchmidt
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfFiniteCovolume
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MuFLtTopOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.UpperTriangularPreservesDiagonalIff

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactSpaceRealUnitaryGroupOfDefinite

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FinCovol

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem compactSpace_unitary_of_definite :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)),
      (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) →
      (X.p0 = 0 ∨ X.p0 = r) → CompactSpace H) := by
  intro r X H hH hp
  obtain ⟨R, hR⟩ := GlobalTheory.orthonormal_frames_bounded_of_definite r X hp
  have hx0 : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  obtain ⟨-, -, h⟩ := GlobalTheory.UnitaryFrames.unitary_group_frames.2 r X H hH
  obtain ⟨horth, ι, hc, -, hι⟩ := h (x0F X) hx0
  have hK := (isCompact_orth_bounded r X R).image_of_continuousOn
    (hc.mono fun x hx => hx.1)
  refine ⟨hK.of_isClosed_subset isClosed_univ fun g _ => ?_⟩
  exact ⟨_, ⟨horth g, hR _ (horth g)⟩, hι g⟩

end GlobalTheory.FinCovol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CompactSpaceRealUnitaryGroupOfDefiniteStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.compactSpace_realUnitaryGroup_of_definite : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → (X.p0 = 0 ∨ X.p0 = r) → CompactSpace H) := by
  first | exact @GlobalTheory.FinCovol.compactSpace_unitary_of_definite | exact GlobalTheory.FinCovol.compactSpace_unitary_of_definite | (intros; apply GlobalTheory.FinCovol.compactSpace_unitary_of_definite <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsDriftFunctionRealUnitaryGroupStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_drift_function_realUnitaryGroup : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H], 0 < X.p0 → X.p0 < r → ∀ x0, IsOrth X x0 → ∃ (σ : Type) (_ : Fintype σ) (_ : Nonempty σ) (h : σ → H) (f : H → ℝ) (c b : ℝ), (∀ s, ∃ k : H, k * h s = (h s)⁻¹ * k) ∧ Measurable f ∧ (∀ g, 0 ≤ f g) ∧ (∀ u : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((u : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → ∀ g, f (u * g) = f g) ∧ 0 ≤ c ∧ c < 1 ∧ 0 ≤ b ∧ (∀ g, ∑ s, f (g * h s) ≤ Fintype.card σ * (c * f g + b)) ∧ ∀ M : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ g : H, f g ≤ M → ε ≤ X.la1 (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0)) := by
  first | exact @GlobalTheory.DriftUnitary.exists_drift_function | exact GlobalTheory.DriftUnitary.exists_drift_function | (intros; apply GlobalTheory.DriftUnitary.exists_drift_function <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.GamDisc

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.GamDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gamDisc : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∃ U ∈ 𝓝 (1 : H), ∀ g : H, (∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∀ τ : X.Ψ, ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1) → g ∈ U → g = 1) := by
  intro r X H _
  have hS := GlobalTheory.LatFin.latFin.2 r X 2
  set S := {γ : GL (Fin r) E | IsUStab X.Gm X.Λ γ ∧ ∀ (τ : X.Ψ) (a b : Fin r),
    ‖τ.1 ((γ : Matrix (Fin r) (Fin r) E) a b)‖ ≤ 2} with hSdef
  let F : GL (Fin r) E → Set H := fun γ => {g : H | ∀ τ : X.Ψ,
    ((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
      (γ : Matrix (Fin r) (Fin r) E).map τ.1}
  have hF : ∀ γ, (F γ).Finite := by
    intro γ
    refine Set.Subsingleton.finite ?_
    intro g hg g' hg'
    refine Subtype.ext (funext fun τ => Units.ext ?_)
    exact (hg τ).trans (hg' τ).symm
  have hT : (⋃ γ ∈ S, F γ).Finite := hS.biUnion fun γ _ => hF γ
  have hC : ((⋃ γ ∈ S, F γ) \ {1})ᶜ ∈ 𝓝 (1 : H) :=
    (hT.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
  have hV : ∀ᶠ g : H in 𝓝 1, ∀ (τ : X.Ψ) (a b : Fin r),
      ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ < 2 := by
    simp only [Filter.eventually_all]
    intro τ a b
    have hc : Continuous fun g : H =>
        ‖((((g : H) : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) a b‖ :=
      ((Units.continuous_val.comp
        ((continuous_apply τ).comp continuous_subtype_val)).matrix_elem a b).norm
    refine hc.continuousAt.eventually_lt continuousAt_const ?_
    by_cases h : a = b <;> simp [Matrix.one_apply, h]
  refine ⟨_, Filter.inter_mem hC hV, ?_⟩
  rintro g ⟨γ, hγ, hg⟩ ⟨h1, h2⟩
  by_contra hne
  refine h1 ⟨Set.mem_biUnion (x := γ) ⟨hγ, fun τ a b => ?_⟩ hg, hne⟩
  have := h2 τ a b
  rw [hg τ] at this
  exact this.le

end GlobalTheory.GamDisc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverUnitaryLattice

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.FiniteCovolume

theorem exists_finite_measure_cover : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  intro r X H hH _ _ ν _
  obtain ⟨Γ, hΓ⟩ := GlobalTheory.FiniteCovolume.exists_stabiliser_image_subgroup r X H hH
  suffices hS : ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ ∈ Γ, ∃ w ∈ Ω, g = γ * w by
    obtain ⟨Ω, h1, h2, h3⟩ := hS
    refine ⟨Ω, h1, h2, fun g => ?_⟩
    obtain ⟨u, hu, w, hw, rfl⟩ := h3 g
    obtain ⟨γ, hγ, hγu⟩ := (hΓ u).1 hu
    refine ⟨γ, hγ, w, hw, fun τ => ?_⟩
    rw [← hγu τ]
    simp
  by_cases hp : X.p0 = 0 ∨ X.p0 = r
  · haveI : CompactSpace H := GlobalTheory.T.compactSpace_realUnitaryGroup_of_definite r X H hH hp
    exact ⟨Set.univ, MeasurableSet.univ, isCompact_univ.measure_lt_top,
      fun g => ⟨1, Γ.one_mem, g, Set.mem_univ _, (one_mul g).symm⟩⟩
  · have hp0 : 0 < X.p0 := Nat.pos_of_ne_zero fun h => hp (Or.inl h)
    have hpr : X.p0 < r := lt_of_le_of_ne X.p0_le fun h => hp (Or.inr h)
    obtain ⟨hlc, hsc, -⟩ := (GlobalTheory.UnitaryFrames.unitary_group_frames (E := E)).2 r X H hH
    have hx0 : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
    obtain ⟨σ, _, _, h, f, c, b, hk, hf, hf0, hinv, hc0, hc1, hb, hdrift, hsub⟩ :=
      GlobalTheory.T.exists_drift_function_realUnitaryGroup r X H hH hp0 hpr (x0F X) hx0
    obtain ⟨U, hU, hU1⟩ := GlobalTheory.GamDisc.gamDisc r X H hH
    refine GlobalTheory.exists_finite_measure_cover_of_drift_function H ν Γ σ h f c b
      ⟨U, hU, fun γ hγ => hU1 γ ((hΓ γ).1 hγ)⟩ hk hf hf0
      (fun γ hγ => hinv γ ((hΓ γ).1 hγ)) hc0 hc1 hb hdrift fun M => ?_
    obtain ⟨ε, hε, hM⟩ := hsub M
    obtain ⟨K, hK, hKc⟩ := GlobalTheory.T.compact_mod_latticeStabiliser_of_le_firstMinimum r X H hH (x0F X) hx0 ε hε
    refine ⟨K, hK, fun g hg => ?_⟩
    obtain ⟨u, hu, k, hk, e⟩ := hKc g (hM g hg)
    exact ⟨u, (hΓ u).2 hu, k, hk, e⟩

end GlobalTheory.FiniteCovolume
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsFiniteMeasureCoverUnitaryLatticeStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.exists_finite_measure_cover_unitary_lattice : (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
  first | exact @GlobalTheory.FiniteCovolume.exists_finite_measure_cover | exact GlobalTheory.FiniteCovolume.exists_finite_measure_cover | (intros; apply GlobalTheory.FiniteCovolume.exists_finite_measure_cover <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuOfCovolume

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.ClosedFiniteMeasure

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finMu_of_covolume :
    (∀ (r : ℕ) (X : Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsHaarMeasure], ∃ Ω : Set H, MeasurableSet Ω ∧ ν Ω < ⊤ ∧ ∀ g : H, ∃ γ : GL (Fin r) E, IsUStab X.Gm X.Λ γ ∧ ∃ w ∈ Ω, ∀ τ : X.Ψ, (((g : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * (((w : X.Ψ → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) → (∀ (r : ℕ) (X : Data E r), FinMu X) := by
  intro hcov
  exact GlobalTheory.FiniteCovolume.finMu_of_finite_covolume hcov GlobalTheory.UnitaryFrames.unitary_group_frames
    (GlobalTheory.UnitaryInvMeasure.invMeas GlobalTheory.FrameMeasureClosed.measInv_holds
      GlobalTheory.GramSchmidtCont.exists_continuous_gramSchmidt GlobalTheory.isOrth_rmul_iff_unitary_diagonal
      (GlobalTheory.SatFin.muF_sat_lt_top GlobalTheory.FrameMeasureClosed.measInv_holds)
      GlobalTheory.UnitaryFrames.unitary_group_frames.2)
    GlobalTheory.ClosedDiscontinuity.propDisc_closed

end GlobalTheory.ClosedFiniteMeasure
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FinMuUnconditional

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.DriftCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finMu_unconditional : ∀ (r : ℕ) (X : Data E r), FinMu X :=
  GlobalTheory.ClosedFiniteMeasure.finMu_of_covolume GlobalTheory.T.exists_finite_measure_cover_unitary_lattice

end GlobalTheory.DriftCovolume
end
end
