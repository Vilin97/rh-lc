module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterCommutesLieAction
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneParameterSubgroupExists
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianLiePreservesStable

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.Dblock

theorem lie_skew_mem_of_cpt_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (F : Submodule ℂ (Sm E a)), FiniteDimensional ℂ F → (∀ k, ∀ φ ∈ F, cptRep E a k φ ∈ F) →
    ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ φ ∈ F, lie E a X φ ∈ F := by
  intro E _ _ _ a F hf hK X hX φ hφ
  obtain ⟨c, -, h0, -, hc, hu⟩ := GlobalTheory.CompanionTheory.LieCurve.exists_curve E a X
  let W' : Submodule ℂ (GA E a → ℂ) := F.map (Sm E a).subtype
  have hfin : FiniteDimensional ℂ W' := by
    have := hf
    exact inferInstance
  have hcl : IsClosed (W' : Set (GA E a → ℂ)) := W'.closed_of_finiteDimensional
  let G : ℝ → GA E a → ℂ := fun t g => φ.1 (g * infGL E a (c t))
  have hG : ∀ t, G t ∈ W' := fun t =>
    ⟨cptRep E a ⟨(c t).val, hu hX t⟩ φ, hK _ _ hφ, funext fun g => by
      have : Unitary.toUnits (⟨(c t).val, hu hX t⟩ : Kinf E a) = c t := Units.ext rfl
      change φ.1 (g * infGL E a (Unitary.toUnits _)) = _
      rw [this]⟩
  have hd : Filter.Tendsto (slope G 0) (nhdsWithin 0 {0}ᶜ) (nhds (lieD X φ.1)) :=
    tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_curve φ g c X h0 hc)
  have hm : lieD X φ.1 ∈ W' := hcl.mem_of_tendsto hd (Filter.Eventually.of_forall fun t =>
    W'.smul_of_tower_mem _ (W'.sub_mem (hG t) (hG 0)))
  obtain ⟨w, hw, e⟩ := hm
  rwa [show lie E a X φ = w from Subtype.ext e.symm]

end GlobalTheory.CompanionTheory.Dblock
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SkewHermitianLiePreservesStableStatement

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.skew_hermitian_lie_preserves_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (F : Submodule ℂ (Sm E a)), FiniteDimensional ℂ F → (∀ k, ∀ φ ∈ F, cptRep E a k φ ∈ F) → ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ φ ∈ F, lie E a X φ ∈ F := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable | exact GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable | (intros; apply GlobalTheory.CompanionTheory.Dblock.lie_skew_mem_of_cpt_stable <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimStableSubspace

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.IrredMod

theorem exists_finiteDimensional_zalg_lie_stable : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (W : Submodule ℂ (Sm E a)), _root_.GlobalTheory.CuspRep.IsStable W → (∀ φ ∈ W, IsAutForm φ) → ∀ φ ∈ W, ∃ Y : Submodule ℂ (Sm E a),
      FiniteDimensional ℂ Y ∧ Y ≤ W ∧ φ ∈ Y ∧ (∀ z ∈ Zalg E a, ∀ y ∈ Y, z y ∈ Y) ∧
      ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ y ∈ Y, lie E a X y ∈ Y := by
  intro E _ _ _ a W hW hA φ hφ

  let S₀ : Submodule ℂ (Sm E a) := Submodule.span ℂ (Set.range fun k => cptRep E a k φ)
  have hS₀fd : FiniteDimensional ℂ S₀ := (hA φ hφ).kfin
  have hS₀W : S₀ ≤ W := Submodule.span_le.2 (by
    rintro _ ⟨k, rfl⟩
    exact hW (.cpt k) φ hφ)
  have hS₀K : ∀ k, ∀ ψ ∈ S₀, cptRep E a k ψ ∈ S₀ := by
    intro k ψ hψ
    have hle : S₀ ≤ S₀.comap (cptRep E a k) := Submodule.span_le.2 (by
      rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      simp only [map_mul, Module.End.mul_apply])
    exact hle hψ
  have hS₀L : ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ ψ ∈ S₀, lie E a X ψ ∈ S₀ :=
    fun X hX ψ hψ => GlobalTheory.T.skew_hermitian_lie_preserves_stable E a S₀ hS₀fd hS₀K X hX ψ hψ
  have hφS₀ : φ ∈ S₀ := Submodule.subset_span ⟨1, by simp⟩

  let Y : Submodule ℂ (Sm E a) := Submodule.span ℂ
    (Set.image2 (fun (z : Module.End ℂ (Sm E a)) (s : Sm E a) => z s) (Zalg E a : Set (Module.End ℂ (Sm E a))) S₀)
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional S₀).2 hS₀fd
  let Zs : Sm E a → Submodule ℂ (Sm E a) := fun s =>
    Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z s) '' Zalg E a)
  have hts : ∀ s ∈ t, s ∈ S₀ := fun s hs => ht ▸ Submodule.subset_span hs
  have hZfd : ∀ s : t, FiniteDimensional ℂ (Zs s.1) := fun s => (hA s.1 (hS₀W (hts s.1 s.2))).zfin
  let T : Submodule ℂ (Sm E a) := ⨆ s : t, Zs s.1
  have hTfd : FiniteDimensional ℂ T := Submodule.finiteDimensional_iSup _
  have hYT : Y ≤ T := Submodule.span_le.2 (by
    rintro _ ⟨z, hz, s, hs, rfl⟩
    have hle : S₀ ≤ T.comap z := by
      rw [← ht]
      refine Submodule.span_le.2 fun u hu => ?_
      exact Submodule.mem_iSup_of_mem (⟨u, hu⟩ : t) (Submodule.subset_span ⟨z, hz, rfl⟩)
    exact hle hs)
  have hWlie : ∀ X, ∀ ψ ∈ W, lie E a X ψ ∈ W := fun X ψ hψ => hW (.lie X) ψ hψ
  refine ⟨Y, Submodule.finiteDimensional_of_le hYT, Submodule.span_le.2 ?_, Submodule.subset_span
    ⟨1, (Zalg E a).one_mem, φ, hφS₀, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, s, hs, rfl⟩
    exact Zalg_stable hWlie hz s (hS₀W hs)
  · intro z hz y hy
    have hle : Y ≤ Y.comap z := Submodule.span_le.2 (by
      rintro _ ⟨z', hz', s, hs, rfl⟩
      exact Submodule.subset_span ⟨z * z', (Zalg E a).mul_mem hz hz', s, hs, rfl⟩)
    exact hle hy
  · intro X hX y hy
    have hle : Y ≤ Y.comap (lie E a X) := Submodule.span_le.2 (by
      rintro _ ⟨z, hz, s, hs, rfl⟩
      have e : lie E a X (z s) = z (lie E a X s) :=
        (LinearMap.congr_fun (GlobalTheory.CompanionTheory.ZalgCentral.Zalg_mul_lie E a z hz X) s).symm
      change lie E a X (z s) ∈ Y
      rw [e]
      exact Submodule.subset_span ⟨z, hz, _, hS₀L X hX s hs, rfl⟩)
    exact hle hy

end GlobalTheory.CompanionTheory.IrredMod
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimStableSubspaceStatement

section

@[expose] public section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.finite_dim_stable_subspace : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (W : Submodule ℂ (Sm E a)), _root_.GlobalTheory.CuspRep.IsStable W → (∀ φ ∈ W, IsAutForm φ) → ∀ φ ∈ W, ∃ Y : Submodule ℂ (Sm E a), FiniteDimensional ℂ Y ∧ Y ≤ W ∧ φ ∈ Y ∧ (∀ z ∈ Zalg E a, ∀ y ∈ Y, z y ∈ Y) ∧ ∀ X : GlobalTheory.CuspRep.Lie E a, (Matrix.of X)ᴴ = -(Matrix.of X) → ∀ y ∈ Y, lie E a X y ∈ Y := by
  first | exact @GlobalTheory.CompanionTheory.IrredMod.exists_finiteDimensional_zalg_lie_stable | exact GlobalTheory.CompanionTheory.IrredMod.exists_finiteDimensional_zalg_lie_stable | (intros; apply GlobalTheory.CompanionTheory.IrredMod.exists_finiteDimensional_zalg_lie_stable <;> assumption)
end
end
