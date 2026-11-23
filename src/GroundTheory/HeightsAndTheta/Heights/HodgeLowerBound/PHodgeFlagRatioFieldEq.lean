module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagRatioFieldEq
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsRatioFieldSpan
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagSpan
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPivotMinorFlag
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ObjectsTied
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PGenLeadMinorNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermFubiniStudyO1
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagSpan
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Tactic.Linter.Style

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.GenMat0FrEqMap

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem genMat0Fr_eq_map (F : Type) [Field F] (Ψ : Type) (n j : ℕ) (τ : Ψ) :
    genMat0Fr F Ψ n j τ = (algebraMap (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n)).mapMatrix
      (Matrix.of fun (p q : Fin n) => if (p : ℕ) < j ∧ j ≤ (q : ℕ) then 0 else
        (X (τ, p, q) : MvPolynomial (Ψ × Fin n × Fin n) F)) := by
  ext p q
  simp only [genMat0Fr, genMatFr, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

theorem GenLeadMinor0NeZero.full : GenLeadMinor0NeZero.Statement := by
  intro F _ Ψ n j τ a
  rw [genMat0Fr_eq_map, ← leadMinor_map]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (MvPolynomial (Ψ × Fin n × Fin n) F) (GenFrac F Ψ n))).2 ?_
  intro h0
  have h1 := congrArg (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)) h0
  rw [leadMinor_map, map_zero] at h1
  have hP : (MvPolynomial.eval (fun q : Ψ × Fin n × Fin n => if q.2.1 = q.2.2 then (1 : F) else 0)).mapMatrix
      (Matrix.of fun (p q : Fin n) => if (p : ℕ) < j ∧ j ≤ (q : ℕ) then 0 else
        (X (τ, p, q) : MvPolynomial (Ψ × Fin n × Fin n) F)) = 1 := by
    ext p q
    by_cases hc : (p : ℕ) < j ∧ j ≤ (q : ℕ)
    · have hpq : p ≠ q := by
        rintro rfl
        obtain ⟨hc₁, hc₂⟩ := hc
        omega
      simp [hc, hpq]
    · simp [hc, Matrix.one_apply]
  rw [hP, leadMinor_one] at h1
  exact one_ne_zero h1

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPivotMinorFlag

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem PivotMinorFlag.full : PivotMinorFlag.Statement := by
  intro R _ n M a b hab
  exact ⟨⟨Finset.univ.image (pivotCols a b), card_image_pivotCols a b hab⟩, pivotMinor_eq_flagMinor M a b hab⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PRatioFieldSpan

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace RatioFieldSpan

variable {F M : Type} [Field F] [Field M] [Algebra F M]

theorem div_mem_adjoin {I : Type} (u : I → M) (v : M) {x : M}
    (hx : x ∈ Submodule.span F (Set.range u)) :
    x / v ∈ IntermediateField.adjoin F (Set.range fun i => u i / v) := by
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨i, rfl⟩ := h
    exact IntermediateField.subset_adjoin F _ ⟨i, rfl⟩
  | zero => simp
  | add x y _ _ hx hy =>
    rw [add_div]
    exact add_mem hx hy
  | smul a x _ hx =>
    rw [Algebra.smul_def, mul_div_assoc]
    exact mul_mem (IntermediateField.algebraMap_mem _ a) hx

theorem adjoin_le {I J : Type} (u : I → M) (w : J → M) (v v' : M)
    (hw : ∀ j, w j ∈ Submodule.span F (Set.range u)) (hv' : v' ∈ Submodule.span F (Set.range u))
    (hv : v ≠ 0) (hv'0 : v' ≠ 0) :
    IntermediateField.adjoin F (Set.range fun j => w j / v') ≤
      IntermediateField.adjoin F (Set.range fun i => u i / v) := by
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  have h1 := div_mem_adjoin (F := F) u v (hw j)
  have h2 := div_mem_adjoin (F := F) u v hv'
  have key : w j / v' = (w j / v) / (v' / v) := by
    field_simp
  show w j / v' ∈ IntermediateField.adjoin F (Set.range fun i => u i / v)
  rw [key]
  exact div_mem h1 h2

theorem full : RatioFieldSpan.Statement := by
  intro F M _ _ _ I J u w v v' hspan hv hv' hv0 hv'0
  apply le_antisymm
  · apply adjoin_le w u v' v
    · intro i
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [← hspan]; exact hv
    · exact hv'0
    · exact hv0
  · apply adjoin_le u w v v'
    · intro j
      rw [hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    · exact hv'
    · exact hv0
    · exact hv'0

end RatioFieldSpan

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
end

-- Source module: GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHodgeFlagRatioFieldEq

section

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem HodgeFlagRatioFieldEq.proof (h₁ : RatioFieldSpan.Statement) (h₂ : HodgeFlagSpan.Statement)
    (h₃ : PivotMinorFlag.Statement) (h₄ : GenLeadMinor0NeZero.Statement) : HodgeFlagRatioFieldEq.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B c hc

  have hq : ∀ (τ : Ψ) (i : Fin (D.N - 1)),
      IntermediateField.adjoin Ω (Set.range fun m =>
          Pl.pluecker0 B τ i m / Pl.pluecker0 B τ i (c (Sum.inr (τ, i)))) =
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i) := by
    intro τ i
    have hspan := h₂ II Ψ K ι Ω E D Pl H B τ i
    obtain ⟨S₀, hS₀⟩ := h₃ _ D.N (genMat0Fr Ω Ψ D.N D.j τ) i (Fin.castLE (Nat.sub_le D.N 1) i) le_rfl
    refine h₁ Ω Pl.ΩY _ _ _ _ _ _ hspan (Submodule.subset_span ⟨_, rfl⟩) ?_ (hc (Sum.inr (τ, i)))
      (h₄ Ω Ψ D.N D.j τ i)
    rw [hspan]
    exact Submodule.subset_span ⟨S₀, by rw [leadMinor, hS₀]⟩
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k | q, t⟩, rfl⟩
    · show Pl.ofΩ (D.y ⟨k, t⟩) / Pl.ofΩ (D.y ⟨k, c (Sum.inl k)⟩) ∈ _
      rw [PlueckerData.ofΩ_eq, PlueckerData.ofΩ_eq, ← map_div₀]
      exact IntermediateField.algebraMap_mem _ _
    · have hmem : Pl.pluecker0 B q.1 q.2 t / Pl.pluecker0 B q.1 q.2 (c (Sum.inr (q.1, q.2))) ∈
          IntermediateField.adjoin Ω (Set.range fun m =>
            Pl.pluecker0 B q.1 q.2 m / Pl.pluecker0 B q.1 q.2 (c (Sum.inr (q.1, q.2)))) :=
        IntermediateField.subset_adjoin _ _ ⟨t, rfl⟩
      rw [hq] at hmem
      refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
      rintro _ ⟨S, rfl⟩
      exact ⟨(q.1, ⟨q.2, S⟩), rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨τ, i, S⟩, rfl⟩
    have hmem : flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i ∈
        IntermediateField.adjoin Ω (Set.range fun S : PluckerBlocks D.N D.N i =>
          flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i S / leadMinor (genMat0Fr Ω Ψ D.N D.j τ) i) :=
      IntermediateField.subset_adjoin _ _ ⟨S, rfl⟩
    rw [← hq] at hmem
    refine IntermediateField.adjoin.mono _ _ _ ?_ hmem
    rintro _ ⟨m, rfl⟩
    exact ⟨⟨Sum.inr (τ, i), m⟩, rfl⟩

theorem HodgeFlagRatioFieldEq.full : HodgeFlagRatioFieldEq.Statement :=
  HodgeFlagRatioFieldEq.proof RatioFieldSpan.full HodgeFlagSpan.full PivotMinorFlag.full GenLeadMinor0NeZero.full

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
end
