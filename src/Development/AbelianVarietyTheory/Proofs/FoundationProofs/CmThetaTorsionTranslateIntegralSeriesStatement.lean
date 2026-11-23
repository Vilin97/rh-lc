module

public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormThetaTranslateValueAtZeroPadicPeriodicStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorSeriesInParameterRescaleOfAlgebraic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateLogNormParallelogramLawStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateSeriesEqConstMulIntegralOneSeriesStatement
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOne
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionParallelogramLawPeriodicVanish

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem GlobalTheory.torsion_parallelogram_vanish : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ (N : ℕ), 0 < N → ∀ M : ℂ → ℝ,
    (∀ t ∈ Λ, M t = 0) → (∀ t ω : ℂ, (N : ℂ) * t ∈ Λ → ω ∈ Λ → M (t + ω) = M t) →
    (∀ P Q : ℂ, (N : ℂ) * P ∈ Λ → (N : ℂ) * Q ∈ Λ → Q ∉ Λ → M (P + Q) + M (P - Q) = 2 * M P + 2 * M Q) →
    ∀ t : ℂ, (N : ℂ) * t ∈ Λ → M t = 0 := by
  intro Λ _ N hN M h0 _ hlaw t ht
  by_cases hQ : t ∈ Λ
  · exact h0 t hQ
  have key : ∀ k : ℕ, M ((k:ℂ) * t) = (k:ℝ)^2 * M t ∧
      M (((k:ℂ)+1) * t) = ((k:ℝ)+1)^2 * M t := by
    intro k
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp [h0 0 (zero_mem Λ)]
      · simp
    | succ k ih =>
      refine ⟨by push_cast; exact ih.2, ?_⟩
      have hmem : (N:ℂ) * (((k:ℂ)+1) * t) ∈ Λ := by
        have e : (N:ℂ) * (((k:ℂ)+1) * t) = (k+1 : ℕ) • ((N:ℂ) * t) := by
          rw [nsmul_eq_mul]; push_cast; ring
        rw [e]; exact AddSubgroup.nsmul_mem Λ ht _
      have h := hlaw (((k:ℂ)+1) * t) t hmem ht hQ
      have e1 : ((k:ℂ)+1) * t + t = ((k:ℂ)+1+1) * t := by ring
      have e2 : ((k:ℂ)+1) * t - t = (k:ℂ) * t := by ring
      rw [e1, e2, ih.1, ih.2] at h
      push_cast
      linear_combination h
  have h1 := (key N).1
  rw [h0 _ ht] at h1
  have hN' : (N:ℝ)^2 ≠ 0 := by positivity
  exact (mul_eq_zero.mp h1.symm).resolve_left hN'
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionParallelogramLawPeriodicVanishStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsion_parallelogramLaw_periodic_vanish : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ (N : ℕ), 0 < N → ∀ M : ℂ → ℝ,
    (∀ t ∈ Λ, M t = 0) → (∀ t ω : ℂ, (N : ℂ) * t ∈ Λ → ω ∈ Λ → M (t + ω) = M t) →
    (∀ P Q : ℂ, (N : ℂ) * P ∈ Λ → (N : ℂ) * Q ∈ Λ → Q ∉ Λ → M (P + Q) + M (P - Q) = 2 * M P + 2 * M Q) →
    ∀ t : ℂ, (N : ℂ) * t ∈ Λ → M t = 0 := by
  first | exact @GlobalTheory.torsion_parallelogram_vanish | exact GlobalTheory.torsion_parallelogram_vanish | (intros; apply GlobalTheory.torsion_parallelogram_vanish <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOneStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsionPoint_padicAbscissa_norm_le_one : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ‖GlobalTheory.EvenTheta.xAt g t‖ ≤ 1 := by
  first | exact @GlobalTheory.TorsionAbscissa.norm_xAt_le | exact GlobalTheory.TorsionAbscissa.norm_xAt_le | (intros; apply GlobalTheory.TorsionAbscissa.norm_xAt_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeries

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTransl

theorem intMv_iff {p : ℕ} [Fact p.Prime] (f : PowerSeries ℂ_[p]) : IntegralMv f ↔ GlobalTheory.EvenTheta.IntSer f := by
  constructor
  · intro h n; exact h (Finsupp.single () n)
  · intro h n
    have := h (n ())
    rwa [PowerSeries.coeff_def (s := n) rfl] at this

theorem transl_holds : ∀ D : D7, GL3Theta.transl D := by
  intro D p _ cc δ g hg t ht
  have hg' := hg
  obtain ⟨hcc, -, hδ, hΛ, -⟩ := hg'
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, -, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  rw [← hΛ] at hlat huse
  have hlat' : GlobalTheory.EvenTheta.IsLat g.abelian₂ := hlat
  have hred := GlobalTheory.T.torsionPoint_padicAbscissa_norm_le_one D p cc δ g hg
  have hun := GlobalTheory.T.thetaTranslateSeries_eq_const_mul_integral_one_series D p cc δ g hg hred
  obtain ⟨n, hn, hnp, hnt⟩ := ht.2
  have hM : logc g t = 0 := by
    refine GlobalTheory.T.torsion_parallelogramLaw_periodic_vanish g.abelian₂ hlat' n hn (logc g) (fun s hs => by simp [logc, hs]) ?_ ?_ t hnt
    · intro s ω hs hω
      by_cases h1 : s ∈ g.abelian₂
      · simp [logc, h1, add_mem h1 hω]
      · have h2 : s + ω ∉ g.abelian₂ := fun h => h1 (by simpa using sub_mem h hω)
        simp only [logc, h1, h2, if_false]
        rw [GlobalTheory.T.norm_thetaTranslateValueAtZeroPadic_periodic D p cc δ g hg s ω ⟨n, hn, hs⟩ hω]
    · intro P Q hP hQ hQ'
      exact GlobalTheory.T.thetaTranslateLogNorm_parallelogram_law D p cc δ g hg hred hun P Q ⟨n, hn, hnp, hP⟩ ⟨hQ', n, hn, hnp, hQ⟩
  have hA : GlobalTheory.EvenTheta.AlgEnt (U1 g.abelian₂ t (sgStar g.abelian₂)) := ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse t ⟨n, hn, hnt⟩⟩
  obtain ⟨hq, hc0⟩ := (GlobalTheory.SerTransport.transport p g).2.2.1 _ hA
  have hne : U1 g.abelian₂ t (sgStar g.abelian₂) 0 ≠ 0 := by
    simp only [U1, zero_add, ne_eq, mul_eq_zero, Complex.exp_ne_zero, or_false]
    exact fun h => ht.1 ((hlat'.sg_eq_zero t).1 h)
  have hcne : cval g t ≠ 0 := by
    unfold cval lamC
    rw [dite_eq_left hq]
    exact (map_ne_zero g.lam).2 fun h => hne (congrArg Subtype.val h)
  have hc1 : ‖cval g t‖ = 1 := by
    simp only [logc, ht.1, if_false] at hM
    rcases Real.log_eq_zero.1 hM with h | h | h
    · exact absurd (norm_eq_zero.1 h) hcne
    · exact h
    · linarith [norm_nonneg (cval g t)]
  obtain ⟨w, hw, -, hτ⟩ := hun t ht
  refine ⟨?_, ?_⟩
  · rw [intMv_iff]
    change GlobalTheory.EvenTheta.IntSer (tau g t)
    intro k
    rw [hτ, PowerSeries.coeff_C_mul, norm_mul, hc1, one_mul]
    exact hw k
  · rw [hc0]; exact hc1

end GlobalTheory.ThetaTransl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeriesStatement

section

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.cm_theta_torsion_translate_integral_series : ∀ D : D7, GL3Theta.transl D := by
  first | exact @GlobalTheory.ThetaTransl.transl_holds | exact GlobalTheory.ThetaTransl.transl_holds | (intros; apply GlobalTheory.ThetaTransl.transl_holds <;> assumption)
end
end
