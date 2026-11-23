module

public import Formalism.PeriodIntegrals.LengthPoleInLift
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFromAlt
public import Formalism.PeriodIntegrals.BallQuotLen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BallQuotientLength.LengthBallQuotientEqSumMulFdeg
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
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FiltLenF
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SumAntidiagonalTuple
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.GradedCoef
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Closed
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.FiltOk
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.LiftMul
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FinitePtsOfCurve
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.RestrictedDerivativeLinear
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.AssembleAlt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BaseLengthBound.TaylorRep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Vanish

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BallQuotLen

section

@[expose] public section

theorem ball_quotient_length : PI.BallQuotLen := PI.UnitaryGroupMassFormula.BallQuotLen.ballQuotLen_main
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.BallQuot

section

@[expose] public section

noncomputable section

namespace PI.PoleLengthCount

theorem pole_ballQuot : BallQuot := ball_quotient_length

end PI.PoleLengthCount
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.AALeAAp

section

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem AA_le_AAp' (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (T : ℕ)
    (m : PtsG G la → ℕ) : Q.AA T ≤ Q.AAp T m := by
  refine Submodule.span_mono (Set.image_mono ?_)
  rintro x ⟨hx, hb⟩
  refine ⟨hx, fun β hβ ζ => le_trans (WithTop.coe_le_coe.2 ?_) (hb β hβ ζ)⟩
  dsimp only
  omega

theorem bound (hF : FiltStep) (hM : MonCount) (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO))
    (Q : LocalPointData G la) (T : ℕ) (m : PtsG G la → ℕ)
    (h1 : FiltOk G la T) (h2 : GradedCoef G la Q T m) (h3 : PiBallLen G la Q m) :
    Module.length (Op X la G.N) (↥(Q.AAp T m) ⧸ (Q.AA T).comap (Q.AAp T m).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ᶠ ζ, m ζ * fdeg ζ : ℕ) : ℕ∞) := by
  obtain ⟨ψ, hker, hP, hQ⟩ := h2
  refine (hF (Op X la G.N) (WK X la G.w wF (a0 D j T)) (Fk G la T) (a0 D j T) h1.1 h1.2.1 h1.2.2
    (fun k => Vk G la k) ψ hker (Q.AAp T m) (Q.AA T) (fun k => Pk G la Q m k) (fun k => Qk G la Q k)
    (AA_le_AAp' G la Q T m) hP hQ).trans ?_
  refine (Finset.sum_le_sum (fun k _ => (h3 k).le)).trans ?_
  rw [← Nat.cast_sum, Nat.cast_le, ← Finset.sum_mul]
  refine Nat.mul_le_mul_right _ ?_
  by_cases hT : WeightFamilies.dimY D j < T
  · rw [show a0 D j T = T - WeightFamilies.dimY D j from rfl, hM _ _ hT]
  · rw [show a0 D j T = 0 from by simp only [a0]; omega]
    simp

theorem target (hF : FiltStep) (hM : MonCount) (hS : Steps) : PI.LengthPoleInLift := by
  intro D B P j X ka wL wF G la Q S CRm T e c hOk hw hL
  obtain ⟨h1, h2, h3⟩ := hS G la Q S CRm T e c hOk hw hL
  exact bound hF hM G la Q T _ h1 h2 h3

end PI.PoleLengthCount
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiBallFrom

section

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

theorem ball_product_length : PiBallFrom := by
  intro hPi hBQ D B P j X ka wL wF G la Q S CRm T e c hOk k

  have hC : Q.InCurve := hOk.2.1
  haveI : FiniteDimensional (Kp X la G.N) (OsK X la G.w) := hC.1
  haveI : IsReduced (OsK X la G.w) := hC.2.1
  haveI : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC
  have hU := isUnif_of_curve Q hC

  have hle : ballO (unifO X la G.N) Q.e Q.c ≤
      ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ)) := by
    intro v hv
    exact ball_mono hU hC.2.2 (fun ζ => by dsimp only; omega) hv

  have h1 := hPi (Op X la G.N) (SectionSheafQuotient X la G.w wF) (Mon (WeightFamilies.dimY D j) k)
    (ballO (unifO X la G.N) Q.e (fun ζ => Q.c ζ + ((Q.mm S T e ζ : ℕ) : ℤ)))
    (ballO (unifO X la G.N) Q.e Q.c) hle
  have h2 := hBQ (Op X la G.N) (Kp X la G.N) (OsK X la G.w) (unifO X la G.N)
    (unifO_irreducible X la G.N) (finite_As_of_curve Q hC) (SectionSheafQuotient X la G.w wF) Q.e hC.2.2 Q.c (Q.mm S T e)
  refine h1.trans ?_
  rw [h2, Fintype.card_coe, Nat.cast_mul]

end PI.PoleLengthCount
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PiLenHolds

section

@[expose] public section

noncomputable section

namespace PI.PoleLengthCount

open Module

theorem piLen_holds : PiLen := by
  intro R M ι _ _ _ _ P Q _
  classical
  set PP := Submodule.pi Set.univ fun _ : ι => P
  set QQ := Submodule.pi Set.univ fun _ : ι => Q
  let q : Submodule R ↥P := Q.comap P.subtype
  let g : ι → (↥PP →ₗ[R] ↥P) := fun i =>
    ((LinearMap.proj i).comp PP.subtype).codRestrict P (fun x => x.2 i (Set.mem_univ i))
  let f : ↥PP →ₗ[R] (ι → ↥P ⧸ q) := LinearMap.pi fun i => q.mkQ.comp (g i)
  have hker : QQ.comap PP.subtype = LinearMap.ker f := by
    ext x
    simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, f, QQ,
      Submodule.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h
      funext i
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero]
      exact h i
    · intro h i
      have := congrFun h i
      simp only [LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
        Submodule.Quotient.mk_eq_zero] at this
      exact this
  have hsurj : Function.Surjective f := by
    intro y
    choose p hp using fun i => Submodule.Quotient.mk_surjective q (y i)
    refine ⟨⟨fun i => (p i : M), fun i _ => (p i).2⟩, ?_⟩
    funext i
    simp only [f, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [← hp i]
    rfl
  have e1 := (Submodule.quotEquivOfEq _ _ hker).trans (LinearMap.quotKerEquivOfSurjective f hsurj)
  rw [e1.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card]

end PI.PoleLengthCount
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.Taylor

section

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem taylor_holds (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) : Taylor G la := by
  intro k x hx
  obtain ⟨cf, hcf⟩ := PoleLengthBounds.pow_smul_top_le_monSpan (M := ↥(HK X la G.w wF))
    (fun i : Fin (WeightFamilies.dimY D j) => sfr X la G.w i.succ) k hx
  refine ⟨fun α => cf α.1, 0, Submodule.zero_mem _, ?_⟩
  rw [add_zero, hcf]
  exact (Finset.sum_coe_sort (Finset.Nat.antidiagonalTuple (WeightFamilies.dimY D j) k)
    (fun α => (∏ i, sfr X la G.w i.succ ^ α i) • cf α)).symm

end PI.PoleLengthCount
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.StepsOf

section

@[expose] public section

noncomputable section

open Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace PI.PoleLengthCount

theorem steps_of (hBQ : BallQuot) : Steps := by
  intro D B P j X ka wL wF G la Q S CRm T e c hOk hw hL
  have h3 := unit_columns_holds G la Q S CRm T c hOk hw
  exact ⟨image_filtration_decreasing G la T,
    pole_length_assemble G la Q S CRm T e c hOk hw hL (hasse_preserves_kernel G la) (vanishingOnQuadric G la) h3 (taylor_holds G la)
      (column_derivative G la) (restricted_derivative_linear G la) (liftMul_of Q T hOk.2.1 h3),
    ball_product_length piLen_holds hBQ G la Q S CRm T e c hOk⟩

theorem pole_length_bound_of_balls (hBQ : BallQuot) : PI.LengthPoleInLift := target filtration_length_bound sum_antidiagonalTuple (steps_of hBQ)

end PI.PoleLengthCount
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PoleLengthBound.PoleLengthBound

section

@[expose] public section

namespace PI.PoleLengthCount

theorem pole_length_bound : PI.LengthPoleInLift := pole_length_bound_of_balls pole_ballQuot

end PI.PoleLengthCount
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.LengthPoleInLift

section

@[expose] public section

theorem length_pole_t0 : PI.LengthPoleInLift := PI.PoleLengthCount.pole_length_bound
end
end
