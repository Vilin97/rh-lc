module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartUnipotentFderivContinuousOn
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
public import Formalism.LocalToGlobal.GlobalTheory.GL1.CompactFixesLattice.ExistsDenOfIsCompactAdele
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalSubBoundedInfiniteSmallFinite

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.AdeleApprox

theorem exists_compact_integral (E : Type) [Field E] [NumberField E] :
    ∃ C : Set (InfiniteAdeleRing E), IsCompact C ∧
      ∀ x : Ad E, ∃ a : E, (x - algebraMap E (Ad E) a).1 ∈ C ∧
        ∀ v, (x - algebraMap E (Ad E) a).2 v ∈ v.adicCompletionIntegers E := by
  obtain ⟨C, hC, hCy⟩ := Formalism.IndefR.Eqv.G5.adl_inf_cocompact (F := E)
  refine ⟨C, hC, fun x => ?_⟩
  obtain ⟨u, hu⟩ := Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.exists_sub_mem_intAd x.2
  obtain ⟨r, hr⟩ := hCy (x.1 - algebraMap E _ u)
  refine ⟨u + r, ?_, ?_⟩
  · show x.1 - algebraMap E (InfiniteAdeleRing E) (u + r) ∈ C
    rw [map_add (f := _), ← sub_sub]
    exact hr
  · have : x.2 - algebraMap E (Af E) (u + r) =
        (x.2 - algebraMap E _ u) - algebraMap E _ (r : E) := by rw [map_add (f := _), sub_sub]
    show ∀ v, (x.2 - algebraMap E (Af E) (u + r)) v ∈ _
    rw [this]
    exact sub_mem hu (Formalism.L2.GlobalTheoryTheory.FiltrationBoundaryCriterion.CompactFixesLatticeTheory.algebraMap_mem_intAd r)

theorem exists_rat_sub_bounded_small :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (U : Set (Af E)), U ∈ nhds (0 : Af E) →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Ad E, ∃ ξ : E, ‖pInf E (x - algebraMap E (Ad E) ξ)‖ ≤ R ∧
        pFin E (x - algebraMap E (Ad E) ξ) ∈ U := by
  intro E _ _ _ U hU
  obtain ⟨C, hC, hcov⟩ := exists_compact_integral E
  obtain ⟨N, hN, hNU⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele E U hU
  have hc : Continuous (infEq E).symm := by
    refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex
      (IsTotallyComplex.isComplex w)).continuous.comp (continuous_apply w)
  obtain ⟨B, hB⟩ := isBounded_iff_forall_norm_le.1 (hC.image hc).isBounded
  refine ⟨N * max B 0, by positivity, fun x => ?_⟩
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  obtain ⟨a, h1, h2⟩ := hcov (algebraMap E (Ad E) (N : E)⁻¹ * x)
  set k := algebraMap E (Ad E) (N : E)⁻¹ * x - algebraMap E (Ad E) a with hk
  have e : x - algebraMap E (Ad E) ((N : E) * a) = N • k := by
    rw [hk, nsmul_eq_mul, ← map_natCast (algebraMap E (Ad E)) N, mul_sub, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hN', map_one, one_mul, map_mul]
  refine ⟨(N : E) * a, ?_, ?_⟩
  · rw [e, map_nsmul]
    have hb : ‖pInf E k‖ ≤ max B 0 := (hB _ ⟨k.1, h1, rfl⟩).trans (le_max_left _ _)
    exact (norm_nsmul_le).trans (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _))
  · rw [e, map_nsmul]
    exact hNU _ h2

end GlobalTheory.AdeleApprox
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalSubBoundedInfiniteSmallFiniteStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.exists_rational_sub_bounded_infinite_small_finite : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (U : Set (Af E)), U ∈ nhds (0 : Af E) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : Ad E, ∃ ξ : E, ‖pInf E (x - algebraMap E (Ad E) ξ)‖ ≤ R ∧ pFin E (x - algebraMap E (Ad E) ξ) ∈ U := by
  first | exact @GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small | exact GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small | (intros; apply GlobalTheory.AdeleApprox.exists_rat_sub_bounded_small <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalAdelicEqRatMulBoundedRealMulLeve

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.RapCover

theorem unip_eq_rat_mul_inf_mul_fin : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ)
    (L : Set (GL (Fin a) (Af E))), L ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : BlockIx a s → Ad E,
    ∃ (ξ : BlockIx a s → E) (z : BlockIx a s → Cinf E) (k : GL (Fin a) (Af E)), k ∈ L ∧ ‖z‖ ≤ R ∧
    unip x = ratGL E a (unip ξ) * infGL E a (unip z) * finGL E a k := by
  intro E _ _ _ a s L hL
  have h0 : (unip (0 : BlockIx a s → Af E)) = 1 := by
    have h := unip_add (0 : BlockIx a s → Af E) 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hpre : (fun y : BlockIx a s → Af E => unip y) ⁻¹' L ∈ nhds (0 : BlockIx a s → Af E) := by
    apply JointCont.continuous_unip.continuousAt.preimage_mem_nhds
    rw [h0]; exact hL
  rw [nhds_pi, Filter.mem_pi] at hpre
  obtain ⟨I, -, t, ht, hsub⟩ := hpre
  have hU : (⋂ p, t p) ∈ nhds (0 : Af E) := Filter.iInter_mem.2 fun p => by simpa using ht p
  obtain ⟨R, hR, hx⟩ := GlobalTheory.T.exists_rational_sub_bounded_infinite_small_finite E (⋂ p, t p) hU
  refine ⟨R, hR, fun x => ?_⟩
  choose ξ hξ1 hξ2 using fun p => hx (x p)
  refine ⟨ξ, fun p => pInf E (x p - algebraMap E (Ad E) (ξ p)),
    unip (fun p => pFin E (x p - algebraMap E (Ad E) (ξ p))), ?_, ?_, ?_⟩
  · apply hsub
    intro p _
    exact Set.mem_iInter.1 (hξ2 p) p
  · exact (pi_norm_le_iff_of_nonneg hR).2 hξ1
  · have hsplit : x = (fun p => algebraMap E (Ad E) (ξ p)) + (fun p => x p - algebraMap E (Ad E) (ξ p)) := by
      funext p; simp
    conv_lhs => rw [hsplit, unip_add, unip_algebraMap,
      ← infGL_mul_finGL (unip (fun p => x p - algebraMap E (Ad E) (ξ p))), JointCont.map_unip, JointCont.map_unip]
    rw [mul_assoc]

end GlobalTheory.RapCover
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalAdelicEqRatMulBoundedRealMulLeveStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.unipotentRadical_adelic_eq_rat_mul_boundedReal_mul_level : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ) (L : Set (GL (Fin a) (Af E))), L ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ R : ℝ, 0 ≤ R ∧ ∀ x : BlockIx a s → Ad E, ∃ (ξ : BlockIx a s → E) (z : BlockIx a s → Cinf E) (k : GL (Fin a) (Af E)), k ∈ L ∧ ‖z‖ ≤ R ∧ unip x = ratGL E a (unip ξ) * infGL E a (unip z) * finGL E a k := by
  first | exact @GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin | exact GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin | (intros; apply GlobalTheory.RapCover.unip_eq_rat_mul_inf_mul_fin <;> assumption)
end
end
