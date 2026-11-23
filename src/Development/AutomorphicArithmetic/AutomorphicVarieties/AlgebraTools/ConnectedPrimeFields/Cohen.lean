module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.PsBase
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.InjOfFinite

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.DvrBase

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.dvrBase :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O], IsBase O := by
  intro O _ _ _ _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  haveI : Nontrivial (QuotSMulTop ϖ O) := by
    open Pointwise in
    refine Submodule.Quotient.nontrivial_iff.mpr ?_
    intro h
    have h1 : (1 : O) ∈ ϖ • (⊤ : Submodule O O) := by rw [h]; exact Submodule.mem_top
    obtain ⟨x, -, hx⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact hϖ.not_isUnit (IsUnit.of_mul_eq_one x (by simpa [smul_eq_mul] using hx))
  refine ⟨inferInstance, inferInstance, ⟨inferInstance, 1, ?_, [ϖ], rfl, ?_, ?_⟩, inferInstance⟩
  · rw [IsDiscreteValuationRing.ringKrullDim_eq_one]; rfl
  · intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  · rw [RingTheory.Sequence.isRegular_cons_iff]
    refine ⟨fun a b hab => mul_left_cancel₀ hϖ.ne_zero (by simpa [smul_eq_mul] using hab), ?_⟩
    exact RingTheory.Sequence.IsRegular.nil _ _
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Cohen

section

@[expose] public section

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.cohen :
    ∀ {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
      [CommRing R] [IsLocalRing R] [Algebra O R], UpperTheory.V.CA.IsCL O R → CohenType R := by
  intro O R _ _ _ _ _ _ _ h p hp
  haveI : IsDomain (R ⧸ p) := Ideal.Quotient.isDomain p
  haveI : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hS : UpperTheory.V.CA.IsCL O (R ⧸ p) :=
    UpperTheory.V.CA.cl_quot O R (R ⧸ p) (Ideal.Quotient.mkₐ O p) (Ideal.Quotient.mkₐ_surjective O p) h
  obtain ⟨h1, h2⟩ := UpperTheory.V.CA.cl_nn O (R ⧸ p) hS
  by_cases hi : Function.Injective (algebraMap O (R ⧸ p))
  · obtain ⟨d, φ, hφ, hf, -, -⟩ := h1 hi
    exact ⟨MvPowerSeries (Fin d) O, inferInstance, inferInstance, φ.toRingHom,
      psBase O (dvrBase O) d, hφ, hf⟩
  · obtain ⟨d, φ, hφ, hf, -, -⟩ := h2 hi
    exact ⟨MvPowerSeries (Fin d) (ResidueField O), inferInstance, inferInstance, φ.toRingHom,
      psBase (ResidueField O) (isBase_field _) d, hφ, hf⟩
end
end
