module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsContractNeZero
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.BridgesMore
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.PublishedTheoremStatements.ProvedMore
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.GrothendieckRingPolynomialOfSeg
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
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
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsListPairwiseNotRel
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ProbeL
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.MultiProdCompInvTranspose
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.EssSquareIntegrableSegmentsHolds

section

section

namespace PositivityTheory.Groth

theorem grothendieckRingPolynomial_holds : GlobalTheory.Published.GrothendieckRingPolynomial :=
  grothendieckRingPolynomial_of_seg PositivityTheory.RgGu.segmentRepresentation

end PositivityTheory.Groth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideRest

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.LocGL.LExist

theorem main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
    GlobalTheory.Published.StandardCosocleGL → (∀ Δ : Segment k, ∃ x : IrrGL (k := k), IsLSeg Δ x.rep) →
      ∀ 𝔪 : Multiset (Segment k), ∃ x : IrrGL (k := k), IsL 𝔪 x.rep := by
  intro k _ _ _ _ _ hS hL 𝔪
  obtain ⟨Δ, hΔ⟩ := ((precedes_and_orderedForms k).1.2.2) 𝔪
  choose y hy using hL
  let x : Fin 𝔪.card → IrrGL (k := k) := fun i => y (Δ i)
  have hx : LFactors 𝔪 x := ⟨Δ, hΔ, fun i => hy (Δ i)⟩
  obtain ⟨π, hπ⟩ := hS k 𝔪 𝔪.card _ x rfl hx
  refine ⟨IrrGL.of π.ρ π.smooth π.irr, 𝔪.card, x, rfl, hx, ?_⟩
  exact hπ.of_equiv (IrrGL.equivOf π.ρ π.smooth π.irr) (.refl _)

end GlobalTheory.LocGL.LExist
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExistsClassIsLSeg

section

@[expose] public section


open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL in
theorem PositivityTheory.Exh.exists_class_isLSeg (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (Δ : Segment k) : ∃ x : IrrGL (k := k), IsLSeg Δ x.rep := by
  obtain ⟨π, hd, hc⟩ := PositivityTheory.Exh.lSegExists k Δ
  refine ⟨⟨Δ.deg, Quotient.mk (IrrRep.setoid _) π⟩, ?_⟩
  obtain ⟨e⟩ : Nonempty ((Quotient.mk (IrrRep.setoid _) π).out.ρ.Equiv π.ρ) :=
    Quotient.mk_out (s := IrrRep.setoid _) π
  exact ⟨hd, IsCosocle.of_equiv hc e.symm (Representation.Equiv.refl _)⟩
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.LocalLanglandsExistence.LanglandsDataDualGLOfCosocle

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands

namespace PositivityTheory.Pf1.LocalLanglands.LDual

theorem lExists_of_cosocle (hS : GlobalTheory.Published.StandardCosocleGL) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      ∀ 𝔪 : Multiset (Segment k), ∃ x : IrrGL (k := k), IsL 𝔪 x.rep :=
  fun k _ _ _ _ _ => GlobalTheory.LocGL.LExist.main k hS (PositivityTheory.Exh.exists_class_isLSeg k)

theorem langlandsDataDualGL_of_clauses (hS : GlobalTheory.Published.StandardCosocleGL)
    (hD : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
      (l : List (Segment k)) (x y : IrrGL (k := k)), IsL (l : Multiset (Segment k)) x.rep → DualCl x y →
        ∃ l' : List (Segment k), List.Forall₂ SegDual l l' ∧ IsL (l' : Multiset (Segment k)) y.rep) :
    GlobalTheory.Published.LanglandsDataDualGL :=
  fun k _ _ _ _ _ => ⟨lExists_of_cosocle hS k, hD k⟩

theorem langlandsDataDualGL_of_cosocle (hS : GlobalTheory.Published.StandardCosocleGL) : GlobalTheory.Published.LanglandsDataDualGL :=
  langlandsDataDualGL_of_clauses hS PositivityTheory.Pf1.LDual2.langlandsDataDualGL_dual

end PositivityTheory.Pf1.LocalLanglands.LDual
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi

section

@[expose] public section

namespace UpperTheory.Zero.LLC.Pr

theorem exh : GlobalTheory.Published.LanglandsExhaustionGL := PositivityTheory.Exh.langlandsExhaustionGL_holds
theorem multi : GlobalTheory.Published.LanglandsMultisegments := PositivityTheory.Exh.langlandsMultisegments_holds
theorem cos : GlobalTheory.Published.StandardCosocleGL := PositivityTheory.Exh.standardCosocleGL_holds
theorem bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness := PositivityTheory.Prw.bernsteinZelevinskyFiniteness_holds
theorem zel : GlobalTheory.Published.ZelevinskyPolynomialRing :=
  PositivityTheory.Prw.zelevinskyPolynomialRing_of bz PositivityTheory.RgGu.segmentRepresentation PositivityTheory.Groth.grothendieckRingPolynomial_holds
theorem dual : GlobalTheory.Published.LanglandsDataDualGL := PositivityTheory.Pf1.LocalLanglands.LDual.langlandsDataDualGL_of_cosocle cos
theorem adm : GlobalTheory.Published.IrreducibleAdmissibleGL := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
theorem dzs : GlobalTheory.Published.DepthZeroSupport := GlobalTheory.SmGL.depthZeroSupport

end UpperTheory.Zero.LLC.Pr
end
end
