module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.EssSquareIntegrableSegments
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ExhaustionOfThree
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LUnlinkedIrrOfSeg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LanglandsMultisegmentsOfSeg
public import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.ProbeL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.PropsCos
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFreeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissibleStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CasselmanNecTemp
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CohomologicalCsdTemperedOfUsed
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.ExistsUnitaryCentralTwist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.Development
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.TempProdUsedOf
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopStd

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.SegmentOfTwistedSquareIntegrable

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.PfEss.H13

theorem isLSeg_of_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {Δ : Segment k} {x y : IrrGL (k := k)} (hxy : x = y) (h : IsLSeg Δ x.rep) : IsLSeg Δ y.rep := by
  subst hxy
  exact h

theorem segment_of_twisted_square_integrable (hU : PositivityTheory.Zltwo.EssSqIntUsed) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (δ : IrrGL (k := k)), 1 ≤ δ.1 →
      (∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep) → ∃ Δ : Segment k, IsLSeg Δ δ.rep := by
  intro k _ _ _ _ _ δ hδ ⟨χ, hχ, hs⟩
  obtain ⟨Δ', hΔ'⟩ := hU k (δ.tw χ hχ) hδ hs
  refine ⟨Δ'.tw χ⁻¹ hχ.inv, ?_⟩
  exact isLSeg_of_eq (IrrGL.tw_tw_inv δ χ hχ)
    ((hΔ'.tw χ⁻¹ hχ.inv).of_equiv ((δ.tw χ hχ).twEquiv χ⁻¹ hχ.inv))

theorem square_integrable_of_segment_twist
    (h2 : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (y : IrrGL (k := k)),
      ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y.tw χ hχ) t c → ‖c‖ = 1)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSegJacquet k → ∀ (δ : IrrGL (k := k)), (∃ Δ : Segment k, IsLSeg Δ δ.rep) →
      ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep := by
  intro k _ _ _ _ hJ δ ⟨Δ, hΔ⟩
  obtain ⟨χ, hχ, hc⟩ := h2 k δ
  exact ⟨χ, hχ, Zls.FreeSingleHomotopyEquivDiscreteChains.centredSegSqInt k hA hF hJ (Δ.tw χ hχ) (δ.tw χ hχ)
    ((hΔ.tw χ hχ).of_equiv (δ.twEquiv χ hχ)) hc⟩

end PositivityTheory.PfEss.H13

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.Development

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL

namespace PositivityTheory.PfEss

theorem segment_of_twisted_square_integrable (hU : PositivityTheory.Zltwo.EssSqIntUsed) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (δ : IrrGL (k := k)), 1 ≤ δ.1 →
      (∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep) → ∃ Δ : Segment k, IsLSeg Δ δ.rep := by
  exact PositivityTheory.PfEss.H13.segment_of_twisted_square_integrable hU

theorem exists_unitary_central_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (y : IrrGL (k := k)), ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ),
      ∀ (t : kˣ) (c : ℂ), Zl.ScalarBy (y.tw χ hχ) t c → ‖c‖ = 1 := by
  exact PositivityTheory.PfEss.H2.exists_unitary_central_twist hA

theorem segment_gives_square_integrable (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength) :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], Zc.LSegJacquet k → ∀ (δ : IrrGL (k := k)), (∃ Δ : Segment k, IsLSeg Δ δ.rep) →
      ∃ (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ), IsSqIntCoeff (δ.tw χ hχ).rep := by
  exact PositivityTheory.PfEss.H13.square_integrable_of_segment_twist (exists_unitary_central_twist hA) hA hF

theorem essSquareIntegrableSegments_of (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSocleGL k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegExists k)
    (hJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegJacquet k) : GlobalTheory.Published.EssSquareIntegrableSegments := by
  intro k _ _ _ _ _ δ hδ
  exact ⟨segment_of_twisted_square_integrable (PositivityTheory.Zltwo.essSqIntUsed_of hE hS hL) k δ hδ, segment_gives_square_integrable hA hF k (hJ k) δ⟩

end PositivityTheory.PfEss

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.EssSquareIntegrableSegmentsOfLit

section

@[expose] public section

noncomputable section

namespace PositivityTheory.PfEss

theorem essSquareIntegrableSegments_main (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSocleGL k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegExists k)
    (hJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegJacquet k) : GlobalTheory.Published.EssSquareIntegrableSegments :=
  essSquareIntegrableSegments_of hE PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hF hS hL hJ

end PositivityTheory.PfEss

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.SquareIntegrableSegments.EssSquareIntegrableSegmentsMain2

section

@[expose] public section

noncomputable section

namespace PositivityTheory.PfEss

theorem lSocleGL_of_orderFree (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hO : Zc.LOrderFree k) : Zc.LSocleGL k :=
  GlobalTheory.T.langlands_socle_of_order_free PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (GlobalTheory.T.local_langlands_of_irreducible_admissible PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top) hO

theorem essSquareIntegrableSegments_main2 (hE : GlobalTheory.Published.LanglandsExhaustionGL)
    (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LOrderFree k)
    (hL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegExists k)
    (hJ : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k], Zc.LSegJacquet k) : GlobalTheory.Published.EssSquareIntegrableSegments :=
  essSquareIntegrableSegments_main hE hF (fun k _ _ _ _ _ => lSocleGL_of_orderFree k (hO k)) hL hJ

end PositivityTheory.PfEss

end
end
end

-- Source module: Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.EssSquareIntegrableSegmentsOfSeg

section

@[expose] public section

namespace PositivityTheory.Exh

theorem essSquareIntegrableSegments_of_seg (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.EssSquareIntegrableSegments := by
  have hI : GlobalTheory.Published.IrreducibleAdmissibleGL := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hU := PositivityTheory.Exh.lUnlinkedIrr_of_seg hZ
  exact PositivityTheory.PfEss.essSquareIntegrableSegments_main2
    (PositivityTheory.Exh.langlandsExhaustionGL_of_seg hZ)
    PositivityTheory.Tls2.BZGL.standardFunctorsFiniteLength_top
    (fun k _ _ _ _ _ => PositivityTheory.Exh.lOrderFree_of hU k)
    (fun k _ _ _ _ _ => PositivityTheory.Exh.lSegExists k)
    (fun k _ _ _ _ _ => GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet hI hZ)

end PositivityTheory.Exh
end
end
