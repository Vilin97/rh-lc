module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GenericUnlinkedGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentJacquetAll
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
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
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFinitenessStatement
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GeometricSplitting.Imports
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.Realize
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalIsGeneric
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalTwistedKernelTopStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeZeroWhittakerKernel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNontrivialDerivative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.ExistsEquivOfMapUnivEq
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerHeredity.Replay
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.NuPairInjectivity.NuPair

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltrationStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.geometricLemma_of_bzFiniteness_of_filtration : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemmaFiltration → GlobalTheory.Published.GeometricLemma := by
  first | exact @GlobalTheory.geometricLemma_of_filtration | exact GlobalTheory.geometricLemma_of_filtration | (intros; apply GlobalTheory.geometricLemma_of_filtration <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOf

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.RgGu

theorem suppExists (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    SuppExists k := by
  intro N V _ _ π hs hi
  have hG : GlobalTheory.Published.GeometricLemma := GlobalTheory.T.geometricLemma_of_bzFiniteness_of_filtration GlobalTheory.T.bernstein_zelevinsky_finiteness PositivityTheory.Geo.geometricLemmaFiltration
  obtain ⟨s, h⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport GlobalTheory.T.bernstein_zelevinsky_finiteness hG (IrrGL.of π hs hi)
  exact ⟨s, h.of_equiv (IrrGL.equivOf π hs hi).symm⟩

theorem genericUnlinkedGL_of
    (hS : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      SuppExists k)
    (hU : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      GenericUnique k)
    (hR : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k],
      UnlinkedRealize k) :
    GlobalTheory.Published.GenericUnlinkedGL := by
  intro k _ _ _ _ _ N V _ _ π hs hi hg
  obtain ⟨s, hsupp⟩ := hS k N V π hs hi
  have hsum : (s.map Sigma.fst).sum = N := by simpa using hsupp.sum_fst
  obtain ⟨h, Δ, x, hd, hΔ, hL, hx, hxg⟩ := hR k N s (fun y hy => hsupp.isCusp hy) hsum
  exact ⟨h, Δ, x, hd, hΔ, hL, hU k N s V _ π (prodIrr x hd) hsupp hx hg hxg⟩

end GlobalTheory.RgGu

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.CuspidalGenericity.Direct

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

theorem GlobalTheory.BZSeg.Cusp.isGenericFor_of_isCuspidal_direct :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (GL (Fin (N + 1)) k) V), IsCuspidal π → Nontrivial V → IsGenericFor ψ π :=
  GlobalTheory.CompanionTheory.BZDeriv.isGenericFor_of_isCuspidal_of GlobalTheory.CompanionTheory.BZMirDer.NonZero.exists_derivative_nontrivial
    (fun k _ _ _ _ ψ m n V _ _ π => GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM (k := k) ψ m n V π) GlobalTheory.T.cuspidal_twisted_kernel_top
    (fun k _ _ _ _ ψ N V _ _ π => GlobalTheory.CompanionTheory.DerWhit.twKer_derUnip_zero (k := k) ψ N V π)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.CuspidalGenericity.Bridge

section

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir

namespace GlobalTheory.BZSeg.Cusp

theorem nontrivial_of_isIrreducible {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  exact bot_ne_top (α := Subrepresentation ρ) (Subrepresentation.ext (Subsingleton.elim _ _))

theorem cuspGeneric (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GlobalTheory.BZSeg.CuspGeneric k := by
  intro N V _ _ π hN _ hirr hc
  obtain ⟨ψ, hψc, hψ1⟩ := exists_continuous_addChar_ne_one (k := k)
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  exact ⟨ψ, hψc, hψ1, GlobalTheory.BZSeg.Cusp.isGenericFor_of_isCuspidal_direct k ψ hψc hψ1 M V π hc (nontrivial_of_isIrreducible π hirr)⟩

end GlobalTheory.BZSeg.Cusp

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.TopAll

section

@[expose] public section

namespace GlobalTheory.RgGu

theorem genericUnique (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    GenericUnique k :=
  genericUnique_of PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top (PositivityTheory.rg.gu.hered2.whitHeredity_all k)
    (PositivityTheory.rg.gu.whit.whitRankIrr k) (GlobalTheory.BZSeg.Cusp.cuspGeneric k)

end GlobalTheory.RgGu
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOfSegRep2

section

@[expose] public section

namespace GlobalTheory.RgGu

theorem genericUnlinkedGL_of_segRep2 (hZ : GlobalTheory.Published.SegmentRepresentation) : GlobalTheory.Published.GenericUnlinkedGL :=
  genericUnlinkedGL_of (fun k _ _ _ _ _ => suppExists k) (fun k _ _ _ _ _ => genericUnique k)
    (fun k _ _ _ _ _ => unlinkedRealize (k := k)
      (GlobalTheory.CompanionTheory.SegCoarse.lSegJacquet PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top hZ) (GlobalTheory.RgGu.Nup2.nuPair k))

end GlobalTheory.RgGu
end
end
