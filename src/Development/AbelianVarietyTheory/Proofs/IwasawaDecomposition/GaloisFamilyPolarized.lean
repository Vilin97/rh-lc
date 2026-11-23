module

public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfIsConjPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqIffConjPl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.Objects
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs

-- Source module: Formalism.LocalToGlobal.GaloisLevelStructure.LevelQ

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain

namespace Formalism.L2

variable {D : D7} {C : Host.CharFrame D} {nch : NChoice D}

theorem qPl_tup (Tp : Host.TupTied D C nch) (μ : D.what₂.Tup) (j : Fin D.R.m) :
    qPl D (Tp.tup μ j) = {v | v ∉ gPl D ∧ ∃ w : PlE D.host, NG.OverPl w v ∧ ¬ (Tp.xi μ).UnrAt w} := by
  ext v
  simp only [qPl, Set.mem_ofPred_eq, Host.TupTied.tup]
  refine and_congr_right fun hv => exists_congr fun w => and_congr_right fun hw => not_congr ?_
  have hm : (C.mu0 j).UnrAt w := by
    refine (C.isMu0 j).unr w fun k hk => hv ?_
    simp only [gPl, Set.mem_ofPred_eq]
    exact ⟨w, hw, k, hk⟩
  constructor
  · intro h x hx
    have hx' := h x hx
    change (C.mu0 j).loc w x * (Tp.xi μ).loc w x = 1 at hx'
    rw [hm x hx, one_mul] at hx'
    exact hx'
  · intro h x hx
    change (C.mu0 j).loc w x * (Tp.xi μ).loc w x = 1
    rw [hm x hx, h x hx, one_mul]

end Formalism.L2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyPolarized

section

@[expose] public section

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.SphNonSplit

theorem not_split_of_overPl (D : D7) {w w' : PlE D.host} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (hw : NG.OverPl w v) (hw' : NG.OverPl w' v) (hs : ¬ IsSplitPl D.host w) : ¬ IsSplitPl D.host w' := by
  intro hs'
  have hu : HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w =
      HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) w' :=
    HeightOneSpectrum.ext (hw.trans hw'.symm)
  have hr : Module.finrank (maximalRealSubfield D.host.E) D.host.E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj D.host.E) hr
      (IsCMField.complexConj_ne_one D.host.E) w' w).1 hu with h | h
  · exact hs (h ▸ hs')
  · have hc : (IsCMField.complexConj D.host.E).toRingEquiv = D.host.conj.toRingEquiv := by
      refine RingEquiv.ext fun x => ?_
      apply D.host.φ₀.injective
      show D.host.φ₀ (IsCMField.complexConj D.host.E x) = D.host.φ₀ (D.host.conj x)
      rw [IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
    rw [hc] at h
    exact hs (GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl hs' ((GlobalTheory.Mem.Chr.conjPl_main.2.1 _ _ w' w).2 h))

theorem split_of_over_g (D : D7) (k : Fin 2) {w : PlE D.host} (hw : w ∈ placesOver D.host.E (D.host.g k)) :
    IsSplitPl D.host w := by
  obtain ⟨u, h | h⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · rw [h]; exact GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u
  · exact GlobalTheory.ConjugatePlaceSplitting.isSplitPl_of_isConjPl (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k u) h

theorem not_mem_bad (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C)
    (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v)
    (w0 : D.what₂.places.Pl) (j : Fin D.R.m) (w : PlE D.host) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)))
    (hw : NG.OverPl w v) (hs : ¬ IsSplitPl D.host w) :
    v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw w0) j) := by
  have hg : v ∉ gPl D := by
    rintro ⟨w', hw', k, hk⟩
    exact not_split_of_overPl D hw hw' hs (split_of_over_g D k hk)
  rintro (h | h)
  · exact hg h
  · rw [qPl_tup] at h
    obtain ⟨-, w', hw', hr⟩ := h
    apply not_split_of_overPl D hw hw' hs
    rw [tp.xi_tw] at hr
    by_contra hns
    apply hr
    have hpsi : (tp.psi w0).UnrAt w' := by
      obtain ⟨Q, hQ⟩ := tp.psi_gen w0
      exact (hQ.ram w').2 fun hq => hns (hQ.split w' hq)
    by_cases hl : D.what₂.places.resChar w0 = D.host.pde
    · have hd : cf.del'.UnrAt w' := cf.isDel'.unr w' fun hp => hns (hsp w' (Or.inr hp))
      intro x hx
      simp only [Host.CharFrame.delAt, hl, ↓reduceIte]
      change cf.del'.loc w' x * (tp.psi w0).loc w' x = 1
      rw [hd x hx, hpsi x hx, one_mul]
    · have hd : cf.del.UnrAt w' := cf.isDel.unr w' fun hp => hns (hsp w' (Or.inl hp))
      intro x hx
      simp only [Host.CharFrame.delAt, hl, ↓reduceIte]
      change cf.del.loc w' x * (tp.psi w0).loc w' x = 1
      rw [hd x hx, hpsi x hx, one_mul]

end GlobalTheory.SphNonSplit

namespace GlobalTheory.SphNonSplit

end GlobalTheory.SphNonSplit
end
end
end
