module

public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsNineAdd
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalPtfsData
public import GroundTheory.ProfiniteCohomology.PoitouTate.PtCompactDualMapEqZeroOfPtCompactToGlobalEqZero
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsCohCharPf
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
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr0B
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr1C
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocTr2
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PfContActionTwDualC
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.NineAddOfFound3
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualQZ
public import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeZeroLeft
public import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.DegreeTwoCohomologyComparisonLeft

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


theorem degree_two_cohomology_comparison_left (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (ζ : AlgebraicClosure ℚ) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] [Finite d.A]
    [∀ v : S, IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))] [IsDiscreteRep (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)] (hρ' : ContAction (twDual μ ρ)) :
    ∃ (E : H2 (twDual μ ρ) ≃+ cohomology (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 2)
      (Ev : ∀ v : S, H2 ((twDual μ ρ).comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 2),
      (∀ v x, Ev v (resH2 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) x) = ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) v 2 (E x)) ∧
      (∀ (z : ↥(Z2 (twDual μ ρ))) (x : cocycles (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 2),
        (∀ s, cochainOf (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) (cocycleι (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 2 x) s = d.eD (z.1 (d.e.symm (s 0), d.e.symm (s 1)))) → E (Submodule.Quotient.mk z) = cohomologyπ (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 2 x) ∧
      (∀ (v : S) (z : ↥(Z2 ((twDual μ ρ).comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 2),
        (∀ s, cochainOf _ (cocycleι _ 2 x) s = d.eD (z.1 (d.ev v (s 0), d.ev v (s 1)))) → Ev v (Submodule.Quotient.mk z) = cohomologyπ _ 2 x) :=
  resCmpChar2' d.e (ι := S) (Lv := fun v : S => ↥(Dec (F := Kf.1) (Av v)))
    (Hv := fun v : S => (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
      (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) (locFam S Av) (continuous_locFam S Av) (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩)
    d.ev (fun v => (d.hev_cont v).1) (fun v => (d.hev_cont v).2) d.hev (twDual μ ρ) hρ' (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) d.eD d.hD

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeOneLeft

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


theorem tate_duality_degree_one_left (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (ζ : AlgebraicClosure ℚ) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] [Finite d.A]
    [∀ v : S, IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A))] [IsDiscreteRep (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)] (hρ' : ContAction (twDual μ ρ)) :
    ∃ (E : H1 (twDual μ ρ) ≃+ cohomology (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 1)
      (Ev : ∀ v : S, H1 ((twDual μ ρ).comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 1),
      (∀ v x, Ev v (resH1 (twDual μ ρ) (locFam S Av v) (continuous_locFam S Av v) x) = ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) v 1 (E x)) ∧
      (∀ (z : ↥(Z1 (twDual μ ρ))) (x : cocycles (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 1),
        (∀ s, cochainOf (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) (cocycleι (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 1 x) s = d.eD (z.1 (d.e.symm (s 0)))) → E (Submodule.Quotient.mk z) = cohomologyπ (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) 1 x) ∧
      (∀ (v : S) (z : ↥(Z1 ((twDual μ ρ).comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) 1),
        (∀ s, cochainOf _ (cocycleι _ 1 x) s = d.eD (z.1 (d.ev v (s 0)))) → Ev v (Submodule.Quotient.mk z) = cohomologyπ _ 1 x) :=
  resCmpChar1' d.e (ι := S) (Lv := fun v : S => ↥(Dec (F := Kf.1) (Av v)))
    (Hv := fun v : S => (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
      (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) (locFam S Av) (continuous_locFam S Av) (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩)
    d.ev (fun v => (d.hev_cont v).1) (fun v => (d.hev_cont v).2) d.hev (twDual μ ρ) hρ' (dualRep (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) d.eD d.hD

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeOneMiddle

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


theorem tate_duality_degree_one_middle (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (ζ : AlgebraicClosure ℚ) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] (hρ : ContAction ρ) :
    ∃ (E : H1 ρ ≃+ cohomology d.A 1)
      (Ev : ∀ v : S, H1 (ρ.comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 1),
      (∀ v x, Ev v (resH1 ρ (locFam S Av v) (continuous_locFam S Av v) x) = ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) d.A v 1 (E x)) ∧
      (∀ (z : ↥(Z1 ρ)) (x : cocycles d.A 1),
        (∀ s, cochainOf d.A (cocycleι d.A 1 x) s = d.eM (z.1 (d.e.symm (s 0)))) → E (Submodule.Quotient.mk z) = cohomologyπ d.A 1 x) ∧
      (∀ (v : S) (z : ↥(Z1 (ρ.comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 1),
        (∀ s, cochainOf _ (cocycleι _ 1 x) s = d.eM (z.1 (d.ev v (s 0)))) → Ev v (Submodule.Quotient.mk z) = cohomologyπ _ 1 x) :=
  resCmpChar1' d.e (ι := S) (Lv := fun v : S => ↥(Dec (F := Kf.1) (Av v)))
    (Hv := fun v : S => (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
      (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) (locFam S Av) (continuous_locFam S Av) (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩)
    d.ev (fun v => (d.hev_cont v).1) (fun v => (d.hev_cont v).2) d.hev ρ hρ d.A d.eM d.hM

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeTwoMiddle

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


theorem tate_duality_degree_two_middle (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (ζ : AlgebraicClosure ℚ) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] (hρ : ContAction ρ) :
    ∃ (E : H2 ρ ≃+ cohomology d.A 2)
      (Ev : ∀ v : S, H2 (ρ.comp (locFam S Av v)) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 2),
      (∀ v x, Ev v (resH2 ρ (locFam S Av v) (continuous_locFam S Av v) x) = ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) d.A v 2 (E x)) ∧
      (∀ (z : ↥(Z2 ρ)) (x : cocycles d.A 2),
        (∀ s, cochainOf d.A (cocycleι d.A 2 x) s = d.eM (z.1 (d.e.symm (s 0), d.e.symm (s 1)))) → E (Submodule.Quotient.mk z) = cohomologyπ d.A 2 x) ∧
      (∀ (v : S) (z : ↥(Z2 (ρ.comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 2),
        (∀ s, cochainOf _ (cocycleι _ 2 x) s = d.eM (z.1 (d.ev v (s 0), d.ev v (s 1)))) → Ev v (Submodule.Quotient.mk z) = cohomologyπ _ 2 x) :=
  resCmpChar2' d.e (ι := S) (Lv := fun v : S => ↥(Dec (F := Kf.1) (Av v)))
    (Hv := fun v : S => (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
      (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) (locFam S Av) (continuous_locFam S Av) (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩)
    d.ev (fun v => (d.hev_cont v).1) (fun v => (d.hev_cont v).2) d.hev ρ hρ d.A d.eM d.hM

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.TateDualityDegreeZeroMiddle

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


theorem tate_duality_degree_zero_middle (Kf : FiniteSubfield) [NumberField Kf.1]
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) {l r : ℕ}
    [Fact l.Prime] (ζ : AlgebraicClosure ℚ) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (d : FoundData Kf S l r ζ Av μ M ρ) [IsDiscreteRep d.A] (hρ : ContAction ρ) :
    ∃ (E : ↥(H0 ρ) ≃+ cohomology d.A 0)
      (Ev : ∀ v : S, ↥(H0 (ρ.comp (locFam S Av v))) ≃+ cohomology (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 0),
      (∀ v x, Ev v (resH0 ρ (locFam S Av v) x) = ptRes (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩) d.A v 0 (E x)) ∧
      (∀ (z : ↥(H0 ρ)) (x : cocycles d.A 0),
        (∀ s, cochainOf d.A (cocycleι d.A 0 x) s = d.eM z.1) → E z = cohomologyπ d.A 0 x) ∧
      (∀ (v : S) (z : ↥(H0 (ρ.comp (locFam S Av v)))) (x : cocycles (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom d.A) 0),
        (∀ s, cochainOf _ (cocycleι _ 0 x) s = d.eM z.1) → Ev v z = cohomologyπ _ 0 x) :=
  resCmpChar0' d.e (ι := S) (Lv := fun v : S => ↥(Dec (F := Kf.1) (Av v)))
    (Hv := fun v : S => (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1) ≃ₐ[
      (v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1]
      AlgebraicClosure ((v : HeightOneSpectrum (𝓞 Kf.1)).adicCompletion Kf.1))) (locFam S Av) (continuous_locFam S Av) (fun v : S => gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩)
    d.ev (fun v => (d.hev_cont v).1) (fun v => (d.hev_cont v).2) d.hev ρ hρ d.A d.eM d.hM

end PositivityTheory.Lit1.PTN
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PoitouTateNineTerm.NineAddCore

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual
  GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2


theorem nineAdd_core (Kf : FiniteSubfield)
    [IsAlgClosure Kf.1 (AlgebraicClosure ℚ)] {l r : ℕ} [Fact l.Prime] (hl : l ≠ 2 ∨ IsTotallyComplex Kf.1) (hr : 0 < r)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (l ^ r))
    (inv : InvFam Kf.1 (AlgebraicClosure ℚ) l r) (hinv : PositivityTheory.PoitouTateConclusion.InvNormalised ζ inv)
    (S : Finset (HeightOneSpectrum (𝓞 Kf.1))) (hS : ContainsAbove S l) (Av : S → ValuationSubring (AlgebraicClosure ℚ))
    (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (μ : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) →* (ZMod (l ^ r))ˣ)
    (hμ : μ.comp (toGS (AlgebraicClosure ℚ) _) = cycMod Kf.1 (AlgebraicClosure ℚ) l r)
    (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
    [DiscreteTopology M]
    (ρ : Representation (ZMod (l ^ r)) (GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 Kf.1)))) M)
    (hρ : ContAction ρ) (d : FoundData Kf S l r ζ Av μ M ρ) :
    NineAdd (loc0 S Av ρ) (tr0 S Av μ (invAt S Av μ hμ inv) ρ) (loc1 S Av ρ)
      (tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ) (loc2 S Av ρ) (tr2 S Av μ (invAt S Av μ hμ inv) ρ) := by
  haveI := d.isDiscrete
  haveI : Finite d.A := Finite.of_equiv M d.eM.toEquiv
  haveI hDd : IsDiscreteRep (dualRep (gsRoots (K := Kf) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A) := isDiscreteRep_dualRep _ _
  haveI hDv : ∀ v : S, IsDiscreteRep (Rep.res (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs ⟨v.1, Finset.mem_coe.2 v.2⟩).toMonoidHom
      (dualRep (gsRoots (K := Kf) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A)) :=
    fun v => isDiscreteRep_res_dualRep_of_finite _ _ _
  have hρ' : ContAction (twDual μ ρ) := contAction_twDual_C S μ hμ ρ hρ
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero r (Fact.out : l.Prime).ne_zero⟩
  have hSN : ∀ v : HeightOneSpectrum (𝓞 Kf.1), (((l ^ r : ℕ) : ℕ) : 𝓞 Kf.1) ∈ v.asIdeal →
      v ∈ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) := by
    intro v hv
    rw [Nat.cast_pow] at hv
    exact Finset.mem_coe.2 (hS v (v.isPrime.mem_of_pow_mem r hv))
  have hK : Odd (l ^ r) ∨ IsTotallyComplex Kf.1 := by
    rcases hl with h | h
    · exact Or.inl ((Fact.out : l.Prime).odd_of_ne_two h).pow
    · exact Or.inr h
  have hMt : ∀ m : d.A, (l ^ r) • m = 0 := by
    intro m
    rw [← d.eM.apply_symm_apply m, ← map_nsmul, nsmul_eq_zero_of_zmod, map_zero]
  have F9 :=
    poitouTate_nineTerm_gs (K := Kf) (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs hSN hK d.A hMt
  have hM0 := tate_duality_degree_zero_middle Kf S ζ Av μ ρ d hρ
  have hM1 := tate_duality_degree_one_middle Kf S ζ Av μ ρ d hρ
  have hM2 := tate_duality_degree_two_middle Kf S ζ Av μ ρ d hρ
  have hD0 := tate_duality_degree_zero_left Kf S ζ Av μ ρ d hρ'
  have hD1 := tate_duality_degree_one_left Kf S ζ Av μ ρ d hρ'
  have hD2 := degree_two_cohomology_comparison_left Kf S ζ Av μ ρ d hρ'
  exact nineAdd_of_found3 (N := l ^ r) S (gsFinFamily (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs) (gsRoots (S : Set (HeightOneSpectrum (𝓞 Kf.1))) (l ^ r)) d.A (gsLocalInvRootsQZ (S : Set (HeightOneSpectrum (𝓞 Kf.1))) d.ιs (l ^ r)) _ _
    F9
    (fun k => resH0 ρ (locFam S Av k)) (fun k => resH1 ρ (locFam S Av k) (continuous_locFam S Av k))
    (fun k => resH2 ρ (locFam S Av k) (continuous_locFam S Av k))
    (fun k => resH0 (twDual μ ρ) (locFam S Av k))
    (fun k => resH1 (twDual μ ρ) (locFam S Av k) (continuous_locFam S Av k))
    (fun k => resH2 (twDual μ ρ) (locFam S Av k) (continuous_locFam S Av k))
    (fun k a b => invAt S Av μ hμ inv k (cupH0H2TwistedDual μ ρ (locFam S Av k) a b))
    (fun k a b => invAt S Av μ hμ inv k (cupH1H1TwistedDual μ ρ (locFam S Av k) (hρ.comp' (continuous_locFam S Av k)) b a))
    (fun k a b => invAt S Av μ hμ inv k (cup20 μ ρ (locFam S Av k) a b))
    (loc0 S Av ρ) (tr0 S Av μ (invAt S Av μ hμ inv) ρ) (loc1 S Av ρ)
    (tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ) (loc2 S Av ρ) (tr2 S Av μ (invAt S Av μ hμ inv) ρ)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun x y => poitouTateNineTerm_transgressionZero_apply S Av μ (invAt S Av μ hμ inv) ρ x y)
    (fun x y => poitouTateNineTerm_transgressionOne_apply S Av μ (invAt S Av μ hμ inv) ρ hρ x y)
    (fun x y => poitouTateNineTerm_transgressionTwo_apply S Av μ (invAt S Av μ hμ inv) ρ x y)
    hM0 hM1 hM2 hD0 hD1 hD2
    (fun Ev Fv c c' k a b => locTr0_B Kf S hr ζ hζ inv hinv hS Av hAv μ hμ ρ hρ d k (Ev k) (c k) (Fv k) (c' k) a b)
    (fun Ev Fv c c' k a b => locTr1_C Kf S hr ζ hζ inv hinv hS Av hAv μ hμ ρ hρ d k (Ev k) (c k) (Fv k) (c' k) a b)
    (fun Ev Fv c c' k a b => locTr2' Kf S hr ζ hζ inv hinv hS Av hAv μ hμ ρ hρ d k (Ev k) (c k) (Fv k) (c' k) a b)

end PositivityTheory.Lit1.PTN
end
end
end
