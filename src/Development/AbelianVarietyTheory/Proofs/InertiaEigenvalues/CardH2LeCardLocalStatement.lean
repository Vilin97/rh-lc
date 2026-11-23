module

public import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
public import Mathlib.Algebra.Group.AddChar
import ReciprocityTheory.GaloisValuations.GlobalA
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2Local

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardDualZmodLeCard

section

@[expose] public section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem card_dual_zmod_le_card :
    ∀ (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A],
      Nat.card (Module.Dual (ZMod n) A) ≤ Nat.card A := by
  apply GlobalTheory.TateTop.card_dual_le <;> assumption

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LeCardLocal

section

@[expose] public section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory

theorem card_H2_le_of_local_duality : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K) M), 0 < r → ContAction rho → Finite (H2 rho) ∧ Nat.card (H2 rho) ≤ Nat.card M := by
  intro hT l _ K hK r M _ _ _ _ _ rho hr hrho
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfin := (GlobalTheory.finite_H1_H2_of_localTateDuality hT l K hK r M rho hr hrho).2
  obtain ⟨⟨e⟩, -, -, -, h20⟩ := hT l K hK r M rho hr hrho
  refine ⟨hfin, ?_⟩
  haveI : Finite (TDual (ZMod (l ^ r)) M) :=
    Finite.of_injective (fun φ : TDual (ZMod (l ^ r)) M => (φ : M → ZMod (l ^ r)))
      DFunLike.coe_injective
  haveI : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Subtype.finite
  haveI : Finite (H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))) →ₗ[ZMod (l ^ r)]
      H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
    Finite.of_injective (fun f => (f : _ → _)) DFunLike.coe_injective
  calc Nat.card (H2 rho)
      ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))) →ₗ[ZMod (l ^ r)]
          H2 ((charRep (Formalism.GaloisCohomology.cycK l K r)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
        Nat.card_le_card_of_injective _ h20.1
    _ = Nat.card (Module.Dual (ZMod (l ^ r))
          (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K))))) :=
        Nat.card_congr (LinearEquiv.congrRight e).toEquiv
    _ ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK l K r) rho).comp (MonoidHom.id (Formalism.GaloisCohomology.GK l K)))) :=
        GlobalTheory.card_dual_zmod_le_card (l ^ r) _
    _ ≤ Nat.card (TDual (ZMod (l ^ r)) M) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ ≤ Nat.card M := GlobalTheory.card_dual_zmod_le_card (l ^ r) M

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2LeCardLocalStatement

section

@[expose] public section

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

theorem _root_.GlobalTheory.T.card_H2_le_card_local : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)), FiniteDimensional ℚ_[l] K → ∀ (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K) M), 0 < r → ContAction rho → Finite (H2 rho) ∧ Nat.card (H2 rho) ≤ Nat.card M := by
  first | exact @GlobalTheory.card_H2_le_of_local_duality | exact GlobalTheory.card_H2_le_of_local_duality | (intros; apply GlobalTheory.card_H2_le_of_local_duality <;> assumption)
end
end
