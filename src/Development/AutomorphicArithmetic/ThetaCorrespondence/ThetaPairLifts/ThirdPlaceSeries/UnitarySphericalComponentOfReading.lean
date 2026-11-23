module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Laws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RpowNegLeNormOfComponent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeMultisetMapInv
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
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatake
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeMultisetMapInvStatement

section

@[expose] public section

open GlobalTheory.LatHecke GlobalTheory.RowSatakeBound

theorem _root_.GlobalTheory.T.isUnitarySphericalSatakeMultiset_map_inv : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (β : Multiset ℂ), IsUnitarySatake O K r β → IsUnitarySatake O K r (β.map (·⁻¹)) := by
  first | exact @GlobalTheory.SatakeInv.isUnitarySatake_map_inv | exact GlobalTheory.SatakeInv.isUnitarySatake_map_inv | (intros; apply GlobalTheory.SatakeInv.isUnitarySatake_map_inv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitarySphericalSatakeOfUnitarisableHasSatakeStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem _root_.GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ), letI := GlobalTheory.LocalData.complRel w; haveI := GlobalTheory.LocalData.isLocalField w; ∀ (π : Irr (w.adicCompletion E) n) (α : Fin n → ℂˣ), HasSatake π.π α → IsUnitarisable π.π → GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w n (Finset.univ.val.map fun i => (α i : ℂ)) := by
  first | exact @GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | exact GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake | (intros; apply GlobalTheory.SatHecke.isUnitarySatakeAt_of_hasSatake <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParametersStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

theorem _root_.GlobalTheory.T.sphericalRepGL_exists_satakeParameters : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (π : Irr k n), IsSpherical π.π → ∃ α : Fin n → ℂˣ, HasSatake π.π α := by
  first | exact @GlobalTheory.SatakeExists.main | exact GlobalTheory.SatakeExists.main | (intros; apply GlobalTheory.SatakeExists.main <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitarySphericalComponentOfReading

section

@[expose] public section



section
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem unitarySphericalComponent_of_reading_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A)
      (S : Reading T), _root_.GlobalTheory.SplitRead.LawsAlt S → RowUnit S → GlobalTheory.RowSatakeBound.UnitarySphericalComponent N A := by
  intro hBZ R H what₂ N A T S hL hU i σ hσ w hw hu
  have hloc := (S i w hw).locW σ hσ
  have hsph : IsSpherical ((S i w hw).row σ).π := by
    rw [← (hL i w hw).sph _ _, ← hloc, ← T.unr]
    exact hu
  obtain ⟨α, hα⟩ := GlobalTheory.T.sphericalRepGL_exists_satakeParameters hBZ _ _ _ hsph
  have hfrob : A.frobEig (A.locW i σ w) =
      (Finset.univ.val.map fun j => (α j : ℂ)).map (·⁻¹) := by
    rw [T.frobEig w _ hu, hloc, (hL i w hw).sat _ _ α hα, Multiset.map_map]
    simp
  have h1 : GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w R.r (Finset.univ.val.map fun j => (α j : ℂ)) :=
    GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake H.E w R.r _ α hα (hU i w hw σ hσ)
  rw [hfrob]
  refine ⟨?_, ?_⟩
  · simpa [Multiset.map_map, Function.comp_def] using h1
  · have := GlobalTheory.RowSatakeBound.finite_residue w
    exact GlobalTheory.T.isUnitarySphericalSatakeMultiset_map_inv _ _ _ _ h1
end GlobalTheory.SplitRead
end
end
end
end
