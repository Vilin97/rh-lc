module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
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
import Mathlib.FieldTheory.Galois.Profinite
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.AlgebraicWeights.IsAlgWeight
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverAlg
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import ReciprocityTheory.Automorphisms.PlaceA
import ReciprocityTheory.GaloisValuations.GlobalA
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyEqOfEqOnDense
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesMemOfFinset

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.CoefField

theorem entries_mem_of_finset : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → ∃ S : Finset (Qbar l), ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, z ∈ K) → ∀ g s t, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  intro l _ E Ω _ _ _ _ _ a ρ hρ
  obtain ⟨L, -, hL⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem l (Formalism.ConjugateSelfDual.G E Ω) a ρ hρ
    ⟨⊥, inferInstance⟩
  haveI := L.2
  let B := Module.finBasis ℚ_[l] ↥L.1
  classical
  refine ⟨Finset.univ.image (fun i => ((B i : ↥L.1) : Qbar l)), fun K hK g s t => ?_⟩
  have key : ∀ x : ↥L.1, (x : Qbar l) ∈ K := by
    intro x
    have hx : x ∈ Submodule.span ℚ_[l] (Set.range B) := B.mem_span x
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact hK _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    | zero => simpa using K.zero_mem
    | add y z _ _ hy hz => simpa using K.add_mem hy hz
    | smul c y _ hy => simpa using K.smul_mem hy (x := c)
  exact key ⟨_, hL g s t⟩

end GlobalTheory.CoefField
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepEntriesMemOfFinsetStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.galoisRep_entries_mem_of_finset : ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l)), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → ∃ S : Finset (Qbar l), ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, z ∈ K) → ∀ g s t, ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  first | exact @GlobalTheory.CoefField.entries_mem_of_finset | exact GlobalTheory.CoefField.entries_mem_of_finset | (intros; apply GlobalTheory.CoefField.entries_mem_of_finset <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolys

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.FrobSysCoef

theorem main : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (Formalism.ConjugateSelfDual.G E Ω)) (p : Formalism.ConjugateSelfDual.G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, ι.symm z ∈ K) → ∀ ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep ρ → (∀ σ ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) → ∃ Pm : GL (Fin a) (Qbar l), ∀ g s t, ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  intro l _ ι E Ω _ _ _ _ _ a U p hU
  classical
  by_cases hex : ∃ ρ₀ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l),
      Continuous (fun g => ((ρ₀ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep ρ₀ ∧
      (∀ σ ∈ U, ((ρ₀ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ)
  · obtain ⟨ρ₀, hc₀, hs₀, hp₀⟩ := hex
    obtain ⟨S₀, hS₀⟩ := GlobalTheory.T.galoisRep_entries_mem_of_finset l E Ω a ρ₀ hc₀
    refine ⟨S₀.image ι, fun K hK ρ hc hs hp => ?_⟩
    have hK' : ∀ z ∈ S₀, z ∈ K := fun z hz => by
      simpa using hK (ι z) (Finset.mem_image_of_mem _ hz)
    have hU' : ∀ σ ∈ U, ((ρ₀ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
        ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly := fun σ hσ =>
      Polynomial.map_injective ι.toRingHom ι.injective ((hp₀ σ hσ).trans (hp σ hσ).symm)
    have hall := GlobalTheory.charpoly_eq_of_eqOn_dense _ _ hc₀ hc U hU hU'
    obtain ⟨Pm, hPm⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ₀ ρ hs₀ hs hall
    refine ⟨Pm⁻¹, fun g s t => ?_⟩
    have : Pm⁻¹⁻¹ * ρ g * Pm⁻¹ = ρ₀ g := by
      rw [hPm g, inv_inv]; group
    rw [this]
    exact hS₀ K hK' g s t
  · refine ⟨∅, fun K _ ρ hc hs hp => ?_⟩
    exact absurd ⟨ρ, hc, hs, hp⟩ hex

end GlobalTheory.FrobSysCoef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteCoefficientSetFrobeniusCharpolysStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

theorem _root_.GlobalTheory.T.exists_finite_coefficient_set_frobenius_charpolys : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ) (U : Set (Formalism.ConjugateSelfDual.G E Ω)) (p : Formalism.ConjugateSelfDual.G E Ω → ℂ[X]), Dense U → ∃ S : Finset ℂ, ∀ K : IntermediateField ℚ_[l] (Qbar l), (∀ z ∈ S, ι.symm z ∈ K) → ∀ ρ : Formalism.ConjugateSelfDual.G E Ω →* GL (Fin a) (Qbar l), Continuous (fun g => ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l))) → IsSSRep ρ → (∀ σ ∈ U, ((ρ σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom = p σ) → ∃ Pm : GL (Fin a) (Qbar l), ∀ g s t, ((Pm⁻¹ * ρ g * Pm : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) s t ∈ K := by
  first | exact @GlobalTheory.FrobSysCoef.main | exact GlobalTheory.FrobSysCoef.main | (intros; apply GlobalTheory.FrobSysCoef.main <;> assumption)
end
end
