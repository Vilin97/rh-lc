module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BlochKatoSelmerVanishes
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bridge

section

@[expose] public section

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp

namespace UpperTheory.V.Af

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def AutOn (K : Type) [Field K] [NumberField K] [IsCMField K] (ι : Qbar l ≃+* ℂ) (j : ℤ)
    (a : G ℚ Ω → Matrix (Fin n) (Fin n) (Qbar l)) : Prop :=
  ∃ (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω) (ρ : G K Ω →* GL (Fin n) (Qbar l)),
    (∀ s : G K Ω, (ρ s : Matrix (Fin n) (Fin n) (Qbar l)) = a (s.restrictScalars ℚ)) ∧ IsAutCsd ι (tw ρ (cycBar K Ω l ^ j))

end UpperTheory.V.Af
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicCases.AutomorphyClauseStatement

section

@[expose] public section

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.Aut

def IsQi (K : Type) [Field K] [NumberField K] : Prop := Module.finrank ℚ K = 2 ∧ ∃ i : K, i * i = -1

structure BPrime (K : Type) [Field K] [NumberField K] [IsCMField K] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : G ℚ Ω → Matrix (Fin 3) (Fin 3) (Qbar l)) : Prop where
  opens : ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ (eta4 Ω).ker → MatIrr U a
  cyc : MatIrr ((eta4 Ω).ker ⊓ (cycZ ℚ Ω l).ker) a
  aut : Af.AutOn K ι (-1) a

end UpperTheory.V.Aut

end
end
end
