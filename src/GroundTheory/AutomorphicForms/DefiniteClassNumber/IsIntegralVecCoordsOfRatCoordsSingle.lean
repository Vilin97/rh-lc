module

public import Mathlib
public import GroundTheory.AutomorphicForms.DefiniteClassNumber.AdelicLattice

@[expose] public section

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField NumberField.InfinitePlace

variable {K : Type*} [Field K] [NumberField K]
variable {E : Type*} [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

variable (K) in

abbrev IntBasisIdx := Free.ChooseBasisIndex ℤ (𝓞 K)

def ratCoords (x : ι → K ⊗[K] E) : (ι × κ) × IntBasisIdx K → ℚ :=
  fun j => (integralBasis K).repr (vecCoords K b x j.1) j.2

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] [Fintype κ] in

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] in

variable (H : Matrix ι ι E)

variable {H}

omit [DecidableEq ι] in

omit [DecidableEq ι] in

omit [DecidableEq ι] in

omit [DecidableEq ι] in

omit [DecidableEq ι] in

omit [DecidableEq ι] in

omit [DecidableEq ι] in

variable (H) in

def ratEmb (x : ι → K ⊗[K] E) : (ι × κ) × IntBasisIdx K → ℝ := fun j => (ratCoords b x j : ℝ)

variable (H) in

variable (H) in

omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [DecidableEq ι] in

end GroundTheory.Automorphic
