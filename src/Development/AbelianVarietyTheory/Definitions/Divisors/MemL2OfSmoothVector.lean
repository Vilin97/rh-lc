import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeL2InnerProduct

noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.GLFin

section Abstract

variable {Γ K : Type*} [Group Γ] [NormedAddCommGroup K] [InnerProductSpace ℂ K]

end Abstract

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def word (l : List (Lie E a)) : Module.End ℂ (Sm E a) := (l.map (lie E a)).prod

variable (μ : Measure (GA E a)) [μ.IsMulLeftInvariant]

variable {μ} {H : Submodule ℂ (L2 (latticeGL E a) μ)}

variable (μ H) in

variable (μ H) in

variable (μ H) in

open Classical in

variable (μ H) in

variable (μ H) in

end GlobalTheory.GLFin

end
