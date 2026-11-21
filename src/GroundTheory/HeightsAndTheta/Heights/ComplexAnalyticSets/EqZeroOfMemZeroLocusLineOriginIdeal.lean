import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Characterised
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.MahlerSectionBasic
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix
open scoped ContDiff ENNReal

noncomputable section

variable {n d e : ℕ}

def zeroLocus {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) : Set (Fin n → ℂ) :=
  {x | ∀ q ∈ J, eval x q = 0}

structure IsAffVariety (J : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) : Prop where
  isPrime : J.IsPrime
  dim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d

open Classical in

open Classical in

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
