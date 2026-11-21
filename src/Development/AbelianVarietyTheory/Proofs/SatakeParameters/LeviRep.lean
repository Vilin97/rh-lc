import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.GodementJacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def eMat (k : Type) [Field k] (r t : ℕ) : Matrix (Fin (r + t)) (Fin r) k :=
  Matrix.of fun i j => if (i : ℕ) = j then 1 else 0

end GlobalTheory.GodementJacquet
