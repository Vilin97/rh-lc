import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfMemZalg

noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.CuspRep

namespace GlobalTheory.LeviGL.ZGood

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem zalg_commute {z z' : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) (hz' : z' ∈ Zalg E a) : Commute z z' := by
  first
  | exact @_root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg
  | exact _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg
  | (apply _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuantumMinorCharts.commute_of_mem_Zalg ..)

end GlobalTheory.LeviGL.ZGood

end
