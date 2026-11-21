import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Partners
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrameLats

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg
open scoped TensorProduct ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.HermitianLocalData

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

section Loc

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E))
  (r : ℕ) (T T' : 𝓞 F) {v : Pl F} (δ : Fv F v) (g : ℕ)

end Loc

open scoped Classical in

omit [NumberField F] [NumberField E] in

section Meas

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

end Meas

end GlobalTheory.IndefiniteRowSideFullHecke.HermitianLocalData
