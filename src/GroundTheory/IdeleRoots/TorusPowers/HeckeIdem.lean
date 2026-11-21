module

public import Mathlib
public import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

open scoped TensorProduct NumberField.AdeleRing
open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GroundTheory.Global GroundTheory.Global.AdeleBaseChange
  GroundTheory.Global.SemiLocal

namespace GroundTheory.BlockD

namespace ThmBHecke

section Single

variable {K : Type} [Field K] [NumberField K]

open Classical in

end Single

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem adeleMap_snd_apply (a : AF F) (w : HeightOneSpectrum (𝓞 E)) :
    (adeleMap F E a).2 w = completionMap (below F w) w (a.2 (below F w)) :=
  rfl

open Classical in

section Conj

variable {σ : E →ₐ[F] E}

end Conj

end ThmBHecke

end GroundTheory.BlockD
