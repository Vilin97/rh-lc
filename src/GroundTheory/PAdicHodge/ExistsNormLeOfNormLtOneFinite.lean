import Mathlib
import GroundTheory.PAdicHodge.WAKummerEps
import GroundTheory.PAdicHodge.FundamentalSeqLog
import GroundTheory.PAdicHodge.FundamentalSeqBCris
import GroundTheory.PAdicHodge.ACrisFrobFixed
import GroundTheory.PAdicHodge.BCrisRegularFinal
import GroundTheory.PAdicHodge.BdRInvariants
import GroundTheory.PAdicHodge.AxLemma
import GroundTheory.PAdicHodge.FundamentalSeqSurj
set_option maxSynthPendingDepth 1

noncomputable section

open _root_.WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

variable {p : ℕ} [hp : Fact p.Prime]

section Span

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {K}

end Span

section Contradiction

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem gal_smul_untilt_iterate_of_eq_mul {ε x : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    {σ : Gal(PadicAlgCl p/K)} {a : ℤ_[p]} (h : tiltGal σ x = x * epsPow hε a) (m : ℕ) :
    σ • ((PreTilt.untilt (φi^[m] x) : 𝒪) : ℂ_[p]) = ((PreTilt.untilt (φi^[m] x) : 𝒪) : ℂ_[p]) *
      ((PreTilt.untilt (φi^[m] ε) : 𝒪) : ℂ_[p]) ^ (PadicInt.toZModPow m a).val := by
  rw [← coe_untilt_iterate_tiltGal, h, iterate_frobSymm_mul, map_mul, untilt_iterate_epsPow,
    MulMemClass.coe_mul, SubmonoidClass.coe_pow]

omit [Fact p.Prime] in

set_option maxHeartbeats 1600000 in

end Contradiction

end GroundTheory.PAdicHodge
