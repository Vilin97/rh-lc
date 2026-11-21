module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_stabilizer_exists : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.StabEx := by
  first | exact @GlobalTheory.StabHaar.stabEx | exact GlobalTheory.StabHaar.stabEx | (intros; apply GlobalTheory.StabHaar.stabEx <;> assumption)
