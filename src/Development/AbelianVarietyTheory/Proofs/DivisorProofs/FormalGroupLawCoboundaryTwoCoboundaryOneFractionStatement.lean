module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOneFraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cob2_cob1_eq_zero_of_isLaw :
    ∀ (B Q : Type) [CommRing B] [CommRing Q] [Algebra B Q] (d : ℕ)
      (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B),
      IsLaw μ → ∀ g : MvPowerSeries (Fin d) Q,
        cob2 (QLog.up (Q := Q) μ) (cob1 (QLog.up (Q := Q) μ) g) = 0 := by
  intro B Q _ _ _ d μ h g
  have hL : IsLaw (QLog.up (Q := Q) μ) := LawUp.isLaw_map (algebraMap B Q) h
  have hCob := (formalGroupLawCoboundaryTwo_coboundaryOne_alt Q d (QLog.up (Q := Q) μ)
    hL.const g).1
  rw [hCob, hL.assoc, sub_self]
