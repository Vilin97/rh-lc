module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Mathlib
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.BesselOrbitConvolutions.BesselNonvanishingL2
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.UniformCoefficientBounds.FromDS
public import CompanionTheory.AutomorphicTheory.RankOneEstimates.RankOne
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecLowPf

@[expose] public section

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.Upq.BesselFunctionalConstruction

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Formalism.FourierDecayAlt.P.CutBP.Jmu

theorem inputs_holds : Inputs :=
  ⟨Formalism.L2.SG.BesselDiscreteSeries.decLow, Coef.decay_infinite_range, CompanionTheory.D.gk.admitted.k_finite_smooth, trivial⟩

section One

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {h : ℝ}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mx k r → (H →L[ℂ] H)} {w0 : H} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [CompleteSpace Wp] [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
  {π : Mx k r → (Wp →L[ℂ] Wp)} {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)}

end One

end CompanionTheory.D.Upq.BesselFunctionalConstruction

end
