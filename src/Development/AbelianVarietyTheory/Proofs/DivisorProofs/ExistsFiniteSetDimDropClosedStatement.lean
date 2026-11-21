module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteSetDimDropClosed
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.LatticeTransfer
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_set_dim_drop_closed : ∀ {T : Type} [TopologicalSpace T] [TopologicalSpace.NoetherianSpace T] [QuasiSober T] (Z : Set T), IsClosed Z → ∃ S : Set T, S.Finite ∧ ∀ C : Set T, IsClosed C → Disjoint S C → topologicalKrullDim (Z ∩ C : Set T) + 1 ≤ topologicalKrullDim Z := by
  first | exact @GlobalTheory.exists_finite_topologicalKrullDim_inter_add_one_le | exact GlobalTheory.exists_finite_topologicalKrullDim_inter_add_one_le | (intros; apply GlobalTheory.exists_finite_topologicalKrullDim_inter_add_one_le <;> assumption)
