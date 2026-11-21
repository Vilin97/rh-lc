import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FormsOver
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocStOfLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoTiedPGraft
import Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime
import Formalism.LocalToGlobal.LatticeGeometry.ShimuraSheafOfIndefiniteSubspace
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

abbrev JC (D : D7) : Type := ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

def JC.Pinned {D : D7} (jC : JC D) : Prop := ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)

abbrev KitT {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A) (jC : JC D) : Type 1 :=
  Kit s L (cxSt D.what₂.LL) jC ngTrue

abbrev KitClass (D : D7) : Type 1 :=
  ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D),
    KitT s L jC → (s.Comp → D.what₂.Tau → ℝ) → Prop

variable {D : D7}

namespace FamOver

variable {Q : KitClass D} {T : Top D} {h : LawsP T} {c : ℕ} (Φ : FamOver Q T h c)

end FamOver

end GlobalTheory.ShFam
