import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsAtlas
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ProjectiveLineMultihomogClassify
import ReciprocityTheory.AnalyticForms.RegularLocalRings.IsOpenAlt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial MeasureTheory Topology
open scoped ContDiff
open GroundTheory.Heights₂.Heights.NumbersDVR (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver IsMultiHomogIdeal IsMultiHomog IsRelevant IsMultiProjPrime
  divCycle intNum)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsSNC HoloMap mInt MIntegrable
  logNormSec)

abbrev HLine {K : Type} [Fintype K] (ι : K → Type) := ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι

section Objects

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev MCone (ι : K → Type) := (Σ k, ι k) → ℂ

def logH (L : HLine ι) : MCone ι → ℝ := fun z => Real.log (L.h z)

variable (ι) in

structure Res (P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℂ ι)) (e : ℕ) where

  D : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℂ ι)
  homog : IsMultiHomogIdeal D
  not_le : ¬ D ≤ P

  R : ReciprocityTheory.AnForm.R.AlgRes ι P D e

namespace Res

variable {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRingOver ℂ ι)} {e : ℕ} (R : Res ι P e)

end Res

open Classical in

def IsProjVarQ (P0 : Ideal (MRing ι ℚ)) (e : ℕ) : Prop :=
  IsMultiProjPrime P0 ∧ ringKrullDim (MRing ι ℚ ⧸ P0) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)

end Objects

section Ring

variable {K : Type} {ι : K → Type}

end Ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
