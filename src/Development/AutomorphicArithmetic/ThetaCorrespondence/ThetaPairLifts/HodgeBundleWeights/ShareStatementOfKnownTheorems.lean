module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulComponentDegreeLeDimension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentImageDegreeBetweenOfProportionalityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRatiosGenerateAtFlagSpaceGenericPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMapBirationalOfCuspFormsGenerate
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShareStatementOfKnownTheorems
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CompactificationTopChernEqVolume
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsWeightHodgeBundleGenerated
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleIsNefIsBigOfWeight
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.JetRankComplexLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityPrincipleCompactification
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulComponentDegreeLeDimensionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

theorem _root_.GlobalTheory.T.choose_mul_componentDegree_le_dimension : Quoted → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (X : GlobalTheory.FlagMod.FlagCover Y) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : CompHS.WtPar Dw) (R : CompHS.Choice X Z U P) (ω : CompHS.CanId R.toModif) (x : ℝ) (D : Formalism.BasicNotions.D7) (V : (c.F →+* ℂ) → Formalism.BasicNotions.TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : CompHS.Ready R ω x V dict) (f₁ : CompHS.CuspFrame Z U x V dict P.u₁) (f₂ : CompHS.CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : CompHS.Consts), IsNef c.F (h.data f₁ f₂ th k).LA → IsBig c.F (h.data f₁ f₂ th k).LA → (h.data f₁ f₂ th k).Birational → (P.T - 1).choose (CompHt.dimFlag Dw) * CompHt.compDeg U Z (AllWt.wtOf Dw P.u₁ 0) ≤ Module.finrank c.F (AllWt.cuspOn U Z (AllWt.wtOf Dw (P.wt P.T) 0)) := by
  first | exact @GlobalTheory.HSCore.CompShare.choose_mul_compDeg_le | exact GlobalTheory.HSCore.CompShare.choose_mul_compDeg_le | (intros; apply GlobalTheory.HSCore.CompShare.choose_mul_compDeg_le <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseMulOneSubLeChoose

section

@[expose] public section

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem choose_mul_one_sub_le_choose (N M D : ℕ) (x : ℝ) (hx : 0 ≤ x) (hDM : D ≤ M) (hMN : M ≤ N)
    (h : (N : ℝ) - M ≤ x * ((N : ℝ) - D + 1)) :
    ∀ k ≤ D, ((N.choose k : ℕ) : ℝ) * (1 - k * x) ≤ ((M.choose k : ℕ) : ℝ) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have hkD : k ≤ D := by omega
    have ih' := ih hkD
    have hkM : k ≤ M := by omega
    have hkN : k ≤ N := by omega
    have eN : ((N.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) := by
      have h := Nat.choose_succ_right_eq N k
      rw [← Nat.cast_sub hkN]
      exact_mod_cast h
    have eM : ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) := by
      have h := Nat.choose_succ_right_eq M k
      rw [← Nat.cast_sub hkM]
      exact_mod_cast h
    have hk1 : (k : ℝ) + 1 ≤ D := by exact_mod_cast hk
    have hMN' : (M : ℝ) ≤ N := by exact_mod_cast hMN
    have hkM' : (k : ℝ) ≤ M := by exact_mod_cast hkM
    have hA : (0 : ℝ) ≤ ((N.choose k : ℕ) : ℝ) := by positivity
    have hpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity

    have hbr : (0 : ℝ) ≤ x * ((N : ℝ) - k) + x * k * ((N : ℝ) - M) - ((N : ℝ) - M) := by
      have h1 : x * ((N : ℝ) - D + 1) ≤ x * ((N : ℝ) - k) := by
        apply mul_le_mul_of_nonneg_left _ hx
        linarith
      have h2 : 0 ≤ x * k * ((N : ℝ) - M) := by
        have : (0 : ℝ) ≤ (N : ℝ) - M := by linarith
        positivity
      linarith
    have hstep : ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) * (1 - ((k : ℝ) + 1) * x)
        ≤ ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) := by
      have h3 : ((N.choose k : ℕ) : ℝ) * (1 - k * x) * ((M : ℝ) - k)
          ≤ ((M.choose k : ℕ) : ℝ) * ((M : ℝ) - k) :=
        mul_le_mul_of_nonneg_right ih' (by linarith)
      have h4 := mul_nonneg hA hbr
      nlinarith [h3, h4]
    have goal' : ((N.choose (k + 1) : ℕ) : ℝ) * (1 - ((k : ℝ) + 1) * x) * ((k : ℝ) + 1)
        ≤ ((M.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) := by
      rw [eM]
      calc ((N.choose (k + 1) : ℕ) : ℝ) * (1 - ((k : ℝ) + 1) * x) * ((k : ℝ) + 1)
          = ((N.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) * (1 - ((k : ℝ) + 1) * x) := by ring
        _ = ((N.choose k : ℕ) : ℝ) * ((N : ℝ) - k) * (1 - ((k : ℝ) + 1) * x) := by rw [eN]
        _ ≤ _ := hstep
    push_cast
    exact le_of_mul_le_mul_right goal' hpos

theorem share_bound_of_jet_count :
    ∀ (D T a : ℕ) (ρ δ d : ℝ), 2 ≤ D → D + 1 ≤ T → 0 ≤ ρ → ρ ≤ 1 / 2 → T + D + 3 ≤ a → (a : ℝ) ≤ ((T : ℝ) + D + 3) / (1 - ρ) → 0 ≤ δ → 0 ≤ d → d ≤ (((a + D).choose D : ℕ) : ℝ) * δ → (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := by
  intro D T a ρ δ d hD hDT hρ0 hρ hTa ha hδ hd0 hd
  have hT1 : 1 ≤ T := by omega
  have hT : (0 : ℝ) < T := by
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT1
    linarith
  have hTr : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
    rw [Nat.cast_sub hT1]
    simp
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hTa' : (T : ℝ) + D + 3 ≤ a := by exact_mod_cast hTa
  have hxnn : 0 ≤ 4 * (D : ℝ) / T + ρ := by positivity

  have key := choose_mul_one_sub_le_choose (a + D) (T - 1) D (4 * (D : ℝ) / T + ρ) hxnn
    (by omega) (by omega) (by
      push_cast
      rw [hTr]
      have h1ρ : (0 : ℝ) < 1 - ρ := by linarith
      have hamul : (a : ℝ) * (1 - ρ) ≤ (T : ℝ) + D + 3 := (le_div_iff₀ h1ρ).mp ha
      have h4 : 4 * (D : ℝ) ≤ 4 * (D : ℝ) / T * ((a : ℝ) + 1) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hT]
        have : (0 : ℝ) ≤ 4 * D := by positivity
        nlinarith
      nlinarith [h4, hamul, hρ0, hD2]) D le_rfl
  have hc : 1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ) ≤ 1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ) := by
    have e : (D : ℝ) * (4 * (D : ℝ) / T + ρ) = 4 * ((D : ℝ) ^ 2 / T) + D * ρ := by ring
    have h1 : 0 ≤ (D : ℝ) ^ 2 / T := by positivity
    have h2 : 0 ≤ (D : ℝ) * ρ := by positivity
    rw [e]
    linarith
  have hB : (0 : ℝ) ≤ (((a + D).choose D : ℕ) : ℝ) * δ := by positivity
  have hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := by positivity
  rcases le_or_gt (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) 0 with h | h
  · have : (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hd0
    linarith
  · calc (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * d
        ≤ (1 - 7 * ((D : ℝ) ^ 2 / T + D * ρ)) * ((((a + D).choose D : ℕ) : ℝ) * δ) :=
          mul_le_mul_of_nonneg_left hd h.le
      _ ≤ (1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ)) * ((((a + D).choose D : ℕ) : ℝ) * δ) :=
          mul_le_mul_of_nonneg_right hc hB
      _ = ((((a + D).choose D : ℕ) : ℝ) * (1 - (D : ℝ) * (4 * (D : ℝ) / T + ρ))) * δ := by ring
      _ ≤ (((T - 1).choose D : ℕ) : ℝ) * δ := mul_le_mul_of_nonneg_right key hδ

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSamuelMapBirationalOfCuspFormsGenerateStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0

theorem _root_.GlobalTheory.T.hilbertSamuel_map_birational_of_cuspForms_generate : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (P : WtPar Dw) (R : Choice X Z U P) (ω : CanId R.toModif) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → TH.HSp D) (dict : ∀ σ, Formalism.L2.Theta.GA D (V σ) → Σ k, FD.Frame ((U σ).X k).Ψ r) (h : Ready R ω x V dict) (f₁ : CuspFrame Z U x V dict P.u₁) (f₂ : CuspFrame Z U x V dict P.u₂) (th : R.L.Sec) (k : Consts), RatGen X Z U P.u₁ → (h.geo f₁ f₂ th k).Birational := by
  first | exact @GlobalTheory.HSApp.birational_of_ratGen | exact GlobalTheory.HSApp.birational_of_ratGen | (intros; apply GlobalTheory.HSApp.birational_of_ratGen <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShareStatementOfKnownTheorems

section

@[expose] public section

section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.CovTop.ShareRowsNef
section Weights
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
end Weights
theorem nef_share_lower_bound (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hSI : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS)
    (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted) (hSL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2) (hj : InR D j)
    (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hbir : BirOn Y.U Z (wtOf _ P.u₁ 0)) :
    (((P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) : ℝ) * Y.dg P.u₁ Z ≤ Y.rkC (P.wt P.T) Z := by
  have hP1 := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨g1, g2, g3⟩ := gapGe_of_wtBig hB
  have good : ∀ la, GapGe 1 la → _ := fun la h =>
    _root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hf hj Y e o hY la (antitone_of_gapGe hp hq h).1 (antitone_of_gapGe hp hq h).2
  obtain ⟨TF, R, ω, h⟩ := _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated hP1 hG hQ hP.q15 hP.q16 hSI hKS.toroidalChartsForFan hSL D T.toCore j Y e o hY hf Z P hB fun i _ => (good _ (g3 i)).1
  obtain ⟨f₁⟩ := nonempty_cuspFrame ((good _ g1).2 Z)
  obtain ⟨f₂⟩ := nonempty_cuspFrame ((good _ g2).2 Z)
  let k : CompHS.Consts := ⟨1, 1, 1, 1, 1, le_rfl, le_rfl, le_rfl⟩
  let th : R.L.Sec := GlobalTheory.CompHS.toSec (R.Δ₁.lift 0)
  have hA := _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight hP1 hQ.nef hSI hKS.toroidalChartsForFan hSL _ _ _ _ _ _ TF Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k hY.geo hB
  have a3 := GlobalTheory.T.hilbertSamuel_map_birational_of_cuspForms_generate TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k (GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hbir)
  obtain ⟨a1, a2⟩ := hA
  have key := GlobalTheory.T.choose_mul_componentDegree_le_dimension hQ _ _ _ _ _ _ _ _ Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k a1 a2 a3
  have hr : rankOn Y.U Z (wtOf _ (P.wt P.T) 0) = Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
    rw [rankOn, Formalism.HN.rkK, ((good _ (g3 P.T)).2 Z).2.2, finrank_top]
  rw [← hr] at key
  exact_mod_cast key
theorem nef_share_upper_bound (hX : GlobalTheory.CovTop.HypothesesX) (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hSI : GlobalTheory.Published.SiegelToroidalIntegral) (hKS : GlobalTheory.Published.ToroidalForFanKS) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSL : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2) (hj : InR D j)
    (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (hs : ∀ τ, StrictAnti (P.u₁ τ) ∧ StrictAnti (CompHt.uPrime _ P.u₁ τ))
    (hbir : ∀ Z, BirOn Y.U Z (wtOf _ P.u₁ 0))
    (hV : ∀ Z, ValMult Y.U Z (wtOf _ P.u₁ 0) (wtOf _ (CompHt.uPrime _ P.u₁) 0))
    (h0 : 0 ≤ CompHt.rhoB _ P.u₁) (h1 : CompHt.rhoB _ P.u₁ ≤ 1 / 2) (la : AllWt.Weight (T.Q.Dw j)) (hla : ∀ τ, Antitone (la τ))
    (hd : ∀ τ, Antitone (((P.T + CompHt.dimFlag (T.Q.Dw j) + 3 : ℕ) : ℤ) • P.u₁ τ - la τ))
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hδ : 0 < Y.dg P.u₁ Z) :
    (1 - 7 * ((CompHt.dimFlag (T.Q.Dw j) : ℝ) ^ 2 / P.T + CompHt.dimFlag (T.Q.Dw j) * CompHt.rhoB _ P.u₁)) * Y.rkC la Z ≤
      (((P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) : ℕ) : ℝ) * Y.dg P.u₁ Z := by
  have hD := GlobalTheory.CompHS.dimFlag_eq (T.Q.Dw j)
  have hg := hB.gaps
  have hT1 := hB.le_T
  have hD2 := two_le_dimFlag hp hq hf
  rw [← hD] at hg hT1 hD2
  have hle := (GlobalTheory.T.componentImageDegree_between_of_proportionality _ _ _ _ _ _ _ Y.U hY.unf (_root_.GlobalTheory.T.proportionality_principle_compactification hP hSI hKS hSL D T hT j hp hq hf hj Y e o hY).1
    (_root_.GlobalTheory.T.compactification_top_chern_eq_volume hP hSI hKS hSL D T hT j hp hq hf hj Y e o hY) P.u₁ (fun τ => (hs τ).1) (fun τ => (hs τ).2) hbir hV Z Z).1
  rw [CompHt.delPrime_eq _ _ (CompHt.vdm_pos fun τ => (hs τ).1).ne'] at hle
  set ρ := CompHt.rhoB _ P.u₁ with hρ
  set n := P.T + CompHt.dimFlag (T.Q.Dw j) + 3 with hn
  have hρ1 : 0 < 1 - ρ := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ha1 : ((⌊(n : ℝ) / (1 - ρ)⌋₊ : ℕ) : ℝ) ≤ n / (1 - ρ) := Nat.floor_le (by positivity)
  have ha2 : (n : ℝ) / (1 - ρ) < (⌊(n : ℝ) / (1 - ρ)⌋₊ : ℕ) + 1 := Nat.lt_floor_add_one _
  have ha3 : n ≤ ⌊(n : ℝ) / (1 - ρ)⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hρ1]; nlinarith)
  have hjet := _root_.GlobalTheory.T.jet_rank_complex_le hX hP hSI hKS hG hQ hSL D T hT j hp hq hf hj Y e o hY Z P.u₁ la n ⌊(n : ℝ) / (1 - ρ)⌋₊ hg hla hd (by
    have h2 : CompHt.topDeg Y.U Z P.u₁ ≤ Y.dg P.u₁ Z / (1 - ρ) := by
      rw [le_div_iff₀ hρ1, mul_comm]; exact hle
    calc (n : ℝ) * CompHt.topDeg Y.U Z P.u₁ ≤ n * (Y.dg P.u₁ Z / (1 - ρ)) := mul_le_mul_of_nonneg_left h2 hn0
      _ = n / (1 - ρ) * Y.dg P.u₁ Z := by ring
      _ < _ := mul_lt_mul_of_pos_right ha2 hδ)
  refine GlobalTheory.share_bound_of_jet_count _ _ _ ρ _ _ hD2 hT1 h0 h1 ha3 ?_ hδ.le (Nat.cast_nonneg _) hjet
  rw [hn] at ha1 ⊢
  push_cast at ha1 ⊢
  exact ha1
end GlobalTheory.CovTop.ShareRowsNef
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
end
end
end
