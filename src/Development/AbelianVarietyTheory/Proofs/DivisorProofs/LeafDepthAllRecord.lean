module

public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthCond
public import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
public import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.AllGoodPrimeDepthDataExistProofStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthLeafGoodPrimesOfPointDataStatement
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudSizesBetweenZeroAndTwiceB
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DegreeWeightKappaLePageBound
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulRowsScaledWeightLeKappaRows
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RunDepthDataLawsAndFiniteLocalDepth
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
public import Formalism.LocalToGlobal.ProjectiveLattices.DepLaws
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTie
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepth2Run
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepthLevelRun
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ColengthBoundSplitPlaceChart
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HodgeTateInclusionChartCharacters
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.UnramifiedCompanionChartCharacters
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimesOfChartForm

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory

theorem leafDepthGood_of_chartForm : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  intro hUp
  obtain ⟨C0, h⟩ := GlobalTheory.T.depthLeaf_goodPrimes_of_point_data
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T hT EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm hR
  exact h D L Pm Tp hK T hT EX K Bs Df S P oc O ι Nm hR
    (fun j => GlobalTheory.T.allGoodPrimeDepthDataExist_proof hUp _ _ _ _ (T.Q.Xo (ι j)) T.Q.c)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimesOfChartFormStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem _root_.GlobalTheory.T.depthTable_goodPrimes_of_chartForm : (∀ (p : ℕ) [Fact p.Prime], ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF.UpFSt p) → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  first | exact @GlobalTheory.leafDepthGood_of_chartForm | exact GlobalTheory.leafDepthGood_of_chartForm | (intros; apply GlobalTheory.leafDepthGood_of_chartForm <;> assumption)
end
end

-- Source module: Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTieSat

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Indef.Tree.DepthTie

open NumberField IsDedekindDomain
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.DIV Formalism.BasicNotions Formalism.L2.Indef.Tree.DepthCond

section Sat

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
  {Dw : ℕ → Datum H} (Xo : ∀ j, Moduli (Dw j) l) (c : Coeff l) [StarRing (𝓞 E)] (Dd : DepData E)
variable {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 c.F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 c.F) (𝓞 K)] [Algebra (𝓞 E) K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (O : OnObj S P oc) (ι : Bs.J → ℕ)

end Sat

section CoreSat

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} (T : Core D) [StarRing (𝓞 D.host.E)] (Dd : DepData D.host.E)
variable {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K]
variable {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  (O : OnObj S P oc) (ι : Bs.J → ℕ)

theorem leafDepthRam_core_sat (N : IndefNum Bs) (Nd : NumDatum) (hL : LawsPi T Dd) (hp : T.Q.Pins)
    (hι : ∀ j, InR D (ι j))
    (hE : ∀ v j, O.E v j = EAt (Xo := T.Q.Xo (ι j)) (c := T.Q.c) (LL := K) Dd v (ι j))
    (hσ : ∀ v j, O.σ v j = sigAt (Dw := T.Q.Dw (ι j)) (H := T.Q.H) (LL := K) Dd (ι j))
    (hT : O.T = ((Dd.Q.T : ℕ) : ℝ))
    (hpr : O.g1 = Dd.Q.g1 ∧ O.g2 = Dd.Q.g2 ∧ O.q1 = Dd.Q.q1 ∧ O.dd = Dd.Q.dd ∧ O.sm = Dd.Q.sm)
    (hstar : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) (hEx : ∀ j, IntChartEx (T.Q.Xo (ι j)) T.Q.c)
    (hPg : LeafPage O) (hSz : LeafSizes O) (tF : ContentEqualsDatumContent N Nd ι) (tP : TiePrimes O Nd) (tK : TieFK O Nd)
    (Dk : Bs.J → ℝ) (C₀ : ℝ) (iD : DegScale O (fun j => (DF (T.Q.Dw (ι j)) (Dd.aL (ι j)) : ℝ)) Dk)
    (iW : DegWeight O Dk C₀) (iP : PageRam O C₀) (iB : WtRam O Nd ι) : LeafDepthRam N O :=
  leafDepthRam_core T Dd O ι N Nd hL hp hι hE hσ hT hpr hstar hEx
    (fun j => Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds (T.Q.Xo (ι j)) T.Q.c) hPg hSz tF tP tK Dk C₀ iD iW iP iB

end CoreSat

section NuFin

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

end NuFin

end Formalism.L2.Indef.Tree.DepthTie
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.KLeSubOneOfLt

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem k_le_sub_one_of_lt (R : Ranks) (l : ℕ) (h : 4 * R.t * R.r + 1 < l) : (R.k : ℝ) ≤ (l : ℝ) - 1 := by
  have h1 : R.k ≤ R.r := by have := R.two_le_m; unfold Ranks.r; omega
  have h2 : 1 ≤ R.t := by have := R.three_m_lt_t; omega
  have h3 : R.r ≤ 4 * R.t * R.r := Nat.le_mul_of_pos_left _ (by omega)
  have h4 : R.k + 1 ≤ l := by omega
  have h5 : ((R.k + 1 : ℕ) : ℝ) ≤ (l : ℝ) := by exact_mod_cast h4
  push_cast at h5
  linarith

theorem leafDepthRam_run : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → LeafDepthRam N O := by
  intro D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg hSz hx hb tF
  obtain ⟨hPi, hDep, -⟩ := laws_and_nuFinAt D L Pm Tp hK T EX hM hR.star_eq
  obtain ⟨-, hW⟩ := sizes_le_two_mul D L Pm hx hb
  refine DepthTie.leafDepthRam_core_sat T (depOf T EX Tp hK) O ι N (numOf D L) hPi hM.pins hR.inR hR.E_eq hR.σ_eq
    hR.T_eq ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ hR.star_eq (fun j => hDep.chartEx _ (hR.inR j)) hPg hSz tF
    ⟨hR.jets_eq_fact, hR.g2_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq, hR.sm_eq⟩ ⟨?_, hR.k_eq⟩ (fun j => (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)) 1 ?_ ?_ ?_ ?_
  · rw [hR.f_eq]
    show ((2 * D.R.n : ℕ) : ℝ) = 2 * ((D.R.n : ℕ) : ℝ)
    push_cast
    ring
  · intro j
    have h1 := (GlobalTheory.WeightExponents.weight_exponents D T.Q hM.pins (ι j) (hR.inR j) (lR Tp hK (ι j))).1
    have h2 := (mul_rows_lR_le_kaR D L Pm Tp hK (ι j) (plOf D (false, 0))).2.2
    show O.T * ((DF (T.Q.Dw (ι j)) (wtA (lR Tp hK (ι j))) : ℕ) : ℝ) ≤ (WeightAlgebra.DF (kaR Tp hK (ι j)) : ℝ)
    rw [h1, hR.T_eq]
    exact_mod_cast h2
  · intro j
    have h1 := (DF_kaR_le D L Pm Tp hK hx hb (ι j) (hR.inR j)).1
    unfold OnObj.sB OnObj.Se
    rw [one_mul, hR.k_eq, hR.wt_eq, hR.f_eq, hR.Sc_eq, hR.eta_eq]
    exact h1
  · unfold PageRam
    rw [one_mul, hR.k_eq, hR.cmQuadraticForm_eq_alternatingForm, hR.dd_eq]
    exact ⟨k_le_sub_one_of_lt D.R _ D.host.qd_big.1, k_le_sub_one_of_lt D.R _ D.host.qd_big.2⟩
  · intro j t
    obtain ⟨h1, h2, h3⟩ := hW (ι j) (hR.inR j)
    rw [h3, h3, hR.bp_eq]
    exact ⟨(h1 _).1, (h1 _).1, (min_le_left _ _).trans (h2 t)⟩

end GlobalTheory.RunDepth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeafDepthAllRun

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

theorem GlobalTheory.RunDepth.leafDepth_all_run : (∀ (p : ℕ) [Fact p.Prime], AvFSt p) → (∀ (p : ℕ) [Fact p.Prime], HTFSt p) → (∀ (p : ℕ) [Fact p.Prime], UpFSt p) → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D) (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (N : IndefNum Bs), LawsM T → RunTie T EX Tp hK O ι → LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ContentEqualsDatumContent N (numOf D L) ι → C0 ≤ oc.C → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → LeafDepthGood N O ∧ LeafDepthRam N O ∧ LeafDepth2 N O ∧ LeafDepthLevel N O := by
  intro hAv hHT hUp
  obtain ⟨C0, hG⟩ := GlobalTheory.T.depthTable_goodPrimes_of_chartForm hUp
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι N hM hR hPg hSz hx hb tF hC hn he
  exact ⟨hG D L Pm Tp hK T hM EX K Bs Df S P oc O ι N hR hC hPg hSz hn he hx hb tF,
    GlobalTheory.RunDepth.leafDepthRam_run D L Pm Tp hK T EX K Bs Df S P oc O ι N hM hR hPg hSz hx hb tF,
    GlobalTheory.RunDepth.leafDepth2_run hAv hHT D L Pm Tp hK T EX K Bs Df S P oc O ι N hM hR hPg hSz hx hb tF,
    GlobalTheory.RunDepth.leafDepthLevel_run D L Pm Tp hK T EX K Bs Df S P oc O ι N hM hR hPg hSz hx hb tF⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeafDepthAllRecord

section

@[expose] public section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Cx Formalism.IndefR.FWT Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.FormTies GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.BigOn.leafDepth_all_record : ∃ C0 : ℝ, ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie J R κ v₀) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (EX : ErrX D) (r : TwoRuns J G) (c : OnConst) (O : OnObj ((R.toCx F).data F.cr false) (Mir R) c), IsRec Tp hK EX F fw r O → ∀ N : IndefNum A.fam.base, LeafPage O → LeafSizes O → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → Formalism.L2.Indef.Tree.DepthCond.ContentEqualsDatumContent N (GlobalTheory.RunDepth.numOf D L) (fun j : Fin D.R.m => (j : ℕ) + 1) → C0 ≤ c.C → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → LeafDepthGood N O ∧ LeafDepthRam N O ∧ LeafDepth2 N O ∧ LeafDepthLevel N O := by
  obtain ⟨C0, h⟩ := GlobalTheory.RunDepth.leafDepth_all_run GlobalTheory.ChF.colength_bound_split_place_chart
    GlobalTheory.ChF.hodgeTate_inclusion_chart GlobalTheory.ChF.unramified_companion_chart_characters
  refine ⟨C0, ?_⟩
  intro D G _ _ Pl0 T0 A J _ R F κ v₀ fw L Pm Tp hK EX r c O hrec N hPg hSz hx hb tF hC hn he
  obtain ⟨st, hd⟩ := hrec.depth
  obtain ⟨hc, -⟩ := hrec.tied
  letI := st
  letI := hostAlg D
  exact h D L Pm Tp hK J.toCore EX D.what₂.LL _ _ _ _ c O _ N hc.toLawsM hd hPg hSz hx hb tF hC hn he
end
end
