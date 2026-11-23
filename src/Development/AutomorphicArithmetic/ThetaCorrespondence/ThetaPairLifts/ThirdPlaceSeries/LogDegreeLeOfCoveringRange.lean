module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BinomialFlagDimensionDegreeBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneOfGapNonneg
public import Formalism.HarderNarasimhan.StatementPl
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteInvLeft
import Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtArith
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralCuspSlopePowerBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizesOfCover
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsAtPoint
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtBigRun
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFinrankCuspFormsLe

section

@[expose] public section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop.DimLogTop

theorem log_size_le (f r L kap S : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hk0 : 0 ≤ kap)
    (hk : Real.log kap ≤ 2 * L) (hfr : Real.log (f * r) ≤ L) (hS0 : 0 ≤ S)
    (hS : S ≤ (f * r * L) ^ 2 * kap + 6 * f * r ^ 2) : Real.log S ≤ 20 * L := by
  rcases hS0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; linarith
  have hfr0 : 0 < f * r := by positivity
  have e1 : f * r ≤ Real.exp L := (Real.log_le_iff_le_exp hfr0).1 hfr
  have e2 : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have e3 : kap ≤ Real.exp (2 * L) := by
    rcases hk0.eq_or_lt with h0 | h0
    · rw [← h0]; exact (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp h0).1 hk
  have e4 : (7 : ℝ) ≤ Real.exp (6 * L) := by linarith [Real.add_one_le_exp (6 * L)]
  have hE : Real.exp (6 * L) = Real.exp L ^ 2 * Real.exp L ^ 2 * Real.exp (2 * L) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  have hE2 : Real.exp L ^ 2 ≤ Real.exp (6 * L) := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; linarith)
  have a1 : (f * r * L) ^ 2 * kap ≤ Real.exp (6 * L) := by
    rw [hE, mul_pow]
    have : (f * r) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ hfr0.le e1 2
    have : L ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ (by linarith) e2 2
    gcongr
  have a2 : 6 * f * r ^ 2 ≤ 6 * Real.exp (6 * L) := by
    have : f * r ^ 2 ≤ (f * r) ^ 2 := by nlinarith
    have : (f * r) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ hfr0.le e1 2
    nlinarith
  have a3 : S ≤ Real.exp (12 * L) := by
    have : Real.exp (12 * L) = Real.exp (6 * L) * Real.exp (6 * L) := by rw [← Real.exp_add]; ring_nf
    rw [this]
    have := Real.exp_pos (6 * L)
    nlinarith
  have := (Real.log_le_iff_le_exp h).2 a3
  linarith

theorem cube_le (Cb L Zb : ℝ) (hL : Cb ≤ L) (hL1 : 1 ≤ L) (hZ : L ≤ Zb) : Cb * Zb ^ 3 ≤ Zb ^ 12 := by
  have h1 : 1 ≤ Zb := hL1.trans hZ
  have h9 : Zb ≤ Zb ^ 9 := le_self_pow₀ h1 (by norm_num)
  have h3 : 0 ≤ Zb ^ 3 := by positivity
  calc Cb * Zb ^ 3 ≤ Zb ^ 9 * Zb ^ 3 := mul_le_mul_of_nonneg_right (by linarith) h3
    _ = Zb ^ 12 := by ring

theorem rkK_eq_finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (L : Submodule (𝓞 K) V) (h : Submodule.span K (L : Set V) = ⊤) :
    Formalism.HN.rkK L = Module.finrank K V := by
  unfold Formalism.HN.rkK
  rw [h, finrank_top]

end GlobalTheory.CovTop.DimLogTop

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LogTopDimensionBoundCovering

section

@[expose] public section



section
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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.DimLogTop
theorem log_top_dimension_le_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) : ℝ) ≤ PP := by
  intro hP hSz
  have hBex := _root_.UpperTheory.Lit.Tam.tamagawa_number_formula hP
  obtain ⟨Cb, -, hB⟩ := hBex
  have hG := _root_.GlobalTheory.CovTop.GoodDom.covering_regular_at_domain hP
  have hQ := _root_.GlobalTheory.QuoWt.weights_at_point_alt hSz
  have hS := _root_.GlobalTheory.CovTop.CovSz.size_rows_alt hSz
  have hW := _root_.GlobalTheory.HSApp.wtBig_run_alt
  refine Closed.imp (Closed.and (Closed.and hQ hS) hW) ?_
  intro eps Fm CH heps hh
  obtain ⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩ := hh
  refine ⟨0, le_rfl, max (max (max x1 x2) x3) ((max Cb 1) ^ eps⁻¹), ?_⟩
  intro x hx hle ι p hp i hi Y hY Z
  have hle1 : max (max x1 x2) x3 ≤ x := (le_max_left _ _).trans hle
  have hq := h1 x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle1)) ι p hp i hi
  have hs := h2 x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle1)) ι p hp i hi Y hY
  have hwb := h3 x hx ((le_max_right _ _).trans hle1) ι p hp i hi
  obtain ⟨hp1, hq1, hE, -, hstr, -, -⟩ := hq
  obtain ⟨hLJ, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, -, hkap, hZ12, -, -, -, -, hwt⟩ := hs
  set PP := (Fm.parT x hx ι).PP with hPP
  have hx1 : Fm.x1 < x := hx
  have hLx : (Fm.L x ι).sc.L = x ^ eps := by
    unfold Scale.L; rw [Fm.L_x x ι hx1, Fm.L_eps x ι]
  have hLC : max Cb 1 ≤ (Fm.L x ι).sc.L := by
    rw [hLx]
    have h0 : (0 : ℝ) ≤ (max Cb 1) ^ eps⁻¹ := Real.rpow_nonneg (by positivity) _
    calc max Cb 1 = ((max Cb 1) ^ eps⁻¹) ^ eps := (Real.rpow_inv_rpow (by positivity) heps.ne').symm
      _ ≤ x ^ eps := Real.rpow_le_rpow h0 ((le_max_right _ _).trans hle) heps.le
  have hT2 : 2 ≤ GlobalTheory.FlagTan.dimFlag (dat p i) + lenT p i PP := by
    have hT1 := hwb.le_T
    have hD1 := hwb.one_le
    change 1 ≤ GlobalTheory.FlagTan.dimFlag (dat p i) at hD1
    change GlobalTheory.FlagTan.dimFlag (dat p i) + 1 ≤ lenT p i PP at hT1
    omega
  have hanti := GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i)
    (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)) (lenT p i PP)
    (fun τ => (hstr τ).1) hT2 hp1 hq1
  have hsum := hwt (lenT p i PP) le_rfl
  have hsize : Real.log (∑ τ, ∑ k, |(((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ :
      WtPar (dat p i)).wt (lenT p i PP)) τ k : ℝ)|) ≤ 20 * (Fm.L x ι).sc.L := by
    refine GlobalTheory.CovTop.DimLogTop.log_size_le ((Fm.D x ι).R.f : ℝ) ((Fm.D x ι).R.r : ℝ) (Fm.L x ι).sc.L (kap p i) _
      (by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.f)) (by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.r))
      hL1 (sizeK_nonneg _ _ _) hkap hfr (by positivity) ?_
    have : (0 : ℝ) ≤ 6 * ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) ^ 2 := by positivity
    have e : zBase (Fm.L x ι) = ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) * (Fm.L x ι).sc.L := by unfold zBase; ring
    rw [← e]; linarith
  have hBr := (hB (Fm.D x ι) p.T hLJ ((i : ℕ) + 1) hp1 hq1 hE hInR Y (expL (Fm.L x ι).sc.L)
    (391 * zBase (Fm.L x ι) ^ 2) hY.1 (Fm.L x ι).sc.L hL1 hM hfs hfr (by unfold zBase; exact le_rfl)
    _ (fun τ => (hanti τ).1) hsize Z).2.2
  have hGd := (hG (Fm.D x ι) p.T hLJ ((i : ℕ) + 1) hp1 hq1 hE hInR Y (expL (Fm.L x ι).sc.L)
    (391 * zBase (Fm.L x ι) ^ 2) hY.1 _ (fun τ => (hanti τ).1) (fun τ => (hanti τ).2)).2 Z
  have hrk : Y.rkC ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ :
      WtPar (dat p i)).wt (lenT p i PP)) Z = (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i)
      ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt
      (lenT p i PP)) 0)) : ℝ) := by
    show ((rankOn Y.U Z _ : ℕ) : ℝ) = _
    unfold rankOn
    rw [rkK_eq_finrank_of_span_top _ hGd.2.2]
  rw [← hrk]
  have hfr1 : (1 : ℝ) ≤ ((Fm.D x ι).R.f : ℝ) * ((Fm.D x ι).R.r : ℝ) := by
    have : 1 ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := Nat.one_le_iff_ne_zero.2 (by positivity)
    exact_mod_cast this
  have hLZ : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    unfold zBase; nlinarith
  have hcube := GlobalTheory.CovTop.DimLogTop.cube_le Cb (Fm.L x ι).sc.L (zBase (Fm.L x ι)) ((le_max_left _ _).trans hLC) hL1 hLZ
  have h2 : Cb * (((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (Fm.L x ι).sc.L) ^ 3 = Cb * zBase (Fm.L x ι) ^ 3 := by
    unfold zBase; ring
  linarith
end GlobalTheory.CovTop.DimLogTop
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

theorem _root_.GlobalTheory.T.log_finrank_cuspOn_le : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) : ℝ) ≤ PP := by
  first | exact @_root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le_alt | exact _root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le_alt | (intros; apply _root_.GlobalTheory.CovTop.DimLogTop.log_top_dimension_le_alt <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LogDegreeLeOfCoveringRange

section

@[expose] public section



section
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
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.DgLog
end GlobalTheory.CovTop.DgLog
namespace GlobalTheory.CovTop.DgLog
end GlobalTheory.CovTop.DgLog
namespace GlobalTheory.CovTop.DgLog
theorem log_degree_le_of_covering_range_alt : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
  intro hX hP hG hQ hSg hFan hSA hDG hSz hFD
  refine Closed.imp (Closed.and (Closed.and (_root_.GlobalTheory.T.binomial_flag_dimension_degree_bound_alt_alt hX hP hG hQ hSg hFan hSA hDG hSz hFD) (_root_.GlobalTheory.T.log_finrank_cuspOn_le hP hSz)) hSz) ?_
  intro eps Fm CH heps hh
  obtain ⟨⟨⟨C1, -, x1, h1⟩, ⟨C2, -, x2, h2⟩⟩, ⟨C3, -, x3, h3⟩⟩ := hh
  refine ⟨0, le_rfl, max (max x1 x2) x3, ?_⟩
  intro x hx hle ι p hp i hi Y hY Z
  have hA := h1 x hx ((le_max_left _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY Z
  have hB := h2 x hx ((le_max_right _ _).trans ((le_max_left _ _).trans hle)) ι p hp i hi Y hY Z
  have hz := h3 x hx ((le_max_right _ _).trans hle) ι p hp i
  set PP := (Fm.parT x hx ι).PP with hPP
  obtain ⟨⟨u1, hu1⟩, hqq⟩ := hz.2.2.2.2.2.2 hi
  have hT := (hqq _ hu1).1
  have hbin : 1 ≤ (lenT p i PP - 1).choose (GlobalTheory.CompHt.dimFlag (dat p i)) := Nat.choose_pos (by omega)
  have hle' : GlobalTheory.CompHt.compDeg Y.U Z (wtOf (dat p i) (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ 0) ≤
      Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) :=
    (Nat.le_mul_of_pos_left _ hbin).trans hA
  have hdg0 : (0 : ℝ) ≤ Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z := Nat.cast_nonneg _
  rcases hdg0.eq_or_lt with h0 | h0
  · rw [← h0, Real.log_zero]
    exact (Real.log_natCast_nonneg _).trans hB
  · have h1 : Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z ≤ (Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf (dat p i) ((⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).wt (lenT p i PP)) 0)) : ℝ) := by
      exact_mod_cast hle'
    exact (Real.log_le_log h0 h1).trans hB
end GlobalTheory.CovTop.DgLog
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

theorem _root_.GlobalTheory.T.log_dg_u1_le_of_flatDeg : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.CoversCondition fun Fm x _ ι p i Y PP _ => ∀ Z, Real.log (Y.dg (⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ : WtPar (dat p i)).u₁ Z) ≤ PP := by
  first | exact @_root_.GlobalTheory.CovTop.DgLog.log_degree_le_of_covering_range_alt | exact _root_.GlobalTheory.CovTop.DgLog.log_degree_le_of_covering_range_alt | (intros; apply _root_.GlobalTheory.CovTop.DgLog.log_degree_le_of_covering_range_alt <;> assumption)
end
end
end
end
