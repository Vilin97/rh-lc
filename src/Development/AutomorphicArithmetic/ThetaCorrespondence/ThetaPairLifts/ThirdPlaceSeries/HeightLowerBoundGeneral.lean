module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.VolumeEstimateHypotheses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftWeightNumerator
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ErrorBudgetCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BudgetOfSizeAndWeight
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsSectionBoundedByBergmanKernel
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsShortSectionCoverHeight
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalOfGrowthOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedWeightGapsBlockAndBar
import Mathlib.Algebra.Order.Star.Int
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ProportionalityPrincipleCompactification
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostN
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeightOfSteps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultCOfRefWStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RefinedSumWeightOfSizeLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZStatement

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BudgetAltAlt

section

@[expose] public section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace GlobalTheory.CovHt.BudgetPf
section Point
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem budget_alt : (∀ M, _root_.GlobalTheory.CovTop.HostNAlt M) → _root_.GlobalTheory.CovTop.LiftWeightNumerator → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition := fun hH hW _ =>
  Closed.imp (Closed.and (hH 1) hW) fun _ _ _ ⟨⟨_, _, h1⟩, ⟨_, _, h2⟩⟩ => by
    obtain ⟨x0, h⟩ := h1.and h2
    exact ⟨83400, by norm_num, x0, fun x hx hle ι p hp i hi Y hY u1 hq =>
      budgetAt p i ((h x hx hle ι p hp).1 i) ((h x hx hle ι p hp).2 i) hi Y hY u1 hq⟩
end GlobalTheory.CovHt.BudgetPf
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BudgetStatement

section

@[expose] public section



section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
theorem _root_.GlobalTheory.T.budget_of_hostN_of_liftWeight_of_size : (∀ M, _root_.GlobalTheory.CovTop.HostNAlt M) → _root_.GlobalTheory.CovTop.LiftWeightNumerator → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.ErrorBudgetCondition := by
  first | exact @_root_.GlobalTheory.CovHt.BudgetPf.budget_alt | exact _root_.GlobalTheory.CovHt.BudgetPf.budget_alt | (intros; apply _root_.GlobalTheory.CovHt.BudgetPf.budget_alt <;> assumption)
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricOfHyp

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

set_option autoImplicit false


noncomputable section

namespace GlobalTheory.CovHt.GeomBound

theorem strictAnti_of_step {N : ℕ} {f : Fin N → ℤ} (h : ∀ a b : Fin N, (b : ℕ) = a + 1 → f b < f a) : StrictAnti f := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [Fin.mk_lt_mk] at hab
  induction b with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h' | h'
    · exact (h ⟨n, by omega⟩ ⟨n + 1, hb⟩ rfl).trans (ih (by omega) h')
    · subst h'
      exact h ⟨a, ha⟩ ⟨a + 1, hb⟩ rfl

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem quo_gaps {PP A M : ℝ} (hN : HostNum D L PP A M) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (u1 : AllWt.Weight (dat p i)) (hu : Quo p i PP u1) :
    ∀ τ (a b : Fin ((dat p i).p + (dat p i).q)), (b : ℕ) = a + 1 →
      (((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℤ) ≤ u1 τ a - u1 τ b := by
  obtain ⟨hsig1, hsig2, hsigr⟩ := hw.sig
  obtain ⟨h0, S, eta, -, -, -, h4T, -, hHyp⟩ := hw.hyp hi
  have hdiv := (quo_iff p i PP h0 S eta u1).1 hu
  have G := GlobalTheory.MeanTop.divided_gaps _ _ _ (hHyp u1) hdiv
  simp only [wtsAt] at G
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hp1 : 1 ≤ (dat p i).p := by rw [hsig1]; simp only [Ranks.sigW]; omega
  have hq1 : 1 ≤ (dat p i).q := by rw [hsig2]; simp only [Ranks.sigW]; omega
  have hr2 : 2 ≤ D.R.r := by omega
  have hD1 : 1 ≤ dimFlag (dat p i) := by
    rw [hw.dim]
    exact Nat.mul_pos (by have := hN.f8; omega) (Nat.choose_pos hr2)

  have hz : (4 : ℝ) ≤ zBase L := by
    unfold zBase
    have c1 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hN.f8
    have c2 : (2 : ℝ) ≤ D.R.r := by exact_mod_cast hr2
    have c3 : (10 : ℝ) ≤ L.sc.L := hN.big.2.1
    have : (8 : ℝ) * 2 * 10 ≤ D.R.f * D.R.r * L.sc.L := by gcongr
    linarith
  have hPP : (4 : ℝ) ≤ PP := hz.trans ((le_self_pow₀ (by linarith) (by norm_num)).trans hN.ppLow)
  have hT : 16 * dimFlag (dat p i) ^ 2 ≤ lenT p i PP := by
    have h1 : (16 * dimFlag (dat p i) ^ 2 : ℝ) ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by
      have c3 : (0 : ℝ) < D.R.m := by exact_mod_cast (by omega : 0 < D.R.m)
      have c4 : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast (by omega : D.R.m ≤ D.R.k)
      have c5 : (16 : ℝ) ≤ PP ^ 2 := by nlinarith
      rw [le_div_iff₀ c3]
      have c6 : (0 : ℝ) ≤ (dimFlag (dat p i) : ℝ) ^ 2 := by positivity
      calc (16 * (dimFlag (dat p i) : ℝ) ^ 2) * D.R.m ≤ (PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2) * D.R.m :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right c5 c6) c3.le
        _ ≤ PP ^ 2 * (dimFlag (dat p i) : ℝ) ^ 2 * D.R.k := mul_le_mul_of_nonneg_left c4 (by positivity)
    have h2 := h1.trans (Nat.le_ceil _)
    unfold lenT
    exact_mod_cast h2
  intro τ a b hb
  obtain ⟨g1, g2, -⟩ := G τ a b hb
  have hTz : (16 * (dimFlag (dat p i) : ℤ) ^ 2) ≤ (lenT p i PP : ℤ) := by exact_mod_cast hT
  have hD1z : (1 : ℤ) ≤ dimFlag (dat p i) := by exact_mod_cast hD1
  have hsq : (dimFlag (dat p i) : ℤ) ≤ (dimFlag (dat p i) : ℤ) ^ 2 := by nlinarith
  push_cast at G ⊢
  by_cases hbp : (b : ℕ) = (dat p i).p
  · have g := (g2 hbp).2
    have hT0 : (0 : ℤ) < 4 * (lenT p i PP : ℤ) := by nlinarith
    have hle : (lenT p i PP : ℤ) ≤ u1 τ a - u1 τ b - 3 * (((dat p i).p + (dat p i).q : ℕ) : ℤ) := by
      by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_left hc hT0
      nlinarith
    push_cast at hle
    linarith
  · have g := g1 hbp
    push_cast at g
    linarith

end Point

end GlobalTheory.CovHt.GeomBound

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GeometricOfHyp

section

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.CovHt.GeomBound
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
theorem geometric_height_bound_at_place (hX : GlobalTheory.CovTop.HypothesesX) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hS1 : GlobalTheory.Published.SiegelToroidalIntegral) (hS2 : GlobalTheory.Published.ToroidalForFanKS)
    (hS3 : GlobalTheory.Published.SemiAbelianLieSeminegative)
    {PP C A M : ℝ} (hsz : SizeAt p i PP C) (hN : HostNum D L PP A M) (hw : WtNum p i PP) (hi : (i : ℕ) + 1 < D.R.m)
    (Y : Cov p i) (hY : GoodCov p i Y) (u1 : AllWt.Weight (dat p i)) (hu : Quo p i PP u1) : GeomAt p i Y u1 := by
  obtain ⟨hsig1, hsig2, -⟩ := hw.sig
  have hk := D.R.m_add_three_le_k
  have hp1 : 1 ≤ (dat p i).p := by rw [hsig1]; simp only [Ranks.sigW]; omega
  have hq1 : 1 ≤ (dat p i).q := by rw [hsig2]; simp only [Ranks.sigW]; omega
  have hf : 2 < Module.finrank ℚ D.host.E / 2 := by rw [hN.deg]; have := hN.f8; omega
  have hj : InR D ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hL : LawsJ p.T := p.fw.laws
  have hYg := hY.1
  obtain ⟨-, -, -, -, -, -, hq⟩ := hsz
  obtain ⟨-, hq⟩ := hq hi
  obtain ⟨-, -, hρ1, -⟩ := hq u1 hu
  have hgap := quo_gaps p i hN hw hi u1 hu
  have hsa : ∀ τ, StrictAnti (u1 τ) := fun τ => strictAnti_of_step fun a b hb => by
    have := hgap τ a b hb
    have : (0 : ℤ) ≤ (((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) : ℤ) := by positivity
    omega
  have hg1 : ∀ τ, 1 ≤ GlobalTheory.CompHS.gap (u1 τ) ((dat p i).p - 1) := fun τ => by
    have e := GlobalTheory.CompHS.gap_eq (u1 τ) (i := ⟨(dat p i).p - 1, by omega⟩) (j := ⟨(dat p i).p, by omega⟩)
      (by simp only; omega)
    simp only at e
    rw [e]
    have := hgap τ ⟨(dat p i).p - 1, by omega⟩ ⟨(dat p i).p, by omega⟩ (by simp only; omega)
    have : (0 : ℤ) ≤ ((dimFlag (dat p i) + 3) ^ 2 + 2 * ((dat p i).p + (dat p i).q) : ℕ) := by positivity
    push_cast at *
    nlinarith
  have hgood := _root_.GlobalTheory.T.covering_domain_lattice_regularity hP _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg u1 (fun τ => (hsa τ).antitone) hg1
  have hbir := _root_.GlobalTheory.T.birOn_wtOf_of_consecutive_gap_bound hX hG hQ hS1 (_root_.GlobalTheory.T.covering_topology_refinement hP) hP.q15 hP.q16 _ p.T hL _ hp1 hq1 Y _ _ hYg u1 hgap
  have hprop := (_root_.GlobalTheory.T.proportionality_principle_compactification hP hS1 hS2 hS3 _ p.T hL _ hp1 hq1 hf hj Y _ _ hYg).1
  intro Z
  refine ⟨hgood.2 Z, hbir Z, ?_⟩
  have hv : vdm u1 ≠ 0 := (GlobalTheory.CompHt.vdm_pos hsa).ne'
  rw [delPrime_eq Y.U Z hv]
  exact mul_le_mul_of_nonneg_left (GlobalTheory.DegTop.compDeg_le hprop Z hsa) (by linarith)
end Point
end GlobalTheory.CovHt.GeomBound
end
end

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeometricOfHyp

section

@[expose] public section



section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option autoImplicit false

noncomputable section
namespace GlobalTheory.CovHt.GeomBound
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
end Point
theorem geom_of_prints_toroidal_deepGood_size : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS →
    GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.GeometricCondition := by
  intro hX hG hQ hP h1 h2 h3 _ hS
  have hH := _root_.GlobalTheory.CovTop.Sizes.hostN_alt 0
  have hW := _root_.GlobalTheory.CovTop.WtShape.wtN_z
  unfold _root_.GlobalTheory.CovHt.GeometricCondition _root_.GlobalTheory.CovTop.CoversCondition _root_.GlobalTheory.CovTop.LiftsCondition
  unfold _root_.GlobalTheory.CovTop.SizeCondition _root_.GlobalTheory.CovTop.LiftsCondition at hS
  unfold _root_.GlobalTheory.CovTop.HostNAlt _root_.GlobalTheory.CovTop.LiftsCondition at hH
  unfold _root_.GlobalTheory.CovTop.LiftWeightNumerator _root_.GlobalTheory.CovTop.LiftsCondition at hW
  refine ((hS.and hH).and hW).imp fun Fm CH _ h => ?_
  obtain ⟨⟨⟨C1, -, e1⟩, ⟨C2, -, e2⟩⟩, ⟨C3, -, e3⟩⟩ := h
  obtain ⟨x0, hx0⟩ := (e1.and e2).and e3
  refine ⟨0, le_rfl, x0, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  obtain ⟨⟨b1, b2⟩, b3⟩ := hx0 x hx hle ι p hp
  exact _root_.GlobalTheory.CovHt.GeomBound.geometric_height_bound_at_place p i hX hG hQ hP h1 h2 h3 (b1 i) (b2 i) (b3 i) hi Y hY u1 hu
end GlobalTheory.CovHt.GeomBound
end
end
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt

theorem _root_.GlobalTheory.T.covHt_geom_of_siegel_toroidal_semiAbelian : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovHt.GeometricCondition := by
  first | exact @_root_.GlobalTheory.CovHt.GeomBound.geom_of_prints_toroidal_deepGood_size | exact _root_.GlobalTheory.CovHt.GeomBound.geom_of_prints_toroidal_deepGood_size | (intros; apply _root_.GlobalTheory.CovHt.GeomBound.geom_of_prints_toroidal_deepGood_size <;> assumption)
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HostNStatement

section

@[expose] public section



section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR.Links ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

theorem _root_.GlobalTheory.T.hostN_forall : ∀ M : ℝ, _root_.GlobalTheory.CovTop.HostNAlt M := by
  first | exact @_root_.GlobalTheory.CovTop.Sizes.hostN_alt | exact _root_.GlobalTheory.CovTop.Sizes.hostN_alt | (intros; apply _root_.GlobalTheory.CovTop.Sizes.hostN_alt <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeightLowerBoundGeneral

section

@[expose] public section



section
section
open GlobalTheory.CovTop GlobalTheory.BigTop
namespace SelfIntersectionVolumeEstimates

theorem height_lower_bound_general_alt : _root_.SelfIntersectionVolumeEstimates.VolumeEstimateHypotheses → GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.CovHt.HypothesesH → GlobalTheory.CompanionTheory.Ar.Plug.DeepStR → _root_.GlobalTheory.CovTop.DeepGoodness → _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.CovTop.CoverDegree → _root_.GlobalTheory.CovTop.FlatDegreeCondition → _root_.GlobalTheory.CovTop.HeightCondition :=
  fun hSB hX hGD hQ hP hH hD hG hS hDg hF => _root_.GlobalTheory.CovHt.HtTopG.height_of_meanAll_bound hSB hP hG hS hDg (_root_.GlobalTheory.T.covering_short_of_deep_size_flatDeg hP hG hS hF) (_root_.GlobalTheory.T.covHt_geom_of_siegel_toroidal_semiAbelian hX hGD hQ hP hH.sieg hX.ks hX.lie hG hS) (_root_.GlobalTheory.T.carrying_section_integral_frame_alt (_root_.GlobalTheory.T.refW_of_prints_deepGood_size_flatDeg hP hG hS hF) (_root_.GlobalTheory.T.exists_section_bounded_by_bergman_kernel_alt hP hH hG hS hF)) (_root_.GlobalTheory.T.budget_of_hostN_of_liftWeight_of_size _root_.GlobalTheory.T.hostN_forall _root_.GlobalTheory.T.lift_weight_numerator hS) hD
end SelfIntersectionVolumeEstimates
end
end
end
end
