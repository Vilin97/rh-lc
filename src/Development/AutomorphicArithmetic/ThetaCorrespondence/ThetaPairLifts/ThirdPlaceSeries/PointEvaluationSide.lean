module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowGood
public import Development.AbelianVarietyTheory.Definitions.Divisors.KerSizes
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RecHeightSWith
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.SharpRestriction.GlobalSchurBounds.IntegralityOfRationalityLocal
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalRingCardinality.DataParams₂
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Formalism.SharpRestriction.ElevenLe
import Formalism.LocalRingCardinality.HostCls
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairLeIffPairHtLe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClassFam
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SevenLogLeLOfPowerBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerSizesOfStdKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelCompatibilitiesStandardKernelDataTrueColumStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSymmetricColumnFormsStepZeroFiniteCharacteStatement
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
public import Formalism.LocalToGlobal.GlobalTheory.CoordinateLengths.SecondBranchAllMembers
public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.HeckeRamifiedZeroAll
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IntegralAtT0Lattice
public import Formalism.SharpRestriction.GlobalSchurBounds.LogXLowerFamilyOfTheorems
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EtaJUntw
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
import Development.AutomorphicArithmetic.PrimeDiscriminants.Scales
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowsUOfColPinsStatement
import Formalism.LocalToGlobal.Divisibility.RecBridgeSel
public import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScaleLargeThree

section

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory

theorem scale_large_three (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    Real.log (4 * s.x) ≤ s.L ∧ 8 ≤ s.X' ∧ 2 ≤ s.x := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ (1/2) * x ^ eps := by
    have := (isLittleO_log_rpow_atTop he).bound (c := 1/2) (by norm_num)
    filter_upwards [this, Filter.eventually_gt_atTop 1] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hp : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hp] at hx
    exact hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, Real.log 4 ≤ (1/2) * x ^ eps := by
    have := (tendsto_rpow_atTop he).eventually_ge_atTop (2 * Real.log 4)
    filter_upwards [this] with x hx
    linarith
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, (3 : ℝ) ≤ x ^ (eps / 3) :=
    (tendsto_rpow_atTop (by linarith : 0 < eps / 3)).eventually_ge_atTop 3
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    (h1.and (h2.and (h3.and (Filter.eventually_ge_atTop (2 : ℝ)))))
  refine ⟨x0, fun s hs hx => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hx0 s.x hx
  have hxpos : 0 < s.x := by linarith
  refine ⟨?_, ?_, a4⟩
  · show Real.log (4 * s.x) ≤ s.x ^ s.eps
    rw [Real.log_mul (by norm_num) hxpos.ne', hs]
    linarith
  · show 8 ≤ Real.exp (s.x ^ (s.eps / 3))
    rw [hs]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h8 : (8 : ℝ) ≤ Real.exp 3 := by
      have : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he1 3]
    exact h8.trans (Real.exp_le_exp.2 a3)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwoLeOfLogPos

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt.RowsOfDesign

theorem two_le_of_log_pos' (n : ℕ) (h : 0 < Real.log (n : ℝ)) : 2 ≤ n := by
  by_contra hn
  have h1 : n = 0 ∨ n = 1 := by omega
  rcases h1 with rfl | rfl <;> simp at h

theorem two_le_rdE' (D : D7) (hq : 2 ≤ D.host.q) (hd : 2 ≤ D.host.d) : 2 ≤ D.host.rdE := by
  have h := (factRd D.R D.host).2.2
  have hf : (2 : ℝ) ≤ D.R.f := by
    have := D.host.four_le_n'
    have h2 : D.R.f = 2 * D.R.n := rfl
    exact_mod_cast (by omega : 2 ≤ D.R.f)
  have h0 : 0 ≤ D.host.rdE := by unfold Host.rdE; positivity
  nlinarith

theorem rows_of_design : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), Formalism.MainNotions.SizesAt L → Real.log (4 * L.sc.x) ≤ L.sc.L →
    DelNat D → ThickUp L → HtRowsS L P.CYL := by
  intro D L P hS hx4 hDN hTU
  obtain ⟨-, -, -, -, hT, hCond, hQD, -, hLa, hRho, hBot, -, -, hEta, hNodes, -, hDel, -⟩ := hS
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hq2 : 2 ≤ D.host.q := two_le_of_log_pos' _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)
  have hd2 : 2 ≤ D.host.d := two_le_of_log_pos' _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)
  have hq' : (2 : ℝ) ≤ D.host.q := by exact_mod_cast hq2
  have hd' : (2 : ℝ) ≤ D.host.d := by exact_mod_cast hd2
  have hrd2 := two_le_rdE' D hq2 hd2
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := by have := D.host.four_le_n'; omega
    exact_mod_cast this
  have ht1 : (1 : ℝ) ≤ D.R.t := hT.1
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) < D.R.k := by
    have : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  refine ⟨⟨P⟩, ⟨?_, hQD.2.2.2.2.2.1, hx4⟩, ?_, ⟨?_, hEta.1, hEta.2.2.2.2.1, hDel.2.2.2.1, ?_⟩, hDN, hTU⟩
  ·
    have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
    have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
      Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hc : D.host.rdE ≤ Formalism.MainNotions.szCond L := by
      refine hQD.2.2.2.2.2.2.2.trans ?_
      unfold Formalism.MainNotions.szCond
      have : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
          (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hs (by positivity)
      have h0 : 0 ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
      nlinarith
    have hc1 : 1 ≤ Formalism.MainNotions.szCond L := by linarith
    have h36 : Formalism.MainNotions.szCond L ≤ Formalism.MainNotions.szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
    have h150 : Formalism.MainNotions.szCond L ^ 36 ≤ Formalism.MainNotions.szCond L ^ 36 * (D.R.t : ℝ) ^ 150 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
    have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hfin : D.host.rdE ≤ L.sc.b := hc.trans (h36.trans (h150.trans (hCond.trans hsb)))
    have := Real.log_le_log (by linarith) hfin
    rwa [show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _] at this
  · intro i
    obtain ⟨Y, hY1, -, hY3, hY4⟩ := P.g_Y
    have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY1
    have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le hY0 (hY4 i).1
    have h1 := Real.log_le_log hg0 (hY4 i).2
    rw [Real.log_mul (by norm_num) hY0.ne'] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    linarith
  · have h1 := hNodes.2.2.2.1
    have h2 : L.etaSz / D.R.m ≤ L.etaSz := div_le_self L.etaSz_pos.le hm1
    have h3 : (0 : ℝ) ≤ D.R.t := by linarith
    linarith
  · intro t
    have h1 := hBot t
    have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1
    have h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
      div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx0 _).le (Real.log_nonneg hx1.le)) hLa0) hk0.le
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
    have hb' : 0 ≤ L.sc.b' := by
      unfold Scale.b' Scale.a Scale.X' Scale.b
      positivity
    have hR : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k +
        L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k ≤ L.sc.x ^ (-2 : ℝ) := hRho
    have h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 := by
      have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
          4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      have h0 : 0 ≤ Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k := by
        unfold Formalism.MainNotions.szNst Scale.delta1
        have := Real.rpow_pos_of_pos hx0 (-(L.sc.eps / 8))
        have := Real.rpow_pos_of_pos hx0 L.sc.eps
        positivity
      linarith
    have h5 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k * L.sc.b' := by ring
    rw [h5] at h1
    nlinarith

end GlobalTheory.CoreHt.RowsOfDesign
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamRowsSizes

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Core GlobalTheory.Core.Ht2 GlobalTheory.CoreHt
open GlobalTheory.ColumnNormCompare (numDatumOfParameters codeRec plRec)
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.CoreHt

theorem famRowsSizes : ∀ {eps : ℝ} (Fm : FamP eps), TuSize Fm → ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, GlobalTheory.CoreHt.DelNat (Fm.D x i) → GlobalTheory.CoreHt.HtRowsS (Fm.L x i) Fm.CYL ∧ 8 ≤ (Fm.L x i).sc.X' ∧ 2 ≤ (Fm.L x i).sc.x ∧ (∀ u, 4 * (Fm.L x i).sc.a < (((Fm.D x i).mem u).A.T : ℝ)) ∧ ∀ u, Real.log ((((Fm.D x i).mem u).A.T : ℕ) : ℝ) ≤ max Fm.CTu 0 * (Fm.D x i).R.m * (Fm.L x i).sc.L := by
  intro eps Fm hTu
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  obtain ⟨x1, hT⟩ := hTu
  obtain ⟨xL, hL⟩ := GlobalTheory.scale_large_three eps he
  obtain ⟨x3, h3⟩ := flipTwoThree.le_rpow_for_large_x ((2 : ℝ) / 5) (by norm_num) 4
  obtain ⟨x4, h4⟩ := flipTwoThree.pow_le_exp_rpow_for_large_x 2 eps he
  refine ⟨max (max (max x1 xL) x3) (max x4 (max 9 (Fm.x1 + 1))), fun x hx i hDel => ?_⟩
  have e1 : x1 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have eL : xL ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have e3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have e4 : x4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have e9 : (9 : ℝ) ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hx
  have e5 : Fm.x1 < x := by
    have := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hx
    linarith
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i e5
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  obtain ⟨hlog, h8, h2⟩ := hL (Fm.L x i).sc hse (by rw [hsx]; exact eL)
  have hThick : ThickUp (Fm.L x i) := fun j j1 j2 τ hc => ((Fm.L x i).win_thick j j1 j2 τ hc).2
  have hrows : HtRowsS (Fm.L x i) Fm.CYL := by
    have := GlobalTheory.CoreHt.RowsOfDesign.rows_of_design (Fm.D x i) (Fm.L x i) (Fm.params x e5 i) (Fm.sizes x e5 i) hlog hDel hThick
    rwa [Fm.params_CYL x e5 i] at this
  have hm : (4 : ℝ) ≤ (Fm.D x i).R.m := by
    have z1 := (flipTwoThree.size_bounds_of_scale (Fm.L x i) (Fm.sizes x e5 i) (by rw [hsx]; linarith)).1
    rw [hsx] at z1
    exact le_trans (h3 x e3) z1
  have hx0 : 0 < x := by linarith
  have hb1 : 1 ≤ (Fm.L x i).sc.b := by
    unfold Scale.b; exact Real.one_le_exp (Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  have hb0 : 0 < (Fm.L x i).sc.b := by linarith
  have h8b : 8 * x < (Fm.L x i).sc.b := by
    have hx2 := h4 x e4
    have hbe : (Fm.L x i).sc.b = Real.exp (x ^ eps) := by
      unfold Scale.b Scale.L; rw [hsx, hse]
    rw [hbe]
    nlinarith
  have hb2 : (Fm.L x i).sc.b ^ (2 : ℝ) ≤ (Fm.L x i).sc.b ^ (((Fm.D x i).R.m : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hb1 (by linarith)
  rw [Real.rpow_two] at hb2
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L; exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _
  have hm0 : (0 : ℝ) ≤ (Fm.D x i).R.m := by linarith
  refine ⟨hrows, h8, h2, fun u => ?_, fun u => ?_⟩
  · have hTge := (hT x e1 i).1 u
    have ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b := by unfold Scale.a; rw [hsx]
    rw [ha]
    have : 8 * (x * (Fm.L x i).sc.b) < (Fm.L x i).sc.b ^ 2 := by
      rw [← mul_assoc, sq]; exact mul_lt_mul_of_pos_right h8b hb0
    have hxb : 0 < x * (Fm.L x i).sc.b := mul_pos hx0 hb0
    linarith
  · refine le_trans ((hT x e1 i).2 u) ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hm0) hL0

end GlobalTheory.CoreHt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeilUnitaryEntries

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc

namespace GlobalTheory.Fc.RL.DefSide


open Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory in
theorem full_rank {eps : ℝ} (Fm : FamP eps) (CH : ℝ) (tie : RealPlaceSecondLayerConditions Fm) (hTu : TuSize Fm) (hCh : ChosenE Fm 3 CH) :
    NuFullF Fm ∧ J.MuRank Fm := by
  have tT := (family_conditions_of_layer_two Fm tie).2.2
  have h := slope_free_branch_family Fm tT freeTT_holds slopeLineT_holds Formalism.L2.GlobalTheoryTheory.LemB.second_branch_all_members
  obtain ⟨hT2, hT5⟩ := Formalism.MainNotions.Wire.family_theorems_two_and_five Fm h.1 h.2.1 (hI_tied Fm tT PI.IntegralAtBasePointLattice.integral_at_t0_lattice)
    (tT.mono fun D u hS ht => Formalism.L2.GlobalTheoryTheory.UnramifiedTrace.hecke_ramified_zero_all D u hS ht) h.2.2
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, cPr, _⟩ := hCh
  exact muRank_items Fm 3 (by norm_num) hT2 hT5 hTu cPr

theorem wts_eq {X X' : Formalism.L2.Col.Fields} (h : X = X') {P : Formalism.L2.Col.Primes X} {P' : Formalism.L2.Col.Primes X'} (hP : HEq P P')
    {R R' : Ranks} (hR : R = R') : Formalism.L2.Col.Wts X P.Word R = Formalism.L2.Col.Wts X' P'.Word R' := by
  subst h; cases hP; subst hR; rfl

end GlobalTheory.Fc.RL.DefSide

end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PointEvaluationSide

section

@[expose] public section



section
noncomputable section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
namespace GlobalTheory.Fc.RL.DefSide
def PointEvaluationSide : BdP _root_.GlobalTheory.Fc.BundleCondition := fun D O _ b =>
  (Formalism.L2.Theta.RealTied D ∧ ∃ C : Formalism.L2.Forms.ColsTiedSym D, ∀ u, Formalism.MainNotions.RT.ChiFin0 (C.forms u)) ∧
  _root_.Formalism.L2.DIV.ColumnCharactersCompatible b.C.toS ∧ ∃ W : Formalism.L2.Col.Wts b.R.T.ker.X b.R.T.ker.Pr.Word D.R, HEq b.C.toS.c.W W ∧
    GlobalTheory.ColRows.KerTies b.R.T.ker W b.DH.1.1 b.DH.1.2 ∧
    ∀ CY CT : ℝ, GlobalTheory.CoreHt.HtRowsS O.L CY → 8 ≤ O.L.sc.X' → 2 ≤ O.L.sc.x → (∀ u, 4 * O.L.sc.a < ((D.mem u).A.T : ℝ)) →
      (∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * O.L.sc.L) →
      GlobalTheory.ColRows.KerSizes b.R.T.ker W b.DH.1.1 b.DH.1.2 CY CT
theorem pointEvaluationSide_of_bWit {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : WPt p.s K) {c : ℝ}
    (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b) : _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide _ _ c b := by
  have hk := b.C.kerTie
  have e : Formalism.L2.Col.Wts _ b.C.c.Pr.Word b.C.c.Rk = Formalism.L2.Col.Wts b.R.T.ker.X b.R.T.ker.Pr.Word (q.w.D q.Z).R :=
    wts_eq hk.1.symm hk.2.2.1 hk.2.1
  have hW : HEq (cast e b.C.c.W) q.B.wts := (cast_heq e _).trans w.cW.1
  refine ⟨⟨q.x.real, GlobalTheory.T.exists_symmetricColumnForms_stepZeroFiniteCharacter q.w.I q.w.ok q.w.pins q.w.l q.Z⟩, w.colPins, cast e b.C.c.W, (cast_heq e _).symm, ?_, ?_⟩
  · exact GlobalTheory.T.kernelCompatibilities_standardKernelData_trueColumns q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex b.R.T.ker _ _ _ q.x.pin.jets w.recPin.k.std hW
      b.DH.2.1 b.DH.2.2 (b.R.T.ker_sharp _)
  · exact GlobalTheory.ColRows.kerSizes_of_stdKer q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex b.R.T.ker _ _ _ w.recPin.k.std hW
      b.DH.2.1 b.DH.2.2
theorem pointEvaluationSide_of_isLinked {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (β : BPt K) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition β.D β.O c)
    (h : _root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p K β c b) : _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide _ _ c b := by
  obtain ⟨q, b', ⟨w⟩, e⟩ := h
  exact Eq.mpr (congrArg (fun y : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c => _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide y.1 y.2.1 c y.2.2) e) (_root_.GlobalTheory.Fc.RL.DefSide.pointEvaluationSide_of_bWit q b' w)
theorem definiteSideCondition_of_nprimeDef_of_nuFull (CY CT : ℝ) (hCT : 0 ≤ CT) : ∃ C0 : ℝ, ∀ (D : D7) (O : Obj D) (c : ℝ) (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (C CH : ℝ),
    _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide D O c b → GlobalTheory.CoreHt.HtRowsS O.L CY → 8 ≤ O.L.sc.X' → 2 ≤ O.L.sc.x → (∀ u, 4 * O.L.sc.a < ((D.mem u).A.T : ℝ)) →
      (∀ u, Real.log (((D.mem u).A.T : ℕ) : ℝ) ≤ CT * D.R.m * O.L.sc.L) → DV.NprimeDef D O.L → D.NuFull →
      (∀ u, 0 < (D.div.Nu u).rank) → C0 ≤ c → _root_.GlobalTheory.Fc.DefiniteSideCondition D O c b C CH := by
  obtain ⟨C0, hC0⟩ := _root_.GlobalTheory.T.kernel_columns_from_ties_alt CY CT hCT
  refine ⟨C0, fun D O c b C CH hE h1 h2 h3 h4 h5 hN hF hR hc => ?_⟩
  obtain ⟨-, hpin, W, hW, hT, hS⟩ := hE
  intro hok1 hsep hP hI lam0 c0 ce Sw C1 H NuC I _ hII u
  have hZs : (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs = b.P.Zs := (_root_.GlobalTheory.Fc.qRealOfBundle b).zs
  have hS0 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.base.toIndefData b.P.S0 := (_root_.GlobalTheory.Fc.qRealOfBundle b).s0
  have hS1 : HEq (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).core.cols.toIndefData b.P.S1 := (_root_.GlobalTheory.Fc.qRealOfBundle b).s1
  have hDc : HEq (b.C.toS.c.face (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI).Zs) b.P.Dc :=
    (congr_arg_heq b.C.toS.c.face hZs).trans (heq_of_eq b.C.toS.colTie.1)
  have hw : HEq (I.wU u) u := ((Formalism.L2.DIV.divTieDat3_heq hZs hS0 hS1 hDc hII).2.2 u).trans (b.C.wTie u)
  obtain ⟨ch, tc, ht, X0, hx, hn, hb, cb, hs, hd, ha, hl⟩ := hC0 D O.L _ _ _ _ _ _ O.ex b.R.T b.P b.C.toS W _ _ hpin hW hT (hS CY CT h1 h2 h3 h4 h5) hN hF hR _ _ C CH
    (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (_root_.GlobalTheory.Fc.qRealOfBundle b) hok1 hsep C CH hP hI) hZs u lam0 c0 ce c Sw C1 (H u) (I.wU u) (I.eNu u) hw hc
  have hspan : Submodule.span D.what₂.LL (O.L.NuLat u : Set (D.div.Nu u).V) = ⊤ := by
    apply top_unique
    rw [← (hF u).2, Submodule.span_le]
    intro y hy
    rw [hN u] at hy
    apply ((Submodule.span_le (p := (Submodule.span D.what₂.LL (O.L.NuLat u : Set (D.div.Nu u).V)).restrictScalars (𝓞 D.what₂.LL))).mpr ?_) hy
    rintro _ ⟨a, _, z, hz, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span hz)
  have hfull : Submodule.IsFullLattice D.what₂.LL (Formalism.L2.DIV.Cons.nuOf O.L u (I.eNu u)) := by
    letI : Submodule.IsLattice D.what₂.LL (Formalism.L2.DIV.Cons.nuOf O.L u (I.eNu u)) := hl
    refine ⟨?_⟩
    let e := I.eNu u
    let S := Submodule.span D.what₂.LL (Formalism.L2.DIV.Cons.nuOf O.L u (I.eNu u)).carrier
    have hm : Submodule.span D.what₂.LL (O.L.NuLat u : Set (D.div.Nu u).V) ≤ S.map e.toLinearMap := by
      apply Submodule.span_le.mpr
      intro y hy
      refine ⟨e.symm y, Submodule.subset_span ?_, e.apply_symm_apply y⟩
      change e (e.symm y) ∈ O.L.NuLat u
      simpa using hy
    rw [hspan, top_le_iff] at hm
    apply top_unique
    intro x _
    have hx' : e x ∈ S.map e.toLinearMap := hm ▸ Submodule.mem_top
    obtain ⟨y, hy, he⟩ := hx'
    have : y = x := e.injective he
    change x ∈ S
    simpa [this] using hy
  exact ⟨ch, tc, ht, X0, hx, hn, hb, cb, hs, hd, ha, hfull⟩
theorem linkedAt_df_of_parameters {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) : _root_.GlobalTheory.Fc.RL.LinkedAt p _root_.GlobalTheory.Fc.RL.RowDefectCondition := by
  refine _root_.GlobalTheory.Fc.RL.LinkedAt.of_row (p := p) (H := Ind.EvWC (Bd := _root_.GlobalTheory.Fc.BundleCondition) (fun _ => True) fun C CH D O c b => _root_.GlobalTheory.Fc.DefiniteSideCondition D O c b C CH)
    ⟨fun _ => _root_.GlobalTheory.Fc.RL.DefSide.PointEvaluationSide, RowE.of_all fun _ _ β c b _ _ h => _root_.GlobalTheory.Fc.RL.DefSide.pointEvaluationSide_of_isLinked β c b h, fun 𝒜 σ s => ?_⟩
  choose c0 hc0 using fun (CY CT : ℝ) => _root_.GlobalTheory.Fc.RL.DefSide.definiteSideCondition_of_nprimeDef_of_nuFull CY (max CT 0) (le_max_right _ _)
  refine (Formalism.MainNotions.DIV.closed_Csz_ge_fn (W3 𝒜) fun l => c0 (l.getD 6 0) (l.getD 13 0)).imp ?_
  intro eps Fm CH _ hC hc _
  have hC' : c0 Fm.CYL Fm.CTu ≤ Fm.Csz := hC
  obtain ⟨κ, -, -, hs⟩ := s Fm (w3_a hc)
  have tie : RealPlaceSecondLayerConditions Fm := ⟨Fm.x1 + 1, fun x hx i => (hs x (by linarith) i).2.1⟩
  obtain ⟨CH', hCh⟩ := hc.2.1
  obtain ⟨⟨a1, hF⟩, ⟨a2, hR⟩⟩ := full_rank Fm CH' tie hc.2.2.1 hCh
  obtain ⟨a3, hz⟩ := GlobalTheory.CoreHt.famRowsSizes Fm hc.2.2.1
  refine ⟨0, le_rfl, fun C _ => ⟨max a1 (max a2 a3), fun x hx h0 i => ?_⟩⟩
  have e1 : a1 ≤ x := le_trans (le_max_left _ _) h0
  have e2 : a2 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) h0
  have e3 : a3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) h0
  obtain ⟨z1, z2, z3, z4, z5⟩ := hz x e3 i ⟨_, (σ Fm (w3_a hc) x hx i).DH.2.1⟩
  exact hc0 Fm.CYL Fm.CTu _ _ _ (σ Fm (w3_a hc) x hx i) C CH (hs x hx i).2 z1 z2 z3 z4 z5 (Fm.nprimeDef x hx i)
    (hF x e1 i) (hR x e2 i) hC'
end GlobalTheory.Fc.RL.DefSide
theorem GlobalTheory.Fc.RL.linkedAt_prmR_df_of_cuspRapidDecay : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) _root_.GlobalTheory.Fc.RL.RowDefectCondition :=
  fun _ _ _ _ _ N S Γ => _root_.GlobalTheory.Fc.RL.DefSide.linkedAt_df_of_parameters (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ)
end
end
end
end
