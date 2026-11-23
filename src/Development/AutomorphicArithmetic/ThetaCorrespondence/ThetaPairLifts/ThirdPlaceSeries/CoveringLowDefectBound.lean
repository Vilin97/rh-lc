module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftLambdaBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
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
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DefectBoundOfConnected
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParametersScaleRankGapBounds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WtNZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDefiniteBoundGeAnchoredMainTermSubCrudeErrors

section

@[expose] public section


open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefArith

theorem sum_laOf_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hq : Dw.q = 0) (hn : Even n) (τ : Psi H) :
    (∑ k, (laOf Dw a n τ k : ℝ)) = (GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ) + (Dw.p : ℝ) * n / 2 := by
  have hm : Dw.mult τ.1 = Dw.p := by unfold Datum.mult; rw [if_pos τ.2]
  have hk : ∀ k : Fin (Dw.p + Dw.q), (laOf Dw a n τ k : ℝ) = (a (τ.1, k) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro k
    have h := k.2
    have hlt : (k : ℕ) < Dw.p := by omega
    simp [laOf, weightOf, hlt]
    norm_cast
  simp_rw [hk]
  rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)) (Dw.p + Dw.q)]
  have hs : (GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ) = ∑ i ∈ Finset.range Dw.p, (a (τ.1, i) : ℝ) := by
    unfold GlobalTheory.DualWeyl.size part
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)) (Dw.mult τ.1), hm]
  rw [hs, hq, add_zero]
  obtain ⟨r, rfl⟩ := hn
  have : (r + r) / 2 = r := by omega
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, this, hq, add_zero]
  push_cast
  ring

end GlobalTheory.DefArith

namespace GlobalTheory.DefArith

theorem two_defBound_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (lo : ℝ), Dw.q = 0 → 1 ≤ Dw.p → Even n → -(∑ τ : Psi H, (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) - |lo| * (∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) - (∑ τ : Psi H, Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) - (n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E| ≤ 2 * defBound Dw a n (-flatDegVal Dw lo) := by
  intro E _ _ _ H Dw a n kc lo hq hp hn
  have hp0 : (Dw.p : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Dw.p := by exact_mod_cast hp
    exact this.ne'

  have hτ : ∀ τ : Psi H, -((Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
      |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) ≤
      2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) := by
    intro τ
    have hS := sum_laOf_eq Dw a n hq hn τ
    have hsplit : (∑ k, (laOf Dw a n τ k : ℝ)) =
        (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) + ∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hq, add_zero]
      ring
    have hb : -(|lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) ≤
        -((∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo) := by
      rw [neg_le_neg_iff]
      calc (∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo
          ≤ |(∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo| := le_abs_self _
        _ = |∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))| * |lo| := abs_mul _ _
        _ ≤ (∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) * |lo| :=
            mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
        _ = |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| := mul_comm _ _
    have he : 2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) =
        -((∑ k, (laOf Dw a n τ k : ℝ)) * lo) - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) := by
      rw [hS]
      unfold flatDegVal
      rw [hq]
      field_simp
      ring
    rw [he, hsplit]
    linarith
  have hlog : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hN : 0 ≤ (n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) := by positivity
  have hl : -((n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E|) ≤
      2 * ((n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)) := by
    have h1 := le_abs_self (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E)
    have h2 : -|GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E| ≤ Real.log (2 * Real.pi) / 2 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hN
    nlinarith
  have hsum := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => hτ τ
  have eL : -(∑ τ : Psi H, (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
      |lo| * (∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) -
      (∑ τ : Psi H, Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) =
      ∑ τ : Psi H, (-((Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
        |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  have eR : 2 * defBound Dw a n (-flatDegVal Dw lo) =
      ∑ τ : Psi H, 2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) +
      2 * ((n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)) := by
    unfold defBound
    rw [mul_add, Finset.mul_sum]
  rw [eL, eR]
  linarith

end GlobalTheory.DefArith
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDefiniteBoundGeAnchoredMainTermSubCrudeErrorsStatement

section

@[expose] public section


open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.two_definiteBound_ge_anchoredMainTerm_sub_crude_errors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (lo : ℝ), Dw.q = 0 → 1 ≤ Dw.p → Even n → -(∑ τ : Psi H, (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) - |lo| * (∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) - (∑ τ : Psi H, Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) - (n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E| ≤ 2 * defBound Dw a n (-flatDegVal Dw lo) := by
  first | exact @GlobalTheory.DefArith.two_defBound_ge | exact GlobalTheory.DefArith.two_defBound_ge | (intros; apply GlobalTheory.DefArith.two_defBound_ge <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ParametersScaleRankGapBoundsStatement

section

@[expose] public section



section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.weight_dimension_log_bound' : _root_.GlobalTheory.CovTop.LiftsCondition fun Fm x _ ι p i _ C => (i : ℕ) + 1 = (Fm.D x ι).R.m → |(ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm| * (∑ τ : Psi p.T.Q.H, ∑ k, |(laOf (dat p i) (wtA (p.κ i)) (p.κ i).n τ k : ℝ) - (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1) τ : ℝ)|) + (∑ τ : Psi p.T.Q.H, Real.log (GlobalTheory.DualWeyl.dim (part (dat p i) (wtA (p.κ i)) τ.1) : ℝ)) + ((p.κ i).n : ℝ) * (Fintype.card (Psi p.T.Q.H) : ℝ) * ((dat p i).p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd (Fm.D x ι).host.E| ≤ C * unitE p := by
  first | exact @_root_.GlobalTheory.CovTop.DefSizes.parameters_scale_rank_gap_bounds | exact _root_.GlobalTheory.CovTop.DefSizes.parameters_scale_rank_gap_bounds | (intros; apply _root_.GlobalTheory.CovTop.DefSizes.parameters_scale_rank_gap_bounds <;> assumption)
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoveringLowDefectBound

section

@[expose] public section



section
section

noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.CovTop.DefLow
theorem covering_low_defect_alt : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.LowDefectCondition := by
  intro hP hG hA
  have hc := _root_.GlobalTheory.T.two_mul_defBound_sub_le_muCore_of_gramAt hP
  refine Closed.imp ((hA.and (hG.and (_root_.GlobalTheory.CovTop.WtShape.wtN_z.and _root_.GlobalTheory.T.weight_dimension_log_bound'))).and hc) fun Fm CH _ h => ?_
  obtain ⟨⟨⟨CA, hCA, xA, eA⟩, ⟨CG, -, xG, eG⟩, ⟨CW, -, xW, eW⟩, ⟨C3, hC3, x3, e3⟩⟩, ⟨C₀, hC₀, x0, h1⟩⟩ := h
  refine ⟨CA + C3 + C₀, by positivity, max (max (max xA xG) (max xW x3)) x0,
    fun x hx hle' ι p hp i hi => ?_⟩
  have hle := le_trans (le_max_left _ _) hle'
  have l0 : x0 ≤ x := le_trans (le_max_right _ _) hle'
  have lA : xA ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hle
  have lG : xG ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hle
  have lW : xW ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hle
  have l3 : x3 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hle
  have a := eA x hx lA ι p hp i
  have g := eG x hx lG ι p hp i
  have w := eW x hx lW ι p hp i
  have s := e3 x hx l3 ι p hp i hi
  have c := h1 x hx l0 ι p hp i hi g
  have hk := (Fm.D x ι).R.m_add_three_le_k
  have q0 : (dat p i).q = 0 := by
    rw [w.sig.2.1]; unfold Ranks.sigW; simp only; omega
  have p1 : 1 ≤ (dat p i).p := by
    rw [w.sig.1]; unfold Ranks.sigW; simp only; omega
  have ar := GlobalTheory.T.two_definiteBound_ge_anchoredMainTerm_sub_crude_errors _ _ (dat p i) (wtA (p.κ i)) (p.κ i).n ((Fm.D x ι).R.k - 1)
    (ofRecord (Fm.D x ι) (Fm.L x ι) p.Del p.h0).logOm q0 p1 (p.κ i).n_even
  have a1 := a.1
  simp only [q0, Nat.cast_zero, sub_zero] at a1
  rw [abs_le] at a1
  unfold LowAt
  linarith [a1.1, a1.2]
end GlobalTheory.CovTop.DefLow
end
end
section
open GlobalTheory.CovTop GlobalTheory.BigTop

theorem _root_.GlobalTheory.T.lowDef_of_gram_of_anchor : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → _root_.GlobalTheory.CovTop.GramCondition → _root_.GlobalTheory.CovTop.AnchorCondition → _root_.GlobalTheory.CovTop.LowDefectCondition := by
  first | exact @_root_.GlobalTheory.CovTop.DefLow.covering_low_defect_alt | exact _root_.GlobalTheory.CovTop.DefLow.covering_low_defect_alt | (intros; apply _root_.GlobalTheory.CovTop.DefLow.covering_low_defect_alt <;> assumption)
end
end
end
end
