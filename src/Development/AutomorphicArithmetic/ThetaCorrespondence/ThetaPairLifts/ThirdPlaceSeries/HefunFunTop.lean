module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieTwRecOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteTOf
public import Formalism.LocalToGlobal.Divisibility.TupUsed
public import Formalism.SharpRestriction.Divisibility.SlopeExcess.HeightBoundOfComponentBounds
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseRankEqOfRealisation
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GammaSizeOfParameters
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HefunPointB
public import Formalism.LocalToGlobal.Divisibility.ArithClauseRec
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalRingCardinality.DataAmbForm
import Formalism.LocalRingCardinality.SpanPowerMembership.NZTypeD
public import Formalism.LocalToGlobal.ClassOfRecordOfChoice
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.HilbertRowConditions.IsHilbertCF
import Formalism.LocalToGlobal.IndefiniteForms.IndefSide
import Formalism.LocalToGlobal.IndefiniteReal.IndefiniteWeightData
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Formalism.LocalToGlobal.IndefiniteRealisationChoice
import Formalism.LocalToGlobal.SiegelLatticeTheory.PtEquivApply
import Formalism.MirabolicMackeyTheory.StatementT
import Formalism.QuotientMetricDivisors.Statement
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.LocalToGlobal.Divisibility.EigenvalueSumLeClosedOf
import Formalism.LocalToGlobal.PtKOfReal
public import Formalism.SharpRestriction.ParamsHeightRankConstant
import Mathlib.Tactic.Linter.Style
public import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLm
public import Formalism.SharpRestriction.Divisibility.ClosedSizeLink.AdmissibleFamilyOfThreshold
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.LocalRingCardinality.PrincipalHermitianLattice
public import Formalism.SharpRestriction.Divisibility.SlopeExcess.FamilyStatementOfScaledLemmas
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.SharpFunctions.FunTop

section

@[expose] public section

noncomputable section

open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.Pk Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S

namespace Formalism.L2.DIV.FunSharpTop

theorem pow_absorb (x B l CH : ℝ) (hx : 56 ≤ x) (hB : 1 ≤ B) (hl : l ≤ 4 * B) :
    x ^ CH * B + 14 * l ≤ x ^ (max CH 1 + 1) * B := by
  have hx1 : 1 ≤ x := by linarith
  have hM : x ^ CH ≤ x ^ (max CH 1) := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_left _ _)
  have hM1 : x ≤ x ^ (max CH 1) := by
    calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ (max CH 1) := Real.rpow_le_rpow_of_exponent_le hx1 (le_max_right _ _)
  have hsplit : x ^ (max CH 1 + 1) = x ^ (max CH 1) * x := by
    rw [Real.rpow_add (by linarith), Real.rpow_one]
  rw [hsplit]
  have hB0 : 0 ≤ B := by linarith
  have hPx : x ^ CH + 56 ≤ x ^ (max CH 1) * x := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x ^ (max CH 1)) (by linarith : (0 : ℝ) ≤ x - 56)]
  have h2 := mul_le_mul_of_nonneg_right hPx hB0
  nlinarith

theorem third_of (d Q : ℝ) (h0 : 0 ≤ d) (h1 : 3 * d * Q ≤ 1) (h2 : 1 ≤ Q) : d ≤ 1 / 3 := by nlinarith

variable {𝒜 : FamClass} {sel : Formalism.L2.TSel 𝒜} {selS : SelS 𝒜 sel} {selP : BaseLevelCompatibleSelection 𝒜 sel} {selDH : SelDH 𝒜 sel}
  {selC : ColumnCompatibleSelection 𝒜 sel selP} {selK : SelK 𝒜 sel}

end Formalism.L2.DIV.FunSharpTop

end
end
end

-- Source module: Formalism.LocalToGlobal.Divisibility.DivisibilityRemainder.SharpFunctions.MidExp

section

@[expose] public section

noncomputable section

namespace Formalism.L2.DIV.FunSharpTop

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk

def reExp (f : List ℝ → ℝ) (l : List ℝ) : List ℝ := l.take 16 ++ f (l.take 16) :: l.drop 17

theorem reExp_eq {eps : ℝ} (Fm : FamP eps) (f : List ℝ → ℝ) (CH : ℝ) :
    reExp f (Fm.cOut ++ Fm.cMid CH) = Fm.cOut ++ Fm.cMid (f Fm.cOut) := rfl

def sharpThresholdTransform (K : TransportedAlt) : TransportedAlt := ⟨K.pre, K.t, K.mid, fun l => K.last (reExp K.mid l)⟩

theorem large_of_large_thresholds {eps : ℝ} {Fm : FamP eps} {K : TransportedAlt} {CH : ℝ} (h : Fm.Large (sharpThresholdTransform K) CH) :
    Fm.Large K (K.mid Fm.cOut) := by
  unfold FamP.Large at h ⊢
  obtain ⟨h1, -, h3, h4⟩ := h
  refine ⟨h1, trivial, fun c hc => ?_, fun c hc => ?_⟩
  · rcases List.mem_cons.1 hc with rfl | hc'
    · exact le_rfl
    · exact h3 c (List.mem_cons_of_mem _ hc')
  · have e := h4 c hc
    have e2 : (sharpThresholdTransform K).last (Fm.cOut ++ Fm.cMid CH) = K.last (Fm.cOut ++ Fm.cMid (K.mid Fm.cOut)) := by
      show K.last (reExp K.mid (Fm.cOut ++ Fm.cMid CH)) = _
      rw [reExp_eq]
    rw [e2] at e
    exact e

theorem closed_atMid {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 P) :
    ∃ f : ℝ → List ℝ → ℝ, Closed 𝒞 fun {eps} Fm _ => P Fm (f eps Fm.cOut) := by
  classical
  unfold Closed at h
  obtain ⟨ε1, hε1, hK⟩ := h
  refine ⟨fun eps l => if hh : 0 < eps ∧ eps ≤ ε1 then (Classical.choose (hK eps hh.1 hh.2)).mid l else 0, ?_⟩
  unfold Closed
  refine ⟨ε1, hε1, fun eps he he1 => ⟨sharpThresholdTransform (Classical.choose (hK eps he he1)), fun Fm CH hC hL => ?_⟩⟩
  dsimp only
  rw [dite_eq_left ⟨he, he1⟩]
  exact Classical.choose_spec (hK eps he he1) Fm _ hC (large_of_large_thresholds hL)

theorem closed_largeE {𝒞 : FamClass} {P Q : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (K0 : ℝ → TransportedAlt) (hP : Closed 𝒞 P)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), Fm.Large (K0 eps) CH → P Fm CH → Q Fm CH) : Closed 𝒞 Q := by
  unfold Closed at hP ⊢
  obtain ⟨ε1, hε1, hK⟩ := hP
  refine ⟨ε1, hε1, fun eps he he1 => ?_⟩
  obtain ⟨K, hK'⟩ := hK eps he he1
  refine ⟨⟨max K.pre (K0 eps).pre, K.t, fun l => max (K.mid l) ((K0 eps).mid l),
    fun l => max (K.last l) ((K0 eps).last l)⟩, fun Fm CH hC hL => ?_⟩
  unfold FamP.Large at hL
  obtain ⟨h1, -, h3, h4⟩ := hL
  have hA : Fm.Large K CH := by
    unfold FamP.Large
    exact ⟨fun c hc => le_trans (le_max_left _ _) (h1 c hc), trivial,
      fun c hc => le_trans (le_max_left _ _) (h3 c hc), fun c hc => le_trans (le_max_left _ _) (h4 c hc)⟩
  have hB : Fm.Large (K0 eps) CH := by
    unfold FamP.Large
    exact ⟨fun c hc => le_trans (le_max_right _ _) (h1 c hc), trivial,
      fun c hc => le_trans (le_max_right _ _) (h3 c hc), fun c hc => le_trans (le_max_right _ _) (h4 c hc)⟩
  exact h Fm CH hB (hK' Fm CH hC hA)

end Formalism.L2.DIV.FunSharpTop

end
end
end

-- Source module: Formalism.SharpRestriction.Divisibility.HookProducts.LambdaZeroLeFourB

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.DIV.HookProducts.FunSharp

open Formalism.BasicNotions Formalism.MainNotions

theorem lambda_zero_le_four_b {D : D7} (L : SizeData₂ D) (hS : SizesAt L) : lam0 D ≤ 4 * L.sc.b := by
  obtain ⟨-, -, hK, hKR, hT, -, -, -, -, -, -, -, -, hEta, hNodes, -, -, -, -, -, hG, -, -⟩ := hS
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hθ : 0 ≤ szTh L := by unfold szTh; have := L.sc.eps_pos; positivity
  have hxθ : 1 ≤ L.sc.x ^ szTh L := Real.one_le_rpow hx1.le hθ
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb0 : 0 ≤ L.sc.b := by unfold Scale.b; exact (Real.exp_pos _).le
  set A : ℝ := L.sc.x ^ szTh L * L.sc.L with hA
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  set F : ℝ := (D.R.f : ℝ) with hFdef
  set R : ℝ := (D.R.r : ℝ) with hRdef

  have hF1 : 1 ≤ F := by
    have h12 : A ≤ F * Real.log D.R.k := hKR.2.2.2.2.2.2.2.2.2.2.2.1
    by_contra hc
    have hf0 : D.R.f = 0 := by
      have : (D.R.f : ℝ) < 1 := not_le.mp hc
      exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast this)
    rw [hFdef, hf0] at h12
    simp at h12
    linarith

  have hR1 : 1 ≤ R := by
    have hfr : F ≤ R ^ 2 := hKR.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hR0 : 0 ≤ R := by positivity
    nlinarith

  have hT1 : 1 ≤ (D.R.t : ℝ) := hT.1
  have hK1 : 1 ≤ (D.R.k : ℝ) := by
    have h := hK.1
    have hp : 0 < L.sc.x ^ (9 / 2 + 10 * L.sc.eps - szTh L) := Real.rpow_pos_of_pos (by linarith) _
    have hk0 : 0 < (D.R.k : ℝ) := lt_of_lt_of_le hp h
    have : 0 < D.R.k := by exact_mod_cast hk0
    exact_mod_cast this

  have hη1 : 1 ≤ L.etaSz := hT1.trans hEta.1
  have hden : 1 ≤ (D.R.t : ℝ) ^ 3 * F * (D.R.k : ℝ) ^ 3 := by
    have h1 : 1 ≤ (D.R.t : ℝ) ^ 3 := one_le_pow₀ hT1
    have h2 : 1 ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hK1
    have h3 : 1 ≤ (D.R.t : ℝ) ^ 3 * F := by nlinarith
    nlinarith
  have hηb : L.etaSz ≤ L.sc.b := hEta.2.1.trans (div_le_self hb0 hden)
  have hηm : L.etaSz / D.R.m ≤ L.etaSz := by
    rcases Nat.eq_zero_or_pos D.R.m with h | h
    · rw [h, Nat.cast_zero, div_zero]; linarith
    · exact div_le_self (by linarith) (by exact_mod_cast h)
  have hQ : L.sc.x ^ szTh L * R ^ 19 * F ^ 5 * L.sc.L ≤ L.sc.b :=
    (hNodes.2.2.1.trans hηm).trans hηb

  have hF5 : F ≤ F ^ 5 := le_self_pow₀ hF1 (by norm_num)
  have hR19 : R ^ 2 ≤ R ^ 19 := pow_le_pow_right₀ hR1 (by norm_num)
  have hFR : F * R ^ 2 ≤ F ^ 5 * R ^ 19 := mul_le_mul hF5 hR19 (by positivity) (by positivity)
  have hQ' : F * R ^ 2 * A ≤ L.sc.b := by
    have : F * R ^ 2 * A ≤ F ^ 5 * R ^ 19 * A := mul_le_mul_of_nonneg_right hFR (by linarith)
    have e : F ^ 5 * R ^ 19 * A = L.sc.x ^ szTh L * R ^ 19 * F ^ 5 * L.sc.L := by rw [hA]; ring
    linarith
  have hFR0 : 0 ≤ F * R ^ 2 := by positivity
  have hFRb : F * R ^ 2 ≤ L.sc.b := le_trans (le_mul_of_one_le_right hFR0 hA1) hQ'

  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (1 : ℝ) ≤ D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).one_lt.le
  have hlog0 : 0 ≤ Real.log (2 * (D.host.g 0 : ℝ)) := Real.log_nonneg (by linarith)
  have hY : ∀ i, (D.host.g i : ℝ) ≤ 2 * (D.host.g 0 : ℝ) := fun i => (hG i 0).2.1
  have h0 := Formalism.MainNotions.DIV.Proofs.ScaledLatticeNorms.scaled_lattice_nonzero_holds D (D.host.g 0 : ℝ) hY
  have hlog : Real.log (2 * (D.host.g 0 : ℝ)) ≤ 1 + A := by
    rw [Real.log_mul (by norm_num) hg0.ne']
    have h2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
    have h3 : Real.log (D.host.g 0 : ℝ) ≤ A := (hG 0 0).2.2
    linarith
  calc lam0 D ≤ 2 * F * R ^ 2 * Real.log (2 * (D.host.g 0 : ℝ)) := h0
    _ ≤ 2 * F * R ^ 2 * (1 + A) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 * (F * R ^ 2) + 2 * (F * R ^ 2 * A) := by ring
    _ ≤ 4 * L.sc.b := by linarith

end Formalism.MainNotions.DIV.HookProducts.FunSharp
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HefunFunTop

section

@[expose] public section



section
noncomputable section
open Module NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.Pk Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.L2 Formalism.L2.Indef Formalism.L2.DIV Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.Cx Formalism.L2.Top3 Formalism.L2.Top4 Formalism.L2.RowDataTransport Formalism.L2.DIV.Arith4S
namespace Formalism.L2.DIV.FunSharpTop
variable {𝒜 : FamClass} {sel : _root_.Formalism.L2.TwistSelection 𝒜} {selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel} {selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel} {selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel}
  {selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP} {selK : _root_.Formalism.L2.Top4.KernelSelection 𝒜 sel}
theorem funSharp_fam_alt [∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x), IsTotallyComplex (Fm.D x i).what₂.LL]
    (selI : _root_.Formalism.L2.Top4.IndefiniteRealisationChoice' 𝒜 sel selS selP selDH selC selK) (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel selI)
    (DefRows4 : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x) (C CH : ℝ), Prop)
    (OneMapRow : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x), Prop)
    (hR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I)
    {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (CH : ℝ) (hCsz : 0 ≤ Fm.Csz) (hDG : Formalism.MainNotions.DGamSize Fm)
    (hRows : _root_.Formalism.L2.Top4.RowsAtSelAlt sel selI DefRows4 OneMapRow Fm hc CH) (hOne : _root_.Formalism.L2.Top4.EventuallyAlongSelection sel Fm hc (OneMapRow Fm hc)) (hN : DIVinN Fm) :
    ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ (max CH 1 + 1) * (Fm.L x i).sc.b := by
  obtain ⟨Cd, x4, hFDG⟩ := hDG
  obtain ⟨C, hC, x1, hr⟩ := hRows
  obtain ⟨x2, ho⟩ := hOne
  refine ⟨max (max (max x1 x2) (max x4 (x0F eps Fm.Ct Fm.Cc CH (ceF C 0 (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)))))
    (max (sel Fm hc).1 56), fun x hx0 hx i => ?_⟩
  have hx1 : x1 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx0
  have hx2 : x2 ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx0
  have hx4 : x4 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx0
  have hx5 : x0F eps Fm.Ct Fm.Cc CH (ceF C 0 (2 + 9 * max Cd 0) (c0F Fm.Csz Fm.Cc Fm.CYL Fm.Ct)) ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx0
  have h : (sel Fm hc).1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx0
  have g56 : (56 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx0
  obtain ⟨ra, -⟩ := hr x hx h hx1 i
  obtain ⟨prows, hsep⟩ := hPA Fm hc x hx h i
  have hok1 := (selC Fm hc x hx h i).ok1
  have hP : CovolumeOntoIsometryConditions (selI Fm hc x hx h i).Rl (selI Fm hc x hx h i).F (selI Fm hc x hx h i).sEE (hkCan (selP Fm hc x hx h i).1.A3) C CH :=
    { toPrimRows3 := prows, w1 := ra.w1, covol := ra.covol, onto := ra.onto hN, lamLow := ra.lamLow (ho x hx h hx2 i),
      seeIso := ra.seeIso, miStar := ra.miStar, fun0 := ra.fun0 hN }
  have hS := Fm.sizes x hx i
  have hFD : FactDGam (Fm.D x i) (max Cd 0) := J.factDGam_mono (hFDG x hx4 i) (le_max_left _ _)
  have hDGp := _root_.Formalism.L2.DIV.Cons.gamma_size_of_sizeData_alt (selP Fm hc x hx h i).2 (_root_.Formalism.L2.Top4Wire2.finite_T_of_squareIntegrableColumns (selC Fm hc x hx h i))
    hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.1 (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 (Fm.L x i).Nc (cloudConstant_nonneg (Fm.L x i))
    (max Cd 0) (le_max_right _ _) hFD
  have eCc : (Fm.L x i).Cc = Fm.Cc := Fm.Cc_eq x i
  have eCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have eCY : (Fm.params x hx i).CYL = Fm.CYL := Fm.params_CYL x hx i
  have hxL : x0F (Fm.L x i).sc.eps (Fm.L x i).Ct (Fm.L x i).Cc CH
      (ceF C 0 (2 + 9 * max Cd 0) (c0F Fm.Csz (Fm.L x i).Cc (Fm.params x hx i).CYL (Fm.L x i).Ct)) ≤ (Fm.L x i).sc.x := by
    rw [Fm.L_eps x i, eCt, eCc, eCY, Fm.L_x x i hx]
    exact hx5
  obtain ⟨lam0', Sw, C1, H, dg, hdg, hdvd, hA⟩ := arithClause_rec (Fm.L x i) (selDH Fm hc x hx h i).1.1 (selDH Fm hc x hx h i).1.2 hS (selDH Fm hc x hx h i).2.1 (selDH Fm hc x hx h i).2.2 (Fm.params x hx i) (Fm.ex x hx i).fdef
    (Fm.ex x hx i).kap_def (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.tied.div.grp.card (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps (selP Fm hc x hx h i).1.ψs (selC Fm hc x hx h i).c.face (selC Fm hc x hx h i).Sp _ C CH Fm.Csz 0
    (2 + 9 * max Cd 0) (_root_.Formalism.L2.Top4Wire2.finite_T_of_squareIntegrableColumns (selC Fm hc x hx h i)) hDGp hC hCsz hxL (_root_.Formalism.L2.RowDataTransport.packageOfPrimitiveLinks (selI Fm hc x hx h i) hok1 hsep C CH hP ra.pass)
  obtain ⟨Qq, hq0, hq1, hq2, -⟩ := (hA (Fm.D x i).u₀).q
  have key := _root_.Formalism.L2.DIV.FunSharpTop.funSharp_pt_alt (selI Fm hc x hx h i) hok1 hsep C CH hP ra.pass (hR Fm hc x hx h i) ra.kap hq0
    (third_of _ _ hq0 hq1 hq2)
  have hla : Formalism.BasicNotions.lam0 (Fm.D x i) = Real.log (Fintype.card (selP Fm hc x hx h i).1.Gp) := by
    unfold Formalism.BasicNotions.lam0
    rw [(selP Fm hc x hx h i).1.tied.div.grp.card]
  have key' : (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
      (Fm.L x i).sc.x ^ CH * (Fm.L x i).sc.b + 14 * Formalism.BasicNotions.lam0 (Fm.D x i) := by
    rw [hla]
    exact key
  have hB1 : 1 ≤ (Fm.L x i).sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (by unfold Scale.L; exact Real.rpow_nonneg (by linarith [(Fm.L x i).sc.one_lt_alt]) _)
  refine key'.trans (pow_absorb _ _ _ CH ?_ hB1 (Formalism.MainNotions.DIV.HookProducts.FunSharp.lambda_zero_le_four_b (Fm.L x i) hS))
  rw [Fm.L_x x i hx]
  exact g56
theorem closed_funSharp_alt (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows (selB Fm hc x hx h i))
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH) :
    ∃ CF0 : ℝ → List ℝ → ℝ, Closed (D3 3 𝒜) fun {eps} Fm _ => ∀ _ : D3 3 𝒜 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm → DIVinN Fm →
      ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ CF0 eps Fm.cOut * (Fm.L x i).sc.b := by
  have : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (i : Fm.Ix x), NumberField.IsTotallyComplex (Fm.D x i).what₂.LL :=
    fun Fm x i => (Fm.D x i).tcLL
  have hDivR : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3 (Fm.D x i) (selP Fm hc x hx h i).1.A3 (selP Fm hc x hx h i).1.P0 (selP Fm hc x hx h i).1.ψ0 (selP Fm hc x hx h i).1.Ps
        (selP Fm hc x hx h i).1.ψs (selP Fm hc x hx h i).1.Zs (selP Fm hc x hx h i).1.S0 (selP Fm hc x hx h i).1.S1 (Fm.ex x hx i).p0 (selP Fm hc x hx h i).1.C (selP Fm hc x hx h i).1.NuC (selP Fm hc x hx h i).1.I :=
    fun Fm hc x hx h i => (hDivG Fm hc x hx h i).toRows (_root_.Formalism.IndefR.LevelRealisationRankEquality.tup_all_used_of_realisation (selB Fm hc x hx h i).Q)
  have hCsz : Closed (D3 3 𝒜) fun Fm _ => 0 ≤ Fm.Csz := Formalism.MainNotions.DIV.closed_Csz_ge_fn (D3 3 𝒜) fun _ => 0
  obtain ⟨f, hf⟩ := closed_atMid (rRows.and hCsz)
  refine ⟨fun e l => max (f e l) 1 + 1, hf.imp fun Fm _ _ hh hc _ hD hN => ?_⟩
  exact _root_.Formalism.L2.DIV.FunSharpTop.funSharp_fam_alt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) hPA _ (_root_.Formalism.L2.Top4.SingleMapCondition selB) hDivR Fm (d3_a hc) _ hh.2 hD (hh.1 hc)
    ⟨0, fun x hx h _ i j => (hRB Fm (d3_a hc) x hx h i).oneMap j⟩ hN
theorem closed_funSharp_thr_alt (𝒜 : FamClass)
    (sel : _root_.Formalism.L2.TwistSelection 𝒜)
    (selS : _root_.Formalism.L2.Top4.SelectionSpectralCondition 𝒜 sel)
    (selP : _root_.Formalism.L2.Top4.BaseLevelTiedChoiceAlt 𝒜 sel)
    (selDH : _root_.Formalism.L2.Top3.SelectionDefiniteHeightCondition 𝒜 sel)
    (selC : _root_.Formalism.L2.Top4.ColumnChoiceCompatibleSelection 𝒜 sel selP)
    (selB : _root_.Formalism.L2.Top4.SelectionBundle 𝒜 sel selS selP selDH selC)
    (hRB : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      _root_.Formalism.IndefR.IndefiniteRealisationBoundedRows (selB Fm hc x hx h i))
    (hPA : _root_.Formalism.L2.Top4.AllRealisationsPrimitive sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB))
    (hDivG : ∀ {eps : ℝ} (Fm : FamP eps) (hc : 𝒜 Fm) (x : ℝ) (hx : Fm.x1 < x) (h : (sel Fm hc).1 ≤ x) (i : Fm.Ix x),
      Formalism.L2.DIV.DivRows3G (selP Fm hc x hx h i).1)
    (rRows : Closed (D3 3 𝒜) fun Fm CH => ∀ hc : D3 3 𝒜 Fm, _root_.Formalism.L2.Top4.RowsAtSelAlt sel (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) (fun Fm hc x hx h i C CH => _root_.Formalism.L2.Top4Wire2.DefRowsFAlt (_root_.Formalism.L2.Top4.indefiniteRealisationChoiceOfSelection selB) Fm hc x hx h i C CH) (_root_.Formalism.L2.Top4.SingleMapCondition selB)
        Fm (d3_a hc) CH)
    (Eb Ec : List ℝ → ℝ) :
    Closed (D3 3 𝒜) fun Fm CH => ∀ _ : D3 3 𝒜 Fm, TuSize Fm → Formalism.MainNotions.DGamSize Fm →
      ∃ CF0 : List ℝ → ℝ, Fm.Large (Formalism.MainNotions.DIV.Proofs.thrHH Eb Ec CF0) CH ∧ (DIVinN Fm →
      ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + DV.meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ CF0 Fm.cOut * (Fm.L x i).sc.b) := by
  obtain ⟨CF0, h⟩ := _root_.Formalism.L2.DIV.FunSharpTop.closed_funSharp_alt 𝒜 sel selS selP selDH selC selB hRB hPA hDivG rRows
  exact closed_largeE (fun e => Formalism.MainNotions.DIV.Proofs.thrHH Eb Ec (CF0 e)) h
    fun {eps} Fm CH hL hP hc hT hD => ⟨CF0 eps, hL, hP hc hT hD⟩
end Formalism.L2.DIV.FunSharpTop
end
end
end
end
