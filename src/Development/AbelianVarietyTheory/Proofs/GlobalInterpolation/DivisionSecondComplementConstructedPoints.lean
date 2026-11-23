module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DivisionSecondComplementAtConstructedPoints
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Formalism.SharpRestriction.ParamsHeightRankConstant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDegreeCountAlongFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleOffTypeFamilyBoundStatement
public import Formalism.LocalToGlobal.GlobalTheory.PlacesP
public import Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLb
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPrimesLossLogSumAdmissibleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagonalRamifiedBoundAlongFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeSizesLeBudgetFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHeightOneIdealIffAdditiveValuationPos
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
public import Formalism.LocalRingCardinality.IntCastDvdOfDvdIntegers
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral

-- Source module: Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLbud

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

variable {D : D7} {L : SizeData₂ D}

theorem gammaDiscriminant_budget_of_sizes {Cn cL CG : ℝ} (hcL : 1 ≤ cL) (hCG : 0 ≤ CG) (hN : NumsL D L Cn cL) (hG : FactDGam D CG) :
    WeightDegreeSizes.StabiliserLogBound D L (4 * CG) := by
  unfold WeightDegreeSizes.StabiliserLogBound
  unfold FactDGam at hG
  intro u
  have hNu := hN u
  unfold flipTwoThree.Nums at hNu
  obtain ⟨hb0, -, -, -, -, hb', -, -, -, -, hNL, -, -, hx2, -, -⟩ := hNu
  have hfk : D.R.f ≤ D.R.k := by
    unfold Ranks.f
    exact D.R.f_le_k
  have hmf : D.R.m ≤ D.R.f := by
    unfold Ranks.f
    exact D.R.m_le_f
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hkN : D.R.k ≤ D.R.N D.R.m := by
    unfold Ranks.N
    omega
  have hfN : (D.R.f : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hfk.trans hkN
  have hf2 : (2 : ℝ) ≤ D.R.f := by exact_mod_cast hm2.trans hmf
  have hm2r : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hN0 : (0 : ℝ) < D.R.N D.R.m := by linarith
  have hx1 := L.sc.one_lt_alt
  have hLr : 1 ≤ L.sc.L := by
    unfold Scale.L
    exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hbb : L.sc.x * L.sc.b / L.sc.x = L.sc.b := by
    field_simp
  rw [hbb] at hb'
  have hT0 : 0 ≤ Real.log ((flipTwoThree.Tu D u : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hNL' : (D.R.N D.R.m : ℝ) * L.sc.L ≤ L.sc.b := by
    have : (D.R.N D.R.m : ℝ) * L.sc.L ≤ (D.R.N D.R.m : ℝ) * (cL * L.sc.L) := by
      apply mul_le_mul_of_nonneg_left _ hN0.le
      nlinarith
    linarith
  have hlogN : Real.log (D.R.N D.R.m : ℝ) ≤ L.sc.L := by
    have hNb : (D.R.N D.R.m : ℝ) ≤ Real.exp L.sc.L := by
      have : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * L.sc.L := le_mul_of_one_le_right hN0.le hLr
      have hb : L.sc.b = Real.exp L.sc.L := rfl
      linarith
    calc Real.log (D.R.N D.R.m : ℝ) ≤ Real.log (Real.exp L.sc.L) := Real.log_le_log hN0 hNb
      _ = L.sc.L := Real.log_exp _
  have hlogf : Real.log (D.R.f : ℝ) ≤ Real.log (D.R.N D.R.m : ℝ) := Real.log_le_log (by linarith) hfN
  have hlog : Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.sc.L := by
    rw [Real.log_mul (by linarith) hN0.ne']
    linarith
  have hB0 : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := rfl
  have hb0' : 0 < L.sc.b := Real.exp_pos _
  have key : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤ 2 * L.B0 := by
    have h1 : (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * Real.log ((D.R.f : ℝ) * (D.R.N D.R.m : ℝ)) ≤
        (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) * (2 * L.sc.L) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have h2 : (D.R.f : ℝ) * ((D.R.N D.R.m : ℝ) * L.sc.L) ≤ (D.R.f : ℝ) * L.sc.b :=
      mul_le_mul_of_nonneg_left hNL' (by positivity)
    have h3 : (D.R.f : ℝ) * L.sc.b * 1 ≤ (D.R.f : ℝ) * L.sc.b * ((D.R.m : ℝ) * L.sc.L) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    rw [hB0]
    nlinarith
  have hG' := hG u
  have := mul_le_mul_of_nonneg_left key hCG
  nlinarith

end Formalism.MainNotions.J

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegConstDiscriminantTermLeBudgetFamilyA

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

theorem exists_nonneg_const_discriminant_term_le_budget_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm →
    ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x,
      Formalism.MainNotions.WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _ hT hG
  obtain ⟨Cn, hN⟩ := J.numsL_wtsL_fam Fm hT (Formalism.L2.GlobalTheoryTheory.Places.dlSize eps Fm)
  obtain ⟨x0, hN⟩ := hN Cn le_rfl 3 le_rfl
  obtain ⟨CG, x1, hG⟩ := hG
  refine ⟨4 * max CG 0, max x0 x1, by positivity, fun x hx _ i => ?_⟩
  exact J.gammaDiscriminant_budget_of_sizes (by norm_num) (le_max_right _ _) (hN x (le_trans (le_max_left _ _) hx) i).1
      (J.factDGam_mono (hG x (le_trans (le_max_right _ _) hx) i) (le_max_left _ _))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonnegConstDiscriminantTermLeBudgetFamilyAStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

theorem _root_.GlobalTheory.T.exists_const_stabiliserLog_bound_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.StabiliserLogBound (Fm.D x i) (Fm.L x i) C := by
  first | exact @GlobalTheory.exists_nonneg_const_discriminant_term_le_budget_family | exact GlobalTheory.exists_nonneg_const_discriminant_term_le_budget_family | (intros; apply GlobalTheory.exists_nonneg_const_discriminant_term_le_budget_family <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeValuationSumEqLogGapFamily

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.TypeValNN

theorem typePrime_valuationSum_eq_logGap_all (D : D7) (X : ErrX D) : Formalism.MainNotions.WeightDegreeSizes.NormDecompositionCond D X := by
  intro i u j _ S hS
  have h1 : ∀ w ∈ S, SizeData₂.sz w (vNN X i u j w) =
      ∑ τ : D.what₂.Tau, nuAbs D u j τ * (2 * SizeData₂.lwP w * (vAdd (D.plEq w) (tauPib X i τ) : ℝ)) := by
    intro w _
    have he : (D.what₂.places.ramIdx w : ℝ) ≠ 0 := by exact_mod_cast (D.what₂.places.ramIdx_pos w).ne'
    unfold SizeData₂.sz vNN
    rw [mul_div_cancel₀ _ he, Finset.mul_sum]
    exact Finset.sum_congr rfl fun τ _ => by ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.mul_sum, GlobalTheory.TypeLoss.sum_half D _ (D.host.g_prime i) S hS _ (GlobalTheory.TypeLoss.tauPib_norm X i τ)]

theorem typePrime_valuationSum_eq_logGap_family : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x),
    Formalism.MainNotions.WeightDegreeSizes.NormDecompositionCond (Fm.D x i) (Fm.ex x hx i).errX :=
  fun Fm x hx i => typePrime_valuationSum_eq_logGap_all (Fm.D x i) (Fm.ex x hx i).errX

end GlobalTheory.TypeValNN
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePrimeValuationSumEqLogGapFamilyStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

theorem _root_.GlobalTheory.T.normDecompositionCond_famP : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x), Formalism.MainNotions.WeightDegreeSizes.NormDecompositionCond (Fm.D x i) (Fm.ex x hx i).errX := by
  first | exact @GlobalTheory.TypeValNN.typePrime_valuationSum_eq_logGap_family | exact GlobalTheory.TypeValNN.typePrime_valuationSum_eq_logGap_family | (intros; apply GlobalTheory.TypeValNN.typePrime_valuationSum_eq_logGap_family <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleComplementTwoAlongFamily

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

theorem familySecondComplementInputs_of_tuSize_of_dGamSize : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm →
    Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm := by
  intro eps Fm h0 h1 hT hG
  obtain ⟨Cdeg, xd, -, hdeg⟩ := GlobalTheory.T.exists_degreeCountBound_of_eps_lt_one_div_52 Fm h0 h1
  obtain ⟨Cg, xg, hCg, hsz⟩ := GlobalTheory.T.typePrime_sizes_le_budget_family Fm h0 h1 hG Cdeg
  obtain ⟨CT, xT, -, hoT⟩ := GlobalTheory.T.admissible_off_type_family_bound Fm h0 h1 hT
  obtain ⟨CG, xG, -, hoG⟩ := GlobalTheory.T.exists_const_stabiliserLog_bound_along_family Fm h0 h1 hT hG
  obtain ⟨Cd, xD, -, hoD⟩ := GlobalTheory.T.offDiagonalRamified_bound_along_family' Fm h0 h1
  obtain ⟨CI, xI, -, hoI⟩ := GlobalTheory.T.inertPrimeLossBound_eventually Fm h0 h1
  refine ⟨Cdeg, Cg, CT, CG, Cd, CI, max xd (max xg (max xT (max xG (max xD xI)))), hCg, ?_⟩
  intro x hx0 hx i
  have a1 : xd ≤ x := (le_max_left _ _).trans hx0
  have r1 := (le_max_right _ _).trans hx0
  have a2 : xg ≤ x := (le_max_left _ _).trans r1
  have r2 := (le_max_right _ _).trans r1
  have a3 : xT ≤ x := (le_max_left _ _).trans r2
  have r3 := (le_max_right _ _).trans r2
  have a4 : xG ≤ x := (le_max_left _ _).trans r3
  have r4 := (le_max_right _ _).trans r3
  have a5 : xD ≤ x := (le_max_left _ _).trans r4
  have a6 : xI ≤ x := (le_max_right _ _).trans r4
  exact ⟨fun u j h => (Fm.D x i).T_ne_g u j h.symm, GlobalTheory.T.normDecompositionCond_famP Fm x hx i, hdeg x a1 hx i, hsz x a2 hx i,
    hoT x a3 hx i, hoG x a4 hx i, hoD x a5 hx i, hoI x a6 hx i⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleComplementTwoAlongFamilyStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

theorem _root_.GlobalTheory.T.admissibleComplementTwo_along_family : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → DGamSize Fm → Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm := by
  first | exact @GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize | exact GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize | (intros; apply GlobalTheory.familySecondComplementInputs_of_tuSize_of_dGamSize <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleConstantsClosedUnderSizeBounds

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

theorem admissibleConstants_closed_under_sizeBounds : ∀ (𝒞 : FamClass), (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm ∧ DGamSize Fm) →
    Closed 𝒞 (fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm) := by
  intro 𝒞 h𝒞
  refine ⟨1 / 100, by norm_num, fun eps he hle => ?_⟩
  have hK : Nonempty TransportedAlt := ⟨by constructor <;> exact 0⟩
  obtain ⟨K⟩ := hK
  refine ⟨K, fun Fm _ hc _ => ?_⟩
  have hlt : eps < 1 / 52 := lt_of_le_of_lt hle (by norm_num)
  exact GlobalTheory.T.admissibleComplementTwo_along_family Fm he hlt (h𝒞 Fm hc).1 (h𝒞 Fm hc).2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DivisionSecondComplementConstructedPoints

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.ClassTwoEntries

theorem divisionSecondComplement_constructedPoints : ∀ (Bd : BdT) (Q : V4.Slot) (Lk : LkT Bd), ClassTwoEntries.DivisionSecondComplementAtConstructedPoints Q Lk := by
  intro Bd Q Lk
  exact Row0.row (Row0.of_all (Q := Q) fun 𝒜 =>
    GlobalTheory.admissibleConstants_closed_under_sizeBounds (W3 𝒜) fun _ h => ⟨h.2.2.1, h.2.2.2⟩) Lk

end GlobalTheory.Fc.ClassTwoEntries
end
end
