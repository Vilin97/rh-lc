module

public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaRunParametersAtTypePrimesProduct
public import Formalism.LocalToGlobal.ProjectiveLattices.RegularityR1ValuedPoints
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETExSt
public import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LocalFormOfWeakForm
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaleExtensionDegreeTwoConstants
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.PageRows
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Counterexamples.JetSurvey.FormAtOfClause

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaValuationTest

open Formalism.MainNotions Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.ModuliIntegralCharts.H1

variable {D : Formalism.BasicNotions.D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem phiC_nonneg (X : WeightAlgebra.PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) : 0 ≤ X.phiC la y := by
  apply Formalism.MainNotions.Gaps.T0.phiC_nonneg <;> assumption

theorem mem_Mlat (X : WeightAlgebra.PJ D B P j) (i : ℕ) (η : B.Cusp j (Formalism.L2.Pj.wEt D j i)) (h : EtVal X i η) :
    η ∈ B.Mlat j _ := by
  refine (X.Mlat_eq _ η).2 fun la y => le_trans ?_ (h la y)
  exact EReal.coe_nonneg.2 (mul_nonneg (by positivity) (phiC_nonneg X la y))

end GlobalTheory.EtaValuationTest
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtValIntegral

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaInt

theorem etVal_integral :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (i : ℕ) (η : (recB h.toLawsCore).Cusp j (wEt D j i)), (Formalism.MainNotions.ModuliIntegralCharts.H1.EtVal (recPJ h j hj) i η ↔ Formalism.L2.Pj.EtVal h j hj i η) ∧ (∀ la (y : (recPJ h j hj).Pt la), 0 ≤ (recPJ h j hj).phiC la y) ∧ (Formalism.L2.Pj.EtVal h j hj i η → IntAlg η.1 ∧ η ∈ (recB h.toLawsCore).Mlat j (wEt D j i)) := by
  intro D T h j hj i η
  refine ⟨Iff.rfl, GlobalTheory.EtaValuationTest.phiC_nonneg _, fun hv => ?_⟩
  have hm : η ∈ (recB h.toLawsCore).Mlat j (wEt D j i) :=
    GlobalTheory.EtaValuationTest.mem_Mlat (recPJ h j hj) i η hv
  refine ⟨?_, hm⟩
  have h0 := ((recPJ h j hj).Mlat_eq _ η).1 hm
  refine (nonneg_iff_of_liesTotal (T.G.liesTotal h.points_condition h.bc66 hj) η.1).2 fun la y => ?_
  exact le_of_le_of_eq (h0 la y) (recPJ_vAt_inc h j hj la y _ η)

end GlobalTheory.EtaInt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaleExtensionDegreeTwoConstantsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

theorem _root_.GlobalTheory.T.etaleExtension_degreeTwo_constants : ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D), (2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f) → ∀ (DF q : ℕ) (R0 : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → 1 ≤ q → Real.log q ≤ 70 * large₂.sc.L → ETEx h (WeightFamilies.PPv D large₂ 200000 2) (EtArch h (I2.th (E := D.host.E) q R0) (200000 * zBase large₂ ^ 2)) := by
  first | exact @GlobalTheory.EtaAn.etEx_deg_two | exact GlobalTheory.EtaAn.etEx_deg_two | (intros; apply GlobalTheory.EtaAn.etEx_deg_two <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsScalarWeightAuxiliaryFormOfRunConditions

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

namespace GlobalTheory.EtaBoundForm




theorem exists_etaOK : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → j < D.R.m → ∃ (i : ℕ) (et : (recB h.toLawsCore).Cusp j (etWt D j i)), EtaOK h j hj large₂ wL i et := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hP hjm
  obtain ⟨Q, PT, hS, -, -⟩ := id hP.page
  have what₂ := GlobalTheory.EtaAn.page_rows D large₂ H.CA hP.hyp.1 hS
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := hP.tie
  have htie : TieC ⟨1, 2, 1, 2, 1, 2, 1, 4, 7⟩ H 1 4 0 11 C2 A2 7 :=
    ⟨t1, t2, t3, t4, t5, rfl, rfl, t6, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩
  have hsupp : EtaleWeightGaps.PageSupp D large₂ (recB h.toLawsCore) C2 A2 nW
      ⟨(((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 (recB h.toLawsCore).KO), 1, 1, 1⟩ wL := by
    refine ⟨hP.p13, fun σ => ?_, hP.frd, hP.r8, hP.df⟩
    have e : σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 (recB h.toLawsCore).KO)) : (recB h.toLawsCore).KO) =
        (((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : ℂ) := by
      rw [← map_natCast σ]
      exact congrArg σ (map_natCast (algebraMap (𝓞 (recB h.toLawsCore).KO) (recB h.toLawsCore).KO) _)
    change _ ≤ Real.log ‖σ (((((D.host.g 0 * D.host.g 1) ^ DF wL : ℕ) : 𝓞 (recB h.toLawsCore).KO)) : (recB h.toLawsCore).KO)‖
    rw [e, Complex.norm_natCast, Nat.cast_pow, Real.log_pow, ← Nat.cast_mul]
    have h1 : 0 ≤ Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have h2 : (0 : ℝ) ≤ (DF wL : ℝ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg h2 h1]
  have hrun := (GlobalTheory.RunParametersAtRecord.run_at_record D _ _ j (recPJ h j hj) _ _ _ _ _ _ large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hP.hyp htie hP.page hsupp).1
  have hq1 : 1 ≤ D.host.g 0 * D.host.g 1 :=
    Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos
  have hlog : Real.log ((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ≤ 70 * large₂.sc.L := by
    have a0 : D.host.g 0 ≠ 0 := fun e => by simp [e] at hq1
    have a1 : D.host.g 1 ≠ 0 := fun e => by simp [e] at hq1
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast a0) (by exact_mod_cast a1)]
    have b0 := what₂.2.2.2.2.1 0
    have b1 := what₂.2.2.2.2.1 1
    linarith [what₂.1]
  obtain ⟨i, hi, η, ha, hb, hc, hd⟩ := GlobalTheory.T.etaleExtension_degreeTwo_constants D T h large₂ what₂ _ _ _ hrun hq1 hlog j hj.1 hjm
  exact ⟨i, η, hi, ha, hb, hc, hd, ((GlobalTheory.EtaInt.etVal_integral D T h j hj i η).2.2 hb).2⟩

end GlobalTheory.EtaBoundForm
end
end
