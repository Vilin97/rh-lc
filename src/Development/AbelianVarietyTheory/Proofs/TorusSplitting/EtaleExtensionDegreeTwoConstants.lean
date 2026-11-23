module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
public import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ArchimedeanBoundTotalConstantSize
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsCuspFormFourClausesExplicitConstantStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogCardCompUnfLe
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
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
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsNullVal
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import Mathlib.Tactic.Lemma

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsPerfectTraceIdeal

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn.PerfectTrace

open FractionalIdeal

theorem cc_eq_conj (D : D7) (z : D.host.E) : FD.cc z = D.host.conj z := by
  unfold FD.cc
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem isIntegral_of_trace (D : D7) (x : D.host.E)
    (h : ∀ a ∈ D.host.AA, ∀ b ∈ D.host.AA,
      ∃ z : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * x * a * D.host.conj b) = z) :
    IsIntegral ℤ x := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have h1ne : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    @one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _
  have key : ∀ e ∈ D.host.AA * D.host.AAbar, D.host.xi0 * x * e ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro e he
    refine FractionalIdeal.mul_induction_on (C := fun e => D.host.xi0 * x * e ∈
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) he
      (fun a ha b hb => ?_) (fun u w hu hw => ?_)
    · show D.host.xi0 * x * (a * b) ∈ _
      rw [mem_dual h1ne]
      intro c hc
      rw [mem_one_iff] at hc
      obtain ⟨c, rfl⟩ := hc
      have hca : c • a ∈ D.host.AA := (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem c ha
      obtain ⟨n, hn⟩ := h _ hca _ (conj_mem_AA D hb)
      rw [conj_conj, Algebra.smul_def] at hn
      rw [Algebra.traceForm_apply, show D.host.xi0 * x * (a * b) * algebraMap (𝓞 D.host.E) D.host.E c =
        D.host.xi0 * x * (algebraMap (𝓞 D.host.E) D.host.E c * a) * b by ring, hn]
      exact ⟨n, eq_intCast (algebraMap ℤ ℚ) _⟩
    · show D.host.xi0 * x * (u + w) ∈ _
      rw [mul_add]
      exact (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E).add_mem hu hw
  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    conv_lhs => rw [← dual_eq hP D, mul_assoc, ← mul_assoc, spanSingleton_mul_spanSingleton, mul_comm x]
    rw [spanSingleton_mul_le_iff]
    exact key
  have hJ : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.dual_ne_zero ℤ ℚ h1ne
  generalize FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = J at hle hJ
  have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x ≤ 1 := by
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x
        = J⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) x * J) := by
          rw [mul_comm _ J, ← mul_assoc, inv_mul_cancel₀ hJ, one_mul]
      _ ≤ J⁻¹ * J := CovariantClass.elim J⁻¹ hle
      _ = 1 := inv_mul_cancel₀ hJ
  have hx := hle2 (mem_spanSingleton_self _ _)
  obtain ⟨c, rfl⟩ := (mem_one_iff _).1 hx
  exact c.isIntegral_coe

theorem exists_perfect_trace_ideal :
    ∀ (D : D7), ∃ (ξ : D.host.E) (AA : Submodule (𝓞 D.host.E) D.host.E), FD.cc ξ = -ξ ∧ ξ ≠ 0 ∧ AA.FG ∧ AA ≠ ⊥ ∧ ∀ x : D.host.E, (∀ a ∈ AA, ∀ b ∈ AA, ∃ z : ℤ, Algebra.trace ℚ D.host.E (ξ * x * a * FD.cc b) = z) ↔ IsIntegral ℤ x := by
  intro D
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  refine ⟨D.host.xi0, (D.host.AA : Submodule (𝓞 D.host.E) D.host.E), conj_xi0_alt D, cmHost_imaginaryGenerator_ne_zero hP D,
    FractionalIdeal.fg_of_isUnit _ (Ne.isUnit (AA_ne_zero hP D)), ?_, fun x => ⟨fun h => ?_, fun hx a ha b hb => ?_⟩⟩
  · intro h
    exact AA_ne_zero hP D (FractionalIdeal.coeToSubmodule_eq_bot.1 h)
  · refine isIntegral_of_trace D x (fun a ha b hb => ?_)
    rw [← cc_eq_conj]
    exact h a ha b hb
  · have hxa : (⟨x, hx⟩ : 𝓞 D.host.E) • a ∈ D.host.AA :=
      (D.host.AA : Submodule (𝓞 D.host.E) D.host.E).smul_mem _ ha
    have hm : x * a * D.host.conj b ∈ NAA D := mul_mem_mul hxa (conj_mem_AAbar D hb)
    obtain ⟨n, hn⟩ := trace_int_of_mem hP D hm
    refine ⟨n, ?_⟩
    rw [cc_eq_conj, ← hn]
    congr 1; ring

end GlobalTheory.EtaAn.PerfectTrace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.LogCardComponentsLeOfRowsBound

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn

theorem log_card_comp_le_of_rows : ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D), (2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f) → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Real.log (Fintype.card (T.U j σ).Comp) ≤ 41 * zBase large₂ ^ 2 := by
  intro D T h large₂ ⟨h2, hrL, hrd, hf, hg, h16⟩ j hj σ hσ
  obtain ⟨ξ, AA, hsk, hne, hFG, hA, hdual⟩ := PerfectTrace.exists_perfect_trace_ideal D
  obtain ⟨-, -, hM, -, -, hfin, hJ⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨-, hr, -⟩ := hJ j hj
  have hMg : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hfd : FD.fdeg D.host.E = D.R.f := by
    unfold FD.fdeg; rw [hfin]; omega
  have hfR : (0 : ℝ) < D.R.f := by exact_mod_cast (by omega : 0 < D.R.f)
  have hdisc : 0 < |((NumberField.discr D.host.E : ℤ) : ℝ)| :=
    abs_pos.2 (by exact_mod_cast NumberField.discr_ne_zero D.host.E)
  have hdE : Real.log (FD.dE D.host.E) ≤ 4 * FD.fdeg D.host.E * large₂.sc.L := by
    unfold Formalism.BasicNotions.Host.rdE at hrd
    rw [Real.log_rpow hdisc, hfin, one_div_mul_eq_div, div_le_iff₀ (by push_cast; positivity)] at hrd
    push_cast at hrd
    rw [hfd]
    unfold FD.dE
    linarith
  have hML : Real.log T.Q.l.M' ≤ 30 * large₂.sc.L := by
    rw [hM, hMg]
    have h0 := hg 0
    have h1 := hg 1
    have a := (D.host.g_prime 0).pos
    have b := (D.host.g_prime 1).pos
    rw [Nat.cast_mul, Real.log_mul (by exact_mod_cast a.ne') (by exact_mod_cast b.ne')]
    linarith
  have key := GlobalTheory.log_card_comp_unf_le GlobalTheory.QNorm.hasseNormSt GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
    D.host.E _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr hσ ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ hσ))
    ξ AA hsk hne hFG hA hdual large₂.sc.L (by rw [hfd]; exact h16) h2 hdE hrL
    (by rw [hfd]; exact hf) hML
  rw [hfd] at key
  exact key

end GlobalTheory.EtaAn
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.LogCardComponentsLeOfRowsBoundStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

theorem _root_.GlobalTheory.T.log_card_components_le_of_rows_bound : ∀ (D : D7) (T : Top D) (_h : LawsP T) (large₂ : SizeData₂ D), (2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f) → ∀ j, InR D j → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → Real.log (Fintype.card (T.U j σ).Comp) ≤ 41 * zBase large₂ ^ 2 := by
  first | exact @GlobalTheory.EtaAn.log_card_comp_le_of_rows | exact GlobalTheory.EtaAn.log_card_comp_le_of_rows | (intros; apply GlobalTheory.EtaAn.log_card_comp_le_of_rows <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TorusSplitting.EtaleExtensionDegreeTwoConstants

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtaForm GlobalTheory.EtaAn

namespace GlobalTheory.EtaAn

private lemma etexnum_one_le_rd (E : Type) [Field E] [NumberField E] [IsCMField E] : 1 ≤ I2.PT.rd E := by
  unfold I2.PT.rd
  refine Real.one_le_rpow ?_ (by positivity)
  have h : (1 : ℤ) ≤ |NumberField.discr E| := Int.one_le_abs (NumberField.discr_ne_zero E)
  exact_mod_cast h

theorem etEx_deg_two : ∀ (D : D7) (T : Top D) (h : LawsP T) (large₂ : SizeData₂ D), (2 ≤ large₂.sc.L ∧ Real.log D.R.r ≤ large₂.sc.L ∧ Real.log D.host.rdE ≤ 2 * large₂.sc.L ∧ Real.log D.R.f ≤ 2 * large₂.sc.L ∧ (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧ 16 ≤ D.R.f) → ∀ (DF q : ℕ) (R0 : ℝ), RunOK D.host.E D.R.r DF q R0 D.R.m → 1 ≤ q → Real.log q ≤ 70 * large₂.sc.L → ETEx h (WeightFamilies.PPv D large₂ 200000 2) (EtArch h (I2.th (E := D.host.E) q R0) (200000 * zBase large₂ ^ 2)) := by
  intro D T h large₂ hrows DF q R0 hrun hq lq
  have hP : WeightFamilies.PPv D large₂ 200000 2 = 200000 * zBase large₂ ^ 2 := by
    unfold WeightFamilies.PPv
    rw [Real.rpow_two]
  rw [hP]
  refine GlobalTheory.T.exists_cuspForm_four_clauses_explicitConstant D T h DF q R0 _ _ hrun (fun j hj => ?_) (by positivity)
  rw [min_self]
  have hN := GlobalTheory.T.log_card_components_le_of_rows_bound D T h large₂ hrows j hj T.σ₀ T.good_σ₀
  obtain ⟨hL, lr, lρ, lf, -, hf⟩ := hrows
  have hm := D.R.two_le_m
  have hk := D.R.f_le_k
  have hn : 1 ≤ D.R.n := Formalism.HC.Frame.ord_pos _
  have hmr : D.R.m ≤ D.R.r := by
    unfold Ranks.r
    unfold Ranks.n at hn
    omega
  have hz : zBase large₂ = (I2.PT.f D.host.E : ℝ) * D.R.r * large₂.sc.L := by
    rw [hostSize_f]; rfl
  rw [hz] at hN ⊢
  exact (archimedeanBoundTotalConstant_size D.host.E D.R.r q D.R.m _ large₂.sc.L hL (by rw [hostSize_f]; omega) (by omega) (by omega) hmr hq
    (etexnum_one_le_rd _) lρ (by rw [hostSize_f]; exact lf) lr lq hN).2

end GlobalTheory.EtaAn
end
end
