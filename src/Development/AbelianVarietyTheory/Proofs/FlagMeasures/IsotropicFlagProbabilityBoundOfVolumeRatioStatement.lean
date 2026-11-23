module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutInstDegreeRootDiscriminantRankStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenLinTamagawaVolumeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermVolumeRatioSameKindOfVolumeRatioInductionStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnfoldingBoundStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeEqFundamentalDomainInterStatement
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHasFlag
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFiveFactorsHermitianVolumeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RiemannianHaarGaugeExistsPosUniqueStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RankTwoDefiniteUnimodularHermitianClassBoundStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryGaugeVolumeLeClassNumberDefiniteStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PointsOfFlagTypeSetMeasurableAndInvariant

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagMeas

theorem typeSet_measurable_invariant : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)), MeasurableSet B → MeasurableSet (typeSet I j B) ∧ (∀ γ ∈ I.GFset, ∀ x ∈ typeSet I j B, γ * x ∈ typeSet I j B) ∧ ∀ x ∈ typeSet I j B, ∀ k ∈ I.Kset, (x.1, x.2 * k) ∈ typeSet I j B := by
  intro I a j B hB
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨s, hs, hm, he⟩ := type_measurable I a j
    have : typeSet I j B = {x : I.GA | ∃ τ, HasType I x j τ} ∩ s ⁻¹' B := by
      ext x
      constructor
      · rintro ⟨τ, h1, h2⟩
        exact ⟨⟨τ, h2⟩, by rw [Set.mem_preimage, he x τ h2]; exact h1⟩
      · rintro ⟨⟨τ, h2⟩, h1⟩
        rw [Set.mem_preimage, he x τ h2] at h1
        exact ⟨τ, h1, h2⟩
    rw [this]
    exact hm.inter (hs hB)
  · rintro γ ⟨g, hg, h1, h2⟩ x ⟨τ, hτ, h⟩
    exact ⟨τ, hτ, ((GlobalTheory.PointEquivariance.equivariance I x g γ hg h1 h2).2.2.2.2.1 a j τ).2 h⟩
  · rintro x ⟨τ, hτ, h⟩ k hk
    refine ⟨τ, hτ, GlobalTheory.PointEquivariance.hasType_of I x (x.1, x.2 * k) (OrderIso.refl _) ?_
      (fun _ => rfl) (fun _ => rfl) j τ h⟩
    have e : ((x.1, x.2 * k) : I.GA) = x * (1, k) := Prod.ext (mul_one _).symm rfl
    rw [e]
    exact (GlobalTheory.PointEquivariance.lamX_mul_eq_iff I x (1, k)).1 hk

end GlobalTheory.FlagMeas
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.PointsOfFlagTypeSetMeasurableAndInvariantStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.pointsOfFlagTypeSet_measurable_and_invariant : ∀ (I : AutInst) (a : ℕ) (j : Fin a → ℕ) (B : Set (Fin a → ℝ)), MeasurableSet B → MeasurableSet (typeSet I j B) ∧ (∀ γ ∈ I.GFset, ∀ x ∈ typeSet I j B, γ * x ∈ typeSet I j B) ∧ ∀ x ∈ typeSet I j B, ∀ k ∈ I.Kset, (x.1, x.2 * k) ∈ typeSet I j B := by
  first | exact @GlobalTheory.FlagMeas.typeSet_measurable_invariant | exact GlobalTheory.FlagMeas.typeSet_measurable_invariant | (intros; apply GlobalTheory.FlagMeas.typeSet_measurable_invariant <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAdelicQuotientVolumePosLtTop

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

theorem fundDom_volume_pos_lt_top : VolumeStep → ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf]
    [μf.IsHaarMeasure] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ p q : ℕ, HasSig I p q → 2 ≤ p →
    0 < I.muA μf fund ∧ I.muA μf fund < ⊤ := by
  intro hstep I μf _ _ fund hfund p q hsig hp
  obtain ⟨hcov, hpos⟩ := GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund Set.univ hfund MeasurableSet.univ
    (fun _ _ _ _ => Set.mem_univ _)
  rw [Set.univ_inter] at hcov
  refine ⟨hpos, ?_⟩
  obtain ⟨⟨I₀, hsame, hsig₀⟩, hratio⟩ := GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction hstep I p q 2 0 hsig hp (Nat.zero_le _) le_rfl
  choose c hc using fun v : InfinitePlace I.F => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I.n (I.ε v)
  choose c₀ hc₀ using fun v : InfinitePlace I₀.F => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I₀.n (I₀.ε v)
  obtain ⟨-, hlc, hsc, -⟩ := GlobalTheory.CongTop.adelic_topology I₀
  obtain ⟨-, -, -, hK, -⟩ := GlobalTheory.CongTop.adelic_topology I
  have hg : IsGaugeAll I c := fun v => (hc v).2.1
  have hg₀ : IsGaugeAll I₀ c₀ := fun v => (hc₀ v).2.1
  let μ₀ : Measure I₀.Gf := Measure.haar
  have heq := hratio I₀ hsame hsig₀ c μf c₀ μ₀ hg hg₀
  have hdef := GlobalTheory.T.unitaryGaugeVolume_le_classNumber_definite I₀ 2 hsig₀ c₀ μ₀ hg₀
  have hcl := GlobalTheory.T.rank_two_definite_unimodular_hermitian_class_bound I₀.E I₀.cm.cmUnram
  have h₀ : gaugeVol I₀ c₀ μ₀ < ⊤ :=
    hdef.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hcl.trans_lt ENNReal.ofReal_lt_top))
  have hfin : gaugeVol I c μf < ⊤ := by
    rw [heq]
    exact ENNReal.mul_lt_top h₀ ENNReal.ofReal_lt_top
  rw [gaugeVol, hcov] at hfin
  by_contra htop
  rw [not_lt, top_le_iff] at htop
  have hcpos : ENNReal.ofReal (∏ v, c v) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Finset.prod_pos fun v _ => (hc v).1)).ne'
  rw [htop, ENNReal.mul_top hcpos, ENNReal.top_div_of_ne_top hK.measure_lt_top.ne] at hfin
  exact lt_irrefl _ hfin

end GlobalTheory.FlagMeas
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryAdelicQuotientVolumePosLtTopStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.unitary_adelic_quotient_volume_pos_lt_top : VolumeStep → ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure] (fund : Set I.GA), I.IsFundDom (I.muA μf) fund → ∀ p q : ℕ, HasSig I p q → 2 ≤ p → 0 < I.muA μf fund ∧ I.muA μf fund < ⊤ := by
  first | exact @GlobalTheory.FlagMeas.fundDom_volume_pos_lt_top | exact GlobalTheory.FlagMeas.fundDom_volume_pos_lt_top | (intros; apply GlobalTheory.FlagMeas.fundDom_volume_pos_lt_top <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagProbabilityBoundOfVolumeRatio

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.FlagMeas.Bound


open scoped ComplexOrder in
theorem zetaE_nonneg (E : Type) [Field E] [NumberField E] (l : ℕ) : 0 ≤ zetaE E l := by
  unfold zetaE dedekindZeta LSeries
  have h : (0 : ℂ) ≤ ∑' n : ℕ, LSeries.term
      (fun n => (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℂ)) ((l : ℝ) : ℂ) n :=
    tsum_nonneg fun n => LSeries.term_nonneg (by exact Nat.cast_nonneg _) _
  have h2 := (Complex.le_def.1 h).1
  simpa using h2

theorem vInv_nonneg (E : Type) [Field E] [NumberField E] : 0 ≤ Formalism.HermitianLatticesTheory.vInv E := by
  unfold Formalism.HermitianLatticesTheory.vInv
  positivity

theorem volU_nonneg (i : ℕ) : 0 ≤ volU i := by
  unfold volU sphV
  positivity

theorem cIw_nonneg (p q : ℕ) {a : ℕ} (j : Fin a → ℕ) : 0 ≤ cIw p q j := by
  unfold cIw
  have h := volU_nonneg
  refine div_nonneg (mul_nonneg (by positivity) (mul_nonneg (h _) (h _)))
    (mul_nonneg (mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (h _) (by positivity)) (h _)) (h _))

theorem div_le_of_scaled {C K x m T V J : ENNReal} {R : ℝ} (hC0 : C ≠ 0) (hC : C ≠ ⊤) (hK0 : K ≠ 0) (hK : K ≠ ⊤)
    (hm0 : m ≠ 0) (hm : m ≠ ⊤) (h1 : C * x / K ≤ T * V * J) (h2 : C * m / K = V * ENNReal.ofReal R) :
    0 < R ∧ x / m ≤ T / ENNReal.ofReal R * J := by
  have hD0 : C / K ≠ 0 := (ENNReal.div_pos hC0 hK).ne'
  have hD : C / K ≠ ⊤ := ENNReal.div_ne_top hC hK0
  have e1 : ∀ y, C * y / K = C / K * y := fun y => by
    rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]
  rw [e1] at h1 h2
  have hp0 : V * ENNReal.ofReal R ≠ 0 := h2 ▸ mul_ne_zero hD0 hm0
  have hp : V * ENNReal.ofReal R ≠ ⊤ := h2 ▸ ENNReal.mul_ne_top hD hm
  have hV0 : V ≠ 0 := left_ne_zero_of_mul hp0
  have hR0 : ENNReal.ofReal R ≠ 0 := right_ne_zero_of_mul hp0
  have hV : V ≠ ⊤ := fun h => hp (by rw [h, ENNReal.top_mul hR0])
  refine ⟨by simpa using hR0, ?_⟩
  calc x / m = (C / K * x) / (C / K * m) := (ENNReal.mul_div_mul_left _ _ hD0 hD).symm
    _ ≤ (T * V * J) / (V * ENNReal.ofReal R) := by rw [h2]; gcongr
    _ = (V * (T * J)) / (V * ENNReal.ofReal R) := by ring_nf
    _ = T * J / ENNReal.ofReal R := ENNReal.mul_div_mul_left _ _ hV0 hV
    _ = T / ENNReal.ofReal R * J := by rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm]

theorem flagMeasureBound : VolumeStep → FlagMeasureBound := by
  intro hstep I μf _ _ fund hfund p q hsig hn a j ha hj hjq B hB hBs
  obtain ⟨hf, -, -, -, -, hpq⟩ := GlobalTheory.T.autInst_degree_rootDiscriminant_rank I
  have hpq := hpq p q hsig
  obtain ⟨hmeas, hinv, -⟩ := GlobalTheory.T.pointsOfFlagTypeSet_measurable_and_invariant I a j B hB
  obtain ⟨hpos, hfin⟩ := GlobalTheory.T.unitary_adelic_quotient_volume_pos_lt_top hstep I μf fund hfund p q hsig (by omega)
  refine ⟨hmeas, hpos, hfin, ?_⟩
  obtain ⟨⟨I₀, hsame, hsig₀⟩, hratio⟩ := GlobalTheory.T.hermVolumeRatioSameKind_of_volumeRatioInduction hstep I p q (p - ∑ i, j i) (q - ∑ i, j i) hsig
    (Nat.sub_le _ _) (Nat.sub_le _ _) (by omega)
  obtain ⟨t₀, lc₀, sc₀, -⟩ := GlobalTheory.CongTop.adelic_topology I₀
  obtain ⟨-, -, -, hKc, hKo, ⟨Ks, hKs⟩, -⟩ := GlobalTheory.CongTop.adelic_topology I
  choose c hc0 hc _ using fun v => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I.n (I.ε v)
  choose c₀ _ hc₀ _ using fun v => GlobalTheory.T.riemannianHaarGauge_exists_pos_unique I₀.n (I₀.ε v)
  let μ₀ : Measure I₀.Gf := Measure.haar
  have hU := GlobalTheory.T.isotropicFlag_unfolding_bound I I₀ p q a j ha hj hjq (by omega) hsame hsig hsig₀ c μf c₀ μ₀ hc hc₀ B hB hBs
  have hR := hratio I₀ hsame hsig₀ c μf c₀ μ₀ hc hc₀
  rw [(GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund _ hfund hmeas hinv).1] at hU
  have hR' : ENNReal.ofReal (∏ v, c v) * I.muA μf fund / μf I.Kset = gaugeVol I₀ c₀ μ₀ *
      ENNReal.ofReal (∏ M ∈ Finset.Ioc (p + q - 2 * ∑ i, j i) (p + q), rankFac I.E M) := by
    have e : p - ∑ i, j i + (q - ∑ i, j i) = p + q - 2 * ∑ i, j i := by omega
    rw [← e, ← hR, gaugeVol,
      (GlobalTheory.T.leftQuotientCovolume_eq_fundamentalDomain_inter I μf fund Set.univ hfund MeasurableSet.univ (fun _ _ _ _ => Set.mem_univ _)).1,
      Set.univ_inter]
  have hK0 : μf I.Kset ≠ 0 := (hKo.measure_pos μf ⟨1, by rw [← hKs]; exact Ks.one_mem⟩).ne'
  have hK : μf I.Kset ≠ ⊤ := hKc.measure_lt_top.ne
  have hC0 : ENNReal.ofReal (∏ v, c v) ≠ 0 := by
    simpa using Finset.prod_pos fun v _ => hc0 v
  obtain ⟨hRpos, hle⟩ := div_le_of_scaled hC0 ENNReal.ofReal_ne_top hK0 hK hpos.ne' hfin.ne hU hR'
  refine hle.trans (le_of_eq ?_)
  congr 1
  have hv := vInv_nonneg I.E
  have hres := (dedekindZeta_residue_pos I.E).le
  rw [← GlobalTheory.T.prod_five_factors_hermitian_volume I.E I.cm.cmUnram p q a j hjq (by omega), ENNReal.ofReal_div_of_pos hRpos, hf, hpq,
    ENNReal.ofReal_mul (mul_nonneg (pow_nonneg (cIw_nonneg p q j) _) (by positivity)),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (Finset.prod_nonneg fun l _ => zetaE_nonneg I.E l)))]
  congr 2
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [GlobalTheory.T.genLin_tamagawa_volume I.E I.cm.cmUnram.1 (j i) (hj i), hf]
  exact (ENNReal.ofReal_mul (by positivity)).symm

end GlobalTheory.FlagMeas.Bound
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagProbabilityBoundOfVolumeRatioStatement

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.isotropicFlagProbabilityBound_of_volumeRatio : VolumeStep → FlagMeasureBound := by
  first | exact @GlobalTheory.FlagMeas.Bound.flagMeasureBound | exact GlobalTheory.FlagMeas.Bound.flagMeasureBound | (intros; apply GlobalTheory.FlagMeas.Bound.flagMeasureBound <;> assumption)
end
end
