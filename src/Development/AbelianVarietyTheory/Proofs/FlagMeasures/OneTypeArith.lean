module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.NearNonzeroTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CountHypPAtAddQAt
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalLatticeFlagIsotropicSelfDual
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NearTermsModeratePointsOneTypeBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeIntegralsAndCardCompositions
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TruncatedLeastLatticeSizeRightTranslateLowerBoun
import Mathlib.Analysis.Complex.ExponentialBounds

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralLeSumTypes

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.TypeDecomp

theorem lintegral_biUnion_le {α ι : Type*} [MeasurableSpace α] (μ : Measure α) (s : Finset ι)
    (A : ι → Set α) (f : α → ENNReal) :
    ∫⁻ x in ⋃ i ∈ s, A i, f x ∂μ ≤ ∑ i ∈ s, ∫⁻ x in A i, f x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hb]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

theorem hasType_cast (I : AutInst) (x : I.GA) {a a' : ℕ} (h : a' = a) (j : Fin a → ℕ) (τ : Fin a → ℝ)
    (H : HasType I x j τ) : ∃ τ', HasType I x (fun i : Fin a' => j (Fin.cast h i)) τ' := by
  subst h
  exact ⟨τ, H⟩

theorem sum_diff (a : ℕ) (r : Fin (a + 1) → ℕ) (j : Fin a → ℕ)
    (h : ∀ i, r i.succ = r i.castSucc + j i) : r (Fin.last a) = r 0 + ∑ i, j i := by
  induction a with
  | zero => simp
  | succ a ih =>
    have key := ih (fun i => r i.castSucc) (fun i => j i.castSucc) (fun i => by
      have := h i.castSucc
      rwa [Fin.succ_castSucc] at this)
    have hl := h (Fin.last a)
    rw [Fin.succ_last] at hl
    simp only [Fin.castSucc_zero] at key
    rw [Fin.sum_univ_castSucc, hl, key]
    ring

theorem exists_type (B : RowsAut) (p q : ℕ) (hs : SigIs B p q) (hn : 1 ≤ B.I.n) (x : B.I.GA)
    (hx : least B.I x < 1 / 2) :
    ∃ J ∈ Finset.Icc 1 q, ∃ c : Composition J, ∃ τ, HasType B.I x c.blocksFun τ := by
  obtain ⟨⟨a, S, τ, hF⟩, -, hprop⟩ := GlobalTheory.PointFlag.flag_spec B.I x
  obtain ⟨hsteps, hlast⟩ := hprop a S τ hF
  have hlt : ∀ i : Fin a, Formalism.HN.rkK (S i.castSucc) < Formalism.HN.rkK (S i.succ) := fun i => (hsteps i).2.1
  set j : Fin a → ℕ := fun i => Formalism.HN.rkK (S i.succ) - Formalism.HN.rkK (S i.castSucc) with hj
  have hstep : ∀ i, Formalism.HN.rkK (S i.succ) = Formalism.HN.rkK (S i.castSucc) + j i := fun i => by
    have := hlt i
    simp only [hj]
    omega
  have hjpos : ∀ i, 0 < j i := fun i => by
    have := hlt i
    simp only [hj]
    omega
  have hT : HasType B.I x j τ := ⟨S, hF, hstep⟩
  have hsum : Formalism.HN.rkK (S (Fin.last a)) = Formalism.HN.rkK (S 0) + ∑ i, j i :=
    GlobalTheory.TypeDecomp.sum_diff a (fun i => Formalism.HN.rkK (S i)) j hstep
  have ha : a ≠ 0 := by
    intro h0
    have := (hlast hn).1.mp h0
    linarith
  obtain ⟨v⟩ : Nonempty (InfinitePlace B.I.F) := inferInstance
  have hiso : Formalism.HN.rkK (stepLt B.I x (1 / 2)) ≤ rkR (B.I.ε v) := (GlobalTheory.FlagIso.flag_isotropic B.I x).2.1 v
  have hq : rkR (B.I.ε v) ≤ q := (min_le_right _ _).trans (hs v).2.le
  have hSl : S (Fin.last a) = stepLt B.I x (1 / 2) := hF.2.2.1
  have h1 : 1 ≤ ∑ i, j i := by
    have := Finset.single_le_sum (f := j) (fun i _ => Nat.zero_le _) (Finset.mem_univ ⟨0, Nat.pos_of_ne_zero ha⟩)
    have := hjpos ⟨0, Nat.pos_of_ne_zero ha⟩
    omega
  have h2 : ∑ i, j i ≤ q := by
    rw [hSl] at hsum
    omega
  let c : Composition (∑ i, j i) :=
    ⟨List.ofFn j, fun {b} hb => by
      simp only [List.mem_ofFn, Set.mem_range] at hb
      obtain ⟨k, rfl⟩ := hb
      exact hjpos k, by simp [List.sum_ofFn]⟩
  have hlen : c.length = a := by simp [c, Composition.length]
  have hc : c.blocksFun = fun i => j (Fin.cast hlen i) := by
    funext i
    show (List.ofFn j).get i = j (Fin.cast hlen i)
    first
      | rw [List.get_ofFn]
      | simp [List.get_eq_getElem, Fin.cast]
  obtain ⟨τ', h'⟩ := GlobalTheory.TypeDecomp.hasType_cast B.I x hlen j τ hT
  refine ⟨∑ i, j i, Finset.mem_Icc.mpr ⟨h1, h2⟩, c, τ', ?_⟩
  rw [hc]
  exact h'

theorem lintegral_le_sum_types : ∀ (B : RowsAut) (p q : ℕ), SigIs B p q → 1 ≤ B.I.n → ∀ Φ : B.I.GA → ENNReal, (∀ x, 1 / 2 ≤ least B.I x → Φ x = 0) → ∫⁻ x in B.fund, Φ x ∂(B.I.muA B.μf) ≤ ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J, ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) := by
  intro B p q hs hn Φ hΦ
  have hT : ∀ (J : ℕ) (c : Composition J),
      MeasurableSet {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} := fun J c => by
    obtain ⟨s, -, h, -⟩ := GlobalTheory.FlagMeas.type_measurable B.I c.length c.blocksFun
    exact h
  set P : Set B.I.GA := ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
    {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} with hP
  set U : Set B.I.GA := ⋃ J ∈ Finset.Icc 1 q, ⋃ c ∈ (Finset.univ : Finset (Composition J)),
    {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund with hU
  have hPm : MeasurableSet P :=
    Finset.measurableSet_biUnion _ fun J _ => Finset.measurableSet_biUnion _ fun c _ => hT J c
  have hcover : B.fund ⊆ U ∪ Pᶜ := by
    intro x hx
    by_cases hxP : x ∈ P
    · left
      simp only [hP, hU, Set.mem_iUnion, Set.mem_inter_iff] at hxP ⊢
      obtain ⟨J, hJ, c, hc, hxc⟩ := hxP
      exact ⟨J, hJ, c, hc, hxc, hx⟩
    · exact Or.inr hxP
  have hzero : ∫⁻ x in Pᶜ, Φ x ∂(B.I.muA B.μf) = 0 := by
    have hae : ∀ᵐ x ∂((B.I.muA B.μf).restrict Pᶜ), Φ x = 0 := by
      rw [ae_restrict_iff' hPm.compl]
      refine ae_of_all _ fun x hx => hΦ x ?_
      by_contra hlt
      push_neg at hlt
      obtain ⟨J, hJ, c, τ, hτ⟩ := GlobalTheory.TypeDecomp.exists_type B p q hs hn x hlt
      apply hx
      simp only [hP, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨J, hJ, c, Finset.mem_univ c, τ, hτ⟩
    rw [lintegral_congr_ae hae, lintegral_zero]
  calc ∫⁻ x in B.fund, Φ x ∂(B.I.muA B.μf)
      ≤ ∫⁻ x in U ∪ Pᶜ, Φ x ∂(B.I.muA B.μf) := lintegral_mono_set hcover
    _ ≤ ∫⁻ x in U, Φ x ∂(B.I.muA B.μf) + ∫⁻ x in Pᶜ, Φ x ∂(B.I.muA B.μf) := lintegral_union_le _ _ _
    _ = ∫⁻ x in U, Φ x ∂(B.I.muA B.μf) := by rw [hzero, add_zero]
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∫⁻ x in ⋃ c ∈ (Finset.univ : Finset (Composition J)),
          {x : B.I.GA | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund, Φ x ∂(B.I.muA B.μf) :=
        GlobalTheory.TypeDecomp.lintegral_biUnion_le _ _ _ _
    _ ≤ _ := Finset.sum_le_sum fun J _ => GlobalTheory.TypeDecomp.lintegral_biUnion_le _ _ _ _

end GlobalTheory.TypeDecomp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ModerateLogFactorAbsorbed

section

@[expose] public section

open Matrix Finset Real

namespace GlobalTheory

theorem moderate_log_factor_absorbed : ∀ Cg : ℝ, ∃ n₀ : ℕ, ∀ (n f q : ℕ) (rd g b : ℝ), n₀ ≤ n → 1 ≤ f → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ rd → Real.log rd ≤ Real.exp n → Real.log f ≤ Real.sqrt n → 2 ≤ b → Real.log b ≤ Real.exp (1 / 16 * n * f * Real.log n) → 1 ≤ g → g ≤ b ^ Cg → 2 * f * q * (11 * q * Real.log (n * f * rd * g * b)) ≤ Real.exp (1 / 8 * n * f * Real.log n) ∧ 2 * (2 : ℝ) ^ q * Real.exp (-(3 / 8) * n * f * Real.log n) ≤ Real.exp (-(1 / 4) * n * f * Real.log n) := by
  intro Cg
  set K : ℝ := 22 * (|Cg| + 4) with hK
  have hC : 0 ≤ |Cg| := abs_nonneg _
  have hK0 : 0 ≤ K := by positivity
  refine ⟨⌈Real.exp (16 * (1 + K))⌉₊, ?_⟩
  intro n f q rd g b hn hf hq hqn hrd hlrd hlf hb hlb hg hgb
  have hn' : Real.exp (16 * (1 + K)) ≤ (n : ℝ) := Nat.ceil_le.mp hn
  have hn1 : (1 : ℝ) ≤ n := le_trans (Real.one_le_exp (by positivity)) hn'
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 16 * (1 + K) ≤ Real.log n := (Real.le_log_iff_exp_le hn0).mpr hn'
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqn' : (q : ℝ) ^ 2 ≤ n := by exact_mod_cast hqn
  set L := Real.log n with hLdef
  have hm1 : (n : ℝ) ≤ n * f := by nlinarith
  have hm : (1 : ℝ) ≤ n * f := by linarith
  have hX : (n * f : ℝ) * (1 + K) ≤ 1 / 16 * n * f * L := by nlinarith
  have hX1 : (n * f : ℝ) ≤ 1 / 16 * n * f * L := by nlinarith
  have hX2 : (n * f : ℝ) + K ≤ 1 / 16 * n * f * L := by nlinarith
  set E := Real.exp (1 / 16 * n * f * L) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hEn : Real.exp n ≤ E := Real.exp_le_exp.mpr (by linarith)
  have hnE : (n : ℝ) ≤ E := by
    have := Real.add_one_le_exp (n : ℝ); linarith
  constructor
  · have hb0 : 0 < b := by linarith
    have hlb0 : 0 ≤ Real.log b := Real.log_nonneg (by linarith)
    have h1 : L ≤ E := by
      have := Real.log_le_sub_one_of_pos hn0; linarith
    have h2 : Real.log f ≤ E := by
      have : Real.sqrt n ≤ n := Real.sqrt_le_iff.mpr ⟨hn0.le, by nlinarith⟩
      linarith
    have h3 : Real.log g ≤ |Cg| * E := by
      have h4 : Real.log g ≤ Real.log (b ^ Cg) := Real.log_le_log (by linarith) hgb
      rw [Real.log_rpow hb0] at h4
      have h5 : Cg * Real.log b ≤ |Cg| * Real.log b :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hlb0
      have h6 : |Cg| * Real.log b ≤ |Cg| * E := mul_le_mul_of_nonneg_left hlb hC
      linarith
    have hlog : Real.log (n * f * rd * g * b) ≤ (|Cg| + 4) * E := by
      have hf0 : (0 : ℝ) < f := by linarith
      have hrd0 : 0 < rd := by linarith
      have hg0 : 0 < g := by linarith
      rw [Real.log_mul (by positivity) hb0.ne', Real.log_mul (by positivity) hg0.ne',
        Real.log_mul (by positivity) hrd0.ne', Real.log_mul hn0.ne' hf0.ne']
      linarith
    have hKE : (n * f : ℝ) * K ≤ E := by
      have a1 : (n * f : ℝ) ≤ Real.exp (n * f) := by
        have := Real.add_one_le_exp (n * f : ℝ); linarith
      have a2 : K ≤ Real.exp K := by
        have := Real.add_one_le_exp K; linarith
      calc (n * f : ℝ) * K ≤ Real.exp (n * f) * Real.exp K :=
            mul_le_mul a1 a2 hK0 (Real.exp_pos _).le
        _ = Real.exp (n * f + K) := (Real.exp_add _ _).symm
        _ ≤ E := Real.exp_le_exp.mpr hX2
    have hEE : Real.exp (1 / 8 * n * f * L) = E * E := by
      rw [hE, ← Real.exp_add]; congr 1; ring
    rw [hEE]
    calc 2 * (f : ℝ) * q * (11 * q * Real.log (n * f * rd * g * b))
        = (22 * f * q ^ 2) * Real.log (n * f * rd * g * b) := by ring
      _ ≤ (22 * f * q ^ 2) * ((|Cg| + 4) * E) :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ (22 * f * n) * ((|Cg| + 4) * E) := by gcongr
      _ = (n * f * K) * E := by rw [hK]; ring
      _ ≤ E * E := by gcongr
  · have hqn2 : (q : ℝ) ≤ n := by nlinarith
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have hp : (2 : ℝ) ^ q ≤ Real.exp q := by
      calc (2 : ℝ) ^ q ≤ (Real.exp 1) ^ q := by gcongr
        _ = Real.exp q := by rw [← Real.exp_nat_mul]; simp
    calc 2 * (2 : ℝ) ^ q * Real.exp (-(3 / 8) * n * f * L)
        ≤ Real.exp 1 * Real.exp q * Real.exp (-(3 / 8) * n * f * L) := by gcongr
      _ = Real.exp (1 + q + -(3 / 8) * n * f * L) := by rw [Real.exp_add, Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneTypeArith

section

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.NearMod

theorem fDeg_eq (I : AutInst) : Formalism.HermitianLatticesTheory.fDeg I.E = I.f := by

  have hE : IsTotallyComplex I.E := I.cm.cmUnram.1
  have hdeg : Module.finrank ℚ I.E = Module.finrank ℚ I.F * 2 := by
    rw [← I.cm.deg2, Module.finrank_mul_finrank]
  have hc := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.E
  have hr : NumberField.InfinitePlace.nrRealPlaces I.E = 0 :=
    NumberField.nrRealPlaces_eq_zero_iff.mpr hE
  unfold Formalism.HermitianLatticesTheory.fDeg AutInst.f
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  omega

theorem two_vInv_eq (I : AutInst) : 2 * Formalism.HermitianLatticesTheory.vInv I.E = I.rd := by
  unfold Formalism.HermitianLatticesTheory.vInv AutInst.rd
  rw [fDeg_eq]
  ring

theorem one_type_arith (L κ Y : ℝ) (a J : ℕ) (hL : 0 ≤ L) (hJ : 1 ≤ J) (haJ : a ≤ J)
    (hκ : κ ≤ Real.exp (-(1 / 2 * J * L))) (hY0 : 0 ≤ Y) (hY : Y ≤ Real.exp (1 / 8 * L)) :
    2 * κ * Y ^ a ≤ 2 * Real.exp (-(3 / 8) * L) := by

  have hYa : Y ^ a ≤ Real.exp (a * (1 / 8 * L)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hY0 hY a
  have hYa0 : 0 ≤ Y ^ a := pow_nonneg hY0 a
  rcases lt_or_ge κ 0 with hκ0 | hκ0
  · have : κ * Y ^ a ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hκ0.le hYa0
    nlinarith [Real.exp_pos (-(3 / 8) * L)]
  · have h1 : κ * Y ^ a ≤ Real.exp (-(1 / 2 * J * L)) * Real.exp (a * (1 / 8 * L)) :=
      mul_le_mul hκ hYa hYa0 (Real.exp_pos _).le
    rw [← Real.exp_add] at h1
    have hJ' : (1 : ℝ) ≤ J := by exact_mod_cast hJ
    have ha' : (a : ℝ) ≤ J := by exact_mod_cast haJ
    have h2 : -(1 / 2 * J * L) + a * (1 / 8 * L) ≤ -(3 / 8) * L := by
      nlinarith [mul_nonneg (sub_nonneg.2 ha') hL, mul_nonneg (sub_nonneg.2 hJ') hL]
    have h3 := Real.exp_le_exp.2 h2
    nlinarith

theorem nearModerate : GlobalTheory.FlagMeas.FlagMeasureBound → GlobalTheory.FlagMeas.ConstantBound → GlobalTheory.Dec.NearUnip →
    GlobalTheory.Deep.PtBound → GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate := by
  intro hFM hCB hNU hPB
  unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.NearModerate
  intro Cg hCg
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.moderate_log_factor_absorbed Cg
  refine ⟨max n₁ (3 ^ 15), ?_⟩
  intro B d p q b hq hC
  have h8 : 8 ≤ max n₁ (3 ^ 15) := le_trans (by norm_num) (le_max_right _ _)
  obtain ⟨-, hrd, hf, -, hpq, -, -, hmin, hd, hX, -, -, h, -, hgap, -, -, -, h120, -⟩ :=
    GlobalTheory.Dec.countHyp_numerics B Cg _ d p q b h8 hC
  obtain ⟨hDS, hSig, hn₀, hq2, hlrd, hlf, hb, hlb, -, hg1, hgb, -⟩ := id hC

  have hPt := hPB B d p q h hDS hSig hgap (by rw [hmin]; exact h120)
  have hm : 0 ≤ mainTerm B d := by
    show 0 ≤ (∏ v, d v) * B.I.vol B.μf B.fund * (B.e 1).re
    exact mul_nonneg (mul_nonneg hd.le ENNReal.toReal_nonneg) hPt.2.2.2.2.1

  have hn3 : 3 ^ 15 ≤ B.I.n := (le_max_right _ _).trans hn₀
  have hn1 : 1 ≤ B.I.n := le_trans (by norm_num) hn3
  have hlogn : 15 ≤ Real.log B.I.n := by
    have h3 : Real.exp 15 ≤ (B.I.n : ℝ) := by
      have e1 : Real.exp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
      calc Real.exp 15 = Real.exp 1 ^ 15 := by rw [← Real.exp_nat_mul]; norm_num
        _ ≤ 3 ^ 15 := pow_le_pow_left₀ (Real.exp_pos 1).le e1 15
        _ ≤ (B.I.n : ℝ) := by exact_mod_cast hn3
    have := Real.log_le_log (Real.exp_pos 15) h3
    rwa [Real.log_exp] at this
  have hL : 0 ≤ (B.I.n : ℝ) * B.I.f * Real.log B.I.n := by
    have : (0 : ℝ) ≤ Real.log B.I.n := by linarith
    positivity

  have hY := hn₁ B.I.n B.I.f q B.I.rd (B.g : ℝ) b ((le_max_left _ _).trans hn₀) hf hq hq2 hrd hlrd hlf
    hb hlb (by exact_mod_cast hg1) hgb
  have hlX : 0 ≤ Real.log (bigX B b) := Real.log_nonneg (by linarith)
  have hY0 : 0 ≤ 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) hlX)
  have hY1 : 2 * (B.I.f : ℝ) * q * (11 * q * Real.log (bigX B b)) ≤
      Real.exp (1 / 8 * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)) :=
    hY.1.trans_eq (by congr 1; ring)

  have hA := GlobalTheory.T.nearTerms_moderate_points_one_type_bound hFM hNU hPB B Cg _ d p q b h8 hq hC
  have hper : ∀ J ∈ Finset.Icc 1 q, ∀ c : Composition J,
      ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund,
          {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) ≤
        ENNReal.ofReal (mainTerm B d *
          (2 * Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)))) := by
    intro J hJmem c
    have hJ := Finset.mem_Icc.1 hJmem
    have hsum : ∑ i, c.blocksFun i = J := c.sum_blocksFun
    have ha : 1 ≤ c.length := c.length_pos_of_pos (by omega)
    have hj1 : ∀ i, 1 ≤ c.blocksFun i := fun i => c.one_le_blocksFun i
    refine (hA.2 c.length c.blocksFun ha hj1 (by rw [hsum]; exact hJ.2)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hm
    have hκ := hCB B.I.E B.I.cm.cmUnram p q c.length c.blocksFun hj1 (by rw [hsum]; exact hJ.2)
      (by rw [hpq]; exact hlogn) (by rw [hpq]; exact hq2) (by rw [two_vInv_eq, hpq]; exact hlrd)
      (by rw [fDeg_eq, hpq]; exact hlf)
    rw [hsum, hpq, fDeg_eq] at hκ
    exact one_type_arith _ _ _ c.length J hL hJ.1 c.length_le (hκ.trans_eq (by congr 1; ring)) hY0 hY1

  have hSm : MeasurableSet {x : B.I.GA | tauStar B q b ≤ least B.I x} :=
    measurableSet_le measurable_const (GlobalTheory.LeastVar.continuous_least B.I hn1).measurable
  have hΦ0 : ∀ x, 1 / 2 ≤ least B.I x →
      {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x = 0 :=
    fun x hx => Set.indicator_apply_eq_zero.2 (fun _ => hA.1 x hx)
  set M : ℝ := mainTerm B d * (2 * Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n))) with hM
  have h2q : (2 : ENNReal) ^ q = ENNReal.ofReal (2 ^ q) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  calc ∫⁻ x in GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.moderate B q b, GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d x ∂(B.I.muA B.μf)
      = ∫⁻ x in B.fund, {x | tauStar B q b ≤ least B.I x}.indicator
          (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) := by
        rw [lintegral_indicator hSm, Measure.restrict_restrict hSm, Set.inter_comm]; rfl
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ c : Composition J,
          ∫⁻ x in {x | ∃ τ, HasType B.I x c.blocksFun τ} ∩ B.fund,
            {x | tauStar B q b ≤ least B.I x}.indicator (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearAbs B d) x ∂(B.I.muA B.μf) :=
        GlobalTheory.TypeDecomp.lintegral_le_sum_types B p q hSig hn1 _ hΦ0
    _ ≤ ∑ J ∈ Finset.Icc 1 q, ∑ _c : Composition J, ENNReal.ofReal M :=
        Finset.sum_le_sum fun J hJ => Finset.sum_le_sum fun c _ => hper J hJ c
    _ = ((∑ J ∈ Finset.Icc 1 q, Fintype.card (Composition J) : ℕ) : ENNReal) * ENNReal.ofReal M := by
        rw [Nat.cast_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (2 : ENNReal) ^ q * ENNReal.ofReal M := by
        gcongr
        exact_mod_cast (GlobalTheory.sum_card_composition_lt q).le
    _ = ENNReal.ofReal (2 ^ q * M) := by
        rw [h2q]; exact (ENNReal.ofReal_mul (by positivity)).symm
    _ ≤ ENNReal.ofReal (GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound B d) := by
        apply ENNReal.ofReal_le_ofReal
        have e2 : Real.exp (-(1 / 4 * (B.I.n : ℝ) * (B.I.f : ℝ) * Real.log (B.I.n : ℝ))) =
            Real.exp (-(1 / 4) * B.I.n * B.I.f * Real.log B.I.n) := by congr 1; ring
        have e1 : Real.exp (-(3 / 8) * ((B.I.n : ℝ) * B.I.f * Real.log B.I.n)) =
            Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n) := by congr 1; ring
        unfold GlobalTheory.IndefiniteRowSideFullHecke.NearNonzeroTerms.nearBound
        rw [e2, hM, e1]
        calc (2 : ℝ) ^ q * (mainTerm B d * (2 * Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n)))
            = mainTerm B d * (2 * 2 ^ q * Real.exp (-(3 / 8) * B.I.n * B.I.f * Real.log B.I.n)) := by ring
          _ ≤ mainTerm B d * Real.exp (-(1 / 4) * B.I.n * B.I.f * Real.log B.I.n) :=
            mul_le_mul_of_nonneg_left hY.2 hm
          _ = _ := mul_comm _ _

end GlobalTheory.NearMod
end
end
