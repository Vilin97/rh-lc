module

public import Formalism.SharpRestriction.LevelLetterCocycles.CocyclesToWachVectorsBoundOfExtTool
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantLetterPolynomialDerivation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantLetterIdempotentSmul
public import Formalism.SharpRestriction.LevelLetterCocycles.MultVNonneg
public import Formalism.SharpRestriction.LevelLetterCocycles.PadicValNatFactorialSucc
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.LevelLetterCocycles.RToolModDStab

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.Step1KillXList

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

section Kill

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

def step1Kill_roots (c : ZMod n) (M h a : ℕ) : Finset ℤ :=
  ((jumpSetL W T c M h) ×ˢ Finset.Icc (((0 : ℕ) : ℤ) + 1) (a : ℤ)).image (fun p : ℤ × ℤ => p.1 + p.2)

theorem step1Kill_xList (c : ZMod n) (M h a : ℕ) :
    xListL W T c M h 0 a = (step1Kill_roots W T c M h a).sort (· ≤ ·) := rfl

theorem step1Kill_cO (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v) (hRN : Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W) :
    ∃ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) ∧
      cO 0 = 0 ∧ ∀ x : ℤ, x ≠ 0 → v (algebraMap O LL (cO x)) = ((padicValInt PD.p x : ℕ) : WithTop ℚ) := by
  classical
  have hc : ∀ j : ℤ, ((PD.p : ℕ) : LL) = 0 → Formalism.MainNotions.CrystallineLiftingInputs.cR W j = 0 := by
    intro j h0
    unfold Formalism.MainNotions.CrystallineLiftingInputs.cR
    simp [h0]
  have hp0 : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h0
    have h1 := hRN.2 1 0 (by norm_num)
    rw [hc 1 h0, hc 0 h0, sub_zero, AddValuation.map_zero] at h1
    exact WithTop.top_ne_coe h1
  have hnn : ∀ x : ℤ, 0 ≤ v (Formalism.MainNotions.CrystallineLiftingInputs.cR W x) := by
    intro x
    by_cases hx : x = 0
    · rw [hx, hRN.1, AddValuation.map_zero]
      exact le_top
    · have h := hRN.2 x 0 hx
      rw [hRN.1, sub_zero] at h
      rw [h]
      first
        | exact WithTop.coe_nonneg.mpr (by positivity)
        | (rw [← WithTop.coe_zero]; exact WithTop.coe_le_coe.mpr (by positivity))
  have hex : ∀ x : ℤ, ∃ o : O, algebraMap O LL o = Formalism.MainNotions.CrystallineLiftingInputs.cR W x := fun x => hV.2.1 _ (hnn x)
  refine ⟨fun x => Classical.choose (hex x), ?_, ?_, ?_⟩
  · intro x
    apply hV.1
    rw [map_mul, map_natCast, Classical.choose_spec (hex x), map_sub, map_one]
    unfold Formalism.MainNotions.CrystallineLiftingInputs.cR
    first
      | (rw [div_neg, mul_neg, mul_div_assoc', mul_div_cancel_left₀ _ hp0, neg_sub])
      | (field_simp; ring)
      | field_simp
  · apply hV.1
    rw [Classical.choose_spec (hex 0), hRN.1, map_zero]
  · intro x hx
    have h := hRN.2 x 0 hx
    rw [hRN.1, sub_zero] at h
    rw [Classical.choose_spec (hex x), h]
    first
      | exact WithTop.coe_natCast _
      | (norm_cast; done)
      | (simp; done)
      | (push_cast; rfl)

theorem step1Kill_kill [NeZero n] (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W) (hDS : DerivationPreservesQLattice W)
    (hD : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (Mi hi : ZMod n → ℕ)
    (hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi) (c : ZMod n) (cO : ℤ → O)
    (hcO : ∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O)) (hc0 : cO 0 = 0)
    (a : ℕ) {y₀ : W.DD T} (hy : QLattice W T c a y₀) :
    Polynomial.aeval (derivationOnWachModule W T)
      (X * ∏ x ∈ (step1Kill_roots W T c (Mi c) (hi c) a).filter (· ≠ 0), (X - C (cO x))) y₀ ∈ W.N T := by
  have hU := hR.πU
  have hπΔ := hR.πΔ
  have hv : v (algebraMap O LL (((W.χΓ W.gam : Oˣ) : O) - 1)) = 1 := by
    rw [map_sub, map_one, W.gam_gen, hA.2.1]
    simp
  have hyNl : Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀ ∈ W.Nl T c := by
    have h1 : Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀ = (letE c : LetA O n) • (Formalism.MainNotions.LiftingTheory.qp W ^ a • y₀) := by
      rw [smul_smul, mul_comm, ← smul_smul, hy.1.1]
    rw [h1]
    exact Formalism.MainNotions.LiftingTheory.liftb_letE_mem W T c hy.2
  obtain ⟨seq, h0, hstep, hN⟩ := hD hA T Mi hi hT hJ (W.χΓ W.gam) rfl hv cO hcO c 0 a y₀
    (Nat.zero_le a) hyNl hy.1.2
  have hseq := Formalism.MainNotions.LiftingTheory.lifta_seq W T (uniformizerInverse W) (algebraMap_uniformizer_mul_inverse hU) cO _ seq hstep
  rw [h0] at hseq
  have hNs : seq (xListL W T c (Mi c) (hi c) 0 a).length ∈ W.N T :=
    Formalism.MainNotions.LiftingTheory.liftb_Nl_le W T c (by simpa using hN)
  rw [hseq] at hNs
  have hprod : ((xListL W T c (Mi c) (hi c) 0 a).map
      fun x => (X - C (cO x) : Polynomial O)).prod =
      ∏ x ∈ step1Kill_roots W T c (Mi c) (hi c) a, (X - C (cO x)) := by
    rw [step1Kill_xList, ← List.prod_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  rw [hprod, ← Finset.prod_filter_mul_prod_filter_not _ (fun x => x ≠ 0)] at hNs
  by_cases h0m : (0 : ℤ) ∈ step1Kill_roots W T c (Mi c) (hi c) a
  · have hf : (step1Kill_roots W T c (Mi c) (hi c) a).filter (fun x => ¬ x ≠ 0) = {0} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton, not_not]
      constructor
      · exact fun h => h.2
      · rintro rfl; exact ⟨h0m, rfl⟩
    rw [hf, Finset.prod_singleton, hc0, map_zero, sub_zero, mul_comm] at hNs
    exact hNs
  · have hf : (step1Kill_roots W T c (Mi c) (hi c) a).filter (fun x => ¬ x ≠ 0) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.notMem_empty, not_not, iff_false, not_and]
      rintro hx rfl
      exact h0m hx
    rw [hf, Finset.prod_empty, mul_one] at hNs
    rw [map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    have hQ : QLattice W T c 0 (Polynomial.aeval (derivationOnWachModule W T)
        (∏ x ∈ (step1Kill_roots W T c (Mi c) (hi c) a).filter (· ≠ 0), (X - C (cO x))) y₀) :=
      ⟨invariantLetter_polynomial_derivation W T hπΔ hU _ hy.1, by simpa [derivationOnWachModule] using hNs⟩
    simpa using (qLattice_derivation W T hDS hA hT c 0 hQ).2

theorem step1Kill_norm (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v) (hvp : v (PD.p : LL) = 1) (cO : ℤ → O)
    (hcv : ∀ x : ℤ, x ≠ 0 → v (algebraMap O LL (cO x)) = ((padicValInt PD.p x : ℕ) : WithTop ℚ))
    (Sx : Finset ℤ) (hS0 : (0 : ℤ) ∉ Sx) (s : ℕ) (hs : ∑ x ∈ Sx, padicValInt PD.p x ≤ s) :
    ∃ w : O, (C w * ∏ x ∈ Sx, (X - C (cO x))).coeff 0 = ((PD.p : ℕ) : O) ^ s := by
  classical
  have hcoef : ∀ w : O, (C w * ∏ x ∈ Sx, (X - C (cO x))).coeff 0 = w * ∏ x ∈ Sx, -(cO x) := by
    intro w
    rw [Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_prod]
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
  have hval : ∀ S : Finset ℤ, (0 : ℤ) ∉ S →
      v (algebraMap O LL (∏ x ∈ S, -(cO x))) = ((∑ x ∈ S, padicValInt PD.p x : ℕ) : WithTop ℚ) := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · intro _
      simp
    · intro a S ha ih h0
      have ha0 : a ≠ 0 := fun h => h0 (by rw [← h]; exact Finset.mem_insert_self a S)
      have hS0' : (0 : ℤ) ∉ S := fun h => h0 (Finset.mem_insert_of_mem h)
      rw [Finset.prod_insert ha, Finset.sum_insert ha, map_mul, AddValuation.map_mul, map_neg,
        AddValuation.map_neg, hcv a ha0, ih hS0', Nat.cast_add]
  have hvc := hval Sx hS0
  have hc0 : algebraMap O LL (∏ x ∈ Sx, -(cO x)) ≠ 0 := by
    intro h
    rw [h, AddValuation.map_zero] at hvc
    exact WithTop.natCast_ne_top _ hvc.symm
  have hvps : v (((PD.p : ℕ) : LL) ^ s) = ((s : ℕ) : WithTop ℚ) := by
    rw [AddValuation.map_pow, hvp, nsmul_one]
  have aux : ∀ r : WithTop ℚ, r + ((∑ x ∈ Sx, padicValInt PD.p x : ℕ) : WithTop ℚ) = ((s : ℕ) : WithTop ℚ) →
      0 ≤ r := by
    intro r hr
    induction r using WithTop.recTopCoe with
    | top => exact le_top
    | coe q =>
      rw [← WithTop.coe_natCast, ← WithTop.coe_natCast, ← WithTop.coe_add, WithTop.coe_inj] at hr
      have hq : ((∑ x ∈ Sx, padicValInt PD.p x : ℕ) : ℚ) ≤ (s : ℚ) := by exact_mod_cast hs
      first
        | exact WithTop.coe_nonneg.mpr (by linarith)
        | (rw [← WithTop.coe_zero]; exact WithTop.coe_le_coe.mpr (by linarith))
  have hw'0 : 0 ≤ v (((PD.p : ℕ) : LL) ^ s / algebraMap O LL (∏ x ∈ Sx, -(cO x))) := by
    apply aux
    rw [← hvc, ← AddValuation.map_mul, div_mul_cancel₀ _ hc0, hvps]
  obtain ⟨w, hw⟩ := hV.2.1 _ hw'0
  refine ⟨w, ?_⟩
  rw [hcoef]
  apply hV.1
  rw [map_mul, hw, div_mul_cancel₀ _ hc0, map_pow, map_natCast]

end Kill

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.FirstLiftOfHypotheses

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

open Polynomial

theorem first_lift_of_hypotheses [NeZero n] (W : LocWach PD LL O v n) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v)
    (h9 : Formalism.MainNotions.LiftingTheory.P9π₀ W) (hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W)
    (hDS : DerivationPreservesQLattice W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W)
    (hEx : Sh.ExpRules W) (hER : Sh.ExpRing W) (hK : Sh.LemK W) (hFD : Sh.FilDim W)
    (hB : Sh.BasTool W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Step1 W := by
  intro d T₁ T₂ F b S η m hS
  haveI : Fact PD.p.Prime := ⟨PD.hp⟩
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hl : 11 ≤ PD.p := hS.2.1
  obtain ⟨hdom, hdvr, hfrac⟩ := hS.2.2.2.1
  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  have hT₂ : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W h9
  set a := ⌈aR PD.p (hpar n b S + η)⌉₊ with ha_def
  have hp1 : (1 : ℝ) < PD.p := by exact_mod_cast (by omega : 1 < PD.p)
  have hpos : (0 : ℝ) < (PD.p : ℝ) - 1 := by linarith
  have haR : 0 ≤ aR PD.p (hpar n b S + η) := by
    have hlam := lam_nonneg_of_one_lt PD.p (hpar n b S + η) (by omega)
    unfold aR
    have : 0 ≤ ((hpar n b S + η : ℕ) : ℝ) * (2 * (PD.p : ℝ) - 1) / ((PD.p : ℝ) - 1) ^ 2 :=
      div_nonneg (mul_nonneg (by positivity) (by linarith)) (sq_nonneg _)
    linarith
  have hab : ∀ c, a + η < b c := by
    intro c
    have h1 := hS.2.2.2.2.2.2.2.2.1 c
    have h2 : (a : ℝ) < aR PD.p (hpar n b S + η) + 1 := Nat.ceil_lt_add_one haR
    have : (a : ℝ) + η < b c := by linarith
    exact_mod_cast this
  have hbh : ∀ c, b c ≤ hpar n b S := fun c =>
    le_trans (Finset.le_sup (f := b) (Finset.mem_univ c)) (Nat.le_add_right _ _)

  have hjw : ∀ c τ, Formalism.MainNotions.LiftingTheory.Over W τ c → JumpsInV PD T₂.ρ τ (JumpWinS d b S η c) :=
    fun c τ hτ => Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS c τ hτ
  set Mb : ZMod n → ℕ := fun i => b i + S + η with hMb
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₂ Mb Mb := by
    intro i τ hτ x hx
    have h := hjw i τ hτ x hx
    unfold JumpWinS at h
    simp only [hMb, Set.mem_Icc]
    split_ifs at h <;> simp only [Set.mem_union, Set.mem_Icc] at h <;> omega
  obtain ⟨cO, hcO, hc0, hcv⟩ := step1Kill_cO W hV (hRN hA)
  set Sx : ZMod n → Finset ℤ := fun c => (step1Kill_roots W T₂ c (Mb c) (Mb c) a).filter (· ≠ 0)
    with hSx_def
  have hSx : ∀ c ∈ evens n d, ∀ x ∈ Sx c, x ≠ 0 ∧ ((1 - ((b c + S : ℕ) : ℤ) ≤ x ∧ x ≤ (a : ℤ) - b c) ∨
      (1 - (η : ℤ) ≤ x ∧ x ≤ ((η + a : ℕ) : ℤ))) := by
    intro c hc x hx
    have hev : (c.val + d) % 2 = 0 := by simpa [evens] using hc
    rw [hSx_def, Finset.mem_filter, step1Kill_roots, Finset.mem_image] at hx
    obtain ⟨⟨p, hp, rfl⟩, hx0⟩ := hx
    rw [Finset.mem_product, Finset.mem_Icc] at hp
    obtain ⟨hu, hj1, hj2⟩ := hp
    unfold jumpSetL at hu
    simp only [Finset.mem_filter] at hu
    obtain ⟨-, τ, hτ, hjmp⟩ := hu
    have hw := hjw c τ hτ p.1 hjmp
    simp only [JumpWinS, hev, if_true, Set.mem_union, Set.mem_Icc] at hw
    refine ⟨hx0, ?_⟩
    push_cast at hj1 hj2 ⊢
    omega

  have hbound : ∀ c ∈ evens n d,
      ((∑ x ∈ Sx c, padicValInt PD.p x : ℕ) : ℝ) ≤ B1 PD.p (hpar n b S) η S := by
    intro c hc
    have hv := padicValInt_sum_le PD.p (b c) S η a (hab c) (Sx c) (hSx c hc)
    have hv' : ((PD.p : ℝ) - 1) * ((∑ x ∈ Sx c, padicValInt PD.p x : ℕ) : ℝ) ≤
        2 * (a : ℝ) + 2 * η + S + ((PD.p : ℝ) - 1) * ((Nat.log PD.p (b c - a - 1) : ℝ) + 1) := by
      have := (Nat.cast_le (α := ℝ)).2 hv
      push_cast [Nat.cast_sub (by omega : 1 ≤ PD.p)] at this ⊢
      linarith
    have hH : (1 : ℝ) ≤ 2 * ((hpar n b S + η : ℕ) : ℝ) := by
      have h1 : 1 ≤ hpar n b S + η := by have := hab c; have := hbh c; omega
      have : (1 : ℝ) ≤ ((hpar n b S + η : ℕ) : ℝ) := by exact_mod_cast h1
      linarith
    have hlog : (Nat.log PD.p (b c - a - 1) : ℝ) ≤ Real.logb PD.p (2 * ((hpar n b S + η : ℕ) : ℝ)) := by
      rcases Nat.eq_zero_or_pos (b c - a - 1) with hK0 | hKpos
      · rw [hK0, Nat.log_zero_right, Nat.cast_zero]
        exact Real.logb_nonneg hp1 hH
      · have hKle : ((b c - a - 1 : ℕ) : ℝ) ≤ 2 * ((hpar n b S + η : ℕ) : ℝ) := by
          have : b c - a - 1 ≤ hpar n b S + η := by have := hbh c; omega
          have : ((b c - a - 1 : ℕ) : ℝ) ≤ ((hpar n b S + η : ℕ) : ℝ) := by exact_mod_cast this
          linarith
        calc (Nat.log PD.p (b c - a - 1) : ℝ) ≤ Real.logb PD.p ((b c - a - 1 : ℕ) : ℝ) :=
              Real.natLog_le_logb _ _
          _ ≤ _ := Real.logb_le_logb_of_le hp1 (by exact_mod_cast hKpos) hKle
    unfold B1 lam
    have hm := mul_le_mul_of_nonneg_left hlog hpos.le
    rw [show ((aN PD.p (hpar n b S + η) : ℕ) : ℝ) = (a : ℝ) from rfl, div_add' _ _ _ hpos.ne',
      le_div_iff₀ hpos]
    nlinarith
  have hB1 : 0 ≤ B1 PD.p (hpar n b S) η S := by
    unfold B1
    have := lam_nonneg_of_one_lt PD.p (hpar n b S + η) (by omega)
    have : 0 ≤ (2 * (aN PD.p (hpar n b S + η) : ℝ) + 2 * (η : ℝ) + (S : ℝ)) / ((PD.p : ℝ) - 1) :=
      div_nonneg (by positivity) hpos.le
    linarith
  set s₁ : ℕ := (evens n d).sup fun c => ∑ x ∈ Sx c, padicValInt PD.p x with hs₁_def
  have hs₁ : (s₁ : ℝ) ≤ B1 PD.p (hpar n b S) η S := by
    have : s₁ ≤ ⌊B1 PD.p (hpar n b S) η S⌋₊ := Finset.sup_le (fun c hc => Nat.le_floor (hbound c hc))
    exact le_trans (by exact_mod_cast this) (Nat.floor_le hB1)
  refine ⟨s₁, hs₁, ?_⟩
  intro FF _ _ _ _ g N y z μ ν hX
  haveI := hdom
  haveI := hdvr
  haveI := hfrac

  have hw : ∀ c, ∃ w : O, c ∈ evens n d →
      (C w * ∏ x ∈ Sx c, (X - C (cO x))).coeff 0 = ((PD.p : ℕ) : O) ^ s₁ := by
    intro c
    by_cases hc : c ∈ evens n d
    · obtain ⟨w, hw⟩ := step1Kill_norm hV W.v_l cO hcv (Sx c) (by simp [hSx_def]) s₁
        (Finset.le_sup (f := fun c => ∑ x ∈ Sx c, padicValInt PD.p x) hc)
      exact ⟨w, fun _ => hw⟩
    · exact ⟨0, fun h => absurd h hc⟩
  choose wc hwc using hw
  set R : ZMod n → Polynomial O := fun c => C (wc c) * ∏ x ∈ Sx c, (X - C (cO x)) with hR_def
  have hkill : ∀ c ∈ evens n d, ∀ y₀, QLattice W T₂ c a y₀ →
      Polynomial.aeval (derivationOnWachModule W T₂) (X * R c) y₀ ∈ W.N T₂ := by
    intro c _ y₀ hy
    have h := step1Kill_kill W T₂ hR hDS hD hA hT₂ Mb Mb hJ c cO hcO hc0 a hy
    have e : X * R c = C (wc c) * (X * ∏ x ∈ Sx c, (X - C (cO x))) := by
      simp only [hR_def]; ring
    rw [e, map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact (W.N T₂).smul_of_tower_mem _ h

  obtain ⟨hX1, hX2⟩ := hX
  have hzΔ : ∀ f, ∀ δ ∈ W.DelF, W.γD T₂ δ (z f) = z f := by
    intro f δ hδ
    obtain ⟨x, -, hxe, -⟩ := hX1 f
    have h := delta_fixes_cocycle_second W T₂ x δ hδ
    rw [hxe] at h
    exact h
  let smE : W.EE → W.DD T₂ →ₗ[O] W.DD T₂ := fun e =>
    (LinearMap.lsmul W.EE (W.DD T₂) e).restrictScalars O
  let smA : LetA O n → W.DD T₂ →ₗ[O] W.DD T₂ := fun e =>
    (LinearMap.lsmul (LetA O n) (W.DD T₂) e).restrictScalars O
  let ms : ZMod n → FF →ₗ[O] W.DD T₂ := fun c =>
    Polynomial.aeval (derivationOnWachModule W T₂) (R c) ∘ₗ
        smE (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ a) ∘ₗ ν c +
      Polynomial.aeval (derivationOnWachModule W T₂) (Polynomial.divX (R c)) ∘ₗ smE (uniformizerInverse W) ∘ₗ
        smA (letE c) ∘ₗ z
  have hcore := fun c (hc : c ∈ evens n d) (f : FF) =>
    lift_of_killing_polynomial W T₂ hR hDS hB hA hT₂ c a N s₁ (R c) (hwc c hc) (hkill c hc)
      ((letE c : LetA O n) • z f) (μ c f) (ν c f) (invariant_letter_idempotent_smul W T₂ (hzΔ f)) (hX2 c f).1
      (hX2 c f).2.1 (hX2 c f).2.2.1 (hX2 c f).2.2.2.2.2
  let uL : ZMod n → FF →ₗ[O] W.DD T₂ := fun c =>
    ((PD.p : ℕ) : O) ^ N • ms c - ((PD.p : ℕ) : O) ^ s₁ • μ c
  have hpass : ∀ c ∈ evens n d, (∀ (lenO : ℕ∞) (cc : ℝ) (A : Submodule O FF),
      ∃ B, PChain lenO m cc A B 1 0 ∧ ∀ f ∈ B, uL c f ∈ W.N T₂) ∧
      (m = 0 → ∀ f, uL c f ∈ W.N T₂) := by
    intro c hc
    obtain ⟨τ, hτ⟩ := exists_embedding_over_letter W hA c
    exact step1Pass_pass W T₂ hA hT₂ ζ hζ hEx hER hK hFD c τ hτ
      (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_fd_letter₂ W hS c) (uL c) a m
      (fun f => ⟨(hcore c hc f).2.2.1.1, (hcore c hc f).2.2.1.2, (hcore c hc f).2.2.2⟩)
      (sum_multV_le W hFD hS hE hC hQ c hc τ hτ a (by have := hab c; omega))
  have hout : ∀ F₁ : Submodule O FF, (∀ c ∈ evens n d, ∀ f ∈ F₁, uL c f ∈ W.N T₂) →
      Step1Out W T₂ d a N s₁ z μ F₁ ms := by
    intro F₁ hF c hc f
    exact ⟨(hcore c hc f).1, (hcore c hc f).2.1, (hcore c hc f).2.2.1.2, (hcore c hc f).2.2.2,
      fun hf => hF c hc f hf⟩
  by_cases hm0 : m = 0
  · exact ⟨⊤, ms, (PChain.refl _ _ _ ⊤).mono (Nat.zero_le _) le_rfl, fun _ => rfl,
      hout ⊤ (fun c hc f _ => (hpass c hc).2 hm0 f)⟩
  · obtain ⟨B, hBc, hBP⟩ := iter_chain (lenO := lenOl PD (O := O)) (m := m)
      (c := lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S)
      (fun c B => ∀ f ∈ B, uL c f ∈ W.N T₂) (· ∈ evens n d)
      (fun _ _ _ hBA hP f hf => hP f (hBA hf)) ⊤ 1 0 (fun c hc A _ => (hpass c hc).1 _ _ A)
      (evens n d).toList (fun c hc => Finset.mem_toList.1 hc) ⊤ le_rfl
    refine ⟨B, ms, ?_, fun h => absurd h hm0, hout B (fun c hc => hBP c (Finset.mem_toList.2 hc))⟩
    simpa [Finset.length_toList] using hBc

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end
end

-- Source module: Formalism.SharpRestriction.LevelLetterCocycles.FirstLiftOfUniformizerClause

section

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem first_lift_of_uniformizer_clause [NeZero n] (W : LocWach PD LL O v n) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing O v)
    (h9 : Formalism.MainNotions.LiftingTheory.P9π₀ W) (hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W)
    (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W) (hEx : Sh.ExpRules W) (hER : Sh.ExpRing W)
    (hK : Sh.LemK W) (hFD : Sh.FilDim W) (hB : Sh.BasTool W) (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL)
    (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL) (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) : Step1 W :=
  first_lift_of_hypotheses W hV h9 hRN (rToolMod_dStab W hP9) hD hEx hER hK hFD hB hE hC hQ

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
end
end
