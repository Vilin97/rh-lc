module

public import Formalism.GaussJetBounds.StatementG
public import Formalism.GaussJetBounds.StatementA
public import Formalism.GaussJetBounds.GaussJetProofs.AsmRDotAddRight
public import Formalism.GaussJetBounds.GaussJetProofs.CapacityLeReachCapacity
public import Formalism.GaussJetBounds.GaussJetProofs.FrameCoeffMulLin
public import Formalism.GaussJetBounds.GenLogInverse
public import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
public import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat
public import Formalism.GaussJetBounds.GaussJetProofs.PureCrossTermWeight
import Formalism.GaussJetBounds.GaussJetProofs.SubstitutionWeightBound
public import Formalism.GaussJetBounds.OneLetterRadius
import Formalism.IncomingBounds.FlowDegreeBounds.ProdRangeEqFactorialMulProdIco
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.GaussJetBounds.GaussJetProofs.OneLetterRadiusIdentity
public import Formalism.GaussJetBounds.GaussJetProofs.ThmAJet
import Formalism.GaussJetBounds.OneLetterRadius
public import Formalism.IncomingBounds.WeightIdentities
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Formalism.GaussJetBounds.GaussJetProofs.LemmaRA

section

@[expose] public section

noncomputable section
open scoped BigOperators

universe u v

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem factValA {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K] {l : ℕ}
    (hl : l.Prime) (hlt : ‖(l : K)‖ < 1) {ι : Type v} [Fintype ι] (κ : ι →₀ ℕ) {a : ℕ}
    (ha : 1 ≤ a) (hκa : ∀ i, κ i ≤ a) :
    ‖((mfact κ : ℕ) : K)‖ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
        (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) := by
  classical
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  set L : ℝ := Real.logb l (a : ℝ) + 1 with hL
  have hL0 : 0 ≤ L := by
    have : 0 ≤ Real.logb l (a : ℝ) := Real.logb_nonneg hl1 (by exact_mod_cast ha)
    linarith
  have hcoord : ∀ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖ ≤
      ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) := by
    intro i hi
    have hki : 1 ≤ κ i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have hb := (Formalism.IncomingBounds.padicValFactorialBounds l hl (κ i) hki).1
    have hlog : Real.logb l (κ i : ℝ) ≤ Real.logb l (a : ℝ) :=
      Real.logb_le_logb_of_le hl1 (by exact_mod_cast hki) (by exact_mod_cast hκa i)
    rw [norm_natCast_eq_pow_padicValNat hl hlt (Nat.factorial_ne_zero _), ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le (by rw [hL]; linarith)
  have hmf : ((mfact κ : ℕ) : K) = ∏ i ∈ κ.support, (((κ i).factorial : ℕ) : K) := by
    rw [mfact, Finsupp.prod, Nat.cast_prod]
  rw [hmf, norm_prod]
  calc ∏ i ∈ κ.support, ‖(((κ i).factorial : ℕ) : K)‖
      ≤ ∏ i ∈ κ.support, ‖(l : K)‖ ^ ((κ i : ℝ) / ((l : ℝ) - 1) - L) :=
        Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hcoord
    _ = ‖(l : K)‖ ^ (∑ i ∈ κ.support, ((κ i : ℝ) / ((l : ℝ) - 1) - L)) :=
        (Real.rpow_sum_of_pos hpi0 _ _).symm
    _ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - (Fintype.card ι : ℝ) * L) := by
        apply Real.rpow_le_rpow_of_exponent_ge hpi0 hlt.le
        rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
        have hsum : ∑ i ∈ κ.support, (κ i : ℝ) / ((l : ℝ) - 1) =
            ∑ i, (κ i : ℝ) / ((l : ℝ) - 1) := by
          apply Finset.sum_subset (Finset.subset_univ _)
          intro i _ hi
          rw [Finsupp.notMem_support_iff.mp hi]; simp
        have hcard : (κ.support.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
          exact_mod_cast Finset.card_le_univ _
        rw [hsum]
        nlinarith

theorem lemmaRA_of (hS : LemmaS.{u}) (hG : GenLogWeight.{u, 0}) (hB : LogBridges.{u})
    (hW1 : SubstWt.{u, 0, v}) (hW0 : SubstWt.{u, 0, 0}) (hRM : RadMono.{u, v})
    (hMW : MulWtLe.{u, v}) (hE : ExpWtLe.{u, v})
    (hP : PureCross.{u, v}) : LemmaRA.{u, v} := by
  intro K _ _ _ l d N0 N1 _ hl hodd hd hde hpi K0 hK0 ζ hζ be hbe ι _ _ lt M hM1 hMlt g hg0 hg
    U hU ε hε sig hsig κ a ha hκa hκ
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  have h1 : ‖(l : K)‖ ≤ 1 := hpi.le
  have hrho : 0 ≤ rho l := by
    unfold rho
    apply div_nonneg zero_le_one
    nlinarith
  have hrg : gam l = 1 / ((l : ℝ) - 1) - rho l := by
    have ha : (l : ℝ) - 1 ≠ 0 := by linarith
    have hb : (l : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
    unfold gam rho
    field_simp
    ring
  obtain ⟨hS1, hS2⟩ := hS K l d hl hodd hd hde hpi K0 hK0 ζ hζ be hbe
  have hbe0 : MvPowerSeries.constantCoeff be = 0 := by
    by_contra h
    have h' : MvPowerSeries.coeff 0 be ≠ 0 := by
      rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have := (hbe.2.2.1 0 h').1
    simp [degE] at this
  obtain ⟨hP1, hP2⟩ := hP K l d N0 N1 hl hpi ι M hM1 be hbe0 hS1 hS2
  have hlin0 : ∀ x, MvPowerSeries.constantCoeff (linSub M x) = 0 := by
    intro x
    simp [linSub]
  have hbS0 : MvPowerSeries.constantCoeff (bSum M be) = 0 := by
    unfold bSum

    rw [map_sum]
    refine Finset.sum_eq_zero fun ab _ => ?_
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => hlin0 _) (fun s => hlin0 _) hbe0
  have hr : ∀ i, (fun _ : ι => rho l) i ≤ (fun i => rho l + sig i) i := fun i => by
    simp only
    linarith [hsig i]

  have hBw : WtGeLe ‖(l : K)‖ (fun i => rho l + sig i) (1 / ((l : ℝ) - 1)) κ
      (ε • bSum M be) := by
    intro n hn
    have hεn : ‖ε‖ = 1 := by rcases hε with h | h <;> simp [h]
    have hc : MvPowerSeries.coeff n (ε • bSum M be) = ε * MvPowerSeries.coeff n (bSum M be) := by
      rw [map_smul, smul_eq_mul]
    rw [monoWtGe_iff, hc, norm_mul, hεn, one_mul]
    by_cases hp : ∃ (i j : ι) (α β : ℕ), n = pureMon l i j α β
    · obtain ⟨i, j, α, β, rfl⟩ := hp
      by_cases hw : MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
          (MvPowerSeries.coeff (pureMon l i j α β) (bSum M be))
      · exact asmR_monoWtGe_rad h0 h1 hr hw
      · have hs1 := hκ i j α β hn hw
        have hlow := hP1 (pureMon l i j α β)
        rw [monoWtGe_iff] at hlow
        refine le_trans hlow (Real.rpow_le_rpow_of_exponent_ge h0 h1 ?_)
        rw [asmR_dot_add_right, asmR_dot_pureMon l i j α β sig]
        linarith
    · exact asmR_monoWtGe_rad h0 h1 hr (hP2 n hp)
  have hBc : MvPowerSeries.constantCoeff (ε • bSum M be) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, map_smul,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hbS0, smul_zero]
  have hExp := hE K l hl hpi ι (fun i => rho l + sig i) κ (ε • bSum M be) hBc hBw

  have hU0 : WtGe ‖(l : K)‖ (fun _ : ZV d N0 N1 => rho l) 0 U := by
    intro n
    rw [monoWtGe_iff]
    refine le_trans (hU n) (Real.one_le_rpow_of_pos_of_le_one_of_nonpos h0 h1 ?_)
    linarith [asmR_dot_nonneg n (r := fun _ : ZV d N0 N1 => rho l) fun _ => hrho]
  have hg' : ∀ x, MvPowerSeries.subst g (genLog (K := K) l
      (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2)) x) = MvPowerSeries.X x := by
    intro x
    rw [← (hB K l d N0 N1).2.1 x]
    exact hg x
  have hgw := hG K l hl hpi (ZV d N0 N1) (fun y : ZV d N0 N1 => (y.1 - 2, y.2.1, y.2.2)) g hg0 hg'
  have hgU : WtGe ‖(l : K)‖ (fun _ : ZV d N0 N1 => rho l) 0 (MvPowerSeries.subst g U) :=
    hW0 K ‖(l : K)‖ h0 hpi (ZV d N0 N1) (ZV d N0 N1) g (fun _ => rho l) (fun _ => rho l) 0 U
      hg0 hgw hU0
  have hlinw : ∀ x, WtGe ‖(l : K)‖ (fun _ : ι => rho l) (rho l) (linSub M x) := by
    intro x n
    rw [monoWtGe_iff]

    simp only [linSub, map_sum, MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (Real.rpow_nonneg h0.le _)
      fun i _ => ?_
    split_ifs with h
    · subst h
      rw [mul_one, asmR_dot_single]
      simpa using hM1 x i
    · simpa using Real.rpow_nonneg h0.le _
  have hY : WtGe ‖(l : K)‖ (fun _ : ι => rho l) 0
      (MvPowerSeries.subst (linSub M) (MvPowerSeries.subst g U)) :=
    hW1 K ‖(l : K)‖ h0 hpi (ZV d N0 N1) ι (linSub M) (fun _ => rho l) (fun _ => rho l) 0 _
      hlin0 hlinw hgU
  have hY1 : WtGeLe ‖(l : K)‖ (fun i => rho l + sig i) 0 κ
      (MvPowerSeries.subst (linSub M) (MvPowerSeries.subst g U)) :=
    (hRM K ‖(l : K)‖ h0 hpi ι (fun _ => rho l) (fun i => rho l + sig i) 0 hr).2 κ _
      fun n _ => hY n
  have hk := hMW K ‖(l : K)‖ h0 ι (fun i => rho l + sig i) 0 0 κ _ _ hY1 hExp κ le_rfl
  rw [monoWtGe_iff] at hk
  have hf := factValA (K := K) hl hpi κ ha hκa
  rw [norm_mul]
  calc _ ≤ ‖(l : K)‖ ^ ((∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) -
          (Fintype.card ι : ℝ) * (Real.logb l (a : ℝ) + 1)) *
        ‖(l : K)‖ ^ (0 + 0 - dot κ (fun i => rho l + sig i)) :=
        mul_le_mul hf hk (norm_nonneg _) (Real.rpow_nonneg h0.le _)
    _ = _ := by
      rw [← Real.rpow_add h0]
      congr 1
      rw [asmR_dot_fintype, hrg]
      have key : ∑ i, (κ i : ℝ) * (1 / ((l : ℝ) - 1) - rho l - sig i) =
          (∑ i, (κ i : ℝ) / ((l : ℝ) - 1)) - ∑ i, (κ i : ℝ) * (rho l + sig i) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      linarith

theorem lemma_R_log_loss : LemmaRA.{u, v} :=
  lemmaRA_of lemmaS generalized_log_weight logarithm_weight_comparison substitution_weight_bound substitution_weight_bound radical_weight_monotone
    multiplicative_weight_le exponential_weight_le pure_cross_term_weight

end Formalism.DworkPowerSeriesWeights
end
end
end

-- Source module: Formalism.GaussJetBounds.GaussJetProofs.TheoremAOneMonomialLogLoss

section

@[expose] public section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open Formalism.IncomingBounds

theorem ThmAJetA_of (hS : LemmaS.{u}) (hR : LemmaRA.{u, 0}) (hA : ThmAAssembly)
    (hFP : FramePure.{u}) : ThmAJetA.{u} := by
  intro K _ _ _ l d N0 N1 _ hl hl3 hd hde hpi h0 K0 hK0 ζ hζ be hbe x hx g hg0 hg U hU ε hε
    TT nu1 nu2 size hnu21 hnu1s a ha hsa spec κ hκtop hκD hspec hcap hkill
  classical
  have hodd : Odd l := hl.odd_of_ne_two (by omega)
  have hl2 : 2 ≤ l := hl.two_le
  have hlpos : 0 < l := by omega
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.mpr (Nat.cast_ne_zero.mpr hl.ne_zero)
  obtain ⟨⟨sig, hsigD, hsigA, hFn⟩, -⟩ := lemmaFa l d hl3 hd hde
    (fun s => (Dl d TT nu1 size s : ℝ)) (fun s => Nat.cast_nonneg _)
  have hsig0 : ∀ s, 0 ≤ sig s := fun s => (hsigD.1 s).1
  have hnotop : ∀ (s : ZMod d) (k : Fin N0), (s ∈ TT ∧ k.val = 0) → spec (s, k) = none := by
    intro s k hsk
    rcases h : spec (s, k) with _ | ⟨s0, j⟩
    · rfl
    · exact absurd hsk (hspec s k s0 j h).2.2.2.1
  obtain ⟨eps, heps0, hepsT, hmain⟩ := hA l d hl3 hd hde TT nu1 nu2 size hnu21 hnu1s sig
    ⟨hsigD, hFn⟩ (ZV d N0 N1) (fun y => y.1) (frameTop TT) (fun y => spec (y.1, y.2.1))
    (fun y => κ y)
    (by
      intro i hi
      have hi' := of_decide_eq_true hi
      exact ⟨hi'.1, hnotop _ _ hi'⟩)
    (by
      intro s hs
      have hset : Finset.univ.filter (fun i : ZV d N0 N1 => i.1 = s ∧ frameTop TT i = true) =
          Finset.univ.image (fun b : Fin N1 => ((s, ⟨0, h0⟩, b) : ZV d N0 N1)) := by
        ext ⟨s', k, b⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, frameTop,
          decide_eq_true_eq, Prod.mk.injEq]
        constructor
        · rintro ⟨rfl, -, hk⟩
          exact ⟨b, rfl, Fin.ext hk.symm, rfl⟩
        · rintro ⟨b', rfl, rfl, rfl⟩
          exact ⟨rfl, hs, rfl⟩
      rw [hset, Finset.sum_image (fun b _ b' _ h => by simpa using h)]
      exact_mod_cast hκtop s hs)
    (by intro s; exact_mod_cast hκD s)
    (by
      intro i s0 j h
      obtain ⟨h1, h2, h3, -, h5, h6⟩ := hspec i.1 i.2.1 s0 j h
      exact ⟨h1, h2, h3, h5, h6⟩)
    (by intro s0 j; exact_mod_cast hcap s0 j)
  have R := dualRadiiInequalities l d hl3 hd hde TT sig eps hsigA hsig0 heps0 hepsT
  obtain ⟨hS1, hS2⟩ := hS K l d hl hodd hd hde hpi K0 hK0 ζ hζ be hbe
  have hM1 : ∀ (z i : ZV d N0 N1), ‖frameM (N1 := N1) x z i‖ ≤ 1 := by
    intro z i
    unfold frameM
    split_ifs
    · exact hx _
    · simp
  have hMlt : ∀ (z i : ZV d N0 N1), frameM (N1 := N1) x z i ≠ 0 → i.1 = z.1 := by
    intro z i h
    unfold frameM at h
    split_ifs at h with h'
    · exact h'.1
    · exact absurd rfl h

  have hsmall : ∀ (i j : ZV d N0 N1) (α β : ℕ),
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      i.1 ≠ j.1 ∧ i.1 + (α : ZMod d) = j.1 + (β : ZMod d) ∧ Odd (α + β) := by
    intro i j α β hnot
    apply jet_bipower hde hl2
    by_contra hnb
    apply hnot
    have hc := jet_collapse (fun y : ZV d N0 N1 => y.1) (frameM (N1 := N1) x) hM1 hMlt be
      (pureMon l i j α β)
    have hmd : (pureMon l i j α β).mapDomain (fun y : ZV d N0 N1 => y.1) =
        Finsupp.single i.1 (l ^ α) + Finsupp.single j.1 (l ^ β) := by
      simp [pureMon, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    rw [hmd] at hc
    have h2 := hS2 _ hnb
    rw [monoWtGe_iff] at h2 ⊢
    refine hc.trans (h2.trans_eq ?_)
    congr 2
    rw [asmR_dot_pureMon, dot_add, asmR_dot_single, asmR_dot_single]
    push_cast
    ring

  have key : ∀ (i j : ZV d N0 N1) (α β : ℕ), pureMon l i j α β ≤ κ →
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      frameTop TT i = true → frameTop TT j = false →
      1 ≤ (l : ℝ) ^ α * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) i +
        (l : ℝ) ^ β * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) j := by
    rintro ⟨s0, k0, b⟩ ⟨s, k, b'⟩ α β hle hnot hti htj
    obtain ⟨hne, heq, hab⟩ := hsmall _ _ α β hnot
    simp only at hne heq
    have hti' : s0 ∈ TT ∧ k0.val = 0 := of_decide_eq_true hti
    have htj' : ¬ (s ∈ TT ∧ k.val = 0) := of_decide_eq_false htj
    obtain rfl : k0 = ⟨0, h0⟩ := Fin.ext hti'.2
    rw [jet_rowRad_top l sig eps _ _ _ _ hti]
    obtain ⟨hz, hw⟩ := hFP K l d N0 N1 hl hpi h0 x hx be hS1 s0 s hne k b b' α β
    have hbb : b = b' := by
      by_contra hbb
      apply hnot
      rw [hz hbb, monoWtGe_iff, norm_zero]
      exact Real.rpow_nonneg hpi0.le _
    subst hbb
    have hij : ((s0, ⟨0, h0⟩, b) : ZV d N0 N1) ≠ (s, k, b) := fun h => hne (congrArg Prod.fst h)
    have hκi : l ^ α ≤ κ (s0, ⟨0, h0⟩, b) := by
      have := hle (s0, ⟨0, h0⟩, b)
      simpa [pureMon, Finsupp.single_apply, hij, Ne.symm hij] using this
    have hκj : l ^ β ≤ κ (s, k, b) := by
      have := hle (s, k, b)
      simpa [pureMon, Finsupp.single_apply, hij, Ne.symm hij] using this
    have hnu : κ (s0, ⟨0, h0⟩, b) ≤ nu1 s0 := by
      rw [← hκtop s0 hti'.1]
      exact Finset.single_le_sum (f := fun b => κ (s0, ⟨0, h0⟩, b)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    have hsz : κ (s, k, b) ≤ size s := by
      have h1 : κ (s, k, b) ≤ Dl d TT nu1 size s := by
        rw [← hκD s]
        exact Finset.single_le_sum (f := fun y => κ y) (fun _ _ => Nat.zero_le _)
          (by simp [htj])
      refine h1.trans ?_
      unfold Dl
      split_ifs <;> omega
    obtain ⟨j0, hj0⟩ : ∃ j0 : ℤ, j0 = (α : ℤ) - β := ⟨_, rfl⟩
    have hsj : s = s0 + (j0 : ZMod d) := by
      rw [hj0]
      push_cast
      linear_combination (-1 : ZMod d) * heq
    have hjodd : Odd j0 := by
      obtain ⟨c, hc⟩ := hab
      exact ⟨(c : ℤ) - β, by omega⟩
    have hlev1 : 0 < j0 → l ^ j0.toNat ≤ nu1 s0 := by
      intro hj
      have : j0.toNat = α - β := by omega
      rw [this]
      exact (Nat.pow_le_pow_right hlpos (Nat.sub_le α β)).trans (hκi.trans hnu)
    have hlev2 : j0 < 0 → l ^ (-j0).toNat ≤ size s := by
      intro hj
      have : (-j0).toNat = β - α := by omega
      rw [this]
      exact (Nat.pow_le_pow_right hlpos (Nat.sub_le β α)).trans (hκj.trans hsz)
    by_cases hsp : spec (s, k) = some (s0, j0)
    · rw [jet_rowRad_spec l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
        (fun y => spec (y.1, y.2.1)) (s, k, b) htj hsp]
      rcases lt_trichotomy α β with hαβ | hαβ | hαβ
      · rw [if_neg (by omega)]
        have ht : (-j0).toNat = β - α := by omega
        rw [ht]
        have := R.2.2.1 s0 α (β - α) (max (sig s) ((l : ℝ) ^ (β - α))⁻¹) (by omega)
          (le_max_right _ _)
        rwa [Nat.add_sub_cancel' hαβ.le] at this
      · subst hαβ
        exfalso
        obtain ⟨c, hc⟩ := hab
        omega
      · rw [if_pos (by omega)]
        have ht : j0.toNat = α - β := by omega
        rw [ht]
        have := R.2.1 s0 β (α - β) (max (sig s) (1 - (l : ℝ) ^ (α - β) * eps s0)) (by omega)
          (le_max_right _ _)
        rwa [Nat.add_sub_cancel' hαβ.le] at this
    · exfalso
      apply hnot
      apply hw
      have hk := hkill s0 hti'.1 s k j0 htj' hjodd hsj hlev1 hlev2 hsp
      by_cases hβα : β ≤ α
      · rw [if_pos hβα]
        rw [if_pos (by omega : (0 : ℤ) ≤ j0)] at hk
        have ht : j0.toNat = α - β := by omega
        rwa [ht] at hk
      · rw [if_neg hβα]
        rw [if_neg (by omega : ¬ (0 : ℤ) ≤ j0)] at hk
        have ht : (-j0).toNat = β - α := by omega
        rwa [ht] at hk
  have hpure : ∀ (i j : ZV d N0 N1) (α β : ℕ), pureMon l i j α β ≤ κ →
      ¬ MonoWtGe ‖(l : K)‖ (fun _ => rho l) (1 / ((l : ℝ) - 1)) (pureMon l i j α β)
        (MvPowerSeries.coeff (pureMon l i j α β) (bSum (frameM (N1 := N1) x) be)) →
      1 ≤ (l : ℝ) ^ α * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) i +
        (l : ℝ) ^ β * rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT)
          (fun y => spec (y.1, y.2.1)) j := by
    intro i j α β hle hnot
    obtain ⟨hne, heq, hab⟩ := hsmall i j α β hnot
    have hsw : pureMon l j i β α = pureMon l i j α β := by
      unfold pureMon; exact add_comm _ _
    cases hti : frameTop TT i <;> cases htj : frameTop TT j
    · exact R.1 i.1 j.1 α β _ _ (jet_rowRad_ge l sig eps _ _ _ i hti)
        (jet_rowRad_ge l sig eps _ _ _ j htj) hab heq
    · have h := key j i β α (by rw [hsw]; exact hle) (by rw [hsw]; exact hnot) htj hti
      linarith
    · exact key i j α β hle hnot hti htj
    · rw [jet_rowRad_top l sig eps _ _ _ _ hti, jet_rowRad_top l sig eps _ _ _ _ htj]
      exact R.2.2.2 i.1 (of_decide_eq_true hti).1 j.1 (of_decide_eq_true htj).1 α β hab heq

  have hκa : ∀ y : ZV d N0 N1, κ y ≤ a := by
    rintro ⟨s, k, b⟩
    cases hty : frameTop TT ((s, k, b) : ZV d N0 N1)
    · have h1 : κ (s, k, b) ≤ Dl d TT nu1 size s := by
        rw [← hκD s]
        exact Finset.single_le_sum (f := fun y => κ y) (fun _ _ => Nat.zero_le _)
          (by simp [hty])
      have h2 : Dl d TT nu1 size s ≤ size s := by
        unfold Dl
        split_ifs <;> omega
      exact h1.trans (h2.trans (hsa s))
    · have hty' : s ∈ TT ∧ k.val = 0 := of_decide_eq_true hty
      obtain rfl : k = ⟨0, h0⟩ := Fin.ext hty'.2
      have h1 : κ (s, ⟨0, h0⟩, b) ≤ nu1 s := by
        rw [← hκtop s hty'.1]
        exact Finset.single_le_sum (f := fun b => κ (s, ⟨0, h0⟩, b)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ b)
      exact h1.trans ((hnu1s s).trans (hsa s))
  have hLR := hR K l d N0 N1 hl hodd hd hde hpi K0 hK0 ζ hζ be hbe (ZV d N0 N1)
    (fun y => y.1) (frameM (N1 := N1) x) hM1 hMlt g hg0 hg U hU ε hε
    (rowRad l sig eps (fun y : ZV d N0 N1 => y.1) (frameTop TT) (fun y => spec (y.1, y.2.1)))
    (jet_rowRad_nonneg l sig eps _ _ _ hsig0 heps0) κ a ha hκa hpure
  have hcard : (Fintype.card (ZV d N0 N1) : ℝ) = (d : ℝ) * N0 * N1 := by
    simp only [ZV, Fintype.card_prod, ZMod.card, Fintype.card_fin]
    push_cast
    ring
  rw [hcard] at hLR
  refine hLR.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hpi.le ?_)
  linarith [hmain]

theorem theorem_A_one_monomial_log_loss : ThmAJetA.{u} :=
  ThmAJetA_of lemmaS.{u} lemma_R_log_loss.{u, 0} rowRadiusAssembly frame_pure_weight.{u}

end Formalism.DworkPowerSeriesWeights
end
end
end

-- Source module: Formalism.GaussJetBounds.MonoShapeTop

section

@[expose] public section

universe u v

namespace Formalism.DworkPowerSeriesWeights

theorem thmAJetA : ThmAJetA.{u} := theorem_A_one_monomial_log_loss

end Formalism.DworkPowerSeriesWeights
end
end
