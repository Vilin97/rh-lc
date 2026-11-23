module

public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComplexConjFrobeniusDepthContentBoundProofStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ErealLeMulOfForallLe
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ForcedContentBoundsProgrammeValueGoodPrime
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.InertPrimeDepthContentBoundProofStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LargePrimePackagesDepthNonposStatement
public import Formalism.LocalToGlobal.CharacterGerms.RestNonneg
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LevelsUsedBalancedValueOrbitSums
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
import Mathlib.Tactic.Lemma
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
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitPrimeDepthContentBoundProofStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterBlocksAttainBoundStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypingsStatement
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OddLevelBlockBoundAttainedStatement
public import Development.AutomorphicArithmetic.OrbitLabellings.FMulLeastAdmissibleLevelRowsLe
public import Development.AutomorphicArithmetic.OrbitLabellings.PkgZeroCsNuNonposOfMonSupply
public import Development.AutomorphicArithmetic.OrbitLabellings.RowBoundLeFnumSumAddError
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.LevelLe

section

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RowBudgets

lemma level_le (k l : ℕ) (hk : 1 ≤ k) (hl : 5 ≤ l) :
    ((RF.i0 k l : ℕ) : ℝ) ≤ 3 + 2 * Real.log k := by
  have h := GlobalTheory.LevelsOrbits.levelBound k l hk hl
  have e : RF.i0 k l = Formalism.L2.FormalSeriesBounds.i0 k l := rfl
  rw [e]
  linarith

theorem main : ∀ (r f n m nW T l k : ℕ) (b L A : ℝ), 1 ≤ m → m ≤ n → n ≤ r → 2 ≤ f → 1 ≤ T → n + 1 = k → 3 ≤ L → Real.log k ≤ L → 10 * (r : ℝ) * (f + (f : ℝ) ^ 2 * (n : ℝ) ^ 3 * L ^ 2 / m) ≤ nW →
  8 * r * f ≤ nW ∧ (5 ≤ l → f * (RF.i0 k l * n) + 2 * r * f ≤ nW) ∧
  (3 ≤ l → 0 ≤ b → m * b / (T * f * (n : ℝ) ^ 3 * L) ≤ l → ∃ s : ℕ, 4 * r * s * f ≤ nW ∧ ∀ x : ℕ, (T : ℝ) * x ≤ 3 * b → x ≤ s * (l - 1)) ∧
  (0 < l → (l : ℝ) < m * b / (T * f * (n : ℝ) ^ 3 * L) → b ≤ A → T * f * (n : ℝ) ^ 3 * Real.log k ^ 2 ≤ Real.log k * m * A / l) := by
  intro r f n m nW T l k b L A hm hmn hnr hf hT hk hL hkL hW
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hnr' : (n : ℝ) ≤ r := by exact_mod_cast hnr
  have hf' : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hk1 : 1 ≤ k := by omega
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk1)
  have hn' : (1 : ℝ) ≤ n := hm'.trans hmn'
  have hr' : (1 : ℝ) ≤ r := hn'.trans hnr'
  have hD : (0 : ℝ) < T * f * (n : ℝ) ^ 3 * L := by positivity
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = f * (n : ℝ) ^ 3 * L / m := ⟨_, rfl⟩
  have hYm : Y * m = f * (n : ℝ) ^ 3 * L := by rw [hY]; field_simp
  have hW' : 10 * ((r : ℝ) * f) + 10 * L * (r * f * Y) ≤ nW := by
    refine le_of_eq_of_le ?_ hW
    rw [hY]; ring
  have hYL : L ≤ Y := by
    rw [hY, le_div_iff₀ (by positivity)]
    have h1 : (m : ℝ) ≤ (n : ℝ) ^ 3 := hmn'.trans (le_self_pow₀ hn' (by norm_num))
    have h2 : (n : ℝ) ^ 3 ≤ f * (n : ℝ) ^ 3 := le_mul_of_one_le_left (by positivity) (by linarith)
    have h3 := mul_le_mul_of_nonneg_right (h1.trans h2) (show 0 ≤ L by linarith)
    linarith
  have hrf : (0 : ℝ) ≤ r * f := by positivity
  have hP : (0 : ℝ) ≤ r * f * Y := mul_nonneg hrf (by linarith)
  have hPL : 3 * (r * f * Y) ≤ L * (r * f * Y) := mul_le_mul_of_nonneg_right hL hP
  refine ⟨?_, fun hl => ?_, fun hl hb h => ?_, fun hl h hA => ?_⟩
  · have : (8 * r * f : ℝ) ≤ nW := by linarith
    exact_mod_cast this
  · have h1 : ((RF.i0 k l : ℕ) : ℝ) ≤ 3 * Y := by
      have := level_le k l hk1 hl
      linarith
    have h2 : ((RF.i0 k l : ℕ) : ℝ) * n ≤ 3 * Y * r :=
      mul_le_mul h1 hnr' (by positivity) (by linarith)
    have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ f by positivity)
    have : (f * (((RF.i0 k l : ℕ) : ℝ) * n) + 2 * r * f : ℝ) ≤ nW := by linarith
    exact_mod_cast this
  · have hl' : (3 : ℝ) ≤ l := by exact_mod_cast hl
    have hq : (0 : ℝ) < T * ((l : ℝ) - 1) := mul_pos (by linarith) (by linarith)
    rw [div_le_iff₀ hD] at h
    have hbY : b ≤ l * T * Y := by
      refine le_of_mul_le_mul_left (a := (m : ℝ)) ?_ (by linarith)
      calc (m : ℝ) * b ≤ l * (T * f * (n : ℝ) ^ 3 * L) := h
        _ = l * T * (Y * m) := by rw [hYm]; ring
        _ = _ := by ring
    have hTY : (0 : ℝ) ≤ T * Y := mul_nonneg (by linarith) (by linarith)
    have hz : 3 * b / (T * ((l : ℝ) - 1)) ≤ 6 * Y := by
      rw [div_le_iff₀ hq]
      have := mul_le_mul_of_nonneg_right hl' hTY
      nlinarith
    refine ⟨⌈3 * b / (T * ((l : ℝ) - 1))⌉₊, ?_, fun x hx => ?_⟩
    · have h1 := (Nat.ceil_lt_add_one (show 0 ≤ 3 * b / (T * ((l : ℝ) - 1)) by positivity)).le
      have h2 := mul_le_mul_of_nonneg_left (h1.trans (add_le_add_left hz 1)) hrf
      have : (4 * r * (⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ : ℝ) * f : ℝ) ≤ nW := by linarith
      exact_mod_cast this
    · have h1 := Nat.le_ceil (3 * b / (T * ((l : ℝ) - 1)))
      rw [div_le_iff₀ hq] at h1
      have h2 : (x : ℝ) ≤ (⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ : ℝ) * ((l : ℝ) - 1) := by
        refine le_of_mul_le_mul_left (a := (T : ℝ)) ?_ (by linarith)
        linarith
      have h3 : ((l : ℝ) - 1) = ((l - 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub (by omega)]; simp
      generalize ⌈3 * b / (T * ((l : ℝ) - 1))⌉₊ = s at h2 ⊢
      rw [h3] at h2
      exact_mod_cast h2
  · have hl' : (0 : ℝ) < l := by exact_mod_cast hl
    rw [lt_div_iff₀ hD] at h
    rw [le_div_iff₀ hl']
    have h1 : (m : ℝ) * b ≤ m * A := mul_le_mul_of_nonneg_left hA (by linarith)
    have h2 : l * (T * f * (n : ℝ) ^ 3 * Real.log k) ≤ l * (T * f * (n : ℝ) ^ 3 * L) := by
      gcongr
    have h3 := mul_le_mul_of_nonneg_left (h2.trans (h.le.trans h1)) hlog
    linarith

end GlobalTheory.RowBudgets
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPlaceDepthBoundProof

section

@[expose] public section

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.GoodDepth NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.GoodDepth

theorem le_DF_of_mult_pos {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (τ : E →+* ℂ) (h : 0 < Dw.mult τ) : a (τ, 0) ≤ DF Dw a := by
  unfold DF
  calc a (τ, 0) = a (τ, ((⟨0, h⟩ : Fin (Dw.mult τ)) : ℕ)) := rfl
    _ ≤ ∑ i : Fin (Dw.mult τ), a (τ, i) :=
        Finset.single_le_sum (f := fun i : Fin (Dw.mult τ) => a (τ, i)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ _)
    _ ≤ _ := Finset.single_le_sum (f := fun τ => ∑ i : Fin (Dw.mult τ), a (τ, i)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ τ)

theorem thl_nonneg' (k l : ℕ) : 0 ≤ thl k l := by
  unfold thl
  apply Real.sSup_nonneg
  rintro t ⟨i, -, -, -, rfl⟩
  positivity

theorem one_le_log_of_five_le {k : ℕ} (hk : 5 ≤ k) : 1 ≤ Real.log k := by
  have h5 : (5 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem parOK_parAt {N : NumDatum} {j l : ℕ} (h : ParOK (parOf N j l)) (d : ℕ) [NeZero d] (pos : RPl N.R → ℕ → RPl N.R) :
    ParOK (parAt N j d pos) := ⟨h.card, h.m_pos, h.mk_le, h.r_eq, h.SE_nonneg⟩

theorem degHyp2_parOf {N : NumDatum} {j : ℕ} {W : RPl N.R → ℕ} {T θ0 rest C1 : ℝ}
    (h : RF.DegHyp2 (parAt N j 1 fun z _ => z) W T θ0 rest C1) (l : ℕ) : RF.DegHyp2 (parOf N j l) W T θ0 rest C1 :=
  ⟨h.T_one, h.w_pos, h.TW_lo, h.TW_hi, h.th_rng, h.th_m, h.rest_nonneg, h.rest_le⟩

private theorem odd_ordP_of_conjIn {N : NumDatum} {l : ℕ} (h : ConjIn N l) : Odd (N.ordP l) := by
  unfold NumDatum.ordP
  rw [if_neg (by rw [h.1]; simp)]
  exact h.2

theorem nuGood : NuGoodSt := by
  intro C1 hC1
  obtain ⟨CI, hCI, HI⟩ := GlobalTheory.T.inertPrimeDepthContentBound_proof C1 hC1
  obtain ⟨CP, hCP, HP⟩ := GlobalTheory.T.complexConjFrobeniusDepthContentBound_proof C1 hC1
  obtain ⟨CS, hCS, HS⟩ := GlobalTheory.T.splitPrimeDepthContentBound_proof C1 hC1
  obtain ⟨CC, hCC, HC⟩ := UpperTheory.rowBound_le_Fnum_sum_add_error GlobalTheory.T.oddLevelBlock_bound_attained.2 GlobalTheory.T.characterBlocks_attain_bound.2 GlobalTheory.T.monomialBlock_supply_both_typings.2 C1 hC1
  obtain ⟨HZ, -⟩ := GlobalTheory.T.largePrime_packages_depth_nonpos
  refine ⟨2 * CI + 2 * CP + 2 * CC + CS + 2, by positivity, ?_⟩
  intro E _ _ _ H Dw lv Xo c _ hstar hIC hPk N j pl a nW T b L w hj1 hjm hpl hp hq hdom hG hw hb la h2 hq' hd hg0 hg1 hM
  obtain ⟨PI, PP, PS, PZ, -, PC, PZC⟩ := hPk
  have hl : (resCharOf la).Prime := Crude.resCharOf_prime la
  have hin := hG.inert_ge _ hl
  have red := GlobalTheory.GoodDepth.nuW_bound_of_charts E H Dw lv Xo c hIC la lv.M a nW
  have PI' := PI hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PP' := PP hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PS' := PS hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PZ' := PZ hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PZC' := PZC hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  have PC' := PC hstar N j pl a hj1 hjm hpl hp hq hdom la h2 hq' hd hM hin
  clear PI PP PS PZ PZC PC
  generalize resCharOf la = l at *
  obtain ⟨θ0, hdeg⟩ := hG.deg
  have hT1 : (1 : ℝ) ≤ T := hdeg.T_one
  have hT1' : 1 ≤ T := by exact_mod_cast hT1
  have hwpos : ∀ z, 0 ≤ N.w j z := fun z => (hdeg.w_pos z).le
  have hsum : 0 ≤ ∑ z, N.w j z := Finset.sum_nonneg fun z _ => hwpos z
  have hw0 : 0 ≤ w := hsum.trans hw
  obtain ⟨hF0, htri, hOK, hFC, hFI⟩ := GlobalTheory.ContentValue.main N j l hl h2 hq' hd hg0 hg1 hwpos hG.ratio
  have hm2 := N.R.two_le_m
  have hmk := N.R.m_add_three_le_k
  have hf2 : 2 ≤ N.R.f := hm2.trans N.R.m_le_f
  have hr : N.R.r = N.R.k + N.R.m - 1 := rfl
  have hn : ((N.R.k - 1 : ℕ) : ℝ) = (N.R.k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hl3 : 3 ≤ l := by
    have := hl.two_le
    have := ne_two_of_not_small h2
    omega
  have hlpos : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  obtain ⟨R1, R2, R3, R4⟩ := GlobalTheory.RowBudgets.main N.R.r N.R.f (N.R.k - 1) N.R.m nW T l N.R.k b L w (by omega) (by omega) (by omega)
    hf2 hT1' (by omega) hG.L_ge hG.log_le (by rw [hn]; exact hG.what₂)
  have R5 := UpperTheory.f_mul_leastAdmissibleLevel_rows_le N.R.r N.R.f (N.R.k - 1) N.R.m nW l N.R.k L (by omega) (by omega) (by omega)
    hf2 (by omega) hG.L_ge hG.log_le (by rw [hn]; exact hG.what₂)
  rw [hn] at R3 R4
  have hzero : ∀ s : ℕ, (∀ τ, 0 < Dw.mult τ → a (τ, 0) ≤ s * (l - 1)) → 4 * N.R.r * s * N.R.f ≤ nW →
      ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, y.IsAlg →
      ∀ (C : IntChart T io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e lv.M a nW → ν ≤ 0 := by
    intro s hs hrow V io e ho y hy C ν hν
    by_cases hc : ConjIn N l
    · obtain ⟨Pk, rfl⟩ := PZC' V io e ho y hy C nW ν hν hc.1 (odd_ordP_of_conjIn hc) hwpos s hs hrow
      exact UpperTheory.pkgZeroCs_nu_nonpos_of_monSupply GlobalTheory.T.monomialBlock_supply_both_typings.2 _ _ Pk
    · obtain ⟨d, _, pos, Pk, rfl⟩ := PZ' V io e ho y hy C nW ν hν hc hwpos s hs
        (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num)))) hrow)
      exact HZ _ _ Pk
  have hSE : 0 ≤ N.Sc + N.eta := hOK.SE_nonneg
  have hlog : 1 ≤ Real.log N.R.k := one_le_log_of_five_le (by omega)
  have hth := thl_nonneg' N.R.k l
  set A1 : ℝ := Real.log N.R.k * N.R.m * w / l with hA1
  set A2 : ℝ := N.R.f * N.R.k * (N.Sc + N.eta) / l with hA2
  set A3 : ℝ := N.R.k * thl N.R.k l * w with hA3
  set A4 : ℝ := if N.sc.X'' N.R.n < (l : ℝ) then N.R.k * w / (l : ℝ) ^ 2 else 0 with hA4
  have a1 : 0 ≤ A1 := by positivity
  have a2 : 0 ≤ A2 := by positivity
  have a3 : 0 ≤ A3 := by positivity
  have a4 : 0 ≤ A4 := by rw [hA4]; split_ifs <;> positivity
  have hA4' : (if N.sc.X'' N.R.n < (l : ℝ) then 2 * (N.R.k * (∑ z, N.w j z) / (l : ℝ) ^ 2) else 0) ≤ 2 * A4 := by
    rw [hA4]
    split_ifs
    · gcongr
    · simp
  set B : ℝ := N.FjP j l + (2 * CI + 2 * CP + 2 * CC + CS + 2) * (A1 + A2 + A3 + A4) with hB
  have hB0 : 0 ≤ B := by positivity
  have hTpos : (0 : ℝ) < T := by linarith
  have hmain : ∀ (V : CDVR) (io : c.F →+* V.Fr) (e : ℕ), OverLa la V.V io e → ∀ y : IntFr Xo c V io, y.IsAlg →
      ∀ (C : IntChart V io y) (ν : ℝ), (((ramOverZ la : ℝ) * ν : ℝ) : EReal) ≤ nuLocC C e lv.M a nW → ν ≤ B / T := by
    intro V io e ho y hy C ν hν
    have hBT : 0 ≤ B / T := by positivity
    by_cases hb0 : b < 0
    · refine le_trans (hzero 0 (fun τ hτ => ?_) (by simp) V io e ho y hy C ν hν) hBT
      have h1 := hG.first τ hτ
      have h2 : (0 : ℝ) ≤ (T : ℝ) * a (τ, 0) := by positivity
      exfalso; linarith
    push Not at hb0
    by_cases hl2 : N.R.m * b / (T * N.R.f * ((N.R.k : ℝ) - 1) ^ 3 * L) ≤ l
    · obtain ⟨s, hs1, hs2⟩ := R3 hl3 hb0 hl2
      exact le_trans (hzero s (fun τ hτ => hs2 _ (hG.first τ hτ)) hs1 V io e ho y hy C ν hν) hBT
    push Not at hl2
    have hadd := R4 (by omega) hl2 hb
    have herr : errB (parOf N j l) l T ≤ 2 * (A1 + A2 + A3) := by
      have e1 : Real.log N.R.k * N.R.m * (∑ z, N.w j z) / l ≤ A1 := by rw [hA1]; gcongr
      have e3 : N.R.k * thl N.R.k l * (∑ z, N.w j z) ≤ A3 := by rw [hA3]; gcongr
      have : errB (parOf N j l) l T = Real.log N.R.k * N.R.m * (∑ z, N.w j z) / l + A2 +
        N.R.k * thl N.R.k l * (∑ z, N.w j z) + T * N.R.f * ((N.R.k : ℝ) - 1) ^ 3 * Real.log N.R.k ^ 2 := rfl
      rw [this]; linarith
    rw [le_div_iff₀ hTpos, mul_comm]
    have p1 := mul_nonneg hCI.le a1
    have p2 := mul_nonneg hCI.le a2
    have p3 := mul_nonneg hCI.le a3
    have p4 := mul_nonneg hCI.le a4
    have q1 := mul_nonneg hCP.le a1
    have q2 := mul_nonneg hCP.le a2
    have q3 := mul_nonneg hCP.le a3
    have q4 := mul_nonneg hCP.le a4
    have s1 := mul_nonneg hCS.le a1
    have s2 := mul_nonneg hCS.le a2
    have s3 := mul_nonneg hCS.le a3
    have s4 := mul_nonneg hCS.le a4
    have c1 := mul_nonneg hCC.le a1
    have c2 := mul_nonneg hCC.le a2
    have c3 := mul_nonneg hCC.le a3
    have c4 := mul_nonneg hCC.le a4
    rcases htri with hI | hS
    · have h5 := hin hI
      by_cases hc : PhiC N l
      · obtain ⟨Pk, hT, hν'⟩ := PP' V io e ho y hy C nW ν hν hc T θ0 C1 (degHyp2_parOf hdeg l) R1
        have h1 := HP _ l hOK hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFC hc
        have h3 := mul_le_mul_of_nonneg_left herr hCP.le
        have h1' : (T : ℝ) * ν ≤ ((N.R.k : ℝ) - 1) * (∑ z, N.w j z) / ((l : ℝ) ^ 2 - 1) + CP * errB (parOf N j l) l T := h1
        rw [hB]; linarith
      by_cases hcs : ConjIn N l
      · obtain ⟨Pk, hT, hν'⟩ := PC' V io e ho y hy C nW ν hν hcs.1 (odd_ordP_of_conjIn hcs) T θ0 C1
          (degHyp2_parOf hdeg l) (R5 h5)
        have h1 := HC _ l hOK.card hOK.m_pos hOK.mk_le hOK.r_eq hOK.SE_nonneg hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFI hI hc Pk.Z Pk.hZ
        have h3 := mul_le_mul_of_nonneg_left herr hCC.le
        have h1' := le_trans h1 (add_le_add h2 h3)
        rw [hB]; linarith
      · obtain ⟨Pk, hT, hν'⟩ := PI' V io e ho y hy C nW ν hν hI hcs T θ0 C1 (degHyp2_parOf hdeg l) (R2 h5)
        have h1 := HI _ l hOK hl h5 Pk
        rw [hT, hν'] at h1
        have h2 := hFI hI hc Pk.Z Pk.hZ
        have h3 := mul_le_mul_of_nonneg_left herr hCI.le
        have h1' := le_trans h1 (add_le_add h2 h3)
        rw [hB]; linarith
    · obtain ⟨d, _, pos, Pk, hT, hν'⟩ := PS' V io e ho y hy C nW ν hν hS T θ0 C1 hdeg
        (le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))) R1)
      have h1 := HS _ l (parOK_parAt hOK d pos) hl Pk
      rw [hT, hν'] at h1
      have h1' : (T : ℝ) * ν ≤ CS * ((N.R.m * (∑ z, N.w j z) + N.R.f * N.R.k * (N.Sc + N.eta)) / l) := h1
      have e1 : (N.R.m * (∑ z, N.w j z) + N.R.f * N.R.k * (N.Sc + N.eta)) / l ≤ A1 + A2 := by
        rw [hA1, hA2, add_div]
        have : (N.R.m : ℝ) * (∑ z, N.w j z) ≤ Real.log N.R.k * N.R.m * w := by
          calc (N.R.m : ℝ) * (∑ z, N.w j z) = 1 * N.R.m * (∑ z, N.w j z) := by ring
            _ ≤ _ := by gcongr
        gcongr
      have h3 := mul_le_mul_of_nonneg_left e1 hCS.le
      rw [hB]; linarith
  obtain ⟨r1, r2, -⟩ := red (B / T) (by positivity) hmain
  refine ⟨r1, ?_, fun hDF => ?_⟩
  · rw [le_div_iff₀ hTpos, mul_comm] at r2
    exact r2
  · refine (red 0 le_rfl (hzero 1 (fun τ hτ => ?_) ?_)).2.2 rfl
    · have := le_DF_of_mult_pos Dw a τ hτ
      omega
    · rw [mul_one]
      exact le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by norm_num))) R1

end GlobalTheory.GoodDepth
end
end
