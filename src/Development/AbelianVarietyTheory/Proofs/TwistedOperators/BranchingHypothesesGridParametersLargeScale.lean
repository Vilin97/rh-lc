module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMinusSignsHalfOfEvenStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridNumericalDataRealPlaceGapSizeBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignsMatchBranchingCoordinateEquiv
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
public import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InterlacedSignedParametersStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSeparatedByOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSpacingAndGapStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedParametersBoundedStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignsMatchBranchingCoordinateEquivStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.exists_signsMatchBranchingCoordinate_equiv : ∀ {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool), (Finset.univ.filter fun a => ε a = false).card = (Finset.univ.filter fun i => ε' i = false).card → ∃ e : Option (Fin n) ≃ Fin (n + 1), GlobalTheory.SepReal.Signs e ε ε' := by
  first | exact @GlobalTheory.SepReal.exists_signs_equiv | exact GlobalTheory.SepReal.exists_signs_equiv | (intros; apply GlobalTheory.SepReal.exists_signs_equiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraParamOfEven

section

@[expose] public section

open Formalism.L2.Theta

namespace GlobalTheory.HCEnum

open GlobalTheory.SignedHC GlobalTheory.SignedHC.GridData

theorem isHCParam_parPi_zero_parD0 : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ}
    {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.k → Even G.m → n + 1 = G.k + G.m →
    IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.IsHCParam mu := by
  intro G n lam ε mu ε' hk hm hn hl hmu
  obtain ⟨k', hk'⟩ := hk
  obtain ⟨m', hm'⟩ := hm
  have hkR : (G.k : ℝ) = k' + k' := by rw [hk']; push_cast; ring
  have hmR : (G.m : ℝ) = m' + m' := by rw [hm']; push_cast; ring
  have hnR : (n : ℝ) = (G.k : ℝ) + G.m - 1 := by
    have : ((n + 1 : ℕ) : ℝ) = ((G.k + G.m : ℕ) : ℝ) := by rw [hn]
    push_cast at this; linarith
  refine ⟨⟨hl.1, fun a => ?_⟩, ⟨hmu.1, fun a => ?_⟩⟩
  · obtain ⟨-, q, hq, hS⟩ := hl
    have hmem : (q a, ε a) ∈ G.parPi 0 := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [parPi_zero, mem_lam] at hmem
    rw [hq a]
    rcases hmem with ⟨i, -, he⟩ | ⟨hc, -⟩
    · have e : q a = G.a i := congrArg Prod.fst he
      refine ⟨G.v 2 + ((G.m : ℤ) + 1 - i) * G.ga + 1 - (k' + m'), ?_⟩
      rw [e]; simp only [GridData.a]; push_cast; rw [hnR, hkR, hmR]; ring
    · obtain ⟨i, -, -, hx⟩ := mem_cloudHalf.1 hc
      simp only at hx
      refine ⟨G.v i - (k' + m'), ?_⟩
      rw [hx]; simp only [vHalf]; push_cast; rw [hnR, hkR, hmR]; ring
  · obtain ⟨-, q, hq, hS⟩ := hmu
    have hmem : (q a, ε' a) ∈ G.parD0 := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    rw [mem_discrete_parameter_iff] at hmem
    rw [hq a]
    rcases hmem with ⟨hc, -⟩ | ⟨l, -, -, he⟩
    · obtain ⟨i, -, -, hx⟩ := mem_cloud.1 hc
      simp only at hx
      refine ⟨G.v i - (k' + m' - 1), ?_⟩
      rw [hx]; push_cast; rw [hnR, hkR, hmR]; ring
    · have e : q a = -(G.b l : ℚ) := congrArg Prod.fst he
      refine ⟨-G.b l - (k' + m' - 1), ?_⟩
      rw [e]; push_cast; rw [hnR, hkR, hmR]; ring

end GlobalTheory.HCEnum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraParamOfEvenStatement

section

@[expose] public section

open Formalism.L2.Theta

theorem _root_.GlobalTheory.T.harish_chandra_param_of_even : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.k → Even G.m → n + 1 = G.k + G.m → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → Formalism.QuantumDeterminants.IsHCParam lam ∧ Formalism.QuantumDeterminants.IsHCParam mu := by
  first | exact @GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 | exact GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 | (intros; apply GlobalTheory.HCEnum.isHCParam_parPi_zero_parD0 <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsInterlacedSubSingleOfSpread

section

@[expose] public section

namespace GlobalTheory.SepReal

theorem interlaced_sub_single : ∀ {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ},
    GlobalTheory.SepReal.Interlaced ε lam ε' mu → (∀ a c, a ≠ c → 2 ≤ |lam a - lam c|) → (∀ a i, mu i < lam a → mu i + 1 < lam a) →
      (∀ a i, lam a ≠ mu i) → ∀ s, GlobalTheory.SepReal.Interlaced ε (lam - Pi.single s 1) ε' mu := by
  intro n ε lam ε' mu hI hw hm hne s
  have h01 : ∀ a, (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 0 ∨ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = 1 := by
    intro a
    by_cases h : a = s
    · subst h; simp
    · simp [Pi.single_apply, h]
  have hb : ∀ a, 0 ≤ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ∧ (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a ≤ 1 := by
    intro a
    rcases h01 a with h | h <;> rw [h] <;> norm_num
  have key : ∀ x y : Fin (n + 1) ⊕ Fin n, Sum.elim (lam - Pi.single s 1) mu y < Sum.elim (lam - Pi.single s 1) mu x ↔
      Sum.elim lam mu y < Sum.elim lam mu x := by
    rintro (a | i) (c | j)
    · simp only [Sum.elim_inl, Pi.sub_apply]
      by_cases hac : a = c
      · subst hac; simp
      · have hw' := hw a c hac
        have ha := h01 a
        have hc := h01 c
        generalize (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) a = da at ha
        generalize (Pi.single s (1:ℝ) : Fin (n+1) → ℝ) c = dc at hc
        rcases le_abs.1 hw' with h | h <;> rcases ha with rfl | rfl <;> rcases hc with rfl | rfl <;>
          constructor <;> intro h' <;> linarith
    · simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
      have hba := hb a
      constructor
      · intro h; linarith
      · intro h; have := hm a j h; linarith
    · simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply]
      have hbc := hb c
      constructor
      · intro h
        by_contra h'
        have hlt : mu i < lam c := lt_of_le_of_ne (not_lt.1 h') (fun e => hne c i e.symm)
        have := hm c i hlt
        linarith
      · intro h; linarith
    · simp
  intro x y h hz
  rw [key] at h
  exact hI x y h (fun z hz' => hz z ⟨(key z y).2 hz'.1, (key x z).2 hz'.2⟩)

end GlobalTheory.SepReal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsInterlacedSubSingleOfSpreadStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.isInterlaced_sub_single_of_spread : ∀ {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ}, GlobalTheory.SepReal.Interlaced ε lam ε' mu → (∀ a c, a ≠ c → 2 ≤ |lam a - lam c|) → (∀ a i, mu i < lam a → mu i + 1 < lam a) → (∀ a i, lam a ≠ mu i) → ∀ s, GlobalTheory.SepReal.Interlaced ε (lam - Pi.single s 1) ε' mu := by
  first | exact @GlobalTheory.SepReal.interlaced_sub_single | exact GlobalTheory.SepReal.interlaced_sub_single | (intros; apply GlobalTheory.SepReal.interlaced_sub_single <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSeparatedByOneStatement

section

@[expose] public section

open Formalism.L2.Theta

theorem _root_.GlobalTheory.T.parameters_separated_by_one : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) → 2 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (∀ a i, mu i < lam a → mu i + 1 < lam a) ∧ ∀ a i, lam a ≠ mu i := by
  first | exact @GlobalTheory.WordSep.word_sep | exact GlobalTheory.WordSep.word_sep | (intros; apply GlobalTheory.WordSep.word_sep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.BranchingHypothesesGridParametersLargeScale

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer

private theorem dualPar_dualPar' (S : SPar) : dualPar (dualPar S) = S := by
  unfold dualPar
  rw [Finset.image_image]
  simp [Function.comp_def]

private theorem shift_zero_lemma_2 (S : SPar) : GlobalTheory.SignedHC.shift 0 S = S := by
  unfold GlobalTheory.SignedHC.shift
  simp

private theorem exists_par_of_gridData_bounds {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {ε : Fin (n + 1) → Bool}
    {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ} {B : ℝ}
    (hke : Even G.k) (hme : Even G.m) (hm2 : 2 ≤ G.m) (hn : n + 1 = G.k + G.m) (h3 : 3 ≤ n)
    (hv : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) (hvk : 2 ≤ G.v G.k + G.b 1)
    (hb : ∀ l, 1 ≤ l → l < G.m → (G.b l : ℝ) + 1000 * ((n : ℝ) + 1) ^ 3 ≤ G.b (l + 1))
    (hga : 1000 * ((n : ℝ) + 1) ^ 3 ≤ G.ga) (hvk0 : 0 ≤ G.v G.k) (hb1 : 0 < G.b 1)
    (ha0 : ((G.a 0 : ℚ) : ℝ) ≤ B) (hbm : (G.b G.m : ℝ) ≤ B)
    (hl : IsEnum (G.parPi 0) lam ε) (hm : IsEnum G.parD0 mu ε') :
    ∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu B := by
  have hga0 : 0 < G.ga := by
    have h0 : (0 : ℝ) < 1000 * ((n : ℝ) + 1) ^ 3 := by positivity
    exact_mod_cast h0.trans_le hga
  have hH : (2 : ℝ) ≤ 1000 * ((n : ℝ) + 1) ^ 3 := by
    have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 3 := one_le_pow₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
    linarith
  have hvk1 : 1 ≤ G.v G.k + G.b 1 := by omega
  obtain ⟨hc, hc'⟩ := GlobalTheory.T.card_minus_signs_half_of_even hme hga0 hl hm
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_signsMatchBranchingCoordinate_equiv ε ε' (hc.trans hc'.symm)
  obtain ⟨hHl, hHm⟩ := GlobalTheory.T.harish_chandra_param_of_even hke hme hn hl hm
  have hw := GlobalTheory.T.interlaced_signed_parameters hga0 hvk1 hl hm
  obtain ⟨hs1, hs2⟩ := GlobalTheory.T.parameters_separated_by_one hga0 hv (by omega) hl hm
  obtain ⟨hwl, hwm, hgl, hgm⟩ := GlobalTheory.T.parameters_spacing_and_gap hH hga hv hvk hb hl hm
  have habs : ∀ a c, a ≠ c → 2 ≤ |lam a - lam c| := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h | h
    · exact (hwl a c h).trans (le_abs_self _)
    · rw [abs_sub_comm]
      exact (hwl c a h).trans (le_abs_self _)
  have hB := GlobalTheory.T.signed_parameters_bounded hvk0 hb1 ha0 hbm hl hm
  have hk2 := G.two_le_k
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
    (fun i => ε' i = false)
  have hneg : ∃ i, ε' i = false := by
    have hpos : 0 < (Finset.univ.filter fun i => ε' i = false).card := by
      rw [hc']
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  have hpos : (Finset.univ.filter fun i => ε' i = false).card ≤ (Finset.univ.filter fun i => ε' i = true).card := by
    have heq : (Finset.univ.filter fun i => ¬ ε' i = false) = Finset.univ.filter fun i => ε' i = true := by
      ext i
      simp
    rw [heq, Finset.card_univ, Fintype.card_fin] at hsum
    omega
  exact ⟨e, he, h3, hHl, hHm, hw, GlobalTheory.T.isInterlaced_sub_single_of_spread hw habs hs1 hs2, hwl, hwm, hgl, hgm, hneg, hpos, hB⟩

theorem realInputPar : Ev fun {D} _ _ {sc} _ _ _ => ∀ (τ : D.what₂.Tau) (ε : Fin (D.R.r + 1) → Bool) (lam : Fin (D.R.r + 1) → ℝ)
    (ε' : Fin D.R.r → Bool) (mu : Fin D.R.r → ℝ), IsEnum (Node.par D sc.cGap (.core 0) τ) lam ε →
    IsEnum (dualPar (parB (Ptw D) 0 τ)) mu ε' → (∃ e, GlobalTheory.SepReal.Par e ε lam ε' mu (sc.b ^ 2)) ∧
      Real.log (8 * ((D.R.r : ℝ) + 1) * sc.b ^ 2) ≤ 6 * Real.log sc.b ∧ 0 ≤ Real.log sc.b := by
  intro _ _ _
  refine ⟨0, fun D large₂ _ _ hS T L μ0 _ Gr W M _ => ?_⟩
  intro τ ε lam ε' mu hlam hmu
  obtain ⟨hv, hvk, hb, hga, hvk0, hb1, ha0, hbm, hb1', hb4⟩ := GlobalTheory.T.chiGridNumericalData_realPlace_gap_size_bounds D large₂ hS τ
  have hl : IsEnum ((GlobalTheory.ChiGrid.num D 1 τ).parPi 0) lam ε := hlam
  have hD : dualPar (parB (Ptw D) 0 τ) = (GlobalTheory.ChiGrid.num D 1 τ).parD0 := by
    rw [← GlobalTheory.SignedHC.GridData.parD_zero_zero, parB, ← parV_zero D 1 (Nat.zero_le _) τ, dualPar_dualPar']
    show GlobalTheory.SignedHC.shift (if Odd (0 + 0) then -(1 / 2) else 0) _ = _
    rw [if_neg (by decide), shift_zero_lemma_2]
  have hm' : IsEnum (GlobalTheory.ChiGrid.num D 1 τ).parD0 mu ε' := hD ▸ hmu
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h2m := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  refine ⟨exists_par_of_gridData_bounds (n := D.R.r) D.R.k_even D.R.m_even h2m
    (by show D.R.r + 1 = D.R.k + D.R.m; omega) (by omega) hv hvk hb hga hvk0 hb1 ha0 hbm hl hm', ?_,
    Real.log_nonneg hb1'⟩
  have hbpos : 0 < large₂.sc.b := by linarith
  show Real.log (8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2) ≤ 6 * Real.log large₂.sc.b
  have h6 := Real.log_pow large₂.sc.b 6
  push_cast at h6
  rw [← h6]
  apply Real.log_le_log (by positivity)
  calc 8 * ((D.R.r : ℝ) + 1) * large₂.sc.b ^ 2 ≤ large₂.sc.b ^ 4 * large₂.sc.b ^ 2 := by gcongr
    _ = large₂.sc.b ^ 6 := by ring

end GlobalTheory.SepPer
end
end
