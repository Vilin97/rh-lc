module

public import Development.AbelianVarietyTheory.Definitions.Jets.SupWOfSup
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OnePointBasisFundamentalDomainVolume
public import Formalism.HermitianCurvature.StatementI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
public import Formalism.HermitianCurvature.StatementM
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TwoBracketsLePowMulProdEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
import Mathlib.RingTheory.WittVector.IsPoly
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WaveGridLiftGridOfLayoutNormaliserBound
import Mathlib.Algebra.Order.Star.Real
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Cut_BPEq
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqLeShifted

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGridFiveApartOnCut

section

@[expose] public section

open Formalism.FourierDecayAlt Finset

namespace GlobalTheory

theorem exists_grid_five_apart_on_cut :
    (∀ (u u' : ℕ → ℝ) (l M₀ : ℕ), 5 * (M₀ : ℝ) ≤ |u l - u' l| → ∃ Y : Finset ℝ, M₀ ≤ Y.card ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧
      ∀ y ∈ Y, I.OnCut u u' l y ∧ I.OnCut u u' l (y + 1)) ∧
    ∀ r : ℕ, 5 * (3 * (r + 1) * (2 * r + 1)) ≤ 30 * (r + 1) ^ 2 + 6 := by
  refine ⟨fun u u' l M₀ h => ?_, fun r => by nlinarith [Nat.zero_le r]⟩
  have hmax : min (u l) (u' l) + 5 * (M₀ : ℝ) ≤ max (u l) (u' l) := by
    have := max_sub_min_eq_abs (u l) (u' l)
    rw [abs_sub_comm] at h
    linarith
  refine ⟨(range M₀).image (fun i : ℕ => -(min (u l) (u' l) + 3 + 5 * (i : ℝ))), ?_, ?_, ?_⟩
  · rw [card_image_of_injective, card_range]
    intro i j hij
    have : (i : ℝ) = j := by
      simp only at hij
      linarith
    exact_mod_cast this
  · intro y hy y' hy' hne
    obtain ⟨i, -, rfl⟩ := mem_image.1 hy
    obtain ⟨j, -, rfl⟩ := mem_image.1 hy'
    have hij : i ≠ j := fun e => hne (by rw [e])
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast hlt
      exact le_trans (by linarith) (le_abs_self _)
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast hlt
      exact le_trans (by linarith) (neg_le_abs _)
  · intro y hy
    obtain ⟨i, hi, rfl⟩ := mem_image.1 hy
    have h1 : (i : ℝ) + 1 ≤ M₀ := by exact_mod_cast mem_range.1 hi
    have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    unfold I.OnCut
    rcases le_total (u l) (u' l) with hle | hle
    · rw [min_eq_left hle, max_eq_right hle] at hmax
      rw [min_eq_left hle]
      exact ⟨Or.inl ⟨by linarith, by linarith⟩, Or.inl ⟨by linarith, by linarith⟩⟩
    · rw [min_eq_right hle, max_eq_left hle] at hmax
      rw [min_eq_right hle]
      exact ⟨Or.inr ⟨by linarith, by linarith⟩, Or.inr ⟨by linarith, by linarith⟩⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.Imports

section

@[expose] public section

open Finset

namespace GlobalTheory.LamSize

theorem main : ∀ (C b T T' : ℝ) (r N : ℕ), 0 ≤ C → 3 ≤ b → (N : ℝ) ≤ b → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T → b ^ (-(C * ((2 * r + 2 : ℕ) : ℝ))) ≤ T' → 1 ≤ b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ)) ∧ (N : ℝ) * b ^ (11 * (2 * r + 2)) ≤ (b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 * (T * T') := by
  intro C b T T' r N hC hb hN hT hT'
  have hm1 : 1 ≤ 2 * r + 2 := by omega
  generalize 2 * r + 2 = m at *
  have hb0 : 0 < b := by linarith
  have hb1 : 1 ≤ b := by linarith
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine ⟨Real.one_le_rpow hb1 (by positivity), ?_⟩
  have hp : 0 < b ^ (-(C * (m : ℝ))) := Real.rpow_pos_of_pos hb0 _
  have hTT : b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))) ≤ T * T' :=
    mul_le_mul hT hT' hp.le (hp.le.trans hT)
  have key : (b ^ ((6 + C) * (m : ℝ))) ^ 2 * (b ^ (-(C * (m : ℝ))) * b ^ (-(C * (m : ℝ))))
      = b ^ (12 * m) := by
    rw [sq, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_add hb0, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  calc (N : ℝ) * b ^ (11 * m) ≤ b * b ^ (11 * m) := by gcongr
    _ = b ^ (11 * m + 1) := by ring
    _ ≤ b ^ (12 * m) := pow_le_pow_right₀ hb1 (by omega)
    _ = _ := key.symm
    _ ≤ _ := by gcongr

end GlobalTheory.LamSize
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdFinEqProdIcc

section

@[expose] public section

open Formalism.FourierDecayAlt Finset

namespace GlobalTheory.NormaliserCutBound

theorem prod_fin_eq_prod_Icc (n : ℕ) (f : Fin n → ℝ) (g : ℕ → ℝ)
    (h : ∀ s : Fin n, g (s.val + 1) = f s) : ∏ s, f s = ∏ s ∈ Finset.Icc 1 n, g s := by
  have h1 : ∏ s, f s = ∏ s : Fin n, g (s.val + 1) := Finset.prod_congr rfl (fun s _ => (h s).symm)
  rw [h1, Fin.prod_univ_eq_prod_range (fun s => g (s + 1)) n, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.prod_Ico_eq_prod_range]
  simp [add_comm]

theorem qC_re (P : M.Par) (y : ℝ) :
    (M.qC P (y : ℂ)).re = I.qpoly P.k P.T P.T' P.u P.u' y := by
  have : M.qC P (y : ℂ) = ((I.qpoly P.k P.T P.T' P.u P.u' y : ℝ) : ℂ) := by
    unfold M.qC I.qpoly
    push_cast
    rfl
  rw [this, Complex.ofReal_re]

theorem main : ∀ (C b c : ℝ) (P : M.Par) (l : ℕ) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (nn : ℝ → ℝ) (Y : Finset ℝ), P.OK → 0 ≤ C → 1 ≤ l → l ≤ P.k → 1 ≤ c → c + 2 ≤ b → (P.k : ℝ) ≤ b → |P.u l| ≤ b → |P.u' l| ≤ b → (∀ s, |lam s| ≤ b) → (∀ s t : Fin (2 * P.r + P.k + 1), s.val + 1 = t.val → t.val + 2 ≤ P.k → lam t + 2 * c ≤ lam s) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u (s.val + 2) + 1 / 2 ≤ lam s)) → (∀ s : Fin (2 * P.r + P.k + 1), s.val + 2 ≤ P.k → (s.val + 1 ≠ l → lam s + 1 / 2 ≤ P.u' (s.val + 1)) ∧ (s.val + 2 ≠ l → P.u' (s.val + 2) + 1 / 2 ≤ lam s)) → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T → b ^ (-(C * ((2 * P.r + 2 : ℕ) : ℝ))) ≤ P.T' → (∀ y, 0 ≤ nn y ∧ nn y ≤ ∏ s, (|y + lam s| + c)) → (∀ y ∈ Y, I.OnCut P.u P.u' l y) → ∀ y ∈ Y, nn y * nn (y + 1) ≤ (b ^ ((6 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) ^ 2 * (M.qC P (y : ℂ)).re := by
  intro C b c P l lam nn Y hP hC hl hlk hc hcb hkb hu hu' hlam hgap hint hint' hT hT' hnn hcut y hy
  have hcy := hcut y hy
  have hb3 : 3 ≤ b := by linarith
  obtain ⟨n, hn⟩ : ∃ n, n = 2 * P.r + P.k + 1 := ⟨_, rfl⟩
  revert lam
  rw [← hn]
  intro lam hlam hgap hint hint' hnn
  let lamN : ℕ → ℝ := fun s => if h : s - 1 < n then lam ⟨s - 1, h⟩ else 0
  have hlamN : ∀ s : Fin n, lamN (s.val + 1) = lam s := by
    intro s
    simp [lamN, s.isLt]
  have hlamN' : ∀ (s : ℕ) (h : s - 1 < n), lamN s = lam ⟨s - 1, h⟩ := by
    intro s h
    simp [lamN, h]
  have hn' : P.k + 2 * P.r + 1 = n := by omega
  have hinter : I.Interlaces P.k P.u P.u' P.lo := by
    intro i hi
    have hg := hP.gap i hi
    unfold M.Par.hi at hg
    have h1 := min_le_left (P.u i) (P.u' i)
    have h2 := min_le_right (P.u i) (P.u' i)
    have h3 := le_max_left (P.u (i + 1)) (P.u' (i + 1))
    have h4 := le_max_right (P.u (i + 1)) (P.u' (i + 1))
    refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> unfold M.Par.lo <;> linarith
  have hint2 : ∀ v : ℕ → ℝ, (∀ s : Fin n, s.val + 2 ≤ P.k →
      (s.val + 1 ≠ l → lam s + 1 / 2 ≤ v (s.val + 1)) ∧
        (s.val + 2 ≠ l → v (s.val + 2) + 1 / 2 ≤ lam s)) →
      ∀ s : ℕ, 1 ≤ s → s + 1 ≤ P.k → (s ≠ l → lamN s + 1 / 2 ≤ v s) ∧
        (s + 1 ≠ l → v (s + 1) + 1 / 2 ≤ lamN s) := by
    intro v hv s hs hsk
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    have ht : t < n := by omega
    have h := hv ⟨t, ht⟩ hsk
    rw [← hlamN ⟨t, ht⟩] at h
    exact h
  have hmain := GlobalTheory.two_brackets_le_pow_mul_prod_entries P.k P.r l b c y lamN P.u P.u' hl hlk hc hcb
    hkb hu hu'
    (by
      intro s hs
      rw [Finset.mem_Icc] at hs
      rw [hlamN' s (by omega)]
      exact hlam _)
    (by
      intro s hs hsk
      obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
      have ht : t < n := by omega
      have ht' : t + 1 < n := by omega
      have h := hgap ⟨t, ht⟩ ⟨t + 1, ht'⟩ rfl (by simp only; omega)
      rw [← hlamN ⟨t, ht⟩, ← hlamN ⟨t + 1, ht'⟩] at h
      exact h)
    (hint2 _ hint) (hint2 _ hint')
    (by
      intro i hi hik
      obtain ⟨h1, h2, h3, h4⟩ := hinter i (Finset.mem_Icc.mpr ⟨hi, hik⟩)
      refine ⟨by linarith, by linarith, by linarith, by linarith⟩)
    hcy
  rw [hn'] at hmain
  have e0 : ∏ s, (|y + lam s| + c) = ∏ s ∈ Finset.Icc 1 n, (|y + lamN s| + c) :=
    prod_fin_eq_prod_Icc n _ (fun s => |y + lamN s| + c) (fun s => by simp only [hlamN])
  have e1 : ∏ s, (|y + 1 + lam s| + c) = ∏ s ∈ Finset.Icc 1 n, (|y + 1 + lamN s| + c) :=
    prod_fin_eq_prod_Icc n _ (fun s => |y + 1 + lamN s| + c) (fun s => by simp only [hlamN])
  rw [← e0, ← e1] at hmain
  have hq := Formalism.FourierDecayAlt.P.q_positive_interlacing P.k P.u P.u' P.lo l y P.T P.T' hl hlk hinter hcy
    hP.T_pos hP.T'_pos
  have hTT : 0 < P.T * P.T' := mul_pos hP.T_pos hP.T'_pos
  have hqe : I.qpoly P.k P.T P.T' P.u P.u' y = (P.T * P.T') *
      ∏ i ∈ Finset.Icc 1 P.k, |(y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)| := by
    rw [← abs_of_pos hq]
    unfold I.qpoly
    rw [abs_mul, abs_neg, abs_of_pos hTT, Finset.abs_prod]
  have hsize := (GlobalTheory.LamSize.main C b P.T P.T' P.r 1 hC hb3 (by push_cast; linarith) hT hT').2
  rw [Nat.cast_one, one_mul] at hsize
  have hA : 0 ≤ ∏ i ∈ Finset.Icc 1 P.k, |(y + 1 / 2 + P.u i) * (y + 1 / 2 + P.u' i)| :=
    Finset.prod_nonneg (fun _ _ => abs_nonneg _)
  rw [qC_re, hqe, ← mul_assoc]
  calc nn y * nn (y + 1) ≤ (∏ s, (|y + lam s| + c)) * ∏ s, (|y + 1 + lam s| + c) :=
        mul_le_mul (hnn y).2 (hnn (y + 1)).2 (hnn (y + 1)).1 ((hnn y).1.trans (hnn y).2)
    _ ≤ _ := hmain
    _ ≤ _ := mul_le_mul_of_nonneg_right hsize hA

end GlobalTheory.NormaliserCutBound
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.WaveGridLiftGridOfLayoutNormaliserBoundStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P

theorem _root_.GlobalTheory.T.waveGrid_liftGrid_of_layout_normaliserBound : ∀ (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (Y : Finset ℝ) (Λ Λ₀ : ℝ) (K N : ℕ), (∀ y, 0 < nn y) → ((∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧ N * (2 * P.r + 1) ≤ Y.card ∧ ∀ y ∈ Y, I.OnCut P.u P.u' p.l0 y ∧ I.OnCut P.u P.u' p.l0 (y + 1)) → (∀ y ∈ Y, nn y * nn (y + 1) ≤ Λ₀ ^ 2 * (M.qC P (y : ℂ)).re) → 0 ≤ Λ → Λ₀ ^ 2 * (5 / 4 : ℝ) ^ N ≤ Λ ^ 2 → TBBx5.WaveGrid p nn Y Λ K N ∧ TBBx5.LiftGrid p nn Y Λ K N := by
  first | exact @GlobalTheory.GridsFromLayout.main | exact GlobalTheory.GridsFromLayout.main | (intros; apply GlobalTheory.GridsFromLayout.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.GridsAtPlaceLongCutNormaliserPositive

section

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

namespace GlobalTheory.GridAtPlace

theorem pow_absorb (C b : ℝ) (r : ℕ) (hb : 3 ≤ b) :
    (b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 * (5 / 4 : ℝ) ^ (3 * (r + 1)) ≤
      (b ^ ((7 + C) * ((2 * r + 2 : ℕ) : ℝ))) ^ 2 := by
  have hb0 : 0 < b := by linarith
  have e : b ^ ((7 + C) * ((2 * r + 2 : ℕ) : ℝ)) =
      b ^ ((6 + C) * ((2 * r + 2 : ℕ) : ℝ)) * b ^ (2 * r + 2) := by
    rw [← Real.rpow_natCast b (2 * r + 2), ← Real.rpow_add hb0]
    congr 1
    ring
  rw [e, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [← pow_mul]
  calc (5 / 4 : ℝ) ^ (3 * (r + 1)) ≤ b ^ (3 * (r + 1)) :=
        pow_le_pow_left₀ (by norm_num) (by linarith) _
    _ ≤ b ^ ((2 * r + 2) * 2) := pow_le_pow_right₀ (by linarith) (by omega)

theorem main : ∀ (C b c : ℝ) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ), 0 ≤ C → GridNum C b c P p.l0 lam → ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0| → (∀ y, 0 < Pst lam c y) ∧ 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∃ Y : Finset ℝ, TBBx5.WaveGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) ∧ TBBx5.LiftGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) := by
  intro C b c P Wp Wq _ _ _ _ _ _ p lam hC hG hcut
  obtain ⟨hc, hcb, hkb, hu, hu', hlam, hgap, hint, hint', hT, hT'⟩ := hG
  have hb3 : 3 ≤ b := by linarith
  have hpos : ∀ y, 0 < Pst lam c y := fun y =>
    Finset.prod_pos (fun s _ => by have := abs_nonneg (y + lam s); linarith)
  have hone : 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) :=
    Real.one_le_rpow (by linarith) (by positivity)
  refine ⟨hpos, hone, ?_⟩
  obtain ⟨Y, hcard, hsep, hon⟩ := GlobalTheory.exists_grid_five_apart_on_cut.1 P.u P.u' p.l0
    (3 * (P.r + 1) * (2 * P.r + 1)) (le_trans (by
      exact_mod_cast GlobalTheory.exists_grid_five_apart_on_cut.2 P.r) hcut)
  have hNQ := GlobalTheory.NormaliserCutBound.main C b c P p.l0 lam (Pst lam c) Y p.hP.1 hC p.hl.1 p.hl.2.1 hc hcb hkb
    hu hu' hlam (fun s t hst _ => hgap s t (by rw [Fin.lt_def]; omega)) hint hint' hT hT'
    (fun y => ⟨(hpos y).le, le_rfl⟩) (fun y hy => (hon y hy).1)
  exact ⟨Y, GlobalTheory.T.waveGrid_liftGrid_of_layout_normaliserBound P Wp Wq p (Pst lam c) Y _ _ 3 (3 * (P.r + 1)) hpos ⟨hsep, hcard, hon⟩ hNQ
    (by linarith) (pow_absorb C b P.r hb3)⟩

end GlobalTheory.GridAtPlace
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.GridsAtPlaceLongCutNormaliserPositiveStatement

section

@[expose] public section

open BpJoin Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 Formalism.FourierDecayAlt.P.CutBPEq Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.grids_at_place_longCut_normaliserPositive : ∀ (C b c : ℝ) (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (p : KB.Pl P Wp Wq) (lam : Fin (2 * P.r + P.k + 1) → ℝ), 0 ≤ C → GridNum C b c P p.l0 lam → ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ |P.u p.l0 - P.u' p.l0| → (∀ y, 0 < Pst lam c y) ∧ 1 ≤ b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∃ Y : Finset ℝ, TBBx5.WaveGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) ∧ TBBx5.LiftGrid p (Pst lam c) Y (b ^ ((7 + C) * ((2 * P.r + 2 : ℕ) : ℝ))) 3 (3 * (P.r + 1)) := by
  first | exact @GlobalTheory.GridAtPlace.main | exact GlobalTheory.GridAtPlace.main | (intros; apply GlobalTheory.GridAtPlace.main <;> assumption)
end
end
