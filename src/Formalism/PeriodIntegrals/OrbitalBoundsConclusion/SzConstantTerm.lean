module

public import Formalism.PeriodIntegrals.SzCt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.FirstCoordinateLeThreeScale
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Development
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.Places

section

@[expose] public section

noncomputable section

namespace PI.SzCt.UnitaryGroupMassFormula

open Formalism.BasicNotions Formalism.MainNotions.G

theorem eTau_tauPl (D : D7) (z : Bool × HH D) :
    (D.eTau (tauPl D z) : D.R.GG) = plGG D z := by
  unfold Formalism.BasicNotions.tauPl
  simp

theorem ramifiedTau1_ne_ramifiedTau2 (φ : Formalism.HC.Frame) (a b : φ.A) : φ.tau1 a ≠ φ.tau2 b := by
  intro h
  have h1 := congrArg (fun x => x.1.1) h
  simp only [Formalism.HC.Frame.tau1, Formalism.HC.Frame.tau2] at h1
  revert h1
  decide

theorem tau1_injective_alt (φ : Formalism.HC.Frame) {a b : φ.A} (h : φ.tau1 a = φ.tau1 b) : a = b := by
  simp only [Formalism.HC.Frame.tau1, Prod.mk.injEq, true_and] at h
  simpa [Formalism.HC.Frame.iota] using h

theorem placeFacts : PlaceFacts := by
  intro D
  have h1 : ∀ t : HH D, (D.eTau (tauPl D (false, t)) : D.R.GG) = D.R.tau1 t := by
    intro t; rw [eTau_tauPl]; simp [plGG]
  have h2 : ∀ t : HH D, (D.eTau (tauPl D (true, t)) : D.R.GG) = D.R.tau2 t := by
    intro t; rw [eTau_tauPl]; simp [plGG]
  have hPsi : ∀ z : Bool × HH D, (D.eTau (tauPl D z) : D.R.GG) ∈ D.R.Psi :=
    fun z => (D.eTau (tauPl D z)).2
  have hnt : ∀ t : HH D, (D.eTau (tauPl D (true, t)) : D.R.GG) ∉ D.host.topPlaces := by
    intro t h
    rw [h2] at h
    unfold Host.topPlaces at h
    obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
    exact ramifiedTau1_ne_ramifiedTau2 _ _ _ ha
  refine ⟨h1, ?_, hnt, ?_⟩
  · intro t ht
    refine ⟨hPsi _, ?_, ?_⟩
    · intro h
      rw [h1] at h
      unfold Host.topPlaces at h
      obtain ⟨a, ha, hat⟩ := Finset.mem_image.1 h
      exact ht (tau1_injective_alt _ hat ▸ ha)
    · intro h
      rw [h1] at h
      unfold Host.thickPlaces at h
      obtain ⟨a, -, ha⟩ := Finset.mem_image.1 h
      exact ramifiedTau1_ne_ramifiedTau2 _ _ _ ha.symm
  · intro t
    by_cases h : (D.eTau (tauPl D (true, t)) : D.R.GG) ∈ D.host.thickPlaces
    · exact Or.inl h
    · exact Or.inr ⟨hPsi _, hnt t, h⟩

end PI.SzCt.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.SizeFacts

section

@[expose] public section

noncomputable section

namespace PI.SzCt.UnitaryGroupMassFormula

open Formalism.BasicNotions Formalism.MainNotions.G

theorem sizeFacts : SizeFacts := by
  intro D L hSz hx
  obtain ⟨-, -, -, -, -, -, -, -, hLa, hRho, hBot, -, -, hEta, -, -, hDel, -⟩ := hSz
  have hx0 : (0 : ℝ) < L.sc.x := by linarith
  have hx1 : (1 : ℝ) ≤ L.sc.x := by linarith
  have hb1 : 1 ≤ L.sc.b := by
    unfold Scale.b
    exact Real.one_le_exp (Real.rpow_nonneg hx0.le _)
  have hb'0 : 0 ≤ L.sc.b' := by
    unfold Scale.b' Scale.a
    exact div_nonneg (mul_nonneg hx0.le (by linarith)) (Real.exp_pos _).le
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    unfold Formalism.BasicNotions.Ranks.n; exact_mod_cast D.R.ord_pos
  have ht1 : (1 : ℝ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have hη := L.etaSz_pos
  refine ⟨?_, ?_, hDel.2.2.2.1, ?_, hEta.2.2.2.2.1, hb1, hb'0⟩
  · intro t
    have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_nonneg hx0.le _) hLa.1
    have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    set Q := Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k with hQ
    have h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
      div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hx0.le _) (Real.log_nonneg hx1)) hLa0) hk0
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have h4 : 4 * Q ≤ 1 := by
      have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * Q := by rw [hQ]; ring
      unfold Formalism.MainNotions.SizeRho at hRho
      linarith
    have h5 := hBot t
    have h6 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = Q * L.sc.b' := by
      rw [hQ]; ring
    rw [h6] at h5
    nlinarith
  · have h := hEta.2.2.2.1
    calc L.etaSz ≤ (D.R.t : ℝ) * L.etaSz := le_mul_of_one_le_left hη.le ht1
      _ ≤ _ := h
  · unfold Scale.w''
    exact div_le_div_of_nonneg_left hb'0 hx0 (le_mul_of_one_le_right hx0.le hn1)

end PI.SzCt.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeCount.SzCtOf

section

@[expose] public section

noncomputable section

namespace PI.SzCt.UnitaryGroupMassFormula

open Formalism.BasicNotions Formalism.MainNotions.G

theorem ct_le (hA : RowA) (hB : RowB) (hC : RowC) (hS : SizeFacts) (hP : PlaceFacts)
    (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (hx : 3 ≤ L.sc.x) (hSz : Formalism.MainNotions.SizesAt L)
    (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (u : D.what₂.Word) (t : HH D) :
    ctD D u j t ≤ (if t ∈ D.host.TT then 2 * L.sc.b else 0) + 4 * (D.R.k : ℝ) * L.sc.b' := by
  obtain ⟨hbT, hη, hkSc, hw'', hmη, hb1, hb'0⟩ := hS D L hSz hx
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hP D
  have hj' := hj
  simp only [SizeData₂.lifts, Finset.mem_Icc] at hj'
  obtain ⟨hj1, hj2⟩ := hj'
  have hk5 : (5 : ℝ) ≤ (D.R.k : ℝ) := by
    have h1 := D.R.m_add_three_le_k
    have h2 := D.R.two_le_m
    exact_mod_cast (by omega : 5 ≤ D.R.k)
  have hx0 : 0 < L.sc.x := by linarith
  have hxne : L.sc.x ≠ 0 := hx0.ne'
  have hSc : 0 < L.Sc := L.Sc_pos
  have hk0 : (0 : ℝ) ≤ (D.R.k : ℝ) := by linarith

  have hq : L.sc.b' / L.sc.x * L.sc.x = L.sc.b' := by field_simp
  have hq0 : 0 ≤ L.sc.b' / L.sc.x := div_nonneg hb'0 hx0.le
  have hbx : 3 * (L.sc.b' / L.sc.x) ≤ L.sc.b' := by nlinarith
  have hkSc0 : 0 ≤ (D.R.k : ℝ) * L.Sc := mul_nonneg hk0 hSc.le
  have hw0 : 0 ≤ L.sc.w'' D.R.n := le_trans hkSc0 hkSc
  have hr : L.sc.w'' D.R.n / L.sc.x * L.sc.x = L.sc.w'' D.R.n := by field_simp
  have hr0 : 0 ≤ L.sc.w'' D.R.n / L.sc.x := div_nonneg hw0 hx0.le
  have hwx : L.sc.w'' D.R.n / L.sc.x ≤ L.sc.w'' D.R.n := by nlinarith
  have h3Sc : 3 * L.Sc ≤ (D.R.k : ℝ) * L.Sc := by nlinarith
  have hkb' : 5 * L.sc.b' ≤ (D.R.k : ℝ) * L.sc.b' := mul_le_mul_of_nonneg_right hk5 hb'0
  have hmη0 : 0 ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
    have : (0 : ℝ) ≤ L.etaSz := by
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hEta, -⟩ := hSz
      exact le_trans (Nat.cast_nonneg _) hEta.1
    positivity
  by_cases ht : t ∈ D.host.TT
  · simp only [ctD, if_pos ht]
    have hRA := hA D L j hj u (tauPl D (false, t))
    have hRC := hC D L P j hj u (tauPl D (true, t)) (hP3 t)
    have hwF := L.win_top j hj1 hj2 (tauPl D (false, t)) ⟨t, ht⟩ (hP1 t)
    have hbt := hbT ⟨t, ht⟩
    have hwT : wj D j (tauPl D (true, t)) ≤ L.sc.b + L.etaSz + 1 ∨
        wj D j (tauPl D (true, t)) ≤ L.sc.w'' D.R.n + L.etaSz := by
      rcases hP4 t with h | h
      · exact Or.inl (L.win_thick j hj1 hj2 _ h).2
      · exact Or.inr (L.win_thin j hj1 hj2 _ h).2
    have hkw : (D.R.k : ℝ) * wj D j (tauPl D (false, t)) ≤
        (D.R.k : ℝ) * ((L.bT ⟨t, ht⟩ : ℝ) + L.sc.b' / L.sc.x + L.etaSz) :=
      mul_le_mul_of_nonneg_left hwF.2 hk0
    have e1 : (D.R.k : ℝ) * ((L.bT ⟨t, ht⟩ : ℝ) + L.sc.b' / L.sc.x + L.etaSz) =
        (D.R.k : ℝ) * (L.bT ⟨t, ht⟩ : ℝ) + (D.R.k : ℝ) * (L.sc.b' / L.sc.x) +
          (D.R.k : ℝ) * L.etaSz := by ring
    have e2 : (D.R.k : ℝ) * (L.Sc + wj D j (tauPl D (false, t))) =
        (D.R.k : ℝ) * L.Sc + (D.R.k : ℝ) * wj D j (tauPl D (false, t)) := by ring
    have k1 : (D.R.k : ℝ) * (L.bT ⟨t, ht⟩ : ℝ) ≤ (D.R.k : ℝ) * (5 / 4 * L.sc.b') :=
      mul_le_mul_of_nonneg_left hbt hk0
    have k2 : (D.R.k : ℝ) * (L.sc.b' / L.sc.x) ≤ (D.R.k : ℝ) * (L.sc.b' / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0
    have k3 : (D.R.k : ℝ) * L.etaSz ≤ (D.R.k : ℝ) * (L.sc.b' / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0
    have e3 : (D.R.k : ℝ) * (5 / 4 * L.sc.b') + (D.R.k : ℝ) * (L.sc.b' / 3) +
        (D.R.k : ℝ) * (L.sc.b' / 3) = 23 / 12 * ((D.R.k : ℝ) * L.sc.b') := by ring
    have e4 : 4 * (D.R.k : ℝ) * L.sc.b' = 4 * ((D.R.k : ℝ) * L.sc.b') := by ring
    rcases hwT with hT | hT <;> linarith
  · simp only [ctD, if_neg ht]
    have hthin := hP2 t ht
    have hRB := hB D L P j hj u (tauPl D (false, t)) hthin.2.1
    have hwF := (L.win_thin j hj1 hj2 (tauPl D (false, t)) hthin).2
    have hkw : (D.R.k : ℝ) * wj D j (tauPl D (false, t)) ≤
        (D.R.k : ℝ) * (L.sc.w'' D.R.n + L.etaSz) :=
      mul_le_mul_of_nonneg_left hwF hk0
    have k1 : (D.R.k : ℝ) * (L.sc.w'' D.R.n + L.etaSz) ≤ (D.R.k : ℝ) * (2 * (L.sc.b' / 3)) :=
      mul_le_mul_of_nonneg_left (by linarith) hk0
    have e1 : ((D.R.k : ℝ) + 2) * L.Sc = (D.R.k : ℝ) * L.Sc + 2 * L.Sc := by ring
    have e2 : (D.R.k : ℝ) * (2 * (L.sc.b' / 3)) = 2 / 3 * ((D.R.k : ℝ) * L.sc.b') := by ring
    have e4 : 4 * (D.R.k : ℝ) * L.sc.b' = 4 * ((D.R.k : ℝ) * L.sc.b') := by ring
    linarith

theorem szCt_of (hA : RowA) (hB : RowB) (hC : RowC) (hS : SizeFacts) (hP : PlaceFacts) :
    PI.SzCt.SzCt := by
  unfold PI.SzCt.SzCt
  intro eps Ct CGam Cc CT2 PK
  refine ⟨3, ?_⟩
  intro D L P _ hx hSz j hj u
  have hsum : ∑ t : HH D, ctD D u j t ≤
      ∑ t : HH D, ((if t ∈ D.host.TT then 2 * L.sc.b else 0) + 4 * (D.R.k : ℝ) * L.sc.b') :=
    Finset.sum_le_sum (fun t _ => ct_le hA hB hC hS hP D L P hx hSz j hj u t)
  refine le_trans hsum ?_
  obtain ⟨-, -, -, -, -, -, hb'0⟩ := hS D L hSz hx
  have hcard : Fintype.card (HH D) = D.R.n := by
    rw [Fintype.card_eq_nat_card]
    show Nat.card (Fin D.R.ord) = D.R.n
    simp [Nat.card_eq_fintype_card, Formalism.BasicNotions.Ranks.n]
  rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const,
    Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, Finset.card_univ, hcard]
  have hf : (D.R.f : ℝ) = 2 * (D.R.n : ℝ) := by
    unfold Formalism.BasicNotions.Ranks.f
    push_cast
    ring
  rw [hf]
  have e : (D.R.n : ℝ) * (4 * (D.R.k : ℝ) * L.sc.b') = 2 * (2 * (D.R.n : ℝ)) * (D.R.k : ℝ) * L.sc.b' := by
    ring
  have e2 : (D.host.TT.card : ℝ) * (2 * L.sc.b) = 2 * (D.host.TT.card : ℝ) * L.sc.b := by ring
  linarith

end PI.SzCt.UnitaryGroupMassFormula
end
end
end

-- Source module: Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SzConstantTerm

section

@[expose] public section

theorem sz_constant_term : PI.SzCt.SzCt :=
  PI.SzCt.UnitaryGroupMassFormula.szCt_of PI.SzCt.UnitaryGroupMassFormula.rowA PI.SzCt.UnitaryGroupMassFormula.rowB PI.SzCt.UnitaryGroupMassFormula.rowC
    PI.SzCt.UnitaryGroupMassFormula.sizeFacts PI.SzCt.UnitaryGroupMassFormula.placeFacts
end
end
