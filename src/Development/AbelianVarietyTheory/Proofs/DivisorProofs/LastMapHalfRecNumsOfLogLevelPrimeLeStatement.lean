module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ColHeightSharpWith
public import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastSideLogBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliDeterminantFirstRowsMemBmW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingListCharacterProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBoundIffOrthBound
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InitMinorNeZeroOfStrictMono
import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NonnegSubOfLt
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InterlacingEquivariance

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthNormLogBound

section

@[expose] public section

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BranchingDeterminantCap Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col GlobalTheory.BrCompare GlobalTheory.BrCompare.Shift

noncomputable section

namespace GlobalTheory.BranchLogBound

variable {n : ℕ} {lam : DomWeight (n + 1)} {sg : DomWeight n}

def sgN (lam : DomWeight (n + 1)) (sg : DomWeight n) : Fin n → ℕ := fun i => (sg.w i - lam.w (Fin.last n)).toNat

theorem interlace_w (h : Br.Interlace rfl lam sg) : Formalism.BranchingDeterminantCap.Interlace lam.w sg.w := by
  intro i
  have : 0 ≤ sg.w i - lam.w i.succ ∧ 0 ≤ lam.w i.castSucc - sg.w i := h i
  omega

theorem sgN_cast (h : Br.Interlace rfl lam sg) (i : Fin n) : (sgN lam sg i : ℤ) = sg.w i - lam.w (Fin.last n) := by
  have h1 := (interlace_w h i).2
  have h2 := lam.anti (Fin.le_last i.succ)
  unfold sgN
  omega

theorem interlace_N (h : Br.Interlace rfl lam sg) : Formalism.BranchingDeterminantCap.Interlace (lamZ (lamN lam)) (fun i => (sgN lam sg i : ℤ)) := by
  intro i
  have := interlace_w h i
  simp only [lamZ_lamN, sgN_cast h]
  omega

theorem xiBr_eq (h : Br.Interlace rfl lam sg) (K : Type) [Field K] :
    Br.xiBr K rfl lam sg = incl K n (xiB K (lamN lam) (sgN lam sg)) := by
  have hb : ∀ s, (Br.bBr rfl lam sg s).toNat = lamN lam s - sgN lam sg s := by
    intro s
    have h1 := lamN_cast lam s
    have h2 := sgN_cast h s
    have h3 : Br.bBr rfl lam sg s = lam.w s.castSucc - sg.w s := rfl
    rw [h3]
    omega
  have ha : ∀ s, (Br.aBr rfl lam sg s).toNat = sgN lam sg s - nuNext (lamN lam) s := by
    intro s
    have h1 := nuNext_cast lam s
    have h2 := sgN_cast h s
    have h3 : Br.aBr rfl lam sg s = sg.w s - lam.w s.succ := rfl
    rw [h3]
    omega
  unfold Br.xiBr xiB
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, map_pow, map_pow, rename_initMinor, rename_initMinor, ha, hb]
  congr 2

theorem extremal_eq (lam : DomWeight (n + 1)) (K : Type) [Field K] :
    extremal K (n + 1) lam = incl K n (hw K (Nat.le_succ n) (lamN lam)) := by
  unfold extremal hw
  rw [map_prod, Fin.prod_univ_castSucc]
  have h0 : lam.natW (Fin.last n) = 0 := by
    have := natW_top lam (Fin.last n)
    omega
  rw [h0, Nat.zero_sub, pow_zero, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_pow]
  congr 1
  · exact (rename_initMinor K (Fin.castLE (by have := i.2; omega) : Fin (i.val + 1) → Fin (n + 1)) (by have := i.2; omega)).symm
  · have h1 := nuNext_cast lam i
    have h2 := natW_top lam i.succ
    have h3 : nuNext lam.natW i.castSucc = lam.natW i.succ := by
      unfold nuNext
      rw [dite_eq_left (by simp)]
      rfl
    rw [h3]
    have h4 : lamN lam i = lam.natW i.castSucc := rfl
    omega

theorem fockF_map {σ : Type} (f : MvPolynomial σ ℝ) :
    (Formalism.REAL.fockF (map (algebraMap ℝ ℂ) f) (map (algebraMap ℝ ℂ) f)).re = fockB f f := by
  unfold Formalism.REAL.fockF fockB
  rw [support_map_of_injective _ (algebraMap ℝ ℂ).injective, Complex.re_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have : ∀ (x : ℝ) (k : ℕ), ((algebraMap ℝ ℂ x) * (starRingEnd ℂ) (algebraMap ℝ ℂ x) * (k : ℂ)).re = x * x * k := by
    intro x k
    simp
  rw [coeff_map]
  exact this _ _

theorem map_xiB (l s : Fin n → ℕ) : map (algebraMap ℝ ℂ) (xiB ℝ l s) = xiB ℂ l s := by
  simp only [xiB, map_prod, map_mul, map_pow, initMinor, RingHom.map_det]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 3 <;> ext1 a b <;> simp

theorem kap_bounds (h : Br.Interlace rfl lam sg) :
    0 < Br.kapBr ℝ rfl lam sg ∧ Br.kapBr ℝ rfl lam sg ≤ weylProd (lamZ (lamN lam)) := by
  have h1 := xiNorm n (lamN lam) (sgN lam sg) (interlace_N h)
  have h2 := (fockPos _ _ (GlobalTheory.Branching.xiB_ne_zero (lamN lam) (sgN lam sg))).1
  have h3 := (fockPos _ _ (hwNe ℂ (n + 1) n (Nat.le_succ n) (lamN lam))).1
  have e : hw ℂ (Nat.le_succ n) (lamN lam) = map (algebraMap ℝ ℂ) (hw ℝ (Nat.le_succ n) (lamN lam)) :=
    (lclosedeq_hw_map _ _ _).symm
  rw [← map_xiB, fockF_map] at h1 h2
  rw [e, fockF_map] at h1 h3
  unfold Br.kapBr
  rw [xiBr_eq h, extremal_eq, fockB_incl, fockB_incl]
  exact ⟨div_pos h2 h3, (div_le_iff₀ h3).2 h1⟩

theorem spread_eq (lam : DomWeight (n + 1)) : lam.spread = lam.w 0 - lam.w (Fin.last n) + (n + 1 : ℕ) := by
  unfold DomWeight.spread
  rw [dite_eq_left (Nat.succ_pos n)]
  rfl

theorem kap_le (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    Br.kapBr ℝ rfl lam sg ≤ A ^ ((n + 1) * n / 2) := by
  have ha : Antitone (lamZ (lamN lam)) := fun a b hab => by
    have := lam.anti hab
    simp only [lamZ_lamN]
    omega
  refine (kap_bounds h).2.trans ((weylDimBound n _ ha).2.trans ?_)
  have h0 := ha (Fin.zero_le (Fin.last n))
  refine pow_le_pow_left₀ (add_nonneg (by exact_mod_cast sub_nonneg.2 h0) (Nat.cast_nonneg n)) ?_ _
  rw [spread_eq] at hA
  simp only [lamZ_lamN]
  push_cast at hA ⊢
  linarith

theorem cBr_eq (lam : DomWeight (n + 1)) (sg : DomWeight n) : Br.cBr rfl lam sg = cCap lam.w sg.w := by
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun v _ => Finset.prod_congr rfl fun j _ => ?_
  ring

theorem c_bounds (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    Br.cBr rfl lam sg ≠ 0 ∧ |((Br.cBr rfl lam sg : ℤ) : ℝ)| ≤ A ^ (n * (GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg).toNat) := by
  obtain ⟨h1, h2⟩ := capConst n lam.w sg.w (interlace_w h)
  rw [cBr_eq]
  refine ⟨h1, ?_⟩
  have e : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg = d1 lam.w sg.w := rfl
  rw [e]
  have h3 : |((cCap lam.w sg.w : ℤ) : ℝ)| ≤
      ((lam.w 0 - lam.w (Fin.last n) + (n : ℤ) - 1 : ℤ) : ℝ) ^ (n * (d1 lam.w sg.w).toNat) := by exact_mod_cast h2
  refine h3.trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h0 := lam.anti (Fin.zero_le (Fin.last n))
  refine pow_le_pow_left₀ (by exact_mod_cast (by omega : (0 : ℤ) ≤ lam.w 0 - lam.w (Fin.last n) + (n : ℤ) - 1)) ?_ _
  rw [spread_eq] at hA
  push_cast at hA ⊢
  linarith

theorem one_position (h : Br.Interlace rfl lam sg) {A : ℝ} (hA : ((lam.spread : ℤ) : ℝ) ≤ A) :
    0 < ((Br.cBr rfl lam sg : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ rfl lam sg ∧
    Real.log (((Br.cBr rfl lam sg : ℤ) : ℝ) ^ 2 * Br.kapBr ℝ rfl lam sg) ≤
      (2 * (((n + 1 : ℕ) : ℝ) - 1) * ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg : ℤ) : ℝ) +
        ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) - 1) / 2) * Real.log A := by
  obtain ⟨c1, c2⟩ := c_bounds h hA
  have k1 := (kap_bounds h).1
  have k2 := kap_le h hA
  have c0 : ((Br.cBr rfl lam sg : ℤ) : ℝ) ≠ 0 := by exact_mod_cast c1
  have hd : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg := (interlaceIdent n lam.w sg.w (interlace_w h)).2.2.2.1
  have hd' : (((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg).toNat : ℕ) : ℝ) = ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne rfl lam sg : ℤ) : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg hd)
  have he : (((n + 1) * n / 2 : ℕ) : ℝ) = ((n : ℝ) + 1) * n / 2 := by
    rw [Nat.cast_div (by rw [mul_comm]; exact (Nat.even_mul_succ_self n).two_dvd) (by norm_num)]
    push_cast
    ring
  refine ⟨by positivity, ?_⟩
  have l1 := Real.log_le_log (abs_pos.2 c0) c2
  have l2 := Real.log_le_log k1 k2
  rw [Real.log_pow, Real.log_abs, Nat.cast_mul, hd'] at l1
  rw [Real.log_pow, he] at l2
  rw [Real.log_mul (pow_ne_zero 2 c0) k1.ne', Real.log_pow]
  push_cast
  linarith

theorem orthNormLogBound : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.OrthNormLogBound := by
  refine ⟨2, fun ι _ N n hN lam sg h1 a ha => ?_⟩
  refine ⟨?_, ?_, GlobalTheory.BrNormCompare.last_ineq hN lam sg h1 a ha⟩
  · subst hN
    exact Finset.prod_pos fun τ _ => (one_position (h1 τ) (ha τ)).1
  · subst hN
    unfold GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.orthNormSq
    rw [Real.log_prod fun τ _ => (one_position (h1 τ) (ha τ)).1.ne']
    exact Finset.sum_le_sum fun τ _ => (one_position (h1 τ) (ha τ)).2

end GlobalTheory.BranchLogBound
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapHalfRecNumsOfLogLevelPrimeLe

section

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.LastSideProof

theorem lastSide_of_logT_le : ∀ (CY CT : ℝ) (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau)
    (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)),
    WeightTie N W pl u δ → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T u : ℝ) ≤ CT * N.R.m * N.sc.L →
    1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R CT (lastLog W u) := by
  intro CY CT N X Pr W pl u δ J _ eJ R hWT hS hSR hlogT hT hR
  obtain ⟨C, hC⟩ := GlobalTheory.BranchLogBound.orthNormLogBound
  have hW : W.Ok := hWT.1
  have hk := N.R.m_add_three_le_k
  have hm := N.R.two_le_m
  obtain ⟨hL, ha, -, -, hmR, -, hkR, hNn, hSc, hη, hb', -⟩ := hR.nums
  obtain ⟨-, -, -, -, -, hnodes, hcloud, -, hbT, hoff⟩ := id hSR
  have hNq : ((N.Nm : ℕ) : ℝ) = (N.R.k : ℝ) + (N.R.m : ℝ) * ((N.R.t : ℝ) + 1) := by
    unfold NumDatum.Nm Ranks.N; push_cast; ring

  let lam1 : RPl N.R → ℝ := fun z => (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ)
  let D0 : RPl N.R → ℝ := fun z => ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
  let D1 : RPl N.R → ℝ := fun z =>
    ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
  let logc : RPl N.R → ℝ := fun z => (R.Nn - 1) * D1 z * Real.log (2 * R.a)
  let logxi : RPl N.R → ℝ := fun _ => R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)
  let bT : RPl N.R → ℝ := fun z => ((N.bT z.2 : ℚ) : ℝ)

  have hrow : ∀ z, (W.hc u (pl z)).v = (N.hc z).v ∧ (W.hc u (pl z)).b = (N.hc z).b ∧ (W.hc u (pl z)).e = (N.hc z).e := fun z =>
    ⟨congrArg RowPar.v (hWT.2.2 z).1, congrArg RowPar.b (hWT.2.2 z).1, congrArg RowPar.e (hWT.2.2 z).1⟩
  have hu0 : ∀ z, (W.hc u (pl z)).u ⟨0, by omega⟩ = (N.hc z).u ⟨0, by omega⟩ := fun z =>
    ((hWT.2.2 z).2 _).trans (uW_first N δ z _)
  have hul : ∀ z, (W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ = (N.hc z).u ⟨N.R.k - 1, by omega⟩ := fun z =>
    ((hWT.2.2 z).2 _).trans (uW_last N δ z _)
  have hlam1 : ∀ z, lam1 z = (((N.hc z).u ⟨0, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 -
      (N.R.m : ℝ) * (((N.R.t : ℝ) + 1) / 2) := by
    intro z
    have h := congrArg (fun q : ℚ => (q : ℝ)) (ext_lam_lo W u (pl z) 0 (by omega))
    rw [hu0 z] at h
    push_cast at h
    show (ext (W.lamTrue u N.R.m (pl z)) 0 : ℝ) = _
    rw [h]; ring
  have hsumB : ∀ z, ((∑ B ∈ Finset.range N.R.m, ((RowPar.of (W.hc u (pl z))).eAt B - (RowPar.of (W.hc u (pl z))).bAt B -
      ((N.R.t : ℚ) + 1) / 2) : ℚ) : ℝ) ≤ (N.R.m : ℝ) * N.eta := by
    intro z
    push_cast
    have : ∀ B ∈ Finset.range N.R.m, (((RowPar.of (W.hc u (pl z))).eAt B : ℚ) : ℝ) - (((RowPar.of (W.hc u (pl z))).bAt B : ℚ) : ℝ) -
        ((N.R.t : ℝ) + 1) / 2 ≤ N.eta := by
      intro B hB
      rw [Finset.mem_range] at hB
      rw [RowPar.eAt_of _ hB, RowPar.bAt_of _ hB, (hrow z).2.1, (hrow z).2.2]
      have h1 := hnodes z ⟨B, hB⟩ ⟨B, hB⟩
      have h2 := neg_abs_le ((((N.hc z).b ⟨B, hB⟩ - (N.hc z).e ⟨B, hB⟩ : ℚ) : ℝ))
      push_cast at h1 h2
      have ht : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
      linarith
    refine (Finset.sum_le_sum this).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hD0 : ∀ z, D0 z ≤ N.Sc + (N.R.m : ℝ) * N.eta + (if z ∈ R.TT then bT z else 0) := by
    intro z
    have h := castQ (bottomRank_sum_le_two_mul_totalRank W hW u (pl z))
    push_cast at h
    have hB := hsumB z
    push_cast at hB
    have hv0 := hcloud z ⟨0, by omega⟩
    rw [← (hrow z).1] at hv0
    have hv0' : (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ) ≤ N.Sc := hv0.2
    have hkR' : (5 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 5 ≤ N.R.k)
    show ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤ _
    split_ifs with htop
    · obtain ⟨h1, h2⟩ := (hR.tops z).1 htop
      have hbz : bT z = -(((N.hc z).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) - ((N.R.k : ℝ) - 1) / 2 := by
        show ((N.bT z.2 : ℚ) : ℝ) = _
        obtain ⟨b, t⟩ := z
        simp only at h1
        subst h1
        unfold NumDatum.bT
        push_cast
        rfl
      rw [hbz, ← hul z]
      linarith
    · have hzero : (0 : ℚ) ≤ (N.hc z).v ⟨N.R.k - 2, by omega⟩ := (hcloud z ⟨N.R.k - 2, by omega⟩).1
      obtain ⟨hlast, -, -⟩ := hoff z (fun h => htop ((hR.tops z).2 h)) (by omega)
      have hl : (((W.hc u (pl z)).u ⟨N.R.k - 1, by omega⟩ : ℚ) : ℝ) = (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) - 1 / 2 := by
        rw [hul z, hlast]; push_cast; ring
      have hzero' : (0 : ℝ) ≤ (((N.hc z).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hzero
      rw [hl] at h
      linarith
  have hD1 : ∀ z, D1 z ≤ 3 * D0 z + N.Sc + N.eta := by
    intro z
    have h := castQ (dOne_le_place W hW u (pl z))
    push_cast at h
    have hv0 := (hcloud z ⟨0, by omega⟩).2
    have hvk := (hcloud z ⟨N.R.k - 2, by omega⟩).1
    rw [← (hrow z).1] at hv0 hvk
    have hvk' : (0 : ℝ) ≤ (((W.hc u (pl z)).v ⟨N.R.k - 2, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hvk
    have hu1 : (((W.hc u (pl z)).u ⟨1, by omega⟩ : ℚ) : ℝ) < (((W.hc u (pl z)).v ⟨0, by omega⟩ : ℚ) : ℝ) := by
      exact_mod_cast (W.hc u (pl z)).v_gt_u ⟨0, by omega⟩
    rw [RowPar.eAt_of _ (by omega : N.R.m - 1 < N.R.m), RowPar.eAt_of _ (by omega : 0 < N.R.m)] at h
    have hg := (W.hc u (pl z)).gap_be ⟨0, by omega⟩
    have hg' : ((((W.hc u (pl z)).b ⟨0, by omega⟩ : ℚ)) : ℝ) ≤ (((W.hc u (pl z)).e ⟨0, by omega⟩ : ℚ) : ℝ) := by
      have ht : (0 : ℚ) ≤ N.R.t := Nat.cast_nonneg _
      exact_mod_cast (by linarith : (W.hc u (pl z)).b ⟨0, by omega⟩ ≤ (W.hc u (pl z)).e ⟨0, by omega⟩)
    have hn := hnodes z ⟨0, by omega⟩ ⟨N.R.m - 1, by omega⟩
    rw [← (hrow z).2.1, ← (hrow z).2.2] at hn
    have hn' := neg_abs_le ((((W.hc u (pl z)).b ⟨0, by omega⟩ - (W.hc u (pl z)).e ⟨N.R.m - 1, by omega⟩ : ℚ) : ℝ))
    push_cast at hn hn'
    have hkR' : (5 : ℝ) ≤ N.R.k := by exact_mod_cast (by omega : 5 ≤ N.R.k)
    have hmt : (0 : ℝ) ≤ ((N.R.m : ℝ) - 1) * ((N.R.t : ℝ) + 1) := by
      have : (1 : ℝ) ≤ N.R.m := by exact_mod_cast (by omega : 1 ≤ N.R.m)
      have : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _

      have : (0 : ℝ) ≤ N.R.t := Nat.cast_nonneg _
      nlinarith
    show ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) ≤
      3 * ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) + N.Sc + N.eta
    linarith
  refine ⟨bT, fun z => lam1 z - D0 z, lam1, D0, D1, logc, logxi, ?_, fun z => le_rfl, fun z => le_rfl, fun z => rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hI : (∀ τ, Br.Interlace (N_m_succ N.R) (W.lamTrue u N.R.m τ) (W.sgTrue τ)) ∧ ∀ τ, Br.SameShift (W.lamTrue u N.R.m τ) (W.sgTrue τ) :=
      ⟨fun τ => GlobalTheory.BranchMembers.interlace W hW u τ, fun τ => GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.members_sameShift W hW u τ⟩
    have hsp : ∀ τ, (((W.lamTrue u N.R.m τ).spread : ℤ) : ℝ) ≤ 2 * N.sc.a := fun τ => hS.spread_le u N.R.m le_rfl τ
    obtain ⟨-, hlog, -⟩ := hC X.Tau (N.R.N N.R.m) (N.R.N N.R.m - 1) (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue
      hI.1 N.sc.a hsp
    have hA : lastLog W u = -((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) * Real.log (Pr.T u : ℝ) +
        Real.log (GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.orthNormSq (N_m_succ N.R) (fun τ => W.lamTrue u N.R.m τ) W.sgTrue) := rfl
    have h0 : ∀ z, ext (W.lamTrue u N.R.m (pl z)) 0 = (W.lamTrue u N.R.m (pl z)).w ⟨0, N.R.N_pos N.R.m⟩ := fun z =>
      ext_of _ ⟨0, _⟩
    have hn : ((∑ τ, Br.nBr (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) = ∑ z, (lam1 z - D0 z) := by
      rw [Int.cast_sum, ← Equiv.sum_comp pl]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [nBr_eq_sub (N_m_succ N.R)]
      show _ = ((ext (W.lamTrue u N.R.m (pl z)) 0 : ℤ) : ℝ) -
        ((Br.d0 (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ)
      rw [h0]
      push_cast
      rfl
    have hre : ∑ τ, (2 * (((N.R.N N.R.m : ℕ) : ℝ) - 1) *
          ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m τ) (W.sgTrue τ) : ℤ) : ℝ) +
          ((N.R.N N.R.m : ℕ) : ℝ) * (((N.R.N N.R.m : ℕ) : ℝ) - 1) / 2) * Real.log (2 * N.sc.a) =
        ∑ z, (2 * logc z + logxi z) := by
      rw [← Equiv.sum_comp pl]
      refine Finset.sum_congr rfl fun z _ => ?_
      show _ = 2 * ((R.Nn - 1) * ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ N.R) (W.lamTrue u N.R.m (pl z)) (W.sgTrue (pl z)) : ℤ) : ℝ) *
        Real.log (2 * R.a)) + R.Nn * (R.Nn - 1) / 2 * Real.log (2 * R.a)
      rw [hNn, ha]
      unfold NumDatum.Nm
      ring
    show lastLog W u ≤ -(∑ z, (lam1 z - D0 z) * R.logT) + ∑ z, (2 * logc z + logxi z)
    rw [hA, hn, hR.logT, ← Finset.sum_mul, ← hre]
    linarith
  · intro z hz
    obtain ⟨h1, h2⟩ := (hR.tops z).1 hz
    obtain ⟨b, t⟩ := z
    simp only at h1
    subst h1
    rw [hlam1, hR.aT t h2, hNn, hkR, hNq]
    unfold NumDatum.aT
    push_cast
    ring
  · intro z hz
    obtain ⟨-, hS1, -⟩ := hoff z (fun h => hz ((hR.tops z).2 h)) (by omega)
    have hv := (hcloud z ⟨0, by omega⟩).1
    have hv' : (0 : ℝ) ≤ (((N.hc z).v ⟨0, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast hv
    rw [hlam1, hSc, hNn, hNq]
    push_cast at hS1
    linarith
  · intro z
    rw [hSc, hmR, hη]
    exact hD0 z
  · intro z
    rw [hSc, hη]
    exact hD1 z
  · intro z hz
    obtain ⟨h1, h2⟩ := (hR.tops z).1 hz
    obtain ⟨b, t⟩ := z
    simp only at h1
    subst h1
    rw [hb']
    exact (hbT t h2).2
  · rw [hR.logT]
    exact Real.log_nonneg (by exact_mod_cast hT)
  · rw [hR.logT, hmR, hL]
    exact hlogT

end GlobalTheory.ColRows.LastSideProof
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastMapHalfRecNumsOfLogLevelPrimeLeStatement

section

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

theorem _root_.GlobalTheory.T.lastMapHalf_recNums_of_log_levelPrime_le : ∀ (CY CT : ℝ) (N : NumDatum) (X : Fields) (Pr : Primes X) (W : Wts X Pr.Word N.R) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N) (J : Type) [Fintype J] (eJ : J ≃ Fin N.R.m) (R : RecNums J (RPl N.R)), WeightTie N W pl u δ → Sizes Pr W N.sc.a → GlobalTheory.Core.Ht2.SizeRowsS CY N δ → Real.log (Pr.T u : ℝ) ≤ CT * N.R.m * N.sc.L → 1 ≤ Pr.T u → Reads N eJ δ (Pr.T u) R → LastSide R CT (lastLog W u) := by
  first | exact @GlobalTheory.ColRows.LastSideProof.lastSide_of_logT_le | exact GlobalTheory.ColRows.LastSideProof.lastSide_of_logT_le | (intros; apply GlobalTheory.ColRows.LastSideProof.lastSide_of_logT_le <;> assumption)
end
end
