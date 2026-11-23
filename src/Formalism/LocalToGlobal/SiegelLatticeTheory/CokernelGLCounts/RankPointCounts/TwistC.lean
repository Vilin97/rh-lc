module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabIntPfLatSk
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NatMulMem
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SgmPinvEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NegOnePowMulSelf
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MemDdPowMulQd

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnitCons

section

@[expose] public section

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (w : Point D.host.E (D.R.rS + 1))

theorem E_strict {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) (i j : Fin (D.R.rS + 1)) (hji : j ≤ i) :
    (X - Psi w X⁻¹) i j = 0 := by
  have hP := Psi_upU w (upU_inv hU) (blk_inv w hU hB)
  rw [Matrix.sub_apply]
  rcases eq_or_lt_of_le hji with h | h
  · subst h; rw [(hU _ _).2 rfl, (hP _ _).2 rfl, sub_self]
  · rw [(hU _ _).1 h, (hP _ _).1 h, sub_self]

theorem unitCons (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ q, Agree δ M q) {X : MatR D} (hU : UpU X) (hB : IsBlockDiagonalMatrix w X) (hG : GrD X)
    {a c : Fin (D.R.rS + 1)} (hac : a < c)
    (hlow : ∀ i j : Fin (D.R.rS + 1), i < j → j.val - i.val < c.val - a.val →
      (X - Psi w X⁻¹) i j ∈ qdPow D (j.val - i.val)) :
    Psi w (X - Psi w X⁻¹) a c - (X - Psi w X⁻¹) a c ∈ qdPow D (c.val - a.val) := by
  have hXd : IsUnit X.det := by rw [upU_det hU]; exact isUnit_one
  have hXi := upU_inv hU
  have hBi := blk_inv w hU hB
  have hGi := grD_inv hU hG
  have hY := Psi_upU w hU hB
  have hGY := Psi_grD w δ M hA hB hG
  have hPi : Psi w X⁻¹ = (Psi w X)⁻¹ := Psi_inv w hXd
  have hYd : IsUnit (Psi w X).det := by rw [upU_det hY]; exact isUnit_one
  have hES := E_strict w hU hB
  have hPE : Psi w (X - Psi w X⁻¹) = Psi w X * (X - Psi w X⁻¹) * X⁻¹ := by
    rw [Psi_sub, Psi_Psi w hBi, hPi, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_nonsing_inv_cancel_right _ _ hXd,
      Matrix.mul_nonsing_inv _ hYd, Matrix.one_mul]
  have decomp : Psi w X * (X - Psi w X⁻¹) * X⁻¹ - (X - Psi w X⁻¹) =
      (Psi w X - 1) * (X - Psi w X⁻¹) * X⁻¹ + (X - Psi w X⁻¹) * (X⁻¹ - 1) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]; abel
  rw [hPE, ← Matrix.sub_apply, decomp, Matrix.add_apply]
  have hac' : a.val < c.val := hac
  refine (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem ?_ ?_
  · rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases h1 : a < i
    · have h1' : a.val < i.val := h1
      by_cases h2 : i < j
      · have h2' : i.val < j.val := h2
        by_cases h3 : j ≤ c
        · have h3' : j.val ≤ c.val := h3
          rw [show (Psi w X - 1) a i = Psi w X a i by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h1), sub_zero]]
          have m1 := hGY a i (le_of_lt h1)
          have m2 := hlow i j h2 (by omega)
          have m3 := hGi j c h3
          have := mem_qdPow_mul (mem_ddPow_mul_qd m1 m2) m3
          rwa [show i.val - a.val + (j.val - i.val) + (c.val - j.val) = c.val - a.val by omega] at this
        · rw [(hXi j c).1 (lt_of_not_ge h3), mul_zero]; exact FractionalIdeal.zero_mem _
      · rw [hES i j (not_lt.1 h2), mul_zero, zero_mul]; exact FractionalIdeal.zero_mem _
    · have h0 : (Psi w X - 1) a i = 0 := by
        rw [Matrix.sub_apply]
        rcases eq_or_lt_of_le (not_lt.1 h1) with h | h
        · rw [h, (hY _ _).2 rfl, Matrix.one_apply_eq, sub_self]
        · rw [(hY _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]
      rw [h0, zero_mul, zero_mul]; exact FractionalIdeal.zero_mem _
  · rw [Matrix.mul_apply]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases h1 : a < j
    · have h1' : a.val < j.val := h1
      by_cases h2 : j < c
      · have h2' : j.val < c.val := h2
        rw [show (X⁻¹ - 1) j c = X⁻¹ j c by rw [Matrix.sub_apply, Matrix.one_apply_ne (ne_of_lt h2), sub_zero]]
        have := mem_qdPow_mul (hlow a j h1 (by omega)) (hGi j c (le_of_lt h2))
        rwa [show j.val - a.val + (c.val - j.val) = c.val - a.val by omega] at this
      · have h0 : (X⁻¹ - 1) j c = 0 := by
          rw [Matrix.sub_apply]
          rcases eq_or_lt_of_le (not_lt.1 h2) with h | h
          · rw [h, (hXi _ _).2 rfl, Matrix.one_apply_eq, sub_self]
          · rw [(hXi _ _).1 h, Matrix.one_apply_ne (ne_of_gt h), sub_self]
        rw [h0, mul_zero]; exact FractionalIdeal.zero_mem _
    · rw [hES a j (not_lt.1 h1), zero_mul]; exact FractionalIdeal.zero_mem _

end Formalism.L2.SG.Pf.StabIntLat
end
end
end

-- Source module: Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.TwistC

section

@[expose] public section

noncomputable section

open scoped Classical

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.PairVal Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.PtCell Formalism.L2.SG.RealObj
  Formalism.L2.SG.Pf.BlockPermutation Formalism.L2.SG.Pf.StabIntSh

namespace Formalism.L2.SG.Pf.StabIntLat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem twistC : TwistC D := by
  intro δ M hA hodd w y
  have hm : 2 * mOdd D = gS D + 1 := by unfold mOdd; obtain ⟨k, hk⟩ := hodd; omega
  have hm' : (1 : D.host.E) - 2 * (mOdd D : D.host.E) = -((gS D : ℕ) : D.host.E) := by
    have : ((2 * mOdd D : ℕ) : D.host.E) = ((gS D + 1 : ℕ) : D.host.E) := by rw [hm]
    push_cast at this; linear_combination -this
  have hEq := E_q w y
  have hτs : ∀ q, selfP w q → τA w q y = (mOdd D : D.host.E) * cf w y q := fun q h => by simp [τA, h]
  have hτu : ∀ q, ¬ selfP w q → upperM w q →
      τA w q y = sgq w (qbar w q) * D.conjF (-(y (qbar w q)) + cf w y (qbar w q)) := fun q h1 h2 => by
    simp [τA, h1, h2]
  have hτl : ∀ q, ¬ selfP w q → ¬ upperM w q → τA w q y = 0 := fun q h1 h2 => by simp [τA, h1, h2]
  have hΛs : ∀ q, selfP w q → ∀ z, z ∈ Λq w q ↔
      z ∈ ddPow D (hgt w q) ∧ z + sgq w q * D.conjF z ∈ qdPow D (hgt w q) := fun q h z => by
    simp only [Λq, h, if_true]; rfl
  have hΛu : ∀ q, ¬ selfP w q → upperM w q → ∀ z, z ∈ Λq w q ↔ z ∈ qdPow D (hgt w q) := fun q h1 h2 z => by
    simp only [Λq, Iq, h1, h2, if_false, not_true_eq_false, or_self]; rfl
  have hΛl : ∀ q, ¬ selfP w q → ¬ upperM w q → ∀ z, z ∈ Λq w q ↔ z ∈ ddPow D (hgt w q) := fun q h1 h2 z => by
    simp only [Λq, Iq, h1, h2, if_false, not_false_eq_true, or_true, if_true]; rfl
  have hup : ∀ q, ¬ selfP w q → upperM w q →
      y q - τA w q y = (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 := by
    intro q h1 h2
    rw [hτu q h1 h2, hEq, sgq_qbar, neg_add_eq_sub]
  have hsq : ∀ q, ¬ selfP w q → ¬ selfP w (qbar w q) := fun q h1 h => h1 (by
    unfold selfP at h ⊢; rw [qbar_qbar] at h; exact h.symm)
  have hgc : ∀ q, (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) ∨
      ¬ (cf w y q ∈ ddPow D (hgt w q)) := fun q => by
    by_cases hc : cf w y q ∈ ddPow D (hgt w q)
    · left; rw [hm', neg_mul]; exact (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem (gS_mul_qd _ hc)
    · right; exact hc
  rw [condX_iff]
  constructor
  · rintro ⟨hy, hE⟩ q
    by_cases h1 : selfP w q
    · rw [hτs q h1, hΛs q h1]
      have hc := cf_mem w y q (fun p _ => hy p)
      refine ⟨(ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem (hy q) (nat_mul_mem _ (mOdd D) hc), ?_⟩
      have hqq : qbar w q = q := h1
      have hEq' := hEq q
      rw [hqq] at hEq'
      rw [self_id (sgq w q) (y q) (cf w y q) _ (mOdd D) (sgq_sq w q) (sgq_conj w q) hEq']
      have e1 := hE q
      have e2 : sgq w q * D.conjF ((Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2) -
          (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) :=
        (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem (sg_qd w δ M hA (hgt_le w q) q e1) e1
      have e3 : (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) := by
        rcases hgc q with h | h
        · exact h
        · exact absurd hc h
      exact (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem
        ((qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem
          ((qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem e1 e2) (nat_mul_mem _ (mOdd D) e2)) e3
    · by_cases h2 : upperM w q
      · rw [hΛu q h1 h2, hup q h1 h2]; exact hE q
      · rw [hτl q h1 h2, sub_zero, hΛl q h1 h2]; exact hy q
  · intro ht
    have hy : ∀ q, y q ∈ ddPow D (hgt w q) := by
      have key : ∀ n, ∀ q, hgt w q = n → y q ∈ ddPow D (hgt w q) := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ih =>
          intro q hq
          have hlow : ∀ p, hgt w p < hgt w q → y p ∈ ddPow D (hgt w p) := fun p hp => ih _ (hq ▸ hp) p rfl
          by_cases h1 : selfP w q
          · have h3 := (hΛs q h1 _).1 (ht q)
            rw [hτs q h1] at h3
            have hc := cf_mem w y q hlow
            have := (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem h3.1 (nat_mul_mem _ (mOdd D) hc)
            rwa [sub_add_cancel] at this
          · by_cases h2 : upperM w q
            · have h3 := (hΛu q h1 h2 _).1 (ht q)
              rw [hτu q h1 h2] at h3
              obtain ⟨hp1, hp2⟩ := upper_qbar w h2
              have hyp : y (qbar w q) ∈ ddPow D (hgt w (qbar w q)) := by
                have := (hΛl _ hp1 hp2 _).1 (ht (qbar w q))
                rwa [hτl _ hp1 hp2, sub_zero] at this
              rw [hgt_qbar] at hyp
              have hcp := cf_mem w y (qbar w q) (fun p hp => hlow p (by rwa [hgt_qbar] at hp))
              rw [hgt_qbar] at hcp
              have hτ := sg_dd w δ M hA (hgt_le w q) (qbar w q)
                ((ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem
                  ((ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).neg_mem hyp) hcp)
              have := (ddPow D _ : Submodule (𝓞 D.host.E) D.host.E).add_mem (qd_le_dd _ h3) hτ
              rwa [sub_add_cancel] at this
            · have := (hΛl q h1 h2 _).1 (ht q)
              rwa [hτl q h1 h2, sub_zero] at this
      exact fun q => key _ q rfl
    have hG := Xmat_grD w y hy
    refine ⟨hy, ?_⟩
    have hB2 : IsBlockDiagonalMatrix w (Xmat w y - Psi w (Xmat w y)⁻¹) := fun a c h => by
      rw [Matrix.sub_apply, Xmat_blk w y a c h,
        Psi_blk w (blk_inv w (Xmat_upU w y) (Xmat_blk w y)) a c h, sub_self]
    have key2 : ∀ n, ∀ q, hgt w q = n →
        (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 ∈ qdPow D (hgt w q) := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro q hq
        have hU := unitCons w δ M hA (Xmat_upU w y) (Xmat_blk w y) hG q.2.1 (fun i j hij hh => by
          by_cases hb : blkOf w.1 i.val = blkOf w.1 j.val
          · exact ih _ (by rw [← hq]; exact hh) ⟨(i, j), hij, hb⟩ rfl
          · rw [hB2 i j hb]; exact FractionalIdeal.zero_mem _)
        have hPsiq : Psi w (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 = sgq w q *
            D.conjF ((Xmat w y - Psi w (Xmat w y)⁻¹) (qbar w q).1.1 (qbar w q).1.2) := rfl
        rw [hPsiq] at hU
        by_cases h1 : selfP w q
        · have hqq : qbar w q = q := h1
          rw [hqq] at hU
          have hT := ((hΛs q h1 _).1 (ht q)).2
          rw [hτs q h1] at hT
          have hEq' := hEq q
          rw [hqq] at hEq'
          rw [self_id (sgq w q) (y q) (cf w y q) _ (mOdd D) (sgq_sq w q) (sgq_conj w q) hEq'] at hT
          have hc := cf_mem w y q (fun p _ => hy p)
          have e3 : (1 - 2 * (mOdd D : D.host.E)) * cf w y q ∈ qdPow D (hgt w q) := by
            rcases hgc q with h | h
            · exact h
            · exact absurd hc h
          set Ee := (Xmat w y - Psi w (Xmat w y)⁻¹) q.1.1 q.1.2 with hEe
          have h5 := (qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).sub_mem
            ((qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).add_mem
              ((qdPow D (hgt w q) : Submodule (𝓞 D.host.E) D.host.E).sub_mem hT e3) (nat_mul_mem _ (mOdd D) hU)) hU
          have eq : Ee + (sgq w q * D.conjF Ee - Ee) - (mOdd D : D.host.E) * (sgq w q * D.conjF Ee - Ee) +
              (1 - 2 * (mOdd D : D.host.E)) * cf w y q - (1 - 2 * (mOdd D : D.host.E)) * cf w y q +
              (mOdd D : D.host.E) * (sgq w q * D.conjF Ee - Ee) - (sgq w q * D.conjF Ee - Ee) = Ee := by ring
          rw [eq] at h5
          exact h5
        · by_cases h2 : upperM w q
          · rw [← hup q h1 h2]; exact (hΛu q h1 h2 _).1 (ht q)
          · have hpu := lower_qbar w h1 h2
            have hps := hsq q h1
            have hEp : (Xmat w y - Psi w (Xmat w y)⁻¹) (qbar w q).1.1 (qbar w q).1.2 ∈
                qdPow D (hgt w (qbar w q)) := by
              rw [← hup _ hps hpu]; exact (hΛu _ hps hpu _).1 (ht _)
            rw [hgt_qbar] at hEp
            have hs := sg_qd w δ M hA (hgt_le w q) q hEp
            have := (qdPow D _ : Submodule (𝓞 D.host.E) D.host.E).sub_mem hs hU
            rwa [sub_sub_cancel] at this
    exact fun q => key2 _ q rfl

end Formalism.L2.SG.Pf.StabIntLat
end
end
end
