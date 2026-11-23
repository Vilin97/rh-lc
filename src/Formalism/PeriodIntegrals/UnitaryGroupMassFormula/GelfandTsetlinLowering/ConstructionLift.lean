module

public import Formalism.PeriodIntegrals.HwIrred
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ZScalarVanish
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftAsm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Formalism.LocalRingCardinality.Params
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftEqvDiv
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftEqvWt
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftFock
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftTuple
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDecomp

section

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem dominant_weight_ext {N : ℕ} (a b : DomWeight N) (hab : a.w = b.w) : a = b := by
  obtain ⟨w, hw⟩ := a
  obtain ⟨w', hw'⟩ := b
  simp only at hab
  subst hab
  rfl

theorem extremal_mem_nablaSq' (n : ℕ) (mu : DomWeight n) : extremal ℂ n mu ∈ nablaSq ℂ n mu :=
  Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl mu.natW (fun i j hij => Int.toNat_le_toNat (by have := mu.anti hij; omega))

theorem degree_sub_det_shift_nonneg {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (hmu : Interlace h lam mu) : 0 ≤ degZ lam mu - lam.detShift := by
  subst h
  have hle : ∀ i : Fin n, mu.w i ≤ lam.w (Fin.castSucc i) := fun i => (hmu i).1
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hle i)
  have hl : lam.detShift = lam.w (Fin.last n) := by
    unfold DomWeight.detShift
    rw [dite_eq_left (by omega)]
    congr 1
  unfold degZ wsum
  rw [hl, Fin.sum_univ_castSucc]
  linarith

theorem weight_sum_eq_of_last_gap {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu sg : DomWeight n)
    (hmu : Interlace h lam mu) (hsg : Interlace h lam sg) (hd : dLast lam mu = dLast lam sg) :
    wsum mu = wsum sg := by
  have h1 := degree_sub_det_shift_nonneg h lam mu hmu
  have h2 := degree_sub_det_shift_nonneg h lam sg hsg
  unfold dLast at hd
  have h3 : degZ lam mu - lam.detShift = degZ lam sg - lam.detShift := by
    rw [← Int.toNat_of_nonneg h1, ← Int.toNat_of_nonneg h2, hd]
  unfold degZ at h3
  linarith

theorem decomp_of (h4 : PI.GTBranch) (hL : EqvLast) : Decomp := by
  intro n N h lam sg hsg io0 hio hne f hf hfw
  classical
  let T : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ) := (nablaSq ℂ n sg).map io0 ⊔ OtherPart h lam sg
  have key : nablaSq ℂ N lam ≤ T.comap (weightedHomogeneousComponent (lastW N) (dLast lam sg)) := by
    rw [(h4 n N h lam).2]
    refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
    rw [Submodule.map_le_iff_le_comap]
    intro s hs
    rw [Submodule.mem_comap, Submodule.mem_comap]
    have hφ' : IsEqv h mu lam φ := hφ
    have hhom := hL n N h lam mu hmu φ hφ' s hs
    by_cases hd : dLast lam mu = dLast lam sg
    · rw [hd] at hhom
      rw [hhom.weightedHomogeneousComponent_same]
      have hw : wsum mu = wsum sg := weight_sum_eq_of_last_gap h lam mu sg hmu hsg hd
      by_cases hmw : mu.w = sg.w
      · have hms : mu = sg := dominant_weight_ext mu sg hmw
        subst hms
        have hboth : ∀ ψ ∈ ({φ, io0} : Set (MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ)),
            (∀ s ∈ nablaSq ℂ n mu, ψ s ∈ nablaSq ℂ N lam) ∧
            ∀ (g : GL (Fin n) ℂ), ∀ s ∈ nablaSq ℂ n mu,
              ψ (sqAct ℂ n mu g s) = sqAct ℂ N lam (embGL ℂ n N h g) (ψ s) := by
          intro ψ hψ
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
          rcases hψ with rfl | rfl
          · exact hφ'
          · exact hio
        obtain ⟨_, c, hc⟩ := (h4 n N h lam).1 mu φ io0 hboth ⟨extremal ℂ n mu, extremal_mem_nablaSq' n mu, hne⟩
        refine Submodule.mem_sup_left ?_
        rw [hc s hs, ← map_smul]
        exact Submodule.mem_map_of_mem (Submodule.smul_mem _ c hs)
      · refine Submodule.mem_sup_right ?_
        unfold OtherPart
        exact Submodule.mem_iSup_of_mem mu (Submodule.mem_iSup_of_mem hmu (Submodule.mem_iSup_of_mem hmw
          (Submodule.mem_iSup_of_mem hw (Submodule.mem_iSup_of_mem φ (Submodule.mem_iSup_of_mem hφ'
            (Submodule.mem_map_of_mem hs))))))
    · rw [hhom.weightedHomogeneousComponent_ne (dLast lam sg) (Ne.symm hd)]
      exact zero_mem _
  have hfT := key hf
  rw [Submodule.mem_comap, hfw.weightedHomogeneousComponent_same] at hfT
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hfT
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
  refine ⟨u, hu, ?_⟩
  rw [← hyz, add_sub_cancel_left]
  exact hz

end PI.WGL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.NablaSqLeOfGen

section

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem nablaSq_le_of_gen (h4 : PI.GTBranch) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N)
    (P : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ))
    (hP : ∀ (mu : DomWeight n), Interlace h lam mu →
      ∀ (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ), IsEqv h mu lam φ →
        ∀ s ∈ nablaSq ℂ n mu, φ s ∈ P) :
    nablaSq ℂ N lam ≤ P := by
  rw [(h4 n N h lam).2]
  refine iSup_le fun mu => iSup_le fun hmu => iSup_le fun φ => iSup_le fun hφ => ?_
  rw [Submodule.map_le_iff_le_comap]
  intro s hs
  exact hP mu hmu φ hφ s hs

theorem comp_gen (hW : EqvRowWt) {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (mu : DomWeight n)
    (hmu : Interlace h lam mu)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (Z : MvPolynomial (Fin N × Fin N) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (z : ℂ)
    (hz : ∀ s ∈ nablaSq ℂ n mu, Z (φ s) = z • φ s) (ν : Fin N → ℕ) (s : MvPolynomial (Fin n × Fin n) ℂ)
    (hs : s ∈ nablaSq ℂ n mu) :
    Z (weightedHomogeneousComponent (rowW N N) ν (φ s)) =
      weightedHomogeneousComponent (rowW N N) ν (Z (φ s)) := by

  have hterm : ∀ ω : Fin n → ℕ,
      Z (weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s))) =
        z • weightedHomogeneousComponent (rowW N N) ν (φ (weightedHomogeneousComponent (rowW n n) ω s)) := by
    intro ω
    have hc : weightedHomogeneousComponent (rowW n n) ω s ∈ nablaSq ℂ n mu :=
      dualWeylRowGraded ℂ n n mu.natW ω s hs
    have hhom : IsWeightedHomogeneous (rowW N N)
        (φ (weightedHomogeneousComponent (rowW n n) ω s)) (liftWt h lam mu ω) :=
      hW n N h lam mu hmu φ hφ ω _ hc (weightedHomogeneousComponent_isWeightedHomogeneous ω s)
    by_cases hν : ν = liftWt h lam mu ω
    · subst hν
      rw [hhom.weightedHomogeneousComponent_same]
      exact hz _ hc
    · rw [hhom.weightedHomogeneousComponent_ne ν hν, map_zero, smul_zero]
  have hsum : s = ∑ ω ∈ (weightedHomogeneousComponent_finsupp (w := rowW n n) s).toFinset,
      weightedHomogeneousComponent (rowW n n) ω s := by
    conv_lhs => rw [← finsum_weightedHomogeneousComponent (rowW n n) s]
    exact finsum_eq_sum _ _
  rw [hz s hs, map_smul]
  conv_lhs => rw [hsum]
  conv_rhs => rw [hsum]

  simp only [map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun ω _ => hterm ω

theorem zComm_of (h4 : PI.GTBranch) (hD : EqvDiv) (hW : EqvRowWt) : ZComm := by
  intro n N h lam Z hZ

  have hcomp : ∀ ν : Fin N → ℕ, ∀ f ∈ nablaSq ℂ N lam,
      Z (weightedHomogeneousComponent (rowW N N) ν f) = weightedHomogeneousComponent (rowW N N) ν (Z f) := by
    intro ν f hf
    have hle := nablaSq_le_of_gen h4 h lam
      (LinearMap.eqLocus (Z ∘ₗ weightedHomogeneousComponent (rowW N N) ν)
        (weightedHomogeneousComponent (rowW N N) ν ∘ₗ Z)) (by
        intro mu hmu φ hφ s hs
        obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
        rw [LinearMap.mem_eqLocus]
        exact comp_gen hW h lam mu hmu φ hφ Z z hz ν s hs)
    have := hle hf
    rw [LinearMap.mem_eqLocus] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    have hle := nablaSq_le_of_gen h4 h lam ((nablaSq ℂ N lam).comap Z) (by
      intro mu hmu φ hφ s hs
      obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
      rw [Submodule.mem_comap, hz s hs]
      exact Submodule.smul_mem _ z (hφ.1 s hs))
    exact hle hf
  · intro a b hab k f hf
    have hle := nablaSq_le_of_gen h4 h lam
      (LinearMap.eqLocus (Z ∘ₗ rowDivL ℂ (eRow h a) (eRow h b) k)
        (rowDivL ℂ (eRow h a) (eRow h b) k ∘ₗ Z)) (by
        intro mu hmu φ hφ s hs
        obtain ⟨z, hz⟩ := hZ mu hmu φ hφ
        rw [LinearMap.mem_eqLocus]
        simp only [LinearMap.comp_apply, rowDivL_apply]
        have hs' : rowDiv ℂ a b k s ∈ nablaSq ℂ n mu := rowDivStable ℂ n n mu.natW a b k s hs
        rw [← hD n N h mu lam φ hφ a b hab k s hs, hz _ hs', hz s hs, rowDiv_smul,
          hD n N h mu lam φ hφ a b hab k s hs])
    have := hle hf
    rw [LinearMap.mem_eqLocus] at this
    simpa only [LinearMap.comp_apply, rowDivL_apply] using this
  · intro ω f hf hhom
    rw [← hhom.weightedHomogeneousComponent_same, hcomp ω f hf]
    exact weightedHomogeneousComponent_isWeightedHomogeneous ω _

end PI.WGL
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.ConstructionLift

section

@[expose] public section

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions MvPolynomial

theorem liftMod_of (h3 : PI.HwIrred) (h4 : PI.GTBranch) (hZ : CapelliZ) (hV : ZScalarVanish)
    (hN : Numbers) (hX : XiFacts) : LiftMod :=
  liftMod_asm hZ hV hN hX equivariant_divisibility equivariant_partial_weight (decomp_of h4 equivariant_last_degree)
    (zComm_of h4 equivariant_divisibility equivariant_partial_weight) (fockDetect_of h3 equivariant_divisibility) tuple_decomposition_formula

end PI.WGL
end
end
end
