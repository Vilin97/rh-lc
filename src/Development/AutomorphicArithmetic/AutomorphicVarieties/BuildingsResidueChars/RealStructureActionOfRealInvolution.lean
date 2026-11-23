module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.SimpSmul

section

@[expose] public section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.simp_smul :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E} (g : E ≃L[ℝ] E) (π : Y ≃ Y), (∀ y h, q (π y) (g h) = q y h) → (∀ k, g k ∈ T ↔ k ∈ T) → (∀ h, IsVert q h → IsVert q (g h)) ∧ ∀ (n : ℕ) (t t' : Fin n → Vert q), (∀ j, (t' j).1 = g (t j).1) → t ∈ simp q T n → t' ∈ simp q T n := by
  intro E Y _ _ q T g π hq hT
  have hpoly : ∀ h, h ∈ poly q → g.symm h ∈ poly q := by
    intro h hh
    show ∀ y, 1 ≤ q y (g.symm h)
    intro y
    have h1 := (hh : ∀ y, 1 ≤ q y h) (π y)
    rw [← hq y (g.symm h), g.apply_symm_apply]
    exact h1
  refine ⟨fun h hv => ⟨?_, ?_⟩, ?_⟩
  · show ∀ y, 1 ≤ q y (g h)
    intro y
    have h1 := (hv.1 : ∀ y, 1 ≤ q y h) (π.symm y)
    rw [← hq (π.symm y) h, π.apply_symm_apply] at h1
    exact h1
  · intro k hk
    have h0 : g.symm k = 0 := by
      refine hv.2 _ fun y hy => ?_
      have h1 : q (π y) (g h) = 1 := by
        rw [hq]
        exact hy
      have h2 := hk (π y) h1
      rw [← hq y (g.symm k), g.apply_symm_apply]
      exact h2
    simpa using congrArg g h0
  · intro n t t' ht ht0
    obtain ⟨x, hx, hxj⟩ : ∃ x ∈ posDual T, ∀ j, x ∈ normalCone q (t j).1 := ht0
    show ∃ x ∈ posDual T, ∀ j, x ∈ normalCone q (t' j).1
    refine ⟨x.comp (g.symm : E →L[ℝ] E), ?_, fun j => ?_⟩
    · show ∀ k ∈ T, k ≠ 0 → 0 < (x.comp (g.symm : E →L[ℝ] E)) k
      intro k hk hk0
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      refine (hx : ∀ k ∈ T, k ≠ 0 → 0 < x k) (g.symm k) ?_ ?_
      · rw [← hT, g.apply_symm_apply]
        exact hk
      · intro h0
        exact hk0 (by simpa using congrArg g h0)
    · show ∀ h' ∈ poly q, (x.comp (g.symm : E →L[ℝ] E)) (t' j).1 ≤ (x.comp (g.symm : E →L[ℝ] E)) h'
      intro h' hh'
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, ht j,
        g.symm_apply_apply]
      exact (hxj j : ∀ h' ∈ poly q, x (t j).1 ≤ x h') (g.symm h') (hpoly h' hh')
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.RealStructureActionOfRealInvolution

section

@[expose] public section

open NumberField UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA


theorem UpperTheory.real_structure_action_of_real_involution :
    UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.ActRe := by
  intro hR L _ _ N σ hσ
  have hHR : ∀ (g : Fix N σ) (h : HR L N), (g : Gm L N) • (h : HS L N) ∈ HR L N :=
    fun g h => ((hR L N σ hσ).2 h h.2).2 g g.2
  have hinv : ∀ (g : Fix N σ) (h : HS L N), ((g⁻¹ : Fix N σ) : Gm L N) • (g : Gm L N) • h = h := by
    intro g h
    rw [← mul_smul, Subgroup.coe_inv, inv_mul_cancel, one_smul]
  have hinv' : ∀ (g : Fix N σ) (h : HS L N), (g : Gm L N) • ((g⁻¹ : Fix N σ) : Gm L N) • h = h := by
    intro g h
    rw [← mul_smul, Subgroup.coe_inv, mul_inv_cancel, one_smul]
  let E : Fix N σ → (HR L N ≃L[ℝ] HR L N) := fun g =>
    LinearEquiv.toContinuousLinearEquiv
      { toFun := fun h => ⟨(g : Gm L N) • (h : HS L N), hHR g h⟩
        invFun := fun h => ⟨((g⁻¹ : Fix N σ) : Gm L N) • (h : HS L N), hHR g⁻¹ h⟩
        map_add' := by
          intro a b
          apply Subtype.ext
          simp only [Submodule.coe_add]
          rw [← actL_apply, ← actL_apply, ← actL_apply, map_add (f := _)]
        map_smul' := by
          intro c a
          apply Subtype.ext
          simp only [Submodule.coe_smul, RingHom.id_apply]
          rw [← actL_apply, ← actL_apply, map_smul]
        left_inv := by
          intro h
          apply Subtype.ext
          exact hinv g h
        right_inv := by
          intro h
          apply Subtype.ext
          exact hinv' g h }
  have hE : ∀ (g : Fix N σ) (h : HR L N), ((E g h : HR L N) : HS L N) = (g : Gm L N) • (h : HS L N) :=
    fun g h => rfl
  let π : Fix N σ → (NZ L N ≃ NZ L N) := fun g =>
    { toFun := fun y => ⟨(g : Gm L N) • (y : Lat L N), smul_ne_zero_lat _ y.2⟩
      invFun := fun y => ⟨((g⁻¹ : Fix N σ) : Gm L N) • (y : Lat L N), smul_ne_zero_lat _ y.2⟩
      left_inv := by
        intro y
        apply Subtype.ext
        show ((g⁻¹ : Fix N σ) : Gm L N) • (g : Gm L N) • (y : Lat L N) = y
        rw [← mul_smul, Subgroup.coe_inv, inv_mul_cancel, one_smul]
      right_inv := by
        intro y
        apply Subtype.ext
        show (g : Gm L N) • ((g⁻¹ : Fix N σ) : Gm L N) • (y : Lat L N) = y
        rw [← mul_smul, Subgroup.coe_inv, mul_inv_cancel, one_smul] }
  have hq : ∀ (g : Fix N σ) (y : NZ L N) (h : HR L N), (qr L N (π g y)) (E g h) = (qr L N y) h := by
    intro g y h
    rw [qr_apply, qr_apply, hE]
    show q ((g : Gm L N) • (h : HS L N)) ((g : Gm L N) • (y : Lat L N)) = q (h : HS L N) (y : Lat L N)
    rw [q_smul, ← mul_smul, inv_mul_cancel, one_smul]
  have hT : ∀ (g : Fix N σ) (k : HR L N), E g k ∈ Tr L N ↔ k ∈ Tr L N := by
    intro g k
    constructor
    · intro hk
      change ((E g k : HR L N) : HS L N) ∈ Psd L N at hk
      rw [hE] at hk
      have h1 := smul_mem_Psd ((g : Gm L N))⁻¹ hk
      rw [← mul_smul, inv_mul_cancel, one_smul] at h1
      exact h1
    · intro hk
      show ((E g k : HR L N) : HS L N) ∈ Psd L N
      rw [hE]
      exact smul_mem_Psd _ hk
  have key := fun g => ConeExtensionAcyclic.simp_smul (E g) (π g) (hq g) (hT g)
  let inst : MulAction (Fix N σ) (ConeExtensionAcyclic.Vert (qr L N)) :=
    { smul := fun g v => ⟨E g v.1, (key g).1 v.1 v.2⟩
      one_smul := by
        intro v
        apply Subtype.ext
        apply Subtype.ext
        show ((1 : Fix N σ) : Gm L N) • ((v.1 : HR L N) : HS L N) = _
        rw [OneMemClass.coe_one, one_smul]
      mul_smul := by
        intro g g' v
        apply Subtype.ext
        apply Subtype.ext
        show ((g * g' : Fix N σ) : Gm L N) • ((v.1 : HR L N) : HS L N) =
          (g : Gm L N) • (g' : Gm L N) • ((v.1 : HR L N) : HS L N)
        rw [Subgroup.coe_mul, mul_smul] }
  refine ⟨inst, fun g v => rfl, ?_⟩
  intro n g t ht
  exact (key g).2 n t _ (fun j => rfl) ht
end
end
