module

public import Development.EtaleCohomology.TateTwists.EtalePrismAlexanderWhitneyHomotopyOfRelations
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

-- Source module: Development.EtaleCohomology.TateTwists.PrismBoundaryMapSquareZeroHolds

section

@[expose] public section

open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

lemma push_push {N M K : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M)
    (θ' : SimplexCategory.mk M ⟶ SimplexCategory.mk K) (c : Pr N →₀ ℤ) :
    Pr.push θ' (Pr.push θ c) = Pr.push (θ ≫ θ') c := by
  simp only [Pr.push, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  rfl

def inv {N : ℕ} (p : Fin (N + 3) × Fin (N + 2)) : Fin (N + 3) × Fin (N + 2) :=
  if h : (p.2 : ℕ) < p.1 then (p.2.castSucc, p.1.pred (by intro e; rw [e] at h; simp at h))
  else (p.2.succ, p.1.castPred (fun e => by have := congrArg Fin.val e; have := p.2.isLt; simp at this; simp at *; omega))

theorem prism_boundary_map_square_zero_holds : leaf_bdbd := by
  intro N c
  unfold Pr.bd

  simp only [map_sum, map_zsmul, push_push, Finset.smul_sum, smul_smul]
  rw [← Finset.sum_product' (f := fun (i : Fin (N + 3)) (j : Fin (N + 2)) => ((-1 : ℤ) ^ (i : ℕ) * (-1) ^ (j : ℕ)) • Pr.push (SimplexCategory.δ j ≫ SimplexCategory.δ i) c)]
  refine Finset.sum_involution (fun p _ => inv p) ?_ ?_ (fun p _ => by simp) ?_
  · rintro ⟨i, j⟩ -
    simp only [inv]
    split_ifs with h
    · have hj : j ≤ i.pred (fun e => by subst e; simp at h) := by
        rw [Fin.le_def, Fin.val_pred]; omega
      have e := SimplexCategory.δ_comp_δ hj
      have hi : (i.pred (fun e => by subst e; simp at h)).succ = i := Fin.succ_pred _ _
      rw [hi] at e
      simp only [Fin.val_castSucc, Fin.val_pred]
      rw [e, ← add_smul]
      refine (congrArg (· • _) ?_).trans (zero_smul ℤ _)
      obtain ⟨k, hk⟩ : ∃ k, (i : ℕ) = k + 1 := ⟨i - 1, by omega⟩
      rw [hk, Nat.add_sub_cancel, pow_succ]; ring
    · push Not at h
      have hne : i ≠ Fin.last (N + 2) := fun e => by have := congrArg Fin.val e; have := j.isLt; simp at this; simp at *; omega
      have hj : i.castPred hne ≤ j := by rw [Fin.le_def, Fin.coe_castPred]; omega
      have e := SimplexCategory.δ_comp_δ hj
      rw [Fin.castSucc_castPred] at e
      simp only [Fin.val_succ, Fin.coe_castPred]
      rw [← e, ← add_smul]
      refine (congrArg (· • _) ?_).trans (zero_smul ℤ _)
      rw [pow_succ]; ring
  · rintro ⟨i, j⟩ - -
    simp only [inv]
    split_ifs with h <;> intro e <;> simp [Prod.ext_iff, Fin.ext_iff] at e <;> omega
  · rintro ⟨i, j⟩ -
    simp only [inv]
    split_ifs with h h2 h2
    · exfalso; simp at h2; omega
    · simp [Prod.ext_iff, Fin.ext_iff]
    · simp [Prod.ext_iff, Fin.ext_iff]
    · exfalso; simp at h2; omega

end LateralTheory.EtaleFoundations.SteenPf
end
end

-- Source module: Development.EtaleCohomology.TateTwists.SteenrodPrismChainDifferentialSquaredEqZeroOfEta

section

@[expose] public section

open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.SteenPf

lemma push_d₁ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₁ = Pr.d₁ (N := M) ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ := by
  obtain ⟨p, r, a, b⟩ := z
  cases p with
  | zero => simp [Pr.d₁]
  | succ p =>

    simp only [Pr.d₁, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]

lemma push_d₂ {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) :
    Pr.push θ z.d₂ = Pr.d₂ (N := M) ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ := by
  obtain ⟨p, r, a, b⟩ := z
  cases r with
  | zero => simp [Pr.d₂]
  | succ r =>

    simp only [Pr.d₂, map_sum, Pr.push, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Category.assoc]

lemma push_single {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (z : Pr N) (n : ℤ) :
    Pr.push θ (Finsupp.single z n) = Finsupp.single ⟨z.1, z.2.1, z.2.2.1 ≫ θ, z.2.2.2 ≫ θ⟩ n := by
  simp [Pr.push]

lemma d_push {N M : ℕ} (θ : SimplexCategory.mk N ⟶ SimplexCategory.mk M) (c : Pr N →₀ ℤ) :
    Pr.d M (Pr.push θ c) = Pr.push θ (Pr.d N c) := by
  have : (Pr.d M).comp (Pr.push θ) = (Pr.push θ).comp (Pr.d N) := by
    refine Finsupp.lhom_ext fun z n => ?_
    simp only [LinearMap.comp_apply, push_single, Pr.d, Finsupp.linearCombination_single, map_smul,
      map_add, push_d₁, push_d₂]
  exact LinearMap.congr_fun this c

theorem steenrod_prism_chain_differential_squared_eq_zero_of_etale : leaf_dbd := by
  intro N c
  unfold Pr.bd

  simp only [map_sum, map_zsmul, d_push]

end LateralTheory.EtaleFoundations.SteenPf
end
end

-- Source module: Development.EtaleCohomology.TateTwists.EtaleSteenrodPrismHomotopyOfAcyclicAlexanderWhit

section

@[expose] public section


open LateralTheory.EtaleFoundations.SteenPf in
theorem LateralTheory.EtaleFoundations.etale_steenrod_prism_homotopy_of_acyclic_alexander_whitney (hA : leaf_acyc) (hAW : leaf_aw) (hWA : leaf_wa) :
    LateralTheory.EtaleFoundations.PrismAlexanderWhitneySwapChainHomotopy :=
  LateralTheory.EtaleFoundations.etale_prism_alexander_whitney_homotopy_of_relations hA steenrod_prism_chain_differential_squared_eq_zero_of_etale prism_boundary_map_square_zero_holds hAW hWA
end
end
