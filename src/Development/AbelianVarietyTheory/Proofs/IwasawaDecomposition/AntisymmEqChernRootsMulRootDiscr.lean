module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvdStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRoots
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XSubXDvdOfRenameSwapEqNegStatement
import Mathlib.Algebra.AffineMonoid.UniqueSums

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernNeZeroStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_ne_zero : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ), rootDiscr m ≠ 0 := by
  first | exact @GlobalTheory.GoodMetric.rootDiscr_ne_zero | exact GlobalTheory.GoodMetric.rootDiscr_ne_zero | (intros; apply GlobalTheory.GoodMetric.rootDiscr_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPermStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.flagRelativeTangentTopChern_rename_block_perm : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (rootDiscr m) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rootDiscr m := by
  first | exact @GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr | exact GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr | (intros; apply GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRootsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.symmetric_poly_chern_roots : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (S : MvPolynomial (Root m) ℝ), (∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S) → ∃ R : MvPolynomial (ι × ℕ) ℝ, chernRoots m R = S := by
  first | exact @GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric | exact GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric | (intros; apply GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSign

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem antisymm_rename_sigmaCongrRight : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))),
    rename (Equiv.sigmaCongrRight w) (antisymm Q) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • antisymm Q := by
  intro ι _ m Q w
  classical
  unfold antisymm

  rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft w) _ _ (fun v => ?_)
  rw [map_zsmul, rename_rename, smul_smul]
  have hf : (⇑(Equiv.sigmaCongrRight w) ∘ fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) =
      fun x : Root m => (⟨x.1, (Equiv.mulLeft w v) x.1 x.2⟩ : Root m) := by
    funext x; rfl
  rw [hf]
  congr 1
  have hs : (∏ τ, Equiv.Perm.sign ((Equiv.mulLeft w v) τ) : ℤˣ) =
      (∏ τ, Equiv.Perm.sign (w τ)) * ∏ τ, Equiv.Perm.sign (v τ) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    simp [Equiv.Perm.sign_mul]
  rw [hs, ← Units.val_mul, ← mul_assoc, Int.units_mul_self, one_mul]

end GlobalTheory.GoodMetric
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSignStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.weylAntisymmetrization_rename_block_perm_sign : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (w : ∀ τ, Equiv.Perm (Fin (m τ))), rename (Equiv.sigmaCongrRight w) (antisymm Q) = ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • antisymm Q := by
  first | exact @GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight | exact GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight | (intros; apply GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNeg

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmSwap

theorem rename_swap_antisymm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (τ : ι)
    (i j : Fin (m τ)), i ≠ j →
      rename (Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩) (antisymm Q) = -antisymm Q := by
  intro ι _ _ m Q τ i j hij
  set u : ∀ t, Equiv.Perm (Fin (m t)) := Function.update 1 τ (Equiv.swap i j) with hu
  have hf : ∀ w : ∀ t, Equiv.Perm (Fin (m t)),
      (⇑(Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩)) ∘ (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))
        = fun x : Root m => (⟨x.1, (u * w) x.1 x.2⟩ : Root m) := by
    intro w
    funext ⟨t, k⟩
    simp only [Function.comp_apply, Pi.mul_apply, Equiv.Perm.mul_apply]
    by_cases ht : t = τ
    · subst ht
      simp only [hu, Function.update_self]
      rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    · have h1 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, i⟩ := fun h => ht (congrArg Sigma.fst h)
      have h2 : (⟨t, w t k⟩ : Root m) ≠ ⟨τ, j⟩ := fun h => ht (congrArg Sigma.fst h)
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, hu, Function.update_of_ne ht]
      rfl
  have hu1 : (∏ t, Equiv.Perm.sign (u t)) = -1 := by
    rw [Fintype.prod_eq_single τ]
    · simp [hu, Equiv.Perm.sign_swap hij]
    · intro t ht
      simp [hu, Function.update_of_ne ht]
  have hs : ∀ w : ∀ t, Equiv.Perm (Fin (m t)),
      (∏ t, Equiv.Perm.sign ((u * w) t) : ℤˣ) = -∏ t, Equiv.Perm.sign (w t) := by
    intro w
    simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, hu1, neg_one_mul]
  unfold GlobalTheory.GoodMetric.antisymm

  rw [map_sum]
  simp_rw [map_zsmul, rename_rename, hf]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_equiv (Equiv.mulLeft u) (by simp) ?_
  intro w _
  simp only [Equiv.coe_mulLeft, hs, Units.val_neg, neg_smul, neg_neg]

end GlobalTheory.AntisymmSwap
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNegStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

theorem _root_.GlobalTheory.T.weylAntisymmetrization_rename_swap_neg : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ) (τ : ι) (i j : Fin (m τ)), i ≠ j → rename (Equiv.swap (⟨τ, i⟩ : Root m) ⟨τ, j⟩) (antisymm Q) = -antisymm Q := by
  first | exact @GlobalTheory.AntisymmSwap.rename_swap_antisymm | exact GlobalTheory.AntisymmSwap.rename_swap_antisymm | (intros; apply GlobalTheory.AntisymmSwap.rename_swap_antisymm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AntisymmEqChernRootsMulRootDiscr

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmChern

theorem antisymm_eq_chernRoots_mul_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ), ∃ R : MvPolynomial (ι × ℕ) ℝ, antisymm Q = chernRoots m R * rootDiscr m := by
  intro ι _ m Q
  classical
  obtain ⟨S, hS⟩ : rootDiscr m ∣ antisymm Q := GlobalTheory.T.flagRelativeTangentTopChern_dvd_of_differences_dvd ι m (antisymm Q) fun τ i j hij =>
    GlobalTheory.T.X_sub_X_dvd_of_rename_swap_eq_neg (⟨τ, i⟩ : Root m) ⟨τ, j⟩ (by simp [hij.ne]) _ (GlobalTheory.T.weylAntisymmetrization_rename_swap_neg ι m Q τ i j hij.ne)
  have hsym : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S := by
    intro w
    have h1 := GlobalTheory.T.weylAntisymmetrization_rename_block_perm_sign ι m Q w
    rw [hS, map_mul, GlobalTheory.T.flagRelativeTangentTopChern_rename_block_perm ι m w, smul_mul_assoc] at h1
    have hs : ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) ≠ 0 := Units.ne_zero _
    exact mul_left_cancel₀ (GlobalTheory.T.flagRelativeTangentTopChern_ne_zero ι m) (smul_right_injective _ hs h1)
  obtain ⟨R, hR⟩ := GlobalTheory.T.symmetric_poly_chern_roots ι m S hsym
  exact ⟨R, by rw [hS, hR, mul_comm]⟩

end GlobalTheory.AntisymmChern
end
end
