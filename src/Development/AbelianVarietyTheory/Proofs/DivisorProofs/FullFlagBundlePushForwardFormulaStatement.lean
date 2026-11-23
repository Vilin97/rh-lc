module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceIntersectionNumberAdjacentSwapNegStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPerm

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAlternatingOfAdjacentSwapBlocks

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

set_option autoImplicit false

namespace GlobalTheory.FlagPush

theorem perm_submonoid_eq_top_of_adj (k : ℕ) (T : Submonoid (Equiv.Perm (Fin k)))
    (h : ∀ a b : Fin k, (b : ℕ) = a + 1 → Equiv.swap a b ∈ T) : T = ⊤ := by
  cases k with
  | zero =>
    rw [eq_top_iff]
    intro x _
    have : x = 1 := Subsingleton.elim _ _
    rw [this]; exact T.one_mem
  | succ n =>
    rw [eq_top_iff, ← Equiv.Perm.mclosure_swap_castSucc_succ, Submonoid.closure_le]
    rintro _ ⟨i, rfl⟩
    exact h _ _ (by simp)

theorem alternating_of_adjacent_swap (ι : Type) [Fintype ι] (m : ι → ℕ)
    (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ)
    (hL : ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q,
      L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q)
    (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ) :
    L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
      (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  let S : Submonoid (∀ τ, Equiv.Perm (Fin (m τ))) :=
    { carrier := {w | ∀ Q, L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) =
        (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q}
      one_mem' := by
        intro Q
        have : (fun x : Root m => (⟨x.1, (1 : ∀ τ, Equiv.Perm (Fin (m τ))) x.1 x.2⟩ : Root m)) = id := by
          funext x; rfl
        rw [this, rename_id]
        simp
      mul_mem' := by
        intro v w hv hw Q
        have : (fun x : Root m => (⟨x.1, (v * w) x.1 x.2⟩ : Root m)) =
            (fun x : Root m => (⟨x.1, v x.1 x.2⟩ : Root m)) ∘
              (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) := by
          funext x; rfl
        simp only [Set.mem_setOf_eq] at hv hw ⊢
        rw [this, ← rename_rename, hv, hw]
        simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib, Units.val_mul, Int.cast_mul]
        ring }
  have hS : S = ⊤ := by
    have htop : (⊤ : Submonoid (∀ τ, Equiv.Perm (Fin (m τ)))) =
        Submonoid.pi Set.univ (fun τ => (⊤ : Submonoid (Equiv.Perm (Fin (m τ))))) := by
      ext x; simp [Submonoid.mem_pi]
    rw [eq_top_iff, htop, ← Submonoid.iSup_map_mulSingle, iSup_le_iff]
    intro τ
    rw [Submonoid.map_le_iff_le_comap]
    rw [perm_submonoid_eq_top_of_adj (m τ) (Submonoid.comap (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ) S) ?_]
    intro a b hab Q
    have hf : (fun x : Root m => (⟨x.1, (MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) x.1 x.2⟩ : Root m)) = Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩ := by
      funext ⟨σ, c⟩
      by_cases h : σ = τ
      · subst h
        simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
        rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
        by_cases h1 : c = a
        · subst h1; simp
        · by_cases h2 : c = b
          · subst h2; simp [h1]
          · simp [h1, h2]
      · simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne h, Equiv.Perm.coe_one, id]
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro e; exact h (congrArg Sigma.fst e)
        · intro e; exact h (congrArg Sigma.fst e)
    have hab' : a ≠ b := by
      intro e; subst e; omega
    have hs : (∏ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
        (Equiv.swap a b)) σ)) = -1 := by
      have : ∀ σ, Equiv.Perm.sign ((MonoidHom.mulSingle (fun τ => Equiv.Perm (Fin (m τ))) τ
          (Equiv.swap a b)) σ) = (Pi.mulSingle τ (Equiv.Perm.sign (Equiv.swap a b)) : ι → ℤˣ) σ := by
        intro σ
        by_cases h : σ = τ
        · subst h; simp
        · simp [Pi.mulSingle_eq_of_ne h]
      simp only [this, Finset.prod_pi_mulSingle', Finset.mem_univ, if_true]
      exact Equiv.Perm.sign_swap hab'
    show L _ = _
    rw [hf, hs, hL τ a b hab Q]
    simp
  have hw : w ∈ S := by rw [hS]; trivial
  exact hw Q

end GlobalTheory.FlagPush
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormAlternatingOfAdjacentSwapBlocksStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ (w : ∀ τ, Equiv.Perm (Fin (m τ))) (Q : MvPolynomial (Root m) ℝ), L (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) Q) = (((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : ℝ) * L Q := by
  first | exact @GlobalTheory.FlagPush.alternating_of_adjacent_swap | exact GlobalTheory.FlagPush.alternating_of_adjacent_swap | (intros; apply GlobalTheory.FlagPush.alternating_of_adjacent_swap <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqOfWeylAntisymmetrizationEq

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush

theorem linForm_eq_of_antisymm_eq : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ Q Q' : MvPolynomial (Root m) ℝ, antisymm Q = antisymm Q' → L Q = L Q' := by
  intro ι _ m L hL Q Q' h
  have sq : ∀ u : ℤˣ, ((u : ℤ) : ℝ) * ((u : ℤ) : ℝ) = 1 := by
    intro u
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  have key : ∀ P : MvPolynomial (Root m) ℝ,
      L (antisymm P) = (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) * L P := by
    intro P

    simp only [GlobalTheory.GoodMetric.antisymm, map_sum, map_zsmul]
    rw [Finset.sum_congr rfl (fun w _ => by
      rw [GlobalTheory.T.linearForm_alternating_of_adjacent_swap_blocks ι m L hL w P, zsmul_eq_mul, ← mul_assoc, sq, one_mul])]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hc : (Fintype.card (∀ τ, Equiv.Perm (Fin (m τ))) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := ∀ τ, Equiv.Perm (Fin (m τ)))).ne'
  have e := congrArg L h
  rw [key, key] at e
  exact mul_left_cancel₀ hc e

end GlobalTheory.FlagPush
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqOfWeylAntisymmetrizationEqStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.linearForm_eq_of_weylAntisymmetrization_eq : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (L : MvPolynomial (Root m) ℝ →ₗ[ℝ] ℝ), (∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q, L (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - L Q) → ∀ Q Q' : MvPolynomial (Root m) ℝ, antisymm Q = antisymm Q' → L Q = L Q' := by
  first | exact @GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq | exact GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq | (intros; apply GlobalTheory.FlagPush.linForm_eq_of_antisymm_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagBundlePushForwardFormula

section

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.FlagPushProof

theorem flagPushForward : GlobalTheory.Published.FlagPushForward := by
  intro F _ _ X Y ι _ m E E' φ f gr hf hg Q R hR
  have hswap := GlobalTheory.T.flagSpace_intersectionNumber_adjacent_swap_neg F X Y ι m E E' φ f hf gr hg
  refine GlobalTheory.T.linearForm_eq_of_weylAntisymmetrization_eq ι m (Y.interPoly gr) hswap Q (chernRoots m R * fibrePoint m) ?_
  classical
  have rename_chernRoots (ι : Type) [Fintype ι] (m : ι → ℕ) (w : ∀ τ, Equiv.Perm (Fin (m τ)))
      (R : MvPolynomial (ι × ℕ) ℝ) :
      rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (chernRoots m R) = chernRoots m R := by
    have h : (rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m))).comp (chernRoots m) = chernRoots m := by
      apply MvPolynomial.algHom_ext
      intro x
      simp only [AlgHom.comp_apply, chernRoots, aeval_X, rename_rename]
      have e : ((fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) ∘ Sigma.mk x.1) = Sigma.mk x.1 ∘ (w x.1) := by
        funext i; rfl
      rw [e, ← rename_rename, rename_esymm]
    exact AlgHom.congr_fun h R

  have antisymm_chernRoots_mul (ι : Type) [Fintype ι] (m : ι → ℕ) (R : MvPolynomial (ι × ℕ) ℝ)
      (Q : MvPolynomial (Root m) ℝ) : antisymm (chernRoots m R * Q) = chernRoots m R * antisymm Q := by
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, rename_chernRoots, mul_smul_comm]

  have prod_Ioi_rev {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v (Fin.rev i) - v (Fin.rev j))) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (v j - v i) := by
    have h : ∀ f : Fin N → Fin N → R, (∏ i : Fin N, ∏ j ∈ Finset.Ioi i, f i j) =
        ∏ i : Fin N, ∏ j : Fin N, if i < j then f i j else 1 := by
      intro f
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← Finset.prod_filter]
      congr 1
      ext j; simp
    rw [h, h, ← Fintype.prod_prod_type' (f := fun i j => if i < j then v (Fin.rev i) - v (Fin.rev j) else 1),
      ← Fintype.prod_prod_type' (f := fun i j => if i < j then v j - v i else 1)]
    refine Fintype.prod_equiv ((Equiv.prodComm _ _).trans (Fin.revPerm.prodCongr Fin.revPerm)) _ _ fun p => ?_
    simp [Fin.rev_lt_rev]

  have sum_sign_prod_neg_pow {R : Type} [CommRing R] {N : ℕ} (v : Fin N → R) :
      (∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ))) =
        ∏ j : Fin N, ∏ i ∈ Finset.Iio j, (v j - v i) := by
    let M : Matrix (Fin N) (Fin N) R := Matrix.of fun j i => (-v j) ^ (N - 1 - (i : ℕ))
    have h1 : M.det = ∑ σ : Equiv.Perm (Fin N), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) * ∏ i : Fin N, (-v (σ i)) ^ (N - 1 - (i : ℕ)) := by
      rw [Matrix.det_apply']
      rfl
    have h2 : M.submatrix Fin.revPerm Fin.revPerm = Matrix.vandermonde (fun j => -v (Fin.rev j)) := by
      ext j i
      simp only [M, Matrix.submatrix_apply, Matrix.of_apply, Matrix.vandermonde_apply, Fin.revPerm_apply, Fin.val_rev]
      congr 1
      omega
    rw [← h1, ← Matrix.det_submatrix_equiv_self Fin.revPerm, h2, Matrix.det_vandermonde,
      GlobalTheory.GoodMetric.RootDiscrPerm.prod_Iio_eq_det, Matrix.det_vandermonde]
    simp only [neg_sub_neg]
    rw [prod_Ioi_rev]

  have antisymm_fibrePoint (ι : Type) [Fintype ι] (m : ι → ℕ) : antisymm (fibrePoint m) = rootDiscr m := by
    have hw : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)),
        ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) • rename (fun x : Root m => (⟨x.1, w x.1 x.2⟩ : Root m)) (fibrePoint m) =
          ∏ τ, ((((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(MvPolynomial.X (⟨τ, w τ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))) := by
      intro w
      unfold fibrePoint
      rw [map_prod, Fintype.prod_sigma, zsmul_eq_mul, Units.coe_prod, Int.cast_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp [map_pow, map_neg, rename_X]
    unfold GlobalTheory.GoodMetric.antisymm
    rw [Finset.sum_congr rfl fun w _ => hw w]
    rw [← Fintype.prod_sum (fun τ (σ : Equiv.Perm (Fin (m τ))) => ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Root m) ℝ) *
            ∏ i : Fin (m τ), (-(MvPolynomial.X (⟨τ, σ i⟩ : Root m) : MvPolynomial (Root m) ℝ)) ^ (m τ - 1 - (i : ℕ))))]
    unfold rootDiscr
    refine Finset.prod_congr rfl fun τ _ => ?_
    exact sum_sign_prod_neg_pow (fun i : Fin (m τ) => (MvPolynomial.X (⟨τ, i⟩ : Root m) : MvPolynomial (Root m) ℝ))
  rw [hR, antisymm_chernRoots_mul ι m R, antisymm_fibrePoint ι m]

end GlobalTheory.FlagPushProof
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagBundlePushForwardFormulaStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.fullFlagBundle_pushForward_formula : GlobalTheory.Published.FlagPushForward := by
  first | exact @GlobalTheory.FlagPushProof.flagPushForward | exact GlobalTheory.FlagPushProof.flagPushForward | (intros; apply GlobalTheory.FlagPushProof.flagPushForward <;> assumption)
end
end
