module

public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.HermitianCurvature.StatementQ
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselColumnStepsFunctionalEigenStatement
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementI
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelationRowStepsFunctionalEigenStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixPicksSplitCasimirEigencomponent

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.ComatrixEigen

open Formalism.REAL

theorem qminor_exists_poly {A : Type} [Ring A] [Algebra ℂ A] {n t : ℕ} (E : Fin n → Fin n → A)
    (a b : Fin t → Fin n) :
    ∃ p : Polynomial A, ∀ u : ℂ, qminor E a b u = ∑ d ∈ p.support, u ^ d • p.coeff d := by
  refine ⟨∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : Polynomial A) *
    (List.ofFn fun k : Fin t => ((if a (σ k) = b k then
      Polynomial.X - Polynomial.C (algebraMap ℂ A (k : ℂ)) else 0) + Polynomial.C (E (a (σ k)) (b k)) :
        Polynomial A)).prod, fun u => ?_⟩
  let φ : Polynomial A →+* A := Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u)
    (fun x => (Algebra.commutes u x).symm)
  have hφ : ∀ p : Polynomial A, φ p = ∑ d ∈ p.support, u ^ d • p.coeff d := by
    intro p
    change Polynomial.eval₂ (RingHom.id A) (algebraMap ℂ A u) p = _
    rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]
  have hX : φ Polynomial.X = algebraMap ℂ A u := Polynomial.eval₂_X _ _
  have hC : ∀ x, φ (Polynomial.C x) = x := fun x => Polynomial.eval₂_C _ _

  rw [← hφ, map_sum, qminor]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp_apply, Tm, map_add, hC]
  split_ifs
  · rw [map_sub φ, hX, hC, map_sub]
  · rw [map_zero]

theorem continuous_qminor_apply {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {n t : ℕ}
    (E : Fin n → Fin n → Module.End ℂ M) (a b : Fin t → Fin n) (v : M) :
    Continuous fun u : ℂ => qminor E a b u v := by
  obtain ⟨p, hp⟩ := qminor_exists_poly E a b
  simp only [hp, LinearMap.sum_apply, LinearMap.smul_apply]
  fun_prop

theorem cof_eigen {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {m : ℕ}
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (mu : Fin (m + 1) → ℝ) (x : Fin (m + 1) → M)
    (hE : GlRel E)
    (hq : ∀ (Y : ℂ) (w : M), qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w)
    (t : Fin (m + 1))
    (hx : splitCas E x = ((-mu t + (1 - ((m + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • x) (i : Fin (m + 1)) (Y : ℂ) :
    ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) =
      (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
  have key : ∀ Y : ℂ, (Y + (mu t : ℂ)) • ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) =
      (Y + (mu t : ℂ)) • (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
    intro Y
    have hT : ∀ j, ∑ l, Tm E (Y + (m : ℂ) / 2 - (m : ℂ)) j l (x l) = (Y + (mu t : ℂ)) • x j := by
      intro j
      have h1 := congrFun hx j
      simp only [splitCas, Pi.smul_apply] at h1
      have h2 : ∀ l, Tm E (Y + (m : ℂ) / 2 - (m : ℂ)) j l (x l) =
          (if j = l then (Y + (m : ℂ) / 2 - (m : ℂ)) • x l else 0) + E j l (x l) := by
        intro l
        rw [Tm, LinearMap.add_apply]
        split_ifs
        · rw [Module.algebraMap_end_apply]
        · rw [LinearMap.zero_apply]
      simp only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [neg_eq_iff_eq_neg] at h1
      rw [h1, ← neg_smul, ← add_smul]
      congr 1
      push_cast
      ring
    have hu : Y + (m : ℂ) / 2 = Y + (((m + 1 : ℕ) : ℂ) - 1) / 2 := by push_cast; ring
    have h3 : ∑ l, (if i = l then qdet E (Y + (m : ℂ) / 2) else 0) (x l) =
        (Y + (mu t : ℂ)) • (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, hu, hq, smul_smul, Finset.mul_prod_erase _ (fun r => Y + (mu r : ℂ)) (Finset.mem_univ t)]
      · intro l _ hl
        rw [if_neg (Ne.symm hl), LinearMap.zero_apply]
      · simp
    rw [← h3]
    simp only [← qComatrix (Module.End ℂ M) m E hE (Y + (m : ℂ) / 2) i, LinearMap.sum_apply]
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Module.End.mul_apply]

    rw [← map_sum, ← map_sum, hT, map_smul, map_smul, Module.End.intCast_apply,
    ← Int.cast_smul_eq_zsmul ℂ]
    push_cast
    rfl
  have hc1 : Continuous fun Y : ℂ => ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) •
      qminor E (Fin.succAbove j) (Fin.succAbove i) (Y + (m : ℂ) / 2) (x j) := by
    refine continuous_finsetSum _ fun j _ => Continuous.const_smul ?_ _
    exact (continuous_qminor_apply E _ _ (x j)).comp (continuous_add_const _)
  have hc2 : Continuous fun Y : ℂ => (∏ r ∈ univ.erase t, (Y + (mu r : ℂ))) • x i := by fun_prop
  have hd : Dense ({-(mu t : ℂ)}ᶜ : Set ℂ) := dense_compl_singleton _
  refine congrFun (Continuous.ext_on hd hc1 hc2 fun Z hZ => ?_) Y
  have hne : Z + (mu t : ℂ) ≠ 0 := fun h => hZ (eq_neg_of_add_eq_zero_left h)
  exact smul_right_injective M hne (key Z)

end GlobalTheory.ComatrixEigen

namespace GlobalTheory

theorem comatrix_picks_eigencomponent : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (mu : Fin (m + 1) → ℝ) (y : Fin (m + 1) → Fin (m + 1) → M), Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ t, splitCas E (y t) = ((-mu t + (1 - ((m + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∀ s i, ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) • Formalism.REAL.qminor E (Fin.succAbove j) (Fin.succAbove i) (-(mu s : ℂ) + (m : ℂ) / 2) (∑ t, y t j) = (∏ t ∈ univ.erase s, ((mu t : ℂ) - mu s)) • y s i := by
  intro M _ _ m E mu y hE hq hy s i

  simp only [map_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  simp only [fun t => ComatrixEigen.cof_eigen E mu (y t) hE hq t (hy t) i (-(mu s : ℂ))]
  rw [Finset.sum_eq_single s]
  · simp only [neg_add_eq_sub]
  · intro t _ ht
    rw [Finset.prod_eq_zero (i := s) (Finset.mem_erase.2 ⟨Ne.symm ht, Finset.mem_univ _⟩) (neg_add_cancel _),
      zero_smul]
  · simp

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliComatrixPicksSplitCasimirEigencomponentStatement

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.capelliComatrix_picks_splitCasimir_eigencomponent : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (mu : Fin (m + 1) → ℝ) (y : Fin (m + 1) → Fin (m + 1) → M), Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + (((m + 1 : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ t, splitCas E (y t) = ((-mu t + (1 - ((m + 1 : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∀ s i, ∑ j : Fin (m + 1), ((-1 : ℂ) ^ (i.val + j.val)) • Formalism.REAL.qminor E (Fin.succAbove j) (Fin.succAbove i) (-(mu s : ℂ) + (m : ℂ) / 2) (∑ t, y t j) = (∏ t ∈ univ.erase s, ((mu t : ℂ) - mu s)) • y s i := by
  first | exact @GlobalTheory.comatrix_picks_eigencomponent | exact GlobalTheory.comatrix_picks_eigencomponent | (intros; apply GlobalTheory.comatrix_picks_eigencomponent <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorBlockLinearMapIntertwine

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem map_ofFn_prod_apply_of_intertwine {M Wp : Type} [AddCommGroup M] [Module ℂ M]
    (l : M → Wp) :
    ∀ (t : ℕ) (f : Fin t → Module.End ℂ M) (g : Fin t → Wp → Wp),
      (∀ k v, l (f k v) = g k (l v)) → ∀ v,
      l ((List.ofFn f).prod v) = List.foldr (fun T h => T h) (l v) (List.ofFn g) := by
  intro t
  induction t with
  | zero => intro f g _ v; simp
  | succ t ih =>
    intro f g h v
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.foldr_cons, Module.End.mul_apply, h,
      ih (fun i => f i.succ) (fun i => g i.succ) (fun k v => h k.succ v) v]

theorem qminor_block_intertwine : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n m : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (w : Fin m → Fin n) (Pop : Fin m → Fin m → Wp → Wp), Function.Injective w → (∀ i j v, l (E (w i) (w j) v) = Pop i j (l v)) → ∀ u v, l (Formalism.REAL.qminor E w w u v) = Formalism.FourierDecayAlt.Q.qmF Pop id id u (l v) := by
  intro M Wp _ _ _ _ n m E l w Pop hw h u v
  unfold Formalism.REAL.qminor Formalism.FourierDecayAlt.Q.qmF

  rw [LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have key := map_ofFn_prod_apply_of_intertwine (l : M → Wp) m
    (fun k => Formalism.REAL.Tm E (u - ((k : ℕ) : ℂ)) (w (σ k)) (w k))
    (fun k y => (if id (σ k) = id k then (u - ((k : ℕ) : ℂ)) • y else 0) + Pop (id (σ k)) (id k) y)
    (fun k x => by
      unfold Formalism.REAL.Tm
      by_cases hk : σ k = k
      · simp [hk, h, sub_smul, Nat.cast_smul_eq_nsmul]
      · have : w (σ k) ≠ w k := fun e => hk (hw e)
        simp [hk, this, h]) v
  rw [← key, Module.End.mul_apply]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorBlockLinearMapIntertwineStatement

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.quantumMinor_block_linearMap_intertwine : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (n m : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (w : Fin m → Fin n) (Pop : Fin m → Fin m → Wp → Wp), Function.Injective w → (∀ i j v, l (E (w i) (w j) v) = Pop i j (l v)) → ∀ u v, l (Formalism.REAL.qminor E w w u v) = Formalism.FourierDecayAlt.Q.qmF Pop id id u (l v) := by
  first | exact @GlobalTheory.qminor_block_intertwine | exact GlobalTheory.qminor_block_intertwine | (intros; apply GlobalTheory.qminor_block_intertwine <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjectorEntryValueUnderLinearFunctional

section

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory
private theorem qminor_cast {M : Type} [AddCommGroup M] [Module ℂ M] {n a b : ℕ} (E : Fin n → Fin n → Module.End ℂ M)
    (h : a = b) (f g : Fin b → Fin n) (u : ℂ) :
    Formalism.REAL.qminor E (fun i : Fin a => f (Fin.cast h i)) (fun i : Fin a => g (Fin.cast h i)) u
      = Formalism.REAL.qminor E f g u := by
  subst h
  rfl
end GlobalTheory

namespace GlobalTheory

theorem capelli_projector_entry_value : ∀ (M Wp : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → ∀ (mu : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (Pop : Fin k → Fin k → Wp → Wp), Function.Injective mu → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((((2 * r + k + 1) : ℕ) : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → (∀ i j v, l (E ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) v) = Pop i j (l v)) → (∀ (w : ℂ) (x : Wp), Formalism.FourierDecayAlt.Q.qmF Pop id id w x = (∏ i ∈ Icc 1 k, (w - (k : ℂ) / 2 + 1 / 2 + (u i : ℂ))) • x) → ∀ s, ∃ c : ℂ, ‖c‖ = (if r = 0 then 1 else τ ^ 2) * ((∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i|) / ∏ t ∈ univ.erase s, |mu s - mu t|) ∧ ∀ (v : M) (y : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → M), (∀ t, splitCas E (y t) = ((-mu t + (1 - (((2 * r + k + 1) : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∑ t, y t = Pi.single (Fin.last (2 * r + k)) v → l (y s (if r = 0 then Fin.last (2 * r + k) else 0)) = c • l v := by
  intro M Wp _ _ _ _ k r E l p τ hk hE hp mu u Pop hmu hq hP hW s
  set D : ℂ := ∏ t ∈ univ.erase s, ((mu t : ℂ) - mu s) with hD
  set N : ℂ := ∏ i ∈ Icc 1 k, (-(mu s : ℂ) + 1 / 2 + (u i : ℂ)) with hN
  have hDn : ‖D‖ = ∏ t ∈ univ.erase s, |mu s - mu t| := by
    rw [hD, norm_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hNn : ‖N‖ = ∏ i ∈ Icc 1 k, |mu s - 1 / 2 - u i| := by
    rw [hN, norm_prod]
    refine Finset.prod_congr rfl fun t _ => ?_
    have : (-(mu s : ℂ) + 1 / 2 + (u t : ℂ)) = ((-(mu s - 1 / 2 - u t) : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg]
  have hD0 : D ≠ 0 := by
    rw [hD, Finset.prod_ne_zero_iff]
    intro t ht h
    have h1 : mu t = mu s := by exact_mod_cast sub_eq_zero.mp h
    exact (Finset.mem_erase.mp ht).1 (hmu h1)
  have hinj : Function.Injective (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) := by
    intro a b h
    have := congrArg Fin.val h
    simp only at this
    exact Fin.ext (by omega)
  have hblock : ∀ v, l (Formalism.REAL.qminor E (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (-(mu s : ℂ) + (k : ℂ) / 2) v) = N • l v := by
    intro v
    rw [GlobalTheory.T.quantumMinor_block_linearMap_intertwine M Wp _ k E l _ Pop hinj hP, hW, hN]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    ring
  have hcof : ∀ (v : M) (y : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → M), (∀ t, splitCas E (y t) = ((-mu t + (1 - (((2 * r + k + 1) : ℕ) : ℝ)) / 2 : ℝ) : ℂ) • y t) → ∑ t, y t = Pi.single (Fin.last (2 * r + k)) v → ∀ i : Fin (2 * r + k + 1),
      D • l (y s i) = ((-1 : ℂ) ^ (i.val + (2 * r + k))) • l (Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * r + k))) (Fin.succAbove i) (-(mu s : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) v) := by
    intro v y hy hs i
    have h := GlobalTheory.T.capelliComatrix_picks_splitCasimir_eigencomponent M (2 * r + k) E mu y hE hq hy s i
    have hj : ∀ j, ∑ t, y t j = (Pi.single (Fin.last (2 * r + k)) v : Fin (2 * r + k + 1) → M) j := by
      intro j
      rw [← hs, Finset.sum_apply]
    rw [Finset.sum_eq_single (Fin.last (2 * r + k))] at h
    · rw [hj, Pi.single_eq_same] at h
      rw [← map_smul, ← map_smul, hD, ← h]
      rfl
    · intro j _ hne
      rw [hj, Pi.single_eq_of_ne hne]
      simp
    · simp
  by_cases hr : r = 0
  · refine ⟨D⁻¹ * N, ?_, ?_⟩
    · rw [norm_mul, norm_inv, hDn, hNn, if_pos hr]; ring
    · intro v y hy hs
      rw [if_pos hr]
      have h := hcof v y hy hs (Fin.last _)
      subst hr
      have hm : Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * 0 + k))) (Fin.succAbove (Fin.last (2 * 0 + k))) (-(mu s : ℂ) + ((2 * 0 + k : ℕ) : ℂ) / 2) = Formalism.REAL.qminor E (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1)))
          (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1))) (-(mu s : ℂ) + (k : ℂ) / 2) := by
        have := qminor_cast E (show k = 2 * 0 + k by omega) (Fin.succAbove (Fin.last (2 * 0 + k))) (Fin.succAbove (Fin.last (2 * 0 + k))) (-(mu s : ℂ) + (k : ℂ) / 2)
        have e : (fun i : Fin k => (⟨0 + i.val, by omega⟩ : Fin (2 * 0 + k + 1))) = fun i => Fin.succAbove (Fin.last (2 * 0 + k)) (Fin.cast (show k = 2 * 0 + k by omega) i) := by
          funext i
          apply Fin.ext
          simp
        rw [e, this]
        simp
      rw [hm, hblock] at h
      have hs1 : ((-1 : ℂ) ^ ((Fin.last (2 * 0 + k)).val + (2 * 0 + k))) = 1 := by
        rw [Fin.val_last, ← two_mul, pow_mul]; simp
      rw [hs1, one_smul] at h
      rw [mul_smul, ← h, smul_smul, inv_mul_cancel₀ hD0, one_smul]
  · have hr1 : 1 ≤ r := by omega
    obtain ⟨c1, hc1, h1⟩ := GlobalTheory.T.glRelation_row_steps_functional_eigen M Wp k r E l p τ hk hE hp hr1
    obtain ⟨c2, hc2, h2⟩ := GlobalTheory.T.besselColumnSteps_functional_eigen M Wp k r E l p τ hk hE hp hr1
    refine ⟨D⁻¹ * ((-1 : ℂ) ^ (2 * r + k) * (c1 * (c2 * N))), ?_, ?_⟩
    · rw [norm_mul, norm_inv, norm_mul, norm_mul, norm_mul, hDn, hNn, if_neg hr, hc1, hc2, norm_pow]
      simp only [norm_neg, norm_one, one_pow]
      ring
    · intro v y hy hs
      rw [if_neg hr]
      have h := hcof v y hy hs 0
      have e : (-(mu s : ℂ) + ((2 * r + k : ℕ) : ℂ) / 2) - (r : ℂ) = -(mu s : ℂ) + (k : ℂ) / 2 := by
        push_cast; ring
      rw [h1, h2, e, hblock, Fin.val_zero, zero_add] at h
      rw [mul_smul, mul_smul, mul_smul, mul_smul, ← h, smul_smul, inv_mul_cancel₀ hD0, one_smul]

end GlobalTheory
end
end
