module

public import Formalism.PieriBlockIdeals.PieriColumnMinors.XiOfDepth2
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.PieriBlockIdeals.PieriColumnMinors.DividedPowerZeroZeroVector
public import Formalism.PieriBlockIdeals.IntegralQuotient
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Formalism.PieriBlockIdeals.PieriColumnMinors.FsDivMem

section

@[expose] public section

namespace Formalism.CohomologicalDescent.LR

open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.Symmetrization

theorem lrd_core {ι V : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℚ V]
    (φ : ι → Module.End ℚ V) (hφ : ∀ a b, Commute (φ a) (φ b)) (L : AddSubgroup V)
    (hL : ∀ (v : ι) (k : ℕ), ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • ((φ v) ^ k) x ∈ L) :
    ∀ (M : Multiset ι), ∀ x ∈ L,
      (((∏ v, (Multiset.count v M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x ∈ L := by
  suffices key : ∀ n : ℕ, ∀ M : Multiset ι, Multiset.card M = n → ∀ x ∈ L,
      (((∏ v, (Multiset.count v M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x ∈ L by
    intro M
    exact key _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hn x hx
    by_cases hM : M = 0
    · subst hM
      simp [hx]
    obtain ⟨v, hv⟩ := Multiset.exists_mem_of_ne_zero hM

    set c := Multiset.count v M with hc
    set M' := M.filter (fun w => ¬ w = v) with hM'
    have hsplit : M = Multiset.replicate c v + M' := by
      rw [hM', hc, ← Multiset.filter_eq' M v, Multiset.filter_add_not]
    have hc0 : 0 < c := Multiset.count_pos.mpr hv
    have hcard : Multiset.card M' < n := by
      have e := congrArg Multiset.card hsplit
      rw [Multiset.card_add, Multiset.card_replicate] at e
      omega
    have hperm : M.toList.Perm (List.replicate c v ++ M'.toList) := by
      have e : (M.toList : Multiset ι) = ((List.replicate c v ++ M'.toList : List ι) : Multiset ι) := by
        rw [Multiset.coe_toList, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_replicate]
        exact hsplit
      exact Multiset.coe_eq_coe.mp e
    have hpw : (M.toList.map φ).Pairwise Commute :=
      List.pairwise_map.mpr (List.pairwise_of_forall fun a b => hφ a b)
    have hprod : (M.toList.map φ).prod = φ v ^ c * (M'.toList.map φ).prod := by
      rw [(hperm.map φ).prod_eq' hpw]
      simp [List.map_append, List.prod_append, List.map_replicate, List.prod_replicate]

    have hcnt : ∀ w ∈ Finset.univ.erase v, Multiset.count w M' = Multiset.count w M := by
      intro w hw
      exact Multiset.count_filter_of_pos (Finset.ne_of_mem_erase hw)
    have hcv : Multiset.count v M' = 0 := Multiset.count_filter_of_neg (fun h => h rfl)
    have hfact : (∏ w, (Multiset.count w M).factorial : ℕ) =
        c.factorial * ∏ w, (Multiset.count w M').factorial := by
      rw [← Finset.mul_prod_erase Finset.univ (fun w => (Multiset.count w M).factorial) (Finset.mem_univ v),
        ← Finset.mul_prod_erase Finset.univ (fun w => (Multiset.count w M').factorial) (Finset.mem_univ v),
        hcv, Nat.factorial_zero, one_mul]
      congr 1
      exact Finset.prod_congr rfl fun w hw => by rw [hcnt w hw]
    have hrest := ih _ (hn ▸ hcard) M' rfl x hx
    have e : (((∏ w, (Multiset.count w M).factorial : ℕ) : ℚ)⁻¹) • (M.toList.map φ).prod x =
        ((c.factorial : ℚ)⁻¹) • (φ v ^ c)
          ((((∏ w, (Multiset.count w M').factorial : ℕ) : ℚ)⁻¹) • (M'.toList.map φ).prod x) := by
      rw [hprod, hfact, Module.End.mul_apply, map_smul, smul_smul, Nat.cast_mul, mul_inv]
    rw [e]
    exact hL v c _ hrest

theorem Fs_div_mem {V P R : Type} [AddCommGroup V] [Module ℚ V] [DecidableEq P] [DecidableEq R] [Fintype P]
    [Fintype R] (S : Symmetrization.HidaSetting ℚ V P R) (L : AddSubgroup V)
    (hL : ∀ (v : R × P) (k : ℕ), ∀ x ∈ L, ((k.factorial : ℚ)⁻¹) • ((S.f v) ^ k) x ∈ L) {n : ℕ}
    (m : Sym (R × P) n) : ∀ x ∈ L, ((Symmetrization.mfact m : ℚ)⁻¹) • S.Fs m x ∈ L := by
  have hcomm : ∀ a b : R × P, Commute (S.f a) (S.f b) := by
    intro a b
    have h := S.comm (Sum.inr a.1) (Sum.inl a.2) (Sum.inr b.1) (Sum.inl b.2)
    simp only [reduceCtorEq, if_false, sub_zero] at h
    exact sub_eq_zero.mp h
  intro x hx
  exact lrd_core S.f hcomm L hL m.1 x hx

end Formalism.CohomologicalDescent.LR
end
end

-- Source module: Formalism.PieriBlockIdeals.PieriColumnMinors.LriEVPowCoe

section

@[expose] public section

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lri_LevZ_le (p q w : ℕ) (lam2 : Fin q → ℕ) :
    LevZ p q w lam2 ≤ (weyl ℤ (p + q) (p + q) le_rfl (LD.blockWt p q w lam2)).map (intQ (p + q) (p + q)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨ω, rfl⟩
  refine ⟨applyWord ℤ (liftWord p ω) (hw ℤ le_rfl (LD.blockWt p q w lam2)), Submodule.subset_span ⟨liftWord p ω, rfl⟩, ?_⟩
  rw [lrc_intQ_apply, ← lclosedeq_applyWord_map, lclosedeq_hw_map]

theorem MW_le_MV (p q w : ℕ) (lam2 : Fin q → ℕ) (u : (rationalBlockModuleSetting p q w lam2).W) (hu : u ∈ MW p q w lam2) :
    (u : VQ p q w lam2) ∈ MV p q w lam2 :=
  lri_LevZ_le p q w lam2 hu

theorem lri_EV_pow_coe (p q w : ℕ) (lam2 : Fin q → ℕ) (a b : Fin p ⊕ Fin q) (k : ℕ) (x : VQ p q w lam2) :
    ((((EV p q w lam2 a b) ^ k) x : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) =
      ((der (p + q) (p + q) (idx p q a) (idx p q b) : Module.End ℚ _) ^ k) (x : MvPolynomial _ ℚ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, EV_coe, ih, pow_succ', Module.End.mul_apply]
    rfl

theorem lri_hL (p q w : ℕ) (lam2 : Fin q → ℕ) (v : Fin q × Fin p) (k : ℕ) (x : VQ p q w lam2)
    (hx : x ∈ MV p q w lam2) :
    ((k.factorial : ℚ)⁻¹) • (((rationalBlockModuleSetting p q w lam2).f v) ^ k) x ∈ MV p q w lam2 := by
  rw [mem_MV] at hx ⊢
  obtain ⟨y, hy, hyx⟩ := hx
  have hne : Fin.natAdd p v.1 ≠ Fin.castAdd q v.2 := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
    have := v.2.isLt
    omega
  have e : (((((k.factorial : ℚ)⁻¹) • (((rationalBlockModuleSetting p q w lam2).f v) ^ k) x : VQ p q w lam2)) :
      MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) =
      rowDiv ℚ (Fin.natAdd p v.1) (Fin.castAdd q v.2) k (x : MvPolynomial _ ℚ) := by
    rw [der_pow _ _ hne, Submodule.coe_smul]
    congr 1
    exact lri_EV_pow_coe p q w lam2 (Sum.inr v.1) (Sum.inl v.2) k x
  rw [e, ← hyx, lrc_intQ_apply, lclosedeq_rowDiv_map]
  exact ⟨_, weylRowDivStable ℤ _ _ le_rfl _ _ _ k y hy, rfl⟩

theorem lri_coe_zsmul (p q w : ℕ) (lam2 : Fin q → ℕ) (m : ℤ) (u : (rationalBlockModuleSetting p q w lam2).W) :
    ((m • u : (rationalBlockModuleSetting p q w lam2).W) : VQ p q w lam2) = m • (u : VQ p q w lam2) := by
  simp

theorem deltaAll_le (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ) :
    DeltaAll (rationalBlockModuleSetting p q w lam2) (DelLR l hl p q w lam2) ≤ locSpan l hl (MV p q w lam2) := by
  refine iSup_le fun n => Submodule.span_le.mpr ?_
  rintro x ⟨m, u, hu, rfl⟩
  obtain ⟨m₀, hm₀, hmu⟩ := (mem_locSpan l hl _ u).1 hu
  have h1 := MW_le_MV p q w lam2 _ hmu
  rw [lri_coe_zsmul] at h1
  have h2 := Fs_div_mem (rationalBlockModuleSetting p q w lam2) (MV p q w lam2) (lri_hL p q w lam2) m _ h1
  refine ⟨m₀, hm₀, ?_⟩
  have e : ((Symmetrization.mfact m : ℚ)⁻¹) • (rationalBlockModuleSetting p q w lam2).Fs m (m₀ • (u : VQ p q w lam2)) =
      m₀ • (((Symmetrization.mfact m : ℚ)⁻¹) • (rationalBlockModuleSetting p q w lam2).Fs m (u : VQ p q w lam2)) := by
    rw [map_zsmul, smul_comm]
  rw [← e]
  exact h2

theorem lri_intQ_zsmul (r : ℕ) (z : ℤ) (x : MvPolynomial (Fin r × Fin r) ℤ) :
    intQ r r (z • x) = (z : ℚ) • intQ r r x := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem lri_intQ_inj (r : ℕ) : Function.Injective (intQ r r) := by
  intro x y h
  rw [lrc_intQ_apply, lrc_intQ_apply] at h
  exact MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ)) h

theorem mem_dual (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w)
    (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) (hx : x ∈ dualWeyl ℤ (p + q) (p + q) (LD.blockWt p q w lam2))
    (hx' : intQ _ _ x ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)) :
    (⟨intQ _ _ x, hx'⟩ : VQ p q w lam2) ∈
      (formB p q w lam2).dualSubmodule (DeltaAll (rationalBlockModuleSetting p q w lam2) (DelLR l hl p q w lam2)) := by
  have hanti := LD.ld_blockWt_anti p q w lam2 ha hb
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  obtain ⟨m, hm, hmy⟩ := (mem_locSpan l hl _ y).1 (deltaAll_le l hl p q w lam2 hy)
  rw [mem_MV] at hmy
  obtain ⟨y', hy', hy'e⟩ := hmy
  obtain ⟨z, hz⟩ := fock_int (p + q) _ hanti x hx y' hy'
  rw [mem_one_iff, zl_mem_iff hl]
  refine ⟨m, hm, z, ?_⟩
  have hc := (hw_norm_pos (LD.blockWt p q w lam2)).ne'
  have e1 : (m : ℚ) * formB p q w lam2 ⟨intQ _ _ x, hx'⟩ y = formB p q w lam2 ⟨intQ _ _ x, hx'⟩ (m • y) := by
    rw [map_zsmul, zsmul_eq_mul]
  rw [e1, formB_apply]
  have e2 : (((m • y : VQ p q w lam2)) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = intQ _ _ y' := by
    rw [hy'e]
  rw [e2]
  change fockQ (intQ (p + q) (p + q) x) (intQ (p + q) (p + q) y') / _ = _
  rw [hz, mul_div_assoc, div_self hc, mul_one]

theorem concl (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ)
    (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ)
    (hx' : intQ _ _ x ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)) (E : ℕ)
    (h : ((l : Zl l) ^ E) • (⟨intQ _ _ x, hx'⟩ : VQ p q w lam2) ∈
      DeltaAll (rationalBlockModuleSetting p q w lam2) (DelLR l hl p q w lam2)) :
    ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ (m * (l : ℤ) ^ E) • x ∈ weyl ℤ (p + q) (p + q) le_rfl (LD.blockWt p q w lam2) := by
  obtain ⟨m, hm, hmv⟩ := (mem_locSpan l hl _ _).1 (deltaAll_le l hl p q w lam2 h)
  rw [mem_MV] at hmv
  obtain ⟨y, hy, hye⟩ := hmv
  refine ⟨m, hm, ?_⟩
  have e : intQ _ _ ((m * (l : ℤ) ^ E) • x) = intQ _ _ y := by
    rw [hye, lri_intQ_zsmul]
    simp only [Submodule.coe_smul_of_tower, lrc_smul_def]
    rw [← Int.cast_smul_eq_zsmul ℚ m, smul_smul]
    congr 1
    push_cast
    rfl
  rw [lri_intQ_inj _ e]
  exact hy

theorem wt_of_hom (p q w : ℕ) (lam2 : Fin q → ℕ) (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ)
    (hx' : intQ _ _ x ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)) (μ : Fin (p + q) → ℕ)
    (hμ : IsWeightedHomogeneous (rowW (p + q) (p + q)) x μ) :
    (⟨intQ _ _ x, hx'⟩ : VQ p q w lam2) ∈ (rationalBlockModuleSetting p q w lam2).wt fun a => (μ (idx p q a) : ℤ) := by
  refine (real_weight p q w lam2 _ μ).1 ?_
  intro d hd
  apply hμ
  intro h0
  apply hd
  change AddMonoidAlgebra.coeff (intQ _ _ x) d = 0
  rw [lrc_intQ_apply, coeff_map, h0, map_zero]

theorem dominant_xi {p q : ℕ} (ξ : Fin (p + q) → ℤ) (hξ : Antitone ξ) (α : Fin p) (b : Fin q) :
    0 ≤ xiOf ξ (Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1) := by
  show 0 ≤ ∑ a, ξ (idx p q a) * ((Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1 : Fin p ⊕ Fin q → ℤ) a)
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine sub_nonneg.mpr (hξ ?_)
  show Fin.castAdd q α ≤ Fin.natAdd p b
  rw [Fin.le_def]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  omega

end Formalism.CohomologicalDescent.LR
end
end
end
