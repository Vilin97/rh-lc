module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
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
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumRefine

section

@[expose] public section

namespace GlobalTheory.SumRefinement

theorem finsum_fst {X F : Type} [Finite F] (g : X → ℂ) (hg : (Function.support g).Finite) :
    ∑ᶠ p : X × F, g p.1 = (Nat.card F : ℂ) * ∑ᶠ x, g x := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  rw [finsum_eq_sum_of_support_subset (s := hg.toFinset ×ˢ Finset.univ) _ ?_,
    finsum_eq_sum_of_support_subset (s := hg.toFinset) _ (by simp),
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · intro p hp
    simp only [Function.mem_support] at hp
    simp [hp]

theorem sum_refine {W : Type} [AddCommGroup W] {A B C : AddSubgroup W} {φ : W → ℂ}
    (h : GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hi : AddSubgroup.relIndex C B ≠ 0) :
    ∑ᶠ (c : W ⧸ C), φ (Quotient.out c) =
      (AddSubgroup.relIndex C B : ℂ) * ∑ᶠ (c : W ⧸ B), φ (Quotient.out c) := by
  classical
  obtain ⟨-, -, hinv, hfin⟩ := h
  set e := AddSubgroup.quotientEquivProdOfLE hCB with he
  have hfst : ∀ x : W ⧸ C, (e x).1 = (QuotientAddGroup.mk (Quotient.out x) : W ⧸ B) := by
    intro x
    conv_lhs => rw [← Quotient.out_eq' x]
    rfl
  have hcong : ∀ u v : W, (QuotientAddGroup.mk u : W ⧸ B) = QuotientAddGroup.mk v → φ u = φ v := by
    intro u v huv
    have hb : -u + v ∈ B := QuotientAddGroup.eq.1 huv
    have h1 := hinv u (-u + v) hb
    rw [add_neg_cancel_left] at h1
    exact h1.symm
  have hval : ∀ x : W ⧸ C, φ (Quotient.out x) = φ (Quotient.out (e x).1) := by
    intro x
    rw [hfst]
    exact hcong _ _ (QuotientAddGroup.out_eq' _).symm
  have : Finite (↥B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hi
  have hg : (Function.support fun b : W ⧸ B => φ (Quotient.out b)).Finite := by
    refine hfin.subset ?_
    intro b hb
    exact ⟨Quotient.out b, hb, QuotientAddGroup.out_eq' b⟩
  rw [← finsum_comp_equiv e.symm]
  simp_rw [hval, Equiv.apply_symm_apply]
  rw [finsum_fst (fun b : W ⧸ B => φ (Quotient.out b)) hg]
  rfl

end GlobalTheory.SumRefinement
end
end

-- Source module: Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CintTranslate

section

@[expose] public section

noncomputable section
open scoped Classical

namespace GlobalTheory.IdxInt.Model
open GlobalTheory.IdxInt

variable {W : Type} [AddCommGroup W]

lemma out_mk {φ : W → ℂ} {B : AddSubgroup W} (h : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) (w : W) :
    φ (QuotientAddGroup.mk w : W ⧸ B).out = φ w := by
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_out_eq_add B w
  rw [hb]; exact h w b b.2

lemma sum_refine {A B C : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (hC : C ≤ B)
    (hi : C.relIndex B ≠ 0) :
    (∑ᶠ c : W ⧸ C, φ c.out) = (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ c.out := by
  first
  | exact @_root_.GlobalTheory.SumRefinement.sum_refine
  | exact _root_.GlobalTheory.SumRefinement.sum_refine
  | (apply _root_.GlobalTheory.SumRefinement.sum_refine <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumRefinement.sum_refine <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumRefinement.sum_refine <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumRefinement.sum_refine ..)

lemma ratio_eq {A B B' : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (h' : Fine A φ B') :
    (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) = (∑ᶠ c : W ⧸ B', φ c.out) / (B'.relIndex A : ℂ) := by
  have hC : (B ⊓ B').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero h.2.1 h'.2.1
  have m1 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B A inf_le_left h.1
  have m2 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B' A inf_le_right h'.1
  have i1 : (B ⊓ B').relIndex B ≠ 0 := fun z => hC (by rw [← m1, z, zero_mul])
  have i2 : (B ⊓ B').relIndex B' ≠ 0 := fun z => hC (by rw [← m2, z, zero_mul])
  have s1 := sum_refine h inf_le_left i1
  have s2 := sum_refine h' inf_le_right i2
  have c1 : (B.relIndex A : ℂ) ≠ 0 := by exact_mod_cast h.2.1
  have c2 : (B'.relIndex A : ℂ) ≠ 0 := by exact_mod_cast h'.2.1
  have c3 : (((B ⊓ B').relIndex B : ℕ) : ℂ) ≠ 0 := by exact_mod_cast i1
  have c4 : (((B ⊓ B').relIndex B' : ℕ) : ℂ) ≠ 0 := by exact_mod_cast i2
  have m : (((B ⊓ B').relIndex B : ℕ) : ℂ) * (B.relIndex A : ℂ) = (((B ⊓ B').relIndex B' : ℕ) : ℂ) * (B'.relIndex A : ℂ) := by
    exact_mod_cast m1.trans m2.symm
  rw [← mul_div_mul_left _ _ c3, ← s1, ← mul_div_mul_left (∑ᶠ c : W ⧸ B', φ c.out) _ c4, ← s2, m]

theorem cint_eq {A B : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) :
    cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by
  have hn : Nice A φ := ⟨B, h⟩
  rw [cint, dite_eq_left hn]
  exact ratio_eq hn.choose_spec h

lemma fine_refine {A B C : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (hC : C ≤ B)
    (hi : C.relIndex A ≠ 0) : Fine A φ C := by
  have m1 := AddSubgroup.relIndex_mul_relIndex C B A hC h.1
  have i1 : C.relIndex B ≠ 0 := fun z => hi (by rw [← m1, z, zero_mul])
  haveI : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero i1
  refine ⟨hC.trans h.1, hi, fun w b hb => h.2.2.1 w b (hC hb), ?_⟩
  let e := AddSubgroup.quotientEquivProdOfLE hC
  refine ((h.2.2.2.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage
    e.injective.injOn).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨⟨w, hw, rfl⟩, trivial⟩

end GlobalTheory.IdxInt.Model
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralProdFubini

section

@[expose] public section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

namespace GlobalTheory.IdxInt.Fubini

variable {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W']

lemma relIndex_prod (H K : AddSubgroup W) (H' K' : AddSubgroup W') :
    (H.prod H').relIndex (K.prod K') = H.relIndex K * H'.relIndex K' := by
  unfold AddSubgroup.relIndex
  rw [← AddSubgroup.index_prod,
    ← AddSubgroup.index_comap_of_surjective ((H.addSubgroupOf K).prod (H'.addSubgroupOf K'))
      (f := (AddSubgroup.prodEquiv K K').toAddMonoidHom) (AddSubgroup.prodEquiv K K').surjective]
  congr 1

lemma exists_fine_prod {A : AddSubgroup W} {A' : AddSubgroup W'} {φ : W × W' → ℂ}
    (h : Nice (A.prod A') φ) :
    ∃ (B : AddSubgroup W) (B' : AddSubgroup W'), B ≤ A ∧ B' ≤ A' ∧ B.relIndex A ≠ 0 ∧
      B'.relIndex A' ≠ 0 ∧ Fine (A.prod A') φ (B.prod B') := by
  obtain ⟨C, hC⟩ := h
  have i1 : (C.comap (AddMonoidHom.inl W W')).relIndex A ≠ 0 := by
    rw [AddSubgroup.relIndex_comap]
    intro z
    refine hC.2.1 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ z)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨ha, A'.zero_mem⟩
  have i2 : (C.comap (AddMonoidHom.inr W W')).relIndex A' ≠ 0 := by
    rw [AddSubgroup.relIndex_comap]
    intro z
    refine hC.2.1 (AddSubgroup.relIndex_eq_zero_of_le_right ?_ z)
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨A.zero_mem, ha⟩
  refine ⟨C.comap (AddMonoidHom.inl W W'), C.comap (AddMonoidHom.inr W W'),
    fun a ha => (hC.1 ha).1, fun a ha => (hC.1 ha).2, i1, i2, Model.fine_refine hC ?_ ?_⟩
  · rintro ⟨a, b⟩ ⟨ha, hb⟩
    have := C.add_mem ha hb
    simpa using this
  · rw [relIndex_prod]
    exact mul_ne_zero i1 i2

theorem cint_prod (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ)
    (h : Nice (A.prod A') φ) :
    (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧
      cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by
  obtain ⟨B, B', hB, hB', i1, i2, hF⟩ := exists_fine_prod h
  let e := QuotientAddGroup.prodEquiv B B'
  have he : ∀ p : W × W', e (QuotientAddGroup.mk p) =
      ((QuotientAddGroup.mk p.1 : W ⧸ B), (QuotientAddGroup.mk p.2 : W' ⧸ B')) := fun _ => rfl
  have hS := hF.2.2.2.image e
  have f1 : ∀ w, Fine A' (fun w' => φ (w, w')) B' := by
    intro w
    refine ⟨hB', i2, fun w' b hb => ?_, (hS.image Prod.snd).subset ?_⟩
    · have := hF.2.2.1 (w, w') (0, b) ⟨B.zero_mem, hb⟩
      simpa using this
    · rintro _ ⟨w', hw', rfl⟩
      exact ⟨_, ⟨_, ⟨(w, w'), hw', rfl⟩, rfl⟩, rfl⟩
  have hinv : ∀ w, ∀ b ∈ B, (fun w' => φ (w + b, w')) = fun w' => φ (w, w') := by
    intro w b hb
    funext w'
    have := hF.2.2.1 (w, w') (b, 0) ⟨hb, B'.zero_mem⟩
    simpa using this
  have f2 : Fine A (fun w => cint A' (fun w' => φ (w, w'))) B := by
    refine ⟨hB, i1, fun w b hb => by simp only [hinv w b hb], (hS.image Prod.fst).subset ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have : ∃ w', φ (w, w') ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hw
      show cint A' (fun w' => φ (w, w')) = 0
      rw [Model.cint_eq (f1 w)]
      simp [hn]
    obtain ⟨w', hw'⟩ := this
    exact ⟨_, ⟨_, ⟨(w, w'), hw', rfl⟩, rfl⟩, rfl⟩
  refine ⟨fun w => ⟨B', f1 w⟩, ⟨B, f2⟩, ?_⟩
  rw [Model.cint_eq hF, Model.cint_eq f2, relIndex_prod]
  simp only [fun w => Model.cint_eq (f1 w)]
  have h1 : ∀ p : (W ⧸ B) × (W' ⧸ B'), φ (e.symm p).out = φ (p.1.out, p.2.out) := by
    intro p
    have : e.symm p = QuotientAddGroup.mk (p.1.out, p.2.out) := by
      rw [Equiv.symm_apply_eq, he]
      simp
    rw [this, Model.out_mk hF.2.2.1]
  have hfin : (Function.support fun p : (W ⧸ B) × (W' ⧸ B') => φ (p.1.out, p.2.out)).Finite := by
    refine hS.subset ?_
    intro p hp
    refine ⟨_, ⟨(p.1.out, p.2.out), hp, rfl⟩, ?_⟩
    rw [he]; simp
  have h2 : (∑ᶠ c : (W × W') ⧸ B.prod B', φ c.out) =
      ∑ᶠ (a : W ⧸ B) (b : W' ⧸ B'), φ (a.out, b.out) := by
    rw [← finsum_comp_equiv e.symm, finsum_congr h1, finsum_curry _ hfin]
  rw [h2]
  simp only [div_eq_mul_inv]
  rw [← finsum_mul]
  push_cast
  rw [mul_inv]
  ring

end GlobalTheory.IdxInt.Fubini
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralProdFubiniStatement

section

@[expose] public section

open GlobalTheory.IdxInt
open scoped Pointwise Classical

theorem _root_.GlobalTheory.T.indexMeasureIntegral_prod_fubini : ∀ {W : Type} [AddCommGroup W] {W' : Type} [AddCommGroup W'] (A : AddSubgroup W) (A' : AddSubgroup W') (φ : W × W' → ℂ), Nice (A.prod A') φ → (∀ w, Nice A' (fun w' => φ (w, w'))) ∧ Nice A (fun w => cint A' (fun w' => φ (w, w'))) ∧ cint (A.prod A') φ = cint A (fun w => cint A' (fun w' => φ (w, w'))) := by
  first | exact @GlobalTheory.IdxInt.Fubini.cint_prod | exact GlobalTheory.IdxInt.Fubini.cint_prod | (intros; apply GlobalTheory.IdxInt.Fubini.cint_prod <;> assumption)
end
end
