module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PiBelow
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PieceTop
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.PiRatio
public import Mathlib.LinearAlgebra.Matrix.Rank
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.TypeStar
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.IdemNilZero
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.RankPosOfNe

section

@[expose] public section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open Matrix

variable {k : Type} [Field k] {N : ℕ}

theorem rank_add_orth {a b : Matrix (Fin N) (Fin N) k} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
    (hab : a * b = 0) (hba : b * a = 0) : (a + b).rank = a.rank + b.rank := by
  have hsup : LinearMap.range (a + b).mulVecLin = LinearMap.range a.mulVecLin ⊔ LinearMap.range b.mulVecLin := by
    apply le_antisymm
    · rintro _ ⟨v, rfl⟩
      simp only [Matrix.mulVecLin_apply, Matrix.add_mulVec]
      exact Submodule.add_mem_sup ⟨v, rfl⟩ ⟨v, rfl⟩
    · refine sup_le ?_ ?_
      · rintro _ ⟨v, rfl⟩
        refine ⟨a *ᵥ v, ?_⟩
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, ha.eq, hba, add_zero]
      · rintro _ ⟨v, rfl⟩
        refine ⟨b *ᵥ v, ?_⟩
        simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, add_mul, hb.eq, hab, zero_add]
  have hinf : LinearMap.range a.mulVecLin ⊓ LinearMap.range b.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    rintro w ⟨⟨u, rfl⟩, ⟨v, hv⟩⟩
    simp only [Matrix.mulVecLin_apply] at hv ⊢
    have h1 : a *ᵥ (a *ᵥ u) = a *ᵥ u := by rw [Matrix.mulVec_mulVec, ha.eq]
    have h2 : a *ᵥ (b *ᵥ v) = 0 := by rw [Matrix.mulVec_mulVec, hab, Matrix.zero_mulVec]
    rw [← hv, h2] at h1
    rw [Submodule.mem_bot, ← hv, ← h1]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range a.mulVecLin) (LinearMap.range b.mulVecLin)
  rw [hinf, finrank_bot, add_zero, ← hsup] at h
  simpa only [Matrix.finrank_range_mulVecLin] using h

theorem idem_sum_orth {ι : Type} (s : Finset ι) (e : ι → Matrix (Fin N) (Fin N) k)
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    IsIdempotentElem (∑ i ∈ s, e i) := by
  unfold IsIdempotentElem
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => ho i hi j hj (Ne.symm hji)) (fun h => absurd hi h)]
  exact hid i hi

theorem rank_sum_orth {ι : Type} (s : Finset ι) (e : ι → Matrix (Fin N) (Fin N) k)
    (hid : ∀ i ∈ s, IsIdempotentElem (e i)) (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → e i * e j = 0) :
    (∑ i ∈ s, e i).rank = ∑ i ∈ s, (e i).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hid' : ∀ j ∈ s, IsIdempotentElem (e j) := fun j hj => hid j (Finset.mem_insert_of_mem hj)
    have ho' : ∀ j ∈ s, ∀ l ∈ s, j ≠ l → e j * e l = 0 := fun j hj l hl h =>
      ho j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl) h
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih hid' ho']
    refine rank_add_orth (hid i (Finset.mem_insert_self i s)) (idem_sum_orth s e hid' ho') ?_ ?_
    · rw [Finset.mul_sum]
      exact Finset.sum_eq_zero fun j hj => ho i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
        (fun h => hi (h ▸ hj))
    · rw [Finset.sum_mul]
      exact Finset.sum_eq_zero fun j hj => ho j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i s)
        (fun h => hi (h ▸ hj))

theorem rank_pos_of_ne {e : Matrix (Fin N) (Fin N) k} (h : e ≠ 0) : 0 < e.rank := by
  rw [Nat.pos_iff_ne_zero]
  intro h0
  apply h
  rw [← Matrix.finrank_range_mulVecLin, Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0
  have : Matrix.toLin' e = 0 := h0
  simpa using congrArg LinearMap.toMatrix' this

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.SqSumLe

section

@[expose] public section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

theorem sq_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) : ∑ i ∈ s, m i ^ 2 ≤ (∑ i ∈ s, m i) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    nlinarith [ih, Nat.zero_le (m a * ∑ i ∈ s, m i)]

theorem sq_sum_lt {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ) (hm : ∀ i ∈ s, 1 ≤ m i) (h : 1 < s.card) :
    ∑ i ∈ s, m i ^ 2 < (∑ i ∈ s, m i) ^ 2 := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < s.card by omega)
  have hne : (s.erase a).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, hb⟩ := hne
  have hM : 1 ≤ ∑ i ∈ s.erase a, m i :=
    (hm b (Finset.mem_of_mem_erase hb)).trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hb)
  have ih := sq_sum_le (s.erase a) m
  rw [← Finset.add_sum_erase s _ ha, ← Finset.add_sum_erase s _ ha]
  have := hm a ha
  nlinarith

theorem num_fib {ι : Type*} [DecidableEq ι] (s : Finset ι) (m dE : ι → ℕ) (n dF : ℕ) (hdF : 0 < dF)
    (hm : ∀ i ∈ s, 1 ≤ m i) (hd : ∀ i ∈ s, dF ≤ dE i) (hsum : n * dF = ∑ i ∈ s, m i * dE i) :
    ∑ i ∈ s, m i ^ 2 ≤ n ^ 2 ∧ (∑ i ∈ s, m i ^ 2 = n ^ 2 → s.Nonempty → ∀ i ∈ s, s = {i} ∧ dE i ≤ dF) := by
  have hMn : ∑ i ∈ s, m i ≤ n := by
    have : (∑ i ∈ s, m i) * dF ≤ n * dF := by
      rw [hsum, Finset.sum_mul]
      exact Finset.sum_le_sum fun i hi => Nat.mul_le_mul_left _ (hd i hi)
    exact Nat.le_of_mul_le_mul_right this hdF
  have h1 := sq_sum_le s m
  have h2 : (∑ i ∈ s, m i) ^ 2 ≤ n ^ 2 := Nat.pow_le_pow_left hMn 2
  refine ⟨h1.trans h2, fun heq hne i hi => ?_⟩
  have hcard : s.card = 1 := by
    by_contra hc
    have := sq_sum_lt s m hm (by have := hne.card_pos; omega)
    omega
  obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hcard
  rw [Finset.mem_singleton] at hi; subst hi
  refine ⟨rfl, ?_⟩
  simp only [Finset.sum_singleton] at heq hsum
  have hn : m i = n := by
    have := (Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0)) heq
    exact this
  rw [← hn] at hsum
  have := hm i (Finset.mem_singleton_self i)
  have : dF = dE i := Nat.eq_of_mul_eq_mul_left (by omega) hsum
  omega

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.TefFinrank

section

@[expose] public section

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece Module

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
  {e f : Matrix (Fin N) (Fin N) k} (he : e ∈ primIdem (Sx D x)) (hf : f ∈ primIdem Z) (hef : e * f = e)
include hZ hx hχ he hf hef

theorem tef_nil {w : Matrix (Fin N) (Fin N) k} (hw : w ∈ Tef (Z := Z) e f) (hn : IsNilpotent w) : w = 0 := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  simp only [LinearMap.mulLeft_apply] at hn ⊢
  rw [tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz hn, mul_zero]

theorem tef_finrank : finrank k (Tef (Z := Z) e f) = finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f)) := by
  have hinj : Function.Injective ((LinearMap.mulLeft k e).comp
      (Submodule.subtype (Z.toSubmodule.map (LinearMap.mulLeft k f)))) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨y, hy⟩ h0
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.mulLeft_apply] at h0
    have hfz := tef_zero hZ hx he.2.1 he.2.2.1 hf hef (sx_le D he.1) hz (by rw [h0]; exact IsNilpotent.zero)
    apply Subtype.ext
    simpa using hfz
  have h := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  exact h

theorem tef_inf : Tef (Z := Z) e f ⊓ Nx D x = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [Submodule.mem_bot]
  exact tef_nil D hZ hx hχ he hf hef hw.1 (nx_nil D hZ hx hχ w hw.2)

theorem tef_le : Tef (Z := Z) e f ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨s, hs, n, hn, rfl⟩ := Submodule.mem_sup.1 (z_le D hZ hx hχ hz)
  simp only [LinearMap.mulLeft_apply]
  have hfS : f ∈ Sx D x := pz_mem_S D hZ hx hχ hf
  have hfC : f ∈ Cx Z x := z_le_cx hf.1
  have heC : e ∈ Cx Z x := sx_le D he.1
  have hs' : s ∈ Sx D x := (Subalgebra.mem_toSubmodule _).1 hs
  rw [mul_add, mul_add]
  refine Submodule.add_mem_sup (Submodule.mem_map.2 ⟨f * s, (Subalgebra.mem_toSubmodule _).2 ((Sx D x).mul_mem hfS hs'), rfl⟩) ?_
  rw [← mul_assoc]
  exact nx_mul D hZ hx (e * f) ((Cx Z x).mul_mem heC hfC) n hn

theorem dim_le : finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f)) ≤
    finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) := by
  rw [← tef_finrank D hZ hx hχ he hf hef]
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)
  rw [tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero] at h1
  have h2 : Tef (Z := Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x :=
    sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right
  have h3 := Submodule.finrank_mono h2
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)
  omega

theorem dim_eq_le (hd : finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) ≤
    finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f))) :
    (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ≤ Tef (Z := Z) e f ⊔ Nx D x := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (Tef (Z := Z) e f) (Nx D x)
  rw [tef_inf D hZ hx hχ he hf hef, finrank_bot, add_zero, tef_finrank D hZ hx hχ he hf hef] at h1
  have h2 : Tef (Z := Z) e f ⊔ Nx D x ≤ (Sx D x).toSubmodule.map (LinearMap.mulLeft k e) ⊔ Nx D x :=
    sup_le (tef_le D hZ hx hχ he hf hef) le_sup_right
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    ((Sx D x).toSubmodule.map (LinearMap.mulLeft k e)) (Nx D x)
  have h5 := Submodule.eq_of_le_of_finrank_le h2 (by omega)
  rw [h5]
  exact le_sup_left

end

section
variable {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
  {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0)
include hZ hx hχ

theorem zn_of_eq (h : ∀ f ∈ primIdem Z, f ∈ primIdem (Sx D x) ∧
      finrank k ((Sx D x).toSubmodule.map (LinearMap.mulLeft k f)) ≤ finrank k (Z.toSubmodule.map (LinearMap.mulLeft k f))) :
    ∃ c ∈ Z, IsNilpotent (x - c) := by
  have hfin := pi_fin hZ
  have hS : (Sx D x).toSubmodule ≤ Z.toSubmodule ⊔ Nx D x := by
    intro s hs
    have hsum : s = ∑ f ∈ hfin.toFinset, f * s := by
      rw [← Finset.sum_mul, pi_sum hZ, one_mul]
    rw [hsum]
    refine Submodule.sum_mem _ (fun f hf => ?_)
    rw [Set.Finite.mem_toFinset] at hf
    obtain ⟨hfS, hd⟩ := h f hf
    have hle := dim_eq_le D hZ hx hχ hfS hf hfS.2.1.eq hd
    have hmem : f * s ∈ (Sx D x).toSubmodule.map (LinearMap.mulLeft k f) :=
      Submodule.mem_map.2 ⟨s, hs, rfl⟩
    have hT : Tef (Z := Z) f f ≤ Z.toSubmodule ⊔ Nx D x := by
      intro w hw
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hw
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hy
      apply Submodule.mem_sup_left
      simp only [LinearMap.mulLeft_apply]
      exact (Subalgebra.mem_toSubmodule _).2 (Z.mul_mem hf.1 (Z.mul_mem hf.1 hz))
    exact (sup_le hT le_sup_right) (hle hmem)
  have hxm : x ∈ Z.toSubmodule ⊔ Nx D x :=
    (sup_le hS le_sup_right : (Sx D x).toSubmodule ⊔ Nx D x ≤ _) (x_mem D hZ hx hχ)
  obtain ⟨c, hc, n, hn, hcn⟩ := Submodule.mem_sup.1 hxm
  refine ⟨c, hc, ?_⟩
  rw [← hcn, add_sub_cancel_left]
  exact nx_nil D hZ hx hχ n hn

end

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.RatioOf

section

@[expose] public section

noncomputable section

open Matrix Polynomial

namespace PositivityTheory.RgUd.TP.Desc.Piece.PDich

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}

open PositivityTheory.RgUd.TP.Desc.Piece Module

abbrev dA (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (e : Matrix (Fin N) (Fin N) k) : ℕ :=
  finrank k (A.toSubmodule.map (LinearMap.mulLeft k e))

theorem ratio_of (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) {e : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) :
    0 < dA A e ∧ dA A e ∣ e.rank ∧
      finrank k ((cenSub A).map (LinearMap.mulLeft k e)) / dA A e = (e.rank / dA A e) ^ 2 := by
  obtain ⟨h0, hd, h⟩ := pi_ratio hA.1 he.1 he.2.1 he.2.2.1 (fun a ha => pi_field hA he ha)
  exact ⟨h0, hd, by rw [h, Nat.mul_div_cancel _ h0]⟩

theorem mu_sum (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) :
    mu A = ∑ e ∈ (pi_fin hA).toFinset, (e.rank / dA A e) ^ 2 := by
  unfold mu
  rw [finsum_mem_eq_finite_toFinset_sum _ (pi_fin hA)]
  exact Finset.sum_congr rfl fun e he => (ratio_of A hA ((Set.Finite.mem_toFinset _).mp he)).2.2

theorem m_pos (A : Subalgebra k (Matrix (Fin N) (Fin N) k)) (hA : CR A) {e : Matrix (Fin N) (Fin N) k}
    (he : e ∈ primIdem A) : 1 ≤ e.rank / dA A e := by
  obtain ⟨h0, hd, -⟩ := ratio_of A hA he
  have hr := rank_pos_of_ne he.2.2.1
  obtain ⟨c, hc⟩ := hd
  rw [hc, Nat.mul_div_cancel_left _ h0]
  rcases Nat.eq_zero_or_pos c with rfl | h
  · simp at hc; omega
  · exact h

open Classical in
theorem dich_pt {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q)
    {x : Matrix (Fin N) (Fin N) k} (hZ : CR Z) (hx : x ∈ Bz Z) (hχ : aeval x χ = 0) :
    mu (Sx D x) < mu Z ∨ ∃ c ∈ Z, IsNilpotent (x - c) := by
  have hS := sx_cr D hZ hx hχ
  set P := (pi_fin hS).toFinset with hP
  set Q := (pi_fin hZ).toFinset with hQ
  have mP : ∀ {e}, e ∈ P ↔ e ∈ primIdem (Sx D x) := fun {e} => Set.Finite.mem_toFinset _
  have mQ : ∀ {f}, f ∈ Q ↔ f ∈ primIdem Z := fun {f} => Set.Finite.mem_toFinset _

  have hsplit : mu (Sx D x) = ∑ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 := by
    rw [mu_sum _ hS]
    calc ∑ e ∈ P, (e.rank / dA (Sx D x) e) ^ 2
        = ∑ e ∈ P, ∑ f ∈ Q, if e * f = e then (e.rank / dA (Sx D x) e) ^ 2 else 0 := by
          refine Finset.sum_congr rfl fun e he => ?_
          obtain ⟨f₀, hf₀, hef₀⟩ := ef_exists D hZ hx hχ (mP.mp he)
          rw [Finset.sum_eq_single_of_mem f₀ (mQ.mpr hf₀) fun f hf hne => if_neg fun h =>
            hne (ef_unique D hZ hx hχ (mP.mp he) (mQ.mp hf) hf₀ h hef₀), if_pos hef₀]
      _ = ∑ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 := by
          rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun f _ => (Finset.sum_filter _ _).symm

  have hfib : ∀ f ∈ Q, ∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 ≤ (f.rank / dA Z f) ^ 2 ∧
      (∑ e ∈ P with e * f = e, (e.rank / dA (Sx D x) e) ^ 2 = (f.rank / dA Z f) ^ 2 →
        f ∈ primIdem (Sx D x) ∧ dA (Sx D x) f ≤ dA Z f) := by
    intro f hf
    have hf' := mQ.mp hf
    have hmem : ∀ e ∈ P.filter (fun e => e * f = e), e ∈ primIdem (Sx D x) ∧ e * f = e := fun e he =>
      ⟨mP.mp (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
    have hfs := fib_sum D hZ hx hχ hf'
    obtain ⟨hdF, hdvF, -⟩ := ratio_of Z hZ hf'
    have hsum : f.rank / dA Z f * dA Z f =
        ∑ e ∈ P with e * f = e, e.rank / dA (Sx D x) e * dA (Sx D x) e := by
      rw [Nat.div_mul_cancel hdvF]
      conv_lhs => rw [← hfs]
      rw [rank_sum_orth _ _ (fun e he => (hmem e he).1.2.1)
        (fun e he e' he' hne => pi_orth hS (hmem e he).1 (hmem e' he').1 hne)]
      exact Finset.sum_congr rfl fun e he => (Nat.div_mul_cancel (ratio_of _ hS (hmem e he).1).2.1).symm
    obtain ⟨hle, heq⟩ := num_fib (P.filter (fun e => e * f = e)) (fun e => e.rank / dA (Sx D x) e)
      (fun e => dA (Sx D x) e) (f.rank / dA Z f) (dA Z f) hdF (fun e he => m_pos _ hS (hmem e he).1)
      (fun e he => dim_le D hZ hx hχ (hmem e he).1 hf' (hmem e he).2) hsum
    refine ⟨hle, fun h => ?_⟩
    have hne : (P.filter (fun e => e * f = e)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.sum_empty] at hfs
      exact hf'.2.2.1 hfs.symm
    obtain ⟨e, he⟩ := hne
    obtain ⟨hsing, hde⟩ := heq h ⟨e, he⟩ e he
    have hef : e = f := by rw [← hfs, hsing, Finset.sum_singleton]
    subst hef
    exact ⟨(hmem e he).1, hde⟩

  have hle : mu (Sx D x) ≤ mu Z := by
    rw [hsplit, mu_sum _ hZ]
    exact Finset.sum_le_sum fun f hf => (hfib f hf).1
  by_cases hlt : mu (Sx D x) < mu Z
  · exact Or.inl hlt
  right
  have heq : mu (Sx D x) = mu Z := le_antisymm hle (not_lt.mp hlt)
  rw [hsplit, mu_sum _ hZ] at heq
  have hall := (Finset.sum_eq_sum_iff_of_le fun f hf => (hfib f hf).1).mp heq
  exact zn_of_eq D hZ hx hχ fun f hf => (hfib f (mQ.mpr hf)).2 (hall f (mQ.mpr hf))

variable (k) in
theorem dich : PositivityTheory.RgUd.TP.Desc.Piece.Dich k := by
  intro N q Z hZ χ D τ x₀ hx₀
  exact dich_pt D hZ hx₀.1 hx₀.2.1

end PositivityTheory.RgUd.TP.Desc.Piece.PDich
end
end
end
