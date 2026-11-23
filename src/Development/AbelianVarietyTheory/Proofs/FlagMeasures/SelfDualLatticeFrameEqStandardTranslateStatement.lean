module

public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDualFamilyInSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsInnerLatticeImageFrameQuotientStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryFrameDualStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTotallyIsotropicDualFamilyInLattice

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.IsotropicDual

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
  [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type}
  [AddCommGroup V] [Module E V] (H : HermSp M V)

theorem h_sum_left {ι : Type} (s : Finset ι) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)
  exact map_sum φ v s

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm y x, ← H.h_herm y' x]

theorem h_smul_right (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem h_sum_right {ι : Type} (s : Finset ι) (x : V) (v : ι → V) :
    H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by

  rw [H.h_herm (∑ i ∈ s, v i) x, h_sum_left, map_sum]
  exact Finset.sum_congr rfl fun i _ => (H.h_herm (v i) x).symm

end Herm

theorem isotropic_dual : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∀ y : Fin r → V, (∀ a, y a ∈ Λ) → (∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0) → ∃ y' : Fin r → V, (∀ a, y' a ∈ Λ) ∧ (∀ a b, H.h (y' a) (Fr.f b) = if b = a.castSucc then 1 else 0) ∧ ∀ a b, H.h (y' a) (y' b) = 0 := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hSD hFr y hy hyf
  letI := hM.loc
  haveI := hM.char0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨htr, -, -, -, hmem, -⟩ := GlobalTheory.UnramOrder.order_facts M.L ϖ hϖ
  have hint : ∀ a b, H.h (y a) (y b) ∈ M.L.O := fun a b => (hSD.2.2 (y a)).1 (hy a) (y b) (hy b)
  have hdiag : ∀ a, ∃ x ∈ M.L.O, x + M.L.cj x = -H.h (y a) (y a) := by
    intro a
    obtain ⟨c, hc⟩ := (M.L.cj_fix (H.h (y a) (y a))).1 (H.h_herm (y a) (y a)).symm
    have hc' : c ∈ 𝒪[F] := (hmem c).1 (hc ▸ hint a a)
    obtain ⟨x, hx, hxe⟩ := htr (-⟨c, hc'⟩)
    refine ⟨x, hx, ?_⟩
    rw [hxe, ← hc]
    simp
  choose x hxO hxe using hdiag
  obtain ⟨m, hmO, hm⟩ : ∃ m : Fin r → Fin r → E, (∀ a k, m a k ∈ M.L.O) ∧
      ∀ a b, m a b + M.L.cj (m b a) = -H.h (y a) (y b) := by
    refine ⟨fun a k => if a < k then -H.h (y a) (y k) else if a = k then x a else 0, ?_, ?_⟩
    · intro a k
      dsimp only
      split_ifs
      · exact M.L.O.neg_mem (hint a k)
      · exact hxO a
      · exact M.L.O.zero_mem
    · intro a b
      dsimp only
      rcases lt_trichotomy a b with h | rfl | h
      · rw [if_pos h, if_neg (not_lt.2 h.le), if_neg h.ne', map_zero, add_zero]
      · rw [if_neg (lt_irrefl a), if_pos rfl]
        exact hxe a
      · rw [if_neg (not_lt.2 h.le), if_neg h.ne', if_pos h, map_neg, ← H.h_herm (y b) (y a),
          zero_add]
  have he : ∀ k : Fin r, Fr.f k.castSucc ∈ Λ := fun k => hFr.1.1 k.castSucc
  have hEf : ∀ (k : Fin r) b, H.h (Fr.f k.castSucc) (Fr.f b) = 0 := fun k b =>
    hFr.2.1 _ _ (Or.inl (Fin.castSucc_lt_last k).ne)
  have hyE : ∀ a k : Fin r, H.h (y a) (Fr.f k.castSucc) = if k = a then 1 else 0 := by
    intro a k
    rw [hyf a k.castSucc]
    simp only [Fin.castSucc_inj]
  have hEy : ∀ k b : Fin r, H.h (Fr.f k.castSucc) (y b) = if k = b then 1 else 0 := by
    intro k b
    rw [H.h_herm (y b) (Fr.f k.castSucc), hyE]
    split_ifs <;> simp
  refine ⟨fun a => y a + ∑ k, m a k • Fr.f k.castSucc, fun a => ?_, fun a b => ?_, fun a b => ?_⟩
  · refine Λ.add_mem (hy a) (Λ.sum_mem fun k _ => ?_)
    exact Λ.smul_mem ⟨m a k, hmO a k⟩ (he k)
  · simp only [H.h_add_left, h_sum_left, H.h_smul_left, hEf, mul_zero, Finset.sum_const_zero,
      add_zero, hyf]
  · simp only [H.h_add_left, h_add_right, h_sum_left, h_sum_right, H.h_smul_left, h_smul_right,
      hyE, hEy, hEf, mul_zero, mul_ite, mul_one, Finset.sum_const_zero, add_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linear_combination hm a b

end GlobalTheory.IsotropicDual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTotallyIsotropicDualFamilyInLatticeStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.exists_totallyIsotropic_dual_family_in_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∀ y : Fin r → V, (∀ a, y a ∈ Λ) → (∀ a b, H.h (y a) (Fr.f b) = if b = a.castSucc then 1 else 0) → ∃ y' : Fin r → V, (∀ a, y' a ∈ Λ) ∧ (∀ a b, H.h (y' a) (Fr.f b) = if b = a.castSucc then 1 else 0) ∧ ∀ a b, H.h (y' a) (y' b) = 0 := by
  first | exact @GlobalTheory.IsotropicDual.isotropic_dual | exact GlobalTheory.IsotropicDual.isotropic_dual | (intros; apply GlobalTheory.IsotropicDual.isotropic_dual <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryImageStandardLatticeEqSelfDualLattice

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

noncomputable section

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

def gen (Fr : FrameD H r) (L : Submodule M.L.O (H.Wb Fr.f)) : Set V :=
  {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
    ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L}

lemma cj_mem' {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := GlobalTheory.UnramOrder.cj_mem M.L hx

lemma smul_mem_lat (Λ : Submodule M.L.O V) {c : E} (hc : c ∈ M.L.O) {w : V} (hw : w ∈ Λ) :
    c • w ∈ Λ := Λ.smul_mem (⟨c, hc⟩ : M.L.O) hw

lemma h_prF_left (Fr : FrameD H r) (p s : V) (h1 : ∀ a, H.h p (Fr.e a) = 0)
    (h2 : ∀ a, H.h p (Fr.es a) = 0) : H.h (Fr.prF s) p = H.h s p := by
  rw [← hl_apply, ← hl_apply]

  simp only [FrameD.prF, map_sub, map_sum, map_smul, hl_apply, h_swap_zero (h1 _),
  h_swap_zero (h2 _)]
  simp

lemma decomp (Fr : FrameD H r) (v s : V) : H.h v s = H.h (Fr.prF v) s +
    ∑ a, H.h v (Fr.es a) * H.h (Fr.e a) s + ∑ a, H.h v (Fr.e a) * H.h (Fr.es a) s := by
  rw [← hl_apply, ← hl_apply]

  simp only [FrameD.prF, map_sub, map_sum, map_smul, hl_apply, smul_eq_mul]
  ring

end GlobalTheory.StdLatImg

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

lemma memL_iff (Fr : FrameD H r) (Λ : Submodule M.L.O V) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f) (w : ↥(H.perp (H.X Fr.f))) :
    H.mkW Fr.f w ∈ L ↔ ∃ x : ↥(H.perp (H.X Fr.f)), (x : V) ∈ Λ ∧ (x : V) - w ∈ H.X Fr.f := by
  rw [← SetLike.mem_coe, hL]
  constructor
  · rintro ⟨x, hx, he⟩; exact ⟨x, hx, (mkW_eq Fr x w).1 he⟩
  · rintro ⟨x, hx, he⟩; exact ⟨x, hx, (mkW_eq Fr x w).2 he⟩

lemma symm_mem_gen (Fr : FrameD H r) (Λ : Submodule M.L.O V) (hSD : H.IsSelfDual Λ)
    (he : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ) (L : Submodule M.L.O (H.Wb Fr.f))
    (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f) (n : V ≃ₗ[E] V) (hn : IsUnitary H n)
    (hfix : ∀ a : Fin r, n (Fr.f a.castSucc) = Fr.f a.castSucc) (hes : ∀ a, n (Fr.es a) ∈ Λ)
    (hX : ∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f) {u : V} (hu : u ∈ Λ) :
    n.symm u ∈ gen Fr L := by
  set v := n.symm u with hv
  have hnv : n v = u := by simp [hv]
  have hve : ∀ a, H.h v (Fr.e a) = H.h u (Fr.e a) := fun a => by
    rw [← hn v (Fr.e a), hnv]; exact congrArg _ (hfix a)
  have hveO : ∀ a, H.h v (Fr.e a) ∈ M.L.O := fun a => by
    rw [hve]; exact (hSD.2.2 u).1 hu _ (he a)
  have hvesO : ∀ a, H.h v (Fr.es a) ∈ M.L.O := fun a => by
    rw [← hn v (Fr.es a), hnv]; exact (hSD.2.2 u).1 hu _ (hes a)
  refine ⟨hvesO, hveO, ⟨Fr.prF v, prF_perp Fr v⟩, rfl, ?_⟩
  set v' := v - ∑ a, H.h v (Fr.e a) • Fr.es a with hv'
  have hv'p : v' ∈ H.perp (H.X Fr.f) := by
    rw [mem_perpX]
    intro b
    rw [← hl_apply]

    simp only [hv', map_sub, map_sum, map_smul, hl_apply, h_es_e, smul_eq_mul]
    simp
  have hx : n v' = u - ∑ a, H.h v (Fr.e a) • n (Fr.es a) := by

    simp [hv', map_sub, map_sum, hnv]
  have hxΛ : n v' ∈ Λ := by
    rw [hx]
    exact Λ.sub_mem hu (Λ.sum_mem fun a _ => smul_mem_lat Λ (hveO a) (hes a))
  have hxv' := hX v' hv'p
  have hxp : n v' ∈ H.perp (H.X Fr.f) := by
    have := (H.perp (H.X Fr.f)).add_mem hv'p (X_le_perp Fr hxv')
    simpa using this
  rw [memL_iff Fr Λ L hL]
  refine ⟨⟨n v', hxp⟩, hxΛ, ?_⟩
  have hpr : Fr.prF v - v' = -∑ a, H.h v (Fr.es a) • Fr.e a := by
    simp only [FrameD.prF, hv']; abel
  have : (n v' : V) - Fr.prF v = (n v' - v') - (Fr.prF v - v') := by abel
  show n v' - Fr.prF v ∈ H.X Fr.f
  rw [this, hpr]
  exact (H.X Fr.f).sub_mem hxv' ((H.X Fr.f).neg_mem
    ((H.X Fr.f).sum_mem fun a _ => (H.X Fr.f).smul_mem _ (e_mem_X Fr a)))

end GlobalTheory.StdLatImg

namespace GlobalTheory.StdLatImg

open GlobalTheory.HL.CoordInnerSnd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}

lemma h_gen_mem (Fr : FrameD H r) (Λ : Submodule M.L.O V) (hSD : H.IsSelfDual Λ)
    (L : Submodule M.L.O (H.Wb Fr.f)) (hL : (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f)
    {v s : V} (hv : v ∈ gen Fr L) (hs : s ∈ gen Fr L) : H.h v s ∈ M.L.O := by
  obtain ⟨hv1, hv2, wv, hwv, hwvL⟩ := hv
  obtain ⟨hs1, hs2, ws, hws, hwsL⟩ := hs
  obtain ⟨x, hxΛ, hxd⟩ := (memL_iff Fr Λ L hL wv).1 hwvL
  obtain ⟨x', hx'Λ, hx'd⟩ := (memL_iff Fr Λ L hL ws).1 hwsL
  rw [hwv] at hxd
  rw [hws] at hx'd

  have hpp : H.h (Fr.prF v) (Fr.prF s) = H.h (x : V) (x' : V) := by
    have e1 : Fr.prF v = x - ((x : V) - Fr.prF v) := by abel
    have e2 : Fr.prF s = x' - ((x' : V) - Fr.prF s) := by abel
    have k1 : H.h ((x : V) - Fr.prF v) (Fr.prF s) = 0 :=
      h_swap_zero (prF_perp Fr s _ hxd)
    have k2 : H.h (x : V) ((x' : V) - Fr.prF s) = 0 := x.2 _ hx'd
    calc H.h (Fr.prF v) (Fr.prF s)
        = H.h (x : V) (Fr.prF s) - H.h ((x : V) - Fr.prF v) (Fr.prF s) := by
          rw [← hl_apply, ← hl_apply, ← hl_apply, ← map_sub, ← e1]
      _ = H.h (x : V) (Fr.prF s) := by rw [k1, sub_zero]
      _ = H.h (x : V) (x' : V) := by
          rw [e2, ← neg_add_eq_sub, h_add_right, ← neg_one_smul E ((x' : V) - Fr.prF s),
            h_smul_right, k2, mul_zero, zero_add]
  have hpO : H.h (Fr.prF v) s ∈ M.L.O := by
    have e3 : H.h (Fr.prF v) s = M.L.cj (H.h s (Fr.prF v)) := H.h_herm _ _
    rw [e3, ← h_prF_left Fr (Fr.prF v) s (h_prF_e Fr v) (h_prF_es Fr v), H.h_herm, M.L.cj_cj, hpp]
    exact (hSD.2.2 x).1 hxΛ _ hx'Λ
  rw [decomp Fr v s]
  refine M.L.O.add_mem (M.L.O.add_mem hpO ?_) ?_
  · refine M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hv1 a) ?_
    rw [H.h_herm]; exact cj_mem' (hs2 a)
  · refine M.L.O.sum_mem fun a _ => M.L.O.mul_mem (hv2 a) ?_
    rw [H.h_herm]; exact cj_mem' (hs1 a)

theorem eq_img_lamStd : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → (∀ a : Fin r, Fr.f a.castSucc ∈ Λ) → ∀ L : Submodule M.L.O (H.Wb Fr.f), (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f → ∀ n : V ≃ₗ[E] V, IsUnitary H n → (∀ a : Fin r, n (Fr.f a.castSucc) = Fr.f a.castSucc) → (∀ a, n (Fr.es a) ∈ Λ) → (∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f) → Λ = img n (Fr.LamStd L) := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr Λ hSD he L hL n hn hfix hes hX
  have hb := fun {u : V} (hu : u ∈ Λ) => symm_mem_gen Fr Λ hSD he L hL n hn hfix hes hX hu
  have hgen : FrameD.LamStd Fr L = Submodule.span M.L.O (gen Fr L) := rfl
  apply le_antisymm
  · intro u hu
    rw [hgen]
    exact ⟨n.symm u, Submodule.subset_span (hb hu), by simp⟩
  · rw [hgen, img, Submodule.map_le_iff_le_comap, Submodule.span_le]
    intro s hs
    show n s ∈ Λ
    refine (hSD.2.2 (n s)).2 fun t ht => ?_
    have ht' : n (n.symm t) = t := by simp
    rw [← ht', hn]
    exact h_gen_mem Fr Λ hSD L hL hs (hb ht)

end GlobalTheory.StdLatImg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryImageStandardLatticeEqSelfDualLatticeStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.unitary_image_standardLattice_eq_selfDual_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → (∀ a : Fin r, Fr.f a.castSucc ∈ Λ) → ∀ L : Submodule M.L.O (H.Wb Fr.f), (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f → ∀ n : V ≃ₗ[E] V, IsUnitary H n → (∀ a : Fin r, n (Fr.f a.castSucc) = Fr.f a.castSucc) → (∀ a, n (Fr.es a) ∈ Λ) → (∀ v ∈ H.perp (H.X Fr.f), n v - v ∈ H.X Fr.f) → Λ = img n (Fr.LamStd L) := by
  first | exact @GlobalTheory.StdLatImg.eq_img_lamStd | exact GlobalTheory.StdLatImg.eq_img_lamStd | (intros; apply GlobalTheory.StdLatImg.eq_img_lamStd <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeFrameEqStandardTranslate

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

namespace GlobalTheory.StdLat

theorem eq_img_lamStd : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧ (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f ∧ ∃ n ∈ Fr.N, (∀ b, n (Fr.f b) = Fr.f b) ∧ Λ = img n (Fr.LamStd L) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r Fr Λ hSD hFr
  obtain ⟨y, hyΛ, hyf⟩ := GlobalTheory.T.exists_dual_family_in_selfDual_lattice M hM H r Fr Λ hSD hFr
  have hy0 : ∀ (a : Fin r) (b : Fin (r + 1)), H.h (y a.castSucc) (Fr.f b) = if b = a.castSucc then 1 else 0 :=
    fun a b => hyf b a.castSucc
  obtain ⟨y', hy'Λ, hy'f, hy'y⟩ := GlobalTheory.T.exists_totallyIsotropic_dual_family_in_lattice M hM H r Fr Λ hSD hFr (fun a : Fin r => y a.castSucc) (fun a : Fin r => hyΛ _) hy0
  obtain ⟨n, hnU, hnf, hnes, hnX⟩ := GlobalTheory.T.exists_unitary_frame_dual' M H r Fr y' hy'f hy'y
  obtain ⟨L, hLset, hLin⟩ := GlobalTheory.T.exists_innerLattice_image_frame_quotient M hM H r Fr Λ hSD hFr y' hy'Λ hy'f
  have heΛ : ∀ a : Fin r, Fr.f a.castSucc ∈ Λ := fun a => hFr.1.1 _
  refine ⟨L, hLin, hLset, n, ?_, hnf, ?_⟩
  · apply Subgroup.subset_closure
    refine ⟨hnU, ?_, hnX⟩
    intro j _ v hv
    have hle : Fr.Fj j ≤ LinearMap.ker ((n : V →ₗ[E] V) - LinearMap.id) := by
      rw [FrameD.Fj, Submodule.span_le]
      rintro _ ⟨a, _, rfl⟩
      simp [FrameD.e, hnf]
    have h1 := hle hv
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply] at h1
    rw [show n v - v = 0 from h1]
    exact zero_mem _
  · exact GlobalTheory.T.unitary_image_standardLattice_eq_selfDual_lattice M H r Fr Λ hSD heΛ L hLset n hnU (fun a => hnf _) (fun a => by rw [hnes]; exact hy'Λ a) hnX

end GlobalTheory.StdLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeFrameEqStandardTranslateStatement

section

@[expose] public section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.selfDual_lattice_frame_eq_standard_translate : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧ (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f ∧ ∃ n ∈ Fr.N, (∀ b, n (Fr.f b) = Fr.f b) ∧ Λ = img n (Fr.LamStd L) := by
  first | exact @GlobalTheory.StdLat.eq_img_lamStd | exact GlobalTheory.StdLat.eq_img_lamStd | (intros; apply GlobalTheory.StdLat.eq_img_lamStd <;> assumption)
end
end
