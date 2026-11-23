module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieValL
public import Formalism.LocalToGlobal.CharacterGerms.GeneralGermZero
import Formalism.LocalToGlobal.CharacterGerms.AbstractGermZeroCondition
import Formalism.LocalToGlobal.CharacterGerms.CoeffSingleSubstOfLowDegree
import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd
public import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsDef
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf
import Formalism.LocalToGlobal.CharacterGerms.EndomorphismLimitIntegral
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyEig2
import Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallMain
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLieSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTieValK
public import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsU
public import Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsE

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTieP_TCoord

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds
namespace TCoord

open Formalism.IncomingBounds FormalGermZero GeneralGermZero

variable {C : Type} [Field C] {κ : Type} [Fintype κ]

theorem tcoord_abs {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ) (g : Fin 2)
    (w : κ → I g → C) (hwI : ∀ x c, V.Ge 0 (w x c))
    (hw : ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (tan : I g → I g → C) (hun : V.v (Matrix.of tan).det = 0)
    (P : κ → MvPowerSeries (I g) C) (hP0 : ∀ j, MvPowerSeries.constantCoeff (P j) = 0) (hPI : ∀ j, IntS V (P j))
    (hPlin : ∀ j c, MvPowerSeries.coeff (Finsupp.single c 1) (P j) = ∑ c', X.u g c' j * tan c c')
    (t : I g → MvPowerSeries (I g) C) (ht0 : ∀ c, MvPowerSeries.constantCoeff (t c) = 0)
    (hPt : ∀ j, MvPowerSeries.subst t (P j) =
      MvPowerSeries.subst (fun i => ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) (X.ex j))
    (c : I g) :
    ∃ T : MvPowerSeries κ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst (fun x => X.expPt g x) T = upG g (t c) := by

  set E : κ → MvPowerSeries (I g) C := fun j =>
    MvPowerSeries.subst (fun i => ∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) (X.ex j) with hE
  have hE0 : ∀ j, MvPowerSeries.constantCoeff (E j) = 0 := fun j => by
    rw [hE]; simp only; rw [← hPt j]; exact constantCoeff_subst_zero ht0 (hP0 j)
  have hlin0 : ∀ i : κ, MvPowerSeries.constantCoeff
      (∑ c', X.u g c' i • (MvPowerSeries.X c' : MvPowerSeries (I g) C)) = 0 := fun i => by

    rw [map_sum]
    exact Finset.sum_eq_zero fun c' _ => by
      rw [MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_X, smul_zero]
  have hXg : MvPowerSeries.HasSubst
      (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun x => MvPowerSeries.constantCoeff_X _
  have hupE : ∀ j, X.expPt g j = upG g (E j) := by
    intro j
    show _ = MvPowerSeries.subst (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C)) (E j)
    rw [hE]
    simp only
    rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hlin0) hXg]
    unfold RawChart.expPt
    congr 1
    funext i

    rw [← MvPowerSeries.coe_substAlgHom hXg, map_sum]
    simp only [map_smul, MvPowerSeries.coe_substAlgHom hXg, MvPowerSeries.subst_X hXg]

  set φ : I g → MvPowerSeries (I g) C := fun k => ∑ j, w j k • P j with hφ
  set t₂ : I g → MvPowerSeries (I g) C := fun k => ∑ j, w j k • E j with ht₂
  have hφ0 : ∀ k, MvPowerSeries.constantCoeff (φ k) = 0 := fun k => by

    rw [hφ]; simp only; rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [MvPowerSeries.constantCoeff_smul, hP0 j, smul_zero]
  have ht₂0 : ∀ k, MvPowerSeries.constantCoeff (t₂ k) = 0 := fun k => by

    rw [ht₂]; simp only; rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [MvPowerSeries.constantCoeff_smul, hE0 j, smul_zero]
  have hφI : ∀ k, IntS V (φ k) := fun k μ => by

    rw [hφ]; simp only; rw [map_sum]
    exact VF.Ge.sum fun j _ => by rw [MvPowerSeries.coeff_smul]; exact (hwI j k).mul_int (hPI j μ)
  have hL : (Matrix.of fun k c : I g => MvPowerSeries.coeff (Finsupp.single c 1) (φ k)) = (Matrix.of tan).transpose := by
    ext k c
    rw [Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply, hφ]
    simp only

    rw [map_sum]
    simp only [MvPowerSeries.coeff_smul, hPlin]
    have e : ∑ j, w j k * ∑ c', X.u g c' j * tan c c' = ∑ c', tan c c' * ∑ j, X.u g c' j * w j k := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    simp only [hw, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hts := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  have ht₂s := MvPowerSeries.hasSubst_of_constantCoeff_zero ht₂0
  have heq : ∀ k, MvPowerSeries.subst t (φ k) = MvPowerSeries.subst t₂ (MvPowerSeries.X k : MvPowerSeries (I g) C) := by
    intro k
    rw [MvPowerSeries.subst_X ht₂s, hφ, ht₂]
    simp only

    rw [← MvPowerSeries.coe_substAlgHom hts, map_sum]
    simp only [map_smul, MvPowerSeries.coe_substAlgHom hts, hPt]
    rfl
  obtain ⟨h, hh0, hhI, hth⟩ := AbstractGermZero.one_group V t t₂ φ (fun k => MvPowerSeries.X k) ht₂0 ht0 hφ0 hφI
    (by rw [hL, Matrix.det_transpose]; exact hun) (fun k => MvPowerSeries.constantCoeff_X k) (fun k => intS_X k) heq

  set ℓ : I g → MvPowerSeries κ C := fun k => ∑ j, w j k • (MvPowerSeries.X j : MvPowerSeries κ C) with hℓ
  have hℓ0 : ∀ k, MvPowerSeries.constantCoeff (ℓ k) = 0 := fun k => by

    rw [hℓ]; simp only; rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by
      rw [MvPowerSeries.constantCoeff_smul, MvPowerSeries.constantCoeff_X, smul_zero]
  have hℓI : ∀ k, IntS V (ℓ k) := fun k μ => by

    rw [hℓ]; simp only; rw [map_sum]
    exact VF.Ge.sum fun j _ => by rw [MvPowerSeries.coeff_smul]; exact (hwI j k).mul_int (intS_X j μ)
  have hpt0 : ∀ x, MvPowerSeries.constantCoeff (X.expPt g x) = 0 := fun x => by
    rw [hupE x]
    exact constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hE0 x)
  have hpts := MvPowerSeries.hasSubst_of_constantCoeff_zero hpt0
  refine ⟨MvPowerSeries.subst ℓ (h c), IntS.subst hℓ0 hℓI (hhI c), constantCoeff_subst_zero hℓ0 (hh0 c), ?_⟩
  rw [MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hℓ0) hpts, hth c]
  show _ = MvPowerSeries.subst (fun x : I g => (MvPowerSeries.X (⟨g, x⟩ : WV I) : MvPowerSeries (WV I) C))
    (MvPowerSeries.subst t₂ (h c))
  rw [MvPowerSeries.subst_comp_subst_apply ht₂s hXg]
  congr 1
  funext k
  rw [hℓ, ht₂]
  simp only

  rw [← MvPowerSeries.coe_substAlgHom hpts, map_sum, ← MvPowerSeries.coe_substAlgHom hXg, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, map_smul, MvPowerSeries.coe_substAlgHom hpts, MvPowerSeries.subst_X hpts,
    MvPowerSeries.coe_substAlgHom hXg, hupE j]
  rfl

theorem tcoord_gen {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (X : RawChart C d I κ)
    (F : κ → MvPowerSeries (Fin 2 × κ) C) (hF0 : ∀ k, MvPowerSeries.constantCoeff (F k) = 0)
    (hFI : ∀ k, IntS V (F k)) (hadd : LgAdd F X.lg)
    (hlin : ∀ k (μ : κ →₀ ℕ), μ.degree ≤ 1 →
      MvPowerSeries.coeff μ (X.lg k) = MvPowerSeries.coeff μ (MvPowerSeries.X k))
    (hexlg : ∀ k, MvPowerSeries.subst X.lg (X.ex k) = (MvPowerSeries.X k : MvPowerSeries κ C))
    (hsat : ∀ g, ∃ w : κ → I g → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I g, ∑ x, X.u g c x * w x c' = if c = c' then 1 else 0)
    (H : ∀ g, X.CartHyp V g) : RawChart.TCoordSt H := by
  intro S t ht g c
  obtain ⟨w, hwI, hw⟩ := hsat g
  obtain ⟨P, hP0, hPI, hPlin, hPt⟩ := sysK_P X F hF0 hFI hadd hlin hexlg (H g) (S g)
  exact tcoord_abs X g w hwI hw (S g).tan (S g).unimod P hP0 hPI hPlin (t g) (ht g).1 (hPt (t g) (ht g)) c

end TCoord

def TCoordSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => ∀ Hc : ∀ g, X.CartHyp V g, RawChart.TCoordSt Hc

theorem tcoordSelf_holds : TCoordSelfSt := by
  unfold TCoordSelfSt AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p H
  exact TCoord.tcoord_gen (Y.rawSelf p) (SelfConjugateGermZero.lawS Y) (SelfConjugateGermZero.lawS_const Y) (SelfConjugateGermZero.lawS_int Y) (SelfConjugateGermZero.lgS_add Y p)
    (SelfConjugateGermZero.lgS_lin Y p) (SelfConjugateGermZero.exS_lg Y p) (SelfConjugateGermZero.sat_self Y p) H

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsPack

section

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0 RowTiePProj

namespace GmPackP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}

theorem half [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0) (ε : O)
    (hε : ∃ y, ε * ε - ε = (V.l : O) * y) (hε1 : ∀ a, V.MM (p.em a ε - 1))
    (hεx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, ε * x = (V.l : O) * y) (M : ℕ → O) (φ : Pt C 1 dd)
    (hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (φ i)) :
    (∀ a, comp1 φ (Y.B.A.act a) = comp1 (Y.B.A.act a) φ) ∧
      ∀ v : Fin dd → C, ∃ b : I0 → C, linAct φ v = ∑ c, b c • p.e c := by
  have hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0 := const_of_lim Y hT
  have act0 : ∀ x i, MvPowerSeries.constantCoeff (Y.B.A.act x i) = 0 := Y.B.A.const
  refine ⟨?_, ?_⟩
  · intro a
    funext i
    have L := TendsS.comp1 (φ := fun n => Y.B.A.act (M n * ε ^ V.l ^ n)) (b := fun _ => Y.B.A.act a)
      (fun _ => act0 a) (act0 a) hT (fun _ => TendsS.const _) i
    have R := TendsS.comp1 (φ := fun _ => Y.B.A.act a) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n))
      (fun n => act0 _) hφ0 (fun _ => TendsS.const _) hT i
    have eq : (fun n => comp1 (Y.B.A.act (M n * ε ^ V.l ^ n)) (Y.B.A.act a) i) =
        fun n => comp1 (Y.B.A.act a) (Y.B.A.act (M n * ε ^ V.l ^ n)) i := funext fun n => by
      rw [← Y.B.A.mul_act, ← Y.B.A.mul_act, mul_comm]
    rw [eq] at L
    exact L.unique R
  · obtain ⟨E, -, -, -, hET⟩ := StartSelf.lim_endo Y p.em p.em_int p.hd p.em_conj ε hε hεx (fun _ => 1)
      (fun N a => by rw [sub_self, map_zero]; exact VF.Ge.zero _)
    have hElim : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
        V.Ge N (MvPowerSeries.coeff μ (E i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i)) := by
      intro N i μ
      obtain ⟨n0, h⟩ := hET i μ N
      exact ⟨n0, fun n hn => by simpa only [one_mul] using h n hn⟩
    have hEspan := hLie C V O dd Y d I0 p ε hε hε1 hεx E hElim
    have hEφ : comp1 E φ = φ := by
      funext i
      have L := TendsS.comp1 (φ := fun n => Y.B.A.act (1 * ε ^ V.l ^ n)) (b := fun n => Y.B.A.act (M n * ε ^ V.l ^ n))
        (fun n => act0 _) hφ0 hET hT i
      have hdiv : ∀ n, ((V.l : O) ^ (n + 1)) ∣ (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n := by
        intro n
        have e1 : (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n) - M n * ε ^ V.l ^ n =
            M n * (ε ^ V.l ^ n * ε ^ V.l ^ n - ε ^ V.l ^ n) := by ring
        rw [e1]
        exact dvd_mul_of_dvd_right (sq_cong hε n) _
      have R := tendsS_of_small RowTiePLSmall.lSmall_holds Y
        (x := fun n => (1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) (x' := fun n => M n * ε ^ V.l ^ n) hdiv hT i
      have eq : (fun n => comp1 (Y.B.A.act (1 * ε ^ V.l ^ n)) (Y.B.A.act (M n * ε ^ V.l ^ n)) i) =
          fun n => Y.B.A.act ((1 * ε ^ V.l ^ n) * (M n * ε ^ V.l ^ n)) i := funext fun n => by
        rw [Y.B.A.mul_act (1 * ε ^ V.l ^ n) (M n * ε ^ V.l ^ n)]
      rw [eq] at L
      exact L.unique R
    intro v
    obtain ⟨b, hb⟩ := hEspan (linAct φ v)
    exact ⟨b, by rw [← hb, ← VP.linAct_comp1 E φ hφ0, hEφ]⟩

theorem one_entry [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
    (M : ℕ → O) (t : ZMod d → C) (hMt : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (t a - p.em a (M N))) :
    ∃ γ γ' : Pt C 1 dd, IsEndo Y γ ∧ IsEndo Y γ' ∧
      (∀ a, comp1 γ (Y.B.A.act a) = comp1 (Y.B.A.act a) γ) ∧
      (∀ a, comp1 γ' (Y.B.A.act a) = comp1 (Y.B.A.act a) γ') ∧
      (∀ c, linAct γ (p.e c) = t (p.ty0 c) • p.e c) ∧
      (∀ c, linAct γ' (p.e c) = t (p.ty0 c + p.hd) • p.e c) ∧
      (∀ v : Fin dd → C, ∃ b : I0 → C, linAct γ v = ∑ c, b c • p.e c) ∧
      (∀ v : Fin dd → C, ∃ b : I0 → C, linAct γ' v = ∑ c, b c • p.e c) ∧
      IntS V (FB.expS C (ev (n := 2) ![comp1 γ (pt C dd 0), pt C dd 1] Y.h -
        ev (n := 2) ![pt C dd 0, comp1 γ' (pt C dd 1)] Y.h)) := by
  obtain ⟨ε, hε, hε1, hεx⟩ := p.em_unr
  have hM : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (M (N + 1) - M N)) := by
    intro N a
    have e2 : p.em a (M (N + 1) - M N) = (t a - p.em a (M N)) - (t a - p.em a (M (N + 1))) := by
      rw [map_sub]; ring
    rw [e2]
    exact (hMt N a).sub ((hMt (N + 1) a).mono (by push_cast; linarith))
  have ht : ∀ a, Tends V (fun n => p.em a (M n)) (t a) := fun a =>
    tends_of_nat fun N => ⟨N, fun n hn => (hMt n a).mono (by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      push_cast; linarith)⟩
  have hεs := star_rel hε
  have hεs1 : ∀ a, V.MM (p.em a (star ε) - 1) := fun a => by rw [p.em_conj]; exact hε1 _
  have hεsx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, star ε * x = (V.l : O) * y := by
    intro x hx
    obtain ⟨y, hy⟩ := hεx (star x) fun a => by rw [p.em_conj]; exact hx (a + p.hd)
    refine ⟨star y, ?_⟩
    have h := congrArg star hy
    simp only [star_mul, star_star, star_natCast] at h
    rw [mul_comm, h, mul_comm]
  have hMs : ∀ (N : ℕ) a, V.Ge ((N + 1 : ℕ) : ℝ) (p.em a (star (M (N + 1)) - star (M N))) := fun N a => by
    rw [← star_sub, p.em_conj]; exact hM N (a + p.hd)
  have cvA := StartSelf.actCv_of Y p.em ε hε (fun a => p.em_int a ε) hεx M hM
  have cvB := StartSelf.actCv_of Y p.em (star ε) hεs (fun a => p.em_int a _) hεsx (fun N => star (M N)) hMs
  have sA : (fun n => star (M n * ε ^ V.l ^ n)) = fun n => star (M n) * star ε ^ V.l ^ n :=
    funext fun n => by rw [star_mul', star_pow]
  have sB : (fun n => star (star (M n) * star ε ^ V.l ^ n)) = fun n => M n * ε ^ V.l ^ n :=
    funext fun n => by rw [star_mul', star_pow, star_star, star_star]
  obtain ⟨γ, γb, hγI, -, hγl, hγbl, hhom, hexp⟩ := endomorphism_limit_integral Y (fun n => M n * ε ^ V.l ^ n) cvA (by rw [sA]; exact cvB)
  obtain ⟨γ2, -, hγ2I, -, hγ2l, -, hhom2, -⟩ := endomorphism_limit_integral Y (fun n => star (M n) * star ε ^ V.l ^ n) cvB
    (by rw [sB]; exact cvA)
  have hT : ∀ i, TendsS V (fun n => Y.B.A.act (M n * ε ^ V.l ^ n) i) (γ i) := tends_of_endomorphism_limit Y hγl
  have hTb : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γb i) := by
    have h := tends_of_endomorphism_limit Y hγbl
    simpa only [star_mul', star_pow] using h
  have hT2 : ∀ i, TendsS V (fun n => Y.B.A.act (star (M n) * star ε ^ V.l ^ n) i) (γ2 i) := tends_of_endomorphism_limit Y hγ2l
  have heq : γ2 = γb := funext fun i => (hT2 i).unique (hTb i)
  subst heq
  obtain ⟨hc, hi⟩ := half hLie Y p ε hε hε1 hεx M γ hT
  obtain ⟨hc', hi'⟩ := half hLie Y p (star ε) hεs hεs1 hεsx (fun N => star (M N)) γ2 hT2
  refine ⟨γ, γ2, ⟨hγI, const_of_lim Y hT, hhom⟩, ⟨hγ2I, const_of_lim Y hT2, hhom2⟩, hc, hc', ?_, ?_, hi, hi', hexp⟩
  · exact fun c => StartSelf.lin_of_lim Y p M ε hε1 t ht γ hT c
  · exact fun c => StartSelf.lin_of_lim Y p (fun N => star (M N)) (star ε) hεs1 (fun a => t (a + p.hd))
      (fun a => by simp only [p.em_conj]; exact ht (a + p.hd)) γ2 hT2 c

end GmPackP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd d : ℕ}

theorem gmPack_of_lie [NeZero d] (hLie : ProjLieSelfSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) : GmPackSt Y p := by
  choose Mm hMm using fun N : ℕ => p.gm_lim (N + 1)
  have h := fun r s : Fin 2 => GmPackP.one_entry hLie Y p (fun N => Mm N r s) (fun a => p.gm a r s)
    (fun N a => hMm N a r s)
  choose γ γ' h1 h2 h3 h4 h5 h6 h7 h8 h9 using h
  exact ⟨γ, γ', ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

theorem gmPack_of [NeZero d] (hE : RowTiePKey.KeyEigSt) (Y : FBChart C V O dd) {I0 : Type} [Fintype I0]
    (p : SelfData Y d I0) : GmPackSt Y p := gmPack_of_lie (projLieSelf_of hE) Y p

theorem gmPack_holds [NeZero d] (Y : FBChart C V O dd) {I0 : Type} [Fintype I0] (p : SelfData Y d I0) :
    GmPackSt Y p := gmPack_of RowTiePKey.keyEig_holds Y p

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.SharpRestriction.GrowthBounds.ProofRowTieVals

section

@[expose] public section

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

theorem unitSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : UnitSelfSt Y p :=
  unitSelf_of Y p fun o => gmPack_holds Y (p o)

theorem projSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : ProjSelfSt Y p :=
  projSelf_of Y p fun o => gmPack_holds Y (p o)

theorem germLiftSelf_holds (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))
    (H : ∀ o, (Y.rawSelf (p o)).Hyps V) : GermLiftSelfSt Y p H :=
  germLiftSelf_of Y p H (projSelf_holds Y p) fun o => tcoordSelf_holds C V O dd Y d (I0 o) (p o) (H o).cartH

end Formalism.L2.FormalSeriesBounds
end
end
