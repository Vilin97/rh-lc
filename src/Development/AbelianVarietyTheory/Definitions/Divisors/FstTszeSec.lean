module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial

@[expose] public section

set_option autoImplicit false

noncomputable section

open TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer.Charts

open CategoryTheory GlobalTheory.CatCoh

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}


theorem _root_.GlobalTheory.AnPer.Charts.tsze_nil {O : Type} [CommRing O] [Algebra ℂ O] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom ℂ O (Fin g → O)).toRingHom) := by
  refine ⟨2, ?_⟩
  rw [pow_two, Submodule.zero_eq_bot, ← le_bot_iff, Ideal.mul_le]
  intro x hx y hy
  rw [RingHom.mem_ker] at hx hy
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply] at hx hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx, hy]


@[reducible] def jet (k : K.K) : K.Obj where
  k := k
  C := TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k))
  alg := ((TrivSqZeroExt.inlHom _ _).comp (K.cst k)).toAlgebra
  J := RingHom.ker (TrivSqZeroExt.fstHom ℂ (Hol (K.W k)) (Fin g → Hol (K.W k))).toRingHom
  nil := tsze_nil
  ρ := TrivSqZeroExt.inlHom _ _
  ρ_cst _ := rfl

def tszeSec {O : Type} [CommRing O] [Algebra ℂ O] (D : Fin g → Derivation ℂ O O) : O →+* TrivSqZeroExt O (Fin g → O) where
  toFun h := TrivSqZeroExt.inl h + TrivSqZeroExt.inr fun a ↦ D a h
  map_one' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_zero' := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_add' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp)
  map_mul' x y := TrivSqZeroExt.ext (by simp) (funext fun a ↦ by simp [mul_comm])


theorem _root_.GlobalTheory.AnPer.Charts.fst_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).fst = h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]


theorem _root_.GlobalTheory.AnPer.Charts.snd_tszeSec {O : Type} [CommRing O] [Algebra ℂ O]
    (D : Fin g → Derivation ℂ O O) (h : O) (a : Fin g) :
    (_root_.GlobalTheory.AnPer.Charts.tszeSec D h).snd a = D a h := by
  simp [_root_.GlobalTheory.AnPer.Charts.tszeSec]

def jetSec (k : K.K) : Hol (K.W k) →+* TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)) := tszeSec dw


theorem _root_.GlobalTheory.AnPer.Charts.tsze_expand {O : Type} [CommRing O] (h : O) (v : Fin g → O) :
    (TrivSqZeroExt.inl h + TrivSqZeroExt.inr v : TrivSqZeroExt O (Fin g → O)) = TrivSqZeroExt.inl h +
      ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) := by
  congr 1
  simp only [TrivSqZeroExt.inl_mul_inr]
  ext b
  · simp [TrivSqZeroExt.fst_sum]
  · simp [TrivSqZeroExt.snd_sum, Finset.sum_apply, Pi.single_apply]

def jet0 (k : K.K) : K.Hom (K.triv k) (K.jet k) := by
  letI := (K.triv k).ring
  letI := (K.triv k).alg
  letI := (K.jet k).ring
  letI := (K.jet k).alg
  exact {
    φ := letI := (K.triv k).alg
      { ((K.jet k).ρ.comp (K.sh (K.le_refl k))) with
        commutes' := fun f ↦ (congrArg (K.jet k).ρ (K.sh_cst (K.le_refl k) f)).trans ((K.jet k).ρ_cst f) }
    deg := 0
    le := K.le_refl k
    mem c hc := by rw [Ideal.mem_bot.1 hc, map_zero]; exact (K.jet k).J.zero_mem
    close := Relation.ReflTransGen.refl }

def jet1 (k : K.K) : K.Hom (K.triv k) (K.jet k) :=
  letI := (K.triv k).ring
  letI := (K.triv k).alg
  letI := (K.jet k).ring
  letI := (K.jet k).alg
  { φ := letI := (K.triv k).alg
      { jetSec k with
        commutes' := fun f ↦ TrivSqZeroExt.ext (fst_tszeSec _ _) (funext fun a ↦ (snd_tszeSec _ _ a).trans (dw_cst k a f)) }
    deg := 0
    le := K.le_refl k
    mem c hc := by rw [Ideal.mem_bot.1 hc, map_zero]; exact (K.jet k).J.zero_mem
    close := Relation.ReflTransGen.single ⟨fun a ↦ TrivSqZeroExt.inr (Pi.single a 1), fun _ ↦ rfl,
      fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _, fun h ↦ by
        simp only [RingHom.comp_apply, sh_refl]
        exact tsze_expand h fun a ↦ dw a h⟩ }

end GlobalTheory.AnPer.Charts
