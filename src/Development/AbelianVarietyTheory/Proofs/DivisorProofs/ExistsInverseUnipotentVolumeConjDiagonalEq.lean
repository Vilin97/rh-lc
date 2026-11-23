module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdL
public import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSumRowCol
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIntegralGLColumnCongruenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjIntegralGLRowCongruenceStatement
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Linter.HaveILetI
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagColumnUnipotentMemPeriodUnipotentIntegralGL

section

@[expose] public section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

namespace GlobalTheory.DiagVol

theorem colE_mem_symN_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
    (t : n ⊕ Fin c) (y : n ⊕ Fin c → k) (hy : ∀ r, y r ∈ 𝒪[k])
    (hz : ∀ r, ¬ ordL c r < ordL c t → y r = 0) :
    ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c),
      x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0) := by
  set E : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of (fun r s => if s = t then y r else 0) with hE
  have hyt : y t = 0 := hz t (lt_irrefl _)
  have hEE : E * E = 0 := by
    ext r s
    simp only [hE, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [Finset.sum_eq_single t]
    · simp [hyt]
    · intro u _ hu; simp [hu]
    · intro h; exact absurd (Finset.mem_univ t) h
  have h1 : (1 + E) * (1 - E) = 1 := by
    have : (1 + E) * (1 - E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  have h2 : (1 - E) * (1 + E) = 1 := by
    have : (1 - E) * (1 + E) = 1 - E * E := by noncomm_ring
    rw [this, hEE, sub_zero]
  let x : GL (n ⊕ Fin c) k := ⟨1 + E, 1 - E, h1, h2⟩
  have hone : ∀ i j : n ⊕ Fin c, (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hEi : ∀ i j, E i j ∈ 𝒪[k] := by
    intro i j
    simp only [hE, Matrix.of_apply]
    split_ifs
    · exact hy i
    · exact zero_mem _
  have hInN : ∀ p : ℕ, (∀ r, y r ≠ 0 → lev p r < lev (n := n) (c := c) p t) → InN p x := by
    intro p hp r s hrs
    show (1 + E) r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
    rw [Matrix.add_apply, add_eq_left]
    simp only [hE, Matrix.of_apply]
    split_ifs with h
    · subst h
      by_contra hne
      exact absurd hrs (not_le.2 (hp r hne))
    · rfl
  refine ⟨x, Subgroup.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
  · show x ∈ N k n c ((c + 1) / 2) ⊔ N k n c (c / 2 + 1)
    cases t with
    | inr j =>
      refine Subgroup.mem_sup_left (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))
      have hlt : ordL c r < ordL c (Sum.inr j : n ⊕ Fin c) := by
        by_contra h; exact hr (hz r h)
      cases r with
      | inl a => simp [ordL, lev] at hlt ⊢; omega
      | inr i => simp [ordL, lev] at hlt ⊢; omega
    | inl a0 =>
      refine Subgroup.mem_sup_right (Model.mem_N_iff.2 (hInN _ fun r hr => ?_))
      have hlt : ordL c r < ordL c (Sum.inl a0 : n ⊕ Fin c) := by
        by_contra h; exact hr (hz r h)
      cases r with
      | inl a => simp [ordL, lev] at hlt ⊢
      | inr i => simp [ordL, lev] at hlt ⊢; omega
  · refine (mem_KO_iff _).2 ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      rw [Matrix.add_apply]; exact add_mem (hone i j) (hEi i j)
    · show (1 - E) i j ∈ 𝒪[k]
      rw [Matrix.sub_apply]; exact sub_mem (hone i j) (hEi i j)

end GlobalTheory.DiagVol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagColumnUnipotentMemPeriodUnipotentIntegralGLStatement

section

@[expose] public section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

theorem _root_.GlobalTheory.T.flagColumnUnipotent_mem_periodUnipotent_integralGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k), (∀ r, y r ∈ 𝒪[k]) → (∀ r, ¬ ordL c r < ordL c t → y r = 0) → ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if s = t then y r else 0) := by
  first | exact @GlobalTheory.DiagVol.colE_mem_symN_KO | exact GlobalTheory.DiagVol.colE_mem_symN_KO | (intros; apply GlobalTheory.DiagVol.colE_mem_symN_KO <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRowUnipotentMemPeriodUnipotentIntegralGL

section

@[expose] public section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

namespace GlobalTheory.DiagVol

theorem rowElt_mem : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k),
    (∀ s, y s ∈ 𝒪[k]) → (∀ s, ¬ ordL c t < ordL c s → y s = 0) →
    ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0) := by
  intro k _ _ _ _ n _ _ c t y hy h0
  set E : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k := Matrix.of (fun r s => if r = t then y s else 0) with hE
  have yt : y t = 0 := h0 t (lt_irrefl _)
  have hEE : E * E = 0 := by
    ext r s
    simp [hE, Matrix.mul_apply, yt]
  have h1 : (1 + E) * (1 - E) = 1 := by
    simp only [add_mul, mul_sub, one_mul, mul_one, hEE]; abel
  have h2 : (1 - E) * (1 + E) = 1 := by
    simp only [sub_mul, mul_add, one_mul, mul_one, hEE]; abel
  let M : GL (n ⊕ Fin c) k := ⟨1 + E, 1 - E, h1, h2⟩
  refine ⟨M, Subgroup.mem_inf.2 ⟨?_, ?_⟩, rfl⟩
  · have key : ∀ p, (∀ s, lev p s ≤ lev p t → y s = 0) → M ∈ N k n c p := by
      intro p hp
      rw [Model.mem_N_iff]
      intro r s hrs
      show (1 + E) r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s
      rw [Matrix.add_apply, hE, Matrix.of_apply]
      split_ifs with hr
      · subst hr; rw [hp s hrs, add_zero]
      · rw [add_zero]
    unfold symN
    rcases t with x | i
    · refine Subgroup.mem_sup_left (key _ fun s hs => h0 s ?_)
      rcases s with z | j <;> simp [ordL, lev] at hs ⊢ <;> omega
    · refine Subgroup.mem_sup_right (key _ fun s hs => h0 s ?_)
      rcases s with z | j <;> simp [ordL, lev] at hs ⊢ <;> omega
  · rw [mem_KO_iff]
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · show (1 + E) i j ∈ 𝒪[k]
      simp only [Matrix.add_apply, hE, Matrix.of_apply, Matrix.one_apply]
      refine add_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hy _
    · show (1 - E) i j ∈ 𝒪[k]
      simp only [Matrix.sub_apply, hE, Matrix.of_apply, Matrix.one_apply]
      refine sub_mem ?_ ?_ <;> split_ifs <;> first | exact one_mem _ | exact zero_mem _ | exact hy _

end GlobalTheory.DiagVol
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagRowUnipotentMemPeriodUnipotentIntegralGLStatement

section

@[expose] public section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx GlobalTheory.DiagVol ValuativeRel Matrix

theorem _root_.GlobalTheory.T.flagRowUnipotent_mem_periodUnipotent_integralGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (t : n ⊕ Fin c) (y : n ⊕ Fin c → k), (∀ s, y s ∈ 𝒪[k]) → (∀ s, ¬ ordL c t < ordL c s → y s = 0) → ∃ x ∈ symN k n c ⊓ KO k (n ⊕ Fin c), x.val = 1 + Matrix.of (fun r s => if r = t then y s else 0) := by
  first | exact @GlobalTheory.DiagVol.rowElt_mem | exact GlobalTheory.DiagVol.rowElt_mem | (intros; apply GlobalTheory.DiagVol.rowElt_mem <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseUnipotentVolumeConjDiagonalEq

section

@[expose] public section

open GlobalTheory.FunObj GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
open ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.DiagVol

section Main
variable {K₀ : Type} [Field K₀] {ι : Type} [Fintype ι] [DecidableEq ι]

def unipSub (ℓ : ι → ℕ) : Subgroup (GL ι K₀) where
  carrier := {g | ∀ r s, ℓ s ≤ ℓ r → g.val r s = (1 : Matrix ι ι K₀) r s}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := fun {a b} ha hb r s hrs => by
    have tri : b.val.BlockTriangular ℓ := fun i j h => by
      rw [hb i j h.le, Matrix.one_apply_ne]; rintro rfl; exact lt_irrefl _ h
    have : (a.val * b.val) r s = ((1 : Matrix ι ι K₀) * b.val) r s := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : ℓ u ≤ ℓ r
      · rw [ha r u hu]
      · rw [tri (show ℓ s < ℓ u by omega)]; simp
    rw [Units.val_mul, this, Matrix.one_mul, hb r s hrs]
  inv_mem' := fun {a} ha r s hrs => by
    have tri : (a⁻¹).val.BlockTriangular ℓ := by
      rw [Matrix.coe_units_inv]
      haveI := a.invertible
      exact Matrix.blockTriangular_inv_of_blockTriangular fun i j h => by
        rw [ha i j h.le, Matrix.one_apply_ne]; rintro rfl; exact lt_irrefl _ h
    have : (a.val * (a⁻¹).val) r s = ((1 : Matrix ι ι K₀) * (a⁻¹).val) r s := by
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases hu : ℓ u ≤ ℓ r
      · rw [ha r u hu]
      · rw [tri (show ℓ s < ℓ u by omega)]; simp
    rw [Units.mul_inv, Matrix.one_mul] at this
    exact this.symm
end Main

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

theorem symN_le_unipSub {F : Type} [Field F] : symN F n c ≤ unipSub (ordL c) := by
  refine sup_le (fun x hx => ?_) (fun x hx => ?_) <;> rw [Model.mem_N_iff] at hx <;>
    intro r s hrs <;> refine hx r s ?_ <;>
    rcases r with r | r <;> rcases s with s | s <;> simp only [ordL, lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega

theorem conj_diag_mem {F : Type} [Field F] (d : n ⊕ Fin c → Fˣ) {x : GL (n ⊕ Fin c) F} (hx : x ∈ symN F n c) :
    diagGL d * x * (diagGL d)⁻¹ ∈ symN F n c := by
  have key : ∀ p, ∀ y ∈ N F n c p, diagGL d * y * (diagGL d)⁻¹ ∈ N F n c p := by
    intro p y hy
    rw [Model.mem_N_iff] at hy ⊢
    intro r s h
    have e : ((diagGL d)⁻¹).val = Matrix.diagonal fun i => (((d i)⁻¹ : Fˣ) : F) := rfl
    rw [Units.val_mul, Units.val_mul, e, diagGL_val, Matrix.mul_diagonal, Matrix.diagonal_mul, hy r s h]
    by_cases hrs : r = s
    · subst hrs; simp
    · simp [Matrix.one_apply_ne hrs]
  have h : symN F n c ≤ (symN F n c).comap (MulAut.conj (diagGL d)).toMonoidHom :=
    sup_le (fun v hv => Subgroup.mem_sup_left (by simpa using key _ v hv))
      fun v hv => Subgroup.mem_sup_right (by simpa using key _ v hv)
  simpa using h hx

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem invVol_diag_one (ϖ : kˣ) (hϖ : IsUnif ϖ) (t : n ⊕ Fin c) :
    ∃ z : ℤ, invVol ((KO k (n ⊕ Fin c)).map (MulAut.conj (diagGL (Pi.mulSingle t ϖ))).toMonoidHom) =
      (resCard k : ℚ) ^ z ∧ |z| ≤ Fintype.card (n ⊕ Fin c) := by
  set g := diagGL (Pi.mulSingle t ϖ) with hg
  set K := KO k (n ⊕ Fin c)
  set C := K.map (MulAut.conj g).toMonoidHom with hC
  set Sout := Finset.univ.filter (fun s : n ⊕ Fin c => ordL c t < ordL c s)
  set Sin := Finset.univ.filter (fun r : n ⊕ Fin c => ordL c r < ordL c t)
  have hU : ∀ x ∈ symN k n c ⊓ K, ∀ r s, ordL c s ≤ ordL c r → x.val r s = (1 : Matrix _ _ k) r s :=
    fun x hx => symN_le_unipSub (Subgroup.mem_inf.1 hx).1

  have hnum : C.relIndex (symN k n c ⊓ K) = resCard k ^ Sout.card := by
    refine GlobalTheory.T.relIndex_conj_integralGL_row_congruence ϖ hϖ t Sout (by simp [Sout]) _ inf_le_right (fun x hx s hs => ?_) (fun y hy h0 => ?_)
    · exact hU x hx t s (by simpa [Sout] using hs)
    · exact GlobalTheory.T.flagRowUnipotent_mem_periodUnipotent_integralGL t y hy fun s hs => h0 s (by simpa [Sout] using hs)

  have hden : K.relIndex (symN k n c ⊓ C) = resCard k ^ Sin.card := by
    set φ := (MulAut.conj g⁻¹).toMonoidHom
    have hφ : Function.Injective φ := (MulAut.conj g⁻¹).injective
    have hCφ : C.map φ = K := by
      rw [hC, Subgroup.map_map]
      conv_rhs => rw [← Subgroup.map_id K]
      congr 1
      ext x; simp [φ, mul_assoc]
    have hNφ : (symN k n c).map φ = symN k n c := by
      have hgi : g⁻¹ = diagGL (Pi.mulSingle t ϖ)⁻¹ := Units.ext rfl
      refine le_antisymm ?_ fun x hx => ?_
      · rintro _ ⟨x, hx, rfl⟩
        simpa [φ, hgi] using conj_diag_mem (Pi.mulSingle t ϖ)⁻¹ hx
      · refine ⟨g * x * g⁻¹, conj_diag_mem _ hx, ?_⟩
        simp [φ, mul_assoc]
    rw [← Subgroup.relIndex_map_map_of_injective _ _ hφ, Subgroup.map_inf_eq _ _ _ hφ, hNφ, hCφ]
    refine GlobalTheory.T.relIndex_conj_integralGL_column_congruence ϖ hϖ t Sin (by simp [Sin]) _ inf_le_right (fun x hx r hr => ?_) (fun y hy h0 => ?_)
    · exact hU x hx r t (by simpa [Sin] using hr)
    · exact GlobalTheory.T.flagColumnUnipotent_mem_periodUnipotent_integralGL t y hy fun r hr => h0 r (by simpa [Sin] using hr)
  have hq : (0 : ℚ) < resCard k := by
    have : 1 < resCard k := Finite.one_lt_card
    exact_mod_cast this.trans' one_pos
  refine ⟨(Sout.card : ℤ) - Sin.card, ?_, ?_⟩
  · rw [invVol, hnum, hden, zpow_sub₀ hq.ne']
    push_cast; rfl
  · have h1 : Sout.card ≤ Fintype.card (n ⊕ Fin c) := Finset.card_le_univ _
    have h2 : Sin.card ≤ Fintype.card (n ⊕ Fin c) := Finset.card_le_univ _
    rw [abs_le]; constructor <;> omega

end GlobalTheory.DiagVol
end
end
end
