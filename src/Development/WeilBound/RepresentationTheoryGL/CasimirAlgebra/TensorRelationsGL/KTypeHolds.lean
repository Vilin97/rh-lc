module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.StepFormula
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PChain
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAnti
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContract
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PCurry
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PHeight
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PJmComm
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PKType
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PLieInv
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PPiQdet
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PQdetFacts
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSWStart
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.QdetFacts
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt
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
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSpectrum
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepChar
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepFormula
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGK
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGl
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAll
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransFin
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransOf
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallAlg
import Mathlib.Tactic.Linter.Style
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PYoungB
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSemiZero

section

@[expose] public section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace SemiInvariantDeterminant

theorem det_bar {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ (bar τ) γ).det = star (κ τ γ).det := by
  have e : κ (bar τ) γ = (starRingEnd ℂ).mapMatrix (κ τ γ) := by
    ext i j; exact hK.conj τ γ i j
  rw [e, ← RingHom.map_det]
  rfl

theorem det_mul_star {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ τ γ).det * star (κ τ γ).det = 1 := by
  have := congrArg Matrix.det (hK.unit τ γ)
  rwa [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this

end SemiInvariantDeterminant

open SemiInvariantDeterminant in
theorem semiZero_of (hQ : QdetFacts) (_hW : WallAlg) (hL : LieInv) (hWQ : WallQuot) : SemiZero := by
  intro n hn M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG s φ hφ hS
  obtain ⟨lab, c, ξ, -, hact, I, w, hw, hwξ⟩ := hS
  have hρ : ∀ γ, ρ γ (ξ I) = (∏ τ, (κ τ γ).det ^ c τ) • ξ I := by
    intro γ
    have h := congrFun (hact γ) I
    rw [actT_apply, Pi.smul_apply] at h
    rw [← h, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    rw [Subsingleton.elim (default : Fin 0 → Fin n) I]
  obtain ⟨N, F, hFgl, -, hFch, hFE, hN⟩ := hWQ n M ι E hG.gl hG.comm (fun _ _ => s) φ (by
    intro τ u
    rw [hφ τ u, Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  have hξN : N.mkQ (ξ I) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN]
    push Not
    exact ⟨w, hw, hwξ⟩
  have htr : ∀ τ', N.mkQ ((∑ a, E τ' a a) (ξ I)) = (∑ a, F τ' a a) (N.mkQ (ξ I)) := by
    intro τ'

    simp only [LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun a _ => LinearMap.congr_fun (hFE τ' a a) (ξ I)
  have hc : ∀ τ, c τ = c (bar τ) := by
    intro τ
    have hl := hL n M ι Γ bar κ E ρ hK hG c (ξ I) hρ τ
    have h1 : N.mkQ ((∑ a, E τ a a) (ξ I)) = N.mkQ ((∑ a, E (bar τ) a a) (ξ I)) := by
      rw [htr, htr, (hQ n (M ⧸ N) (F τ) (hFgl τ)).2.2.1 _ (hFch τ),
        (hQ n (M ⧸ N) (F (bar τ)) (hFgl (bar τ))).2.2.1 _ (hFch (bar τ))]
    have h2 : (∑ a, E τ a a) (ξ I) - (∑ a, E (bar τ) a a) (ξ I) =
        ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • ξ I := by
      rw [LinearMap.sum_apply, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
      simp only [hl, if_true]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have h3 : ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • N.mkQ (ξ I) = 0 := by
      rw [← map_smul, ← h2, map_sub, h1, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (Nat.cast_eq_zero.mp h) (by omega)
      · exact sub_eq_zero.mp (Int.cast_eq_zero.mp h)
    · exact absurd h hξN
  have hχ : ∀ γ, (∏ τ, (κ τ γ).det ^ c τ) = 1 := by
    intro γ
    refine Finset.prod_involution (fun τ _ => bar τ) ?_ ?_ (fun _ _ => Finset.mem_univ _)
      (fun τ _ => hK.invol τ)
    · intro τ _
      rw [det_bar hK, ← hc τ, ← mul_zpow, det_mul_star hK, _root_.one_zpow]
    · intro τ _ _
      exact hK.ne τ
  exact ⟨ξ I, fun γ => by rw [hρ, hχ, one_smul], w, hw, hwξ⟩

end PositivityTheory.Rg.Cz

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallQuot

section

@[expose] public section

noncomputable section

open Formalism.REAL

namespace PositivityTheory.Rg.Cz

namespace WQ

section Alg

variable {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B]

theorem qdet_map (f : A →ₐ[ℂ] B) {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) :
    f (qdet E u) = qdet (fun a b => f (E a b)) u := by
  unfold qdet qminor

  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.prod (congrArg List.ofFn (funext fun k => ?_))
  simp only [Function.comp, Tm, map_add (f := _), apply_ite f, map_zero, AlgHom.commutes]

theorem glRel_map (f : A →ₐ[ℂ] B) {n : ℕ} {E : Fin n → Fin n → A} (h : GlRel E) : GlRel fun a b => f (E a b) := by
  intro a b c d
  have := congrArg f (h a b c d)
  simpa [map_sub, map_mul, apply_ite f] using this

theorem glRel_of_inj (f : A →ₐ[ℂ] B) (hf : Function.Injective f) {n : ℕ} {E : Fin n → Fin n → A}
    (h : GlRel fun a b => f (E a b)) : GlRel E := by
  intro a b c d
  apply hf
  simpa [map_sub, map_mul, apply_ite f] using h a b c d

theorem comm_qdet {n : ℕ} (E : Fin n → Fin n → A) (x : A) (h : ∀ a b, Commute x (E a b)) (u : ℂ) :
    Commute x (qdet E u) := by
  unfold qdet qminor
  refine Commute.sum_right _ _ _ fun σ _ => ?_
  refine Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hy
  unfold Tm
  refine Commute.add_right ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_right _ _
  · exact Commute.zero_right _

end Alg

section Quot

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stab (N : Submodule ℂ M) : Subalgebra ℂ (Module.End ℂ M) where
  carrier := {X | ∀ y ∈ N, X y ∈ N}
  mul_mem' hX hY y hy := hX _ (hY y hy)
  add_mem' hX hY y hy := N.add_mem (hX y hy) (hY y hy)
  algebraMap_mem' c y hy := by simpa [Module.algebraMap_end_apply] using N.smul_mem c hy

def qmap (N : Submodule ℂ M) : stab N →ₐ[ℂ] Module.End ℂ (M ⧸ N) where
  toFun X := N.mapQ N X.1 (fun y hy => X.2 y hy)
  map_one' := by ext y; simp
  map_mul' X Y := by ext y; simp
  map_zero' := by ext y; simp
  map_add' X Y := by ext y; simp
  commutes' c := by ext y; simp [Module.algebraMap_end_apply]

end Quot

end WQ

open WQ

theorem wallQuot_of (hQ : QdetFacts) : WallQuot := by
  intro n M _ _ ι E hgl hcomm l φ hφ
  let N : Submodule ℂ M :=
    { carrier := {y | ∀ w ∈ envAlg E, φ (w y) = 0}
      add_mem' := fun {x y} hx hy w hw => by
        show φ (w (x + y)) = 0
        rw [map_add (f := _), map_add (f := _), hx w hw, hy w hw, add_zero]
      zero_mem' := fun w _ => by simp
      smul_mem' := fun c y hy w hw => by
        show φ (w (c • y)) = 0
        rw [map_smul, map_smul, hy w hw, smul_zero] }
  have hgen : ∀ τ a b, E τ a b ∈ envAlg E := fun τ a b => Algebra.subset_adjoin ⟨τ, a, b, rfl⟩
  have hstab : ∀ τ a b, E τ a b ∈ stab N := fun τ a b y hy w hw =>
    hy (w * E τ a b) (Subalgebra.mul_mem _ hw (hgen τ a b))
  let E' : ι → Fin n → Fin n → stab N := fun τ a b => ⟨E τ a b, hstab τ a b⟩
  let F : ι → Fin n → Fin n → Module.End ℂ (M ⧸ N) := fun τ a b => qmap N (E' τ a b)
  have hgl' : ∀ τ, GlRel (E' τ) := fun τ => glRel_of_inj (stab N).val Subtype.val_injective (hgl τ)
  have hcent : ∀ τ (u : ℂ), ∀ w ∈ envAlg E, Commute w (qdet (E τ) u) := by
    intro τ u w hw
    induction hw using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨τ', a, b, rfl⟩ := hx
      by_cases h : τ' = τ
      · subst h
        exact ((hQ n M (E τ') (hgl τ')).1 u a b).symm
      · exact comm_qdet _ _ (fun c d => hcomm τ' τ h a b c d) u
    | algebraMap c => exact Algebra.commute_algebraMap_left _ _
    | add x y _ _ hx hy => exact hx.add_left hy
    | mul x y _ _ hx hy => exact hx.mul_left hy
  have hq : ∀ τ (u : ℂ) y, qdet (F τ) u (N.mkQ y) = N.mkQ (qdet (E τ) u y) := by
    intro τ u y
    rw [show qdet (F τ) u = qmap N (qdet (E' τ) u) from (qdet_map _ _ _).symm,
      show qdet (E τ) u = (stab N).val (qdet (E' τ) u) from (qdet_map (stab N).val (E' τ) u).symm]
    rfl
  refine ⟨N, F, fun τ => glRel_map (qmap N) (hgl' τ), fun τ τ' h a b c d => ?_, fun τ u => ?_,
    fun τ a b => LinearMap.ext fun y => rfl, fun y => Iff.rfl⟩
  · exact (show Commute (E' τ a b) (E' τ' c d) from Subtype.ext (hcomm τ τ' h a b c d).eq).map (qmap N)
  · refine Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, hq, Module.algebraMap_end_apply, ← N.mkQ.map_smul,
      Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    intro w hw
    show φ (w (qdet (E τ) u y - (∏ k, (u + l τ k)) • y)) = 0
    have hc := congrArg (fun T : Module.End ℂ M => φ (T y)) (hcent τ u w hw).eq
    simp only [Module.End.mul_apply] at hc
    have h2 := LinearMap.congr_fun (hφ τ u) (w y)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h2
    rw [map_sub, map_sub, map_smul, map_smul, hc, h2, sub_self]

end PositivityTheory.Rg.Cz

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PYoung

section

@[expose] public section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace YoungTableau

section Main

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {ι : Type} [DecidableEq ι]
  {Q : Type} [Fintype Q] [DecidableEq Q] {N : ℕ} {C : Type} [DecidableEq C]

theorem altPair_apply (tl : Fin N → ι) (f : TV n M (Q ⊕ (Fin N ⊕ Fin N))) (I : Q ⊕ (Fin N ⊕ Fin N) → Fin n) :
    altPair tl f I = ∑ σ ∈ colG tl, ((Equiv.Perm.sign σ : ℤ) : ℂ) • f (I ∘ dbl σ) := by
  rw [altPair, LinearMap.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, pm_apply]

def inF (Q : Type) (N : ℕ) : Fin N → Q ⊕ (Fin N ⊕ Fin N) := fun k => .inr (.inl k)

def inS (Q : Type) (N : ℕ) : Fin N → Q ⊕ (Fin N ⊕ Fin N) := fun k => .inr (.inr k)

theorem term (tl : Fin N → ι) (col : Q ⊕ (Fin N ⊕ Fin N) → C) (b : Q ⊕ (Fin N ⊕ Fin N) → Fin n)
    (hT : IsTab col b) (h1 : ∀ p k, col (.inl p) ≠ col (.inr k)) (h2 : ∀ k k', col (.inr (.inl k)) ≠ col (.inr (.inr k')))
    (ξ : TV n M (Q ⊕ (Fin N ⊕ Fin N))) (σ : Equiv.Perm (Fin N)) :
    alt (colG col) ξ (b ∘ dbl σ) =
      ((sg (col ∘ inF Q N) (b ∘ inF Q N) ((b ∘ inF Q N) ∘ σ) * sg (col ∘ inS Q N) (b ∘ inS Q N) ((b ∘ inS Q N) ∘ σ) : ℤ) : ℂ)
        • alt (colG col) ξ b := by
  have hFtab : IsTab (col ∘ inF Q N) (b ∘ inF Q N) := by
    refine isTab_comp col b hT (inF Q N) ?_ ?_
    · intro x y hxy
      simpa [inF] using hxy
    · intro q y hq
      simp only [inF] at hq
      rcases q with q | k | k
      · exact absurd hq (h1 q _)
      · exact ⟨k, rfl⟩
      · exact absurd hq.symm (h2 y k)
  have hStab : IsTab (col ∘ inS Q N) (b ∘ inS Q N) := by
    refine isTab_comp col b hT (inS Q N) ?_ ?_
    · intro x y hxy
      simpa [inS] using hxy
    · intro q y hq
      simp only [inS] at hq
      rcases q with q | k | k
      · exact absurd hq (h1 q _)
      · exact absurd hq (h2 k y)
      · exact ⟨k, rfl⟩
  have key : ColInj col (b ∘ dbl σ) →
      (∃ π ∈ colG (col ∘ inF Q N), (b ∘ inF Q N) ∘ ⇑π = (b ∘ inF Q N) ∘ ⇑σ) ∧
      (∃ π ∈ colG (col ∘ inS Q N), (b ∘ inS Q N) ∘ ⇑π = (b ∘ inS Q N) ∘ ⇑σ) := by
    intro hc
    refine ⟨exists_perm _ _ hFtab σ ?_, exists_perm _ _ hStab σ ?_⟩
    · intro k k' hk hb'
      have := hc (inF Q N k) (inF Q N k') hk (by simpa [dbl, inF] using hb')
      simpa [inF] using this
    · intro k k' hk hb'
      have := hc (inS Q N k) (inS Q N k') hk (by simpa [dbl, inS] using hb')
      simpa [inS] using this
  have hdup : ¬ ColInj col (b ∘ dbl σ) → alt (colG col) ξ (b ∘ dbl σ) = 0 := by
    intro hc
    simp only [ColInj, not_forall] at hc
    obtain ⟨p, q, hcol, hbq, hpq⟩ := hc
    exact alt_dup col ξ _ p q hpq hcol hbq
  by_cases hF : ∃ π ∈ colG (col ∘ inF Q N), (b ∘ inF Q N) ∘ ⇑π = (b ∘ inF Q N) ∘ ⇑σ
  · by_cases hS : ∃ π ∈ colG (col ∘ inS Q N), (b ∘ inS Q N) ∘ ⇑π = (b ∘ inS Q N) ∘ ⇑σ
    · obtain ⟨πF, hπF, eF⟩ := hF
      obtain ⟨πS, hπS, eS⟩ := hS
      rw [← eF, ← eS, sg_perm _ _ hFtab.1 πF hπF, sg_perm _ _ hStab.1 πS hπS]
      rw [mem_colG] at hπF hπS
      have hπ : (Equiv.refl Q).sumCongr (πF.sumCongr πS) ∈ colG col := by
        rw [mem_colG]
        rintro (q | k | k)
        · rfl
        · simpa [inF] using hπF k
        · simpa [inS] using hπS k
      have hb : b ∘ dbl σ = b ∘ ⇑((Equiv.refl Q).sumCongr (πF.sumCongr πS)) := by
        funext p
        rcases p with q | k | k
        · rfl
        · simpa [dbl, inF] using (congrFun eF k).symm
        · simpa [dbl, inS] using (congrFun eS k).symm
      rw [hb, alt_perm col ξ b _ hπ, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_sumCongr]
      simp
    · rw [sg_zero _ _ _ hS, mul_zero, Int.cast_zero, zero_smul]
      exact hdup (fun hc => hS (key hc).2)
  · rw [sg_zero _ _ _ hF, zero_mul, Int.cast_zero, zero_smul]
    exact hdup (fun hc => hF (key hc).1)

end Main

end YoungTableau

open YoungTableau in
theorem young_holds : Young := by
  intro n M _ _ ι _ Q _ _ N tl C _ col b hT h1 h2 h3 h4 ξ h
  rw [cA_apply]
  have key : altPair tl (alt (colG col) ξ) b = ((kap tl (col ∘ inF Q N) (col ∘ inS Q N) (b ∘ inF Q N)
      (b ∘ inS Q N) : ℤ) : ℂ) • alt (colG col) ξ b := by
    rw [altPair_apply, kap, Int.cast_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [term tl col b hT h1 h2 ξ σ, smul_smul]
    push_cast
    ring_nf
  rw [h] at key
  have hk := kap_pos tl (col ∘ inF Q N) (col ∘ inS Q N) (b ∘ inF Q N) (b ∘ inS Q N) (fun k k' => h3 k k')
    (fun k k' => h4 k k') (fun k k' ht hr hc => by
      have := hT.1 (inF Q N k) (inF Q N k') ((h3 k k').mpr ⟨ht, hc⟩) hr
      simpa [inF] using this)
  exact (smul_eq_zero.mp key.symm).resolve_left (by exact_mod_cast hk.ne')

end PositivityTheory.Rg.Cz

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.KTypeHolds

section

@[expose] public section

namespace PositivityTheory.Rg.Cz

theorem kType_holds : KType := by
  have tg := tensorGl_holds
  have jm := jmComm_of tg
  have cu := curry_holds
  have qd := qdetFacts_holds
  have pq := piQdet_of tg jm
  have sf := stepFormula_of tg jm pq cu
  have sc := stepChar_of tg sf qd
  have sp := spectrum_of tg jm cu sc
  have ht := height_of tg
  have wq := wallQuot_of qd
  have ch := chain_of tg jm cu sf qd sc ht wq
  have ca := colAnti_of tg jm ht
  have tf := transFin_of tg jm sf qd sp ch ca
  have tr := trans_of tf
  have ta := transAll_of tg tr
  have tk := tensorGK_of tg
  have wa := wallAlg_of tg jm qd sp
  have li := lieInv_holds
  have co := contract_of tg qd wa tk li wq
  have sz := semiZero_of qd wa li wq
  have sa := sphAll_of swStart_holds co sz
  exact kType_of tg ta tk sa young_holds

end PositivityTheory.Rg.Cz
end
end
