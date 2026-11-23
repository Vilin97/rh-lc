module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
import Mathlib.Algebra.Module.StablyFree.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationSpanEqIdOnIrreducible

section

@[expose] public section

open scoped Matrix

namespace GlobalTheory.AugSpan

theorem exists_mem_span_sub_one_eq_id_on :
    ∀ {K : Type} [Field K] [IsAlgClosed K] {Γ : Type} [Group Γ] {m : ℕ}
      (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)),
      (∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P) →
      (∀ Q : Submodule K (Fin m → K), Q ≤ P → (∀ g, ∀ v ∈ Q, S g *ᵥ v ∈ Q) → Q = ⊥ ∨ Q = P) →
      (∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v) →
      ∃ T ∈ Submodule.span K (Set.range fun g => S g - 1), ∀ v ∈ P, T *ᵥ v = v := by
  intro K _ _ Γ _ m S P hst hirrP hnt
  classical
  set J := Submodule.span K (Set.range fun g => S g - 1) with hJ
  obtain ⟨g₀, v₀, hv₀, hne⟩ := hnt
  have hP : P ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hv₀
    apply hne
    rw [hv₀, Matrix.mulVec_zero]
  have hinv : ∀ g, ∀ v ∈ P, (Matrix.toLin' (S g)) v ∈ P :=
    fun g v hv => by rw [Matrix.toLin'_apply]; exact hst g v hv
  let r : Representation K Γ P :=
    { toFun := fun g => (Matrix.toLin' (S g)).restrict (hinv g)
      map_one' := by
        ext v i
        simp [LinearMap.restrict_apply]
      map_mul' := fun g g' => by
        ext v i
        simp [LinearMap.restrict_apply, Matrix.mulVec_mulVec] }
  have hr : ∀ g (v : P), ((r g v : P) : Fin m → K) = S g *ᵥ (v : Fin m → K) :=
    fun g v => by simp [r, LinearMap.restrict_apply]
  have hirr : r.IsIrreducible := by
    have hnt : Nontrivial (Subrepresentation r) := by
      refine ⟨⊥, ⊤, fun hbt => hP ?_⟩
      have h2 := congrArg Subrepresentation.toSubmodule hbt
      change (⊥ : Submodule K P) = ⊤ at h2
      rw [eq_bot_iff]
      intro v hv
      have : (⟨v, hv⟩ : P) ∈ (⊥ : Submodule K P) := by rw [h2]; trivial
      rw [Submodule.mem_bot] at this
      simpa using congrArg Subtype.val this
    refine ⟨fun W => ?_⟩
    have hle : W.toSubmodule.map P.subtype ≤ P := by
      rintro _ ⟨v, _, rfl⟩; exact v.2
    have hinvW : ∀ g, ∀ v ∈ W.toSubmodule.map P.subtype, S g *ᵥ v ∈ W.toSubmodule.map P.subtype := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨r g v, W.apply_mem_toSubmodule g hv, ?_⟩
      simp [hr]
    rcases hirrP _ hle hinvW with h1 | h1
    · left
      refine Subrepresentation.toSubmodule_injective (eq_bot_iff.2 fun v hv => ?_)
      have : (v : Fin m → K) ∈ W.toSubmodule.map P.subtype := ⟨v, hv, rfl⟩
      rw [h1, Submodule.mem_bot] at this
      show v ∈ (⊥ : Submodule K P)
      rw [Submodule.mem_bot]; exact Subtype.ext this
    · right
      refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun v _ => ?_)
      have : (v : Fin m → K) ∈ W.toSubmodule.map P.subtype := by rw [h1]; exact v.2
      obtain ⟨w, hw, hwv⟩ := this
      rwa [show w = v from Subtype.ext hwv] at hw
  have hs := GlobalTheory.BurnsideField.span_range_eq_top_of_isAlgClosed r hirr
  have hJl : ∀ g, ∀ T ∈ J, S g * T ∈ J := by
    intro g T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have : S g * (S h - 1) = (S (g * h) - 1) - (S g - 1) := by
        rw [map_mul, mul_sub, mul_one]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hx
  have hJr : ∀ g, ∀ T ∈ J, T * S g ∈ J := by
    intro g T hT
    induction hT using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      have : (S h - 1) * S g = (S (h * g) - 1) - (S g - 1) := by
        rw [map_mul, sub_mul, one_mul]; abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c hx
  let J' : Submodule K (Module.End K P) :=
    { carrier := {f | ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w}
      add_mem' := by
        rintro f f' ⟨T, hT, hTf⟩ ⟨T', hT', hTf'⟩
        exact ⟨T + T', J.add_mem hT hT', fun w => by
          rw [Matrix.add_mulVec, hTf, hTf']; simp⟩
      zero_mem' := ⟨0, J.zero_mem, fun w => by simp⟩
      smul_mem' := by
        rintro c f ⟨T, hT, hTf⟩
        exact ⟨c • T, J.smul_mem c hT, fun w => by
          rw [Matrix.smul_mulVec, hTf]; simp⟩ }
  have hmem : ∀ f, f ∈ J' ↔ ∃ T ∈ J, ∀ w : P, T *ᵥ (w : Fin m → K) = f w := fun f => Iff.rfl
  have hl : ∀ a : Module.End K P, ∀ f ∈ J', a * f ∈ J' := by
    intro a f hf
    have ha : a ∈ Submodule.span K (Set.range r) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨T, hT, hTf⟩ := (hmem f).1 hf
      refine (hmem _).2 ⟨S g * T, hJl g T hT, fun w => ?_⟩
      rw [← Matrix.mulVec_mulVec, hTf, Module.End.mul_apply, hr]
    | zero => rw [zero_mul]; exact J'.zero_mem
    | add x y _ _ hx hy => rw [add_mul]; exact J'.add_mem hx hy
    | smul c x _ hx => rw [smul_mul_assoc]; exact J'.smul_mem c hx
  have hrt : ∀ a : Module.End K P, ∀ f ∈ J', f * a ∈ J' := by
    intro a f hf
    have ha : a ∈ Submodule.span K (Set.range r) := by rw [hs]; trivial
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨T, hT, hTf⟩ := (hmem f).1 hf
      refine (hmem _).2 ⟨T * S g, hJr g T hT, fun w => ?_⟩
      rw [← Matrix.mulVec_mulVec, ← hr, hTf, Module.End.mul_apply]
    | zero => rw [mul_zero]; exact J'.zero_mem
    | add x y _ _ hx hy => rw [mul_add]; exact J'.add_mem hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact J'.smul_mem c hx
  set f₀ : Module.End K P := r g₀ - 1 with hf₀def
  have hf₀ : f₀ ∈ J' := (hmem _).2 ⟨S g₀ - 1, Submodule.subset_span ⟨g₀, rfl⟩, fun w => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr]; rfl⟩
  set w₀ : P := ⟨v₀, hv₀⟩ with hw₀
  have hfw : f₀ w₀ ≠ 0 := by
    intro h
    apply hne
    have h' := congrArg Subtype.val h
    rw [hf₀def, LinearMap.sub_apply, Submodule.coe_sub, hr, Submodule.coe_zero, sub_eq_zero] at h'
    exact h'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual K P, ψ (f₀ w₀) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hfw ((Module.forall_dual_apply_eq_zero_iff K _).1 hc)
  let b := Module.finBasis K P
  have hid : (1 : Module.End K P) ∈ J' := by
    have heq : (1 : Module.End K P) = ∑ i, ((ψ (f₀ w₀))⁻¹ • ψ.smulRight (b i)) * f₀ *
        ((b.coord i).smulRight w₀) := by
      ext1 w
      rw [LinearMap.sum_apply, Module.End.one_apply]
      conv_lhs => rw [← b.sum_repr w]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul,
        smul_eq_mul, smul_smul, Module.Basis.coord_apply]
      congr 1
      field_simp
    rw [heq]
    exact J'.sum_mem fun i _ => hrt _ _ (hl _ _ hf₀)
  obtain ⟨T, hT, hTid⟩ := (hmem _).1 hid
  exact ⟨T, hT, fun v hv => hTid ⟨v, hv⟩⟩

end GlobalTheory.AugSpan
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationSpanEqIdOnIrreducibleStatement

section

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.exists_augmentationSpan_eq_id_on_irreducible : ∀ {K : Type} [Field K] [IsAlgClosed K] {Γ : Type} [Group Γ] {m : ℕ} (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)), (∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P) → (∀ Q : Submodule K (Fin m → K), Q ≤ P → (∀ g, ∀ v ∈ Q, S g *ᵥ v ∈ Q) → Q = ⊥ ∨ Q = P) → (∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v) → ∃ T ∈ Submodule.span K (Set.range fun g => S g - 1), ∀ v ∈ P, T *ᵥ v = v := by
  first | exact @GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on | exact GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on | (intros; apply GlobalTheory.AugSpan.exists_mem_span_sub_one_eq_id_on <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.AugSpanOneMemOfOrthogonalThree

section

@[expose] public section

open scoped Matrix

namespace GlobalTheory.AugCore

variable {K : Type} [Field K] {Γ : Type} [Group Γ] {m : ℕ}

abbrev augSpan (S : Γ →* Matrix (Fin m) (Fin m) K) : Submodule K (Matrix (Fin m) (Fin m) K) :=
  Submodule.span K (Set.range fun g => S g - 1)

def Stable (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)) : Prop :=
  ∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P

theorem mul_mem_augSpan (S : Γ →* Matrix (Fin m) (Fin m) K) {A C : Matrix (Fin m) (Fin m) K}
    (hA : A ∈ augSpan S) (hC : C ∈ augSpan S) : A * C ∈ augSpan S := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    induction hC using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      have e : (S g - 1) * (S h - 1) = (S (g * h) - 1) - (S g - 1) - (S h - 1) := by
        rw [map_mul]; noncomm_ring
      rw [e]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
        (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul a y _ hy => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ a hx

theorem augSpan_preserves (S : Γ →* Matrix (Fin m) (Fin m) K) {P : Submodule K (Fin m → K)}
    (hP : Stable S P) {T : Matrix (Fin m) (Fin m) K} (hT : T ∈ augSpan S) :
    ∀ v ∈ P, T *ᵥ v ∈ P := by
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    intro v hv
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact P.sub_mem (hP g v hv) hv
  | zero => intro v _; rw [Matrix.zero_mulVec]; exact P.zero_mem
  | add x y _ _ hx hy => intro v hv; rw [Matrix.add_mulVec]; exact P.add_mem (hx v hv) (hy v hv)
  | smul a x _ hx => intro v hv; rw [Matrix.smul_mulVec]; exact P.smul_mem a (hx v hv)

def Good (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)) : Prop :=
  ∃ T ∈ augSpan S, ∀ v ∈ P, T *ᵥ v = v

theorem good_sup (S : Γ →* Matrix (Fin m) (Fin m) K) {L P : Submodule K (Fin m → K)}
    (hL : Stable S L) (hP : Stable S P) (gL : Good S L) (gP : Good S P) : Good S (L ⊔ P) := by
  obtain ⟨T₁, h₁, e₁⟩ := gL
  obtain ⟨T₂, h₂, e₂⟩ := gP
  refine ⟨T₁ + T₂ - T₁ * T₂, Submodule.sub_mem _ (Submodule.add_mem _ h₁ h₂)
    (mul_mem_augSpan S h₁ h₂), ?_⟩
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hTa : T₂ *ᵥ a ∈ L := augSpan_preserves S hL h₂ a ha
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
    e₁ a ha, e₂ b hb, e₁ _ hTa]
  abel

theorem good_bot (S : Γ →* Matrix (Fin m) (Fin m) K) : Good S ⊥ :=
  ⟨0, Submodule.zero_mem _, fun v hv => by
    rw [(Submodule.mem_bot K).mp hv, Matrix.mulVec_zero]⟩

theorem stable_inf (S : Γ →* Matrix (Fin m) (Fin m) K) {L P : Submodule K (Fin m → K)}
    (hL : Stable S L) (hP : Stable S P) : Stable S (L ⊓ P) :=
  fun g v hv => ⟨hL g v hv.1, hP g v hv.2⟩

theorem stable_orthogonal (S : Γ →* Matrix (Fin m) (Fin m) K)
    (B : LinearMap.BilinForm K (Fin m → K))
    (hinv : ∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) {Q : Submodule K (Fin m → K)}
    (hQ : Stable S Q) : Stable S (B.orthogonal Q) := by
  intro g v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro n hn
  have e : S g *ᵥ (S g⁻¹ *ᵥ n) = n := by
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  have := hv _ (hQ g⁻¹ n hn)
  rw [← e, hinv]
  exact this

end GlobalTheory.AugCore

namespace GlobalTheory.AugCore

variable {K : Type} [Field K] {Γ : Type} [Group Γ]

theorem inf_orthogonal_eq_bot (S : Γ →* Matrix (Fin 3) (Fin 3) K)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0)
    {Q : Submodule K (Fin 3 → K)} (hQ : Stable S Q) (hQo : Stable S (B.orthogonal Q)) :
    Q ⊓ B.orthogonal Q = ⊥ := by
  set Z := Q ⊓ B.orthogonal Q with hZ
  have hZs : Stable S Z := stable_inf S hQ hQo
  have hZle : Z ≤ B.orthogonal Z := by
    intro z hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz.2) n hn.1
  have h3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have hfo : Module.finrank K (B.orthogonal Z) = 3 - Module.finrank K Z := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB, h3]
  have hmono := Submodule.finrank_mono hZle
  by_contra hne
  obtain ⟨y, hyZ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hsp : (K ∙ y) ≤ Z := (Submodule.span_singleton_le_iff_mem y Z).mpr hyZ
  have h1 : Module.finrank K (K ∙ y) = 1 := finrank_span_singleton hy0
  have hspm := Submodule.finrank_mono hsp
  have hZ1 : Module.finrank K Z = 1 := by omega
  have heq : (K ∙ y) = Z := Submodule.eq_of_le_of_finrank_eq hsp (by rw [h1, hZ1])
  apply hiso y hy0
  · intro g
    have : S g *ᵥ y ∈ (K ∙ y) := by rw [heq]; exact hZs g y hyZ
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨c, hc.symm⟩
  · exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hyZ.2) y hyZ.1

theorem sup_orthogonal_eq_top (S : Γ →* Matrix (Fin 3) (Fin 3) K)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0)
    {Q : Submodule K (Fin 3 → K)} (hQ : Stable S Q) (hQo : Stable S (B.orthogonal Q)) :
    Q ⊔ B.orthogonal Q = ⊤ := by
  have h3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have key := Submodule.finrank_sup_add_finrank_inf_eq Q (B.orthogonal Q)
  rw [inf_orthogonal_eq_bot S B hB hiso hQ hQo, finrank_bot,
    LinearMap.BilinForm.finrank_orthogonal hB, h3] at key
  have hle := Submodule.finrank_le Q
  rw [h3] at hle
  apply Submodule.eq_top_of_finrank_eq
  rw [h3]; omega

theorem good_of_stable (S : Γ →* Matrix (Fin 3) (Fin 3) K) [IsAlgClosed K]
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hinv : ∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w)
    (hfix : ∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) :
    ∀ n, ∀ P : Submodule K (Fin 3 → K), Stable S P → Module.finrank K P = n → Good S P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hP hn
  by_cases hirr : ∀ Q : Submodule K (Fin 3 → K), Q ≤ P → Stable S Q → Q = ⊥ ∨ Q = P
  · by_cases hbot : P = ⊥
    · rw [hbot]; exact good_bot S
    · have hnt : ∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v := by
        by_contra hc
        push_neg at hc
        apply hbot
        rw [Submodule.eq_bot_iff]
        intro v hv
        exact hfix v (fun g => hc g v hv)
      exact GlobalTheory.T.exists_augmentationSpan_eq_id_on_irreducible S P hP hirr hnt
  · push_neg at hirr
    obtain ⟨Q, hQP, hQs, hQ0, hQne⟩ := hirr
    have hQo : Stable S (B.orthogonal Q) := stable_orthogonal S B hinv hQs
    set R := P ⊓ B.orthogonal Q with hR
    have hRs : Stable S R := stable_inf S hP hQo
    have htop := sup_orthogonal_eq_top S B hB hiso hQs hQo
    have hinf := inf_orthogonal_eq_bot S B hB hiso hQs hQo
    have hQR : Q ⊔ R = P := by
      apply le_antisymm (sup_le hQP inf_le_left)
      intro v hv
      have hvt : v ∈ Q ⊔ B.orthogonal Q := by rw [htop]; trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvt
      have hbP : b ∈ P := by
        have := P.sub_mem hv (hQP ha)
        simpa using this
      exact Submodule.mem_sup.mpr ⟨a, ha, b, ⟨hbP, hb⟩, rfl⟩
    have hQlt : Module.finrank K Q < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hQP hQne)
    have hRne : R ≠ P := by
      intro hRP
      apply hQ0
      rw [eq_bot_iff, ← hinf]
      intro x hx
      have : x ∈ R := by rw [hRP]; exact hQP hx
      exact ⟨hx, this.2⟩
    have hRlt : Module.finrank K R < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hRne)
    have g := good_sup S hQs hRs (ih _ hQlt Q hQs rfl) (ih _ hRlt R hRs rfl)
    rwa [hQR] at g

end GlobalTheory.AugCore

theorem GlobalTheory.augSpan_one_mem_of_orthogonal_three : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (S : Γ →* Matrix (Fin 3) (Fin 3) K) (B : LinearMap.BilinForm K (Fin 3 → K)), B.Nondegenerate → B.IsSymm → (∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) → (∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0) → (∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) → (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range fun g => S g - 1) := by
  intro K _ _ _ Γ _ S B hB _ hinv hfix hiso
  obtain ⟨T, hT, hTv⟩ := GlobalTheory.AugCore.good_of_stable S B hB hinv hfix hiso _ ⊤
    (fun _ _ _ => trivial) rfl
  have e : T = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    exact hTv v trivial
  exact (congrArg (· ∈ Submodule.span K (Set.range fun g => S g - 1)) e).mp hT
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.AugSpanOneMemOfOrthogonalThreeStatement

section

@[expose] public section

open scoped Matrix

theorem _root_.GlobalTheory.T.one_mem_span_sub_one_of_orthogonal_irreducible_three : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (S : Γ →* Matrix (Fin 3) (Fin 3) K) (B : LinearMap.BilinForm K (Fin 3 → K)), B.Nondegenerate → B.IsSymm → (∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) → (∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0) → (∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) → (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range fun g => S g - 1) := by
  first | exact @GlobalTheory.augSpan_one_mem_of_orthogonal_three | exact GlobalTheory.augSpan_one_mem_of_orthogonal_three | (intros; apply GlobalTheory.augSpan_one_mem_of_orthogonal_three <;> assumption)
end
end
