module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.StepFormula
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllB
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllA
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAllC

section

@[expose] public section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TA

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]
  {ι : Type} [DecidableEq ι] (lab : P → ι) (τ₀ : ι)

def labR : {p // ¬ lab p = τ₀} → {τ // τ ≠ τ₀} := fun p => ⟨lab p.1, p.2⟩

theorem conj_tensor_entry_base (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (tE Finset.univ (fun a b => lift (F a b)) c d) =
      tE (fib lab τ₀) F c d := by
  refine LinearMap.ext fun f => ?_
  rw [cj_apply]
  apply (spl (n := n) (M := M) fun p => lab p = τ₀).injective
  have h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ₀) = Finset.univ := by
    ext x
    simp [fib, Finset.mem_subtype, x.2]
  have h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ₀) = ∅ := by
    ext x
    simp [fib, Finset.mem_subtype, x.2]
  rw [LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]

theorem conj_tensor_entry_fibre (τ : {τ // τ ≠ τ₀}) (F : Fin n → Fin n → Module.End ℂ M) (c d : Fin n) :
    cj (spl (n := n) (M := M) fun p => lab p = τ₀) (lift (tE (fib (labR lab τ₀) τ) F c d)) =
      tE (fib lab τ.1) F c d := by
  refine LinearMap.ext fun f => ?_
  rw [cj_apply]
  apply (spl (n := n) (M := M) fun p => lab p = τ₀).injective
  have h1 : Finset.subtype (fun p => lab p = τ₀) (fib lab τ.1) = ∅ := by
    ext x
    simp only [Finset.mem_subtype, fib, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false]
    rw [x.2]
    exact fun h => τ.2 h.symm
  have h2 : Finset.subtype (fun p => ¬ lab p = τ₀) (fib lab τ.1) = fib (labR lab τ₀) τ := by
    ext x
    simp [fib, labR, Finset.mem_subtype, Subtype.ext_iff]
  rw [LinearEquiv.apply_symm_apply, spl_tE, h1, h2, tE_empty]

omit [DecidableEq P] in
theorem card_R (τ : {τ // τ ≠ τ₀}) (co : P → Fin n) (k : Fin n) :
    (Finset.univ.filter fun p : {p // ¬ lab p = τ₀} => labR lab τ₀ p = τ ∧ co p.1 = k).card =
      (Finset.univ.filter fun p => lab p = τ.1 ∧ co p = k).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff] at hp ⊢
    exact hp
  · intro p _ q _ h
    exact Subtype.ext h
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨⟨p, fun h => τ.2 (hp.1.symm.trans h)⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, labR, Subtype.ext_iff]
    exact hp

omit [Fintype P] in
theorem base (E : ι → Fin n → Fin n → Module.End ℂ M) (l : ι → Fin n → ℤ)
    (hl : ∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) (ℓ : M →ₗ[ℂ] ℂ) (hℓ : ℓ ≠ 0) [Fintype P] [IsEmpty P]
    {C : Type} [DecidableEq C] (col : P → C) (b co : P → Fin n) :
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) •
          (ℓ ∘ₗ cA col b ∘ₗ S) := by
  have hfib : ∀ τ, fib lab τ = ∅ := fun τ => Finset.eq_empty_of_isEmpty _
  have hG : colG col = {1} := by
    ext σ
    simp [colG, Subsingleton.elim σ 1]
  obtain ⟨m, hm⟩ : ∃ m, ℓ m ≠ 0 := by
    by_contra h
    push_neg at h
    exact hℓ (LinearMap.ext h)
  refine ⟨1, Subalgebra.one_mem _, ?_, ?_⟩
  · intro h
    apply hm
    have := LinearMap.congr_fun h (fun _ => m)
    simpa [cA, alt, hG, pm] using this
  · intro τ u
    have hc := qdet_lift (P := P) (E τ) (fun k => (l τ k : ℂ)) (hl τ) u
    simp only [hfib, tE_empty]
    rw [hc, Algebra.algebraMap_eq_smul_one, LinearMap.comp_smul]
    simp
    rfl

end PositivityTheory.Rg.Cz.TA

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAll

section

@[expose] public section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TA

def TAk (N : ℕ) : Prop := ∀ (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ι : Type) [Fintype ι] [DecidableEq ι]
  (E : ι → Fin n → Fin n → Module.End ℂ M), (∀ τ, GlRel (E τ)) →
  (∀ τ τ', τ ≠ τ' → ∀ a b c d, Commute (E τ a b) (E τ' c d)) →
  ∀ (l : ι → Fin n → ℤ), (∀ τ, HasChar (E τ) fun k => (l τ k : ℂ)) → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ ≠ 0 → (∀ τ, IsWh (E τ) ℓ) →
  ∀ (P : Type) [Fintype P] [DecidableEq P], Fintype.card P = N →
  ∀ (lab : P → ι) (C : Type) [DecidableEq C] (col : P → C) (b co : P → Fin n),
    (∀ p q, col p = col q → lab p = lab q) → IsTab col b → (∀ p q, col p = col q → co p = co q → p = q) →
    ∃ S ∈ envAlg (fun τ => tE (fib lab τ) (E τ)), ℓ ∘ₗ cA col b ∘ₗ S ≠ 0 ∧ ∀ τ (u : ℂ),
      (ℓ ∘ₗ cA col b ∘ₗ S) ∘ₗ qdet (tE (fib lab τ) (E τ)) u =
        (∏ k, (u + l τ k + ((Finset.univ.filter fun p => lab p = τ ∧ co p = k).card : ℂ))) • (ℓ ∘ₗ cA col b ∘ₗ S)

theorem main (hT : Trans) (N : ℕ) : TAk N := by
  refine Nat.strong_induction_on N ?_
  intro N ih
  intro n M _ _ ι _ _ E hG hC l hl ℓ hℓ hW P _ _ hN lab C _ col b co hcl htab hinj
  rcases isEmpty_or_nonempty P with hP | ⟨⟨p0⟩⟩
  · exact base lab E l hl ℓ hℓ col b co
  obtain ⟨τ0, hp0⟩ : ∃ τ0, lab p0 = τ0 := ⟨_, rfl⟩
  have hcard : Fintype.card {p : P // ¬ lab p = τ0} < N := by
    rw [← hN]
    exact Fintype.card_subtype_lt (p := fun p => ¬ lab p = τ0) (x := p0) (fun h => h hp0)
  obtain ⟨S1, hS1, hne1, hev1⟩ := ih _ hcard n M {τ : ι // τ ≠ τ0} (fun τ => E τ) (fun τ => hG τ)
    (fun τ τ' h => hC τ τ' (fun e => h (Subtype.ext e))) (fun τ => l τ) (fun τ => hl τ) ℓ hℓ
    (fun τ => hW τ) {p : P // ¬ lab p = τ0} rfl (labR lab τ0) C (fun p => col p) (fun p => b p)
    (fun p => co p) (fun p q h => Subtype.ext (hcl p q h))
    ⟨fun p q h1 h2 => Subtype.ext (htab.1 _ _ h1 h2), fun p i hi => by
      obtain ⟨r, hr1, hr2⟩ := htab.2 p i hi
      exact ⟨⟨r, by rw [hcl r p hr1]; exact p.2⟩, hr1, hr2⟩⟩
    (fun p q h1 h2 => Subtype.ext (hinj _ _ h1 h2))
  unfold envAlg at hS1
  have hWh1 : IsWh (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c))
      (ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) := by
    obtain ⟨ψ, h1, h2, h3⟩ := hW τ0
    refine ⟨ψ, h1, h2, fun a c hac => ?_⟩
    have hcomm : Commute S1 (lift (E τ0 a c)) := comm_of_mem_adjoin hS1 (by
      rintro T ⟨τ, c', d', rfl⟩
      exact tE_comm_lift _ _ _ (fun x y => hC τ τ0 τ.2 x y a c) c' d')
    have e2 := cA_lift (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) (E τ0 a c)
    apply LinearMap.ext
    intro F
    have := LinearMap.congr_fun hcomm.eq F
    have h3' := LinearMap.congr_fun (h3 a c hac)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.mul_apply] at this h3' ⊢
    rw [this, ← LinearMap.comp_apply (cA _ _) (lift _), e2, LinearMap.comp_apply, h3']
  have hWh1' := hWh1
  obtain ⟨S0, hS0, hne0, hev0⟩ := hT n (TV n M {p : P // ¬ lab p = τ0})
    (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c))
    (by have := glRel_map (liftA n M {p : P // ¬ lab p = τ0}) (E τ0) (hG τ0); simpa only [liftA_apply] using this)
    (l τ0) (qdet_lift _ _ (hl τ0)) _ hne1 hWh1 {p : P // lab p = τ0} C (fun p => col p) (fun p => b p) (fun p => co p)
    ⟨fun p q h1 h2 => Subtype.ext (htab.1 _ _ h1 h2), fun p i hi => by
      obtain ⟨r, hr1, hr2⟩ := htab.2 p i hi
      exact ⟨⟨r, by rw [hcl r p hr1]; exact p.2⟩, hr1, hr2⟩⟩
    (fun p q h1 h2 => Subtype.ext (hinj _ _ h1 h2))
  unfold envAlg at hS0
  have hcAl : ∀ (B : Module.End ℂ (TV n M {p : P // ¬ lab p = τ0})) (z : TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}),
      cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) (lift B z) = B (cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) z) := fun B z => LinearMap.congr_fun (cA_lift _ _ B) z
  have hkey : ∀ Y : Module.End ℂ (TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}),
      (ℓ ∘ₗ cA col b ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0)) ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) Y =
        (((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ Y) ∘ₗ (spl (n := n) (M := M) (fun p : P => lab p = τ0)).toLinearMap := by
    intro Y
    apply LinearMap.ext
    intro F
    simp only [LinearMap.comp_apply, cj_apply, LinearEquiv.apply_symm_apply, Module.End.mul_apply, LinearEquiv.coe_coe]
    rw [cA_split (fun p => lab p = τ0) col (fun p p' h => by rw [hcl p p' h]) b]
    simp only [LinearEquiv.apply_symm_apply, Module.End.mul_apply]
    rw [hcAl]
  have hkey0 : ℓ ∘ₗ cA col b ∘ₗ cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0) =
        ((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ (spl (n := n) (M := M) (fun p : P => lab p = τ0)).toLinearMap := by
    apply LinearMap.ext
    intro F
    simp only [LinearMap.comp_apply, cj_apply, LinearEquiv.apply_symm_apply, Module.End.mul_apply, LinearEquiv.coe_coe]
    rw [cA_split (fun p => lab p = τ0) col (fun p p' h => by rw [hcl p p' h]) b]
    simp only [LinearEquiv.apply_symm_apply, Module.End.mul_apply]
    rw [hcAl]
  refine ⟨cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) S1 * S0), ?_, ?_, ?_⟩
  · unfold envAlg
    rw [map_mul]
    apply Subalgebra.mul_mem
    · have hsub : Algebra.adjoin ℂ {T : Module.End ℂ (TV n M {p : P // ¬ lab p = τ0}) | ∃ (τ : {τ : ι // τ ≠ τ0}) (a c : Fin n),
          T = tE (fib (labR lab τ0) τ) (E τ) a c} ≤
          (Algebra.adjoin ℂ {T : Module.End ℂ (TV n M P) | ∃ (τ : ι) (a c : Fin n), T = tE (fib lab τ) (E τ) a c}).comap
            ((cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))).comp (liftA n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0})) := by
        apply Algebra.adjoin_le
        rintro T ⟨τ, c, d, rfl⟩
        simp only [SetLike.mem_coe, Subalgebra.mem_comap, AlgHom.comp_apply, liftA_apply]
        rw [conj_tensor_entry_fibre]
        exact Algebra.subset_adjoin ⟨τ, c, d, rfl⟩
      have := hsub hS1
      simpa only [Subalgebra.mem_comap, AlgHom.comp_apply, liftA_apply] using this
    · have hsub : Algebra.adjoin ℂ {T : Module.End ℂ (TV n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0}) | ∃ (_ : Unit) (a c : Fin n),
          T = tE Finset.univ (fun a c => lift (P := {p : P // ¬ lab p = τ0}) (E τ0 a c)) a c} ≤
          (Algebra.adjoin ℂ {T : Module.End ℂ (TV n M P) | ∃ (τ : ι) (a c : Fin n), T = tE (fib lab τ) (E τ) a c}).comap
            (cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))) := by
        apply Algebra.adjoin_le
        rintro T ⟨_, c, d, rfl⟩
        simp only [SetLike.mem_coe, Subalgebra.mem_comap]
        rw [conj_tensor_entry_base]
        exact Algebra.subset_adjoin ⟨τ0, c, d, rfl⟩
      exact hsub hS0
  · rw [hkey0]
    intro h
    apply hne0
    apply LinearMap.ext
    intro G
    have := LinearMap.congr_fun h ((spl (n := n) (M := M) (fun p : P => lab p = τ0)).symm G)
    simpa using this
  · intro τ u
    by_cases hτ : τ = τ0
    · subst hτ
      have hq : qdet (tE (fib lab τ) (E τ)) u =
          cj (spl (n := n) (M := M) (fun p : P => lab p = τ)) (qdet (tE Finset.univ (fun a c => lift (P := {p : P // ¬ lab p = τ}) (E τ a c))) u) := by
        rw [qdet_map']
        simp only [conj_tensor_entry_base]
      rw [hq, hkey, hev0 u, LinearMap.smul_comp, ← hkey0]
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      congr 2
      exact card_sub (fun p : P => lab p = τ) (fun p => co p = k)
    · have hq : qdet (tE (fib lab τ) (E τ)) u =
          cj (spl (n := n) (M := M) (fun p : P => lab p = τ0)) (lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) := by
        have := qdet_map' ((cj (spl (n := n) (M := M) (fun p : P => lab p = τ0))).comp (liftA n (TV n M {p : P // ¬ lab p = τ0}) {p : P // lab p = τ0})) (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u
        simp only [AlgHom.comp_apply, liftA_apply, conj_tensor_entry_fibre] at this
        exact this.symm
      have hcQ : Commute S0 (lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) :=
        comm_of_mem_adjoin hS0 (by
          rintro T ⟨_, c, d, rfl⟩
          exact tE_comm_lift _ _ _ (fun x y => (qdet_commute _ u _ (fun a' c' =>
            tE_comm_lift _ _ _ (fun x' y' => hC τ τ0 hτ x' y' x y) a' c')).symm) c d)
      have hmid : (((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0) ∘ₗ lift (P := {p : P // lab p = τ0}) (qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u)) =
          ((ℓ ∘ₗ cA (fun p : {p : P // ¬ lab p = τ0} => col p) (fun p => b p) ∘ₗ S1) ∘ₗ qdet (tE (fib (labR lab τ0) ⟨τ, hτ⟩) (E τ)) u) ∘ₗ cA (M := TV n M {p : P // ¬ lab p = τ0}) (fun p : {p : P // lab p = τ0} => col p) (fun p => b p) ∘ₗ S0 := by
        apply LinearMap.ext
        intro F
        have := LinearMap.congr_fun hcQ.eq F
        simp only [LinearMap.comp_apply, Module.End.mul_apply] at this ⊢
        rw [this, hcAl]
      rw [hq, hkey, hmid, hev1 ⟨τ, hτ⟩ u, LinearMap.smul_comp, LinearMap.smul_comp, ← hkey0]
      congr 1
      apply Finset.prod_congr rfl
      intro k _
      rw [card_R]

end TA

theorem transAll_of (_h1 : TensorGl) (h2 : Trans) : TransAll := by
  intro n M _ _ ι _ _ E hE hC l hl ℓ hℓ hW P _ _ lab C _ col b co h1' h2' h3'
  exact TA.main h2 (Fintype.card P) n M ι E hE hC l hl ℓ hℓ hW P rfl lab C col b co h1' h2' h3'

end PositivityTheory.Rg.Cz

end
end
end
