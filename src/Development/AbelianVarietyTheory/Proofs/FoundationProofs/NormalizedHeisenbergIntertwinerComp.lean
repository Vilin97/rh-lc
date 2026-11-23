module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjacentSelfDualLatticesIndexSimpleStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PerfectPairingQuotients
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumCompOfIntermediateLattiStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndex
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergSumCompOfAdjacentOfInfEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversalStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversalStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdjacentSelfDualLatticeToward

section

@[expose] public section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem index_comap_toSpanSingleton_ne_zero {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) {y : X} (hy : y ∈ B) :
    (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index ≠ 0 := by
  have h1 : (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup =
      A.toAddSubgroup.comap (LinearMap.toSpanSingleton R X y).toAddMonoidHom := rfl
  rw [h1, AddSubgroup.index_comap]
  intro h0
  refine hAB (AddSubgroup.relIndex_eq_zero_of_le_right ?_ h0)
  rintro _ ⟨r, rfl⟩
  exact B.smul_mem r hy

theorem exists_mem_maximal_annihilator {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    (A B : Submodule R X) (hAB : idx A B ≠ 0) (hBA : ¬ B ≤ A) :
    ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧ ∀ r : R, r • x ∈ A ↔ r ∈ P := by
  have hex : ∃ n, ∃ y ∈ B, y ∉ A ∧
      (A.comap (LinearMap.toSpanSingleton R X y)).toAddSubgroup.index = n := by
    obtain ⟨y, hyB, hyA⟩ := SetLike.not_le_iff_exists.1 hBA
    exact ⟨_, y, hyB, hyA, rfl⟩
  obtain ⟨x, hxB, hxA, hx⟩ := Nat.find_spec hex
  have hne := index_comap_toSpanSingleton_ne_zero A B hAB hxB
  let P : Ideal R := A.comap (LinearMap.toSpanSingleton R X x)
  have hP : ∀ r : R, r • x ∈ A ↔ r ∈ P := fun r => Iff.rfl
  have hfin : Finite (R ⧸ P) := Nat.finite_of_card_ne_zero hne
  have hprime : P.IsPrime := by
    refine ⟨fun htop => hxA ?_, fun {r s} hrs => ?_⟩
    · have : (1 : R) ∈ P := htop ▸ Submodule.mem_top
      simpa using (hP 1).2 this
    · by_contra hcon
      rw [not_or] at hcon
      have hs : s • x ∉ A := fun h => hcon.2 ((hP s).1 h)
      have hmin := Nat.find_min' hex ⟨s • x, B.smul_mem s hxB, hs, rfl⟩
      have hne' := index_comap_toSpanSingleton_ne_zero A B hAB (B.smul_mem s hxB)
      have hle : (A.comap (LinearMap.toSpanSingleton R X x)).toAddSubgroup ≤
          (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup := by
        intro a ha
        have ha' : a • x ∈ A := ha
        show a • s • x ∈ A
        rw [smul_comm]
        exact A.smul_mem s ha'
      have hmul := AddSubgroup.relIndex_mul_index hle
      rw [← hx, ← hmul] at hmin
      have h1 : (A.comap (LinearMap.toSpanSingleton R X x)).toAddSubgroup.relIndex
          (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup = 1 := by
        rw [← hmul] at hne
        have h2 := Nat.pos_of_ne_zero (left_ne_zero_of_mul hne)
        have h3 := Nat.pos_of_ne_zero hne'
        nlinarith
      rw [AddSubgroup.relIndex_eq_one] at h1
      have hr : r ∈ (A.comap (LinearMap.toSpanSingleton R X (s • x))).toAddSubgroup := by
        show r • s • x ∈ A
        rw [smul_smul]
        exact (hP _).2 hrs
      exact hcon.1 (h1 hr)
  haveI := hprime
  exact ⟨x, hxB, P, Ideal.Quotient.maximal_of_isField P (Finite.isField_of_domain _), hfin, hP⟩

theorem exists_adj_selfDual_step : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → ¬ B ≤ A → ∃ A' : Submodule R X, SelfDual γ A' ∧ Adj A A' ∧ A' ≤ (A' ⊓ A) ⊔ (A' ⊓ B) := by
  intro R X M _ _ _ _ _ σ w γ W h A B hA hB hAB hBA
  obtain ⟨x, hxB, P, hPm, hPf, hP⟩ := exists_mem_maximal_annihilator A B hAB hBA
  let T : Submodule R X := Submodule.span R {x}
  have hTB : T ≤ B := (Submodule.span_singleton_le_iff_mem x B).2 hxB
  have hxT : x ∈ T := Submodule.mem_span_singleton_self x
  let S : Submodule R X :=
    { carrier := {a | a ∈ A ∧ ∀ t ∈ T, γ a t = 1}
      add_mem' := fun {a b} ha hb => ⟨A.add_mem ha.1 hb.1, fun t ht => by
        rw [h.add_left, ha.2 t ht, hb.2 t ht, one_mul]⟩
      zero_mem' := ⟨A.zero_mem, fun t _ => h.zero_left t⟩
      smul_mem' := fun r a ha => ⟨A.smul_mem r ha.1, fun t ht => by
        rw [h.adj]
        exact ha.2 _ (T.smul_mem _ ht)⟩ }
  have hS : ∀ a, a ∈ S ↔ a ∈ A ∧ ∀ t ∈ T, γ a t = 1 := fun a => Iff.rfl
  have hSA : S ≤ A := fun a ha => ha.1
  have hidx : A.toAddSubgroup.relIndex T.toAddSubgroup ≠ 0 := fun h0 =>
    hAB (AddSubgroup.relIndex_eq_zero_of_le_right (fun t ht => hTB ht) h0)
  obtain ⟨-, hdual, -⟩ := perfect_pairing_quotients h S.toAddSubgroup A.toAddSubgroup
    A.toAddSubgroup T.toAddSubgroup (fun a ha => ⟨fun h1 => h1.2, fun h1 => ⟨ha, h1⟩⟩)
    (fun t _ => ⟨fun h1 a ha => h.iso hA ha h1,
      fun h1 => (hA t).2 fun a ha => h.swap_eq_one (h1 a ha)⟩) hidx
  refine ⟨S ⊔ T, fun y => ⟨fun hy z hz => ?_, fun hy => ?_⟩,
    ⟨x, Submodule.mem_sup_right hxT, P, hPm, hPf, hP, ?_⟩, ?_⟩
  · obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨b, hb, u, hu, rfl⟩ := Submodule.mem_sup.1 hz
    rw [h.add_left, h.add_right, h.add_right, h.iso hA ha.1 hb.1, ha.2 u hu,
      h.swap_eq_one (hb.2 t ht), h.iso hB (hTB ht) (hTB hu)]
    simp
  · obtain ⟨t, ht, hyt⟩ := hdual y fun a _ ha =>
      h.swap_eq_one (hy a (Submodule.mem_sup_left ha))
    have ht' : t ∈ T := ht
    have h1 : y + -t ∈ S := by
      refine ⟨(hA _).2 fun a ha => h.swap_eq_one ?_, fun u hu => ?_⟩
      · rw [h.add_right, h.neg_right, hyt a ha, mul_inv_cancel₀ (h.ne_zero _ _)]
      · rw [h.add_left, hy u (Submodule.mem_sup_right hu),
          h.iso hB (B.neg_mem (hTB ht')) (hTB hu), one_mul]
    exact Submodule.mem_sup.2 ⟨_, h1, t, ht', by abel⟩
  · exact sup_le_sup_right (le_inf hSA le_sup_left) _
  · exact sup_le_sup (le_inf le_sup_left hSA) (le_inf le_sup_right hTB)

end GlobalTheory.FinWeil
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdjacentSelfDualLatticeTowardStatement

section

@[expose] public section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_adjacent_selfDual_lattice_toward : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → ¬ B ≤ A → ∃ A' : Submodule R X, SelfDual γ A' ∧ Adj A A' ∧ A' ≤ (A' ⊓ A) ⊔ (A' ⊓ B) := by
  first | exact @GlobalTheory.FinWeil.exists_adj_selfDual_step | exact GlobalTheory.FinWeil.exists_adj_selfDual_step | (intros; apply GlobalTheory.FinWeil.exists_adj_selfDual_step <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndexStatement

section

@[expose] public section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.heisenberg_intertwining_sums_comp_eq_index : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → idx A B ≠ 0 → idx B A = idx A B ∧ ∀ v, Fixes W A v → sumOp W B A (sumOp W A B v) = (idx A B : ℂ) • v := by
  first | exact @GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul | exact GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul | (intros; apply GlobalTheory.FinWeil.sumOp_sumOp_eq_idx_smul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergSumCompOfAdjacentOfInfEqStatement

section

@[expose] public section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → A ⊓ C = B ⊓ C → ∀ v, Fixes W A v → sumOp W B C (sumOp W A B v) = lam (idx A B) • sumOp W A C v := by
  first | exact @GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq | exact GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq | (intros; apply GlobalTheory.FinWeil.sumOp_comp_of_adj_of_inf_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedIntertwinerCompOfAdjacentLattices

section

@[expose] public section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem idx_congr_of_inf_eq {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
    {A B C : Submodule R X} (h : A ⊓ C = B ⊓ C) : idx A C = idx B C := by
  unfold idx
  rw [← AddSubgroup.inf_relIndex_right A.toAddSubgroup, ← AddSubgroup.inf_relIndex_right B.toAddSubgroup]
  have : A.toAddSubgroup ⊓ C.toAddSubgroup = B.toAddSubgroup ⊓ C.toAddSubgroup := by
    ext x
    have := SetLike.ext_iff.1 h x
    simpa using this
  rw [this]

theorem normOp_comp_of_adj : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h lam hl A B C hA hB hC hadj hAC v hv
  obtain ⟨x, hx, P, hP, hfin, hann, hle⟩ := id hadj
  obtain ⟨hAB, hBA, -, hsB, hsA⟩ := GlobalTheory.T.adjacent_selfDual_lattices_index_simple h A B hA hB x hx P hP hfin hann hle
  have hn : Nat.card (R ⧸ P) ≠ 0 := Nat.card_pos.ne'
  have hAB0 : idx A B ≠ 0 := hAB ▸ hn
  have hBA0 : idx B A ≠ 0 := hBA ▸ hn
  have hBC0 : idx B C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hBA0 hAC
  have hsq : lam (idx A B) ^ 2 = (idx A B : ℂ) := by
    rw [hAB]; exact (hl.2 P hP hfin).1
  have lAB := hl.1 _ hAB0
  have lBC := hl.1 _ hBC0
  have lAC := hl.1 _ hAC
  have homBC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h B C hC).2.1 hBC0).2.2
  have homAC := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A C hC).2.1 hAC).2.2
  have fixB := ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A B hB).2.1 hAB0).2.1 v hv
  unfold normOp
  rw [homBC, smul_smul]
  by_cases h1 : B ⊓ C ≤ A
  · by_cases h2 : A ⊓ C ≤ B
    · have he : A ⊓ C = B ⊓ C :=
        le_antisymm (le_inf h2 inf_le_right) (le_inf h1 inf_le_right)
      rw [GlobalTheory.T.heisenbergSum_comp_of_adjacent_of_inf_eq h lam hl A B C hA hB hC hadj hAC he v hv, smul_smul, ← idx_congr_of_inf_eq he]
      congr 1
      field_simp
    · have hT : A ⊓ B ⊔ A ⊓ C = A := by
        rcases hsA (A ⊓ B ⊔ A ⊓ C) le_sup_left (sup_le inf_le_left inf_le_left) with h3 | h3
        · exact absurd (le_sup_right.trans h3) h2
        · exact h3
      obtain ⟨hi, hs⟩ := GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h B A C hB hA hC hBA0 hAC hT.ge
      rw [← hs _ fixB, (GlobalTheory.T.heisenberg_intertwining_sums_comp_eq_index h A B hA hB hAB0).2 v hv, homAC, smul_smul, hi,
        hBA.trans hAB.symm, map_mul, ← hsq]
      congr 1
      field_simp
  · have hT : A ⊓ B ⊔ B ⊓ C = B := by
      rcases hsB (A ⊓ B ⊔ B ⊓ C) le_sup_left (sup_le inf_le_right inf_le_left) with h3 | h3
      · exact absurd (le_sup_right.trans h3) h1
      · exact h3
    obtain ⟨hi, hs⟩ := GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h A B C hA hB hC hAB0 hBC0 (by rw [inf_comm B A]; exact hT.ge)
    rw [hs v hv, hi, map_mul]
    congr 1
    field_simp

end GlobalTheory.FinWeil
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedIntertwinerCompOfAdjacentLatticesStatement

section

@[expose] public section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.normalizedIntertwiner_comp_of_adjacent_lattices : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → Adj A B → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  first | exact @GlobalTheory.FinWeil.normOp_comp_of_adj | exact GlobalTheory.FinWeil.normOp_comp_of_adj | (intros; apply GlobalTheory.FinWeil.normOp_comp_of_adj <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedHeisenbergIntertwinerComp

section

@[expose] public section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem normOp_comp : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ (A B C : Submodule R X), SelfDual γ A → SelfDual γ B → SelfDual γ C → idx A B ≠ 0 → idx A C ≠ 0 → ∀ v, Fixes W A v → normOp lam W B C (normOp lam W A B v) = normOp lam W A C v := by
  intro R X M _ _ _ _ _ σ w γ W h lam hlam A B C hA hB hC hAB hAC v hv
  induction hn : idx A B using Nat.strong_induction_on generalizing A v with
  | _ n ih =>
  by_cases hle : B ≤ A
  · have hAB' : A = B := by
      refine le_antisymm (fun x hx => (hB x).2 fun b hb => h.iso hA hx (hle hb)) hle
    subst hAB'
    obtain ⟨h1, h2⟩ := (GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A A hA).2.2 le_rfl
    have : normOp lam W A A v = v := by
      rw [normOp, h1, map_one, inv_one, one_smul, h2 v hv]
    rw [this]
  · obtain ⟨A', hA', hadj, hbet⟩ := GlobalTheory.T.exists_adjacent_selfDual_lattice_toward h A B hA hB hAB hle
    obtain ⟨x, hx, P, hP, hfin, hann, hgen⟩ := id hadj
    obtain ⟨e1, e2, -⟩ := GlobalTheory.T.adjacent_selfDual_lattices_index_simple h A A' hA hA' x hx P hP hfin hann hgen
    have hcard : 1 < Nat.card (R ⧸ P) := by
      haveI : Nontrivial (R ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
      exact Finite.one_lt_card
    have hAA' : idx A A' ≠ 0 := by omega
    have hA'A : idx A' A ≠ 0 := by omega
    have hA'B : idx A' B ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hA'A hAB
    have hA'C : idx A' C ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hA'A hAC
    have hmul := (GlobalTheory.T.heisenbergIntertwiningSum_comp_of_intermediate_lattice h A A' B hA hA' hB hAA' hA'B hbet).1
    have hlt : idx A' B < n := by
      rw [← hn, hmul, e1]
      exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hA'B) hcard
    have hfix : Fixes W A' (normOp lam W A A' v) := by
      intro a ha
      rw [normOp, map_smul, ((GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le h A A' hA').2.1 hAA').2.1 v hv a ha]
    rw [← GlobalTheory.T.normalizedIntertwiner_comp_of_adjacent_lattices h lam hlam A A' B hA hA' hB hadj hAB v hv,
      ih _ hlt A' hA' hA'B hA'C _ hfix rfl,
      GlobalTheory.T.normalizedIntertwiner_comp_of_adjacent_lattices h lam hlam A A' C hA hA' hC hadj hAC v hv]

end GlobalTheory.FinWeil
end
end
