module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportComp
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockGroupUnipotentDoubleCosetCellBlockDia

section

@[expose] public section

open Matrix Topology

noncomputable section

namespace GlobalTheory.JSW.Cut.Block

open GlobalTheory.JSW.KirFin GlobalTheory.SmGL

variable {F : Type} [NormedField F] {m : ℕ}

open Matrix Topology in
variable {F : Type} [NormedField F] {m : ℕ} in
theorem _root_.GlobalTheory.JSW.Cut.Block.mir_inv (a : GL (Fin m) F) (y : Fin m → F) :
    (_root_.GlobalTheory.JSW.KirFin.mir a y)⁻¹ =
      _root_.GlobalTheory.JSW.KirFin.mir a⁻¹ (-((a⁻¹).val *ᵥ y)) := by
  apply inv_eq_of_mul_eq_one_right
  rw [_root_.GlobalTheory.JSW.KirFin.mir_mul]
  simp [mulVec_neg, mulVec_mulVec, ← _root_.GlobalTheory.JSW.KirFin.mir_one]

theorem mir_left_inj {g h : GL (Fin m) F} {x y : Fin m → F} (e : mir g x = mir h y) : g = h := by
  ext i j
  have := congrArg (fun p : GL (Fin (m + 1)) F => p.val i.castSucc j.castSucc) e
  simpa using this

def blocks (U : Subgroup (GL (Fin (m + 1)) F)) : Subgroup (GL (Fin m) F) where
  carrier := {a | ∃ y, mir a y ∈ U}
  one_mem' := ⟨0, by rw [mir_one]; exact U.one_mem⟩
  mul_mem' := by
    rintro a b ⟨y, hy⟩ ⟨z, hz⟩
    exact ⟨a.val *ᵥ z + y, by rw [← mir_mul]; exact U.mul_mem hy hz⟩
  inv_mem' := by
    rintro a ⟨y, hy⟩
    exact ⟨_, by rw [← mir_inv]; exact U.inv_mem hy⟩

theorem exists_blocks_cell_cor_iff : ∀ {F : Type} [NormedField F] {m : ℕ} (U : Subgroup (GL (Fin (m + 2)) F)), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∃ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) ∧ IsOpen (B : Set (GL (Fin (m + 1)) F)) ∧ (∀ b, GlobalTheory.JSW.KirFin.cor b ∈ U → b ∈ B) ∧ ∀ h₀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.cor h ∈ GlobalTheory.JSW.Cut.cell (GlobalTheory.JSW.KirFin.cor h₀) (U : Set (GL (Fin (m + 2)) F)) ↔ h ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
  intro F _ m U hUc hUo
  refine ⟨blocks U, isCompact_blocks hUc, ?_, fun b hb => ⟨0, hb⟩, fun h₀ h => ?_⟩
  · exact Subgroup.isOpen_mono (H₁ := U.comap cor) (fun b hb => ⟨0, hb⟩) (hUo.preimage continuous_cor)
  constructor
  · rintro ⟨n, hn, u, hu, e⟩
    obtain ⟨n', x, rfl⟩ := exists_mir (lr_of_mem hn)
    have hlu : lr u = lr 1 := by
      have h1 : lr (cor h) = lr (1 * u) := by
        rw [e]
        refine lr_mul_congr ?_ u
        rw [lr_mul_congr (lr_of_mem hn) _, one_mul]
        exact lr_mir h₀ 0
      rw [one_mul] at h1
      rw [← h1]
      exact lr_mir h 0
    obtain ⟨a, y, rfl⟩ := exists_mir hlu
    refine ⟨n', mir_mem_iff.1 hn, a, ⟨y, hu⟩, ?_⟩
    change mir h 0 = mir n' x * mir h₀ 0 * mir a y at e
    rw [mir_mul, mir_mul] at e
    exact mir_left_inj e
  · rintro ⟨n', hn', a, ⟨y, hy⟩, rfl⟩
    refine ⟨mir n' (-((n' * h₀).val *ᵥ y)), mir_mem_iff.2 hn', mir a y, hy, ?_⟩
    change mir (n' * h₀ * a) 0 = mir n' _ * mir h₀ 0 * mir a y
    rw [mir_mul, mir_mul, mulVec_zero, zero_add, add_neg_cancel]

end GlobalTheory.JSW.Cut.Block
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockGroupUnipotentDoubleCosetCellBlockDiaStatement

section

@[expose] public section

open Matrix Topology

theorem _root_.GlobalTheory.T.exists_blockGroup_unipotentDoubleCosetCell_blockDiag_iff : ∀ {F : Type} [NormedField F] {m : ℕ} (U : Subgroup (GL (Fin (m + 2)) F)), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∃ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) ∧ IsOpen (B : Set (GL (Fin (m + 1)) F)) ∧ (∀ b, GlobalTheory.JSW.KirFin.cor b ∈ U → b ∈ B) ∧ ∀ h₀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.KirFin.cor h ∈ GlobalTheory.JSW.Cut.cell (GlobalTheory.JSW.KirFin.cor h₀) (U : Set (GL (Fin (m + 2)) F)) ↔ h ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F)) := by
  first | (exact @GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff) | (exact GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff) | (intros; apply GlobalTheory.JSW.Cut.Block.exists_blocks_cell_cor_iff  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentDoubleCosetCellFiniteDisjointIUnion

section

@[expose] public section

open Matrix Topology

namespace GlobalTheory.JSW.Cut

open Pointwise

variable {F : Type} [NormedField F] {n : ℕ}

theorem cell_eq_of_mem (B' : Subgroup (GL (Fin n) F)) {x y g : GL (Fin n) F}
    (hx : g ∈ cell x (B' : Set (GL (Fin n) F))) (hy : g ∈ cell y (B' : Set (GL (Fin n) F))) :
    cell x (B' : Set (GL (Fin n) F)) = cell y (B' : Set (GL (Fin n) F)) := by
  obtain ⟨u, hu, k, hk, rfl⟩ := hx
  obtain ⟨u', hu', k', hk', he⟩ := hy
  have hy' : y = (u'⁻¹ * u) * x * (k * k'⁻¹) := by
    calc y = u'⁻¹ * (u' * y * k') * k'⁻¹ := by group
      _ = (u'⁻¹ * u) * x * (k * k'⁻¹) := by rw [← he]; group
  have hx' : x = (u⁻¹ * u') * y * (k' * k⁻¹) := by
    calc x = u⁻¹ * (u * x * k) * k⁻¹ := by group
      _ = (u⁻¹ * u') * y * (k' * k⁻¹) := by rw [he]; group
  ext g
  constructor
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u⁻¹ * u'), mul_mem hv (mul_mem (inv_mem hu) hu'), k' * k⁻¹ * l,
      mul_mem (mul_mem hk' (inv_mem hk)) hl, ?_⟩
    rw [hx']; group
  · rintro ⟨v, hv, l, hl, rfl⟩
    refine ⟨v * (u'⁻¹ * u), mul_mem hv (mul_mem (inv_mem hu') hu), k * k'⁻¹ * l,
      mul_mem (mul_mem hk (inv_mem hk')) hl, ?_⟩
    rw [hy']; group

theorem cell_finite_disjoint_union (B B' : Subgroup (GL (Fin n) F)) (hB : IsCompact (B : Set (GL (Fin n) F)))
    (hB' : IsOpen (B' : Set (GL (Fin n) F))) (hle : B' ≤ B) (h₀ : GL (Fin n) F) :
    ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ cell h₀ (B : Set (GL (Fin n) F))) ∧
      cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, cell x (B' : Set (GL (Fin n) F))) ∧
      (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => cell x (B' : Set (GL (Fin n) F)) := by
  classical

  obtain ⟨t, ht⟩ := hB.elim_finite_subcover (fun b : B => (b : GL (Fin n) F) • (B' : Set (GL (Fin n) F)))
    (fun b => hB'.smul _) (fun b hb => Set.mem_iUnion.2 ⟨⟨b, hb⟩, ⟨1, one_mem _, by simp⟩⟩)
  set S : Finset (GL (Fin n) F) := t.image fun b : B => h₀ * (b : GL (Fin n) F) with hS
  have hSmem : ∀ x ∈ S, x ∈ cell h₀ (B : Set (GL (Fin n) F)) := by
    intro x hx
    obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
    exact ⟨1, one_mem _, b, b.2, by simp⟩
  have hunion : cell h₀ (B : Set (GL (Fin n) F)) = ⋃ x ∈ S, cell x (B' : Set (GL (Fin n) F)) := by
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨u, hu, k, hk, rfl⟩
      obtain ⟨b, hbt, hkb⟩ := Set.mem_iUnion₂.1 (ht hk)
      obtain ⟨k', hk', hkk⟩ := hkb
      refine ⟨h₀ * b, Finset.mem_image.2 ⟨b, hbt, rfl⟩, u, hu, k', hk', ?_⟩
      rw [← hkk]; simp [smul_eq_mul, mul_assoc]
    · rintro ⟨x, hx, u, hu, k, hk, rfl⟩
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨u, hu, b * k, mul_mem b.2 (hle hk), by simp [mul_assoc]⟩

  set f : GL (Fin n) F → Set (GL (Fin n) F) := fun x => cell x (B' : Set (GL (Fin n) F)) with hf
  set C : Finset (Set (GL (Fin n) F)) := S.image f with hC
  let rep : C → GL (Fin n) F := fun c => Classical.choose (Finset.mem_image.1 c.2)
  have rep_mem : ∀ c : C, rep c ∈ S := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).1
  have rep_eq : ∀ c : C, f (rep c) = c := fun c => (Classical.choose_spec (Finset.mem_image.1 c.2)).2
  refine ⟨C.attach.image rep, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
    exact hSmem _ (rep_mem c)
  · rw [hunion]
    ext g
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨x, hx, hg⟩
      have hc : f x ∈ C := Finset.mem_image.2 ⟨x, hx, rfl⟩
      refine ⟨rep ⟨f x, hc⟩, Finset.mem_image.2 ⟨⟨f x, hc⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
      have := rep_eq ⟨f x, hc⟩
      change g ∈ f (rep ⟨f x, hc⟩)
      rw [this]; exact hg
    · rintro ⟨x, hx, hg⟩
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨rep c, rep_mem c, hg⟩
  · intro x hx y hy hxy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
    obtain ⟨d, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    rw [Function.onFun, Set.disjoint_left]
    intro g hgc hgd
    apply hxy
    have h1 := cell_eq_of_mem B' hgc hgd
    have hcd : c = d := by
      apply Subtype.ext
      rw [← rep_eq c, ← rep_eq d]
      exact h1
    rw [hcd]

theorem cell_finite_disjoint_union' : ∀ {F : Type} [NormedField F] {n : ℕ} (B B' : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B' : Set (GL (Fin n) F)) → B' ≤ B → ∀ h₀ : GL (Fin n) F, ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F))) ∧ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F))) ∧ (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F)) :=
  fun B B' hB hB' hle h₀ => cell_finite_disjoint_union B B' hB hB' hle h₀

end GlobalTheory.JSW.Cut
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentDoubleCosetCellFiniteDisjointIUnionStatement

section

@[expose] public section

open Matrix Topology

theorem _root_.GlobalTheory.T.unipotentDoubleCosetCell_finite_disjoint_iUnion : ∀ {F : Type} [NormedField F] {n : ℕ} (B B' : Subgroup (GL (Fin n) F)), IsCompact (B : Set (GL (Fin n) F)) → IsOpen (B' : Set (GL (Fin n) F)) → B' ≤ B → ∀ h₀ : GL (Fin n) F, ∃ s : Finset (GL (Fin n) F), (∀ x ∈ s, x ∈ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F))) ∧ GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin n) F)) = (⋃ x ∈ s, GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F))) ∧ (s : Set (GL (Fin n) F)).PairwiseDisjoint fun x => GlobalTheory.JSW.Cut.cell x (B' : Set (GL (Fin n) F)) := by
  first | (exact @GlobalTheory.JSW.Cut.cell_finite_disjoint_union') | (exact GlobalTheory.JSW.Cut.cell_finite_disjoint_union') | (intros; apply GlobalTheory.JSW.Cut.cell_finite_disjoint_union'  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCutoffsOfRestrictionCutoffs

section

@[expose] public section

noncomputable section

open Matrix Topology GlobalTheory.SmGL GlobalTheory.Whittaker

namespace GlobalTheory.JSW.Cut

open GlobalTheory.JSW.KirFin

variable {F : Type} [NormedField F]

namespace Red

theorem mul_mem_cell_iff {n : ℕ} {z : GL (Fin n) F} {U : Set (GL (Fin n) F)} {u : GL (Fin n) F}
    (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) : u * g ∈ cell z U ↔ g ∈ cell z U := by
  constructor
  · rintro ⟨v, hv, k, hk, e⟩
    refine ⟨u⁻¹ * v, mul_mem (inv_mem hu) hv, k, hk, ?_⟩
    have : g = u⁻¹ * (u * g) := by group
    rw [this, e]
    simp only [mul_assoc]
  · rintro ⟨v, hv, k, hk, rfl⟩
    exact ⟨u * v, mul_mem hu hv, k, hk, by simp only [mul_assoc]⟩

theorem cell_eq_of_mem {n : ℕ} {z g : GL (Fin n) F} {U : Subgroup (GL (Fin n) F)}
    (hg : g ∈ cell z (U : Set (GL (Fin n) F))) : cell g (U : Set (GL (Fin n) F)) = cell z U := by
  obtain ⟨v, hv, k, hk, rfl⟩ := hg
  ext x
  constructor
  · rintro ⟨u, hu, k', hk', rfl⟩
    exact ⟨u * v, mul_mem hu hv, k * k', mul_mem hk hk', by simp only [mul_assoc]⟩
  · rintro ⟨u, hu, k', hk', rfl⟩
    refine ⟨u * v⁻¹, mul_mem hu (inv_mem hv), k⁻¹ * k', mul_mem (inv_mem hk) hk', ?_⟩
    group

theorem act_mul_left {ψ : AddChar F ℂ} {n : ℕ} (T : GL (Fin n) F →₀ ℂ) {f : GL (Fin n) F → ℂ} (hf : Eqv ψ f)
    {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) :
    act T f (u * g) = ψ (superDiag u) * act T f g := by
  unfold act Finsupp.sum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only
  rw [mul_assoc u g k, hf u hu, mul_left_comm]

theorem indicator_cell_mul_left {ψ : AddChar F ℂ} {n : ℕ} {z : GL (Fin n) F} {U : Set (GL (Fin n) F)}
    {f : GL (Fin n) F → ℂ} (hf : Eqv ψ f) {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) (g : GL (Fin n) F) :
    (cell z U).indicator f (u * g) = ψ (superDiag u) * (cell z U).indicator f g := by
  classical
  by_cases hg : g ∈ cell z U
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((mul_mem_cell_iff hu g).2 hg), hf u hu]
  · rw [Set.indicator_apply, Set.indicator_apply, if_neg hg, if_neg (fun h => hg ((mul_mem_cell_iff hu g).1 h)),
      mul_zero]

end Red

open Red

theorem cuts_mir_of_res : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h) → ∀ U : Subgroup (GL (Fin (m + 2)) F), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∀ z : GL (Fin (m + 2)) F, GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 2)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 2)) F))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1} := by
  intro F _ _ _ ψ _ _ m H U hUc hUo z
  classical
  by_cases hz : ∃ h₀ : GL (Fin (m + 1)) F, cor h₀ ∈ cell z (U : Set (GL (Fin (m + 2)) F))
  swap
  · refine ⟨0, fun f _ _ p hp => ?_⟩
    rw [act_zero, Set.indicator_apply, if_neg]
    intro hpc
    obtain ⟨h, x, rfl⟩ := exists_mir hp
    rw [mir_eq, mul_mem_cell_iff (mir_mem_iff.2 (one_mem _))] at hpc
    exact hz ⟨h, hpc⟩
  obtain ⟨h₀, hh₀⟩ := hz
  have hzc : cell z (U : Set (GL (Fin (m + 2)) F)) = cell (cor h₀) U := (Red.cell_eq_of_mem hh₀).symm
  obtain ⟨B, hBc, _, hUB, hcell⟩ := GlobalTheory.T.exists_blockGroup_unipotentDoubleCosetCell_blockDiag_iff U hUc hUo
  let B' : Subgroup (GL (Fin (m + 1)) F) := U.comap cor
  have hB'o : IsOpen (B' : Set (GL (Fin (m + 1)) F)) := hUo.preimage continuous_cor
  have hB'B : B' ≤ B := fun b hb => hUB b hb
  have hB'c : IsCompact (B' : Set (GL (Fin (m + 1)) F)) :=
    hBc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hB'o) hB'B
  let L : Set (Fin (m + 1) → F) := {y | mir 1 y ∈ U}
  have hL : L ∈ 𝓝 (0 : Fin (m + 1) → F) := by
    refine (hUo.preimage continuous_col).mem_nhds ?_
    show mir 1 0 ∈ U
    rw [mir_one]
    exact one_mem _
  obtain ⟨s, -, hsU, hsd⟩ := GlobalTheory.T.unipotentDoubleCosetCell_finite_disjoint_iUnion B B' hBc hB'o hB'B h₀
  choose T hT using fun x : GL (Fin (m + 1)) F => H B' hB'c hB'o L hL x
  refine ⟨∑ x ∈ s, T x, fun f hf hfU => ?_⟩
  have hB'f : ∀ b ∈ B', ∀ g, f (g * cor b) = f g := fun b hb g => hfU _ hb g
  have hLf : ∀ y ∈ L, ∀ g, f (g * mir 1 y) = f g := fun y hy g => hfU _ hy g
  have hcor : ∀ h, act (∑ x ∈ s, T x) f (cor h) = (cell z (U : Set (GL (Fin (m + 2)) F))).indicator f (cor h) := by
    intro h
    rw [act_finset_sum]
    rw [Finset.sum_congr rfl fun x _ => hT x f hf hB'f hLf h]
    rw [← Finset.indicator_biUnion_apply s _ hsd, ← hsU, hzc]
    by_cases hh : h ∈ cell h₀ (B : Set (GL (Fin (m + 1)) F))
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem ((hcell h₀ h).2 hh)]
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg hh, if_neg fun h' => hh ((hcell h₀ h).1 h')]
  intro p hp
  obtain ⟨h, x, rfl⟩ := exists_mir hp
  have hu : mir 1 x ∈ unipB F (Fin (m + 2)) := mir_mem_iff.2 (one_mem _)
  rw [mir_eq]
  show act _ f (mir 1 x * cor h) = (cell z (U : Set (GL (Fin (m + 2)) F))).indicator f (mir 1 x * cor h)
  rw [act_mul_left _ hf hu, indicator_cell_mul_left hf hu, hcor]

end GlobalTheory.JSW.Cut
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MirabolicCutoffsOfRestrictionCutoffsStatement

section

@[expose] public section

open Matrix Topology

theorem _root_.GlobalTheory.T.mirabolic_cutoffs_of_restriction_cutoffs : ∀ {F : Type} [NormedField F] [ProperSpace F] [IsUltrametricDist F] (ψ : AddChar F ℂ), IsLocallyConstant ψ → ψ ≠ 1 → ∀ m : ℕ, (∀ B : Subgroup (GL (Fin (m + 1)) F), IsCompact (B : Set (GL (Fin (m + 1)) F)) → IsOpen (B : Set (GL (Fin (m + 1)) F)) → ∀ L : Set (Fin (m + 1) → F), L ∈ nhds (0 : Fin (m + 1) → F) → ∀ h₀ : GL (Fin (m + 1)) F, ∃ T : GL (Fin (m + 2)) F →₀ ℂ, ∀ f : GL (Fin (m + 2)) F → ℂ, GlobalTheory.JSW.KirFin.Eqv ψ f → (∀ b ∈ B, ∀ g, f (g * GlobalTheory.JSW.KirFin.cor b) = f g) → (∀ y ∈ L, ∀ g, f (g * GlobalTheory.JSW.KirFin.mir 1 y) = f g) → ∀ h : GL (Fin (m + 1)) F, GlobalTheory.JSW.Cut.act T f (GlobalTheory.JSW.KirFin.cor h) = (GlobalTheory.JSW.Cut.cell h₀ (B : Set (GL (Fin (m + 1)) F))).indicator (fun h => f (GlobalTheory.JSW.KirFin.cor h)) h) → ∀ U : Subgroup (GL (Fin (m + 2)) F), IsCompact (U : Set (GL (Fin (m + 2)) F)) → IsOpen (U : Set (GL (Fin (m + 2)) F)) → ∀ z : GL (Fin (m + 2)) F, GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 2)) F)) (GlobalTheory.JSW.Cut.cell z (U : Set (GL (Fin (m + 2)) F))) {p | GlobalTheory.JSW.KirFin.lr p = GlobalTheory.JSW.KirFin.lr 1} := by
  first | exact @GlobalTheory.JSW.Cut.cuts_mir_of_res | exact GlobalTheory.JSW.Cut.cuts_mir_of_res | (intros; apply GlobalTheory.JSW.Cut.cuts_mir_of_res <;> assumption)
end
end
