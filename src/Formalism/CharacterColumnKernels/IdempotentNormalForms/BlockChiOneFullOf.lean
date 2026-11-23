module

public import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
public import Formalism.CharacterColumnKernels.StatementRho
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthEqKerAddRange
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.BlockRhoFull
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.ColKerChiOne
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerSmulLe
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf

-- Source module: Formalism.CharacterColumnKernels.IdempotentNormalForms.BlockChiOneTriv

section

@[expose] public section

open Finset

noncomputable section

namespace Formalism.NG

namespace TrivialCharacterBlockLength

section Triv

variable {O : Type*} [CommRing O] {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]

lemma length_mid_zero {H : Type*} [AddCommGroup H] [Module O H] (ρM : Representation O G M)
    (hB : ∀ x ∈ coB1 ρM, x = 0) (Ψ : H →ₗ[O] coZ1s ρM) :
    Module.length O ↥(LinearMap.range Ψ ⊓
        LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ) = 0 := by
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  have hz : ∀ z : ↥(LinearMap.range Ψ ⊓
      LinearMap.ker ((coB1 ρM).comap (coZ1s ρM).subtype).mkQ), z = 0 := by
    rintro ⟨z, hz⟩
    obtain ⟨-, hz2⟩ := Submodule.mem_inf.mp hz
    rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap, Submodule.subtype_apply] at hz2
    have h0 := hB _ hz2
    exact Subtype.ext (Subtype.ext h0)
  rw [hz a, hz b]

end Triv

lemma blockTrivAbs {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {G : Type*} [Group G] {M : Type*} [AddCommGroup M] [Module O M]
    {H : Type*} [AddCommGroup H] [Module O H]
    (ρM : Representation O G M) (hB : ∀ x ∈ coB1 ρM, x = 0) (Ψ : H →ₗ[O] coZ1s ρM)
    {ι : Type*} [DecidableEq ι] (what₂ cols : Finset ι) (D : ι → Subgroup G)
    (F : ∀ w, Submodule O (H1z (resRep ρM (D w))))
    (lenRow : ι → ℕ∞) (Q : Submodule O (H1z ρM)) (s : ℕ∞)
    (hrows : ∀ w ∈ what₂, ∃ A : Submodule O (H1z (resRep ρM (D w))),
      F w ≤ A ∧ Module.length O (A ⧸ (F w).comap A.subtype) ≤ lenRow w ∧
      ∀ h : H, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ A)
    (hcols : ∀ w ∈ cols, ∀ h : H,
      resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ F w)
    (hQ : ∀ h : H, Submodule.mkQ _ (Ψ h) ∈ Q)
    (hsel : Module.length O ↥(Q ⊓ ⨅ w ∈ what₂ ∪ cols,
      (F w).comap (resH1 ρM (D w))) ≤ s) :
    Module.length O H ≤ Module.length O (LinearMap.ker Ψ) + (s + ∑ w ∈ what₂, lenRow w) := by
  classical
  let A : ∀ w, Submodule O (H1z (resRep ρM (D w))) := fun w =>
    if hw : w ∈ what₂ then Classical.choose (hrows w hw) else F w
  have hA : ∀ w (hw : w ∈ what₂), A w = Classical.choose (hrows w hw) := fun w hw => dif_pos hw
  have hA' : ∀ w, w ∉ what₂ → A w = F w := fun w hw => dif_neg hw
  have hFA : ∀ w, F w ≤ A w := by
    intro w
    by_cases hw : w ∈ what₂
    · rw [hA w hw]; exact (Classical.choose_spec (hrows w hw)).1
    · rw [hA' w hw]
  let S : Submodule O (H1z ρM) := Q ⊓ ⨅ w ∈ what₂ ∪ cols, (A w).comap (resH1 ρM (D w))
  have hS : LinearMap.range ((Submodule.mkQ ((coB1 ρM).comap (coZ1s ρM).subtype)) ∘ₗ Ψ) ≤ S := by
    rintro _ ⟨h, rfl⟩
    refine (IdempotentNormalFormsRhoFacts.mem_sel (what₂ ∪ cols) (fun w => resH1 ρM (D w)) A Q _).mpr
      ⟨hQ h, fun w hw => ?_⟩
    by_cases hwr : w ∈ what₂
    · rw [hA w hwr]; exact (Classical.choose_spec (hrows w hwr)).2.2 h
    · rw [hA' w hwr]
      exact hcols w ((Finset.mem_union.mp hw).resolve_left hwr) h
  have hchain := lenChain O H (coZ1s ρM) (H1z ρM) Ψ _ S hS
  rw [length_mid_zero ρM hB Ψ, add_zero] at hchain
  have hSel : Module.length O S ≤ s + ∑ w ∈ what₂, lenRow w := by
    have h2 := selRelax O (H1z ρM) ι (what₂ ∪ cols) (fun w => H1z (resRep ρM (D w)))
      (fun w => resH1 ρM (D w)) F A Q hFA
    have hterm : ∀ w ∈ what₂ ∪ cols, Module.length O (A w ⧸ (F w).comap (A w).subtype) ≤
        if w ∈ what₂ then lenRow w else 0 := by
      intro w _
      by_cases hwr : w ∈ what₂
      · rw [if_pos hwr, hA w hwr]
        exact (Classical.choose_spec (hrows w hwr)).2.1
      · rw [if_neg hwr, hA' w hwr, Submodule.comap_subtype_self, Module.length_eq_zero]
    calc Module.length O S ≤ _ := h2
      _ ≤ s + ∑ w ∈ what₂ ∪ cols, (if w ∈ what₂ then lenRow w else 0) :=
          add_le_add hsel (Finset.sum_le_sum hterm)
      _ = s + ∑ w ∈ what₂, lenRow w := by
          rw [Finset.sum_ite_mem, Finset.union_inter_cancel_left]
  exact hchain.trans (add_le_add le_rfl hSel)

lemma final_arith (k X c vδ s R1 R2 : ℕ∞) (hk : k ≤ X + c * vδ) :
    k + (s + (R1 + R2)) ≤ s + X + R1 + 4 * (c + 1) * vδ + R2 := by
  calc k + (s + (R1 + R2)) ≤ (X + c * vδ) + (s + (R1 + R2)) := add_le_add hk le_rfl
    _ ≤ (X + c * vδ) + (s + (R1 + R2)) + (3 * c * vδ + 4 * vδ) := le_self_add
    _ = s + X + R1 + 4 * (c + 1) * vδ + R2 := by ring

end TrivialCharacterBlockLength

end Formalism.NG
end
end
end

-- Source module: Formalism.CharacterColumnKernels.IdempotentNormalForms.BlockChiOneFullOf

section

@[expose] public section

open Finset Classical

noncomputable section

namespace Formalism.NG

universe u₁ u₂ u₃ u₄ u₅ u₆

namespace IdempotentColumnIndexImages

lemma sum_image_colIdx {ι ι' : Type*} [Fintype ι] [DecidableEq ι'] (colIdx : ι → ι')
    (hinj : Function.Injective colIdx) (f : ι' → ℕ∞) :
    ∑ w ∈ (univ : Finset ι).image colIdx, f w = ∑ l : ι, f (colIdx l) :=
  Finset.sum_image fun _ _ _ _ h => hinj h

lemma card_image_colIdx {ι ι' : Type*} [Fintype ι] [DecidableEq ι'] (colIdx : ι → ι')
    (hinj : Function.Injective colIdx) :
    (((univ : Finset ι).image colIdx).card : ℕ∞) = (Fintype.card ι : ℕ∞) := by
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ]

end IdempotentColumnIndexImages

theorem blockChiCFull_of (hK : StatColKerChiC.{u₁, u₂, u₃, u₄, u₅}) :
    StatBlockChiCFull.{u₁, u₂, u₃, u₄, u₅, u₆} := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j Kc k0 ℓ cB sE tE
    hd hE hEE he₁ hEM hk0 hδ hτ ρM Ψ lrows qs F deg vζ Q Sha H0 cols eO vδ hH0 hl hq hcols hQ hsel
  let lenRow : ι' → ℕ∞ := fun w =>
    (if w ∈ lrows then eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) else 0) + (if w ∈ qs then vζ w else 0)
  have hrows : ∀ w ∈ lrows ∪ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B := by
    intro w hw
    by_cases hwl : w ∈ lrows
    · obtain ⟨B, h1, h2, h3⟩ := hl w hwl
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_pos hwl]
      exact le_self_add
    · have hwq : w ∈ qs := (Finset.mem_union.mp hw).resolve_left hwl
      obtain ⟨B, h1, h2, h3⟩ := hq w hwq
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_neg hwl, if_pos hwq, zero_add, le_refl]
  have hkerEq : LinearMap.ker Ψ = kerY (O := O) (M := d → KO O) r χ E e₁ δ
      (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 :=
    colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l))
      Kc k0
  have hK1 := hK O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    he₁ hEM hk0 (fun m => by rw [algebraMap_smul]; exact hδ m)
  have hsumH : ∑ l : ι, Module.length O
      (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D (colIdx l)))) ≤ ∑ w ∈ cols, H0 := by
    calc ∑ l : ι, Module.length O
          (LinearMap.ker (colDO (O := O) (M := d → KO O) r χ (D (colIdx l))))
        ≤ ∑ l : ι, H0 :=
          Finset.sum_le_sum fun l _ => hH0 (colIdx l) (Finset.mem_image_of_mem _ (Finset.mem_univ l))
      _ = ∑ w ∈ cols, H0 := (IdempotentColumnIndexImages.sum_image_colIdx colIdx hinj (fun _ => H0)).symm
  have hker' : Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, ((((fun _ => 0 : ι' → ℕ) w : ℕ) : ℕ∞) *
        (eO * (((fun _ => 0 : ι' → ℕ) w : ℕ) : ℕ∞) + vδ) + (fun _ => H0 : ι' → ℕ∞) w) +
        (cols.card : ℕ∞) * (Fintype.card d : ℕ∞) * vδ := by
    rw [hkerEq]
    refine hK1.trans ?_
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rw [show (cols.card : ℕ∞) = (Fintype.card ι : ℕ∞) from IdempotentColumnIndexImages.card_image_colIdx colIdx hinj]
    exact add_le_add hsumH le_rfl
  have hcob : ∀ (h : ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[A]
      (d → KO O)) (v : d → KO O), (Ψ h : G → (d → KO O)) = coD0 ρM v → (δO * δO) • v = 0 :=
    fun h v hv => cobColumn O A T' G (d → KO O) r χ E e₁ δ δO ι (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0 sE tE hE hEE hEM hδ hτ h v hv
  have h := blockRhoAbs O G d ρM _ Ψ δO hcob ι' (lrows ∪ qs) cols D F lenRow Q Sha ℓ
    (fun _ => 0) (fun _ => 0) (fun _ => H0) hrows hcols hQ hsel hker'
  have hsum : ∑ w ∈ lrows ∪ qs, lenRow w =
      eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + ∑ w ∈ qs, vζ w := by
    simp only [lenRow]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, Finset.mul_sum]
  refine h.trans (le_of_eq ?_)
  simp only [Nat.cast_zero, zero_mul, zero_add, Finset.sum_const, nsmul_eq_mul, hd, Nat.cast_one,
    mul_one]
  rw [hsum]
  ring

theorem blockChiOneFull_of (hK : StatColKerChiOne.{u₁, u₂, u₃, u₄, u₅}) :
    StatBlockChiOneFull.{u₁, u₂, u₃, u₄, u₅, u₆} := by
  intro O _ _ _ A T' G _ _ _ _ d _ _ _ _ _ r χ E e₁ δ δO ι _ _ ι' _ colIdx hinj D j e' Kc k0 ℓ cB
    hd hu he₁ hEM hδ hk0 ρM Ψ lrows qs F deg vζ Q vhE cols eO vδ hl hq hcols hQ hsel
  let lenRow : ι' → ℕ∞ := fun w =>
    (if w ∈ lrows then eO * (cB : ℕ∞) * ((deg w : ℕ∞) + 2) else 0) + (if w ∈ qs then vζ w else 0)
  have hrows : ∀ w ∈ lrows ∪ qs, ∃ B : Submodule O (H1z (resRep ρM (D w))), F w ≤ B ∧
      Module.length O (B ⧸ (F w).comap B.subtype) ≤ lenRow w ∧
      ∀ h, resH1 ρM (D w) (Submodule.mkQ _ (Ψ h)) ∈ B := by
    intro w hw
    by_cases hwl : w ∈ lrows
    · obtain ⟨B, h1, h2, h3⟩ := hl w hwl
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_pos hwl]
      exact le_self_add
    · have hwq : w ∈ qs := (Finset.mem_union.mp hw).resolve_left hwl
      obtain ⟨B, h1, h2, h3⟩ := hq w hwq
      refine ⟨B, h1, h2.trans ?_, h3⟩
      simp only [lenRow, if_neg hwl, if_pos hwq, zero_add, le_refl]
  have hB : ∀ x ∈ coB1 ρM, x = 0 := by
    rintro _ ⟨v, rfl⟩
    funext g
    exact (show uElt r χ g • v - v = 0 by rw [hu, sub_self])
  have h := TrivialCharacterBlockLength.blockTrivAbs ρM hB Ψ (lrows ∪ qs) cols D F lenRow Q vhE hrows hcols hQ hsel
  have hkerEq : LinearMap.ker Ψ = kerY (O := O) (M := d → KO O) r χ E e₁ δ
      (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 :=
    colPsiKer O A T' G (d → KO O) r χ E e₁ δ ι (fun l => D (colIdx l)) (fun l => j (colIdx l))
      Kc k0
  have hK1 := hK O A T' G d r χ E e₁ δ δO ι (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    ℓ (fun l => e' (colIdx l)) hu he₁ hEM (fun m => by rw [algebraMap_smul]; exact hδ m) hk0
  have hker : Module.length O (LinearMap.ker Ψ) ≤
      ∑ w ∈ cols, (eO * (e' w : ℕ∞) + 2 * vδ) + (cols.card : ℕ∞) * vδ := by
    rw [hkerEq]
    refine hK1.trans (le_of_eq ?_)
    rw [hd, Nat.cast_one, mul_one, IdempotentColumnIndexImages.card_image_colIdx colIdx hinj,
      IdempotentColumnIndexImages.sum_image_colIdx colIdx hinj (fun w => eO * (e' w : ℕ∞) + 2 * vδ)]
    simp only [one_mul]
    rfl
  have hsum : ∑ w ∈ lrows ∪ qs, lenRow w =
      eO * (cB : ℕ∞) * ∑ w ∈ lrows, ((deg w : ℕ∞) + 2) + ∑ w ∈ qs, vζ w := by
    simp only [lenRow]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem,
      Finset.union_inter_cancel_left, Finset.union_inter_cancel_right, Finset.mul_sum]
  rw [hsum] at h
  exact h.trans (TrivialCharacterBlockLength.final_arith _ _ _ _ _ _ _ hker)

theorem blockChiCFull : StatBlockChiCFull := blockChiCFull_of colKerChiC

theorem blockChiOneFull : StatBlockChiOneFull := blockChiOneFull_of colKerChiOne

end Formalism.NG
end
end
end
