import Mathlib

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory
namespace OrbitUnfold

variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H}

def pull (𝓕 : Set H) (g : H) : Set H := (fun h => g * h) ⁻¹' 𝓕

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull (hF : IsFundamentalDomain Γ 𝓕 ν) (g : H) :
    NullMeasurableSet (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 g) ν :=
  hF.nullMeasurableSet.preimage (measurePreserving_mul_left ν g).quasiMeasurePreserving

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.aedisjoint_pull (hF : IsFundamentalDomain Γ 𝓕 ν) {a b : Γ}
    (hab : a ≠ b) :
    AEDisjoint ν (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (a : H)) (_root_.GlobalTheory.OrbitUnfold.pull 𝓕 (b : H)) := by
  have key : ∀ c : Γ, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (c : H) = c⁻¹ • 𝓕 := fun c => by
    ext x
    simp [_root_.GlobalTheory.OrbitUnfold.pull, Set.mem_smul_set_iff_inv_smul_mem, Subgroup.smul_def]
  rw [key, key]
  exact hF.aedisjoint (inv_injective.ne hab)

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.setIntegral_pull (g : H) (f : H → ℂ) :
    ∫ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫ h in 𝓕, f h ∂ν :=
  (measurePreserving_mul_left ν g).setIntegral_preimage_emb (measurableEmbedding_mulLeft g) f 𝓕

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
theorem _root_.GlobalTheory.OrbitUnfold.setLIntegral_pull (g : H) (f : H → ℝ≥0∞) :
    ∫⁻ h in _root_.GlobalTheory.OrbitUnfold.pull 𝓕 g, f (g * h) ∂ν = ∫⁻ h in 𝓕, f h ∂ν :=
  (measurePreserving_mul_left ν g).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulLeft g) f 𝓕

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in

theorem _root_.GlobalTheory.OrbitUnfold.isFundamentalDomain_iUnion_pull (hF : IsFundamentalDomain Γ 𝓕 ν)
    (y₀ : Y) {O : Set Y}
    [Countable O] (hO : ∀ γ : Γ, γ • y₀ ∈ O) (σ : O → Γ) (hσ : ∀ a : O, σ a • y₀ = a) :
    IsFundamentalDomain ((MulAction.stabilizer Γ y₀).map Γ.subtype)
      (⋃ a : O, _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H)) ν where
  nullMeasurableSet := .iUnion fun a => _root_.GlobalTheory.OrbitUnfold.nullMeasurableSet_pull hF _
  ae_covers := by
    filter_upwards [hF.ae_covers] with x ⟨γ, hγ⟩
    let a : O := ⟨γ • y₀, hO γ⟩
    have hs : (σ a)⁻¹ * γ ∈ MulAction.stabilizer Γ y₀ := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff, hσ a]
    refine ⟨⟨Γ.subtype ((σ a)⁻¹ * γ), Subgroup.mem_map_of_mem _ hs⟩, Set.mem_iUnion.2 ⟨a, ?_⟩⟩
    simpa [_root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def, mul_assoc] using hγ
  aedisjoint := by
    rintro ⟨_, s, hs, rfl⟩ ⟨_, t, ht, rfl⟩ hst
    have hset : ∀ (u : Γ) (hu : u ∈ MulAction.stabilizer Γ y₀) (a : O),
        (⟨Γ.subtype u, Subgroup.mem_map_of_mem _ hu⟩ :
            (MulAction.stabilizer Γ y₀).map Γ.subtype) •
          _root_.GlobalTheory.OrbitUnfold.pull 𝓕 (σ a : H) = (σ a * u⁻¹)⁻¹ • 𝓕 := by
      intro u hu a
      ext x
      simp [Set.mem_smul_set_iff_inv_smul_mem, _root_.GlobalTheory.OrbitUnfold.pull, Subgroup.smul_def,
        mul_assoc]
    simp only [Function.onFun, Set.smul_set_iUnion, hset s hs, hset t ht]
    refine AEDisjoint.iUnion_left_iff.2 fun a => AEDisjoint.iUnion_right_iff.2 fun b => ?_
    refine hF.aedisjoint (inv_injective.ne fun h => hst ?_)
    have hab : a = b := by
      apply Subtype.ext
      have h1 := congrArg (· • y₀) h
      simp only [mul_smul] at h1
      rwa [inv_smul_eq_iff.2 hs.symm, inv_smul_eq_iff.2 ht.symm, hσ, hσ] at h1
    subst hab
    have : s = t := inv_injective (mul_left_cancel h)
    subst this
    rfl

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in
private theorem selfEquivSigmaOrbits_symm_mk {G X : Type} [Group G] [MulAction G X]
    (ω : MulAction.orbitRel.Quotient G X) (x : MulAction.orbit G ω.out) :
    (MulAction.selfEquivSigmaOrbits G X).symm ⟨ω, x⟩ = x := rfl

open MeasureTheory Set in
open scoped ENNReal Pointwise in
variable {H : Type} [Group H] [MeasurableSpace H] [MeasurableMul H] {ν : Measure H}
  [ν.IsMulLeftInvariant] {Γ : Subgroup H} {Y : Type} [MulAction Γ Y] {𝓕 : Set H} in

theorem _root_.GlobalTheory.OrbitUnfold.tsum_setIntegral_eq_zero :
    ∀ (H : Type) [Group H] [MeasurableSpace H] [MeasurableMul H] (ν : Measure H)
      [ν.IsMulLeftInvariant] (Γ : Subgroup H) [Countable Γ] (Y : Type) [Countable Y]
      [MulAction Γ Y] (𝓕 : Set H), IsFundamentalDomain Γ 𝓕 ν → ∀ Φ : Y → H → ℂ,
      (∀ y, Measurable (Φ y)) → (∀ (γ : Γ) y h, Φ (γ • y) ((γ : H) * h) = Φ y h) →
      ∑' y, ∫⁻ h in 𝓕, ‖Φ y h‖ₑ ∂ν ≠ ⊤ →
      (∀ y (𝓖 : Set H), IsFundamentalDomain ((MulAction.stabilizer Γ y).map Γ.subtype) 𝓖 ν →
        IntegrableOn (Φ y) 𝓖 ν → ∫ h in 𝓖, Φ y h ∂ν = 0) →
      ∑' y, ∫ h in 𝓕, Φ y h ∂ν = 0 := by sorry


















































end OrbitUnfold
end GlobalTheory
