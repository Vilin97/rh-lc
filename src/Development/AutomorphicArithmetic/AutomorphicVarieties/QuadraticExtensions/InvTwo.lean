module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ExtTwo

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.extTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U V : Subgroup Γ) (S : Set Γ) (h : U ≤ V) (σ : Γ) (hσ : σ ∈ V) (h2 : σ * σ ∈ U), IsOpen (U.subgroupOf V : Set V) → U.relIndex V = 2 → σ ∉ U → (∀ s ∈ S, s ∈ V → s ∈ U) →
      ∀ φ ∈ CharOff U S 2, (∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ u' = φ u) → φ ⟨σ * σ, h2⟩ = 0 →
      ∃ ψ ∈ CharOff V S 2, ψ ⟨σ, hσ⟩ = 0 ∧ ∀ u : U, ψ ⟨u.1, h u.2⟩ = φ u := by
  intro Γ _ _ _ U V S h σ hσ h2 hopen hidx hσU hS φ hφ hinv hσσ
  classical
  obtain ⟨hlc, hadd, hoff⟩ := hφ
  have key : ∀ a b : Γ, a ∈ V → b ∈ V → (a * b ∈ U ↔ (a ∈ U ↔ b ∈ U)) := by
    intro a b ha hb
    have := Subgroup.mul_mem_iff_of_index_two (H := U.subgroupOf V) hidx (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)
    simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] using this
  have hσi : σ⁻¹ ∉ U := fun hh => hσU (by simpa using U.inv_mem hh)
  let Φ : Γ → ZMod 2 := fun g => if hg : g ∈ U then φ ⟨g, hg⟩ else 0
  have hΦ : ∀ g (hg : g ∈ U), Φ g = φ ⟨g, hg⟩ := fun g hg => dif_pos hg
  have hΦadd : ∀ a b, a ∈ U → b ∈ U → Φ (a * b) = Φ a + Φ b := by
    intro a b ha hb
    rw [hΦ a ha, hΦ b hb, hΦ _ (U.mul_mem ha hb), ← hadd]
    rfl
  have hR : ∀ a, a ∈ V → a ∉ U → a * σ ∈ U := fun a ha haU =>
    (key a σ ha hσ).2 (by simp [haU, hσU])
  have hL : ∀ a, a ∈ V → a ∉ U → σ⁻¹ * a ∈ U := fun a ha haU =>
    (key σ⁻¹ a (V.inv_mem hσ) ha).2 (by simp [haU, hσi])
  have hconj : ∀ a, a ∈ U → σ⁻¹ * a * σ ∈ U := by
    intro a ha
    refine hR _ (V.mul_mem (V.inv_mem hσ) (h ha)) ?_
    rw [key _ _ (V.inv_mem hσ) (h ha)]
    simp [ha, hσi]
  have hΦconj : ∀ a, a ∈ U → Φ (σ⁻¹ * a * σ) = Φ a := by
    intro a ha
    rw [hΦ a ha, hΦ _ (hconj a ha)]
    exact hinv _ _ rfl
  have hΦσ : Φ (σ * σ) = 0 := by rw [hΦ _ h2, hσσ]
  let ψ : V → ZMod 2 := fun v => if v.1 ∈ U then Φ v.1 else Φ (v.1 * σ)
  have hψU : ∀ v : V, v.1 ∈ U → ψ v = Φ v.1 := fun v hv => if_pos hv
  have hψN : ∀ v : V, v.1 ∉ U → ψ v = Φ (v.1 * σ) := fun v hv => if_neg hv
  have hψadd : ∀ a b : V, ψ (a * b) = ψ a + ψ b := by
    intro a b
    have hk := key a.1 b.1 a.2 b.2
    by_cases ha : a.1 ∈ U <;> by_cases hb : b.1 ∈ U
    · rw [hψU a ha, hψU b hb, hψU (a * b) (U.mul_mem ha hb)]
      exact hΦadd _ _ ha hb
    · have hab : (a * b).1 ∉ U := fun hh => hb ((hk.1 hh).1 ha)
      rw [hψU a ha, hψN b hb, hψN _ hab, ← hΦadd _ _ ha (hR _ b.2 hb), Subgroup.coe_mul, mul_assoc]
    · have hab : (a * b).1 ∉ U := fun hh => ha ((hk.1 hh).2 hb)
      rw [hψN a ha, hψU b hb, hψN _ hab, ← hΦconj _ hb, ← hΦadd _ _ (hR _ a.2 ha) (hconj _ hb), Subgroup.coe_mul]
      congr 1
      group
    · have hab : (a * b).1 ∈ U := hk.2 (by simp [ha, hb])
      have e1 : Φ (b.1 * σ) = Φ (σ⁻¹ * b.1) := by
        rw [← hΦconj _ (hR _ b.2 hb), show σ⁻¹ * (b.1 * σ) * σ = (σ⁻¹ * b.1) * (σ * σ) by group,
          hΦadd _ _ (hL _ b.2 hb) h2, hΦσ, add_zero]
      rw [hψN a ha, hψN b hb, hψU _ hab, e1, ← hΦadd _ _ (hR _ a.2 ha) (hL _ b.2 hb), Subgroup.coe_mul]
      congr 1
      group
  have hφ1 : φ 1 = 0 := by
    have := hadd 1 1
    rw [mul_one] at this
    exact left_eq_add.1 this
  refine ⟨ψ, ⟨?_, hψadd, ?_⟩, ?_, ?_⟩
  · obtain ⟨O, hO, hOe⟩ := isOpen_induced_iff.1 (hlc {0})
    have hW : IsOpen ((U.subgroupOf V : Set V) ∩ Subtype.val ⁻¹' O) :=
      hopen.inter (hO.preimage continuous_subtype_val)
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' ((U.subgroupOf V : Set V) ∩ Subtype.val ⁻¹' O),
      hW.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
    · have h1 : (1 : U) ∈ Subtype.val ⁻¹' O := by rw [hOe]; exact hφ1
      simp only [Set.mem_preimage, inv_mul_cancel]
      exact ⟨(U.subgroupOf V).one_mem, h1⟩
    · rintro y ⟨hy1, hy2⟩
      have hy1' : (x⁻¹ * y).1 ∈ U := hy1
      have h0 : (⟨_, hy1'⟩ : U) ∈ Subtype.val ⁻¹' O := hy2
      rw [hOe] at h0
      have h0' : ψ (x⁻¹ * y) = 0 := by
        rw [hψU _ hy1', hΦ _ hy1']
        exact h0
      have := hψadd x (x⁻¹ * y)
      rwa [mul_inv_cancel_left, h0', add_zero] at this
  · intro v hv
    have hvU := hS _ hv v.2
    rw [hψU v hvU, hΦ _ hvU]
    exact hoff _ hv
  · rw [hψN _ hσU]
    exact hΦσ
  · intro u
    rw [hψU _ u.2]
    exact hΦ _ u.2
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.InvTwo

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

private theorem UpperTheory.V.Two.invTwo_sign (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    (U V : Subgroup Γ) (S : Set Γ) (σ : Γ) (hσ : σ ∈ V) (ho : IsOpen (U.subgroupOf V : Set V)) (hi : U.relIndex V = 2)
    (hn : σ ∉ U) (hS : ∀ s ∈ S, s ∈ V → s ∈ U) :
    ∃ ε ∈ CharOff V S 2, ε ⟨σ, hσ⟩ = 1 ∧ ∀ v : V, v.1 ∈ U → ε v = 0 := by
  classical
  set H : Subgroup V := U.subgroupOf V with hH
  have hidx : H.index = 2 := hi
  have hσH : (⟨σ, hσ⟩ : V) ∉ H := by
    rw [hH, Subgroup.mem_subgroupOf]; exact hn
  have hcl : IsClosed (H : Set V) := H.isClosed_of_isOpen ho
  have h10 : (1 : ZMod 2) ≠ 0 := one_ne_zero
  let ε : V → ZMod 2 := fun v => if v ∈ H then 0 else 1
  have hmem : ε ∈ CharOff V S 2 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [IsLocallyConstant.iff_isOpen_fiber_apply]
      intro x
      by_cases hx : x ∈ H
      · convert ho using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10]
      · convert hcl.isOpen_compl using 1
        ext v
        by_cases hv : v ∈ H <;> simp [ε, hv, hx, h10, h10.symm]
    · intro a b
      have hab := Subgroup.mul_mem_iff_of_index_two hidx (a := a) (b := b)
      by_cases ha : a ∈ H <;> by_cases hb : b ∈ H <;> simp [ε, ha, hb, hab] <;> decide
    · intro u hu
      have : u ∈ H := by
        rw [hH, Subgroup.mem_subgroupOf]; exact hS _ hu u.2
      simp [ε, this]
  refine ⟨ε, hmem, ?_, ?_⟩
  · simp [ε, hσH]
  · intro v hv
    have : v ∈ H := by
      rw [hH, Subgroup.mem_subgroupOf]; exact hv
    simp [ε, this]

theorem UpperTheory.V.Two.invTwo :
    ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (U V : Subgroup Γ) (S : Set Γ) (σ : Γ) (n : ℕ), U ≤ V → σ ∈ V → IsOpen (U.subgroupOf V : Set V) → U.relIndex V = 2 → σ ∉ U → (∀ s ∈ S, s ∈ V → s ∈ U) →
      CardLe (CharOff V S 2) n → CardLe {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} n := by
  intro Γ _ _ _ U V S σ n hUV hσ ho hi hn hS hQ
  have two : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  classical
  obtain ⟨ε, hε, hεσ, hεU⟩ := UpperTheory.V.Two.invTwo_sign Γ U V S σ hσ ho hi hn hS
  have hσσ : σ * σ ∈ U := by
    have h2 : (U.subgroupOf V).index = 2 := hi
    have := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨σ, hσ⟩ : V)) (b := ⟨σ, hσ⟩)).mpr Iff.rfl
    rwa [Subgroup.mem_subgroupOf] at this
  set P := {φ : CharOff U S 2 // ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → φ.1 u' = φ.1 u} with hP
  let val : P → ZMod 2 := fun φ => (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩
  obtain ⟨φ0, hφ0⟩ : ∃ φ0 : P, ∀ φ : P, val φ ≠ 0 → val φ0 = 1 := by
    by_cases hex : ∃ φ : P, val φ ≠ 0
    · obtain ⟨φ, hφ⟩ := hex
      exact ⟨φ, fun _ _ => (two _).resolve_left hφ⟩
    · push_neg at hex
      exact ⟨⟨0, fun _ _ _ => rfl⟩, fun φ h => absurd (hex φ) h⟩
  let χ : P → U → ZMod 2 := fun φ =>
    if val φ = 0 then (φ.1 : U → ZMod 2) else (φ.1 : U → ZMod 2) + (φ0.1 : U → ZMod 2)
  have hχmem : ∀ φ, χ φ ∈ CharOff U S 2 := by
    intro φ
    simp only [χ]
    split_ifs
    · exact φ.1.2
    · exact add_mem φ.1.2 φ0.1.2
  have hχinv : ∀ φ, ∀ u u' : U, u'.1 = σ⁻¹ * u.1 * σ → χ φ u' = χ φ u := by
    intro φ u u' h
    simp only [χ]
    split_ifs
    · exact φ.2 u u' h
    · simp only [Pi.add_apply]
      rw [φ.2 u u' h, φ0.2 u u' h]
  have hχσ : ∀ φ, χ φ ⟨σ * σ, hσσ⟩ = 0 := by
    intro φ
    simp only [χ]
    split_ifs with h
    · exact h
    · have h1 : (φ.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1 := (two _).resolve_left h
      have h2 : (φ0.1 : U → ZMod 2) ⟨σ * σ, hσσ⟩ = 1 := hφ0 φ h
      simp only [Pi.add_apply]
      rw [h1, h2]
      rfl
  have hext : ∀ φ, ∃ ψ ∈ CharOff V S 2, ψ ⟨σ, hσ⟩ = 0 ∧ ∀ u : U, ψ ⟨u, hUV u.2⟩ = χ φ u :=
    fun φ => UpperTheory.V.Two.extTwo Γ U V S hUV σ hσ hσσ ho hi hn hS (χ φ) (hχmem φ) (hχinv φ) (hχσ φ)
  choose ψ hψmem hψσ hψU using hext
  let f : P → CharOff V S 2 := fun φ =>
    ⟨ψ φ + (if val φ = 0 then 0 else ε), add_mem (hψmem φ) (by split_ifs; exact zero_mem _; exact hε)⟩
  refine UpperTheory.V.Two.CardLe.of_injective hQ f ?_
  intro φ φ' hff
  have hfun : ψ φ + (if val φ = 0 then 0 else ε) = ψ φ' + (if val φ' = 0 then 0 else ε) :=
    congrArg Subtype.val hff
  have hbranch : (val φ = 0 ↔ val φ' = 0) := by
    have := congrFun hfun ⟨σ, hσ⟩
    simp only [Pi.add_apply] at this
    rw [hψσ φ, hψσ φ'] at this
    by_cases h : val φ = 0 <;> by_cases h' : val φ' = 0 <;> simp [h, h', hεσ] at this ⊢
  have hχ : χ φ = χ φ' := by
    funext u
    have := congrFun hfun ⟨u, hUV u.2⟩
    simp only [Pi.add_apply] at this
    rw [hψU φ u, hψU φ' u] at this
    have hu : ε ⟨u, hUV u.2⟩ = 0 := hεU _ u.2
    split_ifs at this <;> simpa [hu] using this
  apply Subtype.ext
  apply Subtype.ext
  simp only [χ] at hχ
  by_cases h : val φ = 0
  · have h' := hbranch.mp h
    simpa [h, h'] using hχ
  · have h' : ¬ val φ' = 0 := fun h' => h (hbranch.mpr h')
    simp only [h, h', if_false] at hχ
    exact add_right_cancel hχ
end
end
