module

public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import Development.DiscreteGroups.GlobalIrreducibility.InHCorner
public import Development.DiscreteGroups.GlobalIrreducibility.LConvKirA
public import Development.DiscreteGroups.GlobalIrreducibility.ContinuousKinv2
public import GroundTheory.GlobalFields.TateThesis.NoSmallSubgroups
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
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Mathlib.Tactic.Linter.Style

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvKirB

section

@[expose] public section

noncomputable section
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands ValuativeRel Filter Topology

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

def ballLe (r : ValueGroupWithZero k) : AddSubgroup k where
  carrier := {x | valuation k x ≤ r}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact ((valuation k).map_add a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa [Valuation.map_neg] using ha

def ballLt (γ : (ValueGroupWithZero k)ˣ) : AddSubgroup k where
  carrier := {x | valuation k x < γ}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq] at *
    exact (valuation k).map_add_lt ha hb
  zero_mem' := by simp [Units.zero_lt]
  neg_mem' {a} ha := by simpa [Valuation.map_neg] using ha

theorem isOpen_ballLt (γ : (ValueGroupWithZero k)ˣ) : IsOpen ((ballLt γ : AddSubgroup k) : Set k) :=
  (ballLt γ).isOpen_of_mem_nhds (g := 0) ((IsValuativeTopology.mem_nhds_zero_iff _).2 ⟨γ, fun _ hx => hx⟩)

theorem psi_ball (ψ : AddChar k Circle) (hψ : Continuous ψ) :
    ∃ γ : (ValueGroupWithZero k)ˣ, ∀ x : k, valuation k x < γ → ψ x = 1 := by
  have hU : {t : k | ‖((ψ t : Circle) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 (0 : k) := by
    have hc : Continuous fun t : k => ‖((ψ t : Circle) : ℂ) - 1‖ :=
      ((continuous_subtype_val.comp hψ).sub continuous_const).norm
    exact (isOpen_lt hc continuous_const).mem_nhds (by simp)
  obtain ⟨γ, hγ⟩ := (IsValuativeTopology.mem_nhds_zero_iff _).1 hU
  let H : Subgroup Circle :=
    { carrier := ψ '' {x | valuation k x < γ}
      mul_mem' := by
        rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
        exact ⟨a + b, (valuation k).map_add_lt ha hb, AddChar.map_add_eq_mul ψ a b⟩
      one_mem' := ⟨0, by simp [Units.zero_lt], AddChar.map_zero_eq_one ψ⟩
      inv_mem' := by
        rintro _ ⟨a, ha, rfl⟩
        exact ⟨-a, by simpa [Valuation.map_neg] using ha, AddChar.map_neg_eq_inv ψ a⟩ }
  have hH := GroundTheory.Global.Circle.subgroup_eq_bot_of_norm_sub_one_lt H (by
    rintro _ ⟨a, ha, rfl⟩; exact hγ ha)
  refine ⟨γ, fun x hx => ?_⟩
  have : ψ x ∈ H := ⟨x, hx, rfl⟩
  rw [hH] at this
  exact Subgroup.mem_bot.1 this

theorem small_of_triv (ψ : AddChar k Circle) (y : k) (hy : ψ y ≠ 1) (γ : (ValueGroupWithZero k)ˣ) (b : k)
    (h : ∀ t : k, valuation k t ≤ valuation k y * ↑γ⁻¹ → ψ (b * t) = 1) : valuation k b < γ := by
  by_contra hb'
  have hb := not_lt.1 hb'
  have hb0 : (0 : ValueGroupWithZero k) < valuation k b := lt_of_lt_of_le (Units.zero_lt γ) hb
  have hb0' : b ≠ 0 := fun h0 => by simp [h0] at hb0
  apply hy
  have e : b * (y / b) = y := by field_simp
  rw [← e]
  refine h _ ?_
  rw [map_div₀, div_eq_mul_inv, Units.val_inv_eq_inv_val]
  gcongr (valuation k y) * ?_
  exact (inv_le_inv₀ hb0 (Units.zero_lt γ)).2 hb

theorem continuous_U (c : Fin (m + 1)) : Continuous (fun x : Fin (m + 1) → k => U c x) := by
  have hc : ∀ x' : (Fin (m + 1) → k) → (Fin (m + 1) → k), Continuous x' →
      Continuous fun x => colM c (x' x) := by
    intro x' hx'
    refine continuous_const.add (continuous_matrix fun p q => ?_)
    by_cases h : q = c ∧ p < c
    · simp only [Matrix.of_apply, if_pos h]; exact (continuous_apply p).comp hx'
    · simp only [Matrix.of_apply, if_neg h]; exact continuous_const
  exact Units.continuous_iff.2 ⟨hc id continuous_id, hc (fun x => -x) continuous_neg⟩

end DiscreteGroups.sglob.LConvKir
end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvKirC

section

@[expose] public section

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConvKir

theorem sum_char_eq_zero {A : Type} [AddCommGroup A] (L L'' : AddSubgroup A)
    [Fintype (L ⧸ L''.addSubgroupOf L)] (χ : A → ℂ) (hχ : ∀ x y, χ (x + y) = χ x * χ y)
    (h'' : ∀ x ∈ L'', χ x = 1) (x₀ : L) (hne : χ x₀ ≠ 1) :
    ∑ q : L ⧸ L''.addSubgroupOf L, χ ((Quotient.out q : L) : A) = 0 := by
  have hterm : ∀ q : L ⧸ L''.addSubgroupOf L,
      χ ((Quotient.out ((x₀ : L ⧸ L''.addSubgroupOf L) + q) : L) : A) = χ x₀ * χ ((Quotient.out q : L) : A) := by
    intro q
    set z := Quotient.out ((x₀ : L ⧸ L''.addSubgroupOf L) + q) with hz
    have hq : ((z : L) : L ⧸ L''.addSubgroupOf L) = ((x₀ + Quotient.out q : L) : L ⧸ L''.addSubgroupOf L) := by
      rw [hz, QuotientAddGroup.out_eq', QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    have hd := AddSubgroup.mem_addSubgroupOf.1 (QuotientAddGroup.eq.1 hq)
    have e : (x₀ : A) + ((Quotient.out q : L) : A) = (z : A) + ((-z + (x₀ + Quotient.out q) : L) : A) := by
      simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]; abel
    rw [← hχ, e, hχ, h'' _ hd, mul_one]
  have hT := Equiv.sum_comp (Equiv.addLeft ((x₀ : L ⧸ L''.addSubgroupOf L))) (fun q => χ ((Quotient.out q : L) : A))
  simp only [Equiv.coe_addLeft, hterm, ← Finset.mul_sum] at hT
  have h0 : (χ x₀ - 1) * ∑ q : L ⧸ L''.addSubgroupOf L, χ ((Quotient.out q : L) : A) = 0 := by
    rw [sub_mul, hT, one_mul, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 hne)

variable {k : Type} [Field k]

theorem psi_neg_mul (ψ : AddChar k Circle) (t : k) : ((ψ (-t) : Circle) : ℂ) * (ψ t : ℂ) = 1 := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]

theorem l_gU {m : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar k Circle)
    (ρ : Representation ℂ (GL (Fin (m + 1)) k) V) (l : Module.Dual ℂ V) (hl : IsFunctional ψ ρ l)
    (j : ℕ) (hj : j + 1 < m + 1) (g : GL (Fin (m + 1)) k) (hg : InH (j + 1) g) (x : Fin (m + 1) → k) (w : V) :
    l (ρ g (ρ (U ⟨j + 1, hj⟩ x) w)) =
      (ψ (∑ r, (if r < (⟨j + 1, hj⟩ : Fin (m + 1)) then
        (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ⟨j, by omega⟩ r else 0) * x r) : ℂ) * l (ρ g w) := by
  rw [← Module.End.mul_apply, ← map_mul, conj_U j hj g hg x, map_mul, Module.End.mul_apply,
    hl _ (U_mem _ _), superDiag_U]

end DiscreteGroups.sglob.LConvKir
end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvKirStep

section

@[expose] public section

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep ValuativeRel

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem step (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin (m + 1)) k) V) (hsm : IsSmooth ρ) (j : ℕ) (hj : j + 1 < m + 1)
    (v : V) : ∃ v' : V, ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → l v' = l v ∧
      ((∀ h, InH j h → l (ρ h v) = 0) → ∀ g, InH (j + 1) g → l (ρ g v') = 0) := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    exact hψ (AddChar.ext _ _ fun x => by rw [not_exists_not.1 h x, AddChar.one_apply])
  set c : Fin (m + 1) := ⟨j + 1, hj⟩ with hc
  set jj : Fin (m + 1) := ⟨j, by omega⟩ with hjj
  have hjc : jj < c := Fin.mk_lt_mk.2 (Nat.lt_succ_self j)
  obtain ⟨γ₁, hγ₁⟩ := kappa_nbhd {g | ρ g v = v} (hsm v) (by simp) jj
  obtain ⟨γ₀, hγ₀⟩ := psi_ball ψ hψc
  let r₁ : ValueGroupWithZero k := valuation k y * ↑γ₁⁻¹
  let L : AddSubgroup (Fin (m + 1) → k) := AddSubgroup.pi Set.univ fun _ => ballLe r₁
  let Sx : AddSubgroup (Fin (m + 1) → k) :=
    { carrier := {x | ρ (U c x) v = v}
      add_mem' := by
        intro a b (ha : ρ (U c a) v = v) (hb : ρ (U c b) v = v)
        show ρ (U c (a + b)) v = v
        rw [U_add, map_mul, Module.End.mul_apply, hb, ha]
      zero_mem' := by
        show ρ (U c 0) v = v
        rw [U_zero, map_one, Module.End.one_apply]
      neg_mem' := by
        intro a (ha : ρ (U c a) v = v)
        show ρ (U c (-a)) v = v
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, ← U_add, neg_add_cancel, U_zero, map_one, Module.End.one_apply] }
  let L'' : AddSubgroup (Fin (m + 1) → k) := Sx ⊓ AddSubgroup.pi Set.univ fun _ => ballLt γ₀
  have hLc : IsCompact (L : Set (Fin (m + 1) → k)) :=
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k r₁
  have : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  have hL''o : IsOpen (L'' : Set (Fin (m + 1) → k)) :=
    ((hsm v).preimage (continuous_U c)).inter (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_ballLt γ₀)
  have hQf : Finite (L ⧸ L''.addSubgroupOf L) :=
    AddSubgroup.quotient_finite_of_isOpen _ (hL''o.preimage continuous_subtype_val)
  let _ : Fintype (L ⧸ L''.addSubgroupOf L) := Fintype.ofFinite _
  let xs : (L ⧸ L''.addSubgroupOf L) → Fin (m + 1) → k := fun q => ((Quotient.out q : L) : Fin (m + 1) → k)
  have hN : (Fintype.card (L ⧸ L''.addSubgroupOf L) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card (L ⧸ L''.addSubgroupOf L) : ℂ)⁻¹ • ∑ q : L ⧸ L''.addSubgroupOf L,
    ((ψ (-(xs q jj)) : Circle) : ℂ) • ρ (U c (xs q)) v, fun l hl => ⟨?_, fun hv g hg => ?_⟩⟩

  · simp only [map_smul, map_sum, smul_eq_mul]
    have hq : ∀ q, ((ψ (-(xs q jj)) : Circle) : ℂ) * l (ρ (U c (xs q)) v) = l v := fun q => by
      rw [hl _ (U_mem _ _), superDiag_U, ← mul_assoc, psi_neg_mul, one_mul]
    rw [Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hN, one_mul]

  · simp only [map_smul, map_sum, smul_eq_mul]
    let w : Fin (m + 1) → k := fun r => if r < c then (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj r else 0
    let χ : (Fin (m + 1) → k) → ℂ := fun x => ((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ)
    have hterm : ∀ x, ((ψ (-(x jj)) : Circle) : ℂ) * l (ρ g (ρ (U c x) v)) = χ x * l (ρ g v) := fun x => by
      rw [l_gU ψ ρ l hl j hj g hg x v]; exact (mul_assoc _ _ _).symm
    rw [mul_eq_zero]; right
    have hS : (∑ q : L ⧸ L''.addSubgroupOf L, ((ψ (-(xs q jj)) : Circle) : ℂ) * l (ρ g (ρ (U c (xs q)) v))) =
        (∑ q : L ⧸ L''.addSubgroupOf L, χ (xs q)) * l (ρ g v) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun q _ => hterm (xs q)
    refine hS.trans ?_
    by_cases h0 : l (ρ g v) = 0
    · rw [h0, mul_zero]
    have hχadd : ∀ x x', χ (x + x') = χ x * χ x' := fun x x' => by
      show ((ψ (-((x + x') jj)) : Circle) : ℂ) * (ψ (∑ r, w r * (x + x') r) : ℂ) =
        (((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ)) *
          (((ψ (-(x' jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x' r) : ℂ))
      have hs : ∑ r, w r * (x + x') r = ∑ r, w r * x r + ∑ r, w r * x' r := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun r _ => by rw [Pi.add_apply, mul_add]
      rw [Pi.add_apply, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, hs, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    have hχ'' : ∀ x ∈ L'', χ x = 1 := by
      intro x hx
      have hx1 : ρ (U c x) v = v := (AddSubgroup.mem_inf.1 hx).1
      have hx2 : valuation k (x jj) < γ₀ := (AddSubgroup.mem_pi _).1 (AddSubgroup.mem_inf.1 hx).2 jj (Set.mem_univ _)
      have e1 : ψ (-(x jj)) = 1 := hγ₀ _ (by rwa [Valuation.map_neg])
      have e2 : (ψ (∑ r, w r * x r) : ℂ) = 1 := by
        have := l_gU ψ ρ l hl j hj g hg x v
        rw [hx1] at this
        exact (mul_eq_right₀ h0).1 this.symm
      show ((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ) = 1
      rw [e1, Circle.coe_one, one_mul, e2]
    by_cases hall : ∀ x ∈ L, χ x = 1
    · exfalso
      apply h0
      have hsmall : ∀ i, valuation k (w i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i) < γ₁ := by
        intro i
        refine small_of_triv ψ y hy γ₁ _ fun t ht => ?_
        have hxL : (Pi.single i t : Fin (m + 1) → k) ∈ L := by
          refine (AddSubgroup.mem_pi _).2 fun r _ => ?_
          by_cases hr : r = i
          · rw [hr]
            show valuation k ((Pi.single i t : Fin (m + 1) → k) i) ≤ r₁
            rw [Pi.single_eq_same]; exact ht
          · show valuation k ((Pi.single i t : Fin (m + 1) → k) r) ≤ r₁
            rw [Pi.single_eq_of_ne hr, map_zero]; exact zero_le
        have h3 : ((ψ (-((Pi.single i t : Fin (m + 1) → k) jj)) : Circle) : ℂ) *
            (ψ (∑ r, w r * (Pi.single i t : Fin (m + 1) → k) r) : ℂ) = 1 := hall _ hxL
        have hs : ∑ r, w r * (Pi.single i t : Fin (m + 1) → k) r = w i * t := by
          rw [Finset.sum_eq_single i (fun r _ hr => by rw [Pi.single_eq_of_ne hr, mul_zero]) (by simp),
            Pi.single_eq_same]
        have hsj : (Pi.single i t : Fin (m + 1) → k) jj = (Pi.single jj (1 : k) : Fin (m + 1) → k) i * t := by
          by_cases h : i = jj
          · rw [h, Pi.single_eq_same, Pi.single_eq_same, one_mul]
          · rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne h, zero_mul]
        have h4 : ((ψ ((w i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i) * t) : Circle) : ℂ) = 1 := by
          rw [sub_mul, sub_eq_neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, ← hs, ← hsj]
          exact h3
        exact Circle.coe_eq_one.1 h4
      obtain ⟨κ, hκS, hκ, hκi⟩ := hγ₁ w hsmall
      have hgrow : ∀ r, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj r = w r := fun r => by
        by_cases hr : r < c
        · simp only [w, if_pos hr]
        · simp only [w, if_neg hr]
          rw [hg jj r (fun h => hr (by rw [Fin.lt_def]; exact h.2)),
            Matrix.one_apply_ne (fun h => hr (by rw [← h]; exact hjc))]
      have hMrow : ∀ q, ((g * κ⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj q =
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj q := by
        intro q
        have hk1 : Kmat jj w * Kinv jj w = 1 := by
          rw [← hκ, ← hκi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [Units.val_mul, hκi, Matrix.mul_apply, ← hk1, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hgrow r]
        simp only [Kmat, Matrix.of_apply, ↓reduceIte]
      have hMH : InH (j + 1) (g * κ⁻¹) := by
        intro p q hpq
        rw [Units.val_mul, hκi, Matrix.mul_apply]
        by_cases hp : p < c
        · have hq : ¬ q < c := fun hq => hpq ⟨hp, hq⟩
          have hK : ∀ r, Kinv jj w r q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r q := fun r => by
            by_cases hr : r = jj
            · rw [hr]
              simp only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte]
              rw [if_neg (fun h => hq (by rw [h]; exact hjc)), show w q = 0 from if_neg hq, neg_zero, zero_mul,
                Matrix.one_apply_ne (fun h => hq (by rw [← h]; exact hjc))]
            · simp only [Kinv, Kinv2, Matrix.of_apply, if_neg hr]
          rw [Finset.sum_congr rfl fun r _ => by rw [hK r], ← Matrix.mul_apply, Matrix.mul_one]
          exact hg p q hpq
        · rw [Finset.sum_eq_single p (fun r _ hr => by
              rw [hg p r (fun h => hp h.1), Matrix.one_apply_ne (Ne.symm hr), zero_mul]) (by simp),
            hg p p (fun h => hp h.1), Matrix.one_apply_eq, one_mul]
          simp only [Kinv, Kinv2, Matrix.of_apply, if_neg (fun h : p = jj => hp (by rw [h]; exact hjc))]
      obtain ⟨yv, h, hh, hM⟩ := decomp j (by omega) (g * κ⁻¹) hMH hMrow
      have hki : ρ κ⁻¹ v = v := by
        conv_lhs => rw [← (hκS : ρ κ v = v)]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      have e1 : ρ g v = ρ (g * κ⁻¹) v := by rw [map_mul, Module.End.mul_apply, hki]
      rw [e1, hM, map_mul, Module.End.mul_apply, hl _ (U_mem _ _), hv h hh, mul_zero]
    · push Not at hall
      obtain ⟨x₀, hx₀L, hx₀⟩ := hall
      have hsum := sum_char_eq_zero L L'' χ hχadd hχ'' ⟨x₀, hx₀L⟩ hx₀
      rw [show (∑ q : L ⧸ L''.addSubgroupOf L, χ (xs q)) = 0 from hsum, zero_mul]

end DiscreteGroups.sglob.LConvKir
end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvKir

section

@[expose] public section

noncomputable section
open GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep

namespace DiscreteGroups.sglob.LConv

open DiscreteGroups.sglob.LConvKir in
theorem kirBump : KirBump := by
  intro k _ _ _ _ ψ hψc hψ m V _ _ ρ hsm v₀
  have key : ∀ j, j ≤ m → ∃ v : V, ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l →
      l v = l v₀ ∧ (l v₀ = 0 → ∀ g, InH j g → l (ρ g v) = 0) := by
    intro j
    induction j with
    | zero =>
      intro _
      exact ⟨v₀, fun l _ => ⟨rfl, fun h0 g hg => by rw [InH_zero g hg, map_one, Module.End.one_apply]; exact h0⟩⟩
    | succ j ih =>
      intro hj
      obtain ⟨v, hv⟩ := ih (by omega)
      obtain ⟨v', hv'⟩ := step ψ hψc hψ ρ hsm j (by omega) v
      exact ⟨v', fun l hl => ⟨(hv' l hl).1.trans (hv l hl).1,
        fun h0 g hg => (hv' l hl).2 ((hv l hl).2 h0) g hg⟩⟩
  obtain ⟨v, hv⟩ := key m le_rfl
  exact ⟨v, fun l hl => ⟨(hv l hl).1, fun h0 g => (hv l hl).2 h0 _ (InH_corner g)⟩⟩

end DiscreteGroups.sglob.LConv
end
end
end
