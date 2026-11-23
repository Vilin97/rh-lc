module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Data.Finsupp.SMul
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateWeightGraded

section

@[expose] public section

namespace GlobalTheory

theorem tate_weight_graded : ∀ {C σ Γ : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] (χ : Γ →* Cˣ),
    (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) →
    ∀ (w : σ → ℤ) (J : Submodule C (σ →₀ C)),
    (∀ g : Γ, ∀ φ ∈ J, ∃ ψ ∈ J, ∀ m, ψ m = ((χ g ^ w m : Cˣ) : C) * (g • φ m)) →
    ∀ φ ∈ J, ∀ d : ℤ, φ.filter (fun m => w m = d) ∈ J := by
  intro C σ Γ _ _ _ χ hT w J hJ
  classical
  suffices H : ∀ n, ∀ φ ∈ J, φ.support.card = n → ∀ d : ℤ, φ.filter (fun m => w m = d) ∈ J by
    intro φ hφ d; exact H _ φ hφ rfl d
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro φ hφ hn
  have IH : ∀ φ' ∈ J, φ'.support.card < n → ∀ d : ℤ, φ'.filter (fun m => w m = d) ∈ J :=
    fun φ' h1 h2 d => ih _ h2 φ' h1 rfl d
  by_cases h0 : φ = 0
  · subst h0; intro d; rw [Finsupp.filter_zero]; exact J.zero_mem
  obtain ⟨m0, hm0⟩ := Finsupp.support_nonempty_iff.mpr h0
  have hc : φ m0 ≠ 0 := Finsupp.mem_support_iff.mp hm0
  set c := φ m0 with hcdef
  set φ0 : σ →₀ C := c⁻¹ • φ with hφ0def
  have hφ0 : φ0 ∈ J := J.smul_mem _ hφ
  have hsupp0 : φ0.support = φ.support := Finsupp.support_smul_eq (inv_ne_zero hc)
  have h1 : φ0 m0 = 1 := by
    simp only [φ0, Finsupp.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hc
  have hφeq : φ = c • φ0 := by
    simp only [φ0, smul_smul, mul_inv_cancel₀ hc, one_smul]
  suffices H0 : ∀ d : ℤ, φ0.filter (fun m => w m = d) ∈ J by
    intro d; rw [hφeq, Finsupp.filter_smul]; exact J.smul_mem _ (H0 d)
  have hcard : φ0.support.card = n := by rw [hsupp0, hn]
  have hm0' : m0 ∈ φ0.support := by rw [Finsupp.mem_support_iff, h1]; exact one_ne_zero
  have hψ : ∀ g : Γ, ∃ ψ ∈ J, ∀ m, ψ m =
      ((χ g ^ (-w m0) : Cˣ) : C) * (((χ g ^ w m : Cˣ) : C) * (g • φ0 m)) - φ0 m := by
    intro g
    obtain ⟨ψ', hψ'J, hψ'⟩ := hJ g φ0 hφ0
    refine ⟨((χ g ^ (-w m0) : Cˣ) : C) • ψ' - φ0, J.sub_mem (J.smul_mem _ hψ'J) hφ0, fun m => ?_⟩
    simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hψ']
  choose ψ hψJ hψm using hψ
  have hψm0 : ∀ g, ψ g m0 = 0 := by
    intro g
    rw [hψm, h1, smul_one, mul_one, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
      Units.val_one, sub_self]
  have hψ0 : ∀ g m, φ0 m = 0 → ψ g m = 0 := by
    intro g m h; rw [hψm, h, smul_zero, mul_zero, mul_zero, sub_zero]
  have hψsupp : ∀ g, (ψ g).support ⊆ φ0.support.erase m0 := by
    intro g m hm
    rw [Finset.mem_erase, Finsupp.mem_support_iff]
    rw [Finsupp.mem_support_iff] at hm
    refine ⟨?_, fun h => hm (hψ0 g m h)⟩
    rintro rfl; exact hm (hψm0 g)
  have hlt : ∀ g, (ψ g).support.card < n := fun g =>
    lt_of_le_of_lt (Finset.card_le_card (hψsupp g)) (hcard ▸ Finset.card_erase_lt_of_mem hm0')
  by_cases hall : ∀ g, ψ g = 0
  · have hw : ∀ m, φ0 m ≠ 0 → w m = w m0 := by
      intro m hm
      by_contra hne
      apply hm
      refine hT (w m0 - w m) (sub_ne_zero.mpr (Ne.symm hne)) (φ0 m) (fun g => ?_)
      have e := hψm g m
      rw [hall g, Finsupp.zero_apply, eq_comm, sub_eq_zero] at e
      have hex : w m0 - w m + -w m0 + w m = 0 := by ring
      conv_rhs => rw [← e]
      rw [← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul, ← zpow_add, ← zpow_add,
        hex, zpow_zero, Units.val_one, one_mul]
    intro d
    by_cases hd : w m0 = d
    · rw [(Finsupp.filter_eq_self_iff _ _).mpr (fun m hm => (hw m hm).trans hd)]; exact hφ0
    · rw [(Finsupp.filter_eq_zero_iff _ _).mpr (fun m hm => by
        by_contra h; exact hd ((hw m h).symm.trans hm))]
      exact J.zero_mem
  · push_neg at hall
    obtain ⟨g, hg⟩ := hall
    obtain ⟨m1, hm1⟩ := Finsupp.support_nonempty_iff.mpr hg
    have hm1' := Finset.mem_of_mem_erase (hψsupp g hm1)
    have hψm1 : ψ g m1 ≠ 0 := Finsupp.mem_support_iff.mp hm1
    set a := φ0 m1 / ψ g m1 with hadef
    set φ' : σ →₀ C := φ0 - a • ψ g with hφ'def
    have hφ'J : φ' ∈ J := J.sub_mem hφ0 (J.smul_mem _ (hψJ g))
    have hφ'supp : φ'.support ⊆ φ0.support.erase m1 := by
      intro m hm
      rw [Finset.mem_erase, Finsupp.mem_support_iff]
      rw [Finsupp.mem_support_iff] at hm
      refine ⟨?_, fun h => hm ?_⟩
      · rintro rfl; apply hm
        simp only [φ', a, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
          div_mul_cancel₀ _ hψm1, sub_self]
      · simp only [φ', Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, h, hψ0 g m h,
          mul_zero, sub_zero]
    have hlt' : φ'.support.card < n :=
      lt_of_le_of_lt (Finset.card_le_card hφ'supp) (hcard ▸ Finset.card_erase_lt_of_mem hm1')
    intro d
    have hdec : φ0 = φ' + a • ψ g := by simp only [φ', sub_add_cancel]
    rw [hdec, Finsupp.filter_add, Finsupp.filter_smul]
    exact J.add_mem (IH _ hφ'J hlt' d) (J.smul_mem _ (IH _ (hψJ g) (hlt g) d))

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateWeightGradedStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.filter_weight_mem_of_tate_graded_stable : ∀ {C σ Γ : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] (χ : Γ →* Cˣ), (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) → ∀ (w : σ → ℤ) (J : Submodule C (σ →₀ C)), (∀ g : Γ, ∀ φ ∈ J, ∃ ψ ∈ J, ∀ m, ψ m = ((χ g ^ w m : Cˣ) : C) * (g • φ m)) → ∀ φ ∈ J, ∀ d : ℤ, φ.filter (fun m => w m = d) ∈ J := by
  first | exact @GlobalTheory.tate_weight_graded | exact GlobalTheory.tate_weight_graded | (intros; apply GlobalTheory.tate_weight_graded <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VanishAtHodgeTateCocharacter

section

@[expose] public section

open MvPolynomial

namespace GlobalTheory.HTCPoly

theorem prod_zpow_eq {ι G : Type} [CommGroup G] (u : G) (s : Finset ι) (a : ι → ℤ) :
    ∏ i ∈ s, u ^ a i = u ^ ∑ i ∈ s, a i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

variable {C n : Type} [Field C] [Fintype n] [DecidableEq n]

def wt (k : n → ℤ) (m : (n × n) →₀ ℕ) : ℤ := ∑ i : n × n, (m i : ℤ) * k i.2

theorem unit_prod (k : n → ℤ) (u : Cˣ) (m : (n × n) →₀ ℕ) :
    ∏ i : n × n, ((u ^ k i.2 : Cˣ) : C) ^ (m i) = ((u ^ wt k m : Cˣ) : C) := by
  have h : ∏ i : n × n, (u ^ k i.2) ^ (m i) = u ^ wt k m := by
    rw [wt, ← prod_zpow_eq]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← zpow_natCast, ← zpow_mul, mul_comm]
  rw [← h, Units.coe_prod]
  simp [Units.val_pow_eq_pow_val]

theorem eval_eq_sum {σ : Type} [Fintype σ] (x : σ → C) (p : MvPolynomial σ C)
    (s : Finset (σ →₀ ℕ)) (hs : p.support ⊆ s) :
    eval x p = ∑ m ∈ s, AddMonoidAlgebra.coeff p m * ∏ i, x i ^ m i := by
  rw [eval_eq']
  refine Finset.sum_subset hs fun m _ hm => ?_
  have : AddMonoidAlgebra.coeff p m = 0 := by simpa [MvPolynomial.mem_support_iff] using hm
  rw [this, zero_mul]

theorem eval_mul_diag (k : n → ℤ) (u : Cˣ) (y : Matrix n n C) (p : MvPolynomial (n × n) C)
    (s : Finset ((n × n) →₀ ℕ)) (hs : p.support ⊆ s) :
    eval (fun ij => (y * Matrix.diagonal (fun j => ((u ^ k j : Cˣ) : C))) ij.1 ij.2) p
      = ∑ m ∈ s, ((u ^ wt k m : Cˣ) : C) * AddMonoidAlgebra.coeff p m * ∏ i : n × n, y i.1 i.2 ^ m i := by
  rw [eval_eq_sum _ _ s hs]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [Matrix.mul_diagonal, mul_pow, Finset.prod_mul_distrib, unit_prod]
  ring

variable {Γ : Type} [Group Γ] [MulSemiringAction Γ C]

def vanJ (ρ : Γ →* Matrix.GeneralLinearGroup n C) (P : Matrix n n C) :
    Submodule C (((n × n) →₀ ℕ) →₀ C) where
  carrier := {φ | ∀ γ, eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff φ : MvPolynomial (n × n) C) = 0}
  add_mem' := by
    intro a b ha hb γ
    simp only [Set.mem_setOf_eq] at *
    rw [show (AddMonoidAlgebra.ofCoeff (a + b) : MvPolynomial (n × n) C) =
      AddMonoidAlgebra.ofCoeff a + AddMonoidAlgebra.ofCoeff b by simp, map_add (f := _), ha γ, hb γ, add_zero]
  zero_mem' := by
    intro γ
    simp
  smul_mem' := by
    intro c a ha γ
    simp only [Set.mem_setOf_eq] at *
    rw [show (AddMonoidAlgebra.ofCoeff (c • a) : MvPolynomial (n × n) C) =
      c • AddMonoidAlgebra.ofCoeff a by simp, smul_eval, ha γ, mul_zero]

end GlobalTheory.HTCPoly

namespace GlobalTheory.HTCPoly
variable {C n : Type} [Field C] [Fintype n] [DecidableEq n]
variable {Γ : Type} [Group Γ] [MulSemiringAction Γ C]

theorem mem_vanJ (ρ : Γ →* Matrix.GeneralLinearGroup n C) (P : Matrix n n C)
    (φ : ((n × n) →₀ ℕ) →₀ C) :
    φ ∈ vanJ ρ P ↔ ∀ γ, eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff φ : MvPolynomial (n × n) C) = 0 := Iff.rfl

theorem vanJ_stable (χ : Γ →* Cˣ) (ρ : Γ →* Matrix.GeneralLinearGroup n C)
    (hfix : ∀ (g γ : Γ) (i j : n), g • (ρ γ : Matrix n n C) i j = (ρ γ : Matrix n n C) i j)
    (P : Matrix n n C) (k : n → ℤ)
    (hP : ∀ g : Γ, (ρ g : Matrix n n C) * P.map (fun a => g • a) =
      P * Matrix.diagonal (fun i => ((χ g ^ k i : Cˣ) : C))) :
    ∀ g : Γ, ∀ φ ∈ vanJ ρ P, ∃ ψ ∈ vanJ ρ P,
      ∀ m, ψ m = ((χ g ^ wt k m : Cˣ) : C) * (g • φ m) := by
  intro g φ hφ
  refine ⟨Finsupp.onFinset φ.support (fun m => ((χ g ^ wt k m : Cˣ) : C) * (g • φ m)) ?_, ?_,
    fun m => Finsupp.onFinset_apply⟩
  · intro m hm
    rw [Finsupp.mem_support_iff]
    intro h0
    apply hm
    rw [h0, smul_zero, mul_zero]
  · rw [mem_vanJ] at hφ ⊢
    intro γ
    set σg := MulSemiringAction.toRingHom Γ C g
    set p : MvPolynomial (n × n) C := AddMonoidAlgebra.ofCoeff φ
    have hfix' : (ρ (γ * g) : Matrix n n C).map σg = ρ (γ * g) := by
      ext i j
      exact hfix g (γ * g) i j
    have key : (ρ γ : Matrix n n C) * P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C)) =
        ((ρ (γ * g) : Matrix n n C) * P).map σg := by
      calc (ρ γ : Matrix n n C) * P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C))
          = (ρ γ : Matrix n n C) * (P * Matrix.diagonal (fun j => ((χ g ^ k j : Cˣ) : C))) :=
            Matrix.mul_assoc _ _ _
        _ = (ρ γ : Matrix n n C) * ((ρ g : Matrix n n C) * P.map (fun a => g • a)) := by rw [hP g]
        _ = ((ρ (γ * g) : Matrix n n C) * P).map σg := by
            rw [Matrix.map_mul, hfix', map_mul, Units.val_mul, Matrix.mul_assoc]
            rfl
    have e1 : eval (fun ij : n × n => ((ρ γ : Matrix n n C) * P) ij.1 ij.2)
        (AddMonoidAlgebra.ofCoeff (Finsupp.onFinset φ.support
          (fun m => ((χ g ^ wt k m : Cˣ) : C) * (g • φ m)) (by
            intro m hm
            rw [Finsupp.mem_support_iff]
            intro h0
            apply hm
            rw [h0, smul_zero, mul_zero])) : MvPolynomial (n × n) C)
        = ∑ m ∈ φ.support, ((χ g ^ wt k m : Cˣ) : C) * AddMonoidAlgebra.coeff (map σg p) m *
            ∏ i : n × n, ((ρ γ : Matrix n n C) * P) i.1 i.2 ^ m i := by
      refine (eval_eq_sum _ _ φ.support ?_).trans ?_
      · intro m hm
        rw [MvPolynomial.mem_support_iff] at hm
        rw [Finsupp.mem_support_iff]
        intro h0
        apply hm
        show ((χ g ^ wt k m : Cˣ) : C) * (g • φ m) = 0
        rw [h0, smul_zero, mul_zero]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [coeff_map]
      rfl
    rw [e1, ← eval_mul_diag k (χ g) _ (map σg p) φ.support (MvPolynomial.support_map_subset _ _), key]
    have h2 := eval₂_comp_left σg (RingHom.id C)
      (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p
    rw [RingHom.comp_id] at h2
    rw [eval_map]
    calc eval₂ σg (fun ij : n × n => (((ρ (γ * g) : Matrix n n C) * P).map σg) ij.1 ij.2) p
        = σg (eval₂ (RingHom.id C) (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p) :=
          h2.symm
      _ = 0 := by
          rw [show eval₂ (RingHom.id C) (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p
            = eval (fun ij : n × n => ((ρ (γ * g) : Matrix n n C) * P) ij.1 ij.2) p from rfl, hφ (γ * g),
            map_zero]

end GlobalTheory.HTCPoly

namespace GlobalTheory.HTCPoly

theorem vanish_at_cocharacter : ∀ {C Γ n : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] [Fintype n] [DecidableEq n] (χ : Γ →* Cˣ), (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) → ∀ (ρ : Γ →* Matrix.GeneralLinearGroup n C), (∀ (g γ : Γ) (i j : n), g • (ρ γ : Matrix n n C) i j = (ρ γ : Matrix n n C) i j) → ∀ (P : Matrix.GeneralLinearGroup n C) (k : n → ℤ), (∀ g : Γ, (ρ g : Matrix n n C) * (P : Matrix n n C).map (fun a => g • a) = (P : Matrix n n C) * Matrix.diagonal (fun i => ((χ g ^ k i : Cˣ) : C))) → ∀ f : MvPolynomial (n × n) C, (∀ γ : Γ, MvPolynomial.eval (fun ij => (ρ γ : Matrix n n C) ij.1 ij.2) f = 0) → ∀ t : Cˣ, MvPolynomial.eval (fun ij => ((P : Matrix n n C) * Matrix.diagonal (fun i => ((t ^ k i : Cˣ) : C)) * ((P⁻¹ : Matrix.GeneralLinearGroup n C) : Matrix n n C)) ij.1 ij.2) f = 0 := by
  intro C Γ n _ _ _ _ _ χ hT ρ hfix P k hP f hf t
  set Pm : Matrix n n C := (P : Matrix n n C) with hPm
  set Qm : Matrix n n C := ((P⁻¹ : Matrix.GeneralLinearGroup n C) : Matrix n n C) with hQm
  have hPQ : Pm * Qm = 1 := by
    rw [hPm, hQm, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  let q : n × n → MvPolynomial (n × n) C := fun ij => ∑ l, X (ij.1, l) * MvPolynomial.C (Qm l ij.2)
  have hφ : ∀ y : Matrix n n C, eval (fun ij : n × n => y ij.1 ij.2) (aeval q f) =
      eval (fun ij : n × n => (y * Qm) ij.1 ij.2) f := by
    intro y
    show aeval (fun ij : n × n => y ij.1 ij.2) (aeval q f) =
      aeval (fun ij : n × n => (y * Qm) ij.1 ij.2) f
    rw [← AlgHom.comp_apply, comp_aeval]
    refine congrArg (fun F : n × n → C => aeval F f) (funext fun ij => ?_)
    simp [q, Matrix.mul_apply]
  set p : MvPolynomial (n × n) C := aeval q f with hp
  have hpJ : AddMonoidAlgebra.coeff p ∈ vanJ ρ Pm := by
    rw [mem_vanJ]
    intro γ
    show eval _ p = 0
    rw [hφ, Matrix.mul_assoc, hPQ, Matrix.mul_one]
    exact hf γ
  have hgr := GlobalTheory.T.filter_weight_mem_of_tate_graded_stable χ hT (wt k) (vanJ ρ Pm) (vanJ_stable χ ρ hfix Pm k hP) _ hpJ
  have hzero : ∀ d : ℤ, eval (fun ij : n × n => Pm ij.1 ij.2)
      (AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).filter (fun m => wt k m = d)) :
        MvPolynomial (n × n) C) = 0 := by
    intro d
    have h1 := (mem_vanJ ρ Pm _).mp (hgr d) 1
    rwa [map_one, Units.val_one, Matrix.one_mul] at h1
  rw [← hφ (Pm * Matrix.diagonal (fun i => ((t ^ k i : Cˣ) : C)))]
  rw [eval_mul_diag k t Pm p p.support subset_rfl]
  rw [← Finset.sum_fiberwise_of_maps_to (t := p.support.image (wt k)) (g := wt k)
    (fun m hm => Finset.mem_image_of_mem _ hm)]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [← mul_zero ((t ^ d : Cˣ) : C), ← hzero d,
    eval_eq_sum _ _ (p.support.filter (fun m => wt k m = d)) ?_, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [Finset.mem_filter] at hm
    have hc : AddMonoidAlgebra.coeff (AddMonoidAlgebra.ofCoeff ((AddMonoidAlgebra.coeff p).filter
        (fun m => wt k m = d)) : MvPolynomial (n × n) C) m = AddMonoidAlgebra.coeff p m :=
      Finsupp.filter_apply_pos _ _ hm.2
    rw [hc, hm.2]
    ring
  · intro m hm
    rw [MvPolynomial.mem_support_iff] at hm
    rw [Finset.mem_filter, MvPolynomial.mem_support_iff]
    by_contra hne
    apply hm
    show (Finsupp.filter (fun m => wt k m = d) (AddMonoidAlgebra.coeff p)) m = 0
    by_cases hw : wt k m = d
    · rw [Finsupp.filter_apply_pos (fun m => wt k m = d) _ hw]
      by_contra h
      exact hne ⟨h, hw⟩
    · exact Finsupp.filter_apply_neg _ _ hw

end GlobalTheory.HTCPoly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VanishAtHodgeTateCocharacterStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.vanish_at_hodgeTate_cocharacter : ∀ {C Γ n : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] [Fintype n] [DecidableEq n] (χ : Γ →* Cˣ), (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) → ∀ (ρ : Γ →* Matrix.GeneralLinearGroup n C), (∀ (g γ : Γ) (i j : n), g • (ρ γ : Matrix n n C) i j = (ρ γ : Matrix n n C) i j) → ∀ (P : Matrix.GeneralLinearGroup n C) (k : n → ℤ), (∀ g : Γ, (ρ g : Matrix n n C) * (P : Matrix n n C).map (fun a => g • a) = (P : Matrix n n C) * Matrix.diagonal (fun i => ((χ g ^ k i : Cˣ) : C))) → ∀ f : MvPolynomial (n × n) C, (∀ γ : Γ, MvPolynomial.eval (fun ij => (ρ γ : Matrix n n C) ij.1 ij.2) f = 0) → ∀ t : Cˣ, MvPolynomial.eval (fun ij => ((P : Matrix n n C) * Matrix.diagonal (fun i => ((t ^ k i : Cˣ) : C)) * ((P⁻¹ : Matrix.GeneralLinearGroup n C) : Matrix n n C)) ij.1 ij.2) f = 0 := by
  first | exact @GlobalTheory.HTCPoly.vanish_at_cocharacter | exact GlobalTheory.HTCPoly.vanish_at_cocharacter | (intros; apply GlobalTheory.HTCPoly.vanish_at_cocharacter <;> assumption)
end
end
