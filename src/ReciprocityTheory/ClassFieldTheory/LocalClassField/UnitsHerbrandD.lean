module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.FieldTheory.Galois.NormalBasis
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.Pi
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandA
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

-- Source module: ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandC

section

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable (K L : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

noncomputable def Phi : L ≃L[K] ((L ≃ₐ[K] L) → K) :=
  (IsGalois.normalBasis K L).equivFun.toContinuousLinearEquiv

variable {K L}

theorem Phi_symm_apply (c : (L ≃ₐ[K] L) → K) :
    (Phi K L).symm c = ∑ σ, c σ • σ (IsGalois.normalBasis K L 1) := by
  show (IsGalois.normalBasis K L).equivFun.symm c = _
  rw [Module.Basis.equivFun_symm_apply]
  exact Finset.sum_congr rfl fun σ _ => by rw [IsGalois.normalBasis_apply]

theorem Phi_map (σ : L ≃ₐ[K] L) (x : L) (τ : L ≃ₐ[K] L) : Phi K L (σ x) τ = Phi K L x (σ⁻¹ * τ) := by
  have : σ x = (Phi K L).symm (fun τ => Phi K L x (σ⁻¹ * τ)) := by
    rw [Phi_symm_apply]
    calc σ x = σ ((Phi K L).symm (Phi K L x)) := by simp
      _ = ∑ ρ, Phi K L x ρ • (σ * ρ) (IsGalois.normalBasis K L 1) := by

        rw [Phi_symm_apply, map_sum]
        exact Finset.sum_congr rfl fun ρ _ => by rw [map_smul]; rfl
      _ = ∑ τ, Phi K L x (σ⁻¹ * τ) • τ (IsGalois.normalBasis K L 1) :=
        Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun ρ => by simp)
  rw [this, ContinuousLinearEquiv.apply_symm_apply]

theorem norm_Phi_map (σ : L ≃ₐ[K] L) (x : L) : ‖Phi K L (σ x)‖ ≤ ‖Phi K L x‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro τ
  rw [Phi_map]
  exact norm_le_pi_norm _ _


variable (K L) in
noncomputable def proj1 : L →+ L where
  toFun x := Phi K L x 1 • IsGalois.normalBasis K L 1
  map_zero' := by simp
  map_add' x y := by rw [map_add (f := _), Pi.add_apply, add_smul]

theorem norm_Phi_proj1 (x : L) : ‖Phi K L (proj1 K L x)‖ ≤ ‖Phi K L x‖ := by
  classical
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro τ
  show ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1) τ‖ ≤ _
  rw [map_smul, Pi.smul_apply]
  have : Phi K L (IsGalois.normalBasis K L 1) τ = if 1 = τ then 1 else 0 :=
    Module.Basis.equivFun_self _ _ _
  rw [this, smul_eq_mul]
  split_ifs
  · rw [mul_one]; exact norm_le_pi_norm _ _
  · rw [mul_zero, norm_zero]; exact norm_nonneg _

theorem sum_proj1 (x : L) : ∑ σ : L ≃ₐ[K] L, σ • proj1 K L (σ⁻¹ • x) = x := by
  calc ∑ σ : L ≃ₐ[K] L, σ • proj1 K L (σ⁻¹ • x)
      = ∑ σ : L ≃ₐ[K] L, Phi K L x σ • σ (IsGalois.normalBasis K L 1) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        show σ (Phi K L (σ⁻¹ x) 1 • IsGalois.normalBasis K L 1) = _
        rw [map_smul, Phi_map, inv_inv, mul_one]
    _ = x := by rw [← Phi_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem norm_le_Phi (x : L) : ‖x‖ ≤ ‖((Phi K L).symm : ((L ≃ₐ[K] L) → K) →L[K] L)‖ * ‖Phi K L x‖ := by
  have := ((Phi K L).symm : ((L ≃ₐ[K] L) → K) →L[K] L).le_opNorm (Phi K L x)
  simpa using this

theorem norm_Phi_le (x : L) : ‖Phi K L x‖ ≤ ‖(Phi K L : L →L[K] ((L ≃ₐ[K] L) → K))‖ * ‖x‖ :=
  (Phi K L : L →L[K] ((L ≃ₐ[K] L) → K)).le_opNorm x

theorem exists_consts : ∃ A B C : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧ (∀ x : L, ‖x‖ ≤ A * ‖Phi K L x‖) ∧
    (∀ x : L, ‖Phi K L x‖ ≤ B * ‖x‖) ∧ ∀ x y : L, ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖ := by
  set A := ‖((Phi K L).symm : ((L ≃ₐ[K] L) → K) →L[K] L)‖
  set B := ‖(Phi K L : L →L[K] ((L ≃ₐ[K] L) → K))‖
  have hA : 0 ≤ A := norm_nonneg _
  have hB : 0 ≤ B := norm_nonneg _
  refine ⟨A, B, B * A * A, hA, hB, by positivity, norm_le_Phi, norm_Phi_le, fun x y => ?_⟩
  calc ‖Phi K L (x * y)‖ ≤ B * ‖x * y‖ := norm_Phi_le _
    _ = B * (‖x‖ * ‖y‖) := by rw [norm_mul]
    _ ≤ B * ((A * ‖Phi K L x‖) * (A * ‖Phi K L y‖)) := by
      gcongr
      · exact norm_le_Phi x
      · exact norm_le_Phi y
    _ = B * A * A * ‖Phi K L x‖ * ‖Phi K L y‖ := by ring


variable (K L) in
def ball (t : ℝ) (ht : 0 ≤ t) : AddSubgroup L where
  carrier := {x | ‖Phi K L x‖ ≤ t}
  zero_mem' := by simpa using ht
  add_mem' := fun {x y} hx hy => by
    show ‖Phi K L (x + y)‖ ≤ t
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  neg_mem' := fun {x} hx => by
    show ‖Phi K L (-x)‖ ≤ t
    rw [map_neg, norm_neg]; exact hx

theorem mem_ball {t : ℝ} {ht : 0 ≤ t} {x : L} : x ∈ ball K L t ht ↔ ‖Phi K L x‖ ≤ t := Iff.rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
end
end

-- Source module: ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandB

section

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {R : Type*} [Field R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]

def act (g : G) : Rˣ →* Rˣ := Units.map (MulSemiringAction.toRingHom G R g : R →* R)

theorem act_val (g : G) (u : Rˣ) : ((act g u : Rˣ) : R) = g • (u : R) := rfl


variable (G) in
def normU : Rˣ →* Rˣ := ∏ g : G, act g

theorem normU_val (u : Rˣ) : ((normU G u : Rˣ) : R) = ∏ g : G, g • (u : R) := by
  simp [normU, Units.coe_prod, act_val]

theorem smul_prod_univ (g : G) (x : R) : g • ∏ g' : G, g' • x = ∏ g' : G, g' • x := by
  rw [← MulSemiringAction.toRingHom_apply, map_prod]
  simp only [MulSemiringAction.toRingHom_apply, smul_smul]
  exact Fintype.prod_equiv (Equiv.mulLeft g) _ _ fun _ => rfl

theorem prod_smul_smul (g : G) (x : R) : ∏ g' : G, g' • g • x = ∏ g' : G, g' • x := by
  simp only [smul_smul]
  exact Fintype.prod_equiv (Equiv.mulRight g) _ _ fun _ => rfl

theorem sum_pow_eq {g₀ : G} (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (f : G → R) :
    ∑ k ∈ range (orderOf g₀), f (g₀ ^ k) = ∑ g, f g := by
  classical
  rw [← IsCyclic.image_range_orderOf hg, sum_image]
  intro a ha b hb hab
  exact pow_injOn_Iio_orderOf (by simpa using ha) (by simpa using hb) hab

theorem telescope (g₀ : G) (z : R) (k : ℕ) :
    g₀ • ∑ j ∈ range k, g₀ ^ j • z - ∑ j ∈ range k, g₀ ^ j • z = g₀ ^ k • z - z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, smul_add, smul_smul, ← pow_succ']
    linear_combination ih

namespace Filt

variable {I : ℕ → AddSubgroup R} {e : R →+ R} (h : Filt G I e)

include h

theorem act_mem {n : ℕ} (g : G) {u : Rˣ} (hu : u ∈ h.V n) : act g u ∈ h.V n := by
  rw [mem_V, act_val]
  have := h.smul n g _ hu
  rwa [smul_sub, smul_one] at this

theorem normU_mem {n : ℕ} {u : Rˣ} (hu : u ∈ h.V n) : normU G u ∈ h.V n := by
  rw [normU, MonoidHom.finsetProd_apply]
  exact (h.V n).prod_mem fun g _ => h.act_mem g hu

theorem norm_surj (u : Rˣ) (hu : (u : R) - 1 ∈ I 0) (hfix : ∀ g : G, g • (u : R) = u) :
    ∃ v : Rˣ, (v : R) - 1 ∈ I 0 ∧ ∏ g : G, g • (v : R) = u := by
  let Z : Subgroup Rˣ :=
    { carrier := {u | ∀ g : G, act g u = u}
      one_mem' := fun g => map_one _
      mul_mem' := fun {a b} ha hb g => by rw [map_mul, ha g, hb g]
      inv_mem' := fun {a} ha g => by rw [map_inv, ha g] }
  have step : ∀ n, ∀ u ∈ h.V n, u ∈ Z → ∃ v ∈ h.V n, u / normU G v ∈ h.V (n + 1) := by
    intro n u hu hZ
    have hx : ∀ g : G, g • ((u : R) - 1) = (u : R) - 1 := fun g => by
      rw [smul_sub, smul_one, ← act_val, hZ g]
    have hy : e ((u : R) - 1) ∈ I n := h.e_mem n _ hu
    have htr : ∑ g : G, g • e ((u : R) - 1) = (u : R) - 1 := by
      conv_rhs => rw [← h.e_sum ((u : R) - 1)]
      exact Finset.sum_congr rfl fun g _ => by rw [hx]
    refine ⟨h.mkU _ (h.le_zero n hy), h.mkU_mem _ hy, h.div_mem_V (h.normU_mem (h.mkU_mem _ (h.le_zero n hy))) ?_⟩
    have hp := h.prod_one_add (n := n) univ (fun g : G => g • e ((u : R) - 1)) (fun g _ => h.smul n g _ hy)
    rw [htr] at hp
    rw [normU_val, mkU_val]
    simp only [smul_add, smul_one]
    have := (I (n + 1)).neg_mem hp
    convert this using 1
    ring
  obtain ⟨v, hv, hvu⟩ := exists_of_approx h.V h.V_comp h.V_sep Z (normU G)
    (fun n u hu => h.normU_mem hu)
    (fun u g => Units.ext (by rw [act_val, normU_val, smul_prod_univ])) step u hu
    (fun g => Units.ext (hfix g))
  exact ⟨v, hv, by rw [← normU_val, hvu]⟩

theorem hilbert90_matrix_subalgebra_norm_one (g₀ : G) (hg : ∀ g, g ∈ Subgroup.zpowers g₀) (u : Rˣ) (hu : (u : R) - 1 ∈ I 0)
    (hN : ∏ g : G, g • (u : R) = 1) :
    ∃ v : Rˣ, (v : R) - 1 ∈ I 0 ∧ g₀ • (v : R) = u * v := by
  have step : ∀ n, ∀ u ∈ h.V n, u ∈ (normU G).ker →
      ∃ v ∈ h.V n, u / (act g₀ / MonoidHom.id _ : Rˣ →* Rˣ) v ∈ h.V (n + 1) := by
    intro n u hu hZ
    set x : R := (u : R) - 1 with hxdef
    have hx : x ∈ I n := hu
    have hux : (u : R) = 1 + x := by rw [hxdef]; ring
    have htr : ∑ g : G, g • x ∈ I (n + 1) := by
      have hp := h.prod_one_add (n := n) univ (fun g : G => g • x) (fun g _ => h.smul n g _ hx)
      have h1 : ∏ g : G, (1 + g • x) = 1 := by
        have := congrArg Units.val (MonoidHom.mem_ker.1 hZ)
        rw [normU_val, hux] at this
        simpa only [smul_add, smul_one, Units.val_one] using this
      rw [h1, sub_self, zero_sub] at hp
      simpa using (I (n + 1)).neg_mem hp
    set y : R := ∑ k ∈ range (orderOf g₀), ∑ j ∈ range k, g₀ ^ j • e ((g₀ ^ k)⁻¹ • x) with hydef
    have hy : y ∈ I n := (I n).sum_mem fun k _ => (I n).sum_mem fun j _ =>
      h.smul n _ _ (h.e_mem n _ (h.smul n _ _ hx))
    have hd : g₀ • y - y = x - e (∑ g : G, g • x) := by
      rw [hydef, smul_sum, ← sum_sub_distrib]
      simp only [telescope]

      rw [sum_sub_distrib, sum_pow_eq hg (fun g => g • e (g⁻¹ • x)), h.e_sum, ← map_sum,
      sum_pow_eq hg (fun g => g⁻¹ • x)]
      congr 2
      exact Fintype.sum_equiv (Equiv.inv G) _ _ fun _ => rfl
    have hy0 := h.le_zero n hy
    have hvV : h.mkU y hy0 ∈ h.V n := h.mkU_mem y hy
    refine ⟨h.mkU y hy0, hvV, h.div_mem_V
      ((h.V 0).div_mem (h.act_mem g₀ (h.V_le_zero n hvV)) (h.V_le_zero n hvV)) ?_⟩
    set z : R := (1 + y)⁻¹ - 1 with hzdef
    have hz : z ∈ I n := h.inv n y hy
    have hyz : (1 + y) * (1 + z) = 1 := by
      rw [hzdef, add_sub_cancel, mul_inv_cancel₀ (h.one_add_ne_zero hy0)]
    have hval : (((act g₀ / MonoidHom.id _ : Rˣ →* Rˣ) (h.mkU y hy0) : Rˣ) : R) = (1 + g₀ • y) * (1 + z) := by
      rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_mul_inv, Units.val_mul, act_val,
        Units.val_inv_eq_inv_val, mkU_val, smul_add, smul_one, hzdef, add_sub_cancel]
    rw [hval, hux]
    have : 1 + x - (1 + g₀ • y) * (1 + z) = e (∑ g : G, g • x) - (g₀ • y - y) * z := by
      linear_combination -hyz - hd
    rw [this]
    exact (I (n + 1)).sub_mem (h.e_mem _ _ htr)
      (h.mul n _ _ ((I n).sub_mem (h.smul n _ _ hy) hy) (h.le_zero n hz))
  obtain ⟨v, hv, hvu⟩ := exists_of_approx h.V h.V_comp h.V_sep (normU G).ker (act g₀ / MonoidHom.id _)
    (fun n u hu => (h.V n).div_mem (h.act_mem g₀ hu) hu)
    (fun u => by
      rw [MonoidHom.mem_ker, MonoidHom.div_apply, MonoidHom.id_apply, map_div, div_eq_one]
      exact Units.ext (by rw [normU_val, normU_val, act_val, prod_smul_smul])) step u hu
    (Units.ext (by rw [normU_val, hN]; rfl))
  refine ⟨v, hv, ?_⟩
  rw [MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul] at hvu
  rw [← act_val, hvu, Units.val_mul]

end Filt

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
end
end

-- Source module: ReciprocityTheory.ClassFieldTheory.LocalClassField.UnitsHerbrandD

section

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt

open Finset

variable {K L : Type*} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]

theorem rad_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) (n : ℕ) : 0 ≤ ρ * (1 / 2 : ℝ) ^ n := by positivity

theorem filt_ball {A C ρ : ℝ} (hC : 0 ≤ C) (hρ : 0 ≤ ρ) (hA1 : ∀ x : L, ‖x‖ ≤ A * ‖Phi K L x‖) (hA : 0 ≤ A)
    (hC1 : ∀ x y : L, ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖)
    (hAρ : A * ρ < 1) (hCρ : C * ρ ≤ 1 / 2) :
    Filt (L ≃ₐ[K] L) (fun n => ball (K := K) (L := L) (ρ * (1 / 2 : ℝ) ^ n) (rad_nonneg hρ n)) (proj1 (K := K) (L := L)) := by
  refine {
    anti := ?_
    mul := ?_
    smul := ?_
    comp := ?_
    sep := ?_
    inv := ?_
    e_mem := ?_
    e_sum := ?_ }
  · intro n x hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ (n + 1) at hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n
    refine hx.trans ?_
    rw [pow_succ]
    nlinarith [rad_nonneg hρ n]
  · intro n x y hx hy
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n at hx
    change ‖Phi K L y‖ ≤ ρ * (1 / 2 : ℝ) ^ 0 at hy
    change ‖Phi K L (x * y)‖ ≤ ρ * (1 / 2 : ℝ) ^ (n + 1)
    rw [pow_zero, mul_one] at hy
    calc ‖Phi K L (x * y)‖ ≤ C * ‖Phi K L x‖ * ‖Phi K L y‖ := hC1 x y
      _ ≤ C * (ρ * (1 / 2 : ℝ) ^ n) * ρ := by gcongr
      _ = (C * ρ) * (ρ * (1 / 2 : ℝ) ^ n) := by ring
      _ ≤ (1 / 2) * (ρ * (1 / 2 : ℝ) ^ n) := by
        exact mul_le_mul_of_nonneg_right hCρ (rad_nonneg hρ n)
      _ = ρ * (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
  · intro n g x hx
    exact (norm_Phi_map g x).trans hx
  · intro x hx
    have hx' : ∀ k, ‖Phi K L (x k)‖ ≤ ρ * (1 / 2 : ℝ) ^ k := fun k => by
      exact hx k
    have hsum : Summable fun k => Phi K L (x k) :=
      Summable.of_norm_bounded ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left ρ) hx'
    refine ⟨(Phi K L).symm (∑' k, Phi K L (x k)), fun n => ?_⟩
    change ‖Phi K L ((Phi K L).symm (∑' k, Phi K L (x k)) - ∑ k ∈ range n, x k)‖ ≤ ρ * (1 / 2 : ℝ) ^ n

    rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, map_sum,
    ← hsum.sum_add_tsum_nat_add n, add_sub_cancel_left]
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (rad_nonneg hρ n) fun k => ?_
    refine (hx' (k + n)).trans ?_
    gcongr ρ * ?_
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_left n k)
  · intro x hx
    have hx' : ∀ n, ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n := hx
    have hlim : Filter.Tendsto (fun n : ℕ => ρ * (1 / 2 : ℝ) ^ n) Filter.atTop (nhds (ρ * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul ρ
    have h0 : ‖Phi K L x‖ ≤ ρ * 0 := ge_of_tendsto' hlim hx'
    rw [mul_zero] at h0
    have := norm_le_zero_iff.1 h0
    simpa using this
  · intro n x hx
    change ‖Phi K L x‖ ≤ ρ * (1 / 2 : ℝ) ^ n at hx
    change ‖Phi K L ((1 + x)⁻¹ - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ n
    have hr : ρ * (1 / 2 : ℝ) ^ n ≤ ρ := by
      have : (1 / 2 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    have hxlt : ‖x‖ < 1 := by
      refine lt_of_le_of_lt ((hA1 x).trans ?_) hAρ
      gcongr
      exact hx.trans hr
    have hne : 1 + x ≠ 0 := by
      intro h0
      have : x = -1 := by linear_combination h0
      rw [this, norm_neg, norm_one] at hxlt
      exact lt_irrefl _ hxlt
    set y : L := (1 + x)⁻¹ - 1 with hy
    have hy1 : y = -x + -(x * y) := by
      rw [hy]; field_simp; ring
    have h1 : ‖Phi K L y‖ ≤ max ‖Phi K L x‖ ‖Phi K L (x * y)‖ := by
      conv_lhs => rw [hy1, map_add (f := _), map_neg, map_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
      rw [norm_neg, norm_neg]
    have h2 : ‖Phi K L (x * y)‖ ≤ (1 / 2) * ‖Phi K L y‖ := by
      refine (hC1 x y).trans ?_
      gcongr
      refine le_trans ?_ hCρ
      gcongr
      exact hx.trans hr
    rcases le_max_iff.1 h1 with h3 | h3
    · exact h3.trans hx
    · have : ‖Phi K L y‖ ≤ 0 := by linarith
      exact this.trans (rad_nonneg hρ n)
  · intro n x hx
    classical
    have hbound : ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1)‖ ≤ ‖Phi K L x‖ := by
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro τ
      show ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1) τ‖ ≤ _
      rw [map_smul, Pi.smul_apply]
      have h : Phi K L (IsGalois.normalBasis K L 1) τ = if 1 = τ then 1 else 0 :=
        Module.Basis.equivFun_self _ _ _
      rw [h, smul_eq_mul]
      split_ifs
      · rw [mul_one]
        exact norm_le_pi_norm _ _
      · rw [mul_zero, norm_zero]
        exact norm_nonneg _
    exact hbound.trans (by change ‖Phi K L x‖ ≤ _; exact hx)
  · intro x
    calc ∑ σ : L ≃ₐ[K] L, σ • proj1 (K := K) (L := L) (σ⁻¹ • x)
        = ∑ σ : L ≃ₐ[K] L, Phi K L x σ • σ (IsGalois.normalBasis K L 1) := by
          refine Finset.sum_congr rfl fun σ _ => ?_
          show σ (Phi K L (σ⁻¹ • x) 1 • IsGalois.normalBasis K L 1) = _
          rw [map_smul]
          congr 1
          have h := Phi_map (σ⁻¹) x (1 : L ≃ₐ[K] L)
          simpa [inv_inv] using h
      _ = x := by
        rw [← Phi_symm_apply, ContinuousLinearEquiv.symm_apply_apply]

theorem exists_units_subgroup [IsUltrametricDist L] : ∃ S : Subgroup Lˣ,
    (∀ (σ : L ≃ₐ[K] L) (u v : Lˣ), u ∈ S → (v : L) = σ u → v ∈ S) ∧
    (∀ u ∈ S, ‖(u : L)‖ = 1) ∧ (∃ ε : ℝ, 0 < ε ∧ ∀ u : Lˣ, ‖(u : L) - 1‖ < ε → u ∈ S) ∧
    (∀ u ∈ S, (∀ σ : L ≃ₐ[K] L, σ (u : L) = u) → ∃ v ∈ S, ∏ σ : L ≃ₐ[K] L, σ (v : L) = u) ∧
    ∀ σ₀ : L ≃ₐ[K] L, (∀ σ, σ ∈ Subgroup.zpowers σ₀) → ∀ u ∈ S, ∏ σ : L ≃ₐ[K] L, σ (u : L) = 1 →
      ∃ v ∈ S, σ₀ (v : L) = u * v := by
  obtain ⟨A, B, C, hA, hB, hC, hA1, hB1, hC1⟩ := exists_consts (K := K) (L := L)
  set ρ : ℝ := (2 * (C + A + 1))⁻¹ with hρdef
  have hpos : 0 < 2 * (C + A + 1) := by positivity
  have hρ : 0 < ρ := inv_pos.2 hpos
  have hρ1 : ρ * (2 * (C + A + 1)) = 1 := inv_mul_cancel₀ hpos.ne'
  have hAρ : A * ρ < 1 := by nlinarith [mul_nonneg hC hρ.le, mul_nonneg hA hρ.le]
  have hCρ : C * ρ ≤ 1 / 2 := by nlinarith [mul_nonneg hC hρ.le, mul_nonneg hA hρ.le]
  have F := filt_ball hC hρ.le hA1 hA hC1 hAρ hCρ
  refine ⟨F.V 0, fun σ u v hu hv => ?_, fun u hu => ?_, ⟨ρ / (B + 1), by positivity, fun u hu => ?_⟩,
    fun u hu hfix => F.norm_surj u hu hfix, fun σ₀ hσ₀ u hu hN => F.hilbert90_matrix_subalgebra_norm_one σ₀ hσ₀ u hu hN⟩
  · have : v = act σ u := Units.ext hv
    rw [this]
    exact F.act_mem σ hu
  · have hu' : ‖Phi K L ((u : L) - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ 0 := hu
    rw [pow_zero, mul_one] at hu'
    have hlt : ‖(u : L) - 1‖ < 1 := by
      refine lt_of_le_of_lt ((hA1 _).trans ?_) hAρ
      gcongr
    have h1 : (u : L) = 1 + ((u : L) - 1) := by ring
    rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hlt.ne'), norm_one]
    exact max_eq_left hlt.le
  · show ‖Phi K L ((u : L) - 1)‖ ≤ ρ * (1 / 2 : ℝ) ^ 0
    rw [pow_zero, mul_one]
    refine (hB1 _).trans ?_
    have h2 : B * ‖(u : L) - 1‖ ≤ (B + 1) * (ρ / (B + 1)) := by
      gcongr
      · linarith
    refine h2.trans (le_of_eq ?_)
    field_simp

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
end
end
