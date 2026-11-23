module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemBalBil
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.GlActionMemBalFormsOfSemilinear
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulFinrankBalancedSymmIntBilinFormsStatement
import Mathlib.Algebra.Order.Star.Int
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeSubmoduleFiniteIndexNumberField

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

namespace GlobalTheory

theorem latt_free_sub_full_rank {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    ∃ (f : (Fin (Module.finrank (𝓞 E) X) → 𝓞 E) →ₗ[𝓞 E] X) (m : ℕ), 0 < m ∧
      Function.Injective f ∧ ∀ x : X, m • x ∈ LinearMap.range f := by
  classical
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  set r := Module.finrank (𝓞 E) X
  obtain ⟨e, he⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) (le_refl r)
  let f : (Fin r → 𝓞 E) →ₗ[𝓞 E] X := Fintype.linearCombination (𝓞 E) e
  have hfv' : ∀ c : Fin r → 𝓞 E, f c = ∑ i, c i • e i := fun c => by
    simp [f, Fintype.linearCombination_apply]
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    rw [hfv'] at hc
    exact funext ((Fintype.linearIndependent_iff.mp he) c hc)

  have key : ∀ x : X, ∃ n : ℕ, 0 < n ∧ n • x ∈ LinearMap.range f := by
    intro x
    have hdep : ¬ LinearIndependent (𝓞 E) (Fin.cons x e : Fin (r + 1) → X) := by
      intro h
      have := h.fintype_card_le_finrank
      simp [r] at this
    rw [Fintype.not_linearIndependent_iff] at hdep
    obtain ⟨g, hg, i, hi⟩ := hdep
    rw [Fin.sum_univ_succ] at hg
    simp only [Fin.cons_zero, Fin.cons_succ] at hg
    have ha : g 0 ≠ 0 := by
      intro h0
      rw [h0, zero_smul, zero_add] at hg
      have hz := (Fintype.linearIndependent_iff.mp he) (fun j => g j.succ) hg
      refine hi ?_
      refine Fin.cases h0 (fun j => hz j) i
    have hax : g 0 • x ∈ LinearMap.range f := by
      refine ⟨fun j => - g j.succ, ?_⟩
      rw [hfv']
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact (neg_eq_of_add_eq_zero_left hg)
    have hI : Ideal.span {g 0} ≠ ⊥ := by simpa using ha
    have hN : Ideal.absNorm (Ideal.span {g 0}) ≠ 0 := by
      rwa [Ne, Ideal.absNorm_eq_zero_iff]
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {g 0}))
    refine ⟨Ideal.absNorm (Ideal.span {g 0}), Nat.pos_of_ne_zero hN, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E), ← hb, mul_smul]
    exact Submodule.smul_mem _ _ hax
  choose N hNpos hNmem using key
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := X)
  refine ⟨f, ∏ s ∈ S, N s, Finset.prod_pos (fun s _ => hNpos s), hf, ?_⟩
  have hgen : ∀ s ∈ S, (∏ t ∈ S, N t) • s ∈ LinearMap.range f := by
    intro s hs
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem N hs
    rw [hk, mul_comm, mul_smul]
    exact AddSubmonoid.nsmul_mem (LinearMap.range f).toAddSubmonoid (hNmem s) k
  intro x
  have hx : x ∈ Submodule.span ℤ (S : Set X) := by rw [hS]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact hgen y hy
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_comm]
    exact zsmul_mem hy a

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeSubmoduleFiniteIndexNumberFieldStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.exists_free_submodule_finite_index_numberField : ∀ {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], ∃ (f : (Fin (Module.finrank (𝓞 E) X) → 𝓞 E) →ₗ[𝓞 E] X) (m : ℕ), 0 < m ∧ Function.Injective f ∧ ∀ x : X, m • x ∈ LinearMap.range f := by
  first | exact @GlobalTheory.latt_free_sub_full_rank | exact GlobalTheory.latt_free_sub_full_rank | (intros; apply GlobalTheory.latt_free_sub_full_rank <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedIntBilinFormsEqOfFiniteIndex

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.BalRank

theorem finrank_balBil_le_of_smul_mem_range {O : Type} [CommRing O] (bar : O → O) (X Y : Type)
    [AddCommGroup X] [Module O X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (f : Y →ₗ[O] X) (m : ℕ) (hm : 0 < m) (hf : ∀ x : X, m • x ∈ LinearMap.range f) :
    Module.finrank ℤ (balBil bar X) ≤ Module.finrank ℤ (balBil bar Y) := by
  let f' : Y →ₗ[ℤ] X := f.toAddMonoidHom.toIntLinearMap
  have hf' : ∀ y, f' y = f y := fun y => rfl
  let Φ : balBil bar X →ₗ[ℤ] balBil bar Y :=
    { toFun := fun β => ⟨(β : LinearMap.BilinForm ℤ X).compl₁₂ f' f', by
        intro a y z
        have := β.2 a (f y) (f z)
        simpa [hf', LinearMap.compl₁₂_apply, map_smul] using this⟩
      map_add' := fun β β' => by ext; simp
      map_smul' := fun n β => by ext; simp }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro β hβ
    ext x x'
    obtain ⟨y, hy⟩ := hf x
    obtain ⟨y', hy'⟩ := hf x'
    have h0 : (β : LinearMap.BilinForm ℤ X) (f y) (f y') = 0 := by
      have := congrArg (fun γ : balBil bar Y => (γ : LinearMap.BilinForm ℤ Y) y y') hβ
      simpa [Φ, hf'] using this
    rw [hy, hy'] at h0
    have h1 : ((m : ℤ) * m) * (β : LinearMap.BilinForm ℤ X) x x' = 0 := by
      rw [← h0]
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      ring
    have hm' : ((m : ℤ) * m) ≠ 0 := by positivity
    simpa using (mul_eq_zero.mp h1).resolve_left hm'
  exact LinearMap.finrank_le_finrank_of_injective hinj

theorem finrank_balBil_eq_of_finiteIndex {O : Type} [CommRing O] (bar : O → O) (X Y : Type)
    [AddCommGroup X] [Module O X] [Module.Free ℤ X] [Module.Finite ℤ X]
    [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
    (f : Y →ₗ[O] X) (m : ℕ) (hm : 0 < m) (hf : Function.Injective f)
    (hr : ∀ x : X, m • x ∈ LinearMap.range f) :
    Module.finrank ℤ (balBil bar Y) = Module.finrank ℤ (balBil bar X) := by
  let e := LinearEquiv.ofInjective f hf
  let c : X →ₗ[O] LinearMap.range f :=
    LinearMap.codRestrict (LinearMap.range f) (m • LinearMap.id) (fun x => by simpa using hr x)
  let g : X →ₗ[O] Y := e.symm.toLinearMap ∘ₗ c
  have hfg : ∀ x, f (g x) = m • x := by
    intro x
    have h1 : e (g x) = c x := by simp [g]
    have h2 := congrArg Subtype.val h1
    simpa [e, c] using h2
  have hgf : ∀ y, g (f y) = m • y := by
    intro y; apply hf; rw [hfg, map_nsmul]
  apply le_antisymm
  · exact finrank_balBil_le_of_smul_mem_range bar Y X g m hm (fun y => ⟨f y, hgf y⟩)
  · exact finrank_balBil_le_of_smul_mem_range bar X Y f m hm hr

end GlobalTheory.BalRank
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedIntBilinFormsEqOfFiniteIndexStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.finrank_balancedIntBilinForms_eq_of_finite_index : ∀ {O : Type} [CommRing O] (bar : O → O) (X Y : Type) [AddCommGroup X] [Module O X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup Y] [Module O Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (f : Y →ₗ[O] X) (m : ℕ), 0 < m → Function.Injective f → (∀ x : X, m • x ∈ LinearMap.range f) → Module.finrank ℤ (GlobalTheory.BalRank.balBil bar Y) = Module.finrank ℤ (GlobalTheory.BalRank.balBil bar X) := by
  first | exact @GlobalTheory.BalRank.finrank_balBil_eq_of_finiteIndex | exact GlobalTheory.BalRank.finrank_balBil_eq_of_finiteIndex | (intros; apply GlobalTheory.BalRank.finrank_balBil_eq_of_finiteIndex <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedIntBilinFormsPi

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.BalRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (J : Type) [Fintype J] [DecidableEq J]

def formOfFamily (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) : LinearMap.BilinForm ℤ (J → 𝓞 E) :=
  LinearMap.mk₂ ℤ (fun y z => ∑ i, ∑ j, φ i j (H.bar (y i) * z j))
    (by intro y y' z; simp [map_add (f := _), add_mul, Finset.sum_add_distrib])
    (by intro c y z; simp only [Pi.smul_apply, map_zsmul, smul_mul_assoc, Finset.smul_sum])
    (by intro y z z'; simp [map_add (f := _), mul_add, Finset.sum_add_distrib])
    (by intro c y z; simp only [Pi.smul_apply, map_zsmul, mul_smul_comm, Finset.smul_sum])

theorem formOfFamily_apply (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) (y z : J → 𝓞 E) :
    formOfFamily H J φ y z = ∑ i, ∑ j, φ i j (H.bar (y i) * z j) := rfl

theorem formOfFamily_mem (φ : J → J → (𝓞 E →ₗ[ℤ] ℤ)) : formOfFamily H J φ ∈ balBil H.bar (J → 𝓞 E) := by
  intro a y z
  simp only [formOfFamily_apply, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring_nf

def balBilEquiv : balBil H.bar (J → 𝓞 E) ≃ₗ[ℤ] (J → J → (𝓞 E →ₗ[ℤ] ℤ)) where
  toFun β := fun i j => (β.1 (Pi.single i 1)) ∘ₗ LinearMap.single ℤ (fun _ : J => 𝓞 E) j
  map_add' β β' := by ext; simp
  map_smul' c β := by ext; simp
  invFun φ := ⟨formOfFamily H J φ, formOfFamily_mem H J φ⟩
  left_inv β := by
    apply Subtype.ext
    refine LinearMap.ext₂ fun y z => ?_
    simp only [formOfFamily_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    have hy : y = ∑ i, y i • (Pi.single i (1 : 𝓞 E) : J → 𝓞 E) := by
      conv_lhs => rw [← Finset.univ_sum_single y]
      refine Finset.sum_congr rfl fun i _ => ?_
      ext k
      rcases eq_or_ne k i with rfl | h <;> simp [*]
    conv_rhs => rw [hy]

    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [β.2 (y i) (Pi.single i 1) z]
    conv_rhs => rw [← Finset.univ_sum_single (H.bar (y i) • z)]

    rw [map_sum]
    rfl
  right_inv φ := by
    funext i j
    refine LinearMap.ext fun c => ?_
    simp only [formOfFamily_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single]
    rw [Finset.sum_eq_single i, Finset.sum_eq_single j]
    · simp
    · intro j' _ hj; simp [Pi.single_apply, hj]
    · simp
    · intro i' _ hi; simp [Pi.single_apply, hi]
    · simp

theorem finrank_balBil_pi : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (J : Type) [Fintype J]
    [DecidableEq J], Module.finrank ℤ (GlobalTheory.BalRank.balBil H.bar (J → 𝓞 E)) =
      Module.finrank ℚ E * Fintype.card J * Fintype.card J := by
  intro E _ _ _ H J _ _
  rw [(balBilEquiv H J).finrank_eq, Module.finrank_pi_fintype]
  simp only [Module.finrank_pi_fintype, Module.finrank_linearMap, Module.finrank_self, mul_one,
    NumberField.RingOfIntegers.rank, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

end GlobalTheory.BalRank
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedIntBilinFormsPiStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PolFan

theorem _root_.GlobalTheory.T.finrank_balancedIntBilinForms_pi : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (J : Type) [Fintype J] [DecidableEq J], Module.finrank ℤ (GlobalTheory.BalRank.balBil H.bar (J → 𝓞 E)) = Module.finrank ℚ E * Fintype.card J * Fintype.card J := by
  first | exact @GlobalTheory.BalRank.finrank_balBil_pi | exact GlobalTheory.BalRank.finrank_balBil_pi | (intros; apply GlobalTheory.BalRank.finrank_balBil_pi <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankBalancedSymmIntBilinFormsEq

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.BalRank.finrank_balForms : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X], Module.finrank ℤ (balForms H.bar X) = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) X * Module.finrank (𝓞 E) X := by
  intro E _ _ _ H X _ _ _ _
  obtain ⟨f, m, hm, hf, hmf⟩ := GlobalTheory.T.exists_free_submodule_finite_index_numberField (E := E) X
  have h1 := GlobalTheory.T.two_mul_finrank_balancedSymmIntBilinForms H X
  have h2 := GlobalTheory.T.finrank_balancedIntBilinForms_eq_of_finite_index H.bar X _ f m hm hf hmf
  have h3 := GlobalTheory.T.finrank_balancedIntBilinForms_pi H (Fin (Module.finrank (𝓞 E) X))
  rw [Fintype.card_fin] at h3
  obtain ⟨k, hk⟩ : 2 ∣ Module.finrank ℚ E := ⟨_, IsTotallyComplex.finrank E⟩
  rw [hk, Nat.mul_div_cancel_left _ two_pos]
  rw [← h2, h3, hk] at h1
  nlinarith [h1]
end
end
