module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearMap
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.TotallySplit
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonoHom

section

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.MonoHom

variable {X : Type} [AddCommGroup X] {K : Type} [Field K]

def pform {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) : LinearMap.BilinForm ℤ X :=
  (e.coord i).smulRight (e.coord j)

@[simp] theorem pform_apply {ι : Type} (e : Module.Basis ι ℤ X) (i j : ι) (x y : X) :
    pform e i j x y = e.coord i x * e.coord j y := by
  simp [pform]

end GlobalTheory.MonoHom

namespace GlobalTheory.MonoHom

end GlobalTheory.MonoHom
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueNthRoots

section

@[expose] public section

open GlobalTheory.MonoHom

noncomputable section

namespace GlobalTheory.PerRoot

variable {X : Type} [AddCommGroup X]

def halfForm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j : Fin r) : LinearMap.BilinForm ℤ X :=
  if i < j then pform e i j + pform e j i else if i = j then pform e i i else 0

theorem halfForm_symm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j : Fin r) (x y : X) :
    halfForm e i j x y = halfForm e i j y x := by
  unfold halfForm; split_ifs <;> simp [pform_apply] <;> ring

theorem halfForm_basis {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (i j i₀ j₀ : Fin r) :
    halfForm e i j (e i₀) (e j₀) = if i = min i₀ j₀ ∧ j = max i₀ j₀ then 1 else 0 := by
  unfold halfForm
  rcases lt_trichotomy i₀ j₀ with h | rfl | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega
  · simp only [min_self, max_self]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega
  · rw [min_eq_right h.le, max_eq_left h.le]
    split_ifs <;> simp [pform_apply, Module.Basis.coord_apply, Finsupp.single_apply] <;> (try split_ifs) <;> (try subst_vars) <;> omega

theorem eq_sum_halfForm {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ x y, β x y = β y x) :
    β = ∑ p : Fin r × Fin r, β (e p.1) (e p.2) • halfForm e p.1 p.2 := by
  refine LinearMap.ext_basis e e fun i₀ j₀ => ?_
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, halfForm_basis, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (min i₀ j₀, max i₀ j₀)]
  · simp only [and_self, if_true]
    rcases le_total i₀ j₀ with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h, hβ]
  · intro p _ hp; rw [if_neg]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
  · intro h; exact absurd (Finset.mem_univ _) h

theorem bimul_ext {G : Type} [CommGroup G] {r : ℕ} (e : Module.Basis (Fin r) ℤ X) (f g : X → X → G)
    (hf : ∀ a a' b, f (a + a') b = f a b * f a' b) (hf' : ∀ a b b', f a (b + b') = f a b * f a b')
    (hg : ∀ a a' b, g (a + a') b = g a b * g a' b) (hg' : ∀ a b b', g a (b + b') = g a b * g a b')
    (h : ∀ i j, f (e i) (e j) = g (e i) (e j)) : f = g := by
  have key : ∀ (φ ψ : X → G), (∀ a a', φ (a + a') = φ a * φ a') → (∀ a a', ψ (a + a') = ψ a * ψ a') →
      (∀ i, φ (e i) = ψ (e i)) → φ = ψ := by
    intro φ ψ hφ hψ hi
    let Φ : X →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (φ a)) (fun a a' => by simp [hφ])
    let Ψ : X →+ Additive G := AddMonoidHom.mk' (fun a => Additive.ofMul (ψ a)) (fun a a' => by simp [hψ])
    have hL : Φ.toIntLinearMap = Ψ.toIntLinearMap := e.ext fun i => by simp [Φ, Ψ, hi]
    funext a
    have := congrArg (fun L : X →ₗ[ℤ] Additive G => Additive.toMul (L a)) hL
    simpa [Φ, Ψ] using this
  have h1 : ∀ j a, f a (e j) = g a (e j) := fun j => congrFun
    (key (fun a => f a (e j)) (fun a => g a (e j)) (fun a a' => hf a a' _) (fun a a' => hg a a' _) (fun i => h i j))
  funext a
  exact key (f a) (g a) (hf' a) (hg' a) (fun j => h1 j a)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def IsSymBasis (ε : ι → LinearMap.BilinForm ℤ X) : Prop :=
  (∀ k x y, ε k x y = ε k y x) ∧ LinearIndependent ℤ ε ∧
    ∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → β ∈ Submodule.span ℤ (Set.range ε)

theorem exists_coords {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) {r : ℕ} (e : Module.Basis (Fin r) ℤ X) :
    ∃ c : Fin r × Fin r → ι → ℤ, ∀ p, ∑ k, c p k • ε k = halfForm e p.1 p.2 := by
  have : ∀ p : Fin r × Fin r, ∃ c : ι → ℤ, ∑ k, c k • ε k = halfForm e p.1 p.2 := fun p =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hε.2.2 _ (halfForm_symm e p.1 p.2))
  choose c hc using this
  exact ⟨c, hc⟩

theorem dual_coords {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) {r : ℕ} (e : Module.Basis (Fin r) ℤ X)
    {c : Fin r × Fin r → ι → ℤ} (hc : ∀ p, ∑ k, c p k • ε k = halfForm e p.1 p.2) (k' k : ι) :
    ∑ p, ε k' (e p.1) (e p.2) * c p k = if k' = k then 1 else 0 := by
  have h1 : ε k' = ∑ k, (∑ p, ε k' (e p.1) (e p.2) * c p k) • ε k := by
    conv_lhs => rw [eq_sum_halfForm e (ε k') (hε.1 k')]
    simp_rw [← hc, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  have h2 : ε k' = ∑ k, (if k' = k then (1 : ℤ) else 0) • ε k := by simp
  have h3 : ∑ k, ((∑ p, ε k' (e p.1) (e p.2) * c p k) - (if k' = k then 1 else 0)) • ε k = 0 := by
    simp_rw [sub_smul, Finset.sum_sub_distrib, ← h1, ← h2, sub_self]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hε.2.1 _ h3 k)

variable {G : Type} [CommGroup G]

theorem zpow_sumF {κ : Type} (s : Finset κ) (a : G) (f : κ → ℤ) : a ^ (∑ p ∈ s, f p) = ∏ p ∈ s, a ^ f p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

theorem eq_one_of_prod_zpow {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (u : ι → G) (h : ∀ x y, ∏ k, u k ^ ε k x y = 1) (k : ι) : u k = 1 := by
  let e := Module.finBasis ℤ X
  obtain ⟨c, hc⟩ := exists_coords hε e
  calc u k = ∏ k', u k' ^ (if k' = k then (1 : ℤ) else 0) := by simp
    _ = ∏ k', u k' ^ (∑ p, ε k' (e p.1) (e p.2) * c p k) := by simp_rw [dual_coords hε e hc]
    _ = ∏ p, (∏ k', u k' ^ ε k' (e p.1) (e p.2)) ^ c p k := by
      simp_rw [← Finset.prod_zpow, zpow_sumF, ← zpow_mul]
      exact Finset.prod_comm
    _ = 1 := by simp [h]

theorem existsUnique_coeff {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (q : X → X → G) (hsym : ∀ x y, q x y = q y x) (hadd : ∀ x x' y, q (x + x') y = q x y * q x' y) :
    ∃! σ : ι → G, ∀ x y, q x y = ∏ k, σ k ^ ε k x y := by
  let e := Module.finBasis ℤ X
  obtain ⟨c, hc⟩ := exists_coords hε e
  have hadd' : ∀ x y y', q x (y + y') = q x y * q x y' := fun x y y' => by
    rw [hsym, hadd, hsym y, hsym y']
  have hF : ∀ x y, ∏ k, (∏ p, q (e p.1) (e p.2) ^ c p k) ^ ε k x y =
      ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X), q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y := by
    intro x y
    simp_rw [← Finset.prod_zpow, ← zpow_mul]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← zpow_sumF, ← hc p]
    simp [LinearMap.sum_apply, mul_comm]
  refine ⟨fun k => ∏ p, q (e p.1) (e p.2) ^ c p k, fun x y => ?_, fun σ hσ => funext fun k => ?_⟩
  · rw [hF]
    have := bimul_ext e q (fun x y => ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X),
        q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y) hadd hadd'
      (fun a a' b => by simp only [map_add (f := _), LinearMap.add_apply, zpow_add, Finset.prod_mul_distrib])
      (fun a b b' => by simp only [map_add (f := _), zpow_add, Finset.prod_mul_distrib])
      (fun i j => by
        simp only [halfForm_basis]
        rw [Finset.prod_eq_single (min i j, max i j)]
        · simp only [and_self, if_true, zpow_one]
          rcases le_total i j with h | h
          · rw [min_eq_left h, max_eq_right h]
          · rw [min_eq_right h, max_eq_left h, hsym]
        · intro p _ hp; rw [if_neg, zpow_zero]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
        · intro h; exact absurd (Finset.mem_univ _) h)
    exact congrFun (congrFun this x) y
  · have h0 : ∀ x y, ∏ k, (σ k / ∏ p, q (e p.1) (e p.2) ^ c p k) ^ ε k x y = 1 := fun x y => by
      simp_rw [div_zpow, Finset.prod_div_distrib, ← hσ, hF]
      rw [div_eq_one]
      have := bimul_ext e q (fun x y => ∏ p : Fin (Module.finrank ℤ X) × Fin (Module.finrank ℤ X),
          q (e p.1) (e p.2) ^ halfForm e p.1 p.2 x y) hadd hadd'
        (fun a a' b => by simp only [map_add (f := _), LinearMap.add_apply, zpow_add, Finset.prod_mul_distrib])
        (fun a b b' => by simp only [map_add (f := _), zpow_add, Finset.prod_mul_distrib])
        (fun i j => by
          simp only [halfForm_basis]
          rw [Finset.prod_eq_single (min i j, max i j)]
          · simp only [and_self, if_true, zpow_one]
            rcases le_total i j with h | h
            · rw [min_eq_left h, max_eq_right h]
            · rw [min_eq_right h, max_eq_left h, hsym]
          · intro p _ hp; rw [if_neg, zpow_zero]; rintro ⟨h1, h2⟩; exact hp (Prod.ext h1 h2)
          · intro h; exact absurd (Finset.mem_univ _) h)
      exact congrFun (congrFun this x) y
    exact div_eq_one.1 (eq_one_of_prod_zpow hε _ h0 k)

theorem eq_of_prod_zpow {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (s s' : ι → G) (h : ∀ x y, ∏ k, s k ^ ε k x y = ∏ k, s' k ^ ε k x y) : s = s' := by
  funext k
  refine div_eq_one.1 (eq_one_of_prod_zpow hε (fun k => s k / s' k) (fun x y => ?_) k)
  simp_rw [div_zpow, Finset.prod_div_distrib, h, div_self']

theorem pow_eq_pow_of_prod {ε : ι → LinearMap.BilinForm ℤ X} (hε : IsSymBasis ε) [Module.Free ℤ X] [Module.Finite ℤ X]
    (n : ℕ) (s s' : ι → G) (h : ∀ x y, ∏ k, s k ^ ((n : ℤ) * ε k x y) = ∏ k, s' k ^ ((n : ℤ) * ε k x y)) (k : ι) :
    s k ^ n = s' k ^ n := by
  have := congrFun (eq_of_prod_zpow hε (fun k => s k ^ n) (fun k => s' k ^ n) fun x y => by
    simp_rw [← zpow_natCast, ← zpow_mul]; exact h x y) k
  exact this

theorem isSymBasis_mul : IsSymBasis (fun _ : Fin 1 => (LinearMap.mul ℤ ℤ : LinearMap.BilinForm ℤ ℤ)) := by
  refine ⟨fun _ x y => mul_comm x y, ?_, fun β _ => ?_⟩
  · rw [linearIndependent_unique_iff]
    intro h
    have := LinearMap.congr_fun₂ h 1 1
    simp at this
  · refine (Submodule.mem_span_range_iff_exists_fun ℤ).2 ⟨fun _ => β 1 1, ?_⟩
    refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
    simp only [Finset.univ_unique, Finset.sum_singleton, LinearMap.smul_apply, LinearMap.mul_apply', smul_eq_mul]
    have hx : x = x • (1 : ℤ) := by simp
    have hy : y = y • (1 : ℤ) := by simp
    rw [hx, hy, LinearMap.map_smul₂, LinearMap.map_smul]
    simp only [smul_eq_mul]; ring

end GlobalTheory.PerRoot
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRootsOfPeriods

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PerRoot

open IsDedekindDomain Polynomial

theorem exists_ord (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] :
    ∃ v : (FractionRing V)ˣ →* Multiplicative ℤ,
      (∀ x : (FractionRing V)ˣ, 0 ≤ (v x).toAdd → ∃ a : V, algebraMap V _ a = (x : FractionRing V)) ∧
      ∀ (x : (FractionRing V)ˣ) (a : V), algebraMap V _ a = (x : FractionRing V) →
        (0 < (v x).toAdd ↔ a ∈ maximalIdeal V) := by
  let w := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hw : ∀ x : (FractionRing V)ˣ, w x ≠ 0 := fun x => by simp [w]
  refine ⟨MonoidHom.mk' (fun x => Multiplicative.ofAdd (-WithZero.log (w x))) fun x y => ?_, fun x hx => ?_,
    fun x a ha => ?_⟩
  · rw [← ofAdd_add, Units.val_mul, map_mul, WithZero.log_mul (hw x) (hw y), neg_add]
  · refine IsDiscreteValuationRing.exists_lift_of_le_one ?_
    simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_nonneg] at hx
    exact (WithZero.log_le_log (hw x) one_ne_zero).1 (by simpa using hx)
  · simp only [MonoidHom.mk'_apply, toAdd_ofAdd, neg_pos]
    have h1 : WithZero.log (w x) < 0 ↔ w x < 1 := by
      simpa using WithZero.log_lt_log (hw x) one_ne_zero
    rw [h1, ← ha]
    exact HeightOneSpectrum.valuation_lt_one_iff_mem _ a

theorem exists_nthRoots_ext (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [IsAdicComplete (maximalIdeal V) V] [CharZero V] {I : Type} [Fintype I] (a : I → V) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (maximalIdeal W) W) (f : V →+* W) (s : I → W),
      Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ ∀ k, s k ^ n = f (a k) := by
  classical
  let K := FractionRing V
  haveI : CharZero K := algebraRat.charZero _
  let p : I → K[X] := fun k => X ^ n - C (algebraMap V K (a k))
  have hp : ∀ k, (p k).Monic := fun k => monic_X_pow_sub_C _ (by omega)
  let L := (∏ k, p k).SplittingField
  have hsp : ((∏ k, p k).map (algebraMap K L)).Splits := SplittingField.splits _
  have hroot : ∀ k, ∃ t : L, t ^ n = algebraMap K L (algebraMap V K (a k)) := fun k => by
    have h0 : (∏ k, p k).map (algebraMap K L) ≠ 0 :=
      ((monic_prod_of_monic _ _ fun k _ => hp k).map _).ne_zero
    have h1 : ((p k).map (algebraMap K L)).Splits :=
      hsp.of_dvd h0 (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ k)))
    obtain ⟨t, ht⟩ := h1.exists_eval_eq_zero (by
      rw [(hp k).degree_map, degree_X_pow_sub_C (by omega)]
      exact_mod_cast (by omega : n ≠ 0))
    refine ⟨t, ?_⟩
    simpa [p, sub_eq_zero] using ht
  choose t ht using hroot
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, hinj, hloc, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V K L
  have hs : ∀ k, t k ∈ Set.range (algebraMap W L) := fun k => hint _
    ⟨X ^ n - C (a k), monic_X_pow_sub_C _ (by omega), by simp [ht]⟩
  choose s hs using hs
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, algebraMap V W, s, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, fun k => IsFractionRing.injective W L ?_⟩
  rw [map_pow, hs, ht]
  exact (RingHom.congr_fun hc (a k)).symm

theorem exists_form {G X : Type} [CommGroup G] [AddCommGroup X] (v : G →* Multiplicative ℤ) (q : X → X → G)
    (hsym : ∀ x y, q x y = q y x) (hadd : ∀ x x' y, q (x + x') y = q x y * q x' y) :
    ∃ β : LinearMap.BilinForm ℤ X, ∀ x y, β x y = (v (q x y)).toAdd := by
  have hadd' : ∀ x y y', q x (y + y') = q x y * q x y' := fun x y y' => by
    rw [hsym, hadd, hsym y, hsym y']
  let F : X → X →ₗ[ℤ] ℤ := fun x =>
    (AddMonoidHom.mk' (fun y => (v (q x y)).toAdd) fun y y' => by simp [hadd']).toIntLinearMap
  exact ⟨(AddMonoidHom.mk' F fun x x' => LinearMap.ext fun y => by simp [F, hadd]).toIntLinearMap,
    fun x y => rfl⟩

theorem isSymBasis_of_basis {X I : Type} [AddCommGroup X] (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) X)) :
    IsSymBasis fun k => (ε k : LinearMap.BilinForm ℤ X) := by
  refine ⟨fun k => mem_balForms_int.1 (ε k).2, ε.linearIndependent.map' (Submodule.subtype _) (by simp),
    fun β hβ => ?_⟩
  have h := Submodule.mem_map_of_mem (f := (balForms (id : ℤ → ℤ) X).subtype)
    (ε.mem_span ⟨β, mem_balForms_int.2 hβ⟩)
  rw [Submodule.map_span, ← Set.range_comp] at h
  exact h

theorem exists_roots_of_periods : ∀ (g n : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → 1 ≤ n → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → IsDiscreteValuationRing V → ∀ (r : ℕ), r ≤ g → ∀ (q : (Fin r → ℤ) → (Fin r → ℤ) → (FractionRing V)ˣ), (∀ a b, q a b = q b a) → (∀ a a' b, q (a + a') b = q a b * q a' b) → (∀ a, a ≠ 0 → ∃ w ∈ maximalIdeal V, w ≠ 0 ∧ (q a a : FractionRing V) = algebraMap V _ w) → ∃ (m N : ℕ) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))), IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ))) ∧ (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) x x) ∧ ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (fK : FractionRing V →+* FractionRing V') (s : Fin m ⊕ Fin N → V'), IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap V _ a) = algebraMap V' _ (f a)) ∧ (∀ k, s (.inl k) ∈ maximalIdeal V' ∧ s (.inl k) ≠ 0) ∧ (∀ k, IsUnit (s (.inr k))) ∧ ∀ a b, fK (q a b : FractionRing V) = ∏ k, algebraMap V' _ (s k) ^ ((n : ℤ) * (ε k : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) := by
  intro g n φ hφ hn V _ _ _ hV hD r hr q hsym hadd hpos
  obtain ⟨-, -, hcomp, hchar⟩ := hV
  obtain ⟨v, hv1, hv2⟩ := exists_ord V
  obtain ⟨β, hβ⟩ := exists_form v q hsym hadd
  have hβs : ∀ x y, β x y = β y x := fun x y => by rw [hβ, hβ, hsym]
  have hβp : ∀ x, x ≠ 0 → 0 < β x x := fun x hx => by
    obtain ⟨w, hw, -, h⟩ := hpos x hx
    rw [hβ]
    exact (hv2 _ w h.symm).2 hw
  have hβn : ∀ x, 0 ≤ β x x := fun x => by
    by_cases hx : x = 0
    · simp [hx]
    · exact (hβp x hx).le
  obtain ⟨m, ga, c, hga, hc, hβc⟩ := GlobalTheory.ConeInterior.exists_pos_comb_int g φ hφ r hr β hβs
    (GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 hβs) hβn)
  obtain ⟨N, ε, hε⟩ := hga.basis
  have hεga : ∀ k, (ε (.inl k) : LinearMap.BilinForm ℤ (Fin r → ℤ)) = ga k := fun k => by rw [hε]
  have hsb := isSymBasis_of_basis ε
  obtain ⟨u, hu, -⟩ := existsUnique_coeff hsb q hsym hadd
  have hβv : ∀ x y, β x y = ∑ j, (c j : ℤ) * ga j x y := fun x y => by
    rw [hβc]; simp [LinearMap.sum_apply]
  have hvu : (fun k => v (u k)) = fun k => Multiplicative.ofAdd (Sum.elim (fun j => (c j : ℤ)) 0 k) := by
    refine eq_of_prod_zpow hsb _ _ fun x y => ?_
    simp_rw [← map_zpow, ← map_prod, ← hu]
    apply Multiplicative.toAdd.injective
    rw [← hβ, hβv, toAdd_prod, Fintype.sum_sum_type]
    simp [hεga, mul_comm]
  have hvk : ∀ k, (v (u k)).toAdd = Sum.elim (fun j => (c j : ℤ)) 0 k := fun k => by
    rw [congrFun hvu k]; rfl
  choose a ha using fun k => hv1 (u k) (by rw [hvk]; cases k <;> simp)
  have ha0 : ∀ k, a k ≠ 0 := fun k h => (u k).ne_zero (by rw [← ha, h, map_zero])
  obtain ⟨W, _, _, _, _, f, s, hinj, hfin, hloc, hs⟩ := exists_nthRoots_ext V a hn
  have hinj' : Function.Injective ((algebraMap W (FractionRing W)).comp f) :=
    (IsFractionRing.injective W _).comp hinj
  have hfK : ∀ b, IsFractionRing.lift (K := FractionRing V) hinj' (algebraMap V _ b) =
      algebraMap W (FractionRing W) (f b) := fun b => IsFractionRing.lift_algebraMap hinj' b
  refine ⟨m, N, ε, by simpa only [hεga] using hga, fun x hx => ?_, W, inferInstance, inferInstance, inferInstance, f,
    IsFractionRing.lift hinj', s, ⟨inferInstance, inferInstance, inferInstance, ?_⟩, inferInstance, hinj, hfin, hloc,
    hfK, fun k => ⟨?_, fun h => ?_⟩, fun k => ?_, fun x y => ?_⟩
  · by_contra h
    push_neg at h
    have h1 := hβp x hx
    rw [hβv] at h1
    exact h1.not_ge (Finset.sum_nonpos fun j _ =>
      mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (hεga j ▸ h j))
  · exact charZero_of_injective_ringHom hinj
  · have h1 : a (.inl k) ∈ maximalIdeal V := (hv2 _ _ (ha _)).1 (by rw [hvk]; simpa using hc k)
    intro h
    exact h1 (isUnit_of_map_unit f _ (hs _ ▸ h.pow n))
  · refine ha0 (.inl k) (hinj ?_)
    rw [← hs, h, map_zero, zero_pow (by omega)]
  · have h1 : a (.inr k) ∉ maximalIdeal V := fun h => by
      have := (hv2 _ _ (ha _)).2 h
      rw [hvk] at this
      simp at this
    have h2 : IsUnit (s (.inr k) ^ n) := hs _ ▸ (not_not.1 h1 : IsUnit (a (.inr k))).map f
    exact (isUnit_pow_iff (by omega)).1 h2
  · rw [hu, Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, ← ha, hfK, ← hs, map_pow, zpow_mul, zpow_natCast]

end GlobalTheory.PerRoot
end
end
