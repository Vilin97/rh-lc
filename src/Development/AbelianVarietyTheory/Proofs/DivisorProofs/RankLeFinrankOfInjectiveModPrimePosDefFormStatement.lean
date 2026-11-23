module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFreeOfPositiveDefiniteFormBoundedRank
public import Mathlib.LinearAlgebra.TensorProduct.Lift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
public import Mathlib.RingTheory.Nakayama
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangePadicIntInjectiveSaturatedOfModL

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatticeModL

theorem exists_one_tmul_add_smul (l : ℕ) [Fact l.Prime] (H : Type) [AddCommGroup H]
    (x : ℤ_[l] ⊗[ℤ] H) :
    ∃ (h : H) (y : ℤ_[l] ⊗[ℤ] H), x = (1 : ℤ_[l]) ⊗ₜ h + (l : ℤ_[l]) • y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a h =>
    obtain ⟨c, hc⟩ : ∃ c : ℤ_[l], a - (a.zmodRepr : ℤ_[l]) = (l : ℤ_[l]) * c := by
      have := PadicInt.sub_zmodRepr_mem a
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
      exact this
    refine ⟨(a.zmodRepr : ℤ) • h, c ⊗ₜ h, ?_⟩
    have ha : a = ((a.zmodRepr : ℤ) : ℤ_[l]) + (l : ℤ_[l]) * c := by
      rw [← hc]; push_cast; ring
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, zsmul_eq_mul, _root_.mul_one, ← TensorProduct.add_tmul, ← ha]
  | add x y hx hy =>
    obtain ⟨h₁, y₁, rfl⟩ := hx
    obtain ⟨h₂, y₂, rfl⟩ := hy
    exact ⟨h₁ + h₂, y₁ + y₂, by rw [TensorProduct.tmul_add, smul_add]; abel⟩

end GlobalTheory.LatticeModL


open GlobalTheory.LatticeModL in
theorem GlobalTheory.latticeMap_liftBaseChange_injective_saturated :
    ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [Module.Finite ℤ H] [Module.Free ℤ H]
      [AddCommGroup T] [Module ℤ_[l] T], (∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0) →
      ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') →
      Function.Injective (φ.toIntLinearMap.liftBaseChange ℤ_[l]) ∧
      ∀ t : T, (l : ℤ_[l]) • t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) →
        t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) := by
  intro l _ H T _ _ _ _ _ htor φ hsat
  set F := φ.toIntLinearMap.liftBaseChange ℤ_[l] with hFdef
  have hF : ∀ h, F ((1 : ℤ_[l]) ⊗ₜ h) = φ h := by
    intro h; simp [F]
  have key : ∀ (x : ℤ_[l] ⊗[ℤ] H) (t : T), F x = (l : ℤ_[l]) • t →
      ∃ x', x = (l : ℤ_[l]) • x' := by
    intro x t hx
    obtain ⟨h, y, rfl⟩ := exists_one_tmul_add_smul l H x
    rw [map_add (f := _), map_smul, hF] at hx
    have h1 : φ h = (l : ℤ_[l]) • (t - F y) := by rw [smul_sub, ← hx]; abel
    obtain ⟨h', rfl⟩ := hsat h _ h1
    refine ⟨(1 : ℤ_[l]) ⊗ₜ h' + y, ?_⟩
    rw [smul_add, TensorProduct.tmul_smul]
    simp only [Nat.cast_smul_eq_nsmul]
  have hl : (l : ℤ_[l]) ∈ IsLocalRing.maximalIdeal ℤ_[l] := by
    rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal ℤ_[l]) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨x', rfl⟩ := key x 0 (by rw [hx, smul_zero])
    have : F x' = 0 := htor _ (by rw [← map_smul, hx])
    exact Submodule.smul_mem_smul hl this
  · rintro t ⟨x, hx⟩
    obtain ⟨x', rfl⟩ := key x t hx
    refine ⟨x', ?_⟩
    have : (l : ℤ_[l]) • (F x' - t) = 0 := by rw [smul_sub, ← map_smul, hx, sub_self]
    exact sub_eq_zero.mp (htor _ this)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangePadicIntInjectiveSaturatedOfModLStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.liftBaseChange_padicInt_injective_saturated_of_modL : ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [Module.Finite ℤ H] [Module.Free ℤ H] [AddCommGroup T] [Module ℤ_[l] T], (∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0) → ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') → Function.Injective (φ.toIntLinearMap.liftBaseChange ℤ_[l]) ∧ ∀ t : T, (l : ℤ_[l]) • t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) → t ∈ LinearMap.range (φ.toIntLinearMap.liftBaseChange ℤ_[l]) := by
  first | (exact @GlobalTheory.latticeMap_liftBaseChange_injective_saturated) | (exact GlobalTheory.latticeMap_liftBaseChange_injective_saturated) | (intros; apply GlobalTheory.latticeMap_liftBaseChange_injective_saturated  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFinrankOfInjectiveModPrimePosDefForm

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

def satSpanFamily {H : Type} [AddCommGroup H] {n : ℕ} (u : Fin n → H) : AddSubgroup H where
  carrier := {h | ∃ k : ℤ, k ≠ 0 ∧ k • h ∈ Submodule.span ℤ (Set.range u)}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro a b ⟨k, hk, ha⟩ ⟨m, hm, hb⟩
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    rw [smul_add, mul_smul, mul_smul, smul_comm k m a]
    exact add_mem (Submodule.smul_mem _ m ha) (Submodule.smul_mem _ k hb)
  neg_mem' := by
    rintro a ⟨k, hk, ha⟩
    exact ⟨k, hk, by rw [smul_neg]; exact neg_mem ha⟩

theorem rank_le_finrank_of_injective_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [AddCommGroup T] [Module ℤ_[l] T] [Module.Finite ℤ_[l] T] [Module.Free ℤ_[l] T] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') → ∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ Module.finrank ℤ_[l] T := by
  intro l _ H T _ _ _ _ _ Q hpar hnn hdef φ hφ n u hu
  classical
  set M := satSpanFamily u with hMdef
  have memM : ∀ h, h ∈ M ↔ ∃ k : ℤ, k ≠ 0 ∧ k • h ∈ Submodule.span ℤ (Set.range u) :=
    fun h => Iff.rfl
  have hbound : ∀ (m : ℕ) (v : Fin m → M), LinearIndependent ℤ v → m ≤ n := by
    intro m v hv
    choose k hk hks using fun j => (memM (v j : H)).1 (v j).2
    let w : Fin m → Submodule.span ℤ (Set.range u) := fun j => ⟨k j • (v j : H), hks j⟩
    have hw : LinearIndependent ℤ w := by
      rw [Fintype.linearIndependent_iff] at hv ⊢
      intro g hg j
      have h1 : ∑ i, (g i * k i) • v i = 0 := by
        apply Subtype.ext
        have := congrArg Subtype.val hg
        simpa [w, mul_smul] using this
      exact (mul_eq_zero.1 (hv _ h1 j)).resolve_right (hk j)
    haveI : Module.Finite ℤ (Submodule.span ℤ (Set.range u)) :=
      Module.Finite.span_of_finite ℤ (Set.finite_range u)
    have := hw.fintype_card_le_finrank
    rw [finrank_span_eq_card hu] at this
    simpa using this
  obtain ⟨hfin, hfree, -⟩ := GlobalTheory.finite_free_of_definite_form_of_rank_le M (fun x => Q x)
    (fun f g => by simpa using hpar f g) (fun f => hnn f) (fun f hf => Subtype.ext (hdef _ hf)) n hbound
  haveI := hfin
  haveI := hfree
  let ψ : M →+ T := φ.comp M.subtype
  have hlne : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hψ : ∀ (h : M) (t : T), ψ h = (l : ℤ_[l]) • t → ∃ h' : M, h = l • h' := by
    intro h t ht
    obtain ⟨h', hh'⟩ := hφ (h : H) t ht
    obtain ⟨k, hk, hks⟩ := (memM (h : H)).1 h.2
    refine ⟨⟨h', k * l, mul_ne_zero hk (by exact_mod_cast hlne), ?_⟩, Subtype.ext ?_⟩
    · rw [mul_smul, natCast_zsmul, ← hh']
      exact hks
    · simp [hh']
  have htor : ∀ t : T, (l : ℤ_[l]) • t = 0 → t = 0 := by
    intro t ht
    have hl : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hlne
    exact (smul_eq_zero.1 ht).resolve_left hl
  obtain ⟨hinj, -⟩ := GlobalTheory.T.liftBaseChange_padicInt_injective_saturated_of_modL l M T htor ψ hψ
  have h1 := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Module.finrank_baseChange] at h1
  let v : Fin n → M := fun i => ⟨u i, 1, one_ne_zero, by
    simpa using Submodule.subset_span (Set.mem_range_self i)⟩
  have hv : LinearIndependent ℤ v :=
    LinearIndependent.of_comp M.subtype.toIntLinearMap (by
      have e : (M.subtype.toIntLinearMap : M →ₗ[ℤ] H) ∘ v = u := funext fun i => rfl
      rw [e]; exact hu)
  have h2 := hv.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h2
  omega

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFinrankOfInjectiveModPrimePosDefFormStatement

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.rank_le_finrank_of_injective_mod_prime_posDef_form : ∀ (l : ℕ) [Fact l.Prime] (H T : Type) [AddCommGroup H] [AddCommGroup T] [Module ℤ_[l] T] [Module.Finite ℤ_[l] T] [Module.Free ℤ_[l] T] (Q : H → ℤ), (∀ f g, Q (f + g) + Q (f - g) = 2 * Q f + 2 * Q g) → (∀ f, 0 ≤ Q f) → (∀ f, Q f = 0 → f = 0) → ∀ φ : H →+ T, (∀ (h : H) (t : T), φ h = (l : ℤ_[l]) • t → ∃ h' : H, h = l • h') → ∀ (n : ℕ) (u : Fin n → H), LinearIndependent ℤ u → n ≤ Module.finrank ℤ_[l] T := by
  first | (exact @GlobalTheory.rank_le_finrank_of_injective_mod_prime) | (exact GlobalTheory.rank_le_finrank_of_injective_mod_prime) | (intros; apply GlobalTheory.rank_le_finrank_of_injective_mod_prime  <;> assumption)
end
end
