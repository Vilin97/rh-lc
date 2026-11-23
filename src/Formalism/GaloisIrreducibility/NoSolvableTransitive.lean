module

public import Formalism.GaloisIrreducibility.Statement
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
import Mathlib.GroupTheory.SpecificGroups.ZGroup
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
public import Formalism.GaloisIrreducibility.NoSolvableOf
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.JordanPrime
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PermSubSumInv
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PowerPCycle
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PrimitiveOfPCycle
public import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.RestrictRoots

-- Source module: Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.AltNotSolvable

section

@[expose] public section

namespace Formalism.GaloisIrreducibility

theorem alternating_group_not_solvable : AltNotSolvable := by
  intro α _ _ h hA
  have hcard : 5 ≤ Cardinal.mk α := by
    rw [Cardinal.mk_fintype]
    exact_mod_cast h
  refine Equiv.Perm.not_isSolvable α hcard ?_
  exact Group.isSolvable_of_ker_le_range (alternatingGroup α).subtype Equiv.Perm.sign
    (by rw [Subgroup.range_subtype]; exact le_rfl)

end Formalism.GaloisIrreducibility
end
end

-- Source module: Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.IrredOf

section

@[expose] public section

namespace Formalism.GaloisIrreducibility

open Finset

lemma isSubSum_of_subset {ι : Type} (f : ι → ℕ) (I J : Finset ι) (hJ : J ⊆ I) :
    IsSubSum (I.val.map f) (∑ i ∈ J, f i) := by
  unfold IsSubSum
  exact ⟨J.val.map f, Multiset.map_le_map (Finset.val_le_iff.2 hJ), rfl⟩

theorem irreducible_of_galois_conditions : IrredOf := by
  intro hA K V P ι _ _ _ _ _ τ F q O I hFτ hO hroots hsub W hWτ hWF
  classical
  have hs1 : ∀ v, IsSubSum ((I v).val.map fun i => (O v i).card) (Module.finrank K W) := by
    intro v
    obtain ⟨J, hJ, hJeq⟩ := hA K V ι (τ v) (F v) (q v) (O v) (I v) (hFτ v) (hO v) (hroots v) ⊥ W
      bot_le (by simp) (by simp) (hWτ v) (hWF v)
    rw [finrank_bot, Nat.sub_zero] at hJeq
    rw [hJeq]
    exact isSubSum_of_subset _ _ _ hJ
  have hs2 : ∀ v, IsSubSum ((I v).val.map fun i => (O v i).card)
      (Module.finrank K V - Module.finrank K W) := by
    intro v
    obtain ⟨J, hJ, hJeq⟩ := hA K V ι (τ v) (F v) (q v) (O v) (I v) (hFτ v) (hO v) (hroots v) W ⊤
      le_top (hWτ v) (hWF v) (by simp) (by simp)
    rw [finrank_top] at hJeq
    rw [hJeq]
    exact isSubSum_of_subset _ _ _ hJ
  by_contra hne
  push_neg at hne
  obtain ⟨h0, h1⟩ := hne
  have hd0 : 0 < Module.finrank K W :=
    Nat.pos_of_ne_zero fun h => h0 (Submodule.finrank_eq_zero.mp h)
  have hdN : Module.finrank K W < Module.finrank K V :=
    Submodule.finrank_lt h1
  obtain ⟨v, hv⟩ := hsub (min (Module.finrank K W) (Module.finrank K V - Module.finrank K W))
    (by omega) (by omega)
  apply hv
  rcases min_choice (Module.finrank K W) (Module.finrank K V - Module.finrank K W) with h | h
  · rw [h]
    exact hs1 v
  · rw [h]
    exact hs2 v

end Formalism.GaloisIrreducibility
end
end

-- Source module: Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.LemmaAOf

section

@[expose] public section

namespace Formalism.GaloisIrreducibility

open Module Polynomial

section SlopeTestRemainingChoices
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

lemma la_restrict_pow (τ : Module.End K V) (W : Submodule K V) (hτ : ∀ v ∈ W, τ v ∈ W)
    (n : ℕ) (v : W) : (((τ.restrict hτ) ^ n) v : V) = (τ ^ n) v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.restrict_coe_apply, ih, pow_succ',
      Module.End.mul_apply]

lemma la_card_roots [IsAlgClosed K] [FiniteDimensional K V] (φ : Module.End K V) :
    (LinearMap.charpoly φ).roots.card = finrank K V := by
  rw [← LinearMap.charpoly_natDegree φ]
  exact (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _))

end SlopeTestRemainingChoices

theorem lemmaAOf_statement : LemmaAOf := by
  classical
  unfold LemmaAOf LemmaA
  intro hOS hRR K V ι _ _ _ _ _ τ F q O I hF hO hroots W₁ W₂ hle h1τ h1F h2τ h2F

  obtain ⟨hA1, hA2⟩ := hRR K V τ F q hF W₂ h2τ h2F

  let g : W₂ →ₗ[K] W₂ := F.toLinearMap.restrict h2F
  have hg : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    apply F.injective
    exact congrArg Subtype.val hxy
  let F₂ : W₂ ≃ₗ[K] W₂ := LinearEquiv.ofInjectiveEndo g hg
  have hF₂ : ∀ v, F₂ (τ.restrict h2τ v) = ((τ.restrict h2τ) ^ q) (F₂ v) := by
    intro v
    apply Subtype.ext
    rw [la_restrict_pow τ W₂ h2τ q (F₂ v)]
    exact hF (v : V)

  let W₁' : Submodule K W₂ := W₁.comap W₂.subtype
  have h1τ' : ∀ v ∈ W₁', τ.restrict h2τ v ∈ W₁' := fun v hv => h1τ (v : V) hv
  have h1F' : ∀ v ∈ W₁', F₂ v ∈ W₁' := fun v hv => h1F (v : V) hv
  obtain ⟨hB1, hB2⟩ := hRR K W₂ (τ.restrict h2τ) F₂ q hF₂ W₁' h1τ' h1F'
  have hc2 : (LinearMap.charpoly (τ.restrict h2τ)).roots.card = finrank K W₂ :=
    la_card_roots _
  have hc1 : (LinearMap.charpoly ((τ.restrict h2τ).restrict h1τ')).roots.card
      = finrank K W₁' := la_card_roots _
  have hW : finrank K W₁' = finrank K W₁ := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  set M₂ := (LinearMap.charpoly (τ.restrict h2τ)).roots with hM₂
  set M₁ := (LinearMap.charpoly ((τ.restrict h2τ).restrict h1τ')).roots with hM₁

  have hsplit : M₂ = M₁ + (M₂ - M₁) := (add_tsub_cancel_of_le hB1).symm
  have hmap : (M₂ - M₁).map (fun x : K => x ^ q) = M₂ - M₁ := by
    have h := congrArg (Multiset.map (fun x : K => x ^ q)) hsplit
    rw [Multiset.map_add (f := _), hB2, hA2] at h
    have h' : M₁ + (M₂ - M₁) = M₁ + Multiset.map (fun x : K => x ^ q) (M₂ - M₁) :=
      hsplit.symm.trans h
    exact (add_left_cancel h').symm
  have hsub : M₂ - M₁ ≤ ∑ i ∈ I, (O i).val := by
    rw [← hroots]
    exact tsub_le_self.trans hA1
  obtain ⟨J, hJ, hcard⟩ := hOS K ι (fun x : K => x ^ q) O I (M₂ - M₁) hO hsub hmap
  refine ⟨J, hJ, ?_⟩
  rw [← hcard, Multiset.card_sub hB1, hc2, hc1, hW]

end Formalism.GaloisIrreducibility
end
end

-- Source module: Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.NoSolvableOf

section

@[expose] public section

namespace Formalism.GaloisIrreducibility

theorem no_solvable_subgroup_of : NoSolvableOf := by
  intro h1 h2 h3 h4 α _ _ G σ p hp hσG hpc hlt hge htrans hsolv
  obtain ⟨k, hk, hkc⟩ := h1 α σ p hp hpc hlt
  have hkG : σ ^ k ∈ G := G.pow_mem hσG k
  have hprim := h2 α G (σ ^ k) p hp hkG hk hkc hlt htrans
  have halt := h3 α G (σ ^ k) p hp hkG hk hkc hge hprim
  have h5 : 5 ≤ Fintype.card α := by have := hp.two_le; omega
  apply h4 α h5
  haveI := hsolv
  exact solvable_of_solvable_injective (Subgroup.inclusion_injective halt)

end Formalism.GaloisIrreducibility
end
end

-- Source module: Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OrbitSubSum

section

@[expose] public section

namespace Formalism.GaloisIrreducibility

open Classical

lemma orbit_iterate_mem {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O)
    {x : α} (hx : x ∈ O) : ∀ n : ℕ, f^[n] x ∈ O := by
  intro n
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hO.1 _ ih

lemma orbit_image_eq {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) :
    O.image f = O := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hO.1 x hx
  · intro y hy
    obtain ⟨n, hn⟩ := hO.2 (f y) (hO.1 y hy) y hy
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply'] at hn
    exact Finset.mem_image.mpr ⟨f^[n] y, orbit_iterate_mem hO hy n, hn⟩

lemma orbit_map_eq {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) :
    O.val.map f = O.val := by
  have hinj : Set.InjOn f O := by
    rw [← Finset.card_image_iff, orbit_image_eq hO]
  rw [← Finset.image_val_of_injOn hinj, orbit_image_eq hO]

lemma orbit_le {α : Type} {f : α → α} {O : Finset α} (hO : IsOrbit f O) {M' : Multiset α}
    (hM : M'.map f = M') {x : α} (hxO : x ∈ O) (hxM : x ∈ M') : O.val ≤ M' := by
  rw [Multiset.le_iff_subset O.nodup]
  intro y hy
  obtain ⟨n, rfl⟩ := hO.2 x hxO y (Finset.mem_val.mp hy)
  clear hy
  induction n with
  | zero => simpa using hxM
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← hM]
    exact Multiset.mem_map_of_mem f ih

theorem invariant_multiset_orbit_sum {α ι : Type} (f : α → α) (O : ι → Finset α) (I : Finset ι) :
    ∀ (M' : Multiset α), (∀ i ∈ I, IsOrbit f (O i)) → M' ≤ ∑ i ∈ I, (O i).val →
      M'.map f = M' → ∃ J ⊆ I, M'.card = ∑ i ∈ J, (O i).card := by
  induction I using Finset.strongInduction with
  | H I ih =>
  intro M' hO hle hM
  by_cases h0 : M' = 0
  · exact ⟨∅, Finset.empty_subset _, by simp [h0]⟩
  obtain ⟨x, hx⟩ := Multiset.exists_mem_of_ne_zero h0
  have hxs : x ∈ ∑ i ∈ I, (O i).val := Multiset.mem_of_le hle hx
  rw [Multiset.mem_sum] at hxs
  obtain ⟨i0, hi0, hxi⟩ := hxs
  have hle0 : (O i0).val ≤ M' := orbit_le (hO i0 hi0) hM (Finset.mem_val.mp hxi) hx
  obtain ⟨M'', rfl⟩ : ∃ M'', M' = (O i0).val + M'' :=
    ⟨M' - (O i0).val, (add_tsub_cancel_of_le hle0).symm⟩
  have hM'' : M''.map f = M'' := by
    rw [Multiset.map_add (f := _), orbit_map_eq (hO i0 hi0)] at hM
    exact add_left_cancel hM
  have hle'' : M'' ≤ ∑ i ∈ I.erase i0, (O i).val := by
    rw [← Finset.add_sum_erase I _ hi0] at hle
    exact (add_le_add_iff_left _).mp hle
  obtain ⟨J, hJ, hc⟩ := ih (I.erase i0) (Finset.erase_ssubset hi0) M''
    (fun i hi => hO i (Finset.mem_of_mem_erase hi)) hle'' hM''
  refine ⟨insert i0 J, Finset.insert_subset hi0 (hJ.trans (Finset.erase_subset _ _)), ?_⟩
  have hnot : i0 ∉ J := fun h => by simpa using hJ h
  rw [Finset.sum_insert hnot, Multiset.card_add, hc, Finset.card_val]

theorem orbit_subset_sum : OrbitSubSum := by
  intro α ι f O I M' hO hle hM
  exact invariant_multiset_orbit_sum f O I M' hO hle hM

end Formalism.GaloisIrreducibility
end
end

-- Source module: Formalism.GaloisIrreducibility.NoSolvableTransitive

section

@[expose] public section

namespace Formalism.GaloisIrreducibility

theorem lemmaA : LemmaA := lemmaAOf_statement orbit_subset_sum restrict_roots_to_subfield

theorem irred : Irred := irreducible_of_galois_conditions lemmaA
theorem permSubSumInv : PermSubSumInv := permutation_subset_sum_invariant

theorem primitiveOfPCycle : PrimitiveOfPCycle := primitive_of_p_cycle
theorem jordanPrime : JordanPrime := jordan_prime_cycle_theorem

theorem noSolvableTransitive : NoSolvableTransitive :=
  no_solvable_subgroup_of power_of_p_cycle primitive_of_p_cycle jordan_prime_cycle_theorem alternating_group_not_solvable

end Formalism.GaloisIrreducibility
end
end
