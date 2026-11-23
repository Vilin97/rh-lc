module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsInducedIntPrimeTo
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IndMulClassFunEqIndMulRestrict
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemOfMulMemOfForallPrimeNotDvd
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharacterInnerEqIntMulCardStatement
import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsInducedIntPrimeToStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_integral_comb_induced_linear_not_dvd : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ (E : Subgroup G) (f : G → ℤ) (ι : Type) (_ : Fintype ι) (r : ι → ℂ) (lam : ι → E →* ℂˣ), (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧ ¬ (p : ℤ) ∣ f x ∧ (∀ i, IsIntegral ℤ (r i)) ∧ ∀ g, (f g : ℂ) = ∑ i, r i * ind E (fun e => (lam i e : ℂ)) g := by
  first | exact @GlobalTheory.exists_induced_int_prime_to | exact GlobalTheory.exists_induced_int_prime_to | (intros; apply GlobalTheory.exists_induced_int_prime_to <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIntRelationOfIsIntegralRelation

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem exists_int_eq_of_isIntegral_of_mul_eq_int {x : ℂ} (hx : IsIntegral ℤ x) {n k : ℤ}
    (hn : n ≠ 0) (h : (n : ℂ) * x = k) : ∃ j : ℤ, (j : ℂ) = x := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hq : x = algebraMap ℚ ℂ ((k : ℚ) / n) := by
    simp only [eq_ratCast, Rat.cast_div, Rat.cast_intCast]
    rw [eq_div_iff hn', mul_comm, h]
  rw [hq, isIntegral_algebraMap_iff ] at hx
  obtain ⟨j, hj⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
  refine ⟨j, ?_⟩
  rw [hq, ← hj]
  simp

theorem exists_int_retraction_of_isIntegral :
    ∀ (ι : Type) [Fintype ι] (r : ι → ℂ), (∀ i, IsIntegral ℤ (r i)) →
      ∃ c : ι → ℤ, ∀ (m : ι → ℤ) (d : ℤ), ∑ i, r i * (m i : ℂ) = d → ∑ i, c i * m i = d := by
  intro ι _ r hr
  classical
  let f : (ι → ℤ) →ₗ[ℤ] ℂ := Fintype.linearCombination ℤ r
  have hf : ∀ m, f m = ∑ i, r i * (m i : ℂ) := by
    intro m
    simp [f, Fintype.linearCombination_apply, mul_comm]
  have hfi : ∀ m, IsIntegral ℤ (f m) := by
    intro m
    rw [hf]
    refine IsIntegral.sum _ fun i _ => (hr i).mul ?_
    exact isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := m i)
  let K : Submodule ℤ (ι → ℤ) := (LinearMap.range (Algebra.linearMap ℤ ℂ)).comap f
  have hK : ∀ m, m ∈ K ↔ ∃ j : ℤ, (j : ℂ) = f m := by
    intro m
    simp [K]
  have : Module.IsTorsionFree ℤ ((ι → ℤ) ⧸ K) := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro n x hx
    by_cases hn : n = 0
    · exact Or.inl hn
    right
    obtain ⟨m, rfl⟩ := K.mkQ_surjective x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK] at hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hK]
    obtain ⟨k, hk⟩ := hx
    refine exists_int_eq_of_isIntegral_of_mul_eq_int (hfi m) hn (k := k) ?_
    rw [hk, map_smul, zsmul_eq_mul]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property K.mkQ (LinearMap.id) K.mkQ_surjective
  let p : (ι → ℤ) →ₗ[ℤ] (ι → ℤ) := LinearMap.id - s ∘ₗ K.mkQ
  have hp : ∀ m, p m ∈ K := by
    intro m
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have := LinearMap.congr_fun hs (K.mkQ m)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [p, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub, this,
      sub_self]
  have hp' : ∀ m ∈ K, p m = m := by
    intro m hm
    have : K.mkQ m = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hm
    simp only [p, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, this, map_zero,
      sub_zero]
  choose c hc using fun i : ι => (hK _).mp (hp (Pi.single i 1))
  refine ⟨c, fun m d h => ?_⟩
  have hm : m ∈ K := (hK m).mpr ⟨d, by rw [hf, h]⟩
  have hdec : m = ∑ i, m i • (Pi.single i 1 : ι → ℤ) := by
    ext j
    simp [Pi.single_apply]
  have key : ((∑ i, c i * m i : ℤ) : ℂ) = f (p m) := by
    conv_rhs => rw [hdec]

    rw [map_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, ← hc, zsmul_eq_mul, mul_comm]
  rw [hp' m hm, hf, h] at key
  exact_mod_cast key

end GlobalTheory.CuspGL
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsIntRelationOfIsIntegralRelationStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.exists_int_relation_of_isIntegral_relation : ∀ (ι : Type) [Fintype ι] (r : ι → ℂ), (∀ i, IsIntegral ℤ (r i)) → ∃ c : ι → ℤ, ∀ (m : ι → ℤ) (d : ℤ), ∑ i, r i * (m i : ℂ) = d → ∑ i, c i * m i = d := by
  first | exact @GlobalTheory.CuspGL.exists_int_retraction_of_isIntegral | exact GlobalTheory.CuspGL.exists_int_retraction_of_isIntegral | (intros; apply GlobalTheory.CuspGL.exists_int_retraction_of_isIntegral <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemVirtualCharactersOfIntegralCombination

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.BI

theorem one_mem_of_integral_combination : ∀ (G : Type) [Group G] [Finite G] (S : AddSubgroup (G → ℂ)), S ≤ Virt ℂ ℂ G → ∀ (ι : Type) [Fintype ι] (r : ι → ℂ) (s : ι → G → ℂ), (∀ i, IsIntegral ℤ (r i)) → (∀ i, s i ∈ S) → (∀ g, ∑ i, r i * s i g = 1) → (1 : G → ℂ) ∈ S := by
  intro G _ _ S hS ι _ r s hr hs hsum
  classical
  have := Fintype.ofFinite G
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_int_relation_of_isIntegral_relation ι r hr
  have hone : (1 : G → ℂ) ∈ Virt ℂ ℂ G := AddSubgroup.subset_closure (isChar_one ℂ ℂ G)
  have hcomb : (∑ i, c i • s i) ∈ S := S.sum_mem fun i _ => S.zsmul_mem (hs i) (c i)
  set f : G → ℂ := (∑ i, c i • s i) - 1 with hf
  have hfV : f ∈ Virt ℂ ℂ G := (Virt ℂ ℂ G).sub_mem (hS hcomb) hone
  have hN : (Nat.card G : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := G)).ne'
  choose m hm using fun i => GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card G (s i) f (hS (hs i)) hfV
  obtain ⟨d, hd⟩ := GlobalTheory.T.virtualCharacter_inner_eq_int_mul_card G 1 f hone hfV
  simp only [finsum_eq_sum_of_fintype] at hm hd
  have h1 : ∑ i, r i * (m i : ℂ) = d := by
    apply mul_right_cancel₀ hN
    rw [← hd, Finset.sum_mul]
    simp only [mul_assoc, ← hm, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [← mul_assoc, ← Finset.sum_mul, hsum g, Pi.one_apply]
  have h2 : ∑ i, (c i : ℂ) * (m i : ℂ) = d := by exact_mod_cast hc m d h1
  have hfg : ∀ g, f g = ∑ i, (c i : ℂ) * s i g - 1 := by
    intro g
    simp [hf, Finset.sum_apply]
  have h3 : ∑ g, f g * star (f g) = 0 := by
    have e : ∀ g, f g * star (f g) = ∑ i, (c i : ℂ) * (s i g * star (f g)) - (1 : G → ℂ) g * star (f g) := by
      intro g
      conv_lhs => enter [1]; rw [hfg g]
      simp only [sub_mul, Finset.sum_mul, mul_assoc, Pi.one_apply]
    simp only [e, Finset.sum_sub_distrib]
    rw [Finset.sum_comm, hd, ← h2, Finset.sum_mul, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.mul_sum, hm, mul_assoc]
  have h4 : ∑ g, Complex.normSq (f g) = 0 := by
    have : ((∑ g, Complex.normSq (f g) : ℝ) : ℂ) = 0 := by
      rw [← h3]; push_cast
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [← Complex.mul_conj]; rfl
    exact_mod_cast this
  have h5 : f = 0 := by
    funext g
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun g _ => Complex.normSq_nonneg (f g))).1 h4 g (Finset.mem_univ g)
    exact Complex.normSq_eq_zero.1 this
  have : (∑ i, c i • s i) = 1 := sub_eq_zero.1 (hf.symm.trans h5)
  exact this ▸ hcomb
end GlobalTheory.BI
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemVirtualCharactersOfIntegralCombinationStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.one_mem_virtualCharacters_of_integral_combination : ∀ (G : Type) [Group G] [Finite G] (S : AddSubgroup (G → ℂ)), S ≤ Virt ℂ ℂ G → ∀ (ι : Type) [Fintype ι] (r : ι → ℂ) (s : ι → G → ℂ), (∀ i, IsIntegral ℤ (r i)) → (∀ i, s i ∈ S) → (∀ g, ∑ i, r i * s i g = 1) → (1 : G → ℂ) ∈ S := by
  first | exact @GlobalTheory.BI.one_mem_of_integral_combination | exact GlobalTheory.BI.one_mem_of_integral_combination | (intros; apply GlobalTheory.BI.one_mem_of_integral_combination <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinearStatement

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

theorem _root_.GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear : ∀ (G : Type) [Group G] [Finite G], (∀ a ∈ Virt ℂ ℂ G, ∀ b ∈ Virt ℂ ℂ G, a * b ∈ Virt ℂ ℂ G) ∧ (∀ a ∈ Virt ℂ ℂ G, ∀ (H : Type) [Group H] (f : H →* G), (fun h => a (f h)) ∈ Virt ℂ ℂ H) ∧ (∀ a ∈ Virt ℂ ℂ G, ∀ g x : G, a (x⁻¹ * g * x) = a g) ∧ (∀ (H : Subgroup G) (ψ : H → ℂ), ψ ∈ Virt ℂ ℂ H → ind H ψ ∈ Virt ℂ ℂ G) ∧ ∀ lam : G →* ℂˣ, (fun g => (lam g : ℂ)) ∈ Virt ℂ ℂ G := by
  first | exact @GlobalTheory.BI.virt_mul_comap_conj_ind_linear | exact GlobalTheory.BI.virt_mul_comap_conj_ind_linear | (intros; apply GlobalTheory.BI.virt_mul_comap_conj_ind_linear <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemClosureInducedCentralByPrimePower

section

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.BI

theorem one_mem_closure_ind_centralByPrime :
    ∀ (G : Type) [Group G] [Finite G], (1 : G → ℂ) ∈ AddSubgroup.closure {f : G → ℂ | ∃ (E : Subgroup G) (ψ : E → ℂ), (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧ ψ ∈ Virt ℂ ℂ E ∧ f = ind E ψ} := by
  intro G _ _
  classical
  set A : Set (G → ℂ) := {f : G → ℂ | ∃ (E : Subgroup G) (ψ : E → ℂ), (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧ ψ ∈ Virt ℂ ℂ E ∧ f = ind E ψ} with hA
  obtain ⟨hmul, hpull, hclass, hind, -⟩ := GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear G
  have hAV : ∀ f ∈ A, f ∈ Virt ℂ ℂ G := by
    rintro f ⟨E, ψ, -, hψ, rfl⟩
    exact hind E ψ hψ
  have hJV : AddSubgroup.closure A ≤ Virt ℂ ℂ G := (AddSubgroup.closure_le _).2 hAV
  have hAA : ∀ f ∈ A, ∀ g ∈ A, f * g ∈ A := by
    intro f hf g hg
    have hgV := hAV g hg
    obtain ⟨E, ψ, hE, hψ, rfl⟩ := hf
    refine ⟨E, fun h => ψ h * g h, hE, ?_, ind_mul_classFun_eq_ind_mul_restrict G E ψ g (hclass g hgV)⟩
    exact (GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear E).1 ψ hψ _ (hpull g hgV E E.subtype)
  let R := integralClosure ℤ ℂ
  let J : Submodule R (G → ℂ) := Submodule.span R A
  have hJJ : ∀ f ∈ J, ∀ g ∈ J, f * g ∈ J := by
    intro f hf g hg
    induction hf, hg using Submodule.span_induction₂ with
    | mem_mem x y hx hy => exact Submodule.subset_span (hAA x hx y hy)
    | zero_left y hy => simp
    | zero_right x hx => simp
    | add_left x y z hx hy hz h1 h2 => rw [add_mul]; exact J.add_mem h1 h2
    | add_right x y z hx hy hz h1 h2 => rw [mul_add]; exact J.add_mem h1 h2
    | smul_left r x y hx hy h => rw [smul_mul_assoc]; exact J.smul_mem r h
    | smul_right r x y hx hy h => rw [mul_smul_comm]; exact J.smul_mem r h
  let c : (G → ℤ) →+* (G → ℂ) := (Int.castRingHom ℂ).compLeft G
  let S : AddSubgroup (G → ℤ) := J.toAddSubgroup.comap c.toAddMonoidHom
  have hS : ∀ f, f ∈ S ↔ c f ∈ J := fun f => Iff.rfl
  have h1 : (1 : G → ℤ) ∈ S := by
    refine GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd G S ?_ ?_
    · intro f hf g hg
      rw [hS] at hf hg ⊢
      rw [map_mul]
      exact hJJ _ hf _ hg
    · intro x p hp
      obtain ⟨E, f, ι, _, r, lam, hE, hf, hr, hsum⟩ := GlobalTheory.T.exists_integral_comb_induced_linear_not_dvd G x p hp
      refine ⟨f, ?_, hf⟩
      rw [hS]
      have : c f = ∑ i, (⟨r i, hr i⟩ : R) • ind E (fun e => (lam i e : ℂ)) := by
        funext g
        rw [Finset.sum_apply]
        exact hsum g
      rw [this]
      refine J.sum_mem fun i _ => J.smul_mem _ (Submodule.subset_span ?_)
      exact ⟨E, _, hE, (GlobalTheory.T.virtualCharacters_mul_comap_conj_ind_linear E).2.2.2.2 (lam i), rfl⟩
  rw [hS, map_one] at h1
  obtain ⟨n, r, s, hsum⟩ := Submodule.mem_span_set'.1 h1
  refine GlobalTheory.T.one_mem_virtualCharacters_of_integral_combination G _ hJV (Fin n) (fun i => (r i : ℂ)) (fun i => (s i : G → ℂ)) (fun i => (r i).2)
    (fun i => AddSubgroup.subset_closure (s i).2) fun g => ?_
  have := congrFun hsum g
  rw [Finset.sum_apply] at this
  exact this

end GlobalTheory.BI
end
end
