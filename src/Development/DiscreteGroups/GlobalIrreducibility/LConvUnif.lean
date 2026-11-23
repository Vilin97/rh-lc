module

public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.DiscreteGroups.GlobalIrreducibility.LConvCut
public import GroundTheory.AutomorphicForms.SmoothRep
public import Mathlib.RepresentationTheory.Irreducible
public import GroundTheory.AutomorphicForms.HeckeIrreducible
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.BurnsideSurjectivity.Burnside
public import GroundTheory.AutomorphicForms.Cartan
public import Development.DiscreteGroups.GlobalIrreducibility.LConvUnifB
public import GroundTheory.AutomorphicForms.JacquetAdmissible
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvUnifA

section

@[expose] public section

noncomputable section

namespace DiscreteGroups.sglob.LConvU

open GroundTheory.Automorphic Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (hρ : IsSmooth ρ) {K : Subgroup G} (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

include hρ hKc hKo

theorem fixedProj_eq_avg {L : Subgroup G} (hLK : L ≤ K) (hLo : IsOpen (L : Set G)) :
    ∃ (N : ℕ) (r : Fin N → G), 0 < N ∧ (∀ i, r i ∈ K) ∧
      ∀ v : V, v ∈ fixedVectors ρ L →
        (fixedProj ρ hρ hKc hKo v : V) = (N : ℂ)⁻¹ • ∑ i, ρ (r i) v := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  have hHo : IsOpen ((L.subgroupOf K : Subgroup K) : Set K) := hLo.preimage continuous_subtype_val
  have : Finite (K ⧸ L.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hHo
  let _ : Fintype (K ⧸ L.subgroupOf K) := Fintype.ofFinite _
  have hNpos : 0 < Fintype.card (K ⧸ L.subgroupOf K) :=
    Fintype.card_pos_iff.mpr ⟨QuotientGroup.mk (1 : K)⟩
  let eQ := Fintype.equivFin (K ⧸ L.subgroupOf K)
  refine ⟨Fintype.card (K ⧸ L.subgroupOf K), fun i => ((Quotient.out (eQ.symm i) : K) : G), hNpos,
    fun i => (Quotient.out (eQ.symm i)).2, ?_⟩
  intro v hv
  obtain ⟨s, hs⟩ : ∃ s : V, s = ∑ q : K ⧸ L.subgroupOf K, ρ ((Quotient.out q : K) : G) v := ⟨_, rfl⟩
  have hreidx : ∑ i, ρ ((Quotient.out (eQ.symm i) : K) : G) v = s := by
    rw [hs]
    exact Fintype.sum_equiv eQ.symm _ _ (fun _ => rfl)
  have hsK : s ∈ fixedVectors ρ K := by
    intro k hk
    have key : ∀ q : K ⧸ L.subgroupOf K, ρ k (ρ ((Quotient.out q : K) : G) v) =
        ρ ((Quotient.out ((⟨k, hk⟩ : K) • q) : K) : G) v := by
      intro q
      rw [← Module.End.mul_apply, ← map_mul]
      have h1 : (((⟨k, hk⟩ : K) * Quotient.out q : K) : G) = k * ((Quotient.out q : K) : G) := rfl
      rw [← h1]
      apply act_eq_of_mk_eq ρ hv
      rw [QuotientGroup.out_eq', ← smul_eq_mul, MulAction.Quotient.mk_smul_out]

    rw [hs, map_sum, Finset.sum_congr rfl (fun q _ => key q)]
    exact Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ (fun _ => rfl)
  have hsub : s - ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • v ∈ coinvariantsKer ρ K := by
    have h1 : s - ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • v =
        ∑ q : K ⧸ L.subgroupOf K, (ρ ((Quotient.out q : K) : G) v - v) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul, hs]
    rw [h1]
    exact Submodule.sum_mem _ fun q _ => sub_mem_coinvariantsKer (Quotient.out q).2 v
  have h1 : (fixedProj ρ hρ hKc hKo s : V) = s := fixedProj_apply_of_mem hρ hKc hKo hsK
  have h2 := fixedProj_apply_of_mem_coinvariantsKer hρ hKc hKo hsub
  rw [map_sub, map_smul, sub_eq_zero] at h2
  have h3 : ((Fintype.card (K ⧸ L.subgroupOf K) : ℕ) : ℂ) • (fixedProj ρ hρ hKc hKo v : V) = s := by
    rw [← h1, h2, Submodule.coe_smul]
  rw [hreidx, ← h3, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hNpos.ne'), one_smul]

theorem map_fixedProj_of_invariant {U : Type*} [AddCommGroup U] [Module ℂ U] (f : V →ₗ[ℂ] U)
    (v : V) (hf : ∀ k ∈ K, f (ρ k v) = f v) : f (fixedProj ρ hρ hKc hKo v : V) = f v := by
  have hLo : IsOpen ((K ⊓ stabilizerOf ρ v : Subgroup G) : Set G) := by
    rw [Subgroup.coe_inf]; exact hKo.inter (hρ v)
  obtain ⟨N, r, hN, hr, h⟩ := fixedProj_eq_avg hρ hKc hKo (L := K ⊓ stabilizerOf ρ v) inf_le_left hLo

  rw [h v (fun l hl => hl.2), map_smul, map_sum, Finset.sum_congr rfl (fun i _ => hf (r i) (hr i)),
  Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
  inv_mul_cancel₀ (by exact_mod_cast hN.ne'), one_smul]


variable (ρ) in
def hop (g : G) : Module.End ℂ (fixedVectors ρ K) :=
  (fixedProj ρ hρ hKc hKo) ∘ₗ (ρ g) ∘ₗ (fixedVectors ρ K).subtype

theorem hop_apply (g : G) (w : fixedVectors ρ K) :
    hop ρ hρ hKc hKo g w = fixedProj ρ hρ hKc hKo (ρ g w) := rfl

theorem hop_of_mem {κ : G} (hκ : κ ∈ K) : hop ρ hρ hKc hKo κ = 1 := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  rw [hop_apply, fixedProj_apply_act hρ hKc hKo hκ, Module.End.one_apply,
    fixedProj_apply_of_mem hρ hKc hKo w.2]

theorem hop_one : hop ρ hρ hKc hKo 1 = 1 := hop_of_mem hρ hKc hKo K.one_mem

theorem hop_mul {g h : G}
    (H : ∀ w ∈ fixedVectors ρ K, ∀ κ ∈ K,
      fixedProj ρ hρ hKc hKo (ρ (g * κ * h) w) = fixedProj ρ hρ hKc hKo (ρ (g * h) w)) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h = hop ρ hρ hKc hKo (g * h) := by
  refine LinearMap.ext fun w => ?_
  show fixedProj ρ hρ hKc hKo (ρ g (fixedProj ρ hρ hKc hKo (ρ h w) : V)) =
    fixedProj ρ hρ hKc hKo (ρ (g * h) w)
  have key := map_fixedProj_of_invariant hρ hKc hKo ((fixedProj ρ hρ hKc hKo) ∘ₗ ρ g) (ρ h w)
    (fun κ hκ => by
      simp only [LinearMap.comp_apply]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, H w w.2 κ hκ,
        map_mul, Module.End.mul_apply])
  simp only [LinearMap.comp_apply] at key
  rw [key, map_mul, Module.End.mul_apply]

theorem hop_mul_mem_span (g h : G) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
  let L : Subgroup G := K ⊓ K.comap (MulAut.conj h⁻¹).toMonoidHom
  have hLo : IsOpen (L : Set G) := by
    have hc : Continuous fun x : G => h⁻¹ * x * h⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hKo.inter (hKo.preimage hc)
  obtain ⟨N, r, hN, -, hav⟩ := fixedProj_eq_avg hρ hKc hKo (L := L) inf_le_left hLo
  have hfix : ∀ w : fixedVectors ρ K, ρ h (w : V) ∈ fixedVectors ρ L := by
    intro w l hl
    have hl2 : h⁻¹ * l * h ∈ K := by
      have := hl.2
      simpa [Subgroup.mem_comap, MulAut.conj_apply] using this
    calc ρ l (ρ h w) = ρ h (ρ (h⁻¹ * l * h) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]; congr 2; group
      _ = ρ h w := by rw [w.2 _ hl2]
  have heq : hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo h =
      (N : ℂ)⁻¹ • ∑ i, hop ρ hρ hKc hKo (g * r i * h) := by
    refine LinearMap.ext fun w => ?_
    show fixedProj ρ hρ hKc hKo (ρ g (fixedProj ρ hρ hKc hKo (ρ h w) : V)) = _

    rw [hav _ (hfix w), map_smul, map_smul, map_sum, map_sum, LinearMap.smul_apply,
    LinearMap.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = fixedProj ρ hρ hKc hKo (ρ (g * r i * h) w)
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨_, rfl⟩)

theorem span_hop_mul_mem {a b : Module.End ℂ (fixedVectors ρ K)}
    (ha : a ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)))
    (hb : b ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo))) :
    a * b ∈ Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
    induction hb using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      exact hop_mul_mem_span hρ hKc hKo g h
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [mul_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hy
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x z _ _ hx hz => rw [add_mul]; exact Submodule.add_mem _ hx hz
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

theorem span_hop_eq_top [ρ.IsIrreducible] [FiniteDimensional ℂ (fixedVectors ρ K)]
    [Nontrivial (fixedVectors ρ K)] :
    Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) = ⊤ := by
  have hone : (1 : Module.End ℂ (fixedVectors ρ K)) ∈
      Submodule.span ℂ (Set.range (hop ρ hρ hKc hKo)) := by
    rw [← hop_one hρ hKc hKo]; exact Submodule.subset_span ⟨1, rfl⟩
  let A : Subalgebra ℂ (Module.End ℂ (fixedVectors ρ K)) :=
    Submodule.toSubalgebra _ hone (fun a b ha hb => span_hop_mul_mem hρ hKc hKo ha hb)
  have hirr : ∀ U : Submodule ℂ (fixedVectors ρ K),
      (∀ a : A, ∀ w ∈ U, A.val a w ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    right
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have hT : ∀ g, hop ρ hρ hKc hKo g u ∈ U := fun g =>
      hU ⟨hop ρ hρ hKc hKo g, Submodule.subset_span ⟨g, rfl⟩⟩ u huU
    rw [eq_top_iff]
    intro w _
    have hu0' : (u : V) ≠ 0 := fun h => hu0 (Subtype.ext h)
    have hw := HeckeAlgebra.mem_span_orbit (ρ := ρ) hu0' (w : V)
    have hww : w = fixedProj ρ hρ hKc hKo (w : V) :=
      Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo w.2).symm
    rw [hww]
    have hle : Submodule.map (fixedProj ρ hρ hKc hKo)
        (Submodule.span ℂ (Set.range fun g => ρ g (u : V))) ≤ U := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
      exact hT g
    exact hle ⟨_, hw, rfl⟩
  have hsurj := ReciprocityTheory.GC.burnside_surj_of_irred (k := ℂ) A.val hirr
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha⟩ := hsurj x
  rw [← ha]
  exact a.2

end DiscreteGroups.sglob.LConvU
end
end
end

-- Source module: Development.DiscreteGroups.GlobalIrreducibility.LConvUnif

section

@[expose] public section

noncomputable section

namespace DiscreteGroups.sglob.LConvU

open GroundTheory.Automorphic GroundTheory.Automorphic.Cartan GroundTheory.Automorphic.Parabolic Matrix

section Hop

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin n) F) V}
  (hρ : GroundTheory.Automorphic.IsSmooth ρ) {r : ℕ}
  (hKc : IsCompact (GLnLocal.congruenceSubgroup F n r : Set (GL (Fin n) F)))
  (hKo : IsOpen (GLnLocal.congruenceSubgroup F n r : Set (GL (Fin n) F)))

include hρ hKc hKo

theorem hop_diagPow_mul (hr : 1 ≤ r) {μ ν : Fin n → ℤ} (hμ : IsDominant μ) (hν : IsDominant ν) :
    hop ρ hρ hKc hKo (diagPow F n μ) * hop ρ hρ hKc hKo (diagPow F n ν) =
      hop ρ hρ hKc hKo (diagPow F n (μ + ν)) := by
  rw [diagPow_add]
  refine hop_mul hρ hKc hKo fun w hw κ hκ => ?_
  obtain ⟨a, ha, b, hb, c, hc, h⟩ := dominant_conj hr hμ hν hκ
  have hbc : ρ (b * c) w = w := hw _ (mul_mem hb hc)
  rw [h, show a * (diagPow F n μ * diagPow F n ν) * b * c =
      a * ((diagPow F n μ * diagPow F n ν) * (b * c)) by group,
    map_mul, mul_apply_eq_comp, fixedProj_apply_act hρ hKc hKo ha, map_mul,
    mul_apply_eq_comp, hbc]

theorem hop_integral_mul {k : GL (Fin n) F} (hk : k ∈ GLnLocal.integralGL F n)
    (g : GL (Fin n) F) :
    hop ρ hρ hKc hKo k * hop ρ hρ hKc hKo g = hop ρ hρ hKc hKo (k * g) := by
  refine hop_mul hρ hKc hKo fun w _ κ hκ => ?_
  rw [show k * κ * g = (k * κ * k⁻¹) * (k * g) by group, map_mul, mul_apply_eq_comp,
    fixedProj_apply_act hρ hKc hKo (GLnLocal.conj_mem_congruenceSubgroup F n hk hκ)]

theorem hop_mul_integral (g : GL (Fin n) F) {k : GL (Fin n) F}
    (hk : k ∈ GLnLocal.integralGL F n) :
    hop ρ hρ hKc hKo g * hop ρ hρ hKc hKo k = hop ρ hρ hKc hKo (g * k) := by
  refine hop_mul hρ hKc hKo fun w hw κ hκ => ?_
  rw [show g * κ * k = (g * k) * (k⁻¹ * κ * k⁻¹⁻¹) by group, map_mul, mul_apply_eq_comp,
    hw _ (GLnLocal.conj_mem_congruenceSubgroup F n (inv_mem hk) hκ)]

local notation "K0" => GLnLocal.integralGL F n
local notation "Kr" => GLnLocal.congruenceSubgroup F n r
local notation "W" => fixedVectors ρ Kr
local notation "T" => hop ρ hρ hKc hKo

theorem finrank_le_of_commBound (hr : 1 ≤ r) [ρ.IsIrreducible] [FiniteDimensional ℂ W]
    [Fintype (K0 ⧸ (Kr).subgroupOf K0)] {c : ℕ}
    (hc : ∀ a : Fin (n + 1) → Module.End ℂ W, (∀ i j, a i * a j = a j * a i) →
      2 * Fintype.card (K0 ⧸ (Kr).subgroupOf K0) ^ 2 *
          Module.finrank ℂ (Algebra.adjoin ℂ (Set.range a)) ≤
        Module.finrank ℂ W ^ 2 + c * Module.finrank ℂ W) :
    Module.finrank ℂ W ≤ c := by
  classical
  by_cases h0 : Module.finrank ℂ W = 0
  · rw [h0]; exact Nat.zero_le _
  have hpos : 0 < Module.finrank ℂ W := Nat.pos_of_ne_zero h0
  have : Nontrivial W := Module.finrank_pos_iff.1 hpos
  have hspan := span_hop_eq_top hρ hKc hKo
  let a : Fin (n + 1) → Module.End ℂ W := fun i => T (diagPow F n (gen n i))
  have hcomm : ∀ i j, a i * a j = a j * a i := fun i j => by
    simp only [a]
    rw [hop_diagPow_mul hρ hKc hKo hr (gen_dominant n i) (gen_dominant n j),
      hop_diagPow_mul hρ hKc hKo hr (gen_dominant n j) (gen_dominant n i), add_comm]
  let C := Algebra.adjoin ℂ (Set.range a)
  have hTC : ∀ μ, IsDominant μ → T (diagPow F n μ) ∈ C := by
    refine dom_induct (fun μ => T (diagPow F n μ) ∈ C) ?_ ?_ ?_
    · show T (diagPow F n 0) ∈ C
      rw [diagPow_zero, hop_one]
      exact C.one_mem
    · intro i
      exact Algebra.subset_adjoin ⟨i, rfl⟩
    · intro μ ν hμ hν h1 h2
      show T (diagPow F n (μ + ν)) ∈ C
      rw [← hop_diagPow_mul hρ hKc hKo hr hμ hν]
      exact C.mul_mem h1 h2
  let P : (K0 ⧸ (Kr).subgroupOf K0) → Module.End ℂ W :=
    fun q => T ((Quotient.out q : K0) : GL (Fin n) F)
  have hP : ∀ k (hk : k ∈ K0), P (QuotientGroup.mk ⟨k, hk⟩) = T k := by
    intro k hk
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((Kr).subgroupOf K0) (⟨k, hk⟩ : K0)
    show T ((Quotient.out (QuotientGroup.mk ⟨k, hk⟩ : K0 ⧸ (Kr).subgroupOf K0) : K0) :
      GL (Fin n) F) = T k
    rw [hh, Subgroup.coe_mul, ← hop_mul_integral hρ hKc hKo _ ((h : K0)).2,
      hop_of_mem hρ hKc hKo (Subgroup.mem_subgroupOf.1 h.2), mul_one]
  have hCfin : FiniteDimensional ℂ C :=
    Module.Finite.of_injective C.val.toLinearMap Subtype.val_injective
  let Φ : ((K0 ⧸ (Kr).subgroupOf K0) × (K0 ⧸ (Kr).subgroupOf K0) → C) →ₗ[ℂ] Module.End ℂ W :=
    ∑ p, (LinearMap.mulLeft ℂ (P p.1)) ∘ₗ (LinearMap.mulRight ℂ (P p.2)) ∘ₗ
      C.val.toLinearMap ∘ₗ LinearMap.proj p
  have hΦ : ∀ f, Φ f = ∑ p, P p.1 * (((f p : C) : Module.End ℂ W) * P p.2) := by
    intro f
    rw [LinearMap.sum_apply]
    rfl
  have hrange : Set.range T ⊆ LinearMap.range Φ := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨μ, hμ, k1, hk1, k2, hk2, hg⟩ := exists_eq_mul_diagPow_mul F n g
    refine ⟨Pi.single (QuotientGroup.mk ⟨k1, hk1⟩, QuotientGroup.mk ⟨k2, hk2⟩)
      ⟨_, hTC μ hμ⟩, ?_⟩
    rw [hΦ, Finset.sum_eq_single (QuotientGroup.mk ⟨k1, hk1⟩, QuotientGroup.mk ⟨k2, hk2⟩)]
    · rw [Pi.single_eq_same]
      show P (QuotientGroup.mk ⟨k1, hk1⟩) * (T (diagPow F n μ) * P (QuotientGroup.mk ⟨k2, hk2⟩)) = T g
      rw [hP, hP, hg, mul_assoc, hop_mul_integral hρ hKc hKo _ hk2,
        hop_integral_mul hρ hKc hKo hk1]
    · intro p _ hp
      rw [Pi.single_eq_of_ne hp]
      simp
    · intro h
      exact absurd (Finset.mem_univ _) h
  have htop : LinearMap.range Φ = ⊤ := by
    rw [eq_top_iff, ← hspan, Submodule.span_le]
    exact hrange
  have hdim := LinearMap.finrank_range_le Φ
  rw [htop, finrank_top, Module.finrank_linearMap, Module.finrank_pi_fintype] at hdim
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul] at hdim
  have hcb := hc a hcomm
  have h2 : Module.finrank ℂ W * Module.finrank ℂ W ≤ c * Module.finrank ℂ W := by
    nlinarith [hdim, hcb]
  exact Nat.le_of_mul_le_mul_right h2 hpos

end Hop

end DiscreteGroups.sglob.LConvU

namespace DiscreteGroups.sglob.LConv

open GroundTheory.Automorphic GroundTheory.Automorphic.Parabolic DiscreteGroups.sglob.LConvU

theorem unifOfComm : UnifOfComm := by
  intro hCB k _ _ _ _ m K hK
  classical
  obtain ⟨r0, -, hr0⟩ := (GLnLocal.hasBasis_nhds_one k m).mem_iff.1 (hK.mem_nhds K.one_mem)
  obtain ⟨r, hr, hrr⟩ : ∃ r, 1 ≤ r ∧ r0 ≤ r := ⟨max r0 1, le_max_right _ _, le_max_left _ _⟩
  have hKrK : GLnLocal.congruenceSubgroup k m r ≤ K := fun x hx =>
    hr0 (GLnLocal.congruenceSubgroup_antitone k m hrr hx)
  have hKc := GLnLocal.isCompact_congruenceSubgroup k m r
  have hKo := GLnLocal.isOpen_congruenceSubgroup k m r
  have : CompactSpace (GLnLocal.integralGL k m) :=
    isCompact_iff_compactSpace.mp (GLnLocal.isCompact_integralGL k m)
  have hHo : IsOpen (((GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m) :
      Subgroup (GLnLocal.integralGL k m)) : Set (GLnLocal.integralGL k m)) :=
    hKo.preimage continuous_subtype_val
  have : Finite (GLnLocal.integralGL k m ⧸
      (GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m)) :=
    Subgroup.quotient_finite_of_isOpen _ hHo
  let _ : Fintype (GLnLocal.integralGL k m ⧸
      (GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m)) :=
    Fintype.ofFinite _
  obtain ⟨c, hc⟩ := hCB (m + 1) (2 * Fintype.card (GLnLocal.integralGL k m ⧸
      (GLnLocal.congruenceSubgroup k m r).subgroupOf (GLnLocal.integralGL k m)) ^ 2)
  refine ⟨c, fun V _ _ ρ hρs hρi => ?_⟩
  have hρ : GroundTheory.Automorphic.IsSmooth ρ := fun v => hρs v
  have : ρ.IsIrreducible := hρi
  have hfin : FiniteDimensional ℂ (fixedVectors ρ (GLnLocal.congruenceSubgroup k m r)) :=
    (isAdmissible_of_isIrreducible hρ).2 _ hKc hKo
  have hle : GlobalTheory.PRep.fixed ρ K ≤ fixedVectors ρ (GLnLocal.congruenceSubgroup k m r) := by
    intro v hv κ hκ
    have := hv ⟨κ, hKrK hκ⟩
    simpa using this
  refine ⟨Submodule.finiteDimensional_of_le hle, ?_⟩
  exact (LinearMap.finrank_le_finrank_of_injective (f := Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)).trans
    (finrank_le_of_commBound hρ hKc hKo hr (c := c) fun a ha => hc _ a ha)

end DiscreteGroups.sglob.LConv
end
end
end
