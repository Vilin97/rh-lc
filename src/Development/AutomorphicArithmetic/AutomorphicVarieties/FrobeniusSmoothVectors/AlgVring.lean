module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgLau
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgLimit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgModel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgDefs
import Mathlib.Algebra.AffineMonoid.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Filtration
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.SingleMemOfSpan
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgSep

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_sep :
    ∀ {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K] {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P), IsNoetherianRing (lauSub P) → ⨅ N : ℕ, vertex h ^ N = ⊥ := by
  intro C K _ _ _ _ P _ h hN
  classical
  rw [eq_bot_iff]
  intro p hp
  rw [Submodule.mem_iInf] at hp
  let comp : lauSub P → ℤ → lauSub P := fun x j =>
    ⟨AddMonoidAlgebra.single j (x.1.coeff j), single_mem_lauSub P (x.2 j)⟩
  have coeff_comp (x : lauSub P) (j : ℤ) :
      (comp x j).1 = AddMonoidAlgebra.single j (x.1.coeff j) := rfl
  have comp_mem_vertex : ∀ x : lauSub P, x ∈ vertex h → ∀ j, comp x j ∈ vertex h := by
    intro x hx j
    change ∃ c ∈ maximalIdeal C, algebraMap C K c = (comp x j).1.coeff 0
    rw [coeff_comp, AddMonoidAlgebra.coeff_single]
    by_cases hj : j = 0
    · subst j
      rw [Finsupp.single_eq_same]
      exact hx
    · exact ⟨0, Ideal.zero_mem _, by rw [Finsupp.single_eq_of_ne' hj, map_zero]⟩
  have comp_mem_pow : ∀ (N : ℕ) (x : lauSub P), x ∈ vertex h ^ N →
      ∀ j, comp x j ∈ vertex h ^ N := by
    intro N
    induction N with
    | zero =>
      intro x hx j
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on (C := fun z => ∀ j, comp z j ∈ vertex h ^ (n + 1)) hx ?_ ?_
      · intro y hy z hz j
        have e : comp (y * z) j =
            ∑ i ∈ y.1.coeff.support, comp y i * comp z (-i + j) := by
          apply Subtype.ext
          simp only [AddSubmonoidClass.coe_finsetSum, coeff_comp, Subalgebra.coe_mul,
            AddMonoidAlgebra.single_mul_single, add_neg_cancel_left]
          rw [AddMonoidAlgebra.coeff_mul_apply_left, Finsupp.sum]
          exact map_sum (AddMonoidAlgebra.singleAddHom j) _ _
        rw [e, pow_succ]
        exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (ih y hy i) (comp_mem_vertex z hz _)
      · intro y z hy hz j
        have e : comp (y + z) j = comp y j + comp z j := by
          apply Subtype.ext
          simp only [coeff_comp, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
            AddMonoidAlgebra.single_add]
        rw [e]
        exact add_mem (hy j) (hz j)
  have hcomp : ∀ j : ℤ, (p : AddMonoidAlgebra K ℤ).coeff j = 0 := by
    intro j
    let a := (p : AddMonoidAlgebra K ℤ).coeff j
    let q := comp p j
    have hq : ∀ N : ℕ, q ∈ vertex h ^ N := fun N => comp_mem_pow N p (hp N) j
    have hq' : q ∈ ⨅ i : ℕ, (vertex h) ^ i • (⊤ : Submodule (lauSub P) (lauSub P)) := by
      rw [Submodule.mem_iInf]
      intro i
      simp only [Ideal.smul_eq_mul, Ideal.mul_top]
      exact hq i
    obtain ⟨⟨r, hr⟩, hrq⟩ := (Ideal.mem_iInf_smul_pow_eq_bot_iff (vertex h) q).1 hq'
    have hrq' : r * q = q := hrq
    obtain ⟨c, hc, hcr⟩ := hr
    have h1 : ((r * q : lauSub P) : AddMonoidAlgebra K ℤ).coeff j =
        (r : AddMonoidAlgebra K ℤ).coeff 0 * a := by
      have h0 := AddMonoidAlgebra.coeff_mul_single_add (r : AddMonoidAlgebra K ℤ) a j 0
      rw [zero_add] at h0
      exact h0
    have h2 : ((r * q : lauSub P) : AddMonoidAlgebra K ℤ).coeff j = a := by
      rw [hrq']
      show (AddMonoidAlgebra.single j a).coeff j = a
      rw [AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]
    rw [h2, ← hcr] at h1
    have hu : IsUnit (algebraMap C K (1 - c)) :=
      (IsLocalRing.isUnit_one_sub_self_of_mem_nonunits c hc).map _
    have h3 : algebraMap C K (1 - c) * a = 0 := by
      rw [map_sub, map_one, sub_mul, one_mul, ← h1, sub_self]
    exact hu.mul_right_eq_zero.1 h3
  apply Subtype.ext
  ext j
  simpa using hcomp j
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgVertex

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_vertex :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {K : Type} [CommRing K] [Algebra C K] (ρ : NRep F n K), Cone O C ρ → HasVertex (ρ.part C) := by
  intro l _ O _ _ F n C _ _ _ K _ _ ρ hC
  have off : ∀ (L : List (F.G0 × Fin n × Fin n)) (j : ℤ),
      (L.map (fun s => w n s.2.1 - w n s.2.2)).sum = j → j ≠ 0 → ∃ s ∈ L, s.2.1 ≠ s.2.2 := by
    intro L j hL hj
    by_contra h
    push_neg at h
    apply hj
    rw [← hL]
    apply List.sum_eq_zero
    intro x hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
    rw [h s hs, sub_self]
  constructor
  · intro x hx
    have hle : ρ.mon 0 ⊆ (LinearMap.range (Algebra.linearMap C K) : Set K) := by
      rintro _ ⟨L, hL, rfl⟩
      by_cases hd : ∃ s ∈ L, s.2.1 ≠ s.2.2
      · obtain ⟨c, -, hc⟩ := hC.cyc L hL hd
        exact ⟨c, hc⟩
      · push_neg at hd
        have hm : (L.map (fun s => ρ.r s.1 s.2.1 s.2.2)).prod ∈ (algebraMap C K).rangeS := by
          apply list_prod_mem
          intro y hy
          obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hy
          rw [← hd s hs]
          obtain ⟨c, hc, -⟩ := hC.dg s.1 s.2.1
          exact ⟨c, hc⟩
        obtain ⟨c, hc⟩ := hm
        exact ⟨c, hc⟩
    obtain ⟨c, hc⟩ := Submodule.span_le.2 hle hx
    exact ⟨c, hc⟩
  · intro j hj x hx y hy
    open Pointwise in
    have hle : ρ.mon j * ρ.mon (-j) ⊆
        (Submodule.map (Algebra.linearMap C K) (maximalIdeal C) : Set K) := by
      rintro _ ⟨a, ⟨L1, h1, rfl⟩, b, ⟨L2, h2, rfl⟩, rfl⟩
      obtain ⟨s, hs, hne⟩ := off L1 j h1 hj
      obtain ⟨c, hc, hc'⟩ := hC.cyc (L1 ++ L2)
        (by rw [List.map_append, List.sum_append, h1, h2]; ring) ⟨s, List.mem_append_left _ hs, hne⟩
      refine Submodule.mem_map.2 ⟨c, hc, ?_⟩
      rw [Algebra.linearMap_apply, hc', List.map_append, List.prod_append]
    open Pointwise in
    have hxy : x * y ∈ Submodule.span C (ρ.mon j * ρ.mon (-j)) := by
      rw [← Submodule.span_mul_span]
      exact Submodule.mul_mem_mul hx hy
    obtain ⟨c, hc, hc'⟩ := Submodule.mem_map.1 (Submodule.span_le.2 hle hxy)
    exact ⟨c, hc, hc'⟩
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgVring

section

@[expose] public section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem alg_vring {C K : Type} [CommRing C] [IsLocalRing C] [CommRing K] [Algebra C K]
    {P : ℤ → Submodule C K} [SetLike.GradedMonoid P] (h : HasVertex P) (hi : Function.Injective (algebraMap C K))
    (hn : IsNoetherianRing (lauSub P)) : IsVertexRing C (vertex h) := by
  have hcoeff : ∀ c : C, ((algebraMap C (lauSub P) c : lauSub P) : AddMonoidAlgebra K ℤ).coeff 0 = algebraMap C K c := by
    intro c
    simp
  refine ⟨hn, ?_, alg_sep h hn, ?_, ?_⟩
  · intro c c' hcc
    apply hi
    rw [← hcoeff c, ← hcoeff c', hcc]
  · ext c
    rw [Ideal.mem_comap, mem_vertex, hcoeff]
    constructor
    · rintro ⟨c', hc', he⟩
      rwa [← hi he]
    · intro hc
      exact ⟨c, hc, rfl⟩
  · intro d
    obtain ⟨c, hc⟩ := h.zero _ (d.2 0)
    refine ⟨c, ?_⟩
    rw [mem_vertex]
    refine ⟨0, (maximalIdeal C).zero_mem, ?_⟩
    simp [hc]

private theorem alg_ev (C K : Type) [CommRing C] [CommRing K] [Algebra C K] :
    ∃ e : AddMonoidAlgebra K ℤ →ₐ[C] K, ∀ j x, e (AddMonoidAlgebra.single j x) = x := by
  refine ⟨AddMonoidAlgebra.liftNCAlgHom (AlgHom.id C K) 1 (fun _ _ => Commute.one_right _), fun j x => ?_⟩
  exact (AddMonoidAlgebra.liftNC_single _ _ _ _).trans (by simp)

theorem UpperTheory.V.Fr.alg :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra O K] [Algebra C K] [IsScalarTower O C K], Function.Injective (algebraMap C K) → ∀ ρ : NRep F n K, Cone O C ρ → ∃ (ξ : S.A →ₐ[O] K) (β : S.B →ₐ[O] C), S.u.map (ξ : S.A →+* K) = ρ ∧ ∀ b, ξ (S.inc b) = algebraMap C K (β b) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ K _ _ _ _ hi ρ hcone
  have hv := alg_vertex C ρ hcone
  haveI := alg_ft C ρ hcone.fg
  have hN : IsNoetherianRing (lauSub (NRep.part C ρ)) := Algebra.FiniteType.isNoetherianRing C _
  have hvr := alg_vring hv hi hN
  obtain ⟨ρD, h1, h2⟩ := alg_lau C ρ hcone
  have hmod := alg_model C ρ hcone hv ρD h1 h2
  letI : Algebra O (lauSub (NRep.part C ρ)) :=
    ((algebraMap C (lauSub (NRep.part C ρ))).comp (algebraMap O C)).toAlgebra
  haveI : IsScalarTower O C (lauSub (NRep.part C ρ)) := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨ξ, β, hξ, hβ⟩ := alg_limit S C (vertex hv) ρD hvr hmod
  obtain ⟨e, he⟩ := alg_ev C K
  let ev : lauSub (NRep.part C ρ) →ₐ[O] K := (e.comp (lauSub (NRep.part C ρ)).val).restrictScalars O
  refine ⟨ev.comp ξ, β, ?_, fun b => ?_⟩
  · apply NRep.ext
    · ext g i j
      rw [NRep.map_r]
      have hr := NRep.map_r (ξ : S.A →+* lauSub (NRep.part C ρ)) S.u g i j
      rw [hξ] at hr
      show e ((ξ (S.u.r g i j) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
      have hr' : ξ (S.u.r g i j) = ρD.r g i j := hr.symm
      rw [hr', h1, he]
    · funext v i
      ext g
      rw [NRep.map_ψ]
      have hp := NRep.map_ψ (ξ : S.A →+* lauSub (NRep.part C ρ)) S.u v i g
      rw [hξ] at hp
      show e ((ξ ((S.u.ψ v i g : S.Aˣ) : S.A) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
      have hp' : ξ ((S.u.ψ v i g : S.Aˣ) : S.A) = ((ρD.ψ v i g : (lauSub (NRep.part C ρ))ˣ) : lauSub (NRep.part C ρ)) := hp.symm
      rw [hp', h2, he]
  · show e ((ξ (S.inc b) : lauSub (NRep.part C ρ)) : AddMonoidAlgebra K ℤ) = _
    rw [hβ b]
    exact e.commutes (β b)
end
end
