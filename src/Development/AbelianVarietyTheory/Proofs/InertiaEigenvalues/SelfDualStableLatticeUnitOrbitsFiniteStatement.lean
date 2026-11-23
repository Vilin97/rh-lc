module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulOfSeparableGenerated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerBasisOfCharpolySeparable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscrMulMemOfIsIntegral
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSelfDualIntegralHermitianLatticesModUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSubmodulesBetweenMulLeftImageLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KappaSumZeroAndStableSumMulZeroOfNotIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexUnitStabilizerIntegralUnitsNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusSubmoduleMulLeftImageMemSelfDualStableLatti

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConductorMulMemAdjoinOfSeparable

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

theorem exists_conductor_mul_mem_adjoin : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsIntegral K.O B.g →
    ∃ c : K.O, c ≠ 0 ∧ ∀ u : B.A, IsIntegral K.O u →
      algebraMap K.O B.A c * u ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
  intro K B hP hg
  classical
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B hP
  have hint : ∀ x : B.A, IsIntegral K.O x →
      ∃ t : K.O, algebraMap K.O K.E t = Algebra.trace K.E B.A x := fun x hx =>
    IsIntegrallyClosed.isIntegral_iff.1
      (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral K.O K.E B.A x hx)
  have he_int : ∀ i, IsIntegral K.O (e i) := fun i => by rw [he]; exact hg.pow _
  have hG : ∀ i j, ∃ t : K.O, algebraMap K.O K.E t = Algebra.trace K.E B.A (e i * e j) :=
    fun i j => hint _ ((he_int i).mul (he_int j))
  choose t ht using hG
  let c : K.O := (Matrix.of t).det
  have hc : algebraMap K.O K.E c = (Algebra.traceMatrix K.E e).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [ht, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have hgen : ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f := by
    intro a
    refine ⟨∑ i : Fin (Module.finrank K.E B.A), monomial (i : ℕ) (e.repr a i), ?_⟩
    calc a = ∑ i, e.repr a i • e i := (e.sum_repr a).symm
      _ = _ := by simp [map_sum, aeval_monomial, he, Algebra.smul_def]
  have hdet : (Algebra.traceMatrix K.E e).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    have hwv : e.equivFun (∑ j, v j • e j) = v := by
      rw [← e.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    have hti : ∀ i, Algebra.trace K.E B.A ((∑ j, v j • e j) * e i) = 0 := by
      intro i
      have := congrFun (Algebra.traceMatrix_of_basis_mulVec e (∑ j, v j • e j)) i
      rw [hwv, hv] at this
      exact this.symm
    have hw := GlobalTheory.UnitLemma.TraceNondeg.eq_zero_of_trace_mul_eq_zero K B hP hgen
      (∑ j, v j • e j) (fun y => by

        rw [← e.sum_repr y, Finset.mul_sum, map_sum]
        simp [mul_smul_comm, hti])
    exact funext (Fintype.linearIndependent_iff.1 e.linearIndependent v hw)
  refine ⟨c, fun h0 => hdet (by rw [← hc, h0, map_zero]), fun u hu => ?_⟩
  obtain ⟨w, hw⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum K.O K.E B.A _ e u
    (fun i j => ⟨_, ht i j⟩) (fun i => hint _ (hu.mul (he_int i)))
  have h1 : algebraMap K.O B.A c * u = ∑ j, w j • B.g ^ (j : ℕ) := by
    rw [IsScalarTower.algebraMap_apply K.O K.E B.A, ← Algebra.smul_def, hc, hw]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [algebraMap_smul, he]
  rw [h1]
  exact Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _) _

end GlobalTheory.UnitLemma
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConductorMulMemAdjoinOfSeparableStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.exists_conductor_mul_mem_adjoin_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsIntegral K.O B.g → ∃ c : K.O, c ≠ 0 ∧ ∀ u : B.A, IsIntegral K.O u → algebraMap K.O B.A c * u ∈ Algebra.adjoin K.O ({B.g} : Set B.A) := by
  first | exact @GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin | exact GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin | (intros; apply GlobalTheory.UnitLemma.exists_conductor_mul_mem_adjoin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMaximalOrderHullSelfDualStableLattice

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.HullLat

theorem fg_of_le {R M : Type} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {L X : Submodule R M} (hL : L.FG) (hX : X ≤ L) : X.FG := by
  haveI : IsNoetherian R L := isNoetherian_of_fg_of_noetherian L hL
  have h1 : (X.comap L.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map L.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hX] at h2

theorem exists_hull : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (c : K.O), c ≠ 0 → ∀ L ∈ B.X x,
    (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) →
    ∃ J : Submodule K.O B.A, IsLat K.O K.E J ∧ (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) ∧
      (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) ∧
      (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈
        (algebraMap K.O K.E).range) ∧ mulLat K.O (algebraMap K.O B.A c) J ≤ L ∧ L ≤ J := by
  intro K B x c hc L hL hcL
  obtain ⟨⟨hfg, hspan⟩, -, hdual⟩ := hL
  set Λ := Subalgebra.toSubmodule (integralClosure K.O B.A) with hΛ
  set J : Submodule K.O B.A := Λ * L with hJ
  set γ := algebraMap K.O B.A c with hγ

  have hγu : IsUnit γ := by
    have h0 : algebraMap K.O K.E c ≠ 0 := by
      intro h; exact hc (IsFractionRing.injective K.O K.E (by simpa using h))
    rw [hγ, IsScalarTower.algebraMap_apply K.O K.E B.A]
    exact (isUnit_iff_ne_zero.mpr h0).map (algebraMap K.E B.A)
  have hLJ : L ≤ J := fun y hy => by
    simpa using Submodule.mul_mem_mul (M := Λ) (N := L)
      (show (1 : B.A) ∈ Λ from (integralClosure K.O B.A).one_mem) hy
  have hcJ : ∀ y ∈ J, γ * y ∈ L := by
    intro y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro u hu l hl
      rw [← mul_assoc]
      exact hcL u ((mem_integralClosure_iff _ _).mp hu) l hl
    · intro a b ha hb
      rw [mul_add]; exact add_mem ha hb
  have hmulJ : mulLat K.O γ J ≤ L := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcJ y hy

  have hJfg : J.FG := by
    obtain ⟨u, hu⟩ := hγu
    have hM : (L.map (LinearMap.mulLeft K.O ((u⁻¹ : B.Aˣ) : B.A))).FG := hfg.map _
    refine fg_of_le hM ?_
    intro y hy
    refine ⟨γ * y, hcJ y hy, ?_⟩
    simp only [LinearMap.mulLeft_apply]
    rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
  refine ⟨J, ⟨hJfg, ?_⟩, ?_, ?_, ?_, hmulJ, hLJ⟩
  · rw [eq_top_iff, ← hspan]
    exact Submodule.span_mono hLJ
  · intro a ha y hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro u hu l hl
      rw [← mul_assoc]
      have hu' : u ∈ integralClosure K.O B.A := hu
      exact Submodule.mul_mem_mul (show a * u ∈ Λ from (integralClosure K.O B.A).mul_mem ha hu') hl
    · intro p q hp hq
      rw [mul_add]; exact add_mem hp hq
  · intro y hy
    exact hLJ ((hdual y).mpr fun z hz => hy z (hLJ hz))
  · intro y hy z hz
    exact (hdual (γ * y)).mp (hcJ y hy) (γ * z) (hcJ z hz)

end GlobalTheory.HullLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMaximalOrderHullSelfDualStableLatticeStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.exists_maximalOrder_hull_selfDual_stable_lattice : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (c : K.O), c ≠ 0 → ∀ L ∈ B.X x, (∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L) → ∃ J : Submodule K.O B.A, IsLat K.O K.E J ∧ (∀ a ∈ integralClosure K.O B.A, ∀ y ∈ J, a * y ∈ J) ∧ (∀ y, (∀ z ∈ J, B.herm x y z ∈ (algebraMap K.O K.E).range) → y ∈ J) ∧ (∀ y ∈ J, ∀ z ∈ J, B.herm x (algebraMap K.O B.A c * y) (algebraMap K.O B.A c * z) ∈ (algebraMap K.O K.E).range) ∧ mulLat K.O (algebraMap K.O B.A c) J ≤ L ∧ L ≤ J := by
  first | exact @GlobalTheory.HullLat.exists_hull | exact GlobalTheory.HullLat.exists_hull | (intros; apply GlobalTheory.HullLat.exists_hull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorusSubmoduleMulLeftImageMemSelfDualStableLattiStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.torus_submoduleMulLeftImage_mem_selfDualStableLattices : ∀ (K : UQ) (B : InvAlg K) (x : B.A), ∀ t ∈ B.T, ∀ L ∈ B.X x, mulLat K.O (t : B.A) L ∈ B.X x := by
  first | exact @GlobalTheory.UnitLemma.TorusAction.torus_mem_X | exact GlobalTheory.UnitLemma.TorusAction.torus_mem_X | (intros; apply GlobalTheory.UnitLemma.TorusAction.torus_mem_X <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualStableLatticeUnitOrbitsFinite

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

noncomputable section

namespace GlobalTheory.UnitLemma.OrbitFinite

theorem orbits_finite : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → Finite (Orb K.O B.T (B.X x)) ∧ ∀ L ∈ B.X x, stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  intro K B hsep x hxu hxσ
  by_cases h0 : ∃ L0, L0 ∈ B.X x
  swap
  · push_neg at h0
    haveI : IsEmpty (B.X x) := ⟨fun L => h0 L.1 L.2⟩
    refine ⟨?_, fun L hL => absurd hL (h0 L)⟩
    unfold Orb
    infer_instance
  obtain ⟨L0, hL0⟩ := h0
  have hgi : IsIntegral K.O B.g := isIntegral_of_isLat_stable L0 hL0.1 B.g hL0.2.1
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.exists_conductor_mul_mem_adjoin_of_separable K B hsep hgi

  have hadj : ∀ L ∈ B.X x, ∀ a ∈ Algebra.adjoin K.O ({B.g} : Set B.A), ∀ y ∈ L, a * y ∈ L := by
    intro L hL a ha
    induction ha using Algebra.adjoin_induction with
    | mem a h =>
      rw [Set.mem_singleton_iff] at h
      subst h
      exact hL.2.1
    | algebraMap r =>
      intro y hy
      rw [← Algebra.smul_def]
      exact L.smul_mem r hy
    | add a b _ _ ha hb =>
      intro y hy
      rw [add_mul]
      exact L.add_mem (ha y hy) (hb y hy)
    | mul a b _ _ ha hb =>
      intro y hy
      rw [mul_assoc]
      exact ha _ (hb y hy)
  have hcL : ∀ L ∈ B.X x, ∀ u : B.A, IsIntegral K.O u → ∀ y ∈ L, algebraMap K.O B.A c * u * y ∈ L :=
    fun L hL u hu y hy => hadj L hL _ (hc u hu) y hy
  refine ⟨?_, ?_⟩
  · obtain ⟨S, hSf, hSl, hS⟩ := GlobalTheory.T.finite_selfDualIntegral_hermitianLattices_modUnits K B hsep x hxu hxσ c hc0
    set W : Set (Submodule K.O B.A) :=
      (⋃ J ∈ S, {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) J ≤ M ∧ M ≤ J}) ∩ B.X x with hW
    have hWf : W.Finite :=
      (hSf.biUnion fun J hJ => GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice K B J (hSl J hJ) c hc0).subset Set.inter_subset_left
    haveI : Finite W := hWf.to_subtype
    let f : W → Orb K.O B.T (B.X x) := fun M => Quot.mk _ ⟨M.1, M.2.2⟩
    apply Finite.of_surjective f
    intro o
    set L := (Quot.out o).1 with hLdef
    have hL : L ∈ B.X x := (Quot.out o).2
    obtain ⟨J, hJl, hJs, hJ1, hJ2, hJc, hLJ⟩ := GlobalTheory.T.exists_maximalOrder_hull_selfDual_stable_lattice K B x c hc0 L hL (hcL L hL)
    obtain ⟨t, ht, htS⟩ := hS J hJl hJs hJ1 hJ2
    have hcomm : mulLat K.O (algebraMap K.O B.A c) (mulLat K.O (t : B.A) J) =
        mulLat K.O (t : B.A) (mulLat K.O (algebraMap K.O B.A c) J) := by
      unfold mulLat
      rw [← Submodule.map_comp, ← Submodule.map_comp]
      congr 1
      ext y
      simp [mul_left_comm]
    have hmem : mulLat K.O (t : B.A) L ∈ W := by
      refine ⟨Set.mem_biUnion htS ⟨?_, Submodule.map_mono hLJ⟩, GlobalTheory.T.torus_submoduleMulLeftImage_mem_selfDualStableLattices K B x t ht L hL⟩
      rw [hcomm]
      exact Submodule.map_mono hJc
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [← Quot.out_eq o]
    exact (Quot.sound ⟨t, ht, rfl⟩).symm
  · intro L hL
    refine ⟨?_, GlobalTheory.T.relIndex_unitStabilizer_integralUnits_ne_zero K B L hL.1 c hc0 (hcL L hL)⟩
    rintro t ⟨hs, -⟩
    refine ⟨isIntegral_of_isLat_stable L hL.1 (t : B.A) fun y hy => (hs y).mp hy, ?_⟩
    refine isIntegral_of_isLat_stable L hL.1 _ fun y hy => (hs _).mpr ?_
    rw [← mul_assoc, Units.mul_inv, one_mul]
    exact hy

end GlobalTheory.UnitLemma.OrbitFinite
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualStableLatticeUnitOrbitsFiniteStatement

section

@[expose] public section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.selfDual_stable_lattice_unit_orbits_finite : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ x : B.A, IsUnit x → B.σ x = x → Finite (Orb K.O B.T (B.X x)) ∧ ∀ L ∈ B.X x, stabLat K.O L ⊓ B.T ≤ intUnits K.O B.A ∧ (stabLat K.O L ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) ≠ 0 := by
  first | exact @GlobalTheory.UnitLemma.OrbitFinite.orbits_finite | exact GlobalTheory.UnitLemma.OrbitFinite.orbits_finite | (intros; apply GlobalTheory.UnitLemma.OrbitFinite.orbits_finite <;> assumption)
end
end
