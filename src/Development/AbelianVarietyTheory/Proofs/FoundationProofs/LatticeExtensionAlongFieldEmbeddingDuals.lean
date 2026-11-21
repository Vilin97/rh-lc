module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
public import Formalism.GradedWeylDivisibility.StatementE
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.ProdFormula
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

@[expose] public section

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

namespace GlobalTheory.TauLat

theorem mem_one_iff {K : Type} [Field K] (x : K) : x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨y, rfl⟩
    exact y.isIntegral_coe
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

theorem mem_range_iff {K : Type} [Field K] (x : K) : x ∈ (algebraMap (𝓞 K) K).range ↔ IsIntegral ℤ x := by
  rw [← mem_one_iff, Submodule.mem_one]
  rfl

theorem integral_map {E K : Type} [Field E] [Field K] (f : E →+* K) {x : E} (h : IsIntegral ℤ x) :
    IsIntegral ℤ (f x) := map_isIntegral_int f h

theorem smul_mem_of_integral {K : Type} [Field K] {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) {c : K}
    (hc : IsIntegral ℤ c) {v : Fin n → K} (hv : v ∈ M) : c • v ∈ M :=
  M.smul_mem (⟨c, hc⟩ : 𝓞 K) hv

theorem isLocalizedModule_subtype {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsFullLattice E L) : IsLocalizedModule (nonZeroDivisors (𝓞 E)) L.subtype := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    have := isLocalizedModule_id (nonZeroDivisors (𝓞 E)) (Fin n → E) E
    exact IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E))
      (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E)) s
  · intro y
    have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
    obtain ⟨s, hs⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E (L : Set (Fin n → E)) y hy
    rw [Submodule.span_eq] at hs
    exact ⟨(⟨_, hs⟩, s), rfl⟩
  · intro x₁ x₂ h
    exact ⟨1, by rw [Subtype.ext h]⟩

theorem exists_dual_family {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsFullLattice E L) :
    ∃ (m : ℕ) (x φ : Fin m → Fin n → E), (∀ i, x i ∈ L) ∧ (∀ i, ∀ y ∈ L, IsIntegral ℤ (φ i ⬝ᵥ y)) ∧
      ∀ a b, ∑ i, x i a * φ i b = if a = b then 1 else 0 := by
  have : Module.Finite (𝓞 E) L := Submodule.IsLattice.finite E L
  have : Module.FinitePresentation (𝓞 E) L := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 E) L := Module.Flat.projective_of_finitePresentation
  have := isLocalizedModule_subtype L hL
  obtain ⟨m, π, hπ⟩ := Module.Finite.exists_fin' (𝓞 E) L
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hu : ∀ x : nonZeroDivisors (𝓞 E), IsUnit (algebraMap (𝓞 E) (Module.End (𝓞 E) E) x) :=
    fun x => IsLocalizedModule.map_units (S := nonZeroDivisors (𝓞 E)) (Algebra.linearMap (𝓞 E) E) x
  let f : Fin m → (Fin n → E) →ₗ[E] E := fun i =>
    LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors (𝓞 E)) E
      (IsLocalizedModule.lift (nonZeroDivisors (𝓞 E)) L.subtype
        (Algebra.linearMap (𝓞 E) E ∘ₗ LinearMap.proj i ∘ₗ s) hu)
  have hf : ∀ i (y : L), f i y = algebraMap (𝓞 E) E (s y i) := fun i y =>
    IsLocalizedModule.lift_apply (nonZeroDivisors (𝓞 E)) L.subtype _ hu y
  let x : Fin m → Fin n → E := fun i => (π (Pi.single i 1) : L)
  have hdot : ∀ i y, (fun b => f i (Pi.single b 1)) ⬝ᵥ y = f i y := by
    intro i y
    conv_rhs => rw [pi_eq_sum_univ' y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, dotProduct, mul_comm]
  have key : ∀ y, ∑ i, f i y • x i = y := by
    have : (∑ i, (f i).smulRight (x i)) = LinearMap.id := by
      apply LinearMap.ext_on hL.span_eq_top
      intro y hy
      have h1 : π (s ⟨y, hy⟩) = ⟨y, hy⟩ := LinearMap.congr_fun hs ⟨y, hy⟩
      have h2 : (π (s ⟨y, hy⟩) : Fin n → E) = y := by rw [h1]
      rw [pi_eq_sum_univ' (s ⟨y, hy⟩)] at h2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul] at h2
      simp only [LinearMap.sum_apply, LinearMap.smulRight_apply, LinearMap.id_apply]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h2
      rw [hf i ⟨y, hy⟩, algebraMap_smul]
    intro y
    simpa using LinearMap.congr_fun this y
  refine ⟨m, x, fun i b => f i (Pi.single b 1), fun i => (π (Pi.single i 1)).2, ?_, ?_⟩
  · intro i y hy
    rw [hdot, hf i ⟨y, hy⟩]
    exact (s ⟨y, hy⟩ i).isIntegral_coe
  · intro a b
    have := congrFun (key (Pi.single b 1)) a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at this
    rw [← this]
    simp only [mul_comm]

theorem expand_left {E K : Type} [Field E] [Field K] (f : E →+* K) {n m : ℕ} {x φ : Fin m → Fin n → E}
    (h : ∀ a b, ∑ i, x i a * φ i b = if a = b then 1 else 0) (v : Fin n → K) :
    v = ∑ i, ((fun a => f (x i a)) ⬝ᵥ v) • fun b => f (φ i b) := by
  funext b
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  have : ∀ a, ∑ i, f (x i a) * v a * f (φ i b) = if a = b then v a else 0 := by
    intro a
    have h1 := congrArg f (h a b)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at h1
    calc _ = v a * ∑ i, f (x i a * φ i b) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul]; ring
      _ = _ := by rw [h1]; split_ifs <;> simp
  simp [this]

theorem expand_right {E K : Type} [Field E] [Field K] (f : E →+* K) {n m : ℕ} {x φ : Fin m → Fin n → E}
    (h : ∀ a b, ∑ i, x i a * φ i b = if a = b then 1 else 0) (v : Fin n → K) :
    v = ∑ i, ((fun a => f (φ i a)) ⬝ᵥ v) • fun b => f (x i b) := by
  apply expand_left
  intro a b
  simp only [mul_comm (φ _ a), h, eq_comm]

theorem map_dot {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ} (u v : Fin n → E) :
    f (u ⬝ᵥ v) = (fun a => f (u a)) ⬝ᵥ fun a => f (v a) := by
  simp [dotProduct]

theorem map_mulVec {E K : Type} [Field E] [Field K] (f : E →+* K) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (fun a => f ((J *ᵥ v) a)) = J.map f *ᵥ fun a => f (v a) := by
  funext a
  simp [Matrix.mulVec, dotProduct]

theorem hform_eq {E : Type} [Field E] {n : ℕ} (c : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    Formalism.UG.hform c J x y = (fun a => c (x a)) ⬝ᵥ (J *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem tauLatLattice : TauLatLattice := tauLatticeLattice_holds

theorem tauLatDual : TauLatDual := tauLatticeDual_holds

theorem roundLat : RoundLat := roundLattice_holds

theorem tauLat_lattice_dual_round : TauLatLattice ∧ TauLatDual ∧ RoundLat := ⟨tauLatLattice, tauLatDual, roundLat⟩

end GlobalTheory.TauLat
