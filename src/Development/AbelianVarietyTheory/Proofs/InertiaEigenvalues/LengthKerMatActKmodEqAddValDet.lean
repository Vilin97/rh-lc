module

public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelLengthSpanEqAddValDet

section

@[expose] public section

namespace GlobalTheory.RelativeLengthSpanDet

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] in
theorem addVal_prod (s : Finset ι) (c : ι → R) :
    addVal R (∏ i ∈ s, c i) = ∑ i ∈ s, addVal R (c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]

theorem length_self_eq_top : Module.length R R = ⊤ := by
  by_contra h
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at h
  have : IsArtinianRing R := h.2
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem length_coker_of_det_eq_zero (P : Matrix ι ι R) (h : P.det = 0) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = ⊤ := by
  obtain ⟨w, hw, hwP⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hw
  have hk' : w k ≠ 0 := hk
  let g : R →ₗ[R] (ι → R) ⧸ LinearMap.range P.mulVecLin :=
    (LinearMap.range P.mulVecLin).mkQ ∘ₗ LinearMap.single R (fun _ : ι => R) k
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    have hr' : (Pi.single k r : ι → R) ∈ LinearMap.range P.mulVecLin :=
      (Submodule.Quotient.mk_eq_zero _).mp hr
    obtain ⟨x, hx⟩ := hr'
    have h1 : w ⬝ᵥ P.mulVec x = 0 := by
      rw [Matrix.dotProduct_mulVec, hwP, zero_dotProduct]
    rw [Matrix.mulVecLin_apply] at hx
    rw [hx, dotProduct_single] at h1
    exact (mul_eq_zero.mp h1).resolve_left hk'
  exact top_le_iff.mp (length_self_eq_top (R := R) ▸ Module.length_le_of_injective g hg)

theorem length_coker_of_injective {M : Type*} [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  have hr : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hf
  set c := Submodule.smithNormalFormCoeffs b hr with hc
  set bt := Submodule.smithNormalFormTopBasis b hr with hbt
  set bb := Submodule.smithNormalFormBotBasis b hr with hbb
  have hdef : ∀ i, (bb i : M) = c i • bt i := Submodule.smithNormalFormBotBasis_def b hr
  have h1 : Module.length R (M ⧸ LinearMap.range f) = ∑ i, addVal R (c i) := by
    rw [(Submodule.quotientEquivPiSpan _ b hr).length_eq, Module.length_pi_of_fintype]
    exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (c i)
  have h2 := LinearMap.associated_det_comp_equiv (LinearMap.range f).subtype
    (LinearEquiv.ofInjective f hf) (bt.equiv bb (Equiv.refl ι))
  have h3 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf : M →ₗ[R] _) = f := by
    ext x
    rfl
  have h4 : LinearMap.det ((LinearMap.range f).subtype ∘ₗ
      (bt.equiv bb (Equiv.refl ι) : M →ₗ[R] LinearMap.range f)) = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix bt, ← Matrix.det_diagonal]
    congr 1
    ext i j
    rw [LinearMap.toMatrix_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
      Equiv.refl_apply, Submodule.subtype_apply, hdef, map_smul, Module.Basis.repr_self,
      Finsupp.smul_apply, Finsupp.single_apply, Matrix.diagonal_apply, smul_eq_mul]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij, Ne.symm hij]
  rw [h3, h4] at h2
  rw [h1, (addVal_eq_iff_associated _ _).mpr h2, addVal_prod]

theorem length_coker (P : Matrix ι ι R) :
    Module.length R ((ι → R) ⧸ LinearMap.range P.mulVecLin) = addVal R P.det := by
  by_cases h : P.det = 0
  · rw [length_coker_of_det_eq_zero P h, h, addVal_zero]
  · have hinj : Function.Injective P.mulVecLin := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro x hx
      by_contra hx0
      exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨x, hx0, hx⟩)
    rw [length_coker_of_injective (Pi.basisFun R ι) _ hinj, ← Matrix.toLin'_apply',
      LinearMap.det_toLin']

end GlobalTheory.RelativeLengthSpanDet
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthKerMatActKmodEqAddValDet

section

@[expose] public section

namespace GlobalTheory

open Formalism.MainNotions.BlochKatoReduction Formalism.BasicNotions

theorem matAct_comp_linear {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (f : M →ₗ[R] N)
    (v : Fin n → M) : matAct (M := N) A (fun i => f (v i)) = fun i => f (matAct (M := M) A v i) := by
  funext i

  simp [matAct, map_sum, map_smul]

theorem matAct_self_apply {R : Type*} [CommRing R] {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (v : Fin n → R) : matAct (M := R) A v = A.mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct]

private theorem matAct_fractionRing {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (v : Fin n → FractionRing O) :
    matAct (M := FractionRing O) A v = (A.map (algebraMap O (FractionRing O))).mulVec v := by
  funext i
  simp [matAct, Matrix.mulVec, dotProduct, Algebra.smul_def]

theorem matAct_fraction_bijective {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (h : A.det ≠ 0) :
    Function.Bijective (matAct (M := FractionRing O) A) := by
  set B := A.map (algebraMap O (FractionRing O)) with hB
  have hd : B.det = algebraMap O (FractionRing O) A.det := by
    rw [hB, RingHom.map_det]; rfl
  have hU : IsUnit B := by
    rw [Matrix.isUnit_iff_isUnit_det, hd, isUnit_iff_ne_zero]
    exact (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr h
  have hf : ⇑(matAct (M := FractionRing O) A) = B.mulVec := funext (matAct_fractionRing A)
  rw [hf]
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr hU, Matrix.mulVec_surjective_iff_isUnit.mpr hU⟩

theorem nonempty_coker_equiv_ker_matAct {O : Type} [CommRing O] [IsDomain O] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) O) (h : A.det ≠ 0) :
    Nonempty (((Fin n → O) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[O]
      LinearMap.ker (matAct (M := KmodO O) A)) := by
  classical
  let ι : (Fin n → O) →ₗ[O] (Fin n → FractionRing O) :=
    (Algebra.linearMap O (FractionRing O)).compLeft (Fin n)
  let π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O) :=
    (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)
  let e : (Fin n → FractionRing O) ≃ₗ[O] (Fin n → FractionRing O) :=
    LinearEquiv.ofBijective (matAct (M := FractionRing O) A) (matAct_fraction_bijective A h)
  have he : ∀ x, e x = matAct (M := FractionRing O) A x := fun x => rfl
  have hAι : ∀ y, matAct (M := FractionRing O) A (ι y) = ι (A.mulVec y) := by
    intro y
    have key := matAct_comp_linear A (Algebra.linearMap O (FractionRing O)) y
    rw [matAct_self_apply] at key
    exact key
  have hAπ : ∀ x, matAct (M := KmodO O) A (π x) = π (matAct (M := FractionRing O) A x) :=
    fun x => matAct_comp_linear A (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ x
  have hπι : ∀ y, π (ι y) = 0 := by
    intro y
    funext i
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨y i, rfl⟩
  have hιinj : Function.Injective ι := by
    intro a b hab
    funext i
    exact IsFractionRing.injective O (FractionRing O) (congrFun hab i)
  have hlift : ∀ x, π x = 0 → ∃ y, ι y = x := by
    intro x hx
    have hmem : ∀ i, ∃ a : O, algebraMap O (FractionRing O) a = x i := by
      intro i
      obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 (congrFun hx i)
      exact ⟨a, ha⟩
    choose y hy using hmem
    exact ⟨y, funext hy⟩
  let φ0 : (Fin n → O) →ₗ[O] (Fin n → KmodO O) := π ∘ₗ e.symm.toLinearMap ∘ₗ ι
  have hφ0 : ∀ y, φ0 y ∈ LinearMap.ker (matAct (M := KmodO O) A) := by
    intro y
    rw [LinearMap.mem_ker]
    show matAct (M := KmodO O) A (π (e.symm (ι y))) = 0
    rw [hAπ, ← he, e.apply_symm_apply, hπι]
  let φ := φ0.codRestrict _ hφ0
  have hφ : ∀ y, (φ y : Fin n → KmodO O) = π (e.symm (ι y)) := fun y => rfl
  have hsurj : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    have hpre : ∀ i, ∃ k : FractionRing O, Submodule.Quotient.mk k = x i :=
      fun i => Submodule.Quotient.mk_surjective _ (x i)
    choose k hk using hpre
    have hπk : π k = x := funext hk
    obtain ⟨y, hy⟩ := hlift (matAct (M := FractionRing O) A k) (by
      rw [← hAπ, hπk]
      exact hx)
    refine ⟨y, Subtype.ext ?_⟩
    rw [hφ, hy, ← he, e.symm_apply_apply, hπk]
  have hkerφ : LinearMap.range A.mulVecLin = LinearMap.ker φ := by
    ext y
    rw [LinearMap.mem_range, LinearMap.mem_ker]
    constructor
    · rintro ⟨z, rfl⟩
      apply Subtype.ext
      rw [hφ, Matrix.mulVecLin_apply, ← hAι, ← he, e.symm_apply_apply, hπι]
      rfl
    · intro hy
      have h0 : π (e.symm (ι y)) = 0 := by
        rw [← hφ, hy]
        rfl
      obtain ⟨z, hz⟩ := hlift _ h0
      refine ⟨z, hιinj ?_⟩
      rw [Matrix.mulVecLin_apply, ← hAι, hz, ← he, e.apply_symm_apply]
  exact ⟨(Submodule.quotEquivOfEq _ _ hkerφ).trans (φ.quotKerEquivOfSurjective hsurj)⟩

theorem length_ker_matAct_eq_top {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {n : ℕ} (A : Matrix (Fin n) (Fin n) O) (h : A.det = 0) :
    Module.length O (LinearMap.ker (matAct (M := KmodO O) A)) = ⊤ := by
  classical
  by_contra hne
  have hfl := Module.length_ne_top_iff.mp hne
  have : IsNoetherian O (LinearMap.ker (matAct (M := KmodO O) A)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hfl).1
  set B := A.map (algebraMap O (FractionRing O)) with hB
  have hd : B.det = 0 := by
    rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h, map_zero]
  obtain ⟨v, hv0, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := by
    by_contra hh
    exact hv0 (funext fun i => by
      by_contra hi
      exact hh ⟨i, hi⟩)
  let π : (Fin n → FractionRing O) →ₗ[O] (Fin n → KmodO O) :=
    (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ.compLeft (Fin n)
  let g0 : FractionRing O →ₗ[O] (Fin n → KmodO O) :=
    π ∘ₗ LinearMap.pi (fun i => LinearMap.mulRight O (v i))
  have hg0 : ∀ t, g0 t = π (t • v) := fun t => rfl
  have hg0mem : ∀ t, g0 t ∈ LinearMap.ker (matAct (M := KmodO O) A) := by
    intro t
    rw [LinearMap.mem_ker, hg0]
    refine (matAct_comp_linear A
      (LinearMap.range (Algebra.linearMap O (FractionRing O))).mkQ (t • v)).trans ?_
    rw [matAct_fractionRing, ← hB, Matrix.mulVec_smul, hBv, smul_zero]
    funext i
    simp
  let g := g0.codRestrict _ hg0mem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : algebraMap O (FractionRing O) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hϖ.ne_zero
  have hle : LinearMap.range g ≤ IsLocalRing.maximalIdeal O • LinearMap.range g := by
    rintro _ ⟨t, rfl⟩
    have ht : t = ϖ • (t / algebraMap O (FractionRing O) ϖ) := by
      rw [Algebra.smul_def]
      field_simp
    rw [ht, map_smul]
    exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit) ⟨_, rfl⟩
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal O)
    (LinearMap.range g) (IsNoetherian.noetherian _) hle (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  set t := (algebraMap O (FractionRing O) ϖ * v i0)⁻¹ with ht
  have hgt : g t = 0 := by
    have hm : g t ∈ LinearMap.range g := ⟨t, rfl⟩
    rw [hbot] at hm
    exact (Submodule.mem_bot O).mp hm
  have hcomp : π (t • v) i0 = 0 := by
    rw [← hg0]
    exact congrFun (congrArg Subtype.val hgt) i0
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero _).1 hcomp
  have ha' : algebraMap O (FractionRing O) a * algebraMap O (FractionRing O) ϖ = 1 := by
    have h1 : algebraMap O (FractionRing O) a = t * v i0 := ha
    rw [h1, ht]
    field_simp
  rw [← map_mul, ← map_one (algebraMap O (FractionRing O))] at ha'
  have hmul : a * ϖ = 1 := IsFractionRing.injective O (FractionRing O) ha'
  have hunit : IsUnit ϖ := ⟨⟨ϖ, a, by rw [mul_comm]; exact hmul, hmul⟩, rfl⟩
  exact hϖ.not_isUnit hunit

theorem length_ker_matAct_kmod_eq_addVal_det :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (a : ℕ)
      (Φ : Matrix (Fin a) (Fin a) O),
      Module.length O (LinearMap.ker (Formalism.MainNotions.BlochKatoReduction.matAct (M := Formalism.BasicNotions.KmodO O) Φ)) =
        IsDiscreteValuationRing.addVal O Φ.det := by
  intro O _ _ _ a Φ
  by_cases h : Φ.det = 0
  · rw [length_ker_matAct_eq_top Φ h, h, IsDiscreteValuationRing.addVal_zero]
  · obtain ⟨e⟩ := nonempty_coker_equiv_ker_matAct Φ h
    rw [← e.length_eq]
    exact RelativeLengthSpanDet.length_coker Φ

end GlobalTheory
end
end
