module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixRelatingIntegralVectorZBases

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo

theorem exists_integralMatrix_of_same_multiplicationMatrices {E : Type*} [Field E] [NumberField E] {n N : ℕ}
    (e e₀ : Fin N → Fin n → E) (hli : LinearIndependent ℤ e)
    (he : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e i)
    (he₀ : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) ↔ ∃ z : Fin N → ℤ, u = ∑ i, z i • e₀ i)
    (h : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis E k : E) • e j = ∑ i, z i • e i → (integralBasis E k : E) • e₀ j = ∑ i, z i • e₀ i) :
    ∃ M : Matrix (Fin n) (Fin n) E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j := by
  classical
  let A : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e
  let B : (Fin N → ℤ) →ₗ[ℤ] (Fin n → E) := Fintype.linearCombination ℤ e₀
  have hA : ∀ z, A z = ∑ i, z i • e i := fun z => Fintype.linearCombination_apply ℤ e z
  have hB : ∀ z, B z = ∑ i, z i • e₀ i := fun z => Fintype.linearCombination_apply ℤ e₀ z
  have hAs : ∀ j, A (Pi.single j 1) = e j := fun j => by simp [A]
  have hBs : ∀ j, B (Pi.single j 1) = e₀ j := fun j => by simp [B]
  have hAinj : Function.Injective A := by
    refine (injective_iff_map_eq_zero A).2 fun z hz => ?_
    rw [hA] at hz
    exact funext (Fintype.linearIndependent_iff.1 hli z hz)
  have heint : ∀ j i, IsIntegral ℤ (e j i) := fun j => (he _).2 ⟨Pi.single j 1, by rw [← hA, hAs]⟩
  let S : Submodule ℤ ((Fin n → E) × (Fin n → E)) := LinearMap.range (A.prod B)
  have hk : ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (z : Fin N → ℤ),
      (integralBasis E k : E) • (A z, B z) ∈ S := by
    intro k z
    have h1 : (integralBasis E k : E) • (A z, B z)
        = ∑ j, z j • ((integralBasis E k : E) • (e j, e₀ j)) := by
      have h0 : (A z, B z) = ∑ j, z j • (e j, e₀ j) := by
        refine Prod.ext ?_ ?_
        · rw [Prod.fst_sum]; exact hA z
        · rw [Prod.snd_sum]; exact hB z
      rw [h0, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_comm (z j)]
    rw [h1]
    refine S.sum_mem fun j _ => S.smul_mem _ ?_
    have hint : ∀ i, IsIntegral ℤ (((integralBasis E k : E) • e j) i) := fun i => by
      rw [Pi.smul_apply, smul_eq_mul, integralBasis_apply]
      exact (RingOfIntegers.isIntegral_coe _).mul (heint j i)
    obtain ⟨w, hw⟩ := (he _).1 hint
    refine ⟨w, ?_⟩
    have hw₀ := h k j w hw
    rw [← hA] at hw
    rw [← hB] at hw₀
    exact Prod.ext hw.symm hw₀.symm
  have ha : ∀ a : E, IsIntegral ℤ a → ∀ z : Fin N → ℤ, a • (A z, B z) ∈ S := by
    intro a hai z
    let a' : 𝓞 E := ⟨a, hai⟩
    have h1 : a = ∑ k, (RingOfIntegers.basis E).repr a' k • (integralBasis E k : E) := by
      have h2 := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr a')

      rw [map_sum] at h2
      simp only [map_zsmul] at h2
      simp only [integralBasis_apply]
      exact h2.symm
    rw [h1, Finset.sum_smul]
    refine S.sum_mem fun k _ => ?_
    rw [smul_assoc]
    exact S.smul_mem _ (hk k z)
  have hu : ∀ j : Fin n, ∃ z : Fin N → ℤ, (Pi.single j 1 : Fin n → E) = A z := fun j => by
    obtain ⟨z, hz⟩ := (he (Pi.single j 1)).1 fun i => by
      by_cases hij : i = j
      · subst hij; simpa using isIntegral_one
      · simpa [hij] using isIntegral_zero
    exact ⟨z, by rw [hA]; exact hz⟩
  choose c hc using hu
  refine ⟨Matrix.of fun i j => B (c j) i, fun i j => (he₀ _).2 ⟨c j, hB _⟩ i, fun l => ?_⟩
  have hs : ∑ j, e l j • (A (c j), B (c j)) ∈ S := S.sum_mem fun j _ => ha _ (heint l j) _
  obtain ⟨w, hw⟩ := hs
  have hw1 : A w = e l := by
    have h1 := congrArg Prod.fst hw
    rw [Prod.fst_sum] at h1
    simp only [Prod.smul_mk, ← hc] at h1
    refine Eq.trans h1 ?_
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hw2 : B w = ∑ j, e l j • B (c j) := by
    have h1 := congrArg Prod.snd hw
    rw [Prod.snd_sum] at h1
    exact h1
  have hw3 : w = Pi.single l 1 := hAinj (by rw [hw1, hAs])
  rw [← hBs, ← hw3, hw2]
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem exists_integral_matrix_of_same_mul : ∀ (I : AutInst) {N : ℕ} (e e₀ : Fin N → Fin I.n → I.E),
    IsZBasis I e → IsZBasis I e₀ →
    (∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i → (integralBasis I.E k : I.E) • e₀ j = ∑ i, z i • e₀ i) →
    ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j :=
  fun _ _ e e₀ he he₀ h => exists_integralMatrix_of_same_multiplicationMatrices e e₀ he.1 he.2 he₀.2 h

end GlobalTheory.CuspGeo
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralMatrixRelatingIntegralVectorZBasesStatement

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

theorem _root_.GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases : ∀ (I : AutInst) {N : ℕ} (e e₀ : Fin N → Fin I.n → I.E), IsZBasis I e → IsZBasis I e₀ →
    (∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (z : Fin N → ℤ),
      (integralBasis I.E k : I.E) • e j = ∑ i, z i • e i → (integralBasis I.E k : I.E) • e₀ j = ∑ i, z i • e₀ i) →
    ∃ M : Matrix (Fin I.n) (Fin I.n) I.E, (∀ i j, IsIntegral ℤ (M i j)) ∧ ∀ j, M *ᵥ e j = e₀ j := by
  first | exact @GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul | exact GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul | (intros; apply GlobalTheory.CuspGeo.exists_integral_matrix_of_same_mul <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryOfPreservesHermitianTraceFormIntegralBasi

section

@[expose] public section

noncomputable section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo.TraceUnitary

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def trBil (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) : (Fin n → E) →ₗ[ℚ] (Fin n → E) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun x y => Algebra.trace ℚ E (Formalism.UG.hform σ J x y))
    (fun x x' y => by
      rw [← map_add (f := _)]; congr 1
      simp [Formalism.UG.hform, add_mul, Finset.sum_add_distrib])
    (fun c x y => by
      rw [← map_smul]; congr 1
      simp [Formalism.UG.hform, Finset.smul_sum, Rat.smul_def, mul_assoc])
    (fun x y y' => by
      rw [← map_add (f := _)]; congr 1
      simp [Formalism.UG.hform, mul_add, Finset.sum_add_distrib])
    (fun c x y => by
      rw [← map_smul]; congr 1
      simp only [Formalism.UG.hform, Finset.smul_sum, Rat.smul_def, Pi.smul_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)

theorem trBil_apply (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    trBil σ J x y = Algebra.trace ℚ E (Formalism.UG.hform σ J x y) := rfl

omit [NumberField E] in
theorem hform_smul_right (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (a : E) :
    Formalism.UG.hform σ J x (a • y) = a * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem span_eq_top {N : ℕ} (e : Fin N → Fin n → E)
    (h : ∀ u : Fin n → E, (∀ i, IsIntegral ℤ (u i)) → ∃ z : Fin N → ℤ, u = ∑ i, z i • e i) :
    Submodule.span ℚ (Set.range e) = ⊤ := by
  classical
  rw [eq_top_iff]
  intro u _
  obtain ⟨d, hd, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image u)
  obtain ⟨z, hz⟩ := h (d • u) (fun i => hint (u i) (Finset.mem_image_of_mem u (Finset.mem_univ i)))
  have h1 : (d : ℚ) • u ∈ Submodule.span ℚ (Set.range e) := by
    rw [Int.cast_smul_eq_zsmul, hz]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hd' : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  exact (Submodule.smul_mem_iff _ hd').1 h1

theorem unitary_of_trace (σ : E →+* E) (J M : Matrix (Fin n) (Fin n) E) {N : ℕ} (e : Fin N → Fin n → E)
    (hs : Submodule.span ℚ (Set.range e) = ⊤)
    (h : ∀ i j, trBil σ J (M *ᵥ e i) (M *ᵥ e j) = trBil σ J (e i) (e j)) :
    Formalism.UG.cT σ M * J * M = J := by
  classical
  let f : (Fin n → E) →ₗ[ℚ] (Fin n → E) := (Matrix.mulVecLin M).restrictScalars ℚ
  have hB : (trBil σ J).compl₁₂ f f = trBil σ J := by
    refine LinearMap.ext_on_range hs fun i => LinearMap.ext_on_range hs fun j => ?_
    simpa [f] using h i j
  have hB' : ∀ x y, trBil σ J (M *ᵥ x) (M *ᵥ y) = trBil σ J x y := fun x y => by
    have := LinearMap.congr_fun₂ hB x y
    simpa [f] using this
  have hh : ∀ x y, Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := fun x y => by
    by_contra hne
    have hD : Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) - Formalism.UG.hform σ J x y ≠ 0 := sub_ne_zero.2 hne
    have h1 := hB' x ((Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) - Formalism.UG.hform σ J x y)⁻¹ • y)
    rw [Matrix.mulVec_smul, trBil_apply, trBil_apply, hform_smul_right, hform_smul_right, ← sub_eq_zero,
      ← map_sub, ← mul_sub, inv_mul_cancel₀ hD, ← (algebraMap ℚ E).map_one, Algebra.trace_algebraMap] at h1
    have : Module.finrank ℚ E ≠ 0 := Module.finrank_pos.ne'
    simp [this] at h1
  ext i j
  have := hh (Pi.single i 1) (Pi.single j 1)
  simp only [Formalism.UG.hform, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm, this]
  simp [apply_ite σ]

end GlobalTheory.CuspGeo.TraceUnitary

namespace GlobalTheory.CuspGeo

theorem unitary_of_trForm_zBasis (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E)
    (M : Matrix (Fin I.n) (Fin I.n) I.E) (he : IsZBasis I e)
    (h : ∀ i j, trForm I (M *ᵥ e i) (M *ᵥ e j) = trForm I (e i) (e j)) :
    Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J :=
  TraceUnitary.unitary_of_trace _ _ _ e (TraceUnitary.span_eq_top e fun u hu => (he.2 u).1 hu) h

end GlobalTheory.CuspGeo

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryOfPreservesHermitianTraceFormIntegralBasiStatement

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo

theorem _root_.GlobalTheory.T.unitary_of_preserves_hermitianTraceForm_integralBasis : ∀ (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E) (M : Matrix (Fin I.n) (Fin I.n) I.E), IsZBasis I e →
    (∀ i j, trForm I (M *ᵥ e i) (M *ᵥ e j) = trForm I (e i) (e j)) →
    Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J := by
  first | exact @GlobalTheory.CuspGeo.unitary_of_trForm_zBasis | exact GlobalTheory.CuspGeo.unitary_of_trForm_zBasis | (intros; apply GlobalTheory.CuspGeo.unitary_of_trForm_zBasis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralVectorBasesBoundedFiniteUnitaryClasses

section

@[expose] public section

open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

namespace GlobalTheory.BasesFin

theorem trForm_denom : ∀ (I : AutInst), ∃ c : ℕ, 0 < c ∧ ∀ x y : Fin I.n → I.E, IntVec I x → IntVec I y →
    ∃ m : ℤ, (c : ℚ) * trForm I x y = m := by
  intro I
  classical
  obtain ⟨y, hy0, hyi⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun p : Fin I.n × Fin I.n => I.J p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  have hcJ : ∀ a b, IsIntegral ℤ ((y.natAbs : I.E) * I.J a b) := by
    intro a b
    have h := hyi (I.J a b) (Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩)
    rw [zsmul_eq_mul] at h
    rcases Int.natAbs_eq y with hy | hy
    · rw [hy] at h; simpa using h
    · rw [hy] at h
      have := h.neg
      simpa [neg_mul] using this
  intro x z hx hz
  have hint : IsIntegral ℤ ((y.natAbs : I.E) * Formalism.UG.hform (starRingEnd I.E) I.J x z) := by
    unfold Formalism.UG.hform
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine IsIntegral.sum _ fun j _ => ?_
    have : (y.natAbs : I.E) * ((starRingEnd I.E) (x i) * I.J i j * z j)
        = (starRingEnd I.E) (x i) * ((y.natAbs : I.E) * I.J i j) * z j := by ring
    rw [this]
    have hs : IsIntegral ℤ ((starRingEnd I.E) (x i)) := (hx i).map (starRingEnd I.E).toIntAlgHom
    exact (hs.mul (hcJ i j)).mul (hz j)
  have htr := Algebra.isIntegral_trace (R := ℤ) (L := ℚ) hint
  obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp htr
  refine ⟨m, ?_⟩
  rw [eq_intCast] at hm
  rw [hm]
  unfold trForm
  rw [← map_natCast (algebraMap ℚ I.E), ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem fix_one (I : AutInst) {N : ℕ} (e : Fin N → Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I.n) I.E)
    (he : IsZBasis I e) (hA : ∀ j, A *ᵥ e j = e j) : A = 1 := by
  have key : ∀ u, IntVec I u → A *ᵥ u = u := by
    intro u hu
    obtain ⟨z, rfl⟩ := (he.2 u).1 hu
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, hA]
  ext i j
  have hs : IntVec I (Pi.single j 1) := by
    intro l
    by_cases h : l = j
    · subst h; simpa using isIntegral_one
    · simp [Pi.single_apply, h, isIntegral_zero]
  have := congrFun (key _ hs) i
  rw [Matrix.mulVec_single_one] at this
  simpa [Matrix.col, Matrix.one_apply, Pi.single_apply, eq_comm] using this

theorem bases_finite_classes : ∀ (I : AutInst) (N : ℕ) (R : ℝ), ∃ S : Set (Fin N → Fin I.n → I.E), S.Finite ∧ (∀ e₀ ∈ S, IsZBasis I e₀) ∧ ∀ e : Fin N → Fin I.n → I.E, IsZBasis I e → BddType I R e → ∃ e₀ ∈ S, ∃ γ : GL (Fin I.n) I.E, γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J ∧ (∀ i j, IsIntegral ℤ ((γ : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ (∀ i j, IsIntegral ℤ (((γ⁻¹ : GL (Fin I.n) I.E) : Matrix (Fin I.n) (Fin I.n) I.E) i j)) ∧ ∀ j, (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ e j = e₀ j := by
  intro I N R
  classical
  obtain ⟨c, hc0, hc⟩ := trForm_denom I
  let T := (Module.Free.ChooseBasisIndex ℤ (𝓞 I.E) → Fin N → Fin N → ℤ) × (Fin N → Fin N → ℚ)
  let has : (Fin N → Fin I.n → I.E) → T → Prop := fun e t =>
    (∀ k j, (integralBasis I.E k : I.E) • e j = ∑ i, t.1 k j i • e i) ∧ ∀ i j, trForm I (e i) (e j) = t.2 i j
  let A : Set T := (Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => {z : ℤ | |(z:ℝ)| ≤ R}) ×ˢ
    (Set.univ.pi fun _ => Set.univ.pi fun _ => {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m})
  have hZ : {z : ℤ | |(z:ℝ)| ≤ R}.Finite := by
    refine (Set.finite_Icc (-⌈R⌉) ⌈R⌉).subset fun z hz => ?_
    simp only [Set.mem_setOf_eq] at hz
    have h := abs_le.mp hz
    have hR := Int.le_ceil R
    constructor
    · have : (-(⌈R⌉:ℝ)) ≤ z := by linarith
      exact_mod_cast this
    · have : (z:ℝ) ≤ ⌈R⌉ := by linarith
      exact_mod_cast this
  have hQ : {q : ℚ | |(q:ℝ)| ≤ R ∧ ∃ m : ℤ, (c:ℚ) * q = m}.Finite := by
    refine ((Set.finite_Icc (-⌈R * c⌉) ⌈R * c⌉).image fun m : ℤ => (m : ℚ) / c).subset ?_
    rintro q ⟨hq, m, hm⟩
    have hcpos : (0:ℝ) < c := by exact_mod_cast hc0
    have hmq : (m:ℝ) = c * q := by exact_mod_cast hm.symm
    have h := abs_le.mp hq
    have hR := Int.le_ceil (R * c)
    refine ⟨m, ⟨?_, ?_⟩, ?_⟩
    · have : (-(⌈R*c⌉:ℝ)) ≤ m := by rw [hmq]; nlinarith
      exact_mod_cast this
    · have : (m:ℝ) ≤ ⌈R*c⌉ := by rw [hmq]; nlinarith
      exact_mod_cast this
    · have hc' : (c:ℚ) ≠ 0 := by exact_mod_cast hc0.ne'
      simp only
      rw [← hm]; field_simp
  have hA : A.Finite := (Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.Finite.pi fun _ => hZ).prod
    (Set.Finite.pi fun _ => Set.Finite.pi fun _ => hQ)
  let pick : T → (Fin N → Fin I.n → I.E) := fun t =>
    if h : ∃ e, IsZBasis I e ∧ has e t then Classical.choose h else 0
  have hpick : ∀ t (h : ∃ e, IsZBasis I e ∧ has e t), IsZBasis I (pick t) ∧ has (pick t) t := by
    intro t h
    simp only [pick, dif_pos h]
    exact Classical.choose_spec h
  have uniq : ∀ (f : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → ∀ k j (w : Fin N → ℤ),
      (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → w = t.1 k j := by
    intro f t hf hft k j w hw
    rw [hft.1 k j] at hw
    have h0 : ∑ i, (w i - t.1 k j i) • f i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← hw, sub_self]
    funext i
    exact sub_eq_zero.mp (Fintype.linearIndependent_iff.mp hf.1 _ h0 i)
  have compat : ∀ (f g : Fin N → Fin I.n → I.E) (t : T), IsZBasis I f → has f t → has g t →
      ∀ (k : Module.Free.ChooseBasisIndex ℤ (𝓞 I.E)) (j : Fin N) (w : Fin N → ℤ),
      (integralBasis I.E k : I.E) • f j = ∑ i, w i • f i → (integralBasis I.E k : I.E) • g j = ∑ i, w i • g i := by
    intro f g t hf hft hgt k j w hw
    rw [uniq f t hf hft k j w hw]
    exact hgt.1 k j
  refine ⟨pick '' {t ∈ A | ∃ e, IsZBasis I e ∧ has e t}, (hA.subset (Set.sep_subset _ _)).image _, ?_, ?_⟩
  · rintro _ ⟨t, ⟨-, h⟩, rfl⟩
    exact (hpick t h).1
  · intro e he hb
    choose z hz hzb using hb.1
    let t : T := (z, fun i j => trForm I (e i) (e j))
    have ht : has e t := ⟨hz, fun i j => rfl⟩
    have hint : ∀ i, IntVec I (e i) := fun i => (he.2 (e i)).2 ⟨Pi.single i 1, by simp [Pi.single_apply]⟩
    have htA : t ∈ A := ⟨fun k _ j _ i _ => hzb k j i, fun i _ j _ => ⟨hb.2 i j, hc _ _ (hint i) (hint j)⟩⟩
    have hex : ∃ e', IsZBasis I e' ∧ has e' t := ⟨e, he, ht⟩
    obtain ⟨he₀, ht₀⟩ := hpick t hex
    obtain ⟨M, hMi, hMe⟩ := GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases I e (pick t) he he₀ (compat e (pick t) t he ht ht₀)
    obtain ⟨M', hM'i, hM'e⟩ := GlobalTheory.T.exists_integralMatrix_relating_integralVectorZBases I (pick t) e he₀ he (compat (pick t) e t he₀ ht₀ ht)
    have h1 : M' * M = 1 := fix_one I e _ he fun j => by rw [← Matrix.mulVec_mulVec, hMe, hM'e]
    have h2 : M * M' = 1 := (mul_eq_one_comm_of_card_eq (Fin I.n) (Fin I.n) I.E rfl).mp h1
    let γ : GL (Fin I.n) I.E := ⟨M, M', h2, h1⟩
    refine ⟨pick t, ⟨t, ⟨htA, hex⟩, rfl⟩, γ, ?_, hMi, hM'i, hMe⟩
    show Formalism.UG.cT (starRingEnd I.E) M * I.J * M = I.J
    exact GlobalTheory.T.unitary_of_preserves_hermitianTraceForm_integralBasis I e M he fun i j => by rw [hMe, hMe]; exact ht₀.2 i j

end GlobalTheory.BasesFin
end
end
