module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Unramified.Basic
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
public import Mathlib.LinearAlgebra.Determinant
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGFree
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGLam
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGSemi
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Basify
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGTheta
import Mathlib.Algebra.AffineMonoid.Basic

-- Source module: Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RealOfFixedByConjugations

section

@[expose] public section

open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.UnimodularBaseChange

theorem bijective_baseChange :
    ∀ (Z : Type) [CommRing Z] (L : Type) [AddCommGroup L] [Module.Finite ℤ L] [Module.Free ℤ L]
      (B : LinearMap.BilinForm ℤ L), Function.Bijective B →
      Function.Bijective (B.baseChange Z) := by
  intro Z _ L _ _ _ B hB
  classical
  let b := Module.Free.chooseBasis ℤ L
  let c := b.baseChange Z
  have h1 : IsUnit (LinearMap.toMatrix b b.dualBasis B).det :=
    LinearEquiv.isUnit_det (LinearEquiv.ofBijective B hB) b b.dualBasis
  have h2 : LinearMap.toMatrix c c.dualBasis (B.baseChange Z) =
      (algebraMap ℤ Z).mapMatrix (LinearMap.toMatrix b b.dualBasis B) := by
    ext i j
    simp [c, LinearMap.toMatrix_apply, Module.Basis.baseChange_apply]
  have h3 : IsUnit (LinearMap.toMatrix c c.dualBasis (B.baseChange Z)).det := by
    rw [h2, ← RingHom.map_det]
    exact h1.map _
  exact (LinearEquiv.ofIsUnitDet h3).bijective

end GlobalTheory.CompanionTheory.UnimodularBaseChange
end
end

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGHerm

section

@[expose] public section

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_g_herm : ∀ (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R), (∀ r, σ (σ r) = r) → ∀ lam : R →ₗ[Z] Z, (∀ r, lam (σ r) = -lam r) → Function.Bijective (fun r : R => lam.comp (LinearMap.mulLeft Z r)) → ∀ (N : ℕ) (ψ : LinearMap.BilinForm Z (Fin N → R)), (∀ x, ψ x x = 0) → Function.Bijective ψ → (∀ (a : R) x y, ψ (a • x) y = ψ x (σ a • y)) → ∃ A : Matrix (Fin N) (Fin N) R, (A.map σ).transpose = A ∧ IsUnit A.det ∧ ∀ x y, ψ x y = lam (∑ i, ∑ j, x i * A i j * σ (y j)) := by
  intro Z R _ _ _ σ hσ lam hlam hbij N ψ halt hψ hadj
  have hskew : ∀ x y, ψ x y = -ψ y x := fun x y => by
    have := halt (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, halt] at this
    linear_combination this
  have hinj : ∀ a b : R, (∀ r, lam (a * r) = lam (b * r)) → a = b := fun a b h =>
    hbij.1 (LinearMap.ext fun r => h r)
  have hex : ∀ i j : Fin N, ∃ a : R, ∀ r : R, lam (a * r) = ψ (r • Pi.single i 1) (Pi.single j 1) := by
    intro i j
    obtain ⟨a, ha⟩ := hbij.2 ((ψ.flip (Pi.single j 1)).comp
      ((LinearMap.toSpanSingleton R (Fin N → R) (Pi.single i 1)).restrictScalars Z))
    exact ⟨a, fun r => LinearMap.congr_fun ha r⟩
  choose A hA using hex
  have hform : ∀ x y, ψ x y = lam (∑ i, ∑ j, x i * A i j * σ (y j)) := by
    intro x y
    conv_lhs => rw [pi_eq_sum_univ' x, pi_eq_sum_univ' y]

    simp only [map_sum, LinearMap.sum_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h1 := hadj (σ (y j)) (x i • Pi.single i 1) (Pi.single j 1)
    rw [hσ, smul_smul, ← hA] at h1
    rw [← h1]
    congr 1; ring
  refine ⟨Matrix.of A, ?_, ?_, hform⟩
  · ext i j
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply]
    refine hinj _ _ fun r => ?_
    have h1 := hlam (A j i * σ r)
    rw [map_mul, hσ] at h1
    rw [h1, hA, hA, hadj r, hskew (Pi.single i 1)]
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_surjective_iff_isUnit]
    intro w
    let F : (Fin N → R) →ₗ[Z] Z := ∑ j, lam.comp ((LinearMap.mulLeft Z (w j)).comp
      (σ.toLinearMap.comp ((LinearMap.proj j : (Fin N → R) →ₗ[R] R).restrictScalars Z)))
    obtain ⟨x, hx⟩ := hψ.2 F
    refine ⟨x, funext fun j => hinj _ _ fun r => ?_⟩
    have h1 := LinearMap.congr_fun hx (Pi.single j (σ r))
    rw [hform] at h1
    simp only [F, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
      LinearMap.proj_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply] at h1
    have h2 : ∑ d, lam (w d * σ (Pi.single (M := fun _ => R) j (σ r) d)) = lam (w j * r) := by
      rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp),
        Pi.single_eq_same, hσ]
    rw [← h2, ← h1]
    congr 1
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single j (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp),
      Pi.single_eq_same, hσ]

end PositivityTheory.UnitarySelfGeneration
end
end

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGStd

section

@[expose] public section

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

theorem hermitian_form_standard_basis (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R) (hσ : ∀ r, σ (σ r) = r)
    (N : ℕ) (A g : Matrix (Fin N) (Fin N) R) (hg : IsUnit g.det) (h : (g.map σ).transpose * A * g = 1) :
    ∃ φ : (Fin N → R) ≃ₗ[R] (Fin N → R), ∀ x y,
      ∑ i, ∑ j, φ x i * A i j * σ (φ y j) = ∑ i, x i * σ (y i) := by
  have hM : IsUnit (g.map σ).det := by
    have e : σ g.det = (g.map σ).det := AlgHom.map_det σ g
    rw [← e]
    exact hg.map σ
  refine ⟨Matrix.toLinearEquiv' (g.map σ) (Matrix.invertibleOfIsUnitDet (g.map σ) hM), fun x y => ?_⟩
  have hs : (fun j => σ (Matrix.mulVec (g.map σ) y j)) = Matrix.mulVec g (fun k => σ (y k)) := by
    ext j

    simp [Matrix.mulVec, dotProduct, map_sum, map_mul, hσ]
  have key : ∀ u w : Fin N → R, ∑ i, ∑ j, u i * A i j * w j = dotProduct u (Matrix.mulVec A w) := by
    intro u w
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hT : (A * g).transpose * g.map σ = 1 := by
    rw [← Matrix.transpose_transpose (g.map σ), ← Matrix.transpose_mul, ← Matrix.mul_assoc, h,
      Matrix.transpose_one]
  change ∑ i, ∑ j, Matrix.mulVec (g.map σ) x i * A i j * σ (Matrix.mulVec (g.map σ) y j) = _
  rw [key _ (fun j => σ (Matrix.mulVec (g.map σ) y j)), hs, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  simp [dotProduct]

theorem tw_g_std : ∀ (Z R : Type) [CommRing Z] [CommRing R] [Algebra Z R] (σ : R →ₐ[Z] R), (∀ r, σ (σ r) = r) → ∀ lam : R →ₗ[Z] Z, (∀ r, lam (σ r) = -lam r) → Function.Bijective (fun r : R => lam.comp (LinearMap.mulLeft Z r)) → ∀ (N : ℕ), (∀ A : Matrix (Fin N) (Fin N) R, (A.map σ).transpose = A → IsUnit A.det → ∃ g : Matrix (Fin N) (Fin N) R, IsUnit g.det ∧ (g.map σ).transpose * A * g = 1) → ∀ ψ ψ' : LinearMap.BilinForm Z (Fin N → R), (∀ x, ψ x x = 0) → Function.Bijective ψ → (∀ (a : R) x y, ψ (a • x) y = ψ x (σ a • y)) → (∀ x, ψ' x x = 0) → Function.Bijective ψ' → (∀ (a : R) x y, ψ' (a • x) y = ψ' x (σ a • y)) → ∃ φ : (Fin N → R) ≃ₗ[R] (Fin N → R), ∀ x y, ψ' (φ x) (φ y) = ψ x y := by
  intro Z R _ _ _ σ hσ lam hlam hbij N hstd ψ ψ' hψ0 hψb hψs hψ'0 hψ'b hψ's
  obtain ⟨A, hAh, hAu, hAψ⟩ := tw_g_herm Z R σ hσ lam hlam hbij N ψ hψ0 hψb hψs
  obtain ⟨A', hA'h, hA'u, hA'ψ⟩ := tw_g_herm Z R σ hσ lam hlam hbij N ψ' hψ'0 hψ'b hψ's
  obtain ⟨g, hg, hgA⟩ := hstd A hAh hAu
  obtain ⟨g', hg', hgA'⟩ := hstd A' hA'h hA'u
  obtain ⟨φ, hφ⟩ := hermitian_form_standard_basis Z R σ hσ N A g hg hgA
  obtain ⟨φ', hφ'⟩ := hermitian_form_standard_basis Z R σ hσ N A' g' hg' hgA'
  refine ⟨φ.symm.trans φ', fun x y => ?_⟩
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, hA'ψ, hφ', ← hφ, φ.apply_symm_apply,
    φ.apply_symm_apply, ← hAψ]

end PositivityTheory.UnitarySelfGeneration
end
end

-- Source module: Development.WeilBound.CoreStatements.HomogeneousNonvanishing.TwGPadic

section

@[expose] public section

open NumberField TensorProduct

namespace PositivityTheory.UnitarySelfGeneration

section

variable {Z O L : Type} [CommRing Z] [CommRing O] [AddCommGroup L] [Module O L]

theorem padic_act {N : ℕ} (φ : (Z ⊗[ℤ] L) ≃ₗ[Z] (Fin N → Z ⊗[ℤ] O))
    (hφ : ∀ (z : Z) (a : O) (x : L), φ (z ⊗ₜ (a • x)) = ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ (z ⊗ₜ x)) (a : O)
    (u : Z ⊗[ℤ] L) :
    φ (LinearMap.baseChange Z (LinearMap.lsmul O L a).toAddMonoidHom.toIntLinearMap u) =
      ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    rw [LinearMap.baseChange_tmul]
    exact hφ z a x
  | add u v hu hv => simp only [map_add (f := _), hu, hv, smul_add]

private theorem baseChange_antisymm_of_self_eq_zero (B : LinearMap.BilinForm ℤ L) (hB : ∀ x, B x x = 0) (u v : Z ⊗[ℤ] L) :
    B.baseChange Z u v = - B.baseChange Z v u := by
  have hs : ∀ x y, B x y = - B y x := by
    intro x y
    have h := hB (x + y)
    simp only [map_add (f := _), LinearMap.add_apply, hB, zero_add, add_zero] at h
    exact eq_neg_of_add_eq_zero_right h
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul w y =>
      rw [LinearMap.BilinForm.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul, hs x y, neg_smul, mul_comm]
    | add v w hv hw => simp only [map_add (f := _), LinearMap.add_apply, hv, hw, neg_add]
  | add u u' hu hu' => simp only [map_add (f := _), LinearMap.add_apply, hu, hu', neg_add]

theorem padic_alt (B : LinearMap.BilinForm ℤ L) (hB : ∀ x, B x x = 0) (u : Z ⊗[ℤ] L) :
    B.baseChange Z u u = 0 := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x => rw [LinearMap.BilinForm.baseChange_tmul, hB, zero_smul]
  | add u v hu hv =>
    simp only [map_add (f := _), LinearMap.add_apply, hu, hv]
    rw [baseChange_antisymm_of_self_eq_zero B hB u v]
    abel

theorem padic_adj (bar : O ≃+* O) (B : LinearMap.BilinForm ℤ L) (hB : ∀ (a : O) x y, B (a • x) y = B x (bar a • y))
    (a : O) (u v : Z ⊗[ℤ] L) :
    B.baseChange Z (LinearMap.baseChange Z (LinearMap.lsmul O L a).toAddMonoidHom.toIntLinearMap u) v =
      B.baseChange Z u (LinearMap.baseChange Z (LinearMap.lsmul O L (bar a)).toAddMonoidHom.toIntLinearMap v) := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul z x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul w y =>
      rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
      simp only [AddMonoidHom.coe_toIntLinearMap, LinearMap.toAddMonoidHom_coe, LinearMap.lsmul_apply,
        LinearMap.BilinForm.baseChange_tmul]
      rw [hB]
    | add v w hv hw => simp only [map_add (f := _), hv, hw]
  | add u u' hu hu' => simp only [map_add (f := _), LinearMap.add_apply, hu, hu']

theorem padic_form {N : ℕ} (bar : O ≃+* O) (φ : (Z ⊗[ℤ] L) ≃ₗ[Z] (Fin N → Z ⊗[ℤ] O))
    (hφ : ∀ (z : Z) (a : O) (x : L), φ (z ⊗ₜ (a • x)) = ((1 : Z) ⊗ₜ[ℤ] a : Z ⊗[ℤ] O) • φ (z ⊗ₜ x))
    (B : LinearMap.BilinForm ℤ L) (h1 : ∀ x, B x x = 0) (h2 : Function.Bijective (B.baseChange Z))
    (h3 : ∀ (a : O) x y, B (a • x) y = B x (bar a • y)) :
    ∃ ψ : LinearMap.BilinForm Z (Fin N → Z ⊗[ℤ] O), (∀ u v, ψ (φ u) (φ v) = B.baseChange Z u v) ∧
      (∀ x, ψ x x = 0) ∧ Function.Bijective ψ ∧ ∀ (a : Z ⊗[ℤ] O) x y, ψ (a • x) y =
        ψ x (Algebra.TensorProduct.map (AlgHom.id Z Z) bar.toRingHom.toIntAlgHom a • y) := by
  refine ⟨(B.baseChange Z).compl₁₂ φ.symm.toLinearMap φ.symm.toLinearMap, ?_, ?_, ?_, ?_⟩
  · intro u v
    simp
  · intro x
    simp [padic_alt B h1]
  · constructor
    · intro x y hxy
      apply φ.symm.injective
      apply h2.1
      refine LinearMap.ext fun w => ?_
      have := LinearMap.congr_fun hxy (φ w)
      simpa using this
    · intro f
      obtain ⟨u, hu⟩ := h2.2 (f.comp φ.toLinearMap)
      refine ⟨φ u, LinearMap.ext fun y => ?_⟩
      have := LinearMap.congr_fun hu (φ.symm y)
      simpa using this
  · intro a x y
    obtain ⟨u, rfl⟩ := φ.surjective x
    obtain ⟨v, rfl⟩ := φ.surjective y
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul z c =>
      have hz : ∀ (c' : O) (w : Z ⊗[ℤ] L), (z ⊗ₜ[ℤ] c' : Z ⊗[ℤ] O) • φ w =
          z • φ (LinearMap.baseChange Z (LinearMap.lsmul O L c').toAddMonoidHom.toIntLinearMap w) := by
        intro c' w
        rw [padic_act φ hφ c' w, ← smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [Algebra.TensorProduct.map_tmul]
      have e1 : (AlgHom.id Z Z) z = z := rfl
      have e2 : bar.toRingHom.toIntAlgHom c = bar c := rfl
      rw [e1, e2, hz, hz]
      simp only [LinearMap.map_smul, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply, LinearMap.smul_apply, padic_adj bar B h3]
    | add a a' ha ha' => simp only [add_smul, map_add (f := _), LinearMap.add_apply, ha, ha']

end

theorem padic_unit (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] [Algebra ℤ_[p] R] [Module.Finite ℤ_[p] R] (d : R)
    (h : IsCoprime d (p : R)) : IsUnit d := by
  obtain ⟨a, b, hab⟩ := h
  have hp : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  have hN : (⊤ : Submodule ℤ_[p] R) ≤ (Ideal.span {a * d}).restrictScalars ℤ_[p] := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal ℤ_[p])
      Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    intro x _
    have hx : x = a * d * x + (p : ℤ_[p]) • (b * x) := by
      rw [Algebra.smul_def, map_natCast]
      linear_combination (-x) * hab
    rw [hx]
    exact Submodule.add_mem_sup (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
      (Submodule.smul_mem_smul hp Submodule.mem_top)
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (hN Submodule.mem_top : (1 : R) ∈ _)
  have hu : IsUnit (a * d) := IsUnit.of_mul_eq_one y (by rw [mul_comm]; exact hy)
  exact isUnit_of_mul_isUnit_right hu

theorem padic_freeZ (E : Type) [Field E] [NumberField E] (L : Type) [AddCommGroup L] [Module (𝓞 E) L]
    [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] : Module.Finite ℤ L ∧ Module.Free ℤ L := by
  have h1 : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have h2 : Module.Flat ℤ L := Module.Flat.trans ℤ (𝓞 E) L
  exact ⟨h1, inferInstance⟩

theorem tw_g_padic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (bar : 𝓞 E ≃+* 𝓞 E), (∀ a : 𝓞 E, ((bar a : 𝓞 E) : E) = IsCMField.complexConj E (a : E)) → Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) → ∀ (p : ℕ) [Fact p.Prime] (L L' : Type) [AddCommGroup L] [Module (𝓞 E) L] [Module.Finite (𝓞 E) L] [Module.Projective (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L'] [Module.Finite (𝓞 E) L'] [Module.Projective (𝓞 E) L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L'), Module.finrank (𝓞 E) L = Module.finrank (𝓞 E) L' → (∀ x, B x x = 0) → Function.Bijective B → (∀ (a : 𝓞 E) x y, B (a • x) y = B x (bar a • y)) → (∀ x, B' x x = 0) → Function.Bijective B' → (∀ (a : 𝓞 E) x y, B' (a • x) y = B' x (bar a • y)) → ∃ φ : (ℤ_[p] ⊗[ℤ] L) ≃ₗ[ℤ_[p]] (ℤ_[p] ⊗[ℤ] L'), (∀ (a : 𝓞 E) (x : L), φ (1 ⊗ₜ (a • x)) = LinearMap.baseChange ℤ_[p] (LinearMap.lsmul (𝓞 E) L' a).toAddMonoidHom.toIntLinearMap (φ (1 ⊗ₜ x))) ∧ ∀ u v, B'.baseChange ℤ_[p] (φ u) (φ v) = B.baseChange ℤ_[p] u v := by
  intro E _ _ _ bar hbar hunr p _ L L' _ _ _ _ _ _ _ _ B B' hrk h1 h2 h3 k1 k2 k3
  obtain ⟨_, _⟩ := padic_freeZ E L
  obtain ⟨_, _⟩ := padic_freeZ E L'
  obtain ⟨φ, hφ⟩ := tw_g_free E p L
  have hL' := tw_g_free E p L'
  rw [← hrk] at hL'
  obtain ⟨φ', hφ'⟩ := hL'
  obtain ⟨ψ, hψ, a1, a2, a3⟩ := padic_form bar φ hφ B h1 (GlobalTheory.CompanionTheory.UnimodularBaseChange.bijective_baseChange ℤ_[p] L B h2) h3
  obtain ⟨ψ', hψ', b1, b2, b3⟩ := padic_form bar φ' hφ' B' k1 (GlobalTheory.CompanionTheory.UnimodularBaseChange.bijective_baseChange ℤ_[p] L' B' k2) k3
  obtain ⟨lam, l1, l2⟩ := tw_g_lam E bar hbar hunr p
  obtain ⟨θ, hθ⟩ := tw_g_theta E bar hbar hunr p Fact.out
  have hbb : ∀ a, bar (bar a) = a := fun a => RingOfIntegers.ext (by
    rw [hbar, hbar, IsCMField.complexConj_apply_apply])
  have hσ : ∀ r : ℤ_[p] ⊗[ℤ] 𝓞 E, Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom
      (Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom r) = r := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul]
      exact congrArg (z ⊗ₜ[ℤ] ·) (hbb a)
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hu : ∃ t : ℤ_[p] ⊗[ℤ] 𝓞 E,
      IsUnit (t - Algebra.TensorProduct.map (AlgHom.id ℤ_[p] ℤ_[p]) bar.toRingHom.toIntAlgHom t) := by
    refine ⟨1 ⊗ₜ θ, padic_unit p _ _ ?_⟩
    have := hθ.map (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := 𝓞 E)).toRingHom
    rw [map_natCast, map_sub] at this
    exact this
  obtain ⟨e, he⟩ := tw_g_std ℤ_[p] _ _ hσ lam l1 l2 _ (tw_g_semi p _ _ hσ hu _) ψ ψ' a1 a2 a3 b1 b2 b3
  refine ⟨φ ≪≫ₗ e.restrictScalars ℤ_[p] ≪≫ₗ φ'.symm, fun a x => ?_, fun u v => ?_⟩
  · apply φ'.injective
    rw [padic_act φ' hφ']
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.restrictScalars_apply]
    rw [hφ, map_smul]
  · rw [← hψ', ← hψ]
    simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, LinearEquiv.restrictScalars_apply]
    exact he _ _

end PositivityTheory.UnitarySelfGeneration
end
end
