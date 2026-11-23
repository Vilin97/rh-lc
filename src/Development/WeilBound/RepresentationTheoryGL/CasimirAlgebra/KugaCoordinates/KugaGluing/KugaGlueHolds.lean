module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.IsStarRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactDerivativeSeparatingDual
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Tpr
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.WignerVanishingGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgCasDiff
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgFormRTensor

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactCurveDerivative

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.WigCurve

theorem exists_unitary_matrix_curve (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E))
    (hZ : star Z = -Z) :
    ∃ f : ℝ → Matrix (Fin a) (Fin a) (Cinf E), (∀ t, f t ∈ unitary (Matrix (Fin a) (Fin a) (Cinf E))) ∧
      f 0 = 1 ∧ HasDerivAt (fun t => toL (f t)) (toL Z) 0 := by
  have hcs : ContinuousStar (Matrix (Fin a) (Fin a) (Cinf E)) := inferInstance
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin a) (Fin a) (Cinf E)) := NormedAlgebra.restrictScalars ℚ ℝ _
  refine ⟨fun t => NormedSpace.exp (t • Z), fun t => ?_, by simp, ?_⟩
  · refine @NormedSpace.exp_mem_unitary_of_mem_skewAdjoint _ _ _ _ _ ⟨hcs.continuous_star⟩ _ ?_
    rw [skewAdjoint.mem_iff, star_smul, hZ, star_trivial, smul_neg]
  · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
      LinearMap.toContinuousLinearMap
        { toFun := fun x => toL x, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem exists_kinf_curve_tangent : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (Z : Matrix (Fin a) (Fin a) (Cinf E)), star Z = -Z → ∃ c : ℝ → Kinf E a, c 0 = 1 ∧ HasDerivAt (fun t => toL (c t).1) (toL Z) 0 := by
  intro E _ _ a Z hZ
  obtain ⟨f, hu, h0, hd⟩ := exists_unitary_matrix_curve E a Z hZ
  exact ⟨fun t => ⟨f t, hu t⟩, Subtype.ext h0, hd⟩

end GlobalTheory.WigCurve

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorCompactActionDerivative

section

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.WigSep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def evAt (π : CuspSub E a) (g : GA E a) : π.V →ₗ[ℂ] ℂ :=
  (LinearMap.proj g).comp ((Sm E a).subtype.comp π.V.subtype)

def ell (π : CuspSub E a) (Ξ : AlgRep E a) (g : GA E a) (i : Fin Ξ.d) :
    Module.Dual ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :=
  (TensorProduct.lid ℂ ℂ).toLinearMap.comp (TensorProduct.map (evAt π g) (LinearMap.proj i))

theorem ell_tmul (π : CuspSub E a) (Ξ : AlgRep E a) (g : GA E a) (i : Fin Ξ.d) (φ : π.V) (v : Fin Ξ.d → ℂ) :
    ell π Ξ g i (φ ⊗ₜ v) = φ.1.1 g * v i := by
  simp [ell, evAt]

theorem piScalarRight_eval (π : CuspSub E a) (Ξ : AlgRep E a) (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) (g : GA E a) (i : Fin Ξ.d) :
    ((TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d) m) i).1.1 g = ell π Ξ g i m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, Submodule.coe_add, hx, hy]
  | tmul φ v =>
    rw [ell_tmul]
    simp [TensorProduct.piScalarRight_apply, mul_comm]

theorem ell_sep (π : CuspSub E a) (Ξ : AlgRep E a) (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ))
    (h : ∀ g i, ell π Ξ g i m = 0) : m = 0 := by
  refine (LinearEquiv.map_eq_zero_iff (TensorProduct.piScalarRight ℂ ℂ π.V (Fin Ξ.d))).1 ?_
  funext i
  refine Subtype.ext (Subtype.ext (funext fun g => ?_))
  rw [piScalarRight_eval, h]
  rfl

theorem ell_deriv (π : CuspSub E a) (Ξ : AlgRep E a) (c : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E))
    (h0 : c 0 = 1) (hc : HasDerivAt (fun t => toL (c t).1) (toL Z) 0) (g : GA E a) (i : Fin Ξ.d)
    (m : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) :
    HasDerivAt (fun t => ell π Ξ g i (tensorK π Ξ (c t) m)) (ell π Ξ g i (tensorLie π Ξ (toL Z) m)) 0 := by
  have h0' : Unitary.toUnits (c 0) = 1 := by rw [h0, map_one]
  have hc' : HasDerivAt (fun t => toL (Unitary.toUnits (c t)).val) (toL Z) 0 := hc
  induction m using TensorProduct.induction_on with
  | zero => simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  | add x y hx hy => simp only [map_add (f := _)]; exact hx.add hy
  | tmul φ v =>
    have h1 := GlobalTheory.CuspRep.hasDerivAt_curve φ.1 g (fun t => Unitary.toUnits (c t)) (toL Z) h0' hc'
    have h2 : HasDerivAt (fun t => (Ξ.mat (Unitary.toUnits (c t)) *ᵥ v) i) ((Ξ.dmat (toL Z) *ᵥ v) i) 0 := by
      simp only [Matrix.mulVec, dotProduct]
      exact HasDerivAt.fun_sum (u := Finset.univ) fun j _ =>
        (Ξ.hasDerivAt_curve (fun t => Unitary.toUnits (c t)) (toL Z) h0' hc' i j).mul_const (v j)
    have e1 : ∀ t, ell π Ξ g i (tensorK π Ξ (c t) (φ ⊗ₜ v)) =
        φ.1.1 (g * infGL E a (Unitary.toUnits (c t))) * (Ξ.mat (Unitary.toUnits (c t)) *ᵥ v) i := fun t => by
      rw [tensorK, TensorProduct.map_tmul, ell_tmul]
      rfl
    have e2 : ell π Ξ g i (tensorLie π Ξ (toL Z) (φ ⊗ₜ v)) =
        lieD (toL Z) φ.1.1 g * (Ξ.mat (Unitary.toUnits (c 0)) *ᵥ v) i +
          φ.1.1 (g * infGL E a (Unitary.toUnits (c 0))) * (Ξ.dmat (toL Z) *ᵥ v) i := by
      rw [h0', map_one, map_one, mul_one, Matrix.one_mulVec, tensorLie_tmul, map_add (f := _), ell_tmul, ell_tmul]
      rfl
    rw [funext e1, e2]
    exact h1.mul h2

end GlobalTheory.WigSep

namespace GlobalTheory.WigSep

theorem exists_separating_functionals : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a), ∃ S : Set (Module.Dual ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))), (∀ m, (∀ l ∈ S, l m = 0) → m = 0) ∧ ∀ (c : ℝ → Kinf E a) (Z : Matrix (Fin a) (Fin a) (Cinf E)), c 0 = 1 → HasDerivAt (fun t => toL (c t).1) (toL Z) 0 → ∀ l ∈ S, ∀ m, HasDerivAt (fun t => l (tensorK π Ξ (c t) m)) (l (tensorLie π Ξ (toL Z) m)) 0 := by
  intro E _ _ _ a π Ξ
  refine ⟨Set.range fun p : GA E a × Fin Ξ.d => ell π Ξ p.1 p.2, fun m h => ell_sep π Ξ m fun g i => h _ ⟨(g, i), rfl⟩, ?_⟩
  rintro c Z h0 hc _ ⟨⟨g, i⟩, rfl⟩ m
  exact ell_deriv π Ξ c Z h0 hc g i m

end GlobalTheory.WigSep

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KgCxDmatConj

section

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL

namespace PositivityTheory.Rg.Cz

section
variable {E : Type} [Field E] [NumberField E] {a : ℕ}

omit [NumberField E] in
theorem kg_star_atEmb (τ : E →+* ℂ) (z : ℂ) : star (atEmb τ z) = atEmb τ (starRingEnd ℂ z) := by
  classical
  unfold atEmb
  funext w
  simp only [Pi.star_apply, Pi.single_apply]
  split_ifs <;> simp

theorem kg_cx_dmat_conj (Ξ : AlgRep E a)
    (hΞ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), Ξ.dmat (toL (star X)) = (Ξ.dmat (toL X))ᴴ)
    (τ : E →+* ℂ) (i j : Fin a) : (cx τ Ξ.dmat i j)ᴴ = cx τ Ξ.dmat j i := by
  have e : ∀ z, (Ξ.dmat (toL (Matrix.single i j (atEmb τ z))))ᴴ =
      Ξ.dmat (toL (Matrix.single j i (atEmb τ (starRingEnd ℂ z)))) := by
    intro z; rw [← hΞ, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single, kg_star_atEmb]
  have e2 : Ξ.dmat (toL (Matrix.single j i (atEmb τ (-Complex.I)))) =
      -Ξ.dmat (toL (Matrix.single j i (atEmb τ Complex.I))) := by
    rw [← map_neg]
    congr 1
    funext k l
    show Matrix.single j i (atEmb τ (-Complex.I)) k l = -(Matrix.single j i (atEmb τ Complex.I) k l)
    rw [Matrix.single_apply, Matrix.single_apply, atEmb_eq τ (-Complex.I), atEmb_eq τ Complex.I]
    split_ifs <;> simp
  unfold cx
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, e, e, map_one,
    Complex.conj_I, e2]
  simp only [Complex.star_def, map_div₀, map_one, map_ofNat, Complex.conj_I]
  module

theorem kg_cas_herm (Ξ : AlgRep E a)
    (hΞ : ∀ X : Matrix (Fin a) (Fin a) (Cinf E), Ξ.dmat (toL (star X)) = (Ξ.dmat (toL X))ᴴ) (τ : E →+* ℂ) :
    (∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i)ᴴ = ∑ i, ∑ j, cx τ Ξ.dmat i j * cx τ Ξ.dmat j i := by
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, kg_cx_dmat_conj Ξ hΞ]

omit [NumberField E] in
theorem kg_star_iM {X : Matrix (Fin a) (Fin a) (Cinf E)} (hX : star X = X) : star (iM X) = -iM X := by
  ext i j w
  have h : star (X j i) = X i j := by rw [← Matrix.star_apply, hX]
  have h' : star (X j i w) = X i j w := congrFun h w
  simp only [iM, Matrix.star_apply, Matrix.smul_apply, Matrix.neg_apply, Pi.star_apply, Pi.neg_apply, smul_eq_mul,
    Pi.mul_apply, star_mul', h', Complex.star_def, Complex.conj_I]
  ring

def kgL : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Lie E a where
  toFun := toL
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


omit [NumberField E] in
def kgD (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) : Herm E a →ₗ[ℝ] Herm E a where
  toFun Y := ⟨Z * Y.1 - Y.1 * Z, by
    have hY : star Y.1 = Y.1 := Y.2
    show star (Z * Y.1 - Y.1 * Z) = Z * Y.1 - Y.1 * Z
    rw [star_sub, star_mul, star_mul, hY, hZ, mul_neg, neg_mul, sub_neg_eq_add, neg_add_eq_sub]⟩
  map_add' Y Y' := Subtype.ext (by
    show Z * (Y.1 + Y'.1) - (Y.1 + Y'.1) * Z = (Z * Y.1 - Y.1 * Z) + (Z * Y'.1 - Y'.1 * Z)
    rw [mul_add, add_mul]; abel)
  map_smul' c Y := Subtype.ext (by
    show Z * (c • Y.1) - (c • Y.1) * Z = c • (Z * Y.1 - Y.1 * Z)
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub])

omit [NumberField E] in
theorem kgD_val (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (Y : Herm E a) :
    (kgD Z hZ Y).1 = Z * Y.1 - Y.1 * Z := rfl

end
end PositivityTheory.Rg.Cz
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KugaGlueHolds

section

@[expose] public section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace PositivityTheory.Rg.Cz

set_option maxHeartbeats 800000 in
theorem kugaGlue_holds : KugaGlue := by
  intro hK hF hC _ hT hH E _ _ _ a π Ξ hU hS q₀ ω₀ hω₀ h0
  refine hH E a _ (tensorK π Ξ) (tensorLie π Ξ) (fun q ω hω => ?_) q₀ ω₀ hω₀ h0
  obtain ⟨Hf, σ, hHs, hHp, hHl⟩ := hU
  obtain ⟨B, hB1, hB2, hB3, hB4⟩ := hT π.V Ξ.d Hf hHs hHp
  obtain ⟨hspan, c, hc, hbr, hbr2⟩ := hF E a
  choose cc tt hcas htr htrX hle using hS.2
  have hZ : ∀ k, star (iM (fr (E := E) (a := a) k).1) = -iM (fr k).1 := fun k => kg_star_iM (fr k).2
  have hreal : ∀ X : Lie E a, starRingEnd ℂ (kgT X) = kgT X := fun X => kgT_star X

  have hskew : ∀ (X : Herm E a) (x y : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)),
      B ((kgA π Ξ σ).comp kgH X x) y = -B x ((kgA π Ξ σ).comp kgH X y) := by
    intro X x y
    have h1 := kg_form_rTensor Hf B hB3 (lieOp π (toL X.1)) (σ * kgT (toL X.1)) (fun φ ψ => hHl _ φ ψ) x y
    have hs := hreal (toL X.1)
    rw [LinearMap.comp_apply, show kgH X = toL X.1 from rfl, kgA_apply]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul,
      LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, map_neg, Complex.conj_ofReal, map_div₀, map_ofNat, hs]
    linear_combination h1
  have hherm : ∀ (X : Herm E a) (x y : π.V ⊗[ℂ] (Fin Ξ.d → ℂ)),
      B ((kgR π Ξ σ).comp kgH X x) y = B x ((kgR π Ξ σ).comp kgH X y) := by
    intro X x y
    have hD : (Ξ.dmat (toL X.1))ᴴ = Ξ.dmat (toL X.1) := by
      rw [← hS.1, show star X.1 = X.1 from X.2]
    have h2 := kg_form_lTensor Hf B hB3 _ hD x y
    have hs := hreal (toL X.1)
    rw [LinearMap.comp_apply, show kgH X = toL X.1 from rfl, kgR_apply]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul,
      LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, map_neg, Complex.conj_ofReal, map_div₀, map_ofNat, hs]
    linear_combination h2

  have hbrA : ∀ i j, (kgA π Ξ σ).comp kgH (fr i) * (kgA π Ξ σ).comp kgH (fr j) -
      (kgA π Ξ σ).comp kgH (fr j) * (kgA π Ξ σ).comp kgH (fr i) =
      ∑ k, (c i j k : ℂ) • kgA π Ξ σ (toL (iM (fr k).1)) := by
    intro i j
    show kgA π Ξ σ (toL (fr i).1) * kgA π Ξ σ (toL (fr j).1) - kgA π Ξ σ (toL (fr j).1) * kgA π Ξ σ (toL (fr i).1) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [kgA_comm, hbr i j, show toL (∑ k, c i j k • iM (fr k).1) = kgL (∑ k, c i j k • iM (fr k).1) from rfl,
      map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_smul, ← algebraMap_smul ℂ (c i j k)]
    rfl
  have hbrR : ∀ i j, (kgR π Ξ σ).comp kgH (fr i) * (kgR π Ξ σ).comp kgH (fr j) -
      (kgR π Ξ σ).comp kgH (fr j) * (kgR π Ξ σ).comp kgH (fr i) =
      ∑ k, (c i j k : ℂ) • kgR π Ξ σ (toL (iM (fr k).1)) := by
    intro i j
    show kgR π Ξ σ (toL (fr i).1) * kgR π Ξ σ (toL (fr j).1) - kgR π Ξ σ (toL (fr j).1) * kgR π Ξ σ (toL (fr i).1) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [kgR_comm, hbr i j, show toL (∑ k, c i j k • iM (fr k).1) = kgL (∑ k, c i j k • iM (fr k).1) from rfl,
      map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_smul, ← algebraMap_smul ℂ (c i j k)]
    rfl
  have hDk : ∀ k j, kgD _ (hZ k) (fr j) = ∑ i, c i j k • fr i := fun k j => Subtype.ext (by
    rw [kgD_val, Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    exact hbr2 k j)

  have hinv : ∀ k (Y : Fin q → Herm E a), (kgA π Ξ σ (toL (iM (fr k).1)) + kgR π Ξ σ (toL (iM (fr k).1))) (ω Y) =
      ∑ s, ω (Function.update Y s (kgD _ (hZ k) (Y s))) := by
    intro k Y
    obtain ⟨S, hS1, hS2⟩ := GlobalTheory.WigSep.exists_separating_functionals E a π Ξ
    obtain ⟨cv, hc0, hcd⟩ := GlobalTheory.WigCurve.exists_kinf_curve_tangent E a _ (hZ k)
    rw [kgA_add_kgR]
    exact GlobalTheory.CochainInv.lie_apply_eq_sum E a _ (tensorK π Ξ) (tensorLie π Ξ) S cv _ (hZ k) hc0 hcd hS1
      (hS2 cv _ hc0 hcd) q ω hω Y _ (fun s => rfl)

  have hcasI : ∀ x : π.V ⊗[ℂ] (Fin Ξ.d → ℂ),
      (B (((∑ i, (kgR π Ξ σ).comp kgH (fr i) * (kgR π Ξ σ).comp kgH (fr i) -
        ∑ k, kgR π Ξ σ (toL (iM (fr k).1)) * kgR π Ξ σ (toL (iM (fr k).1))) -
        (∑ i, (kgA π Ξ σ).comp kgH (fr i) * (kgA π Ξ σ).comp kgH (fr i) -
        ∑ k, kgA π Ξ σ (toL (iM (fr k).1)) * kgA π Ξ σ (toL (iM (fr k).1))) :
          Module.End ℂ (π.V ⊗[ℂ] (Fin Ξ.d → ℂ))) x) x).re ≤ 0 := by
    intro x
    have e := kg_casDiff π Ξ σ hC cc tt hcas htr htrX
    have h := kg_re_le B _ cc (fun τ y => hB4 _ (cc τ) (kg_cas_herm Ξ hS.1 τ) (hle τ) y) x
    rw [← e] at h
    exact h

  have key := hK (Herm E a) (π.V ⊗[ℂ] (Fin Ξ.d → ℂ)) _ _ fr B ((kgA π Ξ σ).comp kgH) ((kgR π Ξ σ).comp kgH)
    (fun k => kgA π Ξ σ (toL (iM (fr k).1))) (fun k => kgR π Ξ σ (toL (iM (fr k).1))) (fun k => kgD _ (hZ k)) c
    hspan hB1 hB2 hskew hherm (fun X Y => kgA_kgR_comm π Ξ σ _ _) (fun k => kgA_kgR_comm π Ξ σ _ _) hbrA hbrR hc hDk
    hcasI q ω hinv
  refine AlternatingMap.ext fun X => ?_
  rw [dCo_apply, AlternatingMap.zero_apply, ← key X]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, kgA_add_kgR]
  rfl

end PositivityTheory.Rg.Cz
end
end
end
