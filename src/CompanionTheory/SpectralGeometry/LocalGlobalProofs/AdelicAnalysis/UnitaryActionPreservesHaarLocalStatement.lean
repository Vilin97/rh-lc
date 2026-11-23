module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MapMulVecEqSmul
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorInvolutionAlgebraProperties
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.MapMulEqOfNormOne

section

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.NormOneHaar

variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

def mulEquiv (u v : K) (h : u * v = 1) : K ≃ₜ+ K where
  toFun y := u * y
  invFun y := v * y
  left_inv y := by
    show v * (u * y) = y
    rw [← mul_assoc, mul_comm v u, h, one_mul]
  right_inv y := by
    show u * (v * y) = y
    rw [← mul_assoc, h, one_mul]
  map_add' x y := mul_add u x y
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def invEquiv (σ : K →+* K) (hc : Continuous σ) (hi : ∀ y, σ (σ y) = y) : K ≃ₜ+ K where
  toFun := σ
  invFun := σ
  left_inv := hi
  right_inv := hi
  map_add' := map_add σ
  continuous_toFun := hc
  continuous_invFun := hc

variable [LocallyCompactSpace K] [MeasurableSpace K] [BorelSpace K]

theorem char_conj (σ : K →+* K) (hc : Continuous σ) (hi : ∀ y, σ (σ y) = y) (u v : K)
    (h : u * v = 1) (h' : σ u * σ v = 1) :
    addEquivAddHaarChar (mulEquiv (σ u) (σ v) h') = addEquivAddHaarChar (mulEquiv u v h) := by
  set s := invEquiv σ hc hi
  have e : mulEquiv (σ u) (σ v) h' = (s.trans (mulEquiv u v h)).trans s.symm := by
    ext y
    show σ u * y = σ (u * σ y)
    rw [map_mul, hi]
  rw [e, addEquivAddHaarChar_trans, addEquivAddHaarChar_trans, addEquivAddHaarChar_symm,
    mul_comm (addEquivAddHaarChar s), mul_assoc,
    mul_inv_cancel₀ (addEquivAddHaarChar_pos s).ne', mul_one]

theorem char_mul_eq_one (u v : K) (h : u * v = 1) (h' : v * u = 1) :
    addEquivAddHaarChar (mulEquiv u v h) * addEquivAddHaarChar (mulEquiv v u h') = 1 := by
  have e : (mulEquiv u v h).trans (mulEquiv v u h') = ContinuousAddEquiv.refl K := by
    ext y
    show v * (u * y) = y
    rw [← mul_assoc, h', one_mul]
  rw [← addEquivAddHaarChar_trans, e, addEquivAddHaarChar_refl]

theorem map_mul_eq_of_norm_one :
    ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
      [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (σ : K →+* K),
      Continuous σ → (∀ y, σ (σ y) = y) → ∀ (lam : Measure K) [lam.IsAddHaarMeasure] (u : K),
      u * σ u = 1 → lam.map (fun y => u * y) = lam := by
  intro K _ _ _ _ _ _ _ _ σ hc hi lam _ u hu
  have hu' : σ u * σ (σ u) = 1 := by rw [← map_mul, hu, map_one]
  have hu2 : σ u * u = 1 := by rw [mul_comm, hu]
  have hconj := char_conj σ hc hi u (σ u) hu hu'
  have hprod := char_mul_eq_one u (σ u) hu hu2
  have hsame : mulEquiv (σ u) u hu2 = mulEquiv (σ u) (σ (σ u)) hu' := by
    ext y
    rfl
  rw [hsame, hconj] at hprod
  have hone : addEquivAddHaarChar (mulEquiv u (σ u) hu) = 1 := by
    have h2 : addEquivAddHaarChar (mulEquiv u (σ u) hu) ^ 2 = 1 := by rw [sq, hprod]
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h2
  have hmap := addEquivAddHaarChar_smul_map lam (mulEquiv u (σ u) hu)
  rw [hone, one_smul] at hmap
  exact hmap

end GlobalTheory.CompanionTheory.SW.NormOneHaar
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionPreservesHaarLocal

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.HInv

theorem det_mul_conj_eq_one {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m]
    (τ : A →+* A) (g J : Matrix m m A) (hg : cT τ g * J * g = J) (hJ : IsUnit J.det) :
    g.det * τ g.det = 1 := by
  have hc : (cT τ g).det = τ g.det := by
    rw [cT, Matrix.det_transpose, RingHom.map_det, RingHom.mapMatrix_apply]
  have h := congrArg Matrix.det hg
  rw [Matrix.det_mul, Matrix.det_mul, hc] at h
  apply hJ.mul_left_cancel
  linear_combination h

theorem map_tuple_eq {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] [SecondCountableTopology K] [T2Space K] [MeasurableSpace K]
    [BorelSpace K] [IsArtinianRing K] [IsReduced K] (τ : K →+* K) (hc : Continuous τ)
    (hi : ∀ y, τ (τ y) = y) {M n : ℕ} (A : Matrix (Fin M) (Fin M) K)
    (hA : A.det * τ A.det = 1) (μ : Measure (Fin n → Fin M → K)) [μ.IsAddHaarMeasure] :
    μ.map (fun X a => A *ᵥ X a) = μ := by
  let lam : Measure K := Measure.addHaar
  have hl : lam.map (fun y => A.det * y) = lam :=
    NormOneHaar.map_mul_eq_of_norm_one K τ hc hi lam _ hA
  let μ0 : Measure (Fin M → K) := Measure.pi fun _ => lam
  have hdet : IsUnit A.det := IsUnit.of_mul_eq_one _ hA
  have h0 : μ0.map (fun x => A *ᵥ x) = μ0 := by
    have := ModDet.map_mulVec_eq_smul K (Fin M) μ0 lam A hdet 1 (by simpa using hl)
    simpa using this
  let P : Measure (Fin n → Fin M → K) := Measure.pi fun _ => μ0
  have hmeas : Measurable (fun x : Fin M → K => A *ᵥ x) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  haveI hs : SigmaFinite (μ0.map (fun x => A *ᵥ x)) := by
    rw [h0]; infer_instance
  have hP : P.map (fun X a => A *ᵥ X a) = P := by
    have := Measure.pi_map_pi (μ := fun _ : Fin n => μ0) (f := fun _ x => A *ᵥ x)
      (fun _ => hmeas.aemeasurable)
    simpa only [h0] using this
  have e := Measure.isAddLeftInvariant_eq_smul μ P
  have htuple : Measurable (fun (X : Fin n → Fin M → K) a => A *ᵥ X a) :=
    Measurable.of_eval fun a => hmeas.comp (measurable_pi_apply a)
  rw [e, Measure.map_smul _ htuple.aemeasurable, hP]

theorem map_actW_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R],
    IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure →
    ∀ h : HA R σ J, μ.map (actW R σ J h) = μ := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ hμ h
  obtain ⟨r1, r2, r3, r4, r5, r6, -, -⟩ := hR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI := r5
  haveI := r6
  obtain ⟨t1, t2, t3, t4, tc, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨a1, a2, -, ai, -⟩ := KAlg.algebra_tensor_invol F E σ hCM R
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := a1
  haveI := a2
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hJu : IsUnit (JR (F := F) R J).det := by
    have e : (JR (F := F) R J).det = inclR (F := F) R J.det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, JR]
    rw [e]
    exact (IsUnit.mk0 _ hJ.2).map (inclR (F := F) R)
  have hg : cT (sigR R σ) ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *
      JR (F := F) R J * ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR (F := F) R J :=
    (show (h : HR R σ J).1 ∈ HR R σ J from (h : HR R σ J).2)
  exact map_tuple_eq (sigR R σ) tc ai _ (det_mul_conj_eq_one _ _ _ hg hJu) μ

end GlobalTheory.CompanionTheory.SW.HInv
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionPreservesHaarLocalStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.unitary_action_preserves_haar_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)), μ.IsAddHaarMeasure → ∀ h : HA R σ J, μ.map (actW R σ J h) = μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.HInv.map_actW_eq | exact GlobalTheory.CompanionTheory.SW.HInv.map_actW_eq | (intros; apply GlobalTheory.CompanionTheory.SW.HInv.map_actW_eq <;> assumption)
end
end
