module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyHermitianIntegrallyCongruentCmExtStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoordEquivApply
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceFormGramPowerBasisHermitianNondegenerateStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyLocalIntegersIffPowerBasisCoordsAll

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section
namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ}
  (P : PPol σ r)

theorem map_mem_intLoc_fld {v : HeightOneSpectrum (𝓞 F)} {c : Fv F v ⊗[F] E} (hc : c ∈ intLoc F E v) :
    Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) (IsScalarTower.toAlgHom F E (Fld P)) c ∈
      intLoc F (Fld P) v := by
  refine intLoc_induction (p := fun c => Algebra.TensorProduct.map (AlgHom.id F (Fv F v))
      (IsScalarTower.toAlgHom F E (Fld P)) c ∈ intLoc F (Fld P) v) (fun a ha x => ?_) (by simp)
    (fun y z hy hz => by rw [map_add]; exact add_mem hy hz) (fun y hy => by rw [map_neg]; exact neg_mem hy) hc
  rw [Algebra.TensorProduct.map_tmul]
  exact tmul_mem_intLoc ha ⟨algebraMap E (Fld P) x, x.2.algebraMap⟩

theorem eventually_mem_intLoc_iff_coordEquiv_mem :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] Fld P,
      y ∈ intLoc F (Fld P) v ↔ coordEquiv P (Fv F v) y ∈ latLoc F (stdLattice E r) v := by
  let b := RingOfIntegers.basis (Fld P)
  filter_upwards [eventually_all.2 fun i => eventually_all.2 fun j =>
      eventually_one_tmul_mem_intLoc (F := F) ((powB P).repr (b j : Fld P) i),
    eventually_all.2 fun i => eventually_one_tmul_mem_intLoc (F := F) (E := Fld P) (powB P i)] with v h1 h2 y
  rw [mem_latLoc_stdLattice]
  constructor
  · intro hy i
    rw [coordEquiv_apply]
    refine intLoc_induction (p := fun y => coordF P (Fv F v) i y ∈ intLoc F E v) (fun a ha x => ?_) (by simp)
      (fun y z hy hz => by rw [map_add]; exact add_mem hy hz) (fun y hy => by rw [map_neg]; exact neg_mem hy) hy
    rw [coordF_tmul]
    have e : (powB P).repr (x : Fld P) i = ∑ j, b.repr x j • (powB P).repr (b j : Fld P) i := by
      conv_lhs => rw [← b.sum_repr x]

      simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [← zsmul_eq_mul, map_zsmul]
    rw [e, TensorProduct.tmul_sum]
    refine sum_mem fun j _ => ?_
    rw [TensorProduct.tmul_smul]
    refine zsmul_mem ?_ _
    have e2 : a ⊗ₜ[F] ((powB P).repr (b j : Fld P) i) =
        (a ⊗ₜ[F] ((1 : 𝓞 E) : E)) * ((1 : Fv F v) ⊗ₜ[F] (powB P).repr (b j : Fld P) i) := by simp
    rw [e2]
    exact mul_mem (tmul_mem_intLoc ha 1) (h1 i j)
  · intro h
    rw [← coordInv_coordF P (Fv F v) y]
    refine sum_mem fun i _ => ?_
    rw [smul_eq_map_mul]
    exact mul_mem (map_mem_intLoc_fld P (h i)) (h2 i)

end GlobalTheory.TrUnitLat

theorem GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] Fld P, y ∈ intLoc F (Fld P) v ↔ GlobalTheory.TrUnitLat.coordEquiv P (Fv F v) y ∈ latLoc F (stdLattice E r) v :=
  fun F E _ _ _ _ _ σ r P => GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem P
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyLocalIntegersIffPowerBasisCoordsAllStatement

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.eventually_localIntegers_iff_powerBasisCoords_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ y : Fv F v ⊗[F] Fld P, y ∈ intLoc F (Fld P) v ↔ GlobalTheory.TrUnitLat.coordEquiv P (Fv F v) y ∈ latLoc F (stdLattice E r) v := by
  first | exact @GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all | exact GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all | (intros; apply GlobalTheory.TrUnitLat.eventually_mem_intLoc_iff_coordEquiv_mem_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowerBasisCoordsIsTorusHermitianIsometry

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

namespace GlobalTheory.TrUnitLat

variable {F E : Type} [Field F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {r : ℕ} (P : PPol σ r)

theorem trace_mul_star_eq_sum (z z' : Fld P) :
    ∑ i, ∑ j, σ ((powB P).repr z' i) * gramOne P i j * (powB P).repr z j =
      Algebra.trace E (Fld P) (z * star' P z') := by
  have hs : star' P z' = ∑ i, σ ((powB P).repr z' i) • star' P (powB P i) := by
    conv_lhs => rw [← (powB P).sum_repr z']

    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Algebra.smul_def, map_mul, star'_algebraMap, ← Algebra.smul_def]

  rw [hs, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← (powB P).sum_repr z]

  rw [Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm, map_smul, smul_eq_mul, gramOne, Matrix.of_apply]
  ring

theorem isIsom_coordEquiv : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r)
    (k : Type) [CommRing k] [Algebra F k],
    IsIsom P k (GlobalTheory.TrUnitLat.gramOne P) 1 (GlobalTheory.TrUnitLat.coordEquiv P k) := by
  intro F E _ _ _ σ r P k _ _ y y'
  simp only [Formalism.UG.hform, hx, one_mul, coordEquiv_apply]
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y₁ y₂ h₁ h₂ =>
    simp only [map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]
  | tmul a z =>
    induction y' using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib, h₁, h₂]
    | tmul a' z' =>
      have e1 : ∀ e : E, sigR k σ (a' ⊗ₜ[F] e) = a' ⊗ₜ[F] σ e := fun e => rfl
      have e2 : sigR k (star' P) (a' ⊗ₜ[F] z') = a' ⊗ₜ[F] star' P z' := rfl
      have e3 : ∀ i j, JR k (gramOne P) i j = (1 : k) ⊗ₜ[F] gramOne P i j := fun i j => rfl
      have e4 : ∀ (b : k) (w : Fld P), trBase P k (b ⊗ₜ[F] w) = b ⊗ₜ[F] Algebra.trace E (Fld P) w := fun b w => rfl
      simp only [coordF_tmul, e1, e2, e3, Algebra.TensorProduct.tmul_mul_tmul, e4, mul_one, ← TensorProduct.tmul_sum,
        trace_mul_star_eq_sum]
      rw [mul_comm a' a]

end GlobalTheory.TrUnitLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowerBasisCoordsIsTorusHermitianIsometryStatement

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.powerBasisCoords_isTorusHermitianIsometry : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r) (k : Type) [CommRing k] [Algebra F k], IsIsom P k (GlobalTheory.TrUnitLat.gramOne P) 1 (GlobalTheory.TrUnitLat.coordEquiv P k) := by
  first | exact @GlobalTheory.TrUnitLat.isIsom_coordEquiv | exact GlobalTheory.TrUnitLat.isIsom_coordEquiv | (intros; apply GlobalTheory.TrUnitLat.isIsom_coordEquiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitClassRealizedByLatticeIsometry

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section

namespace GlobalTheory.TrUnitLat
theorem alpha_mem_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (r : ℕ) (P : PPol σ r), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, diagH (star' P) (one₁ P) (Fv F v) (alphaRat P) ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ _ σ r P
  filter_upwards [eventually_one_tmul_mem_intLoc (F := F) (alpha P),
    eventually_one_tmul_mem_intLoc (F := F) (alpha P)⁻¹] with v h1 h2
  have e0 : ∀ Y : Fin 1 → Fv F v ⊗[F] Fld P,
      (matHom _ (star' P) (one₁ P) (diagH (star' P) (one₁ P) (Fv F v) (alphaRat P))).1 *ᵥ Y ∈
        latLoc F (stdLattice (Fld P) 1) v ↔ (1 : Fv F v) ⊗ₜ[F] alpha P * Y 0 ∈ intLoc F (Fld P) v := fun Y => by
    have e : (matHom _ (star' P) (one₁ P) (diagH (star' P) (one₁ P) (Fv F v) (alphaRat P))).1 0 0 =
        (1 : Fv F v) ⊗ₜ[F] alpha P := rfl
    rw [mem_latLoc_stdLattice, Fin.forall_fin_one, ← e]
    simp [Matrix.mulVec, dotProduct]
  have hinv : (1 : Fv F v) ⊗ₜ[F] (alpha P)⁻¹ * (1 : Fv F v) ⊗ₜ[F] alpha P = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ (alpha_ne_zero P), Algebra.TensorProduct.one_def]
  refine mem_stabLoc.2 fun Y => ?_
  rw [e0, mem_latLoc_stdLattice, Fin.forall_fin_one]
  refine ⟨mul_mem h1, fun hY => ?_⟩
  have := mul_mem h2 hY
  rwa [← mul_assoc, hinv, one_mul] at this

theorem stab_torEmb_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (r n : ℕ) (P : PPol σ r) (v : HeightOneSpectrum (𝓞 F)) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) (x : Fv F v ⊗[F] Fld P) (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin n → Fv F v ⊗[F] E)) (h : IsIsom P (Fv F v) J x φ), (∀ y, y ∈ intLoc F (Fld P) v ↔ φ y ∈ latLoc F L v) → ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ σ r n P v J L x φ h hφ t
  have e1 : (matHom _ σ J (torEmb h t)).1 = mulMat φ (torUnit t).1 := rfl
  have e0 : (torUnit t).1 = t.1.1 0 0 := Matrix.det_fin_one _
  have e2 : ∀ Y : Fin 1 → Fv F v ⊗[F] Fld P,
      (matHom _ (star' P) (one₁ P) t).1 *ᵥ Y ∈ latLoc F (stdLattice (Fld P) 1) v ↔
        (torUnit t).1 * Y 0 ∈ intLoc F (Fld P) v := fun Y => by
    rw [mem_latLoc_stdLattice, Fin.forall_fin_one, e0]
    simp [Matrix.mulVec, dotProduct, matHom]
    exact Iff.rfl
  rw [mem_stabLoc, mem_stabLoc]
  constructor
  · intro H Y
    rw [e2, mem_latLoc_stdLattice, Fin.forall_fin_one]
    have := H (φ (Y 0))
    rwa [e1, mulMat_mulVec, ← hφ, ← hφ] at this
  · intro H Y
    obtain ⟨y, rfl⟩ := φ.surjective Y
    rw [e1, mulMat_mulVec, ← hφ, ← hφ]
    have := H (fun _ => y)
    rwa [e2, mem_latLoc_stdLattice, Fin.forall_fin_one] at this

end GlobalTheory.TrUnitLat

namespace GlobalTheory.TrUnitLat

theorem hform_mulVec' {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} (J k : Matrix (Fin n) (Fin n) A) (a b : Fin n → A) :
    Formalism.UG.hform s J (k *ᵥ a) (k *ᵥ b) = Formalism.UG.hform s (Formalism.UG.cT s k * J * k) a b := by
  have e2 : ∀ (J : Matrix (Fin n) (Fin n) A) a b, Formalism.UG.hform s J a b = (s ∘ a) ⬝ᵥ J *ᵥ b := by
    intro J a b
    simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, Function.comp_apply, mul_assoc]
  have e3 : s ∘ (k *ᵥ a) = (s ∘ a) ᵥ* Formalism.UG.cT s k := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose, Function.comp_apply, RingHom.map_mulVec]
  rw [e2, e2, e3, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

theorem eventually_unitClass_isom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin r → Fv F v ⊗[F] E)) (h : IsIsom P (Fv F v) J (1 : plusUnits P (Fv F v)).1.1 φ), gam h ∈ stabLoc σ J L v ∧ ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  intro F E _ _ _ _ _ σ hcm r P J hJ L _
  have := isLattice_stdLattice (E := E) (n := r)
  filter_upwards [GlobalTheory.T.traceFormGramPowerBasis_hermitian_nondegenerate F E σ hcm r P |> fun hH => GlobalTheory.T.eventually_hermitian_integrally_congruent_cmExt F E σ hcm r J (gramOne P) hJ hH,
    eventually_latLoc_eq F L (stdLattice E r), GlobalTheory.T.eventually_localIntegers_iff_powerBasisCoords_all F E σ r P, GlobalTheory.TrUnitLat.alpha_mem_stab F E σ r P] with v hu hL h3 h4
  obtain ⟨u, hu, hul⟩ := hu
  let φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin r → Fv F v ⊗[F] E) :=
    (coordEquiv P (Fv F v)).trans (Matrix.toLinearEquiv' u.1 (Units.invertible u))
  have eφ : ∀ y, φ y = u.1 *ᵥ coordEquiv P (Fv F v) y := fun y => rfl
  have hφ : IsIsom P (Fv F v) J (1 : plusUnits P (Fv F v)).1.1 φ := fun y y' => by
    rw [eφ, eφ, hform_mulVec', hu]
    exact GlobalTheory.T.powerBasisCoords_isTorusHermitianIsometry F E σ r P (Fv F v) y y'
  have h5 : ∀ y, y ∈ intLoc F (Fld P) v ↔ φ y ∈ latLoc F L v := fun y => by
    rw [eφ, hL, hul, h3]
  exact ⟨φ, hφ, (GlobalTheory.TrUnitLat.stab_torEmb_iff F E σ r r P v J L _ φ hφ h5 _).2 h4, GlobalTheory.TrUnitLat.stab_torEmb_iff F E σ r r P v J L _ φ hφ h5⟩

end GlobalTheory.TrUnitLat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyUnitClassRealizedByLatticeIsometryStatement

section

@[expose] public section

open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

theorem _root_.GlobalTheory.T.eventually_unitClass_realized_by_lattice_isometry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r : ℕ) (P : PPol σ r) (J : Matrix (Fin r) (Fin r) E), IsHermND σ J → ∀ (L : Submodule (𝓞 E) (Fin r → E)) [Submodule.IsFullLattice E L], ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∃ (φ : (Fv F v ⊗[F] Fld P) ≃ₗ[Fv F v ⊗[F] E] (Fin r → Fv F v ⊗[F] E)) (h : IsIsom P (Fv F v) J (1 : plusUnits P (Fv F v)).1.1 φ), gam h ∈ stabLoc σ J L v ∧ ∀ t, torEmb h t ∈ stabLoc σ J L v ↔ t ∈ stabLoc (star' P) (one₁ P) (stdLattice (Fld P) 1) v := by
  first | exact @GlobalTheory.TrUnitLat.eventually_unitClass_isom | exact GlobalTheory.TrUnitLat.eventually_unitClass_isom | (intros; apply GlobalTheory.TrUnitLat.eventually_unitClass_isom <;> assumption)
end
end
