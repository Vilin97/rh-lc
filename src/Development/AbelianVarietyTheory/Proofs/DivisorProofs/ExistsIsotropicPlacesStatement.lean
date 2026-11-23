module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactSetUnitaryHermitianRealStatement
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalVectorIsotropicNondegeneratePlanesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactSpecialUnitarySupportedAtPlacesStatement
public import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtA
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Anisotropic
import GroundTheory.GlobalFields.IdeleGroups.UnitBound
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionAdelicFromArchimedean

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

noncomputable section
namespace GlobalTheory
open Classical

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

theorem ainf_single_mul (a b : w.Completion) :
    (show Ainf F from Pi.single w (a * b)) = (show Ainf F from Pi.single w a) * (show Ainf F from Pi.single w b) := by
  funext u
  change (Pi.single w (a*b) : ∀ v : InfinitePlace F, v.Completion) u =
    (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w b : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

theorem ainf_idem_mul (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) (a : w.Completion) :
    e * (show Ainf F from Pi.single w a) = (show Ainf F from Pi.single w a) := by
  funext u
  change (e : ∀ v : InfinitePlace F, v.Completion) u * (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u = (Pi.single w a : ∀ v : InfinitePlace F, v.Completion) u
  by_cases h : u = w
  · subst h; rw [h1, one_mul]
  · simp only [Pi.single_eq_of_ne h, mul_zero]

theorem ainf_single_one (e : Ainf F) (h1 : e w = 1) (h0 : ∀ u, u ≠ w → e u = 0) :
    (show Ainf F from Pi.single w 1) = e := by
  funext u
  change (Pi.single w 1 : ∀ v : InfinitePlace F, v.Completion) u = e u
  by_cases h : u = w
  · subst h; rw [h1, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne h, h0 u h]

theorem af_zero (y : Af F) (h : ∀ v, evalV F v y = 0) : y = 0 := by
  ext v
  exact congrArg _ (h v)

theorem af_ext {p q : AF F} (h1 : fstA F p = fstA F q) (h2 : sndA F p = sndA F q) : p = q :=
  Prod.ext h1 h2

def placeAtInf : w.Completion →ₗ[F] AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).comp (LinearMap.single F (fun u : InfinitePlace F => u.Completion) w)

theorem fstA_placeAtInf (a : w.Completion) : fstA F (placeAtInf F w a) = (show Ainf F from Pi.single w a) := rfl
theorem sndA_placeAtInf (a : w.Completion) : sndA F (placeAtInf F w a) = 0 := rfl

theorem placeAtInf_mul (a b : w.Completion) :
    placeAtInf F w (a * b) = placeAtInf F w a * placeAtInf F w b := by
  apply af_ext
  · have e2 : fstA F (placeAtInf F w a * placeAtInf F w b) =
        fstA F (placeAtInf F w a) * fstA F (placeAtInf F w b) := map_mul (fstA F) _ _
    exact (fstA_placeAtInf F w (a * b)).trans ((ainf_single_mul F w a b).trans
      (e2.trans (congrArg₂ (· * ·) (fstA_placeAtInf F w a) (fstA_placeAtInf F w b))).symm)
  · have e2 : sndA F (placeAtInf F w a * placeAtInf F w b) =
        sndA F (placeAtInf F w a) * sndA F (placeAtInf F w b) := map_mul (sndA F) _ _
    exact (sndA_placeAtInf F w (a * b)).trans ((mul_zero (0 : Af F)).symm.trans
      (e2.trans (congrArg₂ (· * ·) (sndA_placeAtInf F w a) (sndA_placeAtInf F w b))).symm)

variable {F w}

theorem idem_mul_placeAtInf {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (a : w.Completion) :
    ε * placeAtInf F w a = placeAtInf F w a := by
  apply af_ext
  · have e2 : fstA F (ε * placeAtInf F w a) = fstA F ε * fstA F (placeAtInf F w a) := map_mul (fstA F) _ _
    exact e2.trans ((congrArg (fstA F ε * ·) (fstA_placeAtInf F w a)).trans
      ((ainf_idem_mul F w _ (hε.1 w (Finset.mem_singleton_self w))
        (fun u hu => hε.2.1 u (by simpa using hu)) a).trans (fstA_placeAtInf F w a).symm))
  · have e2 : sndA F (ε * placeAtInf F w a) = sndA F ε * sndA F (placeAtInf F w a) := map_mul (sndA F) _ _
    exact e2.trans ((congrArg (sndA F ε * ·) (sndA_placeAtInf F w a)).trans
      ((mul_zero _).trans (sndA_placeAtInf F w a).symm))

theorem placeAtInf_one {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) : placeAtInf F w 1 = ε := by
  apply af_ext
  · refine (fstA_placeAtInf F w 1).trans ?_
    exact ainf_single_one F w _ (hε.1 w (Finset.mem_singleton_self w))
      (fun u hu => hε.2.1 u (by simpa using hu))
  · refine (sndA_placeAtInf F w 1).trans ?_
    exact (af_zero F _ (fun v => hε.2.2.2 v (Finset.notMem_empty v))).symm

variable (F w) (E : Type) [Field E] [Algebra F E]

def placeAtInfE : w.Completion ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  LinearMap.rTensor E (placeAtInf F w)

theorem placeAtInfE_tmul (a : w.Completion) (e : E) :
    placeAtInfE F w E (a ⊗ₜ e) = placeAtInf F w a ⊗ₜ e := rfl

theorem placeAtInfE_mul (x y : w.Completion ⊗[F] E) :
    placeAtInfE F w E (x * y) = placeAtInfE F w E x * placeAtInfE F w E y := by
  induction x using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, zero_mul]
  | add a b ha hb => rw [add_mul, map_add (f := _), map_add (f := _), ha, hb, add_mul]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => rw [mul_zero, map_zero, mul_zero]
    | add c d hc hd => rw [mul_add, map_add (f := _), map_add (f := _), hc, hd, mul_add]
    | tmul b f =>
      unfold placeAtInfE
      rw [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
        LinearMap.rTensor_tmul, Algebra.TensorProduct.tmul_mul_tmul, placeAtInf_mul]

theorem placeAtInfE_sig (σ : E →ₐ[F] E) (x : w.Completion ⊗[F] E) :
    placeAtInfE F w E (sigR w.Completion σ x) = sigR (AF F) σ (placeAtInfE F w E x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, placeAtInfE_tmul]

variable {F w E}

theorem idem_mul_placeAtInfE {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (x : w.Completion ⊗[F] E) :
    algebraMap (AF F) (AF F ⊗[F] E) ε * placeAtInfE F w E x = placeAtInfE F w E x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [mul_add, map_add (f := _), h₁, h₂]
  | tmul a e =>
    rw [placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, Algebra.algebraMap_self, RingHom.id_apply, idem_mul_placeAtInf hε]

theorem placeAtInfE_incl {ε : AF F} (hε : IsPlacesIdem {w} ∅ ε) (c : E) :
    placeAtInfE F w E (inclR w.Completion c) = algebraMap (AF F) (AF F ⊗[F] E) ε * inclR (AF F) c := by
  simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    placeAtInfE_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_one, Algebra.algebraMap_self, RingHom.id_apply, placeAtInf_one hε]

theorem normEq_inf_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : InfinitePlace F) (ε : AF F), IsPlacesIdem {w} ∅ ε → ∀ c : E,
    (∃ t : w.Completion ⊗[F] E, t * sigR w.Completion σ t + inclR w.Completion c = 0) →
    ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  intro F E _ _ _ _ σ w ε hε c ⟨t, ht⟩
  refine ⟨placeAtInfE F w E t, ?_⟩
  rw [← placeAtInfE_sig, ← placeAtInfE_mul, mul_add, idem_mul_placeAtInfE hε, ← placeAtInfE_incl hε,
    ← map_add, ht, map_zero]

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormSolutionAdelicFromArchimedeanStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_norm_solution_adelic_from_archimedean : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (w : InfinitePlace F) (ε : AF F), IsPlacesIdem {w} ∅ ε → ∀ c : E, (∃ t : w.Completion ⊗[F] E, t * sigR w.Completion σ t + inclR w.Completion c = 0) → ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  first | exact @GlobalTheory.normEq_inf_place | exact GlobalTheory.normEq_inf_place | (intros; apply GlobalTheory.normEq_inf_place <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdelicNormEqOfLocalNormEq

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open GlobalTheory.Published.StrongApprox
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.NormFin

variable {F : Type} [Field F] [NumberField F]

theorem af_ext {x y : Af F} (h : ∀ w, evalV F w x = evalV F w y) : x = y :=
  by
  apply RestrictedProduct.ext
  intro w
  exact h w

def iotaL (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F where
  toFun a := pairA F 0 (singleV F v a)
  map_add' a b := by
    refine Prod.ext (by change (0 : Ainf F) = 0 + 0; simp) ?_
    change singleV F v (a + b) = singleV F v a + singleV F v b
    refine af_ext fun w => ?_
    rw [map_add (f := _)]
    by_cases hw : w = v
    · subst hw; simp only [evalV_single_same]
    · simp only [evalV_single_ne hw, add_zero]
  map_smul' c a := by
    refine Prod.ext (by change (0 : Ainf F) = c • 0; simp) ?_
    change singleV F v (c • a) = c • singleV F v a
    refine af_ext fun w => ?_
    rw [map_smul]
    by_cases hw : w = v
    · subst hw; simp only [evalV_single_same]
    · simp only [evalV_single_ne hw, smul_zero]

theorem iotaL_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) :
    iotaL v (a * b) = iotaL v a * iotaL v b := by
  refine Prod.ext (by change (0 : Ainf F) = 0 * 0; simp) ?_
  change singleV F v (a * b) = singleV F v a * singleV F v b
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; simp only [evalV_single_same]
  · simp only [evalV_single_ne hw, mul_zero]

theorem idem_mul_iotaL (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) (a : Fv F v) :
    ε * iotaL v a = iotaL v a := by
  refine Prod.ext (by change fstA F ε * 0 = 0; simp) ?_
  change sndA F ε * singleV F v a = singleV F v a
  refine af_ext fun w => ?_
  rw [map_mul]
  by_cases hw : w = v
  · subst hw; rw [hε.2.2.1 w (Finset.mem_singleton_self w), one_mul]
  · simp only [evalV_single_ne hw, mul_zero]

theorem iotaL_one (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) :
    iotaL v 1 = ε := by
  refine Prod.ext ?_ ?_
  · funext w
    exact (hε.2.1 w (Finset.notMem_empty w)).symm
  · change singleV F v 1 = sndA F ε
    refine af_ext fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [evalV_single_same, hε.2.2.1 w (Finset.mem_singleton_self w)]
    · rw [evalV_single_ne hw, hε.2.2.2 w (fun h => hw (Finset.mem_singleton.1 h))]

section Tensor

variable {E : Type} [Field E] [Algebra F E]

def phi (v : HeightOneSpectrum (𝓞 F)) : Fv F v ⊗[F] E →ₗ[F] AF F ⊗[F] E :=
  TensorProduct.map (iotaL v) LinearMap.id

theorem phi_tmul (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (e : E) :
    phi v (a ⊗ₜ[F] e) = iotaL v a ⊗ₜ[F] e := TensorProduct.map_tmul _ _ _ _

theorem phi_mul (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v ⊗[F] E) :
    phi v (x * y) = phi v x * phi v y := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b f =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, phi_tmul, phi_tmul, phi_tmul, iotaL_mul,
        Algebra.TensorProduct.tmul_mul_tmul]
    | add y z hy hz => rw [mul_add, map_add (f := _), hy, hz, map_add (f := _), mul_add]
  | add x z hx hz => rw [add_mul, map_add (f := _), hx, hz, map_add (f := _), add_mul]

theorem phi_sig (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v ⊗[F] E) :
    phi v (sigR (Fv F v) σ x) = sigR (AF F) σ (phi v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.coe_id, id_eq, phi_tmul]
  | add x z hx hz => rw [map_add (f := _), map_add (f := _), hx, hz, map_add (f := _), map_add (f := _)]

theorem idem_mul_phi (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε)
    (x : Fv F v ⊗[F] E) : algebraMap (AF F) (AF F ⊗[F] E) ε * phi v x = phi v x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, phi_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, idem_mul_iotaL v ε hε]
  | add x z hx hz => rw [map_add (f := _), mul_add, hx, hz]

theorem phi_inclR (v : HeightOneSpectrum (𝓞 F)) (ε : AF F) (hε : IsPlacesIdem ∅ {v} ε) (c : E) :
    phi v (inclR (Fv F v) c) = algebraMap (AF F) (AF F ⊗[F] E) ε * inclR (AF F) c := by
  change phi v ((1 : Fv F v) ⊗ₜ[F] c) = algebraMap (AF F) (AF F ⊗[F] E) ε * ((1 : AF F) ⊗ₜ[F] c)
  rw [phi_tmul, iotaL_one v ε hε, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

end Tensor

theorem idem_norm_eq_of_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlacesIdem ∅ {v} ε → ∀ c : E,
    (∃ t : Fv F v ⊗[F] E, t * sigR (Fv F v) σ t + inclR (Fv F v) c = 0) →
    ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  intro F E _ _ _ _ σ v ε hε c ⟨t, ht⟩
  refine ⟨phi v t, ?_⟩
  rw [← phi_sig, ← phi_mul, mul_add, idem_mul_phi v ε hε, ← phi_inclR v ε hε, ← map_add (f := _), ht, map_zero]

end GlobalTheory.NormFin
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentAdelicNormEqOfLocalNormEqStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.idempotent_adelic_norm_eq_of_local_norm_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlacesIdem ∅ {v} ε → ∀ c : E, (∃ t : Fv F v ⊗[F] E, t * sigR (Fv F v) σ t + inclR (Fv F v) c = 0) → ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) c) = 0 := by
  first | exact @GlobalTheory.NormFin.idem_norm_eq_of_local | exact GlobalTheory.NormFin.idem_norm_eq_of_local | (intros; apply GlobalTheory.NormFin.idem_norm_eq_of_local <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlaces

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

namespace GlobalTheory.PlaceIso

theorem denseRange_algebraMap_completion : ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), DenseRange (algebraMap F w.Completion) := by
  intro F _ _ w y
  have h := InfinitePlace.Completion.denseRange_coe w y
  convert h using 2
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨(WithAbs.equiv w.1).symm x, ?_⟩
    simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]
  · rintro ⟨x, rfl⟩
    refine ⟨WithAbs.equiv w.1 x, ?_⟩
    simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]

theorem exists_isotropic_places : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) := by
  intro F E _ _ _ _ _ σ hσ M J hM hJ S₁ S₂ ε hε hnc
  classical
  have key : (∃ w ∈ S₁, ∃ u : Fin M → w.Completion ⊗[F] E, u ≠ 0 ∧ hR w.Completion σ J u u = 0) ∨
      (∃ v ∈ S₂, ∃ u : Fin M → Fv F v ⊗[F] E, u ≠ 0 ∧ hR (Fv F v) σ J u u = 0) := by
    by_contra hno
    push_neg at hno
    apply hnc
    apply GlobalTheory.T.isCompact_specialUnitary_supportedAtPlaces F E σ hσ M J hJ S₁ S₂ ε hε
    · intro w hw
      letI := GroundTheory.Automorphic.completionNontriviallyNormedField (K := F) w
      exact GlobalTheory.T.exists_compact_set_unitary_hermitian_real F E σ hσ w.Completion M J hJ (fun u hu => by
        by_contra h
        exact hno.1 w hw u h hu)
    · intro v hv
      letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
      haveI := Formalism.BasicNotions.Examples₂.LocF.proper v
      exact GlobalTheory.T.exists_compact_set_unitary_hermitian_real F E σ hσ (Fv F v) M J hJ (fun u hu => by
        by_contra h
        exact hno.2 v hv u h hu)
  rcases key with ⟨w, hw, u, hu0, hu⟩ | ⟨v, hv, u, hu0, hu⟩
  · obtain ⟨ε', hε'⟩ := GlobalTheory.Published.StrongApprox.exists_isPlacesIdem (F := F) {w} ∅
    refine ⟨{w}, ∅, ε', Finset.singleton_subset_iff.2 hw, Finset.empty_subset _,
      Or.inl (Finset.singleton_nonempty w), hε', ?_⟩
    intro x y hx hy
    letI := GroundTheory.Automorphic.completionNontriviallyNormedField (K := F) w
    obtain ⟨z, hz, ⟨h1, ht1⟩, ⟨h2, ht2⟩⟩ :=
      GlobalTheory.T.exists_rational_vector_isotropic_nondegenerate_planes_at_place F E σ hσ w.Completion (denseRange_algebraMap_completion F w) M J hM hJ ⟨u, hu0, hu⟩ x y hx hy
    exact ⟨z, hz, ⟨h1, GlobalTheory.T.exists_norm_solution_adelic_from_archimedean F E σ w ε' hε' _ ht1⟩, ⟨h2, GlobalTheory.T.exists_norm_solution_adelic_from_archimedean F E σ w ε' hε' _ ht2⟩⟩
  · obtain ⟨ε', hε'⟩ := GlobalTheory.Published.StrongApprox.exists_isPlacesIdem (F := F) ∅ {v}
    refine ⟨∅, {v}, ε', Finset.empty_subset _, Finset.singleton_subset_iff.2 hv,
      Or.inr (Finset.singleton_nonempty v), hε', ?_⟩
    intro x y hx hy
    letI : NontriviallyNormedField (v.adicCompletion F) := Valued.toNontriviallyNormedField _ _
    obtain ⟨z, hz, ⟨h1, ht1⟩, ⟨h2, ht2⟩⟩ :=
      GlobalTheory.T.exists_rational_vector_isotropic_nondegenerate_planes_at_place F E σ hσ (Fv F v) (HeightOneSpectrum.denseRange_algebraMap F v) M J hM hJ ⟨u, hu0, hu⟩ x y hx hy
    exact ⟨z, hz, ⟨h1, GlobalTheory.T.idempotent_adelic_norm_eq_of_local_norm_eq F E σ v ε' hε' _ ht1⟩, ⟨h2, GlobalTheory.T.idempotent_adelic_norm_eq_of_local_norm_eq F E σ v ε' hε' _ ht2⟩⟩
end GlobalTheory.PlaceIso
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicPlacesStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_isotropic_places_alt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), 2 ≤ M → IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → ¬ IsCompact (SUSupp σ J ε) → ∃ (S₁' : Finset (InfinitePlace F)) (S₂' : Finset (HeightOneSpectrum (𝓞 F))) (ε' : AF F), S₁' ⊆ S₁ ∧ S₂' ⊆ S₂ ∧ (S₁'.Nonempty ∨ S₂'.Nonempty) ∧ IsPlacesIdem S₁' S₂' ε' ∧ ∀ x y : Fin M → E, hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → ∃ z : Fin M → E, hE σ J z z ≠ 0 ∧ (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) ∧ (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε' * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) := by
  first | exact @GlobalTheory.PlaceIso.exists_isotropic_places | exact GlobalTheory.PlaceIso.exists_isotropic_places | (intros; apply GlobalTheory.PlaceIso.exists_isotropic_places <;> assumption)
end
end
