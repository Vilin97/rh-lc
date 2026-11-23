module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyEntriesConjLeftRightMul
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelFun
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.PiTensorProduct
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.KFacts

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelSpace

section

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def rtr (ε : Fin n → Bool) (k : KG ε) : (KG ε → ℂ) →ₗ[ℂ] (KG ε → ℂ) where
  toFun f := fun x => f (x * k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rtr_mul (ε : Fin n → Bool) (k₁ k₂ : KG ε) (f : KG ε → ℂ) : rtr ε (k₁ * k₂) f = rtr ε k₁ (rtr ε k₂ f) := by
  funext x
  show f (x * (k₁ * k₂)) = f (x * k₁ * k₂)
  rw [mul_assoc]

theorem rtr_one (ε : Fin n → Bool) (f : KG ε → ℂ) : rtr ε 1 f = f := by
  funext x
  show f (x * 1) = f x
  rw [mul_one]

def Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) : Submodule ℂ (KG ε → ℂ) :=
  Submodule.span ℂ (Set.range fun k : KG ε => rtr ε k (f0K ε m))

theorem highest_weight_fn_mem_space (ε : Fin n → Bool) (m : Fin n → ℤ) : f0K ε m ∈ Vsp ε m := by
  have h : rtr ε 1 (f0K ε m) ∈ Vsp ε m := Submodule.subset_span ⟨1, rfl⟩
  rwa [rtr_one] at h

theorem rtr_mem (ε : Fin n → Bool) (m : Fin n → ℤ) (k : KG ε) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    rtr ε k f ∈ Vsp ε m := by
  have h : Vsp ε m ≤ (Vsp ε m).comap (rtr ε k) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k', rfl⟩
    show rtr ε k (rtr ε k' (f0K ε m)) ∈ Vsp ε m
    rw [← rtr_mul]
    exact Submodule.subset_span ⟨k * k', rfl⟩
  exact h hf

def evalK (ε : Fin n → Bool) : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] (KG ε → ℂ) :=
  MvPolynomial.aeval fun p : Fin n × Fin n => fun k : KG ε => toMK k p.1 p.2

def polyK (ε : Fin n → Bool) (D : ℕ) : Submodule ℂ (KG ε → ℂ) :=
  (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap

theorem evalK_apply (ε : Fin n → Bool) (Q : MvPolynomial (Fin n × Fin n) ℂ) (x : KG ε) :
    evalK ε Q x = MvPolynomial.aeval (fun p : Fin n × Fin n => toMK x p.1 p.2) Q := by
  induction Q using MvPolynomial.induction_on
  next a => simp [evalK]
  next p q hp hq => rw [map_add (f := _), map_add (f := _), Pi.add_apply, hp, hq]
  next p i hp =>
    rw [map_mul, map_mul, Pi.mul_apply, hp]
    simp [evalK]

def rsub (ε : Fin n → Bool) (k : KG ε) : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℂ :=
  fun p => ∑ l, MvPolynomial.X (p.1, l) * MvPolynomial.C (toMK k l p.2)

theorem toMK_mul' (ε : Fin n → Bool) (x k : KG ε) : toMK (x * k) = toMK x * toMK k := rfl

theorem rtr_evalK (ε : Fin n → Bool) (k : KG ε) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    rtr ε k (evalK ε Q) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) := by
  funext x
  show evalK ε Q (x * k) = evalK ε (MvPolynomial.bind₁ (rsub ε k) Q) x
  rw [evalK_apply, evalK_apply, MvPolynomial.aeval_bind₁]
  refine congrArg (fun g => MvPolynomial.aeval g Q) ?_
  funext p
  simp [rsub, toMK_mul', Matrix.mul_apply]

theorem totalDegree_rsub (ε : Fin n → Bool) (k : KG ε) (p : Fin n × Fin n) :
    (rsub ε k p).totalDegree ≤ 1 := by
  simp only [rsub]
  refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun l _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]

theorem totalDegree_bind₁_le {σ τ : Type*} (g : σ → MvPolynomial τ ℂ) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial σ ℂ) : (MvPolynomial.bind₁ g Q).totalDegree ≤ Q.totalDegree := by
  apply GlobalTheory.PolyEntryMul.totalDegree_bind₁_le_of_le_one <;> assumption

theorem rtr_polyK (ε : Fin n → Bool) (k : KG ε) (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    rtr ε k (evalK ε Q) ∈ polyK ε Q.totalDegree := by
  rw [rtr_evalK]
  exact Submodule.mem_map_of_mem ((MvPolynomial.mem_restrictTotalDegree ..).mpr
    (totalDegree_bind₁_le _ (totalDegree_rsub ε k) Q))

def f0P (ε : Fin n → Bool) (m : Fin n → ℤ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∏ a, ((Matrix.mvPolynomialX (Fin n) (Fin n) ℂ).submatrix
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))
    (fun b : {b : Fin n // ε b = ε a ∧ b ≤ a} => (b : Fin n))).det ^ (mexp ε m a).toNat

theorem evalK_f0P (ε : Fin n → Bool) (m : Fin n → ℤ) : evalK ε (f0P ε m) = f0K ε m := by
  funext k
  rw [evalK_apply]
  show _ = f0 ε m (toMK k)
  simp only [f0P, f0, blkMinor, map_prod, map_pow]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  rw [AlgHom.map_det]
  congr 1
  ext i j
  simp [Matrix.mvPolynomialX]

theorem Vsp_le_polyK (ε : Fin n → Bool) (m : Fin n → ℤ) : ∃ D : ℕ, Vsp ε m ≤ polyK ε D := by
  refine ⟨(f0P ε m).totalDegree, Submodule.span_le.mpr ?_⟩
  rintro _ ⟨k, rfl⟩
  show rtr ε k (f0K ε m) ∈ polyK ε _
  rw [← evalK_f0P]
  exact rtr_polyK ε k (f0P ε m)

theorem finiteDimensional_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) : FiniteDimensional ℂ (Vsp ε m) := by
  obtain ⟨D, hD⟩ := Vsp_le_polyK ε m
  haveI : FiniteDimensional ℂ (polyK ε D) := by
    unfold polyK
    infer_instance
  exact Submodule.finiteDimensional_of_le hD

theorem differentiable_aeval_entries (Q : MvPolynomial (Fin n × Fin n) ℂ) :
    Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ =>
      MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q) := by
  induction Q using MvPolynomial.induction_on
  next a => simp
  next p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  next p i hp =>
    have hX : Differentiable ℂ (fun M : Matrix (Fin n) (Fin n) ℂ => M i.1 i.2) := by
      fun_prop
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul hX

theorem Vsp_holo (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, Differentiable ℂ F ∧ ∀ k, f k = F (toMK k) := by
  obtain ⟨D, hD⟩ := Vsp_le_polyK ε m
  have h' : f ∈ (MvPolynomial.restrictTotalDegree (Fin n × Fin n) ℂ D).map (evalK ε).toLinearMap := hD hf
  obtain ⟨Q, -, rfl⟩ := Submodule.mem_map.mp h'
  exact ⟨fun M => MvPolynomial.aeval (fun p : Fin n × Fin n => M p.1 p.2) Q,
    differentiable_aeval_entries Q, fun k => evalK_apply ε Q k⟩

theorem continuous_of_mem_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m) :
    Continuous f := by
  obtain ⟨F, hF, hfF⟩ := Vsp_holo ε m hf
  have hfe : f = fun k => F (toMK k) := funext hfF
  rw [hfe]
  refine hF.continuous.comp ?_
  fun_prop

theorem hasDerivAt_of_mem_Vsp (ε : Fin n → Bool) (m : Fin n → ℤ) {f : KG ε → ℂ} (hf : f ∈ Vsp ε m)
    {F : Matrix (Fin n) (Fin n) ℂ → ℂ} (hF : Differentiable ℂ F) (hfF : ∀ k, f k = F (toMK k))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (x : KG ε) :
    HasDerivAt (fun t : ℝ => f (x * kcurve ε X t)) (fderiv ℂ F (toMK x) (toMK x * X)) 0 := by
  have hc : HasDerivAt (fun t : ℝ => toMK (kcurve ε X t)) X 0 := by
    have hk : ∀ t : ℝ, toMK (kcurve ε X t) = NormedSpace.exp ((t : ℝ) • X) := fun t => by
       unfold kcurve
       rw [dite_eq_left hX, Classical.choose_spec (exists_curve ε hX) t, Complex.coe_smul]
    simp only [hk]
    letI iR : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℝ ℂ _
    haveI : @CompleteSpace (Matrix (Fin n) (Fin n) ℂ)
        (@PseudoMetricSpace.toUniformSpace _ (@MetricSpace.toPseudoMetricSpace _ (@NormedRing.toMetricSpace _ iR))) := by
      exact FiniteDimensional.complete ℂ _
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (toMK x))
  have hin : HasDerivAt (fun t : ℝ => L (toMK (kcurve ε X t))) (L X) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 hc
  have h0 : toMK (kcurve ε X 0) = 1 := by
    unfold kcurve
    rw [dite_eq_left hX, Classical.choose_spec (exists_curve ε hX) 0]
    simp
  have hLx : L (toMK (kcurve ε X 0)) = toMK x := by
    rw [h0]
    exact mul_one _
  have hF' := ((hF (toMK x)).hasFDerivAt.restrictScalars ℝ)
  rw [← hLx] at hF'
  have hcomp := hF'.comp_hasDerivAt (0 : ℝ) hin
  have hfun : (fun t : ℝ => f (x * kcurve ε X t)) = fun t => F (L (toMK (kcurve ε X t))) := by
    funext t
    rw [hfF, toMK_mul']
    rfl
  rw [hfun]
  rw [hLx] at hcomp
  exact hcomp

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelInner

section

@[expose] public section

noncomputable section

open Matrix MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

def MV (ε : Fin n → Bool) (m : Fin n → ℤ) : Type := ↥(Vsp ε m)

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : AddCommGroup (MV ε m) := inferInstanceAs (AddCommGroup ↥(Vsp ε m))

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : Module ℂ (MV ε m) := inferInstanceAs (Module ℂ ↥(Vsp ε m))

def MV.fn {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : KG ε → ℂ := ((show ↥(Vsp ε m) from f) : KG ε → ℂ)

def MV.mk {ε : Fin n → Bool} {m : Fin n → ℤ} (f : KG ε → ℂ) (hf : f ∈ Vsp ε m) : MV ε m :=
  (⟨f, hf⟩ : ↥(Vsp ε m))

theorem MV.mem {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : f.fn ∈ Vsp ε m := by
  exact (show ↥(Vsp ε m) from f).2

theorem MV.ext {ε : Fin n → Bool} {m : Fin n → ℤ} {f g : MV ε m} (h : f.fn = g.fn) : f = g := by
  exact Subtype.ext h

@[simp] theorem MV.fn_add {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : (f + g).fn = f.fn + g.fn := rfl

@[simp] theorem MV.fn_smul {ε : Fin n → Bool} {m : Fin n → ℤ} (c : ℂ) (f : MV ε m) : (c • f).fn = c • f.fn := rfl

@[simp] theorem MV.fn_zero {ε : Fin n → Bool} {m : Fin n → ℤ} : (0 : MV ε m).fn = 0 := rfl

def mvInner {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) : ℂ :=
  ∫ x, starRingEnd ℂ (f.fn x) * g.fn x ∂(muK ε)

theorem MV.continuous_fn {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : Continuous f.fn := by
  exact continuous_of_mem_Vsp ε m f.mem

theorem integrable_of_continuous_KG {ε : Fin n → Bool} {F : KG ε → ℂ} (hF : Continuous F) :
    MeasureTheory.Integrable F (muK ε) := by

  have := compactSpace_KG ε
  exact hF.integrable_of_hasCompactSupport (isClosed_tsupport F).isCompact

theorem mvInner_integrable {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) :
    MeasureTheory.Integrable (fun x => starRingEnd ℂ (f.fn x) * g.fn x) (muK ε) := by
  exact integrable_of_continuous_KG
    ((Complex.continuous_conj.comp f.continuous_fn).mul g.continuous_fn)

theorem mvInner_self_eq {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) :
    mvInner f f = ((∫ x, Complex.normSq (f.fn x) ∂(muK ε) : ℝ) : ℂ) := by
  unfold mvInner
  simp_rw [← Complex.normSq_eq_conj_mul_self]
  exact integral_ofReal

theorem mvInner_conj {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) :
    starRingEnd ℂ (mvInner g f) = mvInner f g := by
  unfold mvInner
  rw [← integral_conj]
  congr 1
  funext x
  simp only [map_mul, starRingEnd_apply, star_star]
  exact mul_comm _ _

theorem mvInner_re_nonneg {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) : 0 ≤ (mvInner f f).re := by
  rw [mvInner_self_eq, Complex.ofReal_re]
  exact integral_nonneg fun x => Complex.normSq_nonneg _

theorem mvInner_add_left {ε : Fin n → Bool} {m : Fin n → ℤ} (f g h : MV ε m) :
    mvInner (f + g) h = mvInner f h + mvInner g h := by
  simp only [mvInner, MV.fn_add, Pi.add_apply, map_add (f := _), add_mul]
  exact integral_add (mvInner_integrable f h) (mvInner_integrable g h)

theorem mvInner_smul_left {ε : Fin n → Bool} {m : Fin n → ℤ} (f g : MV ε m) (c : ℂ) :
    mvInner (c • f) g = starRingEnd ℂ c * mvInner f g := by
  simp only [mvInner, MV.fn_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  exact integral_const_mul _ _

theorem mvInner_definite {ε : Fin n → Bool} {m : Fin n → ℤ} (f : MV ε m) (h : mvInner f f = 0) : f = 0 := by

  have hc : Continuous fun x => Complex.normSq (f.fn x) :=
    Complex.continuous_normSq.comp f.continuous_fn
  rw [mvInner_self_eq, Complex.ofReal_eq_zero] at h
  have hae : (fun x => Complex.normSq (f.fn x)) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg _)
      (by
        have := compactSpace_KG ε
        exact hc.integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact)).mp h
  have hz : (fun x => Complex.normSq (f.fn x)) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hc continuous_const).mp hae
  apply MV.ext
  funext x
  simpa using congrFun hz x

@[instance_reducible]
def mvCore (ε : Fin n → Bool) (m : Fin n → ℤ) : InnerProductSpace.Core ℂ (MV ε m) where
  inner := mvInner
  conj_inner_symm := mvInner_conj
  re_inner_nonneg := mvInner_re_nonneg
  add_left := mvInner_add_left
  smul_left := mvInner_smul_left
  definite := mvInner_definite

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : NormedAddCommGroup (MV ε m) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (MV ε m) _ _ _ (mvCore ε m)

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : InnerProductSpace ℂ (MV ε m) :=
  InnerProductSpace.ofCore (mvCore ε m).toCore

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : FiniteDimensional ℂ (MV ε m) :=
  finiteDimensional_Vsp ε m

instance (ε : Fin n → Bool) (m : Fin n → ℤ) : CompleteSpace (MV ε m) := FiniteDimensional.complete ℂ _

end ReciprocityTheory.ChartRestriction.DS.HW
end
end
end
