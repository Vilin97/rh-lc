module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHaarMeasureOfSigmaFinite
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFintypeProd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupUJHaarRightInvariantStatement
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RankOneTensors
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ParametersTermRelations
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFlagUnipotentRadicalIsUnipotent

section

@[expose] public section

open Matrix

noncomputable section

namespace GlobalTheory.UnipRadNilp

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ}

theorem hJ_sub_right (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε x (y - w) = hJ ε x y - hJ ε x w := by
  unfold hJ; rw [mulVec_sub, dotProduct_sub]

theorem hJ_sub_left (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε (x - y) w = hJ ε x w - hJ ε y w := by
  unfold hJ; rw [star_sub, sub_dotProduct]

theorem hJ_add_left (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε (x + y) w = hJ ε x w + hJ ε y w := by
  unfold hJ; rw [star_add, add_dotProduct]

theorem hJ_smul_left (ε : Fin n → Bool) (c : ℂ) (x w : Fin n → ℂ) : hJ ε (c • x) w = star c * hJ ε x w := by
  unfold hJ; rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_zero_left' (ε : Fin n → Bool) (w : Fin n → ℂ) : hJ ε 0 w = 0 := by
  unfold hJ; simp

theorem orth_span (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (b : ℕ) (w : Fin n → ℂ)
    (hw : ∀ c : Fin r, c.1 < b → hJ ε (e c) w = 0) : ∀ v ∈ spanLt e b, hJ ε v w = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    exact hw c hc
  | zero => exact hJ_zero_left' ε w
  | add x y _ _ hx hy => rw [hJ_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [hJ_smul_left, hx, mul_zero]

theorem spanLt_zero (e : Fin r → Fin n → ℂ) : spanLt e 0 = ⊥ := by
  unfold spanLt
  have : (e '' {b : Fin r | b.1 < 0}) = ∅ := by
    ext x; simp
  rw [this, Submodule.span_empty]

theorem pow_lower (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) {G : Matrix (Fin n) (Fin n) ℂ}
    (hG : InS e z G) (k : ℕ) : ∀ m, ∀ v ∈ spanLt e (m + k), (G - 1) ^ k *ᵥ v ∈ spanLt e m := by
  induction k with
  | zero => intro m v hv; simpa using hv
  | succ k ih =>
    intro m v hv
    have h1 : (G - 1) *ᵥ v ∈ spanLt e (m + k) := by
      have hle : spanLt e (m + (k + 1)) ≤ (spanLt e (m + k)).comap (Matrix.mulVecLin (G - 1)) := by
        unfold spanLt
        rw [Submodule.span_le]
        rintro _ ⟨b, hb, rfl⟩
        have hb' : (b : ℕ) < m + (k + 1) := hb
        simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
        refine Submodule.span_mono ?_ (hG.1 b)
        rintro _ ⟨c, hc, rfl⟩
        have hc' : (c : ℕ) < b := hc
        exact ⟨c, show (c : ℕ) < m + k by omega, rfl⟩
      exact hle hv
    rw [pow_succ, ← mulVec_mulVec]
    exact ih m _ h1

theorem nilp (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε)
    (hg : g ∈ NLoc ε e z) : (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 := by
  set G := Formalism.MainNotions.S.uMat g with hGdef
  have hN : InN ε e z G := hg
  have hS' : InS e z (Formalism.MainNotions.S.uMat g⁻¹) :=
    (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI.SG ε e z).inv_mem hg.1
  have hGG' : G * Formalism.MainNotions.S.uMat g⁻¹ = 1 := Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.uMat_mul_inv ε g
  have hiso := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.isIsom_uMat ε g

  have adj : ∀ b : Fin r, ∀ w, hJ ε (e b) ((G - 1) *ᵥ w) = hJ ε ((Formalism.MainNotions.S.uMat g⁻¹ - 1) *ᵥ e b) w := by
    intro b w
    have h1 : hJ ε (e b) (G *ᵥ w) = hJ ε (Formalism.MainNotions.S.uMat g⁻¹ *ᵥ e b) w := by
      have := hiso (Formalism.MainNotions.S.uMat g⁻¹ *ᵥ e b) w
      rw [mulVec_mulVec, hGG', one_mulVec] at this
      exact this
    rw [sub_mulVec, one_mulVec, hJ_sub_right, h1, sub_mulVec, one_mulVec, hJ_sub_left]

  have step1 : ∀ k, ∀ x, ∀ b : Fin r, b.1 < k → hJ ε (e b) ((G - 1) ^ k *ᵥ x) = 0 := by
    intro k
    induction k with
    | zero => intro x b hb; omega
    | succ k ih =>
      intro x b hb
      rw [pow_succ', ← mulVec_mulVec, adj]
      refine orth_span ε e b.1 _ (fun c hc => ih x c (by omega)) _ (hS'.1 b)
  have step2 : ∀ x, (G - 1) ^ (r + 1) *ᵥ x ∈ spanLt e r := by
    intro x
    rw [pow_succ', ← mulVec_mulVec]
    exact hN.2 _ (fun a => step1 r x a a.2)
  have step3 : ∀ x, (G - 1) ^ (2 * r + 1) *ᵥ x = 0 := by
    intro x
    have : (G - 1) ^ (2 * r + 1) = (G - 1) ^ r * (G - 1) ^ (r + 1) := by
      rw [← pow_add]; ring_nf
    rw [this, ← mulVec_mulVec]
    have hm := pow_lower e z hN.1 r 0 _ (by rw [zero_add]; exact step2 x)
    rw [spanLt_zero] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  ext i j
  have := congrFun (step3 (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

end GlobalTheory.UnipRadNilp

theorem GlobalTheory.unipRad_pow_eq_zero : ∀ {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε), g ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc ε e z → (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 :=
  fun ε e z g hg => GlobalTheory.UnipRadNilp.nilp ε e z g hg
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFlagUnipotentRadicalIsUnipotentStatement

section

@[expose] public section

open Matrix

theorem _root_.GlobalTheory.T.realPlaceFlagUnipotentRadical_isUnipotent : ∀ {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε), g ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc ε e z → (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 := by
  first | exact @GlobalTheory.unipRad_pow_eq_zero | exact GlobalTheory.unipRad_pow_eq_zero | (intros; apply GlobalTheory.unipRad_pow_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocal

section

set_option backward.isDefEq.respectTransparency false

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrbQuotProd

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

theorem norm_rankOneInnerOperator {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] (a : V) (b : V') : ‖Formalism.L2.SG.TermOp.rk1 a b‖ = ‖a‖ * ‖b‖ := by
  unfold Formalism.L2.SG.TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem continuous_rankOneOperator {Y V V' : Type*} [TopologicalSpace Y] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] {f : Y → V} {g : Y → V'} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun y => Formalism.L2.SG.TermOp.rk1 (f y) (g y) := by
  unfold Formalism.L2.SG.TermOp.rk1
  have h1 : Continuous fun y => innerSL ℂ (g y) := (innerSL ℂ).continuous.comp hg
  exact ((StrongDual.smulRightL ℂ V' V).continuous.comp h1).clm_apply hf

def stG {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (γ : Formalism.REAL.UJ ε) :
    Subgroup (Formalism.REAL.UJ ε) where
  carrier := StSet (NLoc ε e z) (NLoc ε e z') γ
  one_mem' := ⟨(Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z).one_mem, by
    have h : γ⁻¹ * 1 * γ = 1 := by group
    show γ⁻¹ * 1 * γ ∈ Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z'
    rw [h]; exact (Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z').one_mem⟩
  mul_mem' {a b} ha hb := ⟨(Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z).mul_mem ha.1 hb.1, by
    have := (Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z').mul_mem ha.2 hb.2
    have h : γ⁻¹ * (a * b) * γ = γ⁻¹ * a * γ * (γ⁻¹ * b * γ) := by group
    show γ⁻¹ * (a * b) * γ ∈ Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z'
    rw [h]; exact this⟩
  inv_mem' {a} ha := ⟨(Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z).inv_mem ha.1, by
    have := (Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z').inv_mem ha.2
    have h : γ⁻¹ * a⁻¹ * γ = (γ⁻¹ * a * γ)⁻¹ := by group
    show γ⁻¹ * a⁻¹ * γ ∈ Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z'
    rw [h]; exact this⟩

theorem stG_closed {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (γ : Formalism.REAL.UJ ε) :
    IsClosed (stG ε e z z' γ : Set (Formalism.REAL.UJ ε)) := by
  have h1 := Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG_closed ε e z
  have h2 := Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG_closed ε e z'
  have hc : Continuous fun y : Formalism.REAL.UJ ε => γ⁻¹ * y * γ := by fun_prop
  exact h1.inter (h2.preimage hc)

end GlobalTheory.OrbQuotProd

namespace GlobalTheory.OrbQuotProd

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
open scoped InnerProductSpace NNReal

theorem lint_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μG μ ν : Measure G) {b : G → ℝ≥0}
    (hb : Measurable b) (h1 : ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂ν)
    {f : G → ℝ≥0∞} (hf : Measurable f) (hi : ∀ᵐ s ∂μ, ∀ x, f (s * x) = f x) :
    ∫⁻ x, f x ∂ν = ∫⁻ x, (b x : ℝ≥0∞) * f x ∂μG := by
  have hb' : Measurable fun x => (b x : ℝ≥0∞) := hb.coe_nnreal_ennreal
  have hm : Measurable fun x => (b x : ℝ≥0∞) * f x := hb'.mul hf
  rw [hν _ hm]
  refine lintegral_congr fun x => ?_
  have e : ∫⁻ s, (b (s * x) : ℝ≥0∞) * f (s * x) ∂μ = ∫⁻ s, (b (s * x) : ℝ≥0∞) * f x ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hi] with s hs
    rw [hs x]
  rw [e, lintegral_mul_const (f := fun s => (b (s * x) : ℝ≥0∞)) _ (hb'.comp (measurable_mul_const x)), h1, one_mul]

theorem quot_prod {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) (R : ∀ i, Subgroup (Formalism.REAL.UJ (ε i)))
    (μl νl : ∀ i, Measure (Formalism.REAL.UJ (ε i))) (ν : Measure (∀ i, Formalism.REAL.UJ (ε i)))
    (hR : ∀ i, IsClosed (R i : Set (Formalism.REAL.UJ (ε i))))
    (hH : ∀ i, IsHaarLoc (R i : Set (Formalism.REAL.UJ (ε i))) (μl i))
    (hr : ∀ i, ∀ s ∈ R i, (μl i).map (fun x => x * s) = μl i) (hQl : ∀ i, IsQuotLoc (μl i) (νl i))
    (hQ : ∀ f : (∀ i, Formalism.REAL.UJ (ε i)) → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂(Measure.pi fun i => Formalism.REAL.muG (ε i)) = ∫⁻ x, ∫⁻ s, f (s * x) ∂(Measure.pi μl) ∂ν) :
    (∀ F : ∀ i, Formalism.REAL.UJ (ε i) → ℝ≥0∞, (∀ i, Measurable (F i)) → (∀ i, ∀ s ∈ R i, ∀ x, F i (s * x) = F i x) →
      ∫⁻ x, ∏ i, F i (x i) ∂ν = ∏ i, ∫⁻ x, F i x ∂(νl i)) ∧
    (∀ F : ∀ i, Formalism.REAL.UJ (ε i) → ℂ, (∀ i, Measurable (F i)) → (∀ i, ∀ s ∈ R i, ∀ x, F i (s * x) = F i x) →
      ∫ x, ∏ i, F i (x i) ∂ν = ∏ i, ∫ x, F i x ∂(νl i)) := by
  have : ∀ i, SigmaFinite (μl i) := fun i => (hH i).1
  choose b hb h1 using fun i => GlobalTheory.SnMass.ProdQuot.exists_cutoff (R i) (μl i) (hR i) (hH i).2.1 (hH i).2.2.1
    (fun s hs => ⟨(hH i).2.2.2 s hs, hr i s hs⟩)
  have hbm : Measurable fun x : (∀ i, Formalism.REAL.UJ (ε i)) => ∏ i, b i (x i) :=
    Finset.measurable_prod _ fun i _ => (hb i).comp (measurable_pi_apply i)
  have hB : ∀ g : (∀ i, Formalism.REAL.UJ (ε i)), ∫⁻ s, ((fun x => ∏ i, b i (x i)) (s * g) : ℝ≥0∞) ∂(Measure.pi μl) = 1 :=
    fun g => by
      have := GlobalTheory.SnMass.Push.lintegral_fintype_prod (μ := μl) (fun i s => (b i (s * g i) : ℝ≥0∞))
        fun i => (hb i).coe_nnreal_ennreal.comp (measurable_mul_const (g i))
      simpa [h1] using this
  have hmem : ∀ i, ∀ᵐ s ∂(μl i), s ∈ (R i : Set (Formalism.REAL.UJ (ε i))) := fun i => (hH i).2.2.1
  refine ⟨fun F hF hFi => ?_, fun F hF hFi => ?_⟩
  · have hl := fun i => lint_eq (Formalism.REAL.muG (ε i)) (μl i) (νl i) (hb i) (h1 i) (hQl i) (hF i)
      (by filter_upwards [hmem i] with s hs using hFi i s hs)
    have hg := lint_eq (Measure.pi fun i => Formalism.REAL.muG (ε i)) (Measure.pi μl) ν hbm hB hQ
      (f := fun x => ∏ i, F i (x i)) (Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i))
      (by
        have : ∀ᵐ s ∂(Measure.pi μl), ∀ i, s i ∈ (R i : Set (Formalism.REAL.UJ (ε i))) :=
          Filter.eventually_all.2 fun i => (Measure.tendsto_eval_ae_ae (μ := μl) (i := i)).eventually (hmem i)
        filter_upwards [this] with s hs x
        exact Finset.prod_congr rfl fun i _ => hFi i (s i) (hs i) (x i))
    rw [hg]
    have e : (fun x : (∀ i, Formalism.REAL.UJ (ε i)) => ((∏ i, b i (x i) : ℝ≥0) : ℝ≥0∞) * ∏ i, F i (x i)) =
        fun x => ∏ i, ((b i (x i) : ℝ≥0∞) * F i (x i)) := by
      ext x
      rw [Finset.prod_mul_distrib]
      push_cast
      rfl
    rw [e, GlobalTheory.SnMass.Push.lintegral_fintype_prod (fun i y => (b i y : ℝ≥0∞) * F i y)
      fun i => (hb i).coe_nnreal_ennreal.mul (hF i)]
    exact Finset.prod_congr rfl fun i _ => (hl i).symm
  · have hl := fun i => GlobalTheory.SnMass.ProdQuot.integral_eq (Formalism.REAL.muG (ε i)) (μl i) (νl i) (hb i) (h1 i) (hQl i)
      (hF i) (by filter_upwards [hmem i] with s hs using hFi i s hs)
    have hg := GlobalTheory.SnMass.ProdQuot.integral_eq (Measure.pi fun i => Formalism.REAL.muG (ε i)) (Measure.pi μl) ν hbm hB hQ
      (F := fun x => ∏ i, F i (x i)) (Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i))
      (by
        have : ∀ᵐ s ∂(Measure.pi μl), ∀ i, s i ∈ (R i : Set (Formalism.REAL.UJ (ε i))) :=
          Filter.eventually_all.2 fun i => (Measure.tendsto_eval_ae_ae (μ := μl) (i := i)).eventually (hmem i)
        filter_upwards [this] with s hs x
        exact Finset.prod_congr rfl fun i _ => hFi i (s i) (hs i) (x i))
    have e : (fun x : (∀ i, Formalism.REAL.UJ (ε i)) => ((∏ i, b i (x i) : ℝ≥0) : ℂ) * ∏ i, F i (x i)) =
        fun x => ∏ i, ((b i (x i) : ℂ) * F i (x i)) := by
      ext x
      rw [Finset.prod_mul_distrib]
      push_cast
      rfl
    rw [hg.1, e, integral_fintype_prod_eq_prod fun i y => (b i y : ℂ) * F i y]
    exact Finset.prod_congr rfl fun i _ => (hl i).1.symm

end GlobalTheory.OrbQuotProd

namespace GlobalTheory.OrbQuotProd

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
open scoped InnerProductSpace NNReal

theorem hsNormSq_eq_hs2 {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) :
    Formalism.MainNotions.S.hsNormSq A = Formalism.L2.SG.RealObj.hs2 A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner Formalism.L2.SG.RealObj.hs2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_zero {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] : Formalism.MainNotions.S.hsNormSq (0 : V' →L[ℂ] V) = 0 := by
  rw [hsNormSq_eq_hs2]
  unfold Formalism.L2.SG.RealObj.hs2
  simp

theorem hs_tens {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (A : X.Vpi u' →L[ℂ] X.Vpi u)
    (J : ∀ v, X.Vloc u' v →L[ℂ] X.Vloc u v) (hA : ∀ y, A (X.tensU u' y) = X.tensU u (fun v => J v (y v))) :
    Formalism.MainNotions.S.hsNormSq A = ∏ v, Formalism.MainNotions.S.hsNormSq (J v) := by
  obtain ⟨hon, hsp⟩ := Formalism.L2.SG.RealObj.EnergyCut.tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by simp [B]
  rw [hsNormSq_eq_hs2]
  simp only [hsNormSq_eq_hs2]
  unfold hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hA, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

end GlobalTheory.OrbQuotProd

namespace GlobalTheory.OrbQuotProd

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
open scoped InnerProductSpace NNReal

theorem oo_quot : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (ν : Measure X.B.I.Ginf), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) → IsQuotMeasS X.B.I (Measure.pi μl) ν → (∀ v, ∀ s ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v), ∀ x, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (s * x)) (X.Wloc u' v ((γ v)⁻¹ * (s * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v x) (X.Wloc u' v ((γ v)⁻¹ * x))) → hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vpi u); Formalism.L2.SG.TermOp.OO ν Set.univ (X.Wu u) (X.Wu u') γ) = ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (γ v)) := by
  intro D X u u' γ μl νl ν hH hQl hQ hinv
  let R : ∀ v, Subgroup (Formalism.REAL.UJ (X.B.I.ε v)) := fun v =>
    stG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u')) (γ v)
  have hRc : ∀ v, IsClosed (R v : Set (Formalism.REAL.UJ (X.B.I.ε v))) := fun v => stG_closed _ _ _ _ _
  have hr : ∀ v, ∀ s ∈ R v, (μl v).map (fun x => x * s) = μl v := fun v s hs =>
    GlobalTheory.T.unipotent_subgroup_UJ_haar_right_invariant (X.B.I.ε v) (2 * D.R.rS + 1) (R v) (hRc v) (fun g hg => GlobalTheory.T.realPlaceFlagUnipotentRadical_isUnipotent _ _ _ g hg.1) (μl v)
      (hH v) s hs
  have hq := quot_prod X.B.I.ε R μl νl ν hRc hH hr hQl hQ
  let ψ : ∀ v, Formalism.REAL.UJ (X.B.I.ε v) → (X.Vloc u' v →L[ℂ] X.Vloc u v) := fun v z =>
    Formalism.L2.SG.TermOp.rk1 (X.Wloc u v z) (X.Wloc u' v ((γ v)⁻¹ * z))
  let Φ : X.B.I.Ginf → (X.Vpi u' →L[ℂ] X.Vpi u) := fun x =>
    Formalism.L2.SG.TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x))
  have hψc : ∀ v, Continuous (ψ v) := fun v =>
    continuous_rankOneOperator (X.Wloc_cont u v) ((X.Wloc_cont u' v).comp (continuous_const.mul continuous_id))
  have hΦc : Continuous Φ :=
    continuous_rankOneOperator (X.Wu_spec u).2.2.1 ((X.Wu_spec u').2.2.1.comp (continuous_const.mul continuous_id))
  have hψi : ∀ v, ∀ s ∈ R v, ∀ x, ψ v (s * x) = ψ v x := fun v s hs x => hinv v s hs x
  have hΦr : ∀ x, ‖Φ x‖ = ∏ v, ‖ψ v (x v)‖ := by
    intro x
    simp only [Φ, ψ, norm_rankOneInnerOperator, X.Wu_tens, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u),
      Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u') (X.tensU_inner u'), ← Finset.prod_mul_distrib]
    rfl
  have hΦn : ∀ x, ‖Φ x‖ₑ = ∏ v, ‖ψ v (x v)‖ₑ := by
    intro x
    rw [← ofReal_norm, hΦr, ENNReal.ofReal_prod_of_nonneg fun v _ => norm_nonneg _]
    simp only [ofReal_norm]
  have hL : ∫⁻ x, ‖Φ x‖ₑ ∂ν = ∏ v, ∫⁻ z, ‖ψ v z‖ₑ ∂(νl v) := by
    simp_rw [hΦn]
    exact hq.1 (fun v z => ‖ψ v z‖ₑ) (fun v => (hψc v).measurable.enorm) fun v s hs x => by
      simp only [hψi v s hs x]
  have hOO : Formalism.L2.SG.TermOp.OO ν Set.univ (X.Wu u) (X.Wu u') γ = ∫ x, Φ x ∂ν := by
    unfold Formalism.L2.SG.TermOp.OO
    rw [Measure.restrict_univ]
  have hJv : ∀ v, Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (γ v) = ∫ z, ψ v z ∂(νl v) := by
    intro v
    unfold Formalism.L2.SG.RealObj.Jv Formalism.L2.SG.TermOp.OO
    rw [Measure.restrict_univ]
  rw [hOO]
  simp only [hJv]
  by_cases h0 : ∃ v, ∫⁻ z, ‖ψ v z‖ₑ ∂(νl v) = 0
  · obtain ⟨v0, hv0⟩ := h0
    have hrhs : ∏ v, Formalism.MainNotions.S.hsNormSq (∫ z, ψ v z ∂(νl v)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ v0) ?_
      have hz : ψ v0 =ᵐ[νl v0] 0 := by
        have := (lintegral_eq_zero_iff (hψc v0).measurable.enorm).1 hv0
        filter_upwards [this] with z hz
        simpa using hz
      rw [integral_eq_zero_of_ae hz, hsNormSq_zero]
    have hlhs : ∫ x, Φ x ∂ν = 0 := by
      have hg : ∫⁻ x, ‖Φ x‖ₑ ∂ν = 0 := by
        rw [hL]; exact Finset.prod_eq_zero (Finset.mem_univ v0) hv0
      have hz : Φ =ᵐ[ν] 0 := by
        have := (lintegral_eq_zero_iff hΦc.measurable.enorm).1 hg
        filter_upwards [this] with z hz
        simpa using hz
      exact integral_eq_zero_of_ae hz
    rw [hrhs, hlhs, hsNormSq_zero]
  push_neg at h0
  by_cases hT : ∃ v, ∫⁻ z, ‖ψ v z‖ₑ ∂(νl v) = ⊤
  · obtain ⟨v0, hv0⟩ := hT
    have hrhs : ∏ v, Formalism.MainNotions.S.hsNormSq (∫ z, ψ v z ∂(νl v)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ v0) ?_
      have hni : ¬ Integrable (ψ v0) (νl v0) := fun hi => hi.2.ne hv0
      rw [integral_undef hni, hsNormSq_zero]
    have hg : ∫⁻ x, ‖Φ x‖ₑ ∂ν = ⊤ := by
      rw [hL, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v0), hv0]
      exact ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun v _ => h0 v)
    have hlhs : ∫ x, Φ x ∂ν = 0 := integral_undef fun hi => hi.2.ne hg
    rw [hrhs, hlhs, hsNormSq_zero]
  push_neg at hT
  have hψI : ∀ v, Integrable (ψ v) (νl v) := fun v =>
    ⟨(hψc v).aestronglyMeasurable, lt_top_iff_ne_top.2 (hT v)⟩
  have hΦI : Integrable Φ ν := ⟨hΦc.aestronglyMeasurable, by
    show ∫⁻ x, ‖Φ x‖ₑ ∂ν < ⊤
    rw [hL]; exact ENNReal.prod_lt_top fun v _ => lt_top_iff_ne_top.2 (hT v)⟩
  refine hs_tens X u u' _ _ fun y => ?_
  have hent : ∀ e : ∀ v, X.Vloc u v, ⟪X.tensU u e, (∫ x, Φ x ∂ν) (X.tensU u' y)⟫_ℂ =
      ⟪X.tensU u e, X.tensU u (fun v => (∫ z, ψ v z ∂(νl v)) (y v))⟫_ℂ := by
    intro e
    rw [X.tensU_inner]
    let L : (X.Vpi u' →L[ℂ] X.Vpi u) →L[ℂ] ℂ :=
      (innerSL ℂ (X.tensU u e)).comp (ContinuousLinearMap.apply ℂ (X.Vpi u) (X.tensU u' y))
    have h1 : L (∫ x, Φ x ∂ν) = ∫ x, L (Φ x) ∂ν := (L.integral_comp_comm hΦI).symm
    have h2 : ∀ v, ⟪e v, (∫ z, ψ v z ∂(νl v)) (y v)⟫_ℂ = ∫ z, ⟪e v, ψ v z (y v)⟫_ℂ ∂(νl v) := by
      intro v
      let Lv : (X.Vloc u' v →L[ℂ] X.Vloc u v) →L[ℂ] ℂ :=
        (innerSL ℂ (e v)).comp (ContinuousLinearMap.apply ℂ (X.Vloc u v) (y v))
      exact (Lv.integral_comp_comm (hψI v)).symm
    have h3 : ∀ x, L (Φ x) = ∏ v, ⟪e v, ψ v (x v) (y v)⟫_ℂ := by
      intro x
      show ⟪X.tensU u e, Φ x (X.tensU u' y)⟫_ℂ = _
      simp only [Φ, ψ, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, inner_smul_right, X.Wu_tens, X.tensU_inner,
        ← Finset.prod_mul_distrib]
      rfl
    have h4 := hq.2 (fun v z => ⟪e v, ψ v z (y v)⟫_ℂ)
      (fun v => (continuous_const.inner ((hψc v).clm_apply continuous_const)).measurable)
      (fun v s hs x => by simp only [hψi v s hs x])
    show L (∫ x, Φ x ∂ν) = _
    rw [h1, integral_congr_ae (Filter.Eventually.of_forall h3), h4]
    exact Finset.prod_congr rfl fun v _ => (h2 v).symm
  set d := (∫ x, Φ x ∂ν) (X.tensU u' y) - X.tensU u (fun v => (∫ z, ψ v z ∂(νl v)) (y v)) with hd
  have hw : ∀ w ∈ Submodule.span ℂ (Set.range (X.tensU u)), ⟪w, d⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨e, rfl⟩ := hw
      rw [hd, inner_sub_right, hent, sub_self]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  have := hw d (by rw [X.tensU_span u]; exact Submodule.mem_top)
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

end GlobalTheory.OrbQuotProd
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocalStatement

section

@[expose] public section

open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realOrbitalIntegral_hsNorm_eq_prod_local : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (ν : Measure X.B.I.Ginf), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) → IsQuotMeasS X.B.I (Measure.pi μl) ν → (∀ v, ∀ s ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v), ∀ x, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (s * x)) (X.Wloc u' v ((γ v)⁻¹ * (s * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v x) (X.Wloc u' v ((γ v)⁻¹ * x))) → hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vpi u); Formalism.L2.SG.TermOp.OO ν Set.univ (X.Wu u) (X.Wu u') γ) = ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (γ v)) := by
  first | exact @GlobalTheory.OrbQuotProd.oo_quot | exact GlobalTheory.OrbQuotProd.oo_quot | (intros; apply GlobalTheory.OrbQuotProd.oo_quot <;> assumption)
end
end
