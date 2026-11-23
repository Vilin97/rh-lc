module

public import Development.AbelianVarietyTheory.Definitions.Jets.SameFns
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConnectionMulRelOfEntryRelationsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.EulerDerivMultipliersCommuteCoordOpsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormActualOperatorsAlgebraicHypothesesStatement
public import Formalism.HermitianCurvature.StatementNF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialPairConstantsPointwiseAdjointBoundedStatement
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormEntriesCommutatorMultiplier

section

@[expose] public section

namespace GlobalTheory.HatNF

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory
open scoped ContDiff

theorem mulT_ld_contDiff {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv q (fun u : ℝ => φ (Real.exp u))) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv q hφ

theorem mulT_normSq_contDiff : ContDiff ℝ ∞ (fun w : ℂ => Complex.normSq w) := by
  have : (fun w : ℂ => Complex.normSq w) = fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
    funext w; simp [Complex.normSq_apply]
  rw [this]
  fun_prop

theorem mulT_contDiffOn {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) :
    ContDiffOn ℝ ∞ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ))
      {w : ℂ | T < Complex.normSq w} := by
  have h1 : ContDiffOn ℝ ∞ (fun w : ℂ => Real.log (a * (Complex.normSq w - T)))
      {w : ℂ | T < Complex.normSq w} := by
    refine ContDiffOn.log (contDiff_const.mul (mulT_normSq_contDiff.sub contDiff_const)).contDiffOn ?_
    intro w hw
    exact (mul_pos ha (sub_pos.2 hw)).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((mulT_ld_contDiff hφ q).comp_contDiffOn h1)

theorem mulT_fderiv {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) {w : ℂ}
    (hw : T < Complex.normSq w) (v : ℂ) :
    fderiv ℝ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w v =
      ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) * (Complex.normSq w - T)⁻¹ *
        (2 * (w.re * v.re + w.im * v.im)) : ℝ) : ℂ) := by
  have hp : 0 < Complex.normSq w - T := sub_pos.2 hw
  have hn : HasFDerivAt (fun w : ℂ => Complex.normSq w)
      ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM) w := by
    have : (fun w : ℂ => Complex.normSq w) =
        fun w : ℂ => Complex.reCLM w * Complex.reCLM w + Complex.imCLM w * Complex.imCLM w := by
      funext w; simp [Complex.normSq_apply]
    rw [this]
    have h1 := Complex.reCLM.hasFDerivAt (x := w)
    have h2 := Complex.imCLM.hasFDerivAt (x := w)
    refine ((h1.mul h1).add (h2.mul h2)).congr_fderiv ?_
    refine ContinuousLinearMap.ext fun v => ?_
    simp
    ring
  have h1 := ((hn.sub_const T).const_mul a).log (mul_pos ha hp).ne'
  have h2 : HasDerivAt (iteratedDeriv q (fun u : ℝ => φ (Real.exp u)))
      (LE.ld (q + 1) φ (a * (Complex.normSq w - T))) (Real.log (a * (Complex.normSq w - T))) := by
    unfold LE.ld
    rw [iteratedDeriv_succ]
    exact (((mulT_ld_contDiff hφ q).differentiable (by simp)) _).hasDerivAt
  have h3 := Complex.ofRealCLM.hasFDerivAt.comp w (h2.comp_hasFDerivAt w h1)
  have h4 : fderiv ℝ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w = _ := h3.fderiv
  rw [h4]
  simp only [ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, smul_apply,
    add_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  congr 1
  field_simp

theorem mulT_dZ {φ : ℝ → ℝ} (hφ : LE.SmoothLog φ) (q : ℕ) {a : ℝ} (ha : 0 < a) (T : ℝ) {w : ℂ}
    (hw : T < Complex.normSq w) :
    NF.dZ (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w =
      star w * ((((Complex.normSq w - T : ℝ) : ℂ))⁻¹ *
        ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) ∧
    NF.dZb (fun w : ℂ => ((LE.ld q φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) w =
      w * ((((Complex.normSq w - T : ℝ) : ℂ))⁻¹ *
        ((LE.ld (q + 1) φ (a * (Complex.normSq w - T)) : ℝ) : ℂ)) := by
  unfold NF.dZ NF.dZb
  rw [mulT_fderiv hφ q ha T hw, mulT_fderiv hφ q ha T hw, ← Complex.ofReal_inv]
  generalize LE.ld (q + 1) φ (a * (Complex.normSq w - T)) = b
  generalize (Complex.normSq w - T)⁻¹ = e
  constructor <;> apply Complex.ext <;> simp <;> ring


open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.NFx4 in
theorem t_mul_mulG (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par)
    (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hφ : LE.SmoothLog φ)
    (hW : IsMulG P Bs φ W) (q : ℕ) (Y : ℂ) :
    X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧
      X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧
      X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 := by
  have hU := isOpen_normSq_gt (Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')
  have hDU := Dp_maps (k := P.k) (r := P.r) Bs.z Bs.z'
  have hD := Qx5.Dp_open P.k P.r Bs.z Bs.z'
  have ha : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', 0 < Complex.normSq (∏ a, x.1 a) := fun x hx =>
    Complex.normSq_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => hx.1 a)
  have key := fun (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r)
      (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') =>
    zeta_smooth_level Bs.z Bs.z' hD hU hDU (mulT_contDiffOn hφ q (ha x hx) _) (Qx5.slice_smooth Φ.2 hx.1)
      ⟨hx.2.1, hx.2.2⟩ Y
  have hd := fun (x : (Fin P.r → ℂ) × Q.Mx P.k P.r) (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') =>
    mulT_dZ hφ q (ha x hx) _ (hDU x.2 hx.2.2)
  have hWa : ∀ (p : ℕ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c : Fin P.r → ℂ) (g : Q.Mx P.k P.r),
      (W p Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g =
        ((LE.ld p φ (Complex.normSq (∏ a, c a) * (Complex.normSq (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) g) -
          Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')) : ℝ) : ℂ) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c g :=
    fun p Φ c g => hW p Φ c g
  have ht : ∀ (a b : Fin 2) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r),
      x ∈ Q.DomR P.k P.r Bs.z Bs.z' → (X.t Y a b (W q Φ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
        Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (fun y =>
          ((LE.ld q φ (Complex.normSq (∏ a, x.1 a) * (Complex.normSq (Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) y) -
            Tz P.k P.r Bs.z * Tz P.k P.r Bs.z')) : ℝ) : ℂ) • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 y) x.2 := by
    intro a b Φ x hx
    rw [X.t_apply Y a b _ x hx]
    congr 1
    funext y
    exact hWa q Φ x.1 y
  refine ⟨end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_, end_ext_dom fun Φ x hx => ?_⟩
  · rw [Module.End.mul_apply, ht 1 0 Φ x hx, (key Φ x hx).1, LinearMap.sub_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_sub, Pi.sub_apply,
      Pi.sub_apply, X.fn_apply 2 _ x hx, X.fn_apply 5 _ x hx, hWa, hWa,
      X.t_apply Y 1 0 Φ x hx, X.t_apply Y 1 1 Φ x hx, (hd x hx).1, smul_smul, smul_smul, mul_assoc]
    rfl
  · rw [Module.End.mul_apply, ht 1 1 Φ x hx, (key Φ x hx).2.1, Module.End.mul_apply, hWa,
      X.t_apply Y 1 1 Φ x hx]
  · rw [Module.End.mul_apply, ht 0 1 Φ x hx, (key Φ x hx).2.2, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply, Module.End.mul_apply, Module.End.mul_apply, Submodule.coe_add, Pi.add_apply,
      Pi.add_apply, X.fn_apply 0 _ x hx, X.fn_apply 5 _ x hx, hWa, hWa,
      X.t_apply Y 0 1 Φ x hx, X.t_apply Y 1 1 Φ x hx, (hd x hx).2, smul_smul, smul_smul, mul_assoc]
    rfl

theorem nf_t_mul_mulG : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (q : ℕ) (Y : ℂ), X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧ X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧ X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 :=
  fun Wp Wq _ _ _ _ _ _ P Bs X _ _ _ _ _ _ _ φ W hφ hW q Y => t_mul_mulG Wp Wq P Bs X φ W hφ hW q Y

end GlobalTheory.HatNF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormEntriesCommutatorMultiplierStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.normalForm_entries_commutator_multiplier : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (q : ℕ) (Y : ℂ), X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧ X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧ X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 := by
  first | exact @GlobalTheory.HatNF.nf_t_mul_mulG | exact GlobalTheory.HatNF.nf_t_mul_mulG | (intros; apply GlobalTheory.HatNF.nf_t_mul_mulG <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialMultipliersSatisfyNormalFormRelations

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.MulRelActual

section pairs

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem mkPair_mul_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b * Q.mkP c d = Q.mkP (a * c) (d * b) := rfl
theorem mkPair_add_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b + Q.mkP c d = Q.mkP (a + c) (b + d) := rfl
theorem mkPair_sub_mkPair (a b c d : Module.End ℂ V) : Q.mkP a b - Q.mkP c d = Q.mkP (a - c) (b - d) := rfl
theorem mkPair_congr {a b c d : Module.End ℂ V} (h : a = c) (h' : b = d) : Q.mkP a b = Q.mkP c d := by rw [h, h']

theorem snd_eq_of_mkPair_eq {a b c d : Module.End ℂ V} (h : Q.mkP a b = Q.mkP c d) : b = d :=
  congrArg (fun x : Q.Pr V => MulOpposite.unop (Prod.snd x)) h

theorem commute_mkP {a b w : Module.End ℂ V} (ha : Commute a w) (hb : Commute b w) :
    Commute (Q.mkP a b) (Q.mkP w w) := by
  change Q.mkP a b * Q.mkP w w = Q.mkP w w * Q.mkP a b
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  exact mkPair_congr ha.eq hb.eq.symm

theorem exists_mkP (x : Q.Pr V) : ∃ a b, x = Q.mkP a b := ⟨Prod.fst x, MulOpposite.unop (Prod.snd x), rfl⟩

end pairs

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

omit [FiniteDimensional ℂ Wp] in
theorem hsVec_smul (s : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (s • A) = s • B.hsVec A := rfl

omit [FiniteDimensional ℂ Wp] in
theorem hsVec_sub (A A' : Wq →L[ℂ] Wp) : B.hsVec (A - A') = B.hsVec A - B.hsVec A' := rfl

omit [FiniteDimensional ℂ Wp] in
theorem eq_zero_of_hsVec {A : Wq →L[ℂ] Wp} (h : B.hsVec A = 0) : A = 0 := by
  have h1 : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := fun i => congrArg (fun v => v i) h
  apply ContinuousLinearMap.coe_injective
  apply (stdOrthonormalBasis ℂ Wq).toBasis.ext
  intro i
  simpa using h1 i

omit [FiniteDimensional ℂ Wp] in
theorem eq_of_inner {A A' : Wq →L[ℂ] Wp}
    (h : inner ℂ (B.hsVec (A - A')) (B.hsVec A) = inner ℂ (B.hsVec (A - A')) (B.hsVec A')) : A = A' := by
  have h1 : inner ℂ (B.hsVec (A - A')) (B.hsVec (A - A')) = 0 := by
    nth_rewrite 2 [hsVec_sub]
    rw [inner_sub_right, h, sub_self]
  exact sub_eq_zero.1 (eq_zero_of_hsVec (inner_self_eq_zero.1 h1))

variable {P : M.Par} {Bs : B.RealPlaceData P.k P.r Wp Wq}

theorem radSp_ext {Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'}
    (h : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hx : (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z'
  · exact h (c, g) hx
  · rw [Φ.2.1 (c, g) hx, Ψ.2.1 (c, g) hx]

theorem commute_of_adj {a b w : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hw : P5.multiplicationOperator w m)
    (hab : ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π', ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z',
      B.hsInner ((a Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) =
        B.hsInner ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2) ((b Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)) :
    Commute a w := by
  refine LinearMap.ext fun Φ => radSp_ext fun x hx => ?_
  apply eq_of_inner
  have h1 := hab (w Φ) (a (w Φ) - w (a Φ)) x hx
  have h2 := hab Φ (a (w Φ) - w (a Φ)) x hx
  unfold B.hsInner at h1 h2
  rw [hw Φ, hsVec_smul, inner_smul_right, ← h2, ← inner_smul_right, ← hsVec_smul, ← hw (a Φ)] at h1
  exact h1

theorem commute_of_ptAdj {x : RA P Bs} (hx : PtAdj P Bs x) {w : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')}
    {m : (Fin P.r → ℂ) → Q.Mx P.k P.r → ℂ} (hw : P5.multiplicationOperator w m) : Commute x (Q.mkP w w) := by
  obtain ⟨a, b, rfl⟩ := exists_mkP x
  refine commute_mkP (commute_of_adj (b := b) hw hx) (commute_of_adj (b := a) hw fun Φ Ψ y hy => ?_)
  have h := hx Ψ Φ y hy
  unfold B.hsInner at h ⊢
  rw [← inner_conj_symm, ← inner_conj_symm (B.hsVec ((a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) y.1 y.2))]
  exact congrArg _ h.symm

end hs

theorem mulRel_actual : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → MulRel d.L (fun q => Q.mkP (W q) (W q)) := by
  intro Wp Wq _ _ _ _ _ _ P Bs X μ L st l0 d hD hN φ W hφ hW
  have hH := (GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses Wp Wq P Bs X μ L st l0 d hD hN).1
  have hK := GlobalTheory.T.radialPairConstants_pointwiseAdjoint_bounded Wp Wq P Bs X μ L st l0 d hD hN
  have hC := GlobalTheory.T.eulerDerivMultipliers_coordOps_commutation_relations Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW
  have hT := GlobalTheory.T.normalForm_entries_commutator_multiplier Wp Wq P Bs X μ L st l0 d hD hN φ W hφ hW
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, -⟩, -, hR, hQ⟩ := hN
  have hκ : ∀ q (f : M.Ty P → ℂ), Commute (d.κ f) (Q.mkP (W q) (W q)) := fun q f =>
    commute_of_ptAdj (hK f).1 (hW q)
  have hf : ∀ q, ∀ f ∈ d.L.fns, Commute f (Q.mkP (W q) (W q)) := by
    intro q f hf
    obtain ⟨ho, hfn⟩ := hC q
    rcases hf with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | hf)
    · rw [h3]; exact commute_mkP (ho l).2.2.1 (ho l).2.2.2.2.1
    · rw [h4]; exact commute_mkP (ho l).2.2.2.1 (ho l).2.2.2.2.2
    · rw [h5]; exact commute_mkP (ho l).2.2.2.2.1 (ho l).2.2.1
    · rw [h6]; exact commute_mkP (ho l).2.2.2.2.2 (ho l).2.2.2.1
    · rcases hf with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h7]; exact commute_mkP (hfn _) (hfn _)
      · rw [h8]; exact commute_mkP (hfn _) (hfn _)
      · rw [h9]; exact commute_mkP (hfn _) (hfn _)
      · rw [h10]; exact commute_mkP (hfn _) (hfn _)
      · rw [h11]; exact commute_mkP (hfn _) (hfn _)
      · rw [h12]; exact commute_mkP (hfn _) (hfn _)
  refine GlobalTheory.T.connection_mulRel_of_entry_relations P (RA P Bs) d hH _ fun q => ⟨hf q, fun l => ?_, fun l => ?_, hκ q, rfl, fun Y => ?_⟩
  · rw [h1, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]
    refine mkPair_congr ((hC q).1 l).1 ?_
    rw [neg_mul, ((hC q).1 l).2.1, mul_neg]; abel
  · rw [h2, mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_add_mkPair]
    refine mkPair_congr ((hC q).1 l).2.1 ?_
    rw [neg_mul, ((hC q).1 l).1, mul_neg]; abel
  · have mζ : d.L.ζb ∈ d.L.fns := Or.inr (by simp)
    have mG : d.L.GG ∈ d.L.fns := Or.inr (by simp)
    have mGi : d.L.GGi ∈ d.L.fns := Or.inr (by simp)
    have e11 : d.QQ Y 1 1 = d.L.GG * d.x Y := rfl
    have c11 : ∀ g ∈ d.L.fns, Commute (d.QQ Y 1 1) g := fun g hg => by
      rw [e11]
      exact Commute.mul_left (d.L.fns_comm _ mG _ hg) (hR.2.1 _ g (Or.inl hg))
    have c11m : Commute (d.QQ Y 1 1) (Q.mkP (W (q + 1)) (W (q + 1))) := by
      rw [e11]
      exact Commute.mul_left (hf _ _ mG) (hκ _ _)
    have cζG : Commute d.L.ζb d.L.GGi := d.L.fns_comm _ mζ _ mGi
    have key : d.L.ζb * d.L.GGi * Q.mkP (W (q + 1)) (W (q + 1)) * d.QQ Y 1 1 =
        d.QQ Y 1 1 * (Q.mkP (W (q + 1)) (W (q + 1)) * (d.L.GGi * d.L.ζb)) := by
      rw [← (((c11 _ mζ).mul_right (c11 _ mGi)).mul_right c11m).eq,
        (Commute.mul_left (hf (q + 1) _ mζ) (hf (q + 1) _ mGi)).eq, cζG.eq]
    have hY : star (Y : ℂ) = Y := Complex.conj_ofReal Y
    have q10 : d.QQ Y 1 0 = Q.mkP (X.t Y 1 0) (X.t Y 0 1) := by
      rw [← hQ]
      change Q.mkP (X.t Y 1 0) (X.t (star (Y : ℂ)) 0 1) = _
      rw [hY]
    have q11 : d.QQ Y 1 1 = Q.mkP (X.t Y 1 1) (X.t Y 1 1) := by
      rw [← hQ]
      change Q.mkP (X.t Y 1 1) (X.t (star (Y : ℂ)) 1 1) = _
      rw [hY]
    rw [q11, h9, h12] at key
    rw [q10, q11, h9, h12]
    simp only [mkPair_mul_mkPair, mkPair_sub_mkPair] at key ⊢
    refine mkPair_congr (hT q Y).1 ?_
    rw [snd_eq_of_mkPair_eq key, (hT q Y).2.2]
    abel

end GlobalTheory.HatNF.MulRelActual
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RadialMultipliersSatisfyNormalFormRelationsStatement

section

@[expose] public section

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

theorem _root_.GlobalTheory.T.radialMultipliers_satisfy_normalForm_relations : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → MulRel d.L (fun q => Q.mkP (W q) (W q)) := by
  first | exact @GlobalTheory.HatNF.MulRelActual.mulRel_actual | exact GlobalTheory.HatNF.MulRelActual.mulRel_actual | (intros; apply GlobalTheory.HatNF.MulRelActual.mulRel_actual <;> assumption)
end
end
