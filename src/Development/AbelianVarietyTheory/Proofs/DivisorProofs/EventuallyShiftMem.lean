module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.FderivFnCongr
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderiv
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZeroStatement
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticAtIteratedFDerivSliceAndFderivStatement

section

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.analyticAt_iteratedFDeriv_slice_and_fderiv_eq : ∀ {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] (H : E × F → ℂ) (w₀ : F) (k : ℕ) (v : Fin k → E), AnalyticAt ℂ H (0, w₀) → AnalyticAt ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ ∧ ∀ e : F, fderiv ℂ (fun w ↦ iteratedFDeriv ℂ k (fun z ↦ H (z, w)) 0 v) w₀ e = iteratedFDeriv ℂ k (fun z ↦ fderiv ℂ H (z, w₀) (0, e)) 0 v := by
  first | exact @GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv | exact GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv | (intros; apply GlobalTheory.analyticAt_iteratedFDeriv_slice_and_fderiv <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValuesStatement

section

@[expose] public section

open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

theorem _root_.GlobalTheory.T.tensor_holomorphic_ext_of_values : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (D : Type) [CommRing D] [Algebra ℂ D] (x y : D ⊗[ℂ] Hol W), (∀ (p : E) (hp : p ∈ W), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x = Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) y) → x = y := by
  first | exact @GlobalTheory.tensor_hol_ext_of_values | exact GlobalTheory.tensor_hol_ext_of_values | (intros; apply GlobalTheory.tensor_hol_ext_of_values <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceTaylorAlgHom

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

namespace GlobalTheory.AnPer.SliceTaylor

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

theorem analyticAt_shift (q : (I ⊕ Fin g → ℂ) × (Fin g → ℂ)) :
    AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦
      (((fun i ↦ y.1 (Sum.inl i)), y.2 + fun b ↦ y.1 (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ))) q := by
  have h1 : ∀ j, AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦ y.1 j) q := fun j ↦
    ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I ⊕ Fin g ↦ ℂ) j).comp
      (ContinuousLinearMap.fst ℂ (I ⊕ Fin g → ℂ) (Fin g → ℂ))).analyticAt q
  refine AnalyticAt.prod (analyticAt_pi_iff.2 fun i ↦ h1 _) ?_
  exact analyticAt_snd.add (analyticAt_pi_iff.2 fun i ↦ h1 _)

theorem analyticAt_joint {W : Opens ((I → ℂ) × (Fin g → ℂ))} (h : Hol W) {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun y : (I ⊕ Fin g → ℂ) × (Fin g → ℂ) ↦
      h.fn ((fun i ↦ y.1 (Sum.inl i)), y.2 + fun b ↦ y.1 (Sum.inr b))) (0, w) := by
  refine AnalyticAt.comp_of_eq (h.analytic _ hw) (analyticAt_shift _) ?_
  ext <;> simp

theorem analyticAt_slice {W : Opens ((I → ℂ) × (Fin g → ℂ))} (h : Hol W) {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
      h.fn ((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b))) 0 :=
  AnalyticAt.comp_of_eq (f := fun x : I ⊕ Fin g → ℂ ↦ (x, w)) (analyticAt_joint h hw)
    (analyticAt_id.prod analyticAt_const) rfl

theorem eventually_mem {W : Opens ((I → ℂ) × (Fin g → ℂ))} {w : Fin g → ℂ}
    (hw : ((0 : I → ℂ), w) ∈ W) :
    ∀ᶠ x : I ⊕ Fin g → ℂ in 𝓝 0,
      (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ)) ∈ W := by
  have hc : Continuous (fun x : I ⊕ Fin g → ℂ ↦
      (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : (I → ℂ) × (Fin g → ℂ))) := by
    fun_prop
  refine hc.continuousAt.eventually (W.isOpen.mem_nhds ?_)
  have e : (((fun i ↦ (0 : I ⊕ Fin g → ℂ) (Sum.inl i)), w + fun b ↦ (0 : I ⊕ Fin g → ℂ) (Sum.inr b)) :
      (I → ℂ) × (Fin g → ℂ)) = (0, w) := by
    ext <;> simp
  change _ ∈ W
  simp only [e]
  exact hw

end GlobalTheory.AnPer.SliceTaylor


open GlobalTheory.AnPer.SliceTaylor in
theorem GlobalTheory.AnPer.exists_sliceTaylor_algHom : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I ⊕ Fin g → D), (∀ s : Fin (N + 1) → I ⊕ Fin g, ∏ a, t (s a) = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens ((I → ℂ) × (Fin g → ℂ))) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∃ ρ : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, ∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ h) = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
  intro I _ _ g D _ _ N t ht E _ _ _ W W₀ a ha hW
  have key : ∀ h : Hol W, ∃ r : D ⊗[ℂ] Hol W₀, ∀ (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) r = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
    intro h
    have han : ∀ (k : ℕ) (v : Fin k → (I ⊕ Fin g → ℂ)), AnalyticOnNhd ℂ (fun p ↦ iteratedFDeriv ℂ k
        (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) 0 v) W₀ :=
      fun k v p hp ↦
        AnalyticAt.comp_of_eq (GlobalTheory.T.analyticAt_iteratedFDeriv_slice_and_fderiv_eq _ (a p) k v (analyticAt_joint h (hW p hp))).1 (ha p hp) rfl
    unfold GlobalTheory.PeriodFamily.taylor
    refine ⟨∑ k ∈ Finset.range (N + 1), ∑ s : Fin k → I ⊕ Fin g,
      ((k.factorial : ℂ)⁻¹ • ∏ b, t (s b)) ⊗ₜ[ℂ] Hol.mk _ (han k fun b ↦ Pi.single (s b) 1), fun p hp ↦ ?_⟩

    simp only [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun s _ ↦ ?_
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, Hol.ev_apply, Hol.fn_mk _ _ hp,
      AlgHom.id_apply, Algebra.ofId_apply, mul_comm, ← Algebra.smul_def, smul_smul, mul_comm]
  choose r hr using key
  obtain ⟨hadd, -, hconst, hcongr, -, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have hc : ∀ c : ℂ, r (algebraMap ℂ _ c) = algebraMap ℂ _ c := fun c ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [hr, AlgHom.commutes, ← hconst c]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_algebraMap c hx
  have hA : ∀ f h : Hol W, r (f + h) = r f + r h := fun f h ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [map_add (f := _), hr, hr, hr, ← hadd _ _ (analyticAt_slice f (hW p hp)) (analyticAt_slice h (hW p hp))]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_add f h hx
  have hM : ∀ f h : Hol W, r (f * h) = r f * r h := fun f h ↦ by
    refine GlobalTheory.T.tensor_holomorphic_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    rw [map_mul, hr, hr, hr,
      ← GlobalTheory.T.taylorPolynomialEvalAlgebra_mul_of_prod_eq_zero N t ht _ _ (analyticAt_slice f (hW p hp)) (analyticAt_slice h (hW p hp))]
    refine hcongr _ _ ?_
    filter_upwards [eventually_mem (hW p hp)] with x hx using Hol.fn_mul f h hx
  exact ⟨{ toFun := r
           map_one' := by simpa only [map_one] using hc 1
           map_mul' := hM
           map_zero' := by simpa using hc 0
           map_add' := hA
           commutes' := hc }, hr⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSliceTaylorAlgHomStatement

section

@[expose] public section

open Filter Topology TopologicalSpace GlobalTheory.AnPer TensorProduct

theorem _root_.GlobalTheory.T.tensorLift_ev_rho_eq_taylor_slice : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I ⊕ Fin g → D), (∀ s : Fin (N + 1) → I ⊕ Fin g, ∏ a, t (s a) = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens ((I → ℂ) × (Fin g → ℂ))) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∃ ρ : Hol W →ₐ[ℂ] D ⊗[ℂ] Hol W₀, ∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ h) = GlobalTheory.PeriodFamily.taylor N t (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b))) := by
  first | exact @GlobalTheory.AnPer.exists_sliceTaylor_algHom | exact GlobalTheory.AnPer.exists_sliceTaylor_algHom | (intros; apply GlobalTheory.AnPer.exists_sliceTaylor_algHom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorAddSquareZeroNilpotentStatement

section

@[expose] public section

open Filter Topology

theorem _root_.GlobalTheory.T.taylor_add_square_zero_nilpotent : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D) (n : I → D), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ Ideal.span (Set.range t ∪ Set.range n)) → ∏ a, s a = 0) → (∀ i j, n i * n j = 0) → ∀ f : (I → ℂ) → ℂ, AnalyticAt ℂ f 0 → GlobalTheory.PeriodFamily.taylor N (fun i ↦ t i + n i) f = GlobalTheory.PeriodFamily.taylor N t f + ∑ i, GlobalTheory.PeriodFamily.taylor N t (fun z ↦ fderiv ℂ f z (Pi.single i 1)) * n i := by
  first | exact @GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero | exact GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero | (intros; apply GlobalTheory.PeriodFamily.taylor_add_of_mul_eq_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyShiftMem

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer.CloseTaylor

variable {I : Type} [Fintype I] [DecidableEq I] {g : ℕ}

def splitL (I : Type) [Fintype I] (g : ℕ) : (I ⊕ Fin g → ℂ) →L[ℂ] Tot I g :=
  (ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (Sum.inl i)).prod
    (ContinuousLinearMap.pi fun b ↦ ContinuousLinearMap.proj (Sum.inr b))


omit [DecidableEq I] in
theorem shift_eq (w : Fin g → ℂ) (x : I ⊕ Fin g → ℂ) :
    (((fun i ↦ x (Sum.inl i)), w + fun b ↦ x (Sum.inr b)) : Tot I g) = (0, w) + splitL I g x := by
  ext <;> simp [splitL]

theorem splitL_single (b : Fin g) :
    splitL I g (Pi.single (Sum.inr b) 1) = ((0, Pi.single b 1) : Tot I g) := by
  ext i <;> simp [splitL, Pi.single_apply]


omit [DecidableEq I] in
theorem eventually_shift_mem {W : Opens (Tot I g)} {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W) :
    ∀ᶠ x : I ⊕ Fin g → ℂ in 𝓝 0, (0, w) + splitL I g x ∈ W := by
  have hc : Continuous (fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x) :=
    continuous_const.add (splitL I g).continuous
  refine hc.continuousAt.eventually (W.isOpen.mem_nhds ?_)
  simpa using hw


omit [DecidableEq I] in
theorem analyticAt_shifted {W : Opens (Tot I g)} (h : Hol W) {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W) :
    AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x)) 0 :=
  AnalyticAt.comp_of_eq (f := fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x)
    (h.analytic _ hw) (analyticAt_const.add ((splitL I g).analyticAt 0)) (by simp)

theorem fderiv_shifted {W : Opens (Tot I g)} (h : Hol W) {w : Fin g → ℂ} (hw : ((0 : I → ℂ), w) ∈ W)
    (b : Fin g) :
    (fun z ↦ fderiv ℂ (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x)) z (Pi.single (Sum.inr b) 1))
      =ᶠ[𝓝 0] fun x : I ⊕ Fin g → ℂ ↦ (dw b h).fn ((0, w) + splitL I g x) := by
  filter_upwards [eventually_shift_mem hw] with z hz
  have e : HasFDerivAt (fun x : I ⊕ Fin g → ℂ ↦ h.fn ((0, w) + splitL I g x))
      ((fderiv ℂ h.fn ((0, w) + splitL I g z)).comp (splitL I g)) z :=
    HasFDerivAt.comp (f := fun x : I ⊕ Fin g → ℂ ↦ ((0, w) : Tot I g) + splitL I g x) z
      (h.analytic _ hz).differentiableAt.hasFDerivAt ((splitL I g).hasFDerivAt.const_add _)
  rw [e.fderiv, ContinuousLinearMap.comp_apply, splitL_single]
  exact (Hol.fn_der _ h hz).symm

end GlobalTheory.AnPer.CloseTaylor


open GlobalTheory.AnPer.CloseTaylor in
theorem GlobalTheory.AnPer.close_of_sliceTaylor : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {D : Type} [CommRing D] [Algebra ℂ D] (J : Ideal D) (N : ℕ), (∀ s : Fin (N + 1) → D, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (t : I → D), (∀ i, t i ∈ J) → ∀ (r : ℕ) (n : Fin r → Fin g → D), (∀ j a, n j a ∈ J) → (∀ j a b, n j a * n j b = 0) → ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (W : Opens (Tot I g)) (W₀ : Opens E) (a : E → Fin g → ℂ), AnalyticOnNhd ℂ a W₀ → (∀ p ∈ W₀, ((0 : I → ℂ), a p) ∈ W) → ∀ ρ₁ ρ₂ : Hol W →+* D ⊗[ℂ] Hol W₀, (∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ₁ h) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun b ↦ ∑ j, n j b) (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b)))) → (∀ (h : Hol W) (p : E) (hp : p ∈ W₀), Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) (ρ₂ h) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun _ ↦ 0) (fun x : I ⊕ Fin g → ℂ ↦ h.fn (fun i ↦ x (Sum.inl i), a p + fun b ↦ x (Sum.inr b)))) → Close (J.map (Algebra.TensorProduct.includeLeft : D →ₐ[ℂ] D ⊗[ℂ] Hol W₀)) ρ₁ ρ₂ := by
  intro I _ _ g D _ _ J N hJ t ht r n hn hnn E _ _ _ W W₀ a ha hW ρ₁ ρ₂ h₁ h₂
  induction r generalizing ρ₁ with
  | zero =>
    have : ρ₁ = ρ₂ := RingHom.ext fun h ↦ GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ by
      rw [h₁, h₂]; simp
    rw [this]
    exact Relation.ReflTransGen.refl
  | succ r ih =>
    obtain ⟨ρ', hρ'⟩ := GlobalTheory.T.tensorLift_ev_rho_eq_taylor_slice N (Sum.elim t fun b ↦ ∑ j : Fin r, n j.succ b)
      (fun s ↦ hJ _ fun c ↦ by
        rcases s c with i | b
        · exact ht i
        · exact J.sum_mem fun j _ ↦ hn _ _) W W₀ a ha hW
    refine Relation.ReflTransGen.head (b := (ρ' : Hol W →+* D ⊗[ℂ] Hol W₀)) ?_
      (ih (fun j ↦ n j.succ) (fun j ↦ hn _) (fun j ↦ hnn _) _ hρ')
    refine ⟨fun b ↦ (-n 0 b) ⊗ₜ[ℂ] 1, fun b ↦ Ideal.mem_map_of_mem _ (J.neg_mem (hn 0 b)), fun b c ↦ ?_, fun h ↦ ?_⟩
    · rw [Algebra.TensorProduct.tmul_mul_tmul, neg_mul_neg, hnn, zero_tmul]
    refine GlobalTheory.tensor_hol_ext_of_values W₀ D _ _ fun p hp ↦ ?_
    have e : (Sum.elim t fun b ↦ ∑ j : Fin r, n j.succ b) = fun i : I ⊕ Fin g ↦
        (Sum.elim t fun b ↦ ∑ j, n j b) i + (Sum.elim (fun _ ↦ 0) fun b ↦ -n 0 b) i := by
      ext (i | b)
      · simp
      · simp [Fin.sum_univ_succ]
    have hs := GlobalTheory.T.taylor_add_square_zero_nilpotent N (Sum.elim t fun b ↦ ∑ j, n j b) (Sum.elim (fun _ : I ↦ 0) fun b ↦ -n 0 b)
      (fun s hs ↦ hJ s fun c ↦ (Ideal.span_le.2 (by
        rintro _ (⟨i | b, rfl⟩ | ⟨i | b, rfl⟩)
        · exact ht i
        · exact J.sum_mem fun j _ ↦ hn _ _
        · exact J.zero_mem
        · exact J.neg_mem (hn 0 b))) (hs c))
      (by rintro (i | b) (j | c) <;> simp [hnn]) _ (analyticAt_shifted h (hW p hp))
    obtain ⟨-, -, -, hcongr, -, -⟩ :=
      GlobalTheory.PeriodFamily.taylor_formal_properties N (Sum.elim t fun b ↦ ∑ j, n j b)

    rw [RingHom.coe_coe, hρ', map_add (f := _), map_sum, h₁, e]
    simp only [map_mul, h₁, shift_eq]
    rw [hs, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, mul_zero, Finset.sum_const_zero, zero_add]
    refine congrArg _ (Finset.sum_congr rfl fun b _ ↦ ?_)
    rw [hcongr _ _ (fderiv_shifted h (hW p hp) b)]
    simp
end
end
end
