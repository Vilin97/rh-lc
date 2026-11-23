module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEDecayAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSESiteOpsC
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfSquareDensity
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
import Mathlib.Topology.Sheaves.Init
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SfiniteOfIsHaarOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveOperatorLeL2Subspace
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfStepDensity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSH2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevTransportHer
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHBTl
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHCellTie
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamAlg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHFamJFOK
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHOpClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHRepLin
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSliceFamGood
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHSliceFamJF
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHUUiw
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PTieAll

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWaveOut

section

@[expose] public section

open MeasureTheory Filter Topology
open scoped Matrix ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

section Wave

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S]
  [DecidableEq S]

theorem waveOut_pairAt_left (μ : Measure (Mt k r)) {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → ℂ}
    (hW : multiplicationOperator W (fun c _ => m c)) (Φ Ψ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (W Φ) Ψ c = m c * pairAt μ Φ Ψ c := by
  unfold pairAt
  have e : ∀ g : Mt k r, B.hsInner ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) =
      m c * B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) := by
    intro g
    have h1 := hW Φ c (Matrix.of g)
    simp only at h1
    rw [h1, hsInner_smul_left']
  simp_rw [e]
  exact integral_const_mul _ _

theorem waveOut_pairAt_self (μ : Measure (Mt k r)) {W : Module.End ℂ (RadSp k r z z' π π')} {m : (Fin r → ℂ) → ℂ}
    (hW : multiplicationOperator W (fun c _ => m c)) (hm : ∀ c, ‖m c‖ = 1) (Φ : RadSp k r z z' π π') (c : Fin r → ℂ) :
    pairAt μ (W Φ) (W Φ) c = pairAt μ Φ Φ c := by
  unfold pairAt
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  have h1 := hW Φ c (Matrix.of g)
  simp only at h1
  show B.hsInner ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) ((W Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g)) = _
  rw [h1, hsInner_smul_left', hsInner_smul_right', ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, hm]
  simp

theorem waveOut_glue (l : Fin r) (c : Fin r → ℂ) (t : ℂ) (c' : Cf r l.succ) :
    glue l.succ (Function.update c l t) c' l = t := by
  unfold glue
  rw [dite_eq_right (by simp)]
  first
  | exact Function.update_self l t c
  | simp

theorem waveOut_dens (μ : Measure (Mt k r)) (l : Fin r) (s : ℂ) {W : Module.End ℂ (RadSp k r z z' π π')}
    (hW : multiplicationOperator W (fun c' _ => fsv s (c' l))) (u v : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) :
    Dens μ l (fun b => W (u b)) v c t = fsv s t * Dens μ l u v c t := by
  have e : (fun c' : Cf r l.succ => ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ a, pairAt μ (W (u a)) (v a) (glue l.succ (Function.update c l t) c')) =
      fun c' => fsv s t * (((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (u a) (v a) (glue l.succ (Function.update c l t) c')) := by
    funext c'
    have hp : ∀ a, pairAt μ (W (u a)) (v a) (glue l.succ (Function.update c l t) c') =
        fsv s t * pairAt μ (u a) (v a) (glue l.succ (Function.update c l t) c') := by
      intro a
      rw [waveOut_pairAt_left (m := fun c' => fsv s (c' l)) μ hW, waveOut_glue]
    simp only [hp, ← Finset.mul_sum]
    ring
  simp only [Dens, form]
  rw [e, integral_const_mul]
  ring

end Wave

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWaveOutJ

section

@[expose] public section

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

theorem wave_outgoing_orbital : WaveOutJ := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hdat hl0 hle hz hz' hπ hπ' l hl u v hu hv c hc s Wv hW
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hdat.2.1
  haveI := sfinite_of_isHaarOn _ μ hμ

  have hl2u := fun b => wave_operator_le_l2_subspace P z z' π π' μ hμ D hz hz' hπ hπ' l (hu b)
  have hl2v := fun b => wave_operator_le_l2_subspace P z z' π π' μ hμ D hz hz' hπ hπ' l (hv b)
  have hW1 : ∀ c' : Fin P.r → ℂ, ‖fsv s (c' l)‖ = 1 := fun c' => HerC.norm_fsv s (c' l)
  have hl' : l.castSucc = 0 := by
    ext
    simp [hl]
  have keyu : ∀ b, LevelSquareIntegrable μ l.castSucc (u b) c := by
    intro b
    rw [hl']
    exact (hl2u b).2 c
  have keyv : ∀ b, LevelSquareIntegrable μ l.castSucc (v b) c := by
    intro b
    rw [hl']
    exact (hl2v b).2 c

  have keyW : ∀ b, LevelSquareIntegrable μ l.castSucc (Wv (u b)) c := by
    intro b
    have h := keyu b
    unfold LevelSquareIntegrable at h ⊢
    simp only [waveOut_pairAt_self μ hW hW1]
    exact h
  have hd := dens_int μ hμ l (fun b => Wv (u b)) v (fun b => mul_lc hW _ (hl2u b).1)
    (fun b => (hl2v b).1) c keyW keyv
  rw [← hd.2]
  simp_rw [waveOut_dens μ l s hW u v c]

end Formalism.FourierDecayAlt.P.CutSE
end
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSHChk

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P

theorem cutSH_sliceStepHer_of_sfg (h7 : CutSH.SliceFamGood) : PTie.SliceStepHer :=
  CutSH.sliceStepHer_of CutSH.family_orbital_valid CutSH.family_algebraic CutSH.representation_linear
    cell_compatibility_identity h7 CutSH.slice_family_orbital operator_class_closed boundary_torus_adjoin
    unipotent_scalar_identity

theorem cutSH_levTransportHer_of_sfg (h7 : CutSH.SliceFamGood) : PTie.LevTransportHer :=
  ptie_levTransportHer_of_sliceStep (cutSH_sliceStepHer_of_sfg h7)

theorem level_transport_hermitian : PTie.LevTransportHer := cutSH_levTransportHer_of_sfg slice_family_good

end Formalism.FourierDecayAlt.P
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfStepSquare

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P5.HerD

theorem thmPActualCpt_of_stepExp0 (h0 : StepExp0) : ThmPActualCpt :=
  theorem_P_compact_of_step_density Formalism.FourierDecayAlt.P.level_transport_hermitian h0

end Formalism.FourierDecayAlt.P5.HerD
end
end

-- Source module: Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopHer

section

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem stepExp0_of_leaves (hO : OneLetterDens) (hS : DensSmoothCls) (hR : RadDecay) : Formalism.FourierDecayAlt.P5.HerD.StepExp0 :=
  stepExp0_of_open hO hS (decayPair2_of_smooth hS) (decayPair3_of wave_outgoing_orbital (clsDecayJ_of hR))
    (decayPair4_of wave_outgoing_orbital (clsDecayJ_of hR) site_multiplication_orbital)

theorem thmPActualCpt_of_leaves (hO : OneLetterDens) (hS : DensSmoothCls) (hR : RadDecay) :
    Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  Formalism.FourierDecayAlt.P5.HerD.thmPActualCpt_of_stepExp0 (stepExp0_of_leaves hO hS hR)

end Formalism.FourierDecayAlt.P.CutSE
end
end
