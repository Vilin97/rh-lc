module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearZeroOfKillsTranslatesTensorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepMemSm
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.IndefiniteReal.TopMult
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
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastSmulMemHatL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicitySpaceEqZeroOfApplyNonzeroTensorZero
import Aesop.Main
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurMultMultiplicitySpacesOfRapidDecay
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapRealTranslateEqRightTranslation

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmoothTranslate


open Classical in
theorem mult_equiv {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) (v : M.Vec) (w : M.sm τ)
    (hw : (w : M.H τ) = M.rep τ g (v τ)) :
    T (Function.update v τ w) = rTr V (atTau θ V τ g) (T v) := by
  unfold Mult at hT
  induction hT using Submodule.span_induction with
  | mem T hT => exact hT.equiv τ g hg v w hw
  | zero => funext x; simp [rTr]
  | add T T' _ _ h h' =>
    funext x
    simp only [MultilinearMap.add_apply, Pi.add_apply, h, h', rTr]
  | smul r T _ h =>
    funext x
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, h, rTr]

theorem translate : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : ∀ τ, Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ, ∃ P ∈ GinfC V, ∀ (v : M.Vec) (x : GA D V), T (fun τ => ⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ), GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩) x = T v (x * P) := by
  intro D V S θ M J χ T hT g
  classical
  have key : ∀ s : Finset D.what₂.Tau, ∃ P ∈ GinfC V, ∀ (v : M.Vec) (x : GA D V),
      T (fun τ => if τ ∈ s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
        GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
        else v τ) x = T v (x * P) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, fun v x => by simp⟩
    | insert a s ha ih =>
      obtain ⟨P, hP, hPe⟩ := ih
      refine ⟨atTau θ V a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a)) * P, mul_mem (Formalism.IndefR.TopMult.atTau_mem_GinfC θ a _) hP,
        fun v x => ?_⟩
      have hupd : (fun τ => if τ ∈ insert a s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
          else v τ) = Function.update (fun τ => if τ ∈ s then (⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩ : M.sm τ)
          else v τ) a ⟨M.rep a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a)) (v a),
          GlobalTheory.SmoothStable.rep_mem_sm D V S M a _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g a)) _ (v a).2⟩ := by
        funext τ
        by_cases h : τ = a
        · subst h; simp
        · rw [Function.update_of_ne h]
          simp [Finset.mem_insert, h]
      rw [hupd, mult_equiv θ M J χ T hT a _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g a)) _ _ (by simp [ha])]
      show T _ (x * atTau θ V a (Formalism.IndefR.SchurOrthogonalityAlt.gm (g a))) = _
      rw [hPe, mul_assoc]
  obtain ⟨P, hP, hPe⟩ := key Finset.univ
  exact ⟨P, hP, fun v x => by simpa using hPe v x⟩

end GlobalTheory.SmoothTranslate
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapRealTranslateEqRightTranslationStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.multiplicityMap_realTranslate_eq_rightTranslation : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : ∀ τ, Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ, ∃ P ∈ GinfC V, ∀ (v : M.Vec) (x : GA D V), T (fun τ => ⟨M.rep τ (Formalism.IndefR.SchurOrthogonalityAlt.gm (g τ)) (v τ), GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem (g τ)) _ (v τ).2⟩) x = T v (x * P) := by
  first | exact @GlobalTheory.SmoothTranslate.translate | exact GlobalTheory.SmoothTranslate.translate | (intros; apply GlobalTheory.SmoothTranslate.translate <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodIntegrableBoundedByProductOfNorms

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.PeriodBound

theorem period_bound : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ t ∈ MultT θ M J χ, ∀ (v : GlobalTheory.Unf.Vol V) (F : GA D V → ℂ), GlobalTheory.Unf.IsContAut V F → (∃ C, ∀ g, ‖F g‖ ≤ C) → (∀ x : SmT M, IntegrableOn (fun g => F g * t x g) v.𝓕 v.μ) ∧ ∃ K : ℝ, ∀ w : M.Vec, ‖∫ g in v.𝓕, F g * t (PiTensorProduct.tprod ℂ w) g ∂v.μ‖ ≤ K * ∏ τ, ‖(w τ : M.H τ)‖ := by
  intro hP hV D θ hθ V S M J χ t ht v F hF hFb
  obtain ⟨C0, hC0⟩ := hFb
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have hfin : v.μ v.𝓕 < ⊤ := GlobalTheory.CuspDecay.measure_lt_top hV V v.μ v.𝓕 v.haar v.fund
  have hval : ∀ x : SmT M, Continuous (t x) ∧ ∃ B : ℝ, ∀ g, ‖t x g‖ ≤ B := by
    intro x
    obtain ⟨ha, hc, -⟩ := GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hP D V S M θ hθ J χ t ht x
    exact ⟨ha.cont, GlobalTheory.CuspDecay.bounded_of_cuspForm hP hθ ha hc⟩
  have hint0 : ∀ x : SmT M, IntegrableOn (fun g => F g * t x g) v.𝓕 v.μ := by
    intro x
    obtain ⟨hcont, B, hB⟩ := hval x
    refine Measure.integrableOn_of_bounded (M := C0 * B) hfin.ne
      ((hF.2.mul hcont).measurable.aestronglyMeasurable) (.of_forall fun g => ?_)
    rw [norm_mul]
    exact mul_le_mul (hC0 g) (hB g) (norm_nonneg _) ((norm_nonneg _).trans (hC0 g))
  refine ⟨hint0, ?_⟩
  set T : MMap M := PiTensorProduct.lift.symm t with hTdef
  have hT : T ∈ Mult θ M J χ := (mem_multT θ M J χ t).1 ht
  obtain ⟨c, hc⟩ := GlobalTheory.SchurConst.schurMult_all hP D θ hθ V S M J χ v.μ v.𝓕 v.haar v.fund hθ v.haar v.fund T hT T hT
  have hTw : ∀ w : M.Vec, T w = t (PiTensorProduct.tprod ℂ w) := fun w => by
    rw [hTdef, PiTensorProduct.lift_symm]
    rfl
  set C' : ℝ := max C0 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  have hFC : ∀ g, ‖F g‖ ≤ C' := fun g => (hC0 g).trans (le_max_left _ _)
  refine ⟨C' * ((v.μ v.𝓕).toReal + ‖c‖) / 2, fun w => ?_⟩
  set s : ℝ := ∏ τ, ‖(w τ : M.H τ)‖ with hs
  have hs0 : 0 ≤ s := Finset.prod_nonneg fun τ _ => norm_nonneg _
  rcases hs0.eq_or_lt with h0 | hpos
  · obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 h0.symm
    have hwτ : w τ = 0 := Subtype.ext (norm_eq_zero.1 hτ)
    have h1 : PiTensorProduct.tprod ℂ w = 0 := (PiTensorProduct.tprod ℂ).map_coord_zero τ hwτ
    rw [h1, map_zero, ← h0]
    simp
  · obtain ⟨hint, heq⟩ := hc w w
    have hnsq : ∀ g, ‖star (T w g) * T w g‖ = ‖T w g‖ ^ 2 := fun g => by
      rw [norm_mul, norm_star, sq]
    have hint2 : IntegrableOn (fun g => ‖T w g‖ ^ 2) v.𝓕 v.μ := by
      have h := funext fun g => (hnsq g).symm
      rw [h]
      exact hint.norm
    have hsq : ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ ≤ ‖c‖ * s ^ 2 := by
      have h1 : ((∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ : ℝ) : ℂ) = ∫ g in v.𝓕, star (T w g) * T w g ∂v.μ := by
        rw [← integral_complex_ofReal]
        congr 1
        funext g
        rw [Complex.star_def, Complex.conj_mul']
        push_cast
        ring
      have hnn : 0 ≤ ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ := integral_nonneg fun g => sq_nonneg _
      have h2 : ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ = ‖∫ g in v.𝓕, star (T w g) * T w g ∂v.μ‖ := by
        rw [← h1, Complex.norm_of_nonneg hnn]
      rw [h2, heq, norm_mul, norm_prod, hs, ← Finset.prod_pow]
      refine le_of_eq ?_
      congr 1
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [inner_self_eq_norm_sq_to_K]
      simp
    have hpt : ∀ g, ‖F g * t (PiTensorProduct.tprod ℂ w) g‖ ≤ C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2 := by
      intro g
      rw [norm_mul, ← hTw]
      have h3 : ‖T w g‖ ≤ s / 2 + ‖T w g‖ ^ 2 / (2 * s) := by
        rw [div_add_div _ _ (by norm_num) (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (‖T w g‖ - s)]
      calc ‖F g‖ * ‖T w g‖ ≤ C' * ‖T w g‖ := mul_le_mul_of_nonneg_right (hFC g) (norm_nonneg _)
        _ ≤ C' * (s / 2 + ‖T w g‖ ^ 2 / (2 * s)) := mul_le_mul_of_nonneg_left h3 hC'0
        _ = C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2 := by ring
    have hintR : IntegrableOn (fun g => C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2) v.𝓕 v.μ :=
      (integrableOn_const hfin.ne).add (hint2.const_mul _)
    calc ‖∫ g in v.𝓕, F g * t (PiTensorProduct.tprod ℂ w) g ∂v.μ‖
        ≤ ∫ g in v.𝓕, ‖F g * t (PiTensorProduct.tprod ℂ w) g‖ ∂v.μ := norm_integral_le_integral_norm _
      _ ≤ ∫ g in v.𝓕, (C' * s / 2 + C' / (2 * s) * ‖T w g‖ ^ 2) ∂v.μ :=
          integral_mono (hint0 _).norm hintR hpt
      _ = (v.μ v.𝓕).toReal * (C' * s / 2) + C' / (2 * s) * ∫ g in v.𝓕, ‖T w g‖ ^ 2 ∂v.μ := by
          have hc1 : Integrable (fun _ : GA D V => C' * s / 2) (v.μ.restrict v.𝓕) := integrableOn_const hfin.ne
          have hc2 : Integrable (fun g => C' / (2 * s) * ‖T w g‖ ^ 2) (v.μ.restrict v.𝓕) := hint2.const_mul _
          rw [integral_add hc1 hc2, setIntegral_const,
            integral_const_mul, smul_eq_mul, Measure.real]
      _ ≤ (v.μ v.𝓕).toReal * (C' * s / 2) + C' / (2 * s) * (‖c‖ * s ^ 2) := by
          gcongr
      _ = C' * ((v.μ v.𝓕).toReal + ‖c‖) / 2 * s := by
          field_simp

end GlobalTheory.PeriodBound
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodIntegrableBoundedByProductOfNormsStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.period_integrable_bounded_by_product_of_norms : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ t ∈ MultT θ M J χ, ∀ (v : GlobalTheory.Unf.Vol V) (F : GA D V → ℂ), GlobalTheory.Unf.IsContAut V F → (∃ C, ∀ g, ‖F g‖ ≤ C) → (∀ x : SmT M, IntegrableOn (fun g => F g * t x g) v.𝓕 v.μ) ∧ ∃ K : ℝ, ∀ w : M.Vec, ‖∫ g in v.𝓕, F g * t (PiTensorProduct.tprod ℂ w) g ∂v.μ‖ ≤ K * ∏ τ, ‖(w τ : M.H τ)‖ := by
  first | exact @GlobalTheory.PeriodBound.period_bound | exact GlobalTheory.PeriodBound.period_bound | (intros; apply GlobalTheory.PeriodBound.period_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfOrthogonalRealTranslates

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TransOrth

theorem integral_eq_zero_of_translates : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D),
    IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ),
    ∀ t ∈ MultT θ M J χ, ∀ (v : GlobalTheory.Unf.Vol V) (F : GA D V → ℂ), GlobalTheory.Unf.IsContAut V F → (∃ C, ∀ g, ‖F g‖ ≤ C) →
    ∀ w : SmT M, w ≠ 0 → (∀ h ∈ GinfC V, ∫ g in v.𝓕, F g * t w (g * h) ∂v.μ = 0) →
    ∀ w' : SmT M, ∫ g in v.𝓕, F g * t w' g ∂v.μ = 0 := by
  intro hP hV D θ hθ V S M J χ t ht v F hF hFb w hw hh w'
  classical
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (M.ds τ).1
  obtain ⟨hint, K, hK⟩ := GlobalTheory.T.period_integrable_bounded_by_product_of_norms hP hV D θ hθ V S M J χ t ht v F hF hFb
  let ℓ : SmT M →ₗ[ℂ] ℂ :=
    { toFun := fun x => ∫ g in v.𝓕, F g * t x g ∂v.μ
      map_add' := fun x y => by
        simp only [map_add (f := _), Pi.add_apply, mul_add]
        exact integral_add (hint x) (hint y)
      map_smul' := fun r x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [← integral_const_mul]
        congr 1
        funext g
        ring }
  have hℓ : ∀ x, ℓ x = ∫ g in v.𝓕, F g * t x g ∂v.μ := fun x => rfl
  let L : MultilinearMap (RingHom.id ℂ) (fun τ => M.sm τ) ℂ := ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ)
  have hL : ∀ u, L u = ℓ (PiTensorProduct.tprod ℂ u) := fun u => rfl
  have hx : w ∈ Submodule.span ℂ (Set.range (PiTensorProduct.tprod ℂ (s := fun τ => M.sm τ))) := by
    rw [PiTensorProduct.span_tprod_eq_top]; trivial
  obtain ⟨n, c, gg, hg⟩ := Submodule.mem_span_set'.1 hx
  choose vv hvv using fun j => (gg j).2
  have hw' : w = ∑ j, c j • PiTensorProduct.tprod ℂ (vv j) := by
    rw [← hg]; simp [hvv]
  obtain ⟨φ, hφ⟩ : ∃ φ : M.Vec, GlobalTheory.tprodInnerFun φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hw (GlobalTheory.eq_zero_of_tprodInnerFun w hcon)
  have hφ' : (∑ j, c j * ∏ τ, ⟪((φ τ : M.sm τ) : M.H τ), (vv j τ : M.H τ)⟫_ℂ) ≠ 0 := by
    rw [hw'] at hφ

    simpa [map_sum, GlobalTheory.tprodInnerFun_tprod, Submodule.coe_inner] using hφ
  have hinv : ∀ τ (g : Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ), ∀ x ∈ M.sm τ, Formalism.IndefR.SchurOrthogonalityAlt.piR M τ g x ∈ M.sm τ :=
    fun τ g x hx => GlobalTheory.SmoothStable.rep_mem_sm D V S M τ _ (Formalism.IndefR.SchurOrthogonalityAlt.gm_mem g) x hx
  have htv : ∀ (u : M.Vec) x, (PiTensorProduct.lift.symm t : MMap M) u x = t (PiTensorProduct.tprod ℂ u) x := by
    intro u x; simp [PiTensorProduct.lift_symm]
  have hT : ∀ gs : ∀ τ, Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ,
      ∑ j, c j * L (fun τ => ⟨Formalism.IndefR.SchurOrthogonalityAlt.piR M τ (gs τ) (vv j τ), hinv τ (gs τ) _ (vv j τ).2⟩) = 0 := by
    intro gs
    obtain ⟨P, hPm, hPe⟩ := GlobalTheory.T.multiplicityMap_realTranslate_eq_rightTranslation θ M J χ (PiTensorProduct.lift.symm t) ((mem_multT θ M J χ t).1 ht) gs
    have h0 := hh P hPm
    have e : ∀ x, F x * t w (x * P) = ∑ j, c j * (F x * t (PiTensorProduct.tprod ℂ
        (fun τ => ⟨Formalism.IndefR.SchurOrthogonalityAlt.piR M τ (gs τ) (vv j τ), hinv τ (gs τ) _ (vv j τ).2⟩)) x) := by
      intro x
      rw [hw']

      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e1 := hPe (vv j) x
      rw [htv, htv] at e1
      simp only [Formalism.IndefR.SchurOrthogonalityAlt.piR_apply]
      rw [← e1]
      ring
    simp_rw [e] at h0
    rw [integral_finsetSum _ (fun j _ => (hint _).const_mul (c j))] at h0
    simp_rw [integral_const_mul] at h0
    exact h0
  have hB := GlobalTheory.T.multilinear_zero_of_kills_translates_tensor D.what₂.Tau (fun τ => M.H τ) (fun τ => Formalism.IndefR.SchurOrthogonalityAlt.Gt V τ) (fun τ => Formalism.IndefR.SchurOrthogonalityAlt.piR M τ) (Formalism.IndefR.SchurOrthogonalityAlt.piR_norm M)
    (Formalism.IndefR.SchurOrthogonalityAlt.commutant_scalar M) (fun τ => M.sm τ) (Formalism.IndefR.SchurOrthogonalityAlt.sm_dense M) hinv L K
    (fun u => by rw [hL, hℓ]; exact hK u) n c vv hT (fun τ => (φ τ : M.H τ))
  have hL0 : ∀ u, L u = 0 := fun u => (mul_eq_zero.1 (hB u)).resolve_left hφ'
  have hℓ0 : ℓ w' = 0 := by
    induction w' using PiTensorProduct.induction_on with
    | smul_tprod r u => rw [map_smul, ← hL, hL0, smul_zero]
    | add x y hx hy => rw [map_add (f := _), hx, hy, add_zero]
  rw [← hℓ]; exact hℓ0

end GlobalTheory.TransOrth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfOrthogonalRealTranslatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.integral_eq_zero_of_orthogonal_real_translates : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Mem.Vol.FiniteVolume₂ → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ t ∈ MultT θ M J χ, ∀ (v : GlobalTheory.Unf.Vol V) (F : GA D V → ℂ), GlobalTheory.Unf.IsContAut V F → (∃ C, ∀ g, ‖F g‖ ≤ C) → ∀ w : SmT M, w ≠ 0 → (∀ h ∈ GinfC V, ∫ g in v.𝓕, F g * t w (g * h) ∂v.μ = 0) → ∀ w' : SmT M, ∫ g in v.𝓕, F g * t w' g ∂v.μ = 0 := by
  first | exact @GlobalTheory.TransOrth.integral_eq_zero_of_translates | exact GlobalTheory.TransOrth.integral_eq_zero_of_translates | (intros; apply GlobalTheory.TransOrth.integral_eq_zero_of_translates <;> assumption)
end
end
