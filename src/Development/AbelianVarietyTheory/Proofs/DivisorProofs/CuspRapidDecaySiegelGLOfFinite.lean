module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRapidDecaySiegelConeRealPointsStatement
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Mathlib.Tactic.Linter.Style
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorActStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetAdelicGLExistsCompactDecompositionStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealDiagonalInfGLEqPositiveIdeleDiagonal

section

@[expose] public section

noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic
  GroundTheory.Automorphic.Reduction

namespace GlobalTheory.SiegelTorusInf

theorem exists_diag_infGL (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i) : ∃ d : GL (Fin a) (Cinf E), d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) ∧
      diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) = infGL E a d := by
  have h0 : ∀ i, (r i : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.2 (hr i).ne'
  refine ⟨⟨Matrix.diagonal (fun i => fun _ => (r i : ℂ)), Matrix.diagonal (fun i => fun _ => (r i : ℂ)⁻¹), ?_, ?_⟩,
    rfl, ?_⟩
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    exact mul_inv_cancel₀ (h0 i)
  · rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i w
    exact inv_mul_cancel₀ (h0 i)
  · have key : ∀ i, ((posIdele (K := E) (r i) (hr i) : IdeleGroup E) : Ad E) =
        1 - sInf E 1 + sInf E (fun _ => (r i : ℂ)) := fun i => by
      rw [GlobalTheory.CuspBoundSiegel.posIdele_congr (hr i) (Real.exp_pos _) (Real.exp_log (hr i)).symm,
        GlobalTheory.CuspBoundSiegel.posIdele_exp]
      change 1 - sInf E 1 + sInf E _ = _
      congr 2
      funext w
      change Complex.exp (Real.log (r i) : ℂ) = (r i : ℂ)
      rw [← Complex.ofReal_exp, Real.exp_log (hr i)]
    refine Units.ext ?_
    rw [coe_diagUnits]
    refine Matrix.ext fun i j => ?_
    change _ = (1 : Matrix (Fin a) (Fin a) (Ad E)) i j - sInf E ((1 : Matrix (Fin a) (Fin a) (Cinf E)) i j) +
      sInf E (Matrix.diagonal (fun i => (fun _ => (r i : ℂ) : Cinf E)) i j)
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Matrix.one_apply_eq]
      exact key i
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, Matrix.one_apply_ne h,
        map_zero, sub_zero, add_zero]

end GlobalTheory.SiegelTorusInf

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealDiagonalInfGLEqPositiveIdeleDiagonalStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i), ∃ d : GL (Fin a) (Cinf E), d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) ∧ diagUnits a (fun i => posIdele (K := E) (r i) (hr i)) = infGL E a d := by
  first | exact @GlobalTheory.SiegelTorusInf.exists_diag_infGL | exact GlobalTheory.SiegelTorusInf.exists_diag_infGL | (intros; apply GlobalTheory.SiegelTorusInf.exists_diag_infGL <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTranslatesSmoothFunctionOfCompact

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem finite_translates_of_isCompact (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (φ : Sm E a) (h : IsOpen {k | finRep E a k φ = φ})
    (Kf : Set (GL (Fin a) (Af E))) (hK : IsCompact Kf) :
    ∃ S : Finset (GL (Fin a) (Af E)), ∀ f ∈ Kf, ∃ f' ∈ S,
      finRep E a f φ = finRep E a f' φ := by
  have hn : ∀ f ∈ Kf, {g | finRep E a g φ = finRep E a f φ} ∈ nhds f := by
    intro f _
    have hc : Continuous (fun g : GL (Fin a) (Af E) => f⁻¹ * g) :=
      continuous_const.mul continuous_id
    have ho := h.preimage hc
    refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
    · simp
    · intro g hg
      have hg' : finRep E a (f⁻¹ * g) φ = φ := hg
      have e : g = f * (f⁻¹ * g) := by simp
      show finRep E a g φ = finRep E a f φ
      calc finRep E a g φ = finRep E a (f * (f⁻¹ * g)) φ := by rw [← e]
        _ = finRep E a f (finRep E a (f⁻¹ * g) φ) := by rw [map_mul]; rfl
        _ = finRep E a f φ := by rw [hg']
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun f => {g | finRep E a g φ = finRep E a f φ}) hn
  refine ⟨t, fun f hf => ?_⟩
  have := ht hf
  simp only [Set.mem_iUnion] at this
  obtain ⟨f', hf', h'⟩ := this
  exact ⟨f', hf', h'⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTranslatesSmoothFunctionOfCompactStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.finite_translates_smoothFunction_of_compact : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a), IsOpen {k | finRep E a k φ = φ} → ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ S : Finset (GL (Fin a) (Af E)), ∀ f ∈ Kf, ∃ f' ∈ S, finRep E a f φ = finRep E a f' φ := by
  first | exact @GlobalTheory.finite_translates_of_isCompact | exact GlobalTheory.finite_translates_of_isCompact | (intros; apply GlobalTheory.finite_translates_of_isCompact <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspRapidDecaySiegelGLOfFinite

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspRapidDecaySiegelGL_of_finite (hfin : GlobalTheory.Published.AutomorphicFormsFiniteGL) :
    GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ ω hω hωB _ t ht lam
  obtain ⟨Ω, Kf, hΩ, hKf, hgeom⟩ := GlobalTheory.T.siegelSet_adelicGL_exists_compact_decomposition E a ω hω hωB t ht
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_translates_smoothFunction_of_compact E a φ hφ.1.level Kf hKf
  have hcore := fun f' : GL (Fin a) (Af E) =>
    GlobalTheory.T.cuspForm_rapidDecay_siegelCone_realPoints hfin E a (finRep E a f' φ) (GlobalTheory.T.isCuspForm_operator_act hfin E a (.fin f') φ hφ) Ω hΩ t ht lam
  choose C hC0 hC using hcore
  refine ⟨∑ f' ∈ S, C f', fun b hb r hr hchain hprod k hk => ?_⟩
  obtain ⟨d, hd, hdiag⟩ := GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal E a r hr
  rw [hdiag]
  obtain ⟨c, hc, f, hf, heq⟩ := hgeom r d hr hchain hd b hb k hk
  rw [heq]
  obtain ⟨f', hf', hff'⟩ := hS f hf
  have e : φ.1 (infGL E a (d * c) * finGL E a f) = (finRep E a f' φ).1 (infGL E a (d * c)) := by
    rw [← hff']; rfl
  rw [e]
  refine (hC f' r d hr hchain hd hprod c hc).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hC0 i) hf')
    (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _)

end GlobalTheory
end
end
