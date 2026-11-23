module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResRdApply
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMultiplierEqConstSmulGenerator
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspOnRestrict
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspFormsFiniteDimensionalOfGoodEmb
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantWeightShiftFlatLineDet
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspFormParallelWeightEachComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalMultiplierOfComplexMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicRestrictionSubalgebraFrameDomainIsDom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalGeneratorZpowMulCuspFormMemSpan
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMultiplierEqConstSmulGeneratorStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.commuting_multiplier_eq_const_smul_generator_alt : ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ f ∈ V, rd f ∈ R) → (∀ f ∈ V', rd f ∈ R) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h h' : B, h ∈ R → h' ∈ R → h * h' = 1 → (∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A))) → ∀ T : V →ₗ[K] V', T ≠ 0 → (∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) → ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by
  first | exact @GlobalTheory.commuting_multiplier_eq_const_smul_generator | exact GlobalTheory.commuting_multiplier_eq_const_smul_generator | (intros; apply GlobalTheory.commuting_multiplier_eq_const_smul_generator <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsComponentFiniteDimensionalAndSpannedStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option synthInstance.maxHeartbeats 100000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → (∀ τ i, i < Dw.mult τ → 1 ≤ a (τ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → FiniteDimensional c.F (cuspOn U Z (wtZ a n)) ∧ ∀ P ∈ holSub (U σ).X (modelWt (U σ) (wtZ a n)), (∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z → P k y = 0) → P ∈ Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c))) := by
  intro E _ _ _ H Dw l Xo c r U x h Z σ hσ a n hD hpos hn
  refine ⟨?_, fun P hP hoffZ => ?_⟩
  · have := GlobalTheory.cuspForms_finiteDimensional_of_goodEmb E H Dw l Xo c r U σ hσ (h.unf σ hσ) a n hD
    have hle : cuspOn U Z (wtZ a n) ≤ cusp Xo c U a n := by
      rw [← cuspW_wtZ]
      exact cuspOn_le U Z (wtZ a n)
    exact Submodule.finiteDimensional_of_le hle
  · have hpts : HasPts U Z := GlobalTheory.FlatLine.hasPts U h.pos h.good h.unf Z
    have e : goodOf c σ = σ := ite_eq_left hσ
    have htest := (hpts.1 σ).2
    rw [e] at htest
    have hoff : P ∈ offZero (U σ).X := fun k y hy => hoffZ k y fun hz => hy hz.1
    have hP0 : P ∈ holSub0 (U σ).X (laU (U σ) a n) := ⟨by rwa [← modelWt_wtZ], hoff⟩
    have hsp := h.onto σ hσ a n hD hpos hn hP0
    have hfix : rdU (U σ) (idem Z) * P = P := by
      funext k y
      show rdU (U σ) (idem Z) k y * P k y = P k y
      by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨hd, hl⟩ := hz
        have h1 : rdU (U σ) (idem Z) k y = 1 := by
          simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hd, dite_eq_left]
          rw [evR_idem hl (htest _ ⟨hd, hl⟩ hd)]
          rfl
        rw [h1, one_mul]
      · rw [hoffZ k y hz, mul_zero]
    let g : FDSec (U σ).X →ₗ[ℂ] FDSec (U σ).X := LinearMap.mulLeft ℂ (rdU (U σ) (idem Z))
    have hmap := Submodule.mem_map_of_mem (f := g) hsp
    rw [Submodule.map_span] at hmap
    have hg : g P = P := hfix
    rw [hg] at hmap
    refine Submodule.span_mono ?_ hmap
    rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨idem Z * f, ⟨?_, ?_⟩, ?_⟩
    · rw [← cuspW_wtZ] at hf
      exact GlobalTheory.CompRestr.idem_mul_mem_cuspW h.unf Z hf
    · rw [mul_comm]
      exact mul_mem_suppOn _ (idem_mem_suppOn Z)
    · show rdU (U σ) (idem Z * f) = rdU (U σ) (idem Z) * rdU (U σ) f
      exact GlobalTheory.AllWt.rdU_mul (U σ) _ _
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantWeightShiftFlatLineDetStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.exists_dominant_weight_shift_flatLineDet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (τ : Psi H), Dom a n → (∀ ρ i, i < Dw.mult ρ → 2 ≤ a (ρ, i)) → ∃ a' : (E →+* ℂ) × ℕ → ℕ, Dom a' n ∧ (∀ ρ i, i < Dw.mult ρ → 1 ≤ a' (ρ, i)) ∧ exZ Dw (wtZ a' n) = exZ Dw (wtZ a n + wtOf Dw (flatWt Dw τ) 0) := by
  first | exact @GlobalTheory.FlatShift.exists_shift | exact GlobalTheory.FlatShift.exists_shift | (intros; apply GlobalTheory.FlatShift.exists_shift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspFormParallelWeightEachComponentStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.exists_nonzero_cuspForm_parallelWeight_each_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n ∧ (∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) ∧ 4 * (finrank ℚ E * r) + 4 ≤ n ∧ ∃ f ∈ cuspOn U Z (wtZ a n), f ≠ 0 := by
  first | exact @GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero | exact GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero | (intros; apply GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicRestrictionSubalgebraFrameDomainIsDomStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.FD

theorem _root_.GlobalTheory.T.holomorphicRestrictionSubalgebraFrameDomain_isDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.dom.Nonempty → IsDomain (GlobalTheory.FlatPair.holAlg X) := by
  first | exact @GlobalTheory.FlatPair.holAlg_isDomain | exact GlobalTheory.FlatPair.holAlg_isDomain | (intros; apply GlobalTheory.FlatPair.holAlg_isDomain <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalGeneratorZpowMulCuspFormMemSpanStatement

section

@[expose] public section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem _root_.GlobalTheory.T.horizontalGenerator_zpow_mul_cuspForm_mem_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ), GoodEmb c σ → ∀ (k0 : (U σ).Comp), framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} → ∀ (τ' : ((U σ).X k0).Ψ) (m : ℤ) (b b' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom b n → Dom b' n → (∀ ρ i, i < Dw.mult ρ → 1 ≤ b' (ρ, i)) → 4 * (finrank ℚ E * r) + 4 ≤ n → modelWt (U σ) (wtZ b' n) k0 = modelWt (U σ) (wtZ b n) k0 + m • modelFlat r τ' → ∀ f ∈ cuspOn U Z (wtZ b n), (fun y : ↥((U σ).X k0).dom => horizGen τ' y.1 ^ m * rdU (U σ) f k0 y.1) ∈ Submodule.span ℂ ((fun g : Rul Xo c => fun y : ↥((U σ).X k0).dom => rdU (U σ) g k0 y.1) '' (cuspOn U Z (wtZ b' n) : Set (Rul Xo c))) := by
  first | exact @GlobalTheory.FlatCore.MulSpan.horizGen_zpow_mul_rdU_mem_span | exact GlobalTheory.FlatCore.MulSpan.horizGen_zpow_mul_rdU_mem_span | (intros; apply GlobalTheory.FlatCore.MulSpan.horizGen_zpow_mul_rdU_mem_span <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPairQuotientHorizontalGenerator

section

@[expose] public section

noncomputable section
namespace GlobalTheory.FlatPair
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

section Lemmas
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

theorem relab_mem {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf V) (τ : Psi H) (k : V.Comp) :
    relab c σ τ.1 ∈ (V.X k).Ψ :=
  ((hU.2.1 k).2 _).2 (by
    have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
    exact (congrArg σ (Subtype.ext τ.2)).trans hσ0)

theorem modelWt_shift {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf V) (τ : Psi H)
    {G G' : WTZ E} (hG : Even G.2) (h : exZ Dw G' = exZ Dw (G + wtOf Dw (flatWt Dw τ) 0)) (k : V.Comp)
    (hτ : relab c σ τ.1 ∈ (V.X k).Ψ) : modelWt V G' k = modelWt V G k + modelFlat r ⟨_, hτ⟩ := by
  rw [modelWt_congr V hσ hU h, modelWt_add V hG (even_wtOf _ _), modelWt_flatWt V hσ hU τ k hτ]

theorem cuspOn_congr {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (Z : Comp Xo c)
    {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') : cuspOn U Z G = cuspOn U Z G' := by
  ext f
  simp only [cuspOn, Submodule.mem_inf, mem_cuspW, h]
  refine and_congr_left fun _ => and_congr_right fun _ => forall₂_congr fun σ hσ => ?_
  rw [modelWt_congr (U σ) hσ (hU σ hσ) h]

theorem res_indep {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ} (hL : Laws U x) (Z : Comp Xo c)
    (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (k0 : (U σ).Comp)
    (hk : framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom}) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    (∀ (m : ℕ) (b : Fin m → Rul Xo c), (∀ i, b i ∈ sec Xo c a n) → (∀ i, b i ∈ suppOn Z) →
      LinearIndependent c.F b →
      LinearIndependent ℂ (fun i => fun y : ↥((U σ).X k0).dom => rdU (U σ) (b i) k0 y.1)) ∧
    ∀ f ∈ sec Xo c a n, f ∈ suppOn Z → f ≠ 0 → ∃ y : ↥((U σ).X k0).dom, rdU (U σ) f k0 y.1 ≠ 0 := by
  have hR := GlobalTheory.reading_linearIndependent_and_injective GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ H Dw l Xo c σ r
    (Formalism.L2.PjFree.Unf.ofPj (U σ)) (hL.unf σ hσ) a n
  simp only [Formalism.L2.PjFree.rdU_ofPj] at hR
  have hoff : ∀ f ∈ suppOn Z, ∀ k y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∉ framesOn (U σ) Z →
      rdU (U σ) f k y = 0 := fun f hf k y hz => rdU_eq_zero (U σ) hf hz
  refine ⟨fun m b hb hs hli => ?_, fun f hf hs hne => ?_⟩
  · have h0 : LinearIndependent ℂ (fun i => rdU (U σ) (b i)) := hR.1 m b hb hli
    rw [Fintype.linearIndependent_iff] at h0 ⊢
    intro w hw
    refine h0 w ?_
    funext k y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
    · rw [hk] at hz
      obtain ⟨rfl, hy⟩ := hz
      have := congrFun hw ⟨y, hy⟩
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using this
    · exact Finset.sum_eq_zero fun i _ => by rw [hoff _ (hs i) k y hz, mul_zero]
  · by_contra hall
    push_neg at hall
    refine hne (hR.2 f hf fun k y hy => ?_)
    by_cases hz : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
    · rw [hk] at hz
      obtain ⟨rfl, hy'⟩ := hz
      exact hall ⟨y, hy'⟩
    · exact hoff f hs k y hz

theorem horizGen_mem (X : Data E r) (τ : X.Ψ) :
    (fun y : ↥X.dom => horizGen τ y.1) ∈ holAlg X ∧ (fun y : ↥X.dom => (horizGen τ y.1)⁻¹) ∈ holAlg X ∧
      ∀ y ∈ X.dom, horizGen τ y ≠ 0 := by
  have hdet : Differentiable ℂ (fun y : Frame X.Ψ r => (mat y τ).det) := by
    have e : (fun y : Frame X.Ψ r => (mat y τ).det) =
        fun y => ∑ p : Equiv.Perm (Fin r), ((Equiv.Perm.sign p : ℤ) : ℂ) * ∏ i, y τ (p i) i := by
      funext y
      rw [Matrix.det_apply]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Units.smul_def, zsmul_eq_mul]
      rfl
    rw [e]
    fun_prop
  have hne : ∀ y ∈ X.dom, (mat y τ).det ≠ 0 := fun y hy => (hy τ).1
  refine ⟨⟨fun y => horizGen τ y, ?_, fun y => rfl⟩, ⟨fun y => (horizGen τ y)⁻¹, ?_, fun y => rfl⟩,
    fun y hy => inv_ne_zero (hne y hy)⟩
  · exact (hdet.differentiableOn).inv hne
  · have : (fun y => (horizGen τ y)⁻¹) = fun y : Frame X.Ψ r => (mat y τ).det := by
      funext y; simp [horizGen]
    rw [this]; exact hdet.differentiableOn

theorem resRd_mem_holAlg {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} (σ : c.F →+* ℂ) (hσ : GoodEmb c σ)
    (hT : AllTest Xo c) (k : (U σ).Comp) (G : WTZ E) (f : Rul Xo c) (hf : f ∈ cuspW Xo c U G) :
    resRd (U σ) hT k f ∈ holAlg ((U σ).X k) := by
  have h1 := (mem_cuspW.1 hf).2 σ hσ
  have h2 : ∀ P ∈ holSub (U σ).X (modelWt (U σ) G), DifferentiableOn ℂ (P k) ((U σ).X k).dom := by
    intro P hP
    induction hP using Submodule.span_induction with
    | mem P hP => exact (hP k).1.1.1
    | zero => exact differentiableOn_const 0
    | add P Q _ _ hP hQ => exact hP.add hQ
    | smul a P _ hP => exact (differentiableOn_const a).mul hP
  exact ⟨rdU (U σ) f k, h2 _ h1, fun y => rfl⟩

end Lemmas

set_option synthInstance.maxHeartbeats 200000 in
theorem flat_pair : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E)
    (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H), ∃ (G : WTZ E) (f g : Rul Xo c), Even G.2 ∧
      f ∈ cuspOn U Z G ∧ g ∈ cuspOn U Z (G + wtOf Dw (flatWt Dw τ) 0) ∧ f ≠ 0 ∧ IsFlatQuot U Z τ f g := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ
  obtain ⟨a, n, hD, h2, hn, f0, hf0, hf0ne⟩ := GlobalTheory.T.exists_nonzero_cuspForm_parallelWeight_each_component E H Dw l Xo c r U x hL Z
  obtain ⟨a', hD', h1', hex⟩ := GlobalTheory.T.exists_dominant_weight_shift_flatLineDet E H Dw a n τ hD h2
  have h1 : ∀ ρ i, i < Dw.mult ρ → 1 ≤ a (ρ, i) := fun ρ i hi => le_trans (by norm_num) (h2 ρ i hi)
  have hT : AllTest Xo c :=
    GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange E H Dw l Xo c
  have hEv : Even (wtZ a n).2 := by
    obtain ⟨m, hm⟩ := hD.2
    exact ⟨m, by simp [wtZ, hm]⟩
  have hVV' : cuspOn U Z (wtZ a' n) = cuspOn U Z (wtZ a n + wtOf Dw (flatWt Dw τ) 0) :=
    cuspOn_congr hL.unf Z hex

  have hsec : ∀ (b : (E →+* ℂ) × ℕ → ℕ), cuspOn U Z (wtZ b n) ≤ sec Xo c b n := fun b f hf => by
    have := cuspW_le_secZ (U := U) (wtZ b n) (cuspOn_le U Z _ hf)
    rwa [AllWt.exZ_wtZ, secZ_nat] at this
  have hsupp : ∀ (G : WTZ E), cuspOn U Z G ≤ suppOn Z := fun G => inf_le_right
  have pk : ∀ σ, GoodEmb c σ → ∃ (k0 : (U σ).Comp) (hτ : relab c σ τ.1 ∈ ((U σ).X k0).Ψ),
      framesOn (U σ) Z = {z | z.1 = k0 ∧ z.2 ∈ ((U σ).X z.1).dom} ∧
      (∀ f ∈ cuspOn U Z (wtZ a n), (fun y : ↥((U σ).X k0).dom => horizGen ⟨_, hτ⟩ y.1) * resRd (U σ) hT k0 f ∈
        Submodule.span ℂ (resRd (U σ) hT k0 '' (cuspOn U Z (wtZ a' n) : Set (Rul Xo c)))) ∧
      (∀ f ∈ cuspOn U Z (wtZ a' n), (fun y : ↥((U σ).X k0).dom => (horizGen ⟨_, hτ⟩ y.1)⁻¹) * resRd (U σ) hT k0 f ∈
        Submodule.span ℂ (resRd (U σ) hT k0 '' (cuspOn U Z (wtZ a n) : Set (Rul Xo c)))) := by
    intro σ hσ
    obtain ⟨k0, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
    have hτ := relab_mem (U σ) hσ (hL.unf σ hσ) τ k0
    have hw := modelWt_shift (U σ) hσ (hL.unf σ hσ) τ hEv hex k0 hτ
    refine ⟨k0, hτ, hk, fun f hf => ?_, fun f hf => ?_⟩
    · have := GlobalTheory.T.horizontalGenerator_zpow_mul_cuspForm_mem_span E H Dw l Xo c r U x hL Z σ hσ k0 hk ⟨_, hτ⟩ 1 a a' n hD hD' h1' hn (by rw [hw, one_smul]) f hf
      convert this using 1 <;> first | rfl | (funext y; simp [resRd_apply])
    · have := GlobalTheory.T.horizontalGenerator_zpow_mul_cuspForm_mem_span E H Dw l Xo c r U x hL Z σ hσ k0 hk ⟨_, hτ⟩ (-1) a' a n hD' hD h1 hn
        (by rw [hw, neg_one_smul, add_neg_cancel_right]) f hf
      convert this using 1 <;> first | rfl | (funext y; simp [resRd_apply])
  obtain ⟨σ0, hσ0⟩ : ∃ σ, GoodEmb c σ := ⟨_, goodEmb_goodOf c c.F.val.toRingHom⟩
  haveI : FiniteDimensional c.F (cuspOn U Z (wtZ a n)) :=
    (GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned E H Dw l Xo c r U x hL Z σ0 hσ0 a n hD h1 hn).1
  haveI : FiniteDimensional c.F (cuspOn U Z (wtZ a' n)) :=
    (GlobalTheory.T.cuspForms_component_finiteDimensional_and_spanned E H Dw l Xo c r U x hL Z σ0 hσ0 a' n hD' h1' hn).1
  have hprod : ∀ f ∈ cuspOn U Z (wtZ a n), ∀ g ∈ cuspOn U Z (wtZ a' n),
      f * g ∈ sec Xo c (a + a') (n + n) ⊓ suppOn Z := by
    intro f hf g hg
    have e : exZ Dw (wtZ (a + a') (n + n)) = exZ Dw (wtZ a n) + exZ Dw (wtZ a' n) := by
      rw [wtZ_add]; funext i; exact exZ_add _ _ i
    have hm := mul_mem_secZ (cuspW_le_secZ (U := U) _ (cuspOn_le U Z _ hf))
      (cuspW_le_secZ (U := U) _ (cuspOn_le U Z _ hg))
    rw [← e, AllWt.exZ_wtZ, secZ_nat] at hm
    refine ⟨hm, ?_⟩
    rw [mul_comm]
    exact mul_mem_suppOn g (hsupp _ hf)
  obtain ⟨k0, hτ0, hk0, hA0, -⟩ := pk σ0 hσ0
  obtain ⟨T, hT0, hTc⟩ := GlobalTheory.T.exists_rational_multiplier_of_complex_multiplier c.F (Rul Xo c) (↥((U σ0).X k0).dom → ℂ) σ0 (resRd (U σ0) hT k0)
    (resRd_smul (U σ0) hT k0) (cuspOn U Z (wtZ a n)) (cuspOn U Z (wtZ a' n))
    (fun m b hb hli => by
      have hb' : ∀ i, b i ∈ sec Xo c (a + a') (n + n) ⊓ suppOn Z := fun i =>
        (Submodule.mul_le.2 hprod) (hb i)
      exact (res_indep hL Z σ0 hσ0 k0 hk0 (a + a') (n + n)).1 m b (fun i => (hb' i).1) (fun i => (hb' i).2) hli)
    (fun y => horizGen ⟨_, hτ0⟩ y.1) hA0 ⟨f0, hf0, fun h0 => by
      obtain ⟨y, hy⟩ := (res_indep hL Z σ0 hσ0 k0 hk0 a n).2 f0 (hsec a hf0) (hsupp _ hf0) hf0ne
      have := congrFun h0 y
      simp only [Pi.mul_apply, resRd_apply, Pi.zero_apply, mul_eq_zero] at this
      rcases this with h | h
      · exact (horizGen_mem _ _).2.2 y.1 y.2 h
      · exact hy h⟩
  refine ⟨wtZ a n, f0, T ⟨f0, hf0⟩, hEv, hf0, hVV' ▸ (T ⟨f0, hf0⟩).2, hf0ne, fun σ hσ => ?_⟩
  obtain ⟨k1, hτ, hk, hA, hA'⟩ := pk σ hσ
  obtain ⟨y0, -⟩ := (res_indep hL Z σ hσ k1 hk a n).2 f0 (hsec a hf0) (hsupp _ hf0) hf0ne
  haveI := GlobalTheory.T.holomorphicRestrictionSubalgebraFrameDomain_isDomain E r ((U σ).X k1) ⟨y0.1, y0.2⟩
  obtain ⟨hh, hh', hne⟩ := horizGen_mem ((U σ).X k1) ⟨_, hτ⟩
  obtain ⟨α, hα, hαT⟩ := GlobalTheory.T.commuting_multiplier_eq_const_smul_generator_alt c.F (Rul Xo c) (↥((U σ).X k1).dom → ℂ) σ (resRd (U σ) hT k1)
    (resRd_smul _ _ _) (holAlg ((U σ).X k1)) (cuspOn U Z (wtZ a n)) (cuspOn U Z (wtZ a' n))
    (fun f hf => resRd_mem_holAlg σ hσ hT k1 _ f (cuspOn_le U Z _ hf))
    (fun f hf => resRd_mem_holAlg σ hσ hT k1 _ f (cuspOn_le U Z _ hf))
    (fun m b hb hli => (res_indep hL Z σ hσ k1 hk a n).1 m b (fun i => hsec a (hb i)) (fun i => hsupp _ (hb i)) hli)
    (fun m b hb hli => (res_indep hL Z σ hσ k1 hk a' n).1 m b (fun i => hsec a' (hb i)) (fun i => hsupp _ (hb i))
      hli)
    _ _ hh hh' (by funext y; exact mul_inv_cancel₀ (hne y.1 y.2)) hA' T hT0 hTc
  refine ⟨α, hα, fun k hτk y hy => ?_⟩
  rw [hk] at hy
  obtain ⟨rfl, hyd⟩ := hy
  have e := congrFun (hαT ⟨f0, hf0⟩) ⟨y, hyd⟩
  simp only [resRd_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul] at e
  rw [e]
  ring

end GlobalTheory.FlatPair
end
end
end
