module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsJInvariantInModularFunctionFractionFieldStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmpPropsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeOfDvdStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldIsAlgebraicAdjoinJInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JTLevelOneStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOverStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionFractionFieldOfQExpansionsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldAnSlGermStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldBoundedDenominatorsStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOverStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldExpUpperTriangularStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldExpansionConvergesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldNonempty
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSaturation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSlRightActionStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityModularFunctionFractionField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExistsGammaLevel

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem sl_ofSL_io_of_gamma {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (T : Frac Ω ε) (a : ring ε.range) (M : ℕ)
    (ha : ∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, (a : ℍ → ℂ) (γ • τ) = (a : ℍ → ℂ) τ)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma M) : T.sl (ofSL γ) (T.io a) = T.io a := by
  apply T.sl_io
  rw [GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob.2.2.1 γ a]
  funext τ
  exact (ha γ hγ τ).symm

theorem frac_exists_level (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K) :
    ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f := by
  obtain ⟨a, b, hb, hf⟩ := T.io_surj f
  obtain ⟨N₁, w₁, hN₁, h₁⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 a).1 a.2
  obtain ⟨N₂, w₂, hN₂, h₂⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 b).1 b.2
  have hM : 0 < N₁ * N₂ := Nat.mul_pos hN₁ hN₂
  have h₁' := GlobalTheory.T.lv_mono_of_dvd_of_le ε.range N₁ (N₁ * N₂) w₁ w₁ a hM (dvd_mul_right _ _) le_rfl h₁
  have h₂' := GlobalTheory.T.lv_mono_of_dvd_of_le ε.range N₂ (N₁ * N₂) w₂ w₂ b hM (dvd_mul_left _ _) le_rfl h₂
  refine ⟨N₁ * N₂, hM, fun γ hγ => ?_⟩
  have ea := sl_ofSL_io_of_gamma T a _ h₁'.1 γ hγ
  have eb := sl_ofSL_io_of_gamma T b _ h₂'.1 γ hγ
  have hib : T.io b ≠ 0 := by
    intro h
    apply hb
    apply T.io_inj
    rw [h, map_zero]
  have key : T.sl (ofSL γ) f * T.io b = f * T.io b := by
    have := congrArg (T.sl (ofSL γ)) hf
    rw [map_mul, eb, ea] at this
    rw [this, hf]
  exact mul_right_cancel₀ hib key

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExistsGammaLevelStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.fractionField_exists_gamma_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f := by
  first | exact @GlobalTheory.FN.frac_exists_level | exact GlobalTheory.FN.frac_exists_level | (intros; apply GlobalTheory.FN.frac_exists_level <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldConstAndQuotient

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_const_and_quot : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ c : Ω, T.an (algebraMap Ω T.K c) = ((fun _ => ε c : ℂ → ℂ) : Mero)) ∧ ∀ f : T.K, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧ T.an f * (b : Mero) = (a : Mero) := by
  intro Ω _ _ _ ε T
  have hmem := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs := fun a =>
    ((GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict).2.1 _).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ε.range _ ((hmem.1 _).1 a.2))
  refine ⟨fun c => ?_, fun f => ?_⟩
  · have hc : (fun _ : ℍ => ε c) ∈ ring ε.range := (hmem.1 _).2 (hmem.2 _ ⟨c, rfl⟩)
    rw [← T.io_c c ⟨_, hc⟩ rfl, T.an_io]
    rfl
  · obtain ⟨a, b, hb, h⟩ := T.io_surj f
    refine ⟨up (a : ℍ → ℂ), up (b : ℍ → ℂ), hdiff a, hdiff b, ?_, ?_⟩
    · intro h0
      have h1 : T.an (T.io b) = T.an (T.io 0) := by
        rw [T.an_io, map_zero, map_zero]; exact h0
      exact hb (T.io_inj ((GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.2.2 h1))
    · have := congrArg T.an h
      rw [map_mul, T.an_io, T.an_io] at this
      exact this

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldConstAndQuotientStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_const_and_quotient : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ c : Ω, T.an (algebraMap Ω T.K c) = ((fun _ => ε c : ℂ → ℂ) : Mero)) ∧ ∀ f : T.K, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧ T.an f * (b : Mero) = (a : Mero) := by
  first | exact @GlobalTheory.FN.frac_const_and_quot | exact GlobalTheory.FN.frac_const_and_quot | (intros; apply GlobalTheory.FN.frac_const_and_quot <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldNonemptyStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_nonempty : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), Nonempty (Frac Ω ε) := by
  first | exact @GlobalTheory.FN.frac_nonempty | exact GlobalTheory.FN.frac_nonempty | (intros; apply GlobalTheory.FN.frac_nonempty <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldSaturationStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modularFunctionFractionField_saturation : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a b : ℂ → ℂ) (M : ℕ), 0 < M → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (b : Mero) ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ((fun z => a (mob (ofSL γ) z) * b z) : Mero) = ((fun z => a z * b (mob (ofSL γ) z)) : Mero)) → (∃ P : Polynomial T.K, P ≠ 0 ∧ P.eval₂ T.an (((a / b : ℂ → ℂ)) : Mero) = 0) → ∃ f : T.K, T.an f * (b : Mero) = (a : Mero) := by
  first | exact @GlobalTheory.fn_sat | exact GlobalTheory.fn_sat | (intros; apply GlobalTheory.fn_sat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityModularFunctionFractionFieldStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.shimuraReciprocity_modularFunctionFractionField : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (M : ℕ) (f : T.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f) → ∀ ζ : Ω, IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  first | exact @GlobalTheory.FNRecip.main | exact GlobalTheory.FNRecip.main | (intros; apply GlobalTheory.FNRecip.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsModularFunctionTowerAlgebraicCoefficients

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem tower_exists : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), ∃ T : Tower Ω ε, IsStd T := by
  intro Ω _ _ _ ε
  obtain ⟨T⟩ := GlobalTheory.T.modularFunctionFractionField_nonempty Ω ε
  obtain ⟨a, ha, hinv, h1, h2, h3⟩ := GlobalTheory.T.exists_jInvariant_in_modularFunctionFractionField Ω ε T
  have hgerm := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  have hj := GlobalTheory.T.lv_jT_one_and_jT_smul_eq
  have hhol : DifferentiableOn ℂ (up jT) Hs :=
    (hgerm.2.1 jT).1 (GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver ⊤ jT ⟨1, 1, one_pos, (hj ⊤).1⟩)
  refine ⟨{ K := T.K, exp := T.exp, sl := T.sl, sl_one := (GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T).1, sl_mul := (GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T).2,
            gal := T.gal, gal_exp := T.gal_exp,
            an := T.an, an_c := (GlobalTheory.T.modularFunctionFractionField_const_and_quotient Ω ε T).1, an_sl := GlobalTheory.T.modularFunctionFractionField_an_sl_germ Ω ε T, an_mero := (GlobalTheory.T.modularFunctionFractionField_const_and_quotient Ω ε T).2,
            an_exp := fun f => (GlobalTheory.T.modularFunctionFractionField_expansion_converges Ω ε T f).2,
            level := GlobalTheory.T.fractionField_exists_gamma_level Ω ε T, exp_upper := GlobalTheory.T.modularFunctionFractionField_exp_upperTriangular Ω ε T, recip := GlobalTheory.T.shimuraReciprocity_modularFunctionFractionField Ω ε T,
            jK := T.io a, j_inv := hinv, j_exp := ⟨h1, h2, h3⟩,
            j_hol := ⟨up jT, by rw [T.an_io, ha]; rfl, hhol⟩,
            alg_j := GlobalTheory.T.fractionField_isAlgebraic_adjoin_jInvariant Ω ε T a ha, bdd := GlobalTheory.T.modularFunctionFractionField_bounded_denominators Ω ε T, sat := GlobalTheory.T.modularFunctionFractionField_saturation Ω ε T,
            mem_q := GlobalTheory.T.mem_modularFunctionFractionField_of_qExpansions Ω ε T }, ?_⟩
  show T.an (T.io a) = germ jT
  rw [T.an_io, ha]

end GlobalTheory.FN
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsModularFunctionTowerAlgebraicCoefficientsStatement

section

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.exists_modular_function_tower_algebraic_coefficients : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ), ∃ T : Tower Ω ε, IsStd T := by
  first | exact @GlobalTheory.FN.tower_exists | exact GlobalTheory.FN.tower_exists | (intros; apply GlobalTheory.FN.tower_exists <;> assumption)
end
end
