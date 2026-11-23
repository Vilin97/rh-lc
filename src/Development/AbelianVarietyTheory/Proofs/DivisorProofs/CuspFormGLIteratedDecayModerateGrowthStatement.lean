module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Aesop.Main
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspForm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AdlEqZeroOfMemNbhd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrowthOfTame
import GroundTheory.AutomorphicForms.LocallyProfinite
import GroundTheory.AutomorphicForms.ReductionBlock
import GroundTheory.GlobalFields.KummerTheory.LocalIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelConeSmoothVariationAlongBoundedUnipotentStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentRadicalAdelicEqRatMulBoundedRealMulLeveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightMulLeOfIsCompactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorActStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainRationalBlockUnipotentGL

section

@[expose] public section

noncomputable section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open Topology

namespace GlobalTheory.CuspRep

theorem discreteTopology_ratN (E : Type) [Field E] [NumberField E] (a s : ℕ) :
    DiscreteTopology (ratN E a s) := by
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hU : IsOpen (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd (F := E)) :=
    isOpen_set_pi Set.finite_univ fun _ _ => Formalism.IndefR.Eqv.G5.adl_isOpen_nbhd
  have h : ({0} : Set (ratN E a s)) =
      Subtype.val ⁻¹' (Set.univ.pi fun _ : BlockIx a s => Formalism.IndefR.Eqv.G5.adlNbhd (F := E)) := by
    ext ⟨x, q, hq⟩
    constructor
    · intro hx p _
      have : x = 0 := congrArg Subtype.val hx
      subst this
      exact Formalism.IndefR.Eqv.G5.adl_zero_mem_nbhd
    · intro hx
      subst hq
      apply Subtype.ext
      funext p
      have h0 : q p = 0 := Formalism.IndefR.Eqv.G5.adl_eq_zero_of_mem_nbhd (q p) (hx p (Set.mem_univ _))
      show algebraMap E (Ad E) (q p) = 0
      rw [h0, map_zero]
  rw [h]
  exact hU.preimage continuous_subtype_val

theorem exists_isAddFundamentalDomain_ratN : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ) [MeasurableSpace (BlockIx a s → Ad E)] [BorelSpace (BlockIx a s → Ad E)] (μ : Measure (BlockIx a s → Ad E)) [μ.IsAddHaarMeasure], ∃ 𝓕 : Set (BlockIx a s → Ad E), IsAddFundamentalDomain (ratN E a s) 𝓕 μ ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 < ⊤ := by
  intro E _ _ _ a s _ _ μ _
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := discreteTopology_ratN E a s
  haveI := countable_ratN (E := E) (a := a) s
  obtain ⟨D, -, -, hD⟩ := GlobalTheory.exists_isAddFundamentalDomain_addSubgroup (ratN E a s)
  haveI : MeasurableConstVAdd (ratN E a s) (BlockIx a s → Ad E) :=
    ⟨fun γ => (continuous_const.add continuous_id :
      Continuous fun x : BlockIx a s → Ad E => (γ : BlockIx a s → Ad E) + x).measurable⟩
  haveI : VAddInvariantMeasure (ratN E a s) (BlockIx a s → Ad E) μ :=
    ⟨fun γ t _ => measure_preimage_add μ (γ : BlockIx a s → Ad E) t⟩
  have hμ : μ ≠ 0 := fun h => by
    have := isOpen_univ.measure_ne_zero μ Set.univ_nonempty
    rw [h] at this
    exact this rfl
  exact ⟨D, hD μ, (hD μ).measure_ne_zero hμ, covol_lt_top μ D (hD μ)⟩

end GlobalTheory.CuspRep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainRationalBlockUnipotentGLStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.exists_fundamentalDomain_rationalBlockUnipotentGL : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (s : ℕ) [MeasurableSpace (BlockIx a s → Ad E)] [BorelSpace (BlockIx a s → Ad E)] (μ : Measure (BlockIx a s → Ad E)) [μ.IsAddHaarMeasure], ∃ 𝓕 : Set (BlockIx a s → Ad E), IsAddFundamentalDomain (ratN E a s) 𝓕 μ ∧ μ 𝓕 ≠ 0 ∧ μ 𝓕 < ⊤ := by
  first | exact @GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN | exact GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN | (intros; apply GlobalTheory.CuspRep.exists_isAddFundamentalDomain_ratN <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormNormLeOfUnipotentVariation

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

noncomputable section

namespace GlobalTheory.CuspRep

theorem norm_le_of_unip_variation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a),
    IsCuspForm ψ → ∀ s : ℕ, 0 < s → s < a → ∀ (g : GA E a) (e : ℝ),
      (∀ x : BlockIx a s → Ad E, ‖ψ.1 (unip x * g) - ψ.1 g‖ ≤ e) → ‖ψ.1 g‖ ≤ e := by
  intro E _ _ _ a ψ hψ s hs0 hsa g e he
  letI : MeasurableSpace (BlockIx a s → Ad E) := borel _
  haveI : BorelSpace (BlockIx a s → Ad E) := ⟨rfl⟩
  set μ : Measure (BlockIx a s → Ad E) := Measure.addHaar with hμ
  obtain ⟨𝓕, h𝓕, h0, htop⟩ := GlobalTheory.T.exists_fundamentalDomain_rationalBlockUnipotentGL E a s μ
  have hc := ContAut.continuous_of_isOpen_stab E a ψ hψ.1.level
  have hI := CuspidalL2GL.integrableOn_unip hc hψ.1.left μ h𝓕 g
  have hz : ∫ x in 𝓕, ψ.1 (unip x * g) ∂μ = 0 := hψ.2 s hs0 hsa μ 𝓕 inferInstance h𝓕 g
  have key : ∫ x in 𝓕, (ψ.1 g - ψ.1 (unip x * g)) ∂μ = μ.real 𝓕 • ψ.1 g := by
    have h1 : IntegrableOn (fun _ => ψ.1 g) 𝓕 μ := integrableOn_const htop.ne
    rw [integral_sub h1 hI, hz, setIntegral_const, sub_zero]
  have hb : ‖∫ x in 𝓕, (ψ.1 g - ψ.1 (unip x * g)) ∂μ‖ ≤ e * μ.real 𝓕 :=
    norm_setIntegral_le_of_norm_le_const htop fun x _ => by rw [norm_sub_rev]; exact he x
  rw [key, norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg, mul_comm] at hb
  have hpos : 0 < μ.real 𝓕 := ENNReal.toReal_pos h0 htop.ne
  exact le_of_mul_le_mul_right hb hpos

end GlobalTheory.CuspRep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormNormLeOfUnipotentVariationStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.cuspForm_norm_le_of_unipotent_variation : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ s : ℕ, 0 < s → s < a → ∀ (g : GA E a) (e : ℝ), (∀ x : BlockIx a s → Ad E, ‖ψ.1 (unip x * g) - ψ.1 g‖ ≤ e) → ‖ψ.1 g‖ ≤ e := by
  first | exact @GlobalTheory.CuspRep.norm_le_of_unip_variation | exact GlobalTheory.CuspRep.norm_le_of_unip_variation | (intros; apply GlobalTheory.CuspRep.norm_le_of_unip_variation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLSiegelConeDecayOneStep

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspForm_decay_step : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ t : ℝ, 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  intro E _ _ _ a ψ hψ t ht i j hij Ω hΩ
  have hL : {k | finRep E a k ψ = ψ} ∈ nhds (1 : GL (Fin a) (Af E)) :=
    hψ.1.level.mem_nhds (by simp)
  obtain ⟨R, hR0, hcov⟩ := GlobalTheory.T.unipotentRadical_adelic_eq_rat_mul_boundedReal_mul_level E a (j : ℕ) _ hL
  obtain ⟨Ω', B, C, hΩ', hC, hvar⟩ := GlobalTheory.T.siegelCone_smooth_variation_along_bounded_unipotent E a t ht i j hij Ω hΩ R hR0
  refine ⟨Ω', B, C, hΩ', hC, fun r d hr hrt hd M hM hY c hc => ?_⟩
  refine GlobalTheory.T.cuspForm_norm_le_of_unipotent_variation E a ψ hψ (j : ℕ) (by omega) j.2 (infGL E a (d * c)) (C * (r j / r i) * M) fun x => ?_
  obtain ⟨ξ, z, k, hk, hz, hx⟩ := hcov x
  have hk' : finRep E a k ψ = ψ := hk
  have e : ψ.1 (unip x * infGL E a (d * c)) = ψ.1 (infGL E a (unip z * (d * c))) := by
    rw [hx, mul_assoc, mul_assoc, ← infGL_comm, ← mul_assoc (infGL E a (unip z)), ← map_mul, hψ.1.left]
    have := congrArg (fun φ : Sm E a => φ.1 (infGL E a (unip z * (d * c)))) hk'
    exact this
  rw [e]
  exact hvar ψ r d hr hrt hd M hM hY c hc z hz

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLSiegelConeDecayOneStepStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.cuspForm_GL_siegel_cone_decay_one_step : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ψ : Sm E a), IsCuspForm ψ → ∀ t : ℝ, 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ (Ω' : Set (GL (Fin a) (Cinf E))) (B : Finset (Lie E a)) (C : ℝ), IsCompact Ω' ∧ 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ M : ℝ, 0 ≤ M → (∀ Y ∈ B, ∀ c' ∈ Ω', ‖lieD Y ψ.1 (infGL E a (d * c'))‖ ≤ M) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * M := by
  first | exact @GlobalTheory.cuspForm_decay_step | exact GlobalTheory.cuspForm_decay_step | (intros; apply GlobalTheory.cuspForm_decay_step <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLIteratedDecayModerateGrowth

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.CuspRapid

theorem iterated_decay : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (m : ℕ) (ψ : Sm E a), IsCuspForm ψ → (∀ l : List (Lie E a), ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod ψ).1 (infGL E a y)‖ ≤ C * height y ^ N) → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N := by
  intro hfin E _ _ _ a N t ht i j hij m
  induction m with
  | zero =>
    intro ψ _ htame Ω hΩ
    obtain ⟨C0, hC0⟩ := htame []
    obtain ⟨B, hB1, hB⟩ := GlobalTheory.T.exists_height_mul_le_of_isCompact E a Ω hΩ
    refine ⟨|C0| * B ^ N, by positivity, ?_⟩
    intro r d _ _ _ c hc
    have h1 := hC0 (d * c)
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply] at h1
    have hh0 : 0 ≤ height (d * c) := le_trans zero_le_one (one_le_height _)
    have hh : height (d * c) ^ N ≤ (B * height d) ^ N := pow_le_pow_left₀ hh0 (hB c hc d) N
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ C0 * height (d * c) ^ N := h1
      _ ≤ |C0| * height (d * c) ^ N := mul_le_mul_of_nonneg_right (le_abs_self C0) (pow_nonneg hh0 N)
      _ ≤ |C0| * (B * height d) ^ N := mul_le_mul_of_nonneg_left hh (abs_nonneg C0)
      _ = |C0| * B ^ N * (r j / r i) ^ 0 * height d ^ N := by rw [mul_pow]; ring
  | succ m ih =>
    intro ψ hψ htame Ω hΩ
    obtain ⟨Ω', B, C, hΩ', hC, hstep⟩ := GlobalTheory.T.cuspForm_GL_siegel_cone_decay_one_step E a ψ hψ t ht i j hij Ω hΩ
    have hY : ∀ Y ∈ B, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) →
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) →
        ∀ c ∈ Ω', ‖(lie E a Y ψ).1 (infGL E a (d * c))‖ ≤ C' * (r j / r i) ^ m * height d ^ N := by
      intro Y _
      have hcusp : IsCuspForm (lie E a Y ψ) := GlobalTheory.T.isCuspForm_operator_act hfin E a (.lie Y) ψ hψ
      refine ih (lie E a Y ψ) hcusp ?_ Ω' hΩ'
      intro l
      obtain ⟨C1, hC1⟩ := htame (l ++ [Y])
      refine ⟨C1, fun y => ?_⟩
      have e : (l.map (lie E a)).prod (lie E a Y ψ) = ((l ++ [Y]).map (lie E a)).prod ψ := by
        simp [List.map_append, List.prod_append, Module.End.mul_apply]
      rw [e]
      exact hC1 y
    choose! CY hCY0 hCY using hY
    refine ⟨C * ∑ Y ∈ B, CY Y, mul_nonneg hC (Finset.sum_nonneg hCY0), ?_⟩
    intro r d hr hrt hd c hc
    have hq : 0 ≤ (r j / r i) ^ m * height d ^ N :=
      mul_nonneg (pow_nonneg (div_nonneg (hr j).le (hr i).le) m)
        (pow_nonneg (le_trans zero_le_one (one_le_height d)) N)
    have hM0 : 0 ≤ (∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N) :=
      mul_nonneg (Finset.sum_nonneg hCY0) hq
    have h := hstep r d hr hrt hd _ hM0 (fun Y hYB c' hc' => by
      have h2 : lieD Y ψ.1 = (lie E a Y ψ).1 := rfl
      rw [h2]
      calc ‖(lie E a Y ψ).1 (infGL E a (d * c'))‖ ≤ CY Y * (r j / r i) ^ m * height d ^ N := hCY Y hYB r d hr hrt hd c' hc'
        _ = CY Y * ((r j / r i) ^ m * height d ^ N) := by ring
        _ ≤ (∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N) :=
          mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun Y hY => hCY0 Y hY) hYB) hq) c hc
    calc ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) * ((∑ Y ∈ B, CY Y) * ((r j / r i) ^ m * height d ^ N)) := h
      _ = (C * ∑ Y ∈ B, CY Y) * (r j / r i) ^ (m + 1) * height d ^ N := by ring

end GlobalTheory.CuspRapid
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormGLIteratedDecayModerateGrowthStatement

section

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

theorem _root_.GlobalTheory.T.cuspForm_GL_iterated_decay_moderateGrowth : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : ℕ) (t : ℝ), 0 < t → ∀ i j : Fin a, (j : ℕ) = i + 1 → ∀ (m : ℕ) (ψ : Sm E a), IsCuspForm ψ → (∀ l : List (Lie E a), ∃ C : ℝ, ∀ y, ‖((l.map (lie E a)).prod ψ).1 (infGL E a y)‖ ≤ C * height y ^ N) → ∀ (Ω : Set (GL (Fin a) (Cinf E))), IsCompact Ω → ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : Fin a → ℝ) (d : GL (Fin a) (Cinf E)), (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → d.val = Matrix.diagonal (fun i => fun _ => (r i : ℂ)) → ∀ c ∈ Ω, ‖ψ.1 (infGL E a (d * c))‖ ≤ C * (r j / r i) ^ m * height d ^ N := by
  first | exact @GlobalTheory.CuspRapid.iterated_decay | exact GlobalTheory.CuspRapid.iterated_decay | (intros; apply GlobalTheory.CuspRapid.iterated_decay <;> assumption)
end
end
