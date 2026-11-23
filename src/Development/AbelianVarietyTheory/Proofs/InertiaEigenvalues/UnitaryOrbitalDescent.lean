module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MulMatMemUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitaryGroupTorusCutoff
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
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FourierDescendedFunctionEqPartialFourierStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HermitianBlockInvariantsIffIsometryStatement
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisInvKRegularIffIsUnitStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisOrbitalIntegrandIsLocallyConstantCoStatement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryGroupPositiveCharacterTrivialAndUnimodulaStatement
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PartialFourierPreservesTestFixesUnitStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitaryGroupTorusCutoffStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_unitary_group_torus_cutoff : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F), A.IsGen τ p → ∀ (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ Z : Set (Matrix (Fin r) (Fin r) E), IsCompact Z → ∃ α : Matrix.unitaryGroup (Fin r) E → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1 := by
  first | exact @GlobalTheory.JR.TorusCutOff.exists_unitary_cutoff | exact GlobalTheory.JR.TorusCutOff.exists_unitary_cutoff | (intros; apply GlobalTheory.JR.TorusCutOff.exists_unitary_cutoff <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportDescendedFunction

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem GlobalTheory.JR.descFn_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → IsTest (A.descFn M Ax j lam α f) := by
  intro F E _ _ _ _ _ A r M Ax j lam α hαl hαc f hf

  have hstar : Continuous (star : E → E) := by
    have : Isometry (starAddEquiv : E ≃+ E) :=
      (AddMonoidHomClass.isometry_iff_norm (starAddEquiv : E ≃+ E)).2 (fun x => Unram.norm_star F x)
    exact this.continuous
  haveI : ContinuousStar E := ⟨hstar⟩
  haveI : LocallyCompactSpace F := Unram.lcF E
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : IsTopologicalAddGroup A.L := IsModuleTopology.topologicalAddGroup F A.L
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ (Unram.finrank_eq (F := F) (E := E))
  have hj : Continuous j := IsModuleTopology.continuous_of_linearMap ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  have hjs : Continuous j.symm :=
    LinearMap.continuous_of_finiteDimensional ((j.symm : (Fin r → E) →ₗ[E] A.L).restrictScalars F)

  have hact : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E => (actU p.2 (Ax, j p.1, lam) : Hn r F E)) := by
    have hg : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E => (p.2 : Matrix (Fin r) (Fin r) E)) :=
      continuous_subtype_val.comp continuous_snd
    have c1 : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E =>
        (p.2 : Matrix (Fin r) (Fin r) E) * Ax.1 * star (p.2 : Matrix (Fin r) (Fin r) E)) :=
      (hg.mul continuous_const).mul hg.star
    have c2 : Continuous (fun p : A.L × Matrix.unitaryGroup (Fin r) E =>
        (p.2 : Matrix (Fin r) (Fin r) E) *ᵥ j p.1) :=
      Continuous.matrix_mulVec hg (hj.comp continuous_fst)
    exact Continuous.prodMk (Continuous.subtype_mk c1 _) (Continuous.prodMk c2 continuous_const)
  set Φ : A.L × Matrix.unitaryGroup (Fin r) E → ℂ := fun p => f (actU p.2 (Ax, j p.1, lam)) * (α p.2 : ℂ) with hΦ
  have hΦl : IsLocallyConstant Φ := by
    refine IsLocallyConstant.mul (hf.1.comp_continuous hact) ?_
    exact (hαl.comp_continuous continuous_snd).comp (fun x : ℝ => (x : ℂ))
  have hdesc : ∀ y, A.descFn M Ax j lam α f y = (letI := M.mU; ∫ g, Φ (y, g) ∂M.μU) := fun y => rfl
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y0
    have key : ∀ᶠ y in 𝓝 y0, ∀ g ∈ tsupport α, Φ (y, g) = Φ (y0, g) := by
      refine hαc.isCompact.eventually_forall_of_forall_eventually ?_
      intro g _
      have h1 := (IsLocallyConstant.iff_eventually_eq Φ).1 hΦl (y0, g)
      have h2 : ∀ᶠ z : A.L × Matrix.unitaryGroup (Fin r) E in 𝓝 (y0, g), Φ (y0, z.2) = Φ (y0, g) := by
        have h3 : Tendsto (fun z : A.L × Matrix.unitaryGroup (Fin r) E => ((y0, z.2) : A.L × _)) (𝓝 (y0, g)) (𝓝 (y0, g)) := by
          have : Continuous (fun z : A.L × Matrix.unitaryGroup (Fin r) E => ((y0, z.2) : A.L × _)) :=
            continuous_const.prodMk continuous_snd
          simpa using this.tendsto (y0, g)
        exact h3.eventually h1
      filter_upwards [h1, h2] with z hz1 hz2
      rw [hz1, hz2]
    filter_upwards [key] with y hy
    rw [hdesc, hdesc]
    congr 1
    funext g
    by_cases hg : g ∈ tsupport α
    · exact hy g hg
    · have : α g = 0 := image_eq_zero_of_notMem_tsupport hg
      simp [hΦ, this]
  · let S : Set (Fin r → E) := Prod.fst '' (Prod.snd '' tsupport f)
    let Kset : Set A.L := (fun p : Matrix.unitaryGroup (Fin r) E × (Fin r → E) => j.symm (star (p.1 : Matrix (Fin r) (Fin r) E) *ᵥ p.2)) '' (tsupport α ×ˢ S)
    have hS : IsCompact S :=
      (hf.2.isCompact.image continuous_snd).image continuous_fst
    have hK : IsCompact Kset := by
      refine (hαc.isCompact.prod hS).image ?_
      refine hjs.comp ?_
      exact Continuous.matrix_mulVec ((continuous_subtype_val.comp continuous_fst).star) continuous_snd
    have hKc : IsClosed Kset := by
      have h1 : IsClosed (j '' Kset) := (hK.image hj).isClosed
      have h2 : Kset = j ⁻¹' (j '' Kset) := (Set.preimage_image_eq _ j.injective).symm
      rw [h2]
      exact h1.preimage hj
    refine HasCompactSupport.intro' hK hKc ?_
    intro y hy
    by_contra hne
    rw [hdesc] at hne
    have : ∃ g, Φ (y, g) ≠ 0 := by
      by_contra hall
      push_neg at hall
      apply hne
      have : (fun g => Φ (y, g)) = fun _ => 0 := funext hall
      rw [this]
      simp
    obtain ⟨g, hg⟩ := this
    have hfg : f (actU g (Ax, j y, lam)) ≠ 0 := left_ne_zero_of_mul hg
    have hαg : (α g : ℂ) ≠ 0 := right_ne_zero_of_mul hg
    have hαg' : α g ≠ 0 := by exact_mod_cast hαg
    apply hy
    refine ⟨(g, g.1 *ᵥ j y), ⟨subset_tsupport _ hαg', ?_⟩, ?_⟩
    · exact ⟨(actU g (Ax, j y, lam)).2, ⟨actU g (Ax, j y, lam), subset_tsupport _ hfg, rfl⟩, rfl⟩
    · simp only [Matrix.mulVec_mulVec]
      have hu : star (g.1 : Matrix (Fin r) (Fin r) E) * g.1 = 1 := Matrix.UnitaryGroup.star_mul_self g
      rw [hu, Matrix.one_mulVec, LinearEquiv.symm_apply_apply]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocallyConstantCompactSupportDescendedFunctionStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.isLocallyConstantCompactSupport_descendedFunction : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)) (j : A.L ≃ₗ[E] (Fin r → E)) (lam : F) (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → HasCompactSupport α → ∀ f : Hn r F E → ℂ, IsTest f → IsTest (A.descFn M Ax j lam α f) := by
  first | exact @GlobalTheory.JR.descFn_isTest | exact GlobalTheory.JR.descFn_isTest | (intros; apply GlobalTheory.JR.descFn_isTest <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitalIntegralDescendedEqUnitary

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.DescOrb

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem mulMat_comm (A : Et F E) {r : ℕ} (τ : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (Ax : Matrix (Fin r) (Fin r) E)
    (hA : ∀ z, j (algebraMap A.K A.L τ * z) = Ax *ᵥ j z) (t : A.L) :
    Ax * A.mulMat j t = A.mulMat j t * Ax := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨z, rfl⟩ := j.surjective v
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Et.mulMat_mulVec_apply, ← hA]
  congr 1; ring

theorem actU_actU {r : ℕ} (g h : unitaryGroup (Fin r) E) (X : Hn r F E) :
    actU g (actU h X) = actU (g * h) X := by
  refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
  · show g.1 * (h.1 * X.1.1 * star h.1) * star g.1 = (g.1 * h.1) * X.1.1 * star (g.1 * h.1)
    rw [star_mul]; simp only [Matrix.mul_assoc]
  · show g.1 *ᵥ (h.1 *ᵥ X.2.1) = (g.1 * h.1) *ᵥ X.2.1
    rw [Matrix.mulVec_mulVec]

end GlobalTheory.JR.DescOrb

namespace GlobalTheory.JR.DescOrb

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem continuous_mulMat [hU : Unram F E] (A : Et F E) {r : ℕ} (j : A.L ≃ₗ[E] (Fin r → E)) :
    Continuous fun t : A.L => A.mulMat j t := by
  haveI := hU.lcF
  haveI := EtMeas.finite_L A
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have hj : Continuous (j : A.L → Fin r → E) :=
    IsModuleTopology.continuous_of_linearMap ((j : A.L →ₗ[E] (Fin r → E)).restrictScalars F)
  refine continuous_matrix fun i k => ?_
  simp only [Et.mulMat, LinearMap.toMatrix'_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    LinearEquiv.coe_coe]
  exact (continuous_apply i).comp (hj.comp (continuous_id.mul continuous_const))

theorem orbL_descFn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (τ : A.K) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (lam : F) (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → (∀ g, 0 ≤ α g) → ∀ Z : Set (Matrix (Fin r) (Fin r) E), (∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1) → ∀ f₀ : Hn r F E → ℂ, Continuous f₀ → (∀ X, f₀ X ≠ 0 → X.1.1 ∈ Z) → ∀ y : A.L, (letI := M.mU; Integrable (fun g => f₀ (actU g (Ax, j y, lam))) M.μU) → A.orbL ν (A.descFn M Ax j lam α f₀) y = orbU M f₀ (Ax, j y, lam) := by
  intro F E _ _ _ _ hU A r M τ x j hx Ax hA lam ν hν α hα hα0 Z hZ f₀ hf₀ hf₀Z y hint
  letI := M.mU
  haveI := M.bU
  haveI := M.haarU
  haveI := hU.ultraE; haveI := hU.lcE; haveI := hU.ultraF; haveI := hU.lcF
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun y => (hU.norm_star y).le⟩
  haveI : SecondCountableTopology (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (SecondCountableTopology (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) E) :=
    inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → E))
  haveI : LocallyCompactSpace (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).locallyCompactSpace
  haveI : SecondCountableTopology (unitaryGroup (Fin r) E) :=
    (isClosed_unitary (R := Matrix (Fin r) (Fin r) E)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI := EtMeas.finite_L A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  haveI : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  haveI : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  haveI : LocallyCompactSpace (unitary A.L) := (isClosed_unitary (R := A.L)).locallyCompactSpace
  haveI : SecondCountableTopology (unitary A.L) :=
    (isClosed_unitary (R := A.L)).isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : SigmaFinite ν := inferInstance
  haveI : SigmaFinite M.μU := inferInstance
  haveI : M.μU.IsMulRightInvariant := (GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular F E r).2 M
  have huc : Continuous (A.uHom hx) := continuous_induced_rng.2 ((continuous_mulMat A j).comp continuous_subtype_val)
  have hinvc : Continuous fun g : unitaryGroup (Fin r) E => g⁻¹ := continuous_inv

  set X : Hn r F E := (Ax, j y, lam) with hXdef
  have hcomm : ∀ t : unitary A.L, ((A.uHom hx t : Matrix (Fin r) (Fin r) E)) * Ax.1 = Ax.1 * A.uHom hx t := fun t =>
    (mulMat_comm A τ j Ax.1 hA t).symm
  have hshift : ∀ t : unitary A.L, ((Ax, j (t.1 * y), lam) : Hn r F E) = actU (A.uHom hx t) X := by
    intro t
    refine Prod.ext (Subtype.ext ?_) (Prod.ext ?_ rfl)
    · show Ax.1 = (A.uHom hx t : Matrix (Fin r) (Fin r) E) * Ax.1 * star (A.uHom hx t : Matrix (Fin r) (Fin r) E)
      rw [hcomm, Matrix.mul_assoc, Unitary.mul_star_self_of_mem (A.uHom hx t).2, Matrix.mul_one]
    · show j (t.1 * y) = (A.uHom hx t : Matrix (Fin r) (Fin r) E) *ᵥ j y
      rw [Et.uHom_apply, Et.mulMat_mulVec_apply]
  have step1 : ∀ t : unitary A.L, A.descFn M Ax j lam α f₀ (t.1 * y) =
      ∫ g, f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ) ∂M.μU := by
    intro t
    have h := integral_mul_right_eq_self (μ := M.μU)
      (fun g => f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) (A.uHom hx t)
    simp only [mul_inv_cancel_right] at h
    rw [← h]
    show (∫ g, f₀ (actU g ((Ax, j (t.1 * y), lam) : Hn r F E)) * (α g : ℂ) ∂M.μU) = _
    simp only [hshift t, actU_actU]
  have hact : Continuous fun g : unitaryGroup (Fin r) E => actU g X := by
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ continuous_const)
    · exact (((continuous_subtype_val.matrix_mul continuous_const).matrix_mul
        (continuous_subtype_val.star))).subtype_mk _
    · exact continuous_subtype_val.matrix_mulVec continuous_const
  have hcont : Continuous (Function.uncurry fun (t : unitary A.L) (g : unitaryGroup (Fin r) E) =>
      f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) :=
    (hf₀.comp (hact.comp continuous_snd)).mul (Complex.continuous_ofReal.comp
      (hα.continuous.comp (continuous_snd.mul (hinvc.comp (huc.comp continuous_fst)))))
  have hαint : ∀ g : unitaryGroup (Fin r) E, f₀ (actU g X) ≠ 0 →
      Integrable (fun t => α (g * (A.uHom hx t)⁻¹)) ν := by
    intro g hg
    by_contra hn
    have h1 := integral_undef hn
    rw [hZ g (hf₀Z _ hg)] at h1
    exact one_ne_zero h1
  have hInt : Integrable (Function.uncurry fun (t : unitary A.L) (g : unitaryGroup (Fin r) E) =>
      f₀ (actU g X) * (α (g * (A.uHom hx t)⁻¹) : ℂ)) (ν.prod M.μU) := by
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun g => ?_, ?_⟩
    · by_cases hg : f₀ (actU g X) = 0
      · simp [Function.uncurry, hg]
      · exact ((hαint g hg).ofReal).const_mul (f₀ (actU g X))
    · refine hint.norm.congr (Eventually.of_forall fun g => ?_)
      simp only [Function.uncurry_apply_pair, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [integral_const_mul]
      by_cases hg : f₀ (actU g X) = 0
      · simp [hg]
      · rw [integral_congr_ae (Eventually.of_forall fun t => abs_of_nonneg (hα0 _)), hZ g (hf₀Z _ hg), mul_one]
  show ∫ t : unitary A.L, A.descFn M Ax j lam α f₀ (t.1 * y) ∂ν = ∫ g, f₀ (actU g X) ∂M.μU
  simp_rw [step1]
  rw [integral_integral_swap hInt]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  rw [integral_const_mul, integral_complex_ofReal]
  by_cases hg : f₀ (actU g X) = 0
  · simp [hg]
  · rw [hZ g (hf₀Z _ hg)]; simp

end GlobalTheory.JR.DescOrb
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrbitalIntegralDescendedEqUnitaryStatement

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.orbitalIntegral_descended_eq_unitary : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (M : Meas r F E) (τ : A.K) (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) (hx : A.IsIsom x j) (Ax : selfAdjoint (Matrix (Fin r) (Fin r) E)), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ (lam : F) (ν : Measure (unitary A.L)), ν.IsHaarMeasure → ∀ (α : Matrix.unitaryGroup (Fin r) E → ℝ), IsLocallyConstant α → (∀ g, 0 ≤ α g) → ∀ Z : Set (Matrix (Fin r) (Fin r) E), (∀ g : Matrix.unitaryGroup (Fin r) E, g.1 * Ax.1 * star g.1 ∈ Z → ∫ t, α (g * (A.uHom hx t)⁻¹) ∂ν = 1) → ∀ f₀ : Hn r F E → ℂ, Continuous f₀ → (∀ X, f₀ X ≠ 0 → X.1.1 ∈ Z) → ∀ y : A.L, (letI := M.mU; Integrable (fun g => f₀ (actU g (Ax, j y, lam))) M.μU) → A.orbL ν (A.descFn M Ax j lam α f₀) y = orbU M f₀ (Ax, j y, lam) := by
  first | exact @GlobalTheory.JR.DescOrb.orbL_descFn | exact GlobalTheory.JR.DescOrb.orbL_descFn | (intros; apply GlobalTheory.JR.DescOrb.orbL_descFn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOrbitalDescent

section

@[expose] public section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem unitary_orbital_descent : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (r : ℕ) (M : Meas r F E) (τ : A.K) (p : Fin r → F) (lam : F), A.IsGen τ p → ∀ (x : A.Kˣ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → ∀ Ax : selfAdjoint (Matrix (Fin r) (Fin r) E), (∀ z, j (algebraMap A.K A.L τ * z) = Ax.1 *ᵥ j z) → ∀ f : Hn r F E → ℂ, IsTest f → ∃ φ : A.L → ℂ, IsTest φ ∧ ∀ y : A.L, IsUnit y → orbU M f (Ax, j y, lam) = A.orbL m.ν φ y ∧ orbU M (fourU M ψ f) (Ax, j y, lam) = A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) φ) y := by
  intro F E _ _ _ _ _ A ψ hψ m r M τ p lam hgen x j hx Ax hAx f hf
  have hν : m.ν.IsHaarMeasure := m.nat.1
  set Z : Set (Matrix (Fin r) (Fin r) E) := (fun X : Hn r F E => X.1.1) '' tsupport f with hZdef
  have hZ : IsCompact Z := hf.2.image (continuous_subtype_val.comp continuous_fst)
  obtain ⟨α, hαlc, hαcs, hα0, hα1⟩ := GlobalTheory.T.exists_unitary_group_torus_cutoff F E A r τ p hgen (x : A.K) j hx Ax hAx m.ν hν Z hZ
  have hsuppf : ∀ X, f X ≠ 0 → X.1.1 ∈ Z := fun X hX => ⟨X, subset_tsupport f hX, rfl⟩
  have hsuppF : ∀ X, fourU M ψ f X ≠ 0 → X.1.1 ∈ Z := by
    intro X hX
    by_contra hZ'
    apply hX
    have h0 : ∀ c, f (X.1, c, X.2.2) = 0 := fun c => by
      by_contra hc
      exact hZ' (hsuppf (X.1, c, X.2.2) hc)
    simp [fourU, h0]
  have hFtest : IsTest (fourU M ψ f) := (GlobalTheory.T.partialFourier_preserves_test_fixes_unit F E r M ψ hψ).2.1 f hf
  have hint : ∀ f₀ : Hn r F E → ℂ, IsTest f₀ → ∀ y : A.L, IsUnit y →
      (letI := M.mU; Integrable (fun g => f₀ (actU g (Ax, j y, lam))) M.μU) := by
    intro f₀ hf₀ y hy
    letI := M.mU
    haveI := M.bU
    haveI := M.haarU
    have ha : IsUnit ((x : A.K) * A.NL y) := x.isUnit.mul (hy.map (Algebra.norm A.K))
    have hD := ((GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ p lam hgen).2 ((x : A.K) * A.NL y)).2.mpr ha
    obtain ⟨Ax', hAx', hinv⟩ := (GlobalTheory.T.hermitianBlock_invariants_iff_isometry F E A r τ p lam hgen).2 x j hx
    have hAA : Ax' = Ax := by
      apply Subtype.ext
      apply Matrix.toLin'.injective
      apply LinearMap.ext
      intro v
      obtain ⟨z, rfl⟩ := j.surjective v
      simp only [Matrix.toLin'_apply, ← hAx', ← hAx]
    subst hAA
    have ht := (GlobalTheory.T.jacquetRallis_orbitalIntegrand_isLocallyConstantCompactSupport F E r M).2 f₀ hf₀ _ _ hD (hinv y)
    exact ht.1.continuous.integrable_of_hasCompactSupport ht.2
  refine ⟨A.descFn M Ax j lam α f, GlobalTheory.T.isLocallyConstantCompactSupport_descendedFunction F E A r M Ax j lam α hαlc hαcs f hf, fun y hy => ⟨?_, ?_⟩⟩
  · exact (GlobalTheory.T.orbitalIntegral_descended_eq_unitary F E A r M τ x j hx Ax hAx lam m.ν hν α hαlc hα0 Z hα1 f hf.1.continuous hsuppf y
      (hint f hf y hy)).symm
  · rw [GlobalTheory.T.fourier_descendedFunction_eq_partialFourier F E A ψ hψ r M x j hx (m.μL x) (m.sdL x) Ax lam α hαlc hαcs f hf]
    exact (GlobalTheory.T.orbitalIntegral_descended_eq_unitary F E A r M τ x j hx Ax hAx lam m.ν hν α hαlc hα0 Z hα1 _ hFtest.1.continuous hsuppF y
      (hint _ hFtest y hy)).symm

end GlobalTheory.JR
end
end
