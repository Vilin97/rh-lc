module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisInvariantHaarFamilyAdelicUnitaryStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoboundaryOfInvariantUnitaryStepConstants
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNontrivialAdeleCharTrivialOnTotallyRealStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueOneVectorStepHaarMeasureStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueStdHermitianFibreProductOfRankGeThreStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuadricFibreMeasureEqSmulNormalisedProductStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupPointsEquivOfChangeOfBasisStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOneVectorStepCompatibleChangeOfBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerAnisotropicVectorEquivComplemenStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerMeasureIndependentOfPath
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoboundaryOfInvariantUnitaryStepConstantsStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.exists_coboundary_of_invariant_unitary_step_constants : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (Γ : Type) [CommGroup Γ] (c : ∀ M : ℕ, Matrix (Fin (M + 1)) (Fin (M + 1)) E → (Fin 1 → Fin (M + 1) → E) → Matrix (Fin (M + 1)) (Fin M) E → Γ), (∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (P : GL (Fin (M + 1)) E) (Q : GL (Fin M) E), 2 ≤ M → StepData σ J x a B J' → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E).mulVec (x₂ 0) = x 0 → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * B₂ = B * (Q : Matrix (Fin M) (Fin M) E) → c M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E)) x₂ B₂ = c M J x B) → (∀ (M : ℕ) (J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E) (x₁ x₂ : Fin 1 → Fin (M + 1 + 1) → E) (a₁ a₂ : F) (B₁ B₂ : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E) (J₁ J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (y₁ y₂ : Fin 1 → Fin (M + 1) → E) (b₁ b₂ : F) (C₁ C₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₀ : Matrix (Fin M) (Fin M) E), 2 ≤ M → StepData σ J x₁ a₁ B₁ J₁ → StepData σ J₁ y₁ b₁ C₁ J₀ → StepData σ J x₂ a₂ B₂ J₂ → StepData σ J₂ y₂ b₂ C₂ J₀ → B₁ * C₁ = B₂ * C₂ → c (M + 1) J x₁ B₁ * c M J₁ y₁ C₁ = c (M + 1) J x₂ B₂ * c M J₂ y₂ C₂) → ∃ α : ∀ M : ℕ, Matrix (Fin M) (Fin M) E → Γ, (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J → α M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E)) = α M J) ∧ ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M → StepData σ J x a B J' → α (M + 1) J = c M J x B * α M J' := by
  first | exact @GlobalTheory.GaugeAlg.exists_coboundary | exact GlobalTheory.GaugeAlg.exists_coboundary | (intros; apply GlobalTheory.GaugeAlg.exists_coboundary <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyStandardLocalHaarMeasures

section

@[expose] public section

noncomputable section

namespace GlobalTheory.GaugeEx.StdExist

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

def coordHomeo {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] :
    (R ⊗[F] E) ≃ₜ (Fin d → R) where
  toEquiv := (Algebra.TensorProduct.basis R b).equivFun.toEquiv
  continuous_toFun := by
    haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
    exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
  continuous_invFun := by
    haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
    exact IsModuleTopology.continuous_of_linearMap
      (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem isCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
  haveI := GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v
  exact isCompact_iff_compactSpace.2 this

theorem isOpen_integers (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) :=
  Valued.isOpen_valuationSubring _

theorem intV_eq {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    intV b v = coordHomeo b (Fv F v) ⁻¹'
      (Set.univ.pi fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
  ext y
  simp only [intV, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
  rfl

theorem isCompact_intV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (intV b v) := by
  rw [intV_eq, Homeomorph.isCompact_preimage]
  exact isCompact_univ_pi fun _ => isCompact_integers v

theorem isOpen_intV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (intV b v) := by
  rw [intV_eq]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integers v).preimage
    (coordHomeo b (Fv F v)).continuous

def intK (v : HeightOneSpectrum (𝓞 F)) : TopologicalSpace.PositiveCompacts (Fv F v) where
  carrier := v.adicCompletionIntegers F
  isCompact' := isCompact_integers v
  interior_nonempty' := by
    rw [(isOpen_integers v).interior_eq]
    exact ⟨0, zero_mem _⟩

def intVK {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) :
    TopologicalSpace.PositiveCompacts (Fv F v ⊗[F] E) where
  carrier := intV b v
  isCompact' := isCompact_intV b v
  interior_nonempty' := by
    rw [(isOpen_intV b v).interior_eq]
    exact ⟨0, fun k => by simp⟩

theorem nonempty_stdMeas (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (d : ℕ) (b : Module.Basis (Fin d) F E) : Nonempty (StdMeas b) := by
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  exact ⟨{
    lamI := Measure.addHaar
    lamV := fun v => Measure.addHaarMeasure (intVK b v)
    nuI := Measure.addHaar
    nuV := fun v => Measure.addHaarMeasure (intK v)
    haar_lamI := inferInstance
    haar_lamV := fun v => inferInstance
    haar_nuI := inferInstance
    haar_nuV := fun v => inferInstance
    lamV_int := fun v => Measure.addHaarMeasure_self (K₀ := intVK b v)
    nuV_int := fun v => Measure.addHaarMeasure_self (K₀ := intK v) }⟩

end GlobalTheory.GaugeEx.StdExist
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyStandardLocalHaarMeasuresStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.nonempty_standardLocalHaarMeasures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), Nonempty (StdMeas b) := by
  first | exact @GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas | exact GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas | (intros; apply GlobalTheory.GaugeEx.StdExist.nonempty_stdMeas <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOneVectorStepCompatibleChangeOfBasisStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.unitaryOneVectorStep_compatible_changeOfBasis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E) (x₂ : Fin 1 → Fin (M + 1) → E) (B₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₂' : Matrix (Fin M) (Fin M) E) (P : GL (Fin (M + 1)) E) (Q : GL (Fin M) E) (eP : HA (AF F) σ J ≃* HA (AF F) σ J₂) (eQ : HA (AF F) σ J' ≃* HA (AF F) σ J₂') (μ : Measure (HA (AF F) σ J)) (μ' : Measure (HA (AF F) σ J')), StepData σ J x a B J' → J₂ = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) → J₂' = Formalism.UG.cT (σ : E →+* E) (Q : Matrix (Fin M) (Fin M) E) * J' * (Q : Matrix (Fin M) (Fin M) E) → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E).mulVec (x₂ 0) = x 0 → (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) * B₂ = B * (Q : Matrix (Fin M) (Fin M) E) → (∀ g, FrameRel J J₂ (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) g (eP g)) → (∀ g, FrameRel J' J₂' (Q : Matrix (Fin M) (Fin M) E) g (eQ g)) → StepRel s σ J x a B J' μ μ' → StepData σ J₂ x₂ a B₂ J₂' ∧ StepRel s σ J₂ x₂ a B₂ J₂' (μ.map eP) (μ'.map eQ) := by
  first | exact @GlobalTheory.GaugeEx.stepRel_basis | exact GlobalTheory.GaugeEx.stepRel_basis | (intros; apply GlobalTheory.GaugeEx.stepRel_basis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryStabilizerMeasureIndependentOfPathStatement

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

theorem _root_.GlobalTheory.T.unitaryStabilizer_measure_independent_of_path : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (s : StdMeas b) (M : ℕ) (J : Matrix (Fin (M + 1 + 1)) (Fin (M + 1 + 1)) E) (x₁ x₂ : Fin 1 → Fin (M + 1 + 1) → E) (a₁ a₂ : F) (B₁ B₂ : Matrix (Fin (M + 1 + 1)) (Fin (M + 1)) E) (J₁ J₂ : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (y₁ y₂ : Fin 1 → Fin (M + 1) → E) (b₁ b₂ : F) (C₁ C₂ : Matrix (Fin (M + 1)) (Fin M) E) (J₀ : Matrix (Fin M) (Fin M) E) (μ₀ : Measure (HA (AF F) σ J₀)) (μ₁ : Measure (HA (AF F) σ J₁)) (μ₂ : Measure (HA (AF F) σ J₂)) (τ₁ τ₂ : Measure (HA (AF F) σ J)), 2 ≤ M → StepData σ J x₁ a₁ B₁ J₁ → StepData σ J₁ y₁ b₁ C₁ J₀ → StepData σ J x₂ a₂ B₂ J₂ → StepData σ J₂ y₂ b₂ C₂ J₀ → B₁ * C₁ = B₂ * C₂ → μ₀.IsHaarMeasure → StepRel s σ J₁ y₁ b₁ C₁ J₀ μ₁ μ₀ → StepRel s σ J x₁ a₁ B₁ J₁ τ₁ μ₁ → StepRel s σ J₂ y₂ b₂ C₂ J₀ μ₂ μ₀ → StepRel s σ J x₂ a₂ B₂ J₂ τ₂ μ₂ → τ₁ = τ₂ := by
  first | exact @GlobalTheory.GaugeSquare.square | exact GlobalTheory.GaugeSquare.square | (intros; apply GlobalTheory.GaugeSquare.square <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsGaugeOfIsCMExt

section

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

section Scale

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isCompatible_smul {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {x : Fin 1 → Fin M → E}
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (Hstab (AF F) σ J x)}
    {ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)} (h : IsCompatible F E σ M J x μ μ' ν) (c k : ℝ≥0) :
    IsCompatible F E σ M J x ((k * c) • μ) (c • μ') (k • ν) := by
  intro f hf sec hsec
  simp only [lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
  rw [h f hf sec hsec]
  simp only [lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  push_cast
  ring

theorem StepRel.smul [NumberField E] (hσ : IsCMExt F E σ) {d : ℕ} {b : Module.Basis (Fin d) F E} {s : StdMeas b} {M : ℕ}
    {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E} {β : F}
    {B : Matrix (Fin (M + 1)) (Fin M) E} {J' : Matrix (Fin M) (Fin M) E}
    {μ : Measure (HA (AF F) σ J)} {μ' : Measure (HA (AF F) σ J')}
    (hS : StepData σ J x β B J') (h : StepRel s σ J x β B J' μ μ') (c : ℝ≥0) : StepRel s σ J x β B J' (c • μ) (c • μ') := by
  intro ν hν e he
  have hc := isCompatible_smul (h ν hν e he) c 1
  have hm := ((GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ (AF F) M J x β B J' hS).2.2 e he).2.measurable
  simpa only [one_mul, one_smul, Measure.map_smul c hm.aemeasurable] using hc

end Scale

theorem smul_haar_inj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] (μ : Measure G) [μ.IsHaarMeasure] {c c' : ℝ≥0}
    (h : c • μ = c' • μ) : c = c' := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  have hpos : μ K ≠ 0 :=
    (μ.measure_pos_of_nonempty_interior ⟨1, mem_interior_iff_mem_nhds.2 hK1⟩).ne'
  have htop : μ K ≠ ⊤ := hK.measure_lt_top.ne
  have h2 := congrArg (fun m : Measure G => m K) h
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj hpos htop).1 h2)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

theorem stepData_unique {M : ℕ} {J : Matrix (Fin (M + 1)) (Fin (M + 1)) E} {x : Fin 1 → Fin (M + 1) → E}
    {a a' : F} {B : Matrix (Fin (M + 1)) (Fin M) E} {J' J'' : Matrix (Fin M) (Fin M) E}
    (h : StepData σ J x a B J') (h' : StepData σ J x a' B J'') : a = a' ∧ J' = J'' := by
  obtain ⟨-, -, h1, -, h2, -⟩ := h
  obtain ⟨-, -, h1', -, h2', -⟩ := h'
  exact ⟨(algebraMap F E).injective (h1.symm.trans h1'), h2.trans h2'.symm⟩

theorem exists_const (hσ : IsCMExt F E σ) {d : ℕ} {b : Module.Basis (Fin d) F E} (s : StdMeas b)
    (G : GaugeFam F E σ) (hG : G.IsHaar) :
    ∃ c : ∀ M : ℕ, Matrix (Fin (M + 1)) (Fin (M + 1)) E → (Fin 1 → Fin (M + 1) → E) →
      Matrix (Fin (M + 1)) (Fin M) E → ℝ≥0ˣ,
      ∀ M J x a B J', 2 ≤ M → StepData σ J x a B J' →
        StepRel s σ J x a B J' ((c M J x B : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have key : ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E)
      (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E),
      2 ≤ M → StepData σ J x a B J' →
      ∃ u : ℝ≥0ˣ, StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
    intro M J x a B J' hM hS
    haveI : (G.μ M J').IsHaarMeasure := hG M J' hS.2.2.2.2.2
    haveI : (G.μ (M + 1) J).IsHaarMeasure := hG (M + 1) J hS.1
    obtain ⟨⟨μ, hμ, hrel⟩, -⟩ :=
      GlobalTheory.T.exists_unique_oneVectorStep_haarMeasure F E σ hσ d b s M J x a B J' (G.μ M J') hM hS inferInstance
    haveI := hμ
    refine ⟨Units.mk0 (Measure.haarScalarFactor μ (G.μ (M + 1) J))
      (Measure.haarScalarFactor_pos_of_isHaarMeasure _ _).ne', ?_⟩
    rw [Units.val_mk0, ← Measure.isMulLeftInvariant_eq_smul]
    exact hrel
  refine ⟨fun M J x B => if h : ∃ u : ℝ≥0ˣ, ∃ (a : F) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M ∧
      StepData σ J x a B J' ∧ StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J')
    then h.choose else 1, ?_⟩
  intro M J x a B J' hM hS
  have hex : ∃ u : ℝ≥0ˣ, ∃ (a : F) (J' : Matrix (Fin M) (Fin M) E), 2 ≤ M ∧
      StepData σ J x a B J' ∧ StepRel s σ J x a B J' ((u : ℝ≥0) • G.μ (M + 1) J) (G.μ M J') := by
    obtain ⟨u, hu⟩ := key M J x a B J' hM hS
    exact ⟨u, a, J', hM, hS, hu⟩
  simp only [dif_pos hex]
  obtain ⟨a₀, J₀, -, hS₀, hR₀⟩ := hex.choose_spec
  obtain ⟨rfl, rfl⟩ := stepData_unique hS₀ hS
  exact hR₀

theorem exists_std_family (hσ : IsCMExt F E σ) {d : ℕ} {b : Module.Basis (Fin d) F E} (s : StdMeas b) :
    ∃ (G : GaugeFam F E σ) (α : ∀ M : ℕ, Matrix (Fin M) (Fin M) E → ℝ≥0ˣ), G.IsHaar ∧ G.BasisInv ∧
      (∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (P : GL (Fin M) E), IsHermND σ J →
        α M (Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin M) (Fin M) E) * J * (P : Matrix (Fin M) (Fin M) E)) =
          α M J) ∧
      ∀ M J x a B J', 2 ≤ M → StepData σ J x a B J' →
        StepRel s σ J x a B J' ((α (M + 1) J : ℝ≥0) • G.μ (M + 1) J) ((α M J' : ℝ≥0) • G.μ M J') := by
  classical
  obtain ⟨G, hH, hB⟩ := GlobalTheory.T.exists_basisInvariant_haar_family_adelicUnitary F E σ hσ
  obtain ⟨c, hc⟩ := exists_const hσ s G hH
  refine (GlobalTheory.T.exists_coboundary_of_invariant_unitary_step_constants F E σ hσ ℝ≥0ˣ c ?inv ?coc).elim fun α hα => ?main
  case main =>
    obtain ⟨hαinv, hαstep⟩ := hα
    refine ⟨G, α, hH, hB, hαinv, ?_⟩
    intro M J x a B J' hM hS
    have r := (hc M J x a B J' hM hS).smul hσ hS (α M J' : ℝ≥0)
    rw [smul_smul] at r
    rw [hαstep M J x a B J' hM hS, Units.val_mul, mul_comm]
    exact r
  case inv =>
    intro M J x a B J' x₂ B₂ P Q hM hS hx hPB
    obtain ⟨J₂, hJ₂⟩ : ∃ J₂, J₂ = Formalism.UG.cT (σ : E →+* E) (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) *
        J * (P : Matrix (Fin (M + 1)) (Fin (M + 1)) E) := ⟨_, rfl⟩
    obtain ⟨J₂', hJ₂'⟩ : ∃ J₂', J₂' = Formalism.UG.cT (σ : E →+* E) (Q : Matrix (Fin M) (Fin M) E) *
        J' * (Q : Matrix (Fin M) (Fin M) E) := ⟨_, rfl⟩
    rw [← hJ₂]
    obtain ⟨⟨eP, heP⟩, hmapP⟩ := hB (M + 1) J J₂ P hS.1 hJ₂
    obtain ⟨⟨eQ, heQ⟩, hmapQ⟩ := hB M J' J₂' Q hS.2.2.2.2.2 hJ₂'
    obtain ⟨hS₂, hR₂⟩ := GlobalTheory.T.unitaryOneVectorStep_compatible_changeOfBasis F E σ hσ _ b s M J J₂ x a B J' x₂ B₂ J₂' P Q eP eQ _ _ hS hJ₂
      hJ₂' hx hPB heP heQ (hc M J x a B J' hM hS)
    have hmP := ((GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) (M + 1) J J₂ P hJ₂).2 eP heP).1.measurable
    rw [Measure.map_smul _ hmP.aemeasurable, hmapP eP heP, hmapQ eQ heQ] at hR₂
    have hR₃ := hc M J₂ x₂ a B₂ J₂' hM hS₂
    have hHaar₂ : (G.μ M J₂').IsHaarMeasure := hH M J₂' hS₂.2.2.2.2.2
    have huniq := (GlobalTheory.T.exists_unique_oneVectorStep_haarMeasure F E σ hσ _ b s M J₂ x₂ a B₂ J₂' (G.μ M J₂') hM hS₂ hHaar₂).2 _ _
      hR₃ hR₂
    haveI : (G.μ (M + 1) J₂).IsHaarMeasure := hH (M + 1) J₂ hS₂.1
    exact Units.ext (smul_haar_inj _ huniq)
  case coc =>
    intro M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀ hM h1 h1' h2 h2' hBC
    haveI : (G.μ M J₀).IsHaarMeasure := hH M J₀ h1'.2.2.2.2.2
    haveI : (G.μ (M + 1 + 1) J).IsHaarMeasure := hH _ J h1.1
    have r1 := (hc (M + 1) J x₁ a₁ B₁ J₁ (by omega) h1).smul hσ h1 (c M J₁ y₁ C₁ : ℝ≥0)
    have r2 := (hc (M + 1) J x₂ a₂ B₂ J₂ (by omega) h2).smul hσ h2 (c M J₂ y₂ C₂ : ℝ≥0)
    have heq := GlobalTheory.T.unitaryStabilizer_measure_independent_of_path F E σ hσ _ b s M J x₁ x₂ a₁ a₂ B₁ B₂ J₁ J₂ y₁ y₂ b₁ b₂ C₁ C₂ J₀
      (G.μ M J₀) _ _ _ _ hM h1 h1' h2 h2' hBC inferInstance (hc M J₁ y₁ b₁ C₁ J₀ hM h1') r1
      (hc M J₂ y₂ b₂ C₂ J₀ hM h2') r2
    rw [smul_smul, smul_smul] at heq
    have he := smul_haar_inj _ heq
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, mul_comm, he, mul_comm]

theorem exists_isGauge_of_isCMExt (hσ : IsCMExt F E σ) : ∃ G : GaugeFam F E σ, G.IsGauge := by
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  haveI : IsTotallyReal F := hσ.1
  obtain ⟨s⟩ := GlobalTheory.T.nonempty_standardLocalHaarMeasures F E _ (Module.finBasis F E)
  obtain ⟨G, α, hH, hB, hαinv, hstep⟩ := exists_std_family hσ s
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.quadricFibreMeasure_eq_smul_normalisedProduct F E σ hσ _ _ s
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.exists_nontrivial_adeleChar_trivial_on_totallyReal F
  obtain ⟨K, hK⟩ : ∃ K : ℕ → ℝ≥0, K = fun M => ∏ i ∈ Finset.range (M + 1), κ i := ⟨_, rfl⟩
  have hK0 : ∀ M, K M ≠ 0 := fun M => by
    rw [hK]; exact Finset.prod_ne_zero_iff.2 fun i _ => hκ0 i
  have hKs : ∀ M, K (M + 1) = κ (M + 1) * K M := fun M => by
    rw [hK]; simp only [Finset.prod_range_succ (n := M + 1)]; ring
  refine ⟨⟨fun M J => (K M * α M J : ℝ≥0) • G.μ M J⟩, ?_, ?_, ?_⟩
  · intro M J hJ
    haveI : (G.μ M J).IsHaarMeasure := hH M J hJ
    exact Measure.IsHaarMeasure.nnreal_smul _ (mul_ne_zero (hK0 M) (α M J).ne_zero)
  · intro M J J' P hJ hJ'
    obtain ⟨⟨e, he⟩, hmap⟩ := hB M J J' P hJ hJ'
    refine ⟨⟨e, he⟩, fun e' he' => ?_⟩
    show ((K M * α M J : ℝ≥0) • G.μ M J).map e' = (K M * α M J' : ℝ≥0) • G.μ M J'
    have hm := ((GlobalTheory.T.unitary_group_points_equiv_of_change_of_basis F E σ (AF F) M J J' P hJ').2 e' he').1.measurable
    rw [Measure.map_smul _ hm.aemeasurable, hmap e' he', hJ', hαinv M J P hJ]
  · intro M J J' x β B hM hJ hβ hx hB' hJ'' hJ'
    have hS : StepData σ J x β B J' := ⟨hJ, hβ, hx, hB', hJ'', hJ'⟩
    obtain ⟨ν, hν, -⟩ := GlobalTheory.T.existsUnique_stdHermitianFibreProduct_of_rank_ge_three F E σ hσ _ _ s (M + 1) J β hM hJ hβ
    obtain ⟨e, he, -⟩ := (GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ (AF F) M J x β B J' hS).2.1
    refine ⟨⟨ψ, hψ⟩, fun ψ' hψ' => ?_⟩
    have hX := hκ (M + 1) J β ψ' ν (by omega) hJ hβ hψ' hν
    refine ⟨⟨_, (hX _).2 rfl⟩, fun νX hνX => ?_⟩
    rw [(hX νX).1 hνX]
    refine ⟨⟨e, he⟩, fun e' he' => ?_⟩
    have hc := isCompatible_smul (hstep M J x β B J' (by omega) hS ν hν e' he') (K M) (κ (M + 1))
    convert hc using 1
    · show ((K (M + 1) * α (M + 1) J : ℝ≥0) • G.μ (M + 1) J) = _
      rw [smul_smul, hKs, mul_assoc]
    · show ((K M * α M J' : ℝ≥0) • G.μ M J').map e'.symm = _
      have hm := ((GlobalTheory.T.unitary_stabilizer_anisotropic_vector_equiv_complement F E σ hσ (AF F) M J x β B J' hS).2.2 e' he').2.measurable
      simp only [Measure.map_smul _ hm.aemeasurable, smul_smul]

end GlobalTheory.GaugeEx


open Formalism.BasicNotions Formalism.MainNotions.G in
theorem GlobalTheory.GaugeEx.exists_isGauge : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E), ∃ G : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.GaugeFam F E cm.sig, G.IsGauge := by
  intro F E _ _ _ _ _ _ cm
  have hσ : IsCMExt F E cm.sig :=
    ⟨cm.totReal, cm.cmUnram.1, cm.deg2, fun τ x => cm.cmUnram.2.1 τ x⟩
  exact exists_isGauge_of_isCMExt hσ
end
end
