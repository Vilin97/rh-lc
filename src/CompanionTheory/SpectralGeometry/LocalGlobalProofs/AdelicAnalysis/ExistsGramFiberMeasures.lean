module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityFormulaStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentitiesStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarModularCharacterOfContinuousActionStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOrbitLocalSectionSubgroupStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityExistsStatement
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureDisintegrationFormula

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GramNear

theorem fibre_on_orbit (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [IsTopologicalAddGroup V]
    [AddCommGroup X] [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] [IsTopologicalAddGroup X]
    (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v))
    (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q]
    [SecondCountableTopology Q] [T2Space Q] [DistribMulAction Q V] [ContinuousSMul Q V]
    [DistribMulAction Q X] [ContinuousSMul Q X]
    (heq : ∀ (q : Q) (v : V), g (q • v) = q • g v) (b₀ : X)
    (ho : IsOpenEmbedding (fun q : Q => q • b₀)) :
    ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' (Set.range fun q : Q => q • b₀)) ν
      (Set.range fun q : Q => q • b₀) fib := by
  obtain ⟨χ, hχ, hμ⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action V μ Q
  obtain ⟨χ', hχ', hν⟩ := GlobalTheory.T.haar_modular_character_of_continuous_action X ν Q
  exact GlobalTheory.T.exists_fibre_family_on_open_orbit V X Y μ ν f g ι hι hg hf Q heq χ χ' hχ hχ' hμ hν b₀ ho

theorem exists_fibre_near : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ S : HermR R σ n, IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ B : Set (HermR R σ n), IsOpen B ∧ S ∈ B ∧ (∀ S' ∈ B, IsUnit (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (gramR R σ J ⁻¹' (Subtype.val '' B)) ν B fib := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hR n μ ν hμ hν S hS
  have hR' := hR
  obtain ⟨_, _, _, _, -, -, -, -⟩ := hR'
  obtain ⟨_, _, _, _, hsig, -, -, hbor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ R
  have hbor' := hbor n M
  obtain ⟨_, _, _, _, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hσ R n
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  obtain ⟨hgram, hmul, hone, hherm, -⟩ := GlobalTheory.T.gram_right_action_identities F E σ hσ M J hJ R n
  obtain ⟨Q, o, _, _, hoe, ho⟩ := GlobalTheory.T.hermitian_orbit_local_section_subgroup F E σ hσ R hR n S hS

  let c : Q → Matrix (Fin n) (Fin n) (R ⊗[F] E) := fun q => (((q⁻¹ : Q) : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
  have hc1 : c 1 = 1 := by simp [c]
  have hcm : ∀ a b : Q, c (a * b) = c b * c a := by
    intro a b
    simp only [c, mul_inv_rev]
    rfl
  have hcc : Continuous c := Units.continuous_val.comp (continuous_subtype_val.comp continuous_inv)
  letI actV : DistribMulAction Q (Fin n → Fin M → R ⊗[F] E) :=
    { smul := fun q X => rmul R X (c q)
      one_smul := fun X => by
        change rmul R X (c 1) = X
        rw [hc1, hone]
      mul_smul := fun a b X => by
        change rmul R X (c (a * b)) = rmul R (rmul R X (c b)) (c a)
        rw [hcm, hmul]
      smul_zero := fun q => by
        change rmul R 0 (c q) = 0
        funext a i; simp [rmul]
      smul_add := fun q X Y => by
        change rmul R (X + Y) (c q) = rmul R X (c q) + rmul R Y (c q)
        funext a i; simp [rmul, add_mul, Finset.sum_add_distrib] }
  have hsmulV : ∀ (q : Q) (X : Fin n → Fin M → R ⊗[F] E), q • X = rmul R X (c q) := fun _ _ => rfl
  letI actH : DistribMulAction Q (HermR R σ n) :=
    { smul := fun q T => ⟨cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q, hherm T (c q)⟩
      one_smul := fun T => by
        apply Subtype.ext
        change cT (sigR R σ) (c 1) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c 1 = T
        rw [hc1]; simp [cT]
      mul_smul := fun a b T => by
        apply Subtype.ext
        change cT (sigR R σ) (c (a * b)) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c (a * b) =
          cT (sigR R σ) (c a) * (cT (sigR R σ) (c b) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c b) * c a
        rw [hcm]
        simp only [cT, Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      smul_zero := fun q => by
        apply Subtype.ext
        change cT (sigR R σ) (c q) * (0 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q = 0
        simp
      smul_add := fun q T T' => by
        apply Subtype.ext
        change cT (sigR R σ) (c q) * ((T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) + T') * c q =
          cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q +
            cT (sigR R σ) (c q) * (T' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q
        rw [Matrix.mul_add, Matrix.add_mul] }
  have hsmulH : ∀ (q : Q) (T : HermR R σ n), ((q • T : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
      cT (sigR R σ) (c q) * (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c q := fun _ _ => rfl
  have hcontV : ContinuousSMul Q (Fin n → Fin M → R ⊗[F] E) := by
    refine ⟨?_⟩
    change Continuous fun p : Q × (Fin n → Fin M → R ⊗[F] E) => rmul R p.2 (c p.1)
    refine continuous_pi fun a => continuous_pi fun i => ?_
    simp only [rmul]
    refine continuous_finsetSum _ fun b _ => Continuous.mul ?_ ?_
    · exact (continuous_apply i).comp ((continuous_apply b).comp continuous_snd)
    · exact (hcc.comp continuous_fst).matrix_elem b a
  have hcontH : ContinuousSMul Q (HermR R σ n) := by
    refine ⟨?_⟩
    refine Continuous.subtype_mk (f := fun p : Q × HermR R σ n => cT (sigR R σ) (c p.1) * (p.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * c p.1) ?_ _
    have h1 : Continuous fun p : Q × HermR R σ n => c p.1 := hcc.comp continuous_fst
    have h2 : Continuous fun p : Q × HermR R σ n => cT (sigR R σ) (c p.1) :=
      (h1.matrix_map hsig).matrix_transpose
    exact (h2.matrix_mul (continuous_subtype_val.comp continuous_snd)).matrix_mul h1
  have heq : ∀ (q : Q) (X : Fin n → Fin M → R ⊗[F] E), g (q • X) = q • g X := by
    intro q X
    apply Subtype.ext
    rw [hsmulV, hsmulH, ← hgf, ← hgf, hgram]
  have horb : IsOpenEmbedding (fun q : Q => q • S) := by
    have : (fun q : Q => q • S) = o ∘ (Homeomorph.inv Q) := by
      funext q
      apply Subtype.ext
      rw [hsmulH]
      exact (ho q⁻¹).symm
    rw [this]
    exact hoe.comp (Homeomorph.inv Q).isOpenEmbedding
  obtain ⟨fib, hfib⟩ := fibre_on_orbit (Fin n → Fin M → R ⊗[F] E) (HermR R σ n) (Matrix (Fin n) (Fin n) (R ⊗[F] E))
    μ ν (gramR R σ J) g Subtype.val Subtype.val_injective hgc hgf Q heq S horb
  refine ⟨Set.range fun q : Q => q • S, horb.isOpen_range, ⟨1, one_smul _ _⟩, ?_, fib, ?_⟩
  · rintro _ ⟨q, rfl⟩
    change IsUnit ((q • S : HermR R σ n) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det
    rw [hsmulH]
    have hdc : IsUnit (c q).det := Matrix.isUnits_det_units _
    have hdc' : IsUnit (cT (sigR R σ) (c q)).det := by
      simp only [cT, Matrix.det_transpose]
      have := hdc.map (sigR R σ)
      rwa [RingHom.map_det] at this
    rw [Matrix.det_mul, Matrix.det_mul]
    exact (hdc'.mul hS).mul hdc
  · have hpre : gramR R σ J ⁻¹' (Subtype.val '' (Set.range fun q : Q => q • S)) = g ⁻¹' (Set.range fun q : Q => q • S) := by
      ext X
      simp only [Set.mem_preimage, hgf X]
      exact Subtype.val_injective.mem_set_image
    rw [hpre]
    exact hfib

end GlobalTheory.CompanionTheory.SW.GramNear
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureDisintegrationFormulaStatement

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_measure_disintegration_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∀ S : HermR R σ n, IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det → ∃ B : Set (HermR R σ n), IsOpen B ∧ S ∈ B ∧ (∀ S' ∈ B, IsUnit (S' : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ∧ ∃ fib, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ (gramR R σ J) Subtype.val (gramR R σ J ⁻¹' (Subtype.val '' B)) ν B fib := by
  first | exact @GlobalTheory.CompanionTheory.SW.GramNear.exists_fibre_near | exact GlobalTheory.CompanionTheory.SW.GramNear.exists_fibre_near | (intros; apply GlobalTheory.CompanionTheory.SW.GramNear.exists_fibre_near <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RestrFamily

section

@[expose] public section

open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.FibreGlue

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Local

variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure V} {ν : Measure X} {f : V → Y} {g : V → X} {ι : X → Y}

lemma ae_g_eq (hι : Function.Injective ι) (hf : ∀ v, f v = ι (g v)) {U : Set V} {m : Measure V}
    {b : X} (h : m (f ⁻¹' {ι b} ∩ U)ᶜ = 0) : ∀ᵐ v ∂m, g v = b := by
  have h' : ∀ᵐ v ∂m, v ∈ f ⁻¹' {ι b} ∩ U := by
    rw [ae_iff]; exact h
  refine h'.mono fun v hv => ?_
  apply hι
  rw [← hf v]
  exact hv.1

lemma piece (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {s D : Set X} (hD : MeasurableSet D) (hDs : D ⊆ s) {F : X → Measure V}
    (h : IsFibreFamily μ f ι (g ⁻¹' s) ν s F) {φ : V → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ v in g ⁻¹' D, φ v ∂μ = ∫⁻ b in D, ∫⁻ v, φ v ∂(F b) ∂ν := by
  have hm : MeasurableSet (g ⁻¹' D) := hg.measurable hD
  have e1 : ∫⁻ v in g ⁻¹' D, φ v ∂μ = ∫⁻ v in g ⁻¹' s, (g ⁻¹' D).indicator φ v ∂μ := by
    rw [setLIntegral_indicator hm, Set.inter_eq_left.2 (Set.preimage_mono hDs)]
  rw [e1, h.2.1 _ (hφ.indicator hm), ← lintegral_indicator hD]
  refine lintegral_congr fun b => ?_
  have hae := ae_g_eq hι hf (h.1 b)
  by_cases hb : b ∈ D
  · rw [Set.indicator_of_mem hb]
    refine lintegral_congr_ae (hae.mono fun v hv => ?_)
    have : v ∈ g ⁻¹' D := by
      show g v ∈ D
      rw [hv]; exact hb
    simp only [Set.indicator_of_mem this]
  · rw [Set.indicator_of_notMem hb]
    have e : ∫⁻ v, (g ⁻¹' D).indicator φ v ∂(F b) = ∫⁻ _, 0 ∂(F b) := by
      refine lintegral_congr_ae (hae.mono fun v hv => ?_)
      have : v ∉ g ⁻¹' D := by
        show g v ∉ D
        rw [hv]; exact hb
      simp only [Set.indicator_of_notMem this]
    simpa using e


open Classical in
noncomputable def restr (B : Set X) (fam : X → Measure V) : X → Measure V := by
  classical
  exact fun b => if b ∈ B then fam b else 0

lemma restr_family (hι : Function.Injective ι) (hg : Continuous g) (hf : ∀ v, f v = ι (g v))
    {B B₂ : Set X} (hB₂ : IsOpen B₂) (hsub : B₂ ⊆ B) {fam : X → Measure V}
    (h : IsFibreFamily μ f ι (g ⁻¹' B) ν B fam) :
    IsFibreFamily μ f ι (g ⁻¹' B₂) ν B₂ (restr B₂ fam) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b
    by_cases hb : b ∈ B₂
    · simp only [restr, if_pos hb]
      refine measure_mono_null ?_ (h.1 b)
      intro v hv hv2
      apply hv
      refine ⟨hv2.1, ?_⟩
      show g v ∈ B₂
      have : g v = b := by
        apply hι
        rw [← hf v]
        exact hv2.1
      rw [this]; exact hb
    · simp [restr, hb]
  · intro φ hφ
    rw [piece hι hg hf hB₂.measurableSet hsub h hφ, ← lintegral_indicator hB₂.measurableSet]
    refine lintegral_congr fun b => ?_
    by_cases hb : b ∈ B₂
    · simp [restr, hb]
    · simp [restr, hb]
  · intro φ hφ hφc hφs
    have H := h.2.2 φ hφ hφc (hφs.trans (Set.preimage_mono hsub))
    refine ⟨fun b hb => ?_, ?_⟩
    · simp only [restr, if_pos hb]
      exact H.1 b (hsub hb)
    · refine (H.2.mono hsub).congr fun b hb => ?_
      simp only [restr, if_pos hb]

end Local

theorem glue : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (B : Set X), IsOpen B → (∀ b ∈ B, ∃ B' : Set X, IsOpen B' ∧ b ∈ B' ∧ B' ⊆ B ∧ ∃ fib' : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B') ν B' fib') → ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib := by
  intro V X Y _ _ _ _ _ _ _ _ _ _ _ _ μ ν _ _ _ f g ι hι hg hf B hB hloc
  classical
  choose! C hCo hbC hCB F hF using hloc
  let fib : X → Measure V := fun b => if b ∈ B then F b b else 0
  have hfibB : ∀ c ∈ B, fib c = F c c := fun c hc => by simp only [fib, if_pos hc]
  have hagree : ∀ a ∈ B, ∀ c ∈ C a, fib c = F a c := by
    intro a ha c hc
    have hcB : c ∈ B := hCB a ha hc
    have hI : IsOpen (C c ∩ C a) := (hCo c hcB).inter (hCo a ha)
    have r1 := restr_family hι hg hf hI Set.inter_subset_right (hF a ha)
    have u := GlobalTheory.T.fibre_family_eq_on_open_subset V X Y μ ν f g ι hι hg hf (C c) (C c ∩ C a) (hCo c hcB) hI
      Set.inter_subset_left (F c) (restr (C c ∩ C a) (F a)) (hF c hcB) r1 c ⟨hbC c hcB, hc⟩
    have hm : c ∈ C c ∩ C a := ⟨hbC c hcB, hc⟩
    simp only [restr, if_pos hm] at u
    rw [hfibB c hcB, u]
  refine ⟨fib, ?_, ?_, ?_⟩
  · intro b
    by_cases hb : b ∈ B
    · rw [hfibB b hb]
      refine measure_mono_null (Set.compl_subset_compl.2 ?_) ((hF b hb).1 b)
      intro v hv
      exact ⟨hv.1, hCB b hb hv.2⟩
    · simp [fib, hb]
  · intro φ hφ
    rcases B.eq_empty_or_nonempty with rfl | hne
    · simp [fib]
    obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun b : B => C b)
      (fun b => hCo b b.2)
    have hall : ⋃ b : B, C b = B := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun b => hCB b b.2
      · intro b hb
        exact Set.mem_iUnion.2 ⟨⟨b, hb⟩, hbC b hb⟩
    have hTne : T.Nonempty := by
      by_contra hT
      rw [Set.not_nonempty_iff_eq_empty] at hT
      subst hT
      rw [hall] at hTU
      simp only [Set.mem_empty_iff_false, Set.iUnion_of_empty, Set.iUnion_empty] at hTU
      exact hne.ne_empty hTU.symm
    obtain ⟨e, he⟩ := hTc.exists_eq_range hTne
    let s : ℕ → Set X := fun n => C (e n)
    have hsU : ⋃ n, s n = B := by
      rw [← hall, ← hTU, he]
      simp [s]
    have hDm : ∀ n, MeasurableSet (disjointed s n) :=
      MeasurableSet.disjointed fun n => (hCo (e n) (e n).2).measurableSet
    have hDd : Pairwise (Function.onFun Disjoint (disjointed s)) := disjoint_disjointed s
    have hDU : ⋃ n, disjointed s n = B := by rw [iUnion_disjointed, hsU]
    calc ∫⁻ v in g ⁻¹' B, φ v ∂μ
        = ∫⁻ v in ⋃ n, g ⁻¹' (disjointed s n), φ v ∂μ := by
          rw [← Set.preimage_iUnion, hDU]
      _ = ∑' n, ∫⁻ v in g ⁻¹' (disjointed s n), φ v ∂μ :=
          lintegral_iUnion (fun n => hg.measurable (hDm n))
            (fun i j hij => (hDd hij).preimage g) _
      _ = ∑' n, ∫⁻ b in disjointed s n, ∫⁻ v, φ v ∂(fib b) ∂ν := by
          refine tsum_congr fun n => ?_
          rw [piece hι hg hf (hDm n) (disjointed_subset s n) (hF (e n) (e n).2) hφ]
          refine setLIntegral_congr_fun (hDm n) fun b hb => ?_
          rw [hagree (e n) (e n).2 b (disjointed_subset s n hb)]
      _ = ∫⁻ b in ⋃ n, disjointed s n, ∫⁻ v, φ v ∂(fib b) ∂ν :=
          (lintegral_iUnion hDm hDd _).symm
      _ = ∫⁻ b in B, ∫⁻ v, φ v ∂(fib b) ∂ν := by rw [hDU]
      _ = ∫⁻ b, ∫⁻ v, φ v ∂(fib b) ∂ν := by
          rw [← lintegral_indicator hB.measurableSet]
          refine lintegral_congr fun b => ?_
          by_cases hb : b ∈ B
          · simp [hb]
          · simp [hb, fib]
  · intro φ hφ hφc hφs
    have key : ∀ b ∈ B, Integrable φ (fib b) ∧
        ContinuousAt (fun c => ∫ v, φ v ∂(fib c)) b := by
      intro b hb
      obtain ⟨L₁, hL₁c, hbL₁, hL₁C⟩ := exists_compact_between (isCompact_singleton (x := b))
        (hCo b hb) (Set.singleton_subset_iff.2 (hbC b hb))
      obtain ⟨L₂, hL₂c, hbL₂, hL₂C⟩ := exists_compact_between (isCompact_singleton (x := b))
        isOpen_interior hbL₁
      have hclos : IsCompact (closure (interior L₁)) :=
        hL₁c.closure_of_subset interior_subset
      obtain ⟨χ, hχs, hχ1, -⟩ := exists_tsupport_one_of_isOpen_isClosed isOpen_interior hclos
        hL₂c.isClosed hL₂C
      have hK : L₂ ∈ 𝓝 b := mem_interior_iff_mem_nhds.1 (hbL₂ rfl)
      let ψ : V → ℝ := φ * (χ ∘ g)
      have hψ : Continuous ψ := hφ.mul (χ.continuous.comp hg)
      have hψc : HasCompactSupport ψ := hφc.mul_right
      have hψs : tsupport ψ ⊆ g ⁻¹' (C b) := by
        refine (tsupport_mul_subset_right).trans ?_
        refine (tsupport_comp_subset_preimage _ hg).trans ?_
        exact Set.preimage_mono (hχs.trans (interior_subset.trans hL₁C))
      have H := (hF b hb).2.2 ψ hψ hψc hψs
      have hCsub : L₂ ⊆ C b := hL₂C.trans (interior_subset.trans hL₁C)
      have hae : ∀ c ∈ L₂, ∀ᵐ v ∂(F b c), ψ v = φ v := by
        intro c hc
        refine (ae_g_eq hι hf ((hF b hb).1 c)).mono fun v hv => ?_
        simp [ψ, hv, hχ1 hc]
      have hbK : b ∈ L₂ := mem_of_mem_nhds hK
      refine ⟨?_, ?_⟩
      · rw [hagree b hb b (hbC b hb)]
        exact (H.1 b (hbC b hb)).congr (hae b hbK)
      · refine (H.2.continuousAt ((hCo b hb).mem_nhds (hbC b hb))).congr ?_
        filter_upwards [hK] with c hc
        rw [hagree b hb c (hCsub hc)]
        exact integral_congr_ae (hae c hc)
    exact ⟨fun b hb => (key b hb).1, fun b hb => (key b hb).2.continuousWithinAt⟩

end GlobalTheory.CompanionTheory.SW.FibreGlue
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasures

section

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GramExist

theorem exists_gramFib : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n : ℕ) (μ : Measure (Fin n → Fin M → R ⊗[F] E)) (ν : Measure (HermR R σ n)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → ∃ m, IsGramFib R σ J n μ ν m := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n μ ν hμ hν
  have hR' := hR
  obtain ⟨htr, hlc, hsc, ht2, -, -, -, -⟩ := hR'
  obtain ⟨hKtr, hKlc, hKsc, hKt2, -, -, -, hKb, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  have hKu := GlobalTheory.T.units_open_embedding_local_tensor F E σ hCM R hR
  obtain ⟨hXlc, hXsc, hXt2, hXb, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM R n
  obtain ⟨g, hg, hgf⟩ := hlift M J hJ
  haveI := hKb n M
  have hinj : Function.Injective (Subtype.val : HermR R σ n → Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    Subtype.val_injective
  have hBo : IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
    have hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      Continuous.matrix_det continuous_subtype_val
    have : {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} =
        (fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det) ⁻¹'
          Set.range (Units.val : (R ⊗[F] E)ˣ → R ⊗[F] E) := by
      ext S
      simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_range]
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage hc
  have hpre : ∀ B' : Set (HermR R σ n), gramR R σ J ⁻¹' (Subtype.val '' B') = g ⁻¹' B' := by
    intro B'
    ext X
    simp only [Set.mem_preimage, Set.mem_image, hgf X]
    exact hinj.mem_set_image
  have hglue := GlobalTheory.CompanionTheory.SW.FibreGlue.glue (Fin n → Fin M → R ⊗[F] E) (HermR R σ n)
    (Matrix (Fin n) (Fin n) (R ⊗[F] E)) μ ν (gramR R σ J) g Subtype.val hinj hg hgf
    {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} hBo ?_
  · obtain ⟨fib, hfib⟩ := hglue
    refine ⟨fib, ?_⟩
    have hU : {X | IsUnit (gramR R σ J X).det} =
        g ⁻¹' {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_preimage, hgf X]
    unfold IsGramFib
    rw [hU]
    exact hfib
  · intro S hS
    obtain ⟨B, hB, hSB, hBu, fib, hfib⟩ :=
      GlobalTheory.T.gram_fiber_measure_disintegration_formula F E σ hCM M J hJ R hR n μ ν hμ hν S hS
    refine ⟨B, hB, hSB, fun S' hS' => hBu S' hS', fib, ?_⟩
    rw [← hpre]
    exact hfib

end GlobalTheory.CompanionTheory.SW.GramExist
end
end
