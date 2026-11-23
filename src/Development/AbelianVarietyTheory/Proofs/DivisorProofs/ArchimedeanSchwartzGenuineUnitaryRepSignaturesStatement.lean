module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousRhoApplyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivContinuousCharacterRealUnitaryOneParameterStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanPhaseSpaceCoordinatesPlaceSignaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousHomUnitaryRealPlacesPlacewiseSigStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodingerStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousSymplecticHomOfIndefiniteUnitary
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLieRightActionRealCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfComStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionQuadraticOperatorsFactorSignaturesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergOpArchimedeanVectorActsBySchrodingerTrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExist
public import CompanionTheory.ThickeningEstimates.LieGroupReduction.MetaplecticRepresentation.RealMetaplecticRepresentationHolds
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftDarbouxAdelicSymplectic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPairingSpaceResultOfSchrodingerCoordinates
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Separation.CompletelyRegular

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticHomOfUnitaryTransposeAction

section

@[expose] public section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.ColActionD

theorem exists_symplectic_hom_of_unitary_dep : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  intro ι l _ _ _ _ P Q R S φ hφ G _ _ k hk hkJ
  let A : G → (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) := fun g =>
    { toFun := fun c w => c w * (k g w)ᵀ
      map_add' := fun c c' => by ext w : 1; simp [Matrix.add_mul]
      map_smul' := fun r c => by ext w : 1; simp [Matrix.smul_mul] }
  let T : G → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ) := fun g => φ.toLinearMap ∘ₗ A g ∘ₗ φ.symm.toLinearMap
  have hT : ∀ g c, T g (φ c) = φ (fun w => c w * (k g w)ᵀ) := fun g c => by simp [T, A]
  have hsy : ∀ g u v, sympl (T g u) (T g v) = sympl u v := by
    intro g u v
    obtain ⟨c, rfl⟩ := φ.surjective u
    obtain ⟨c', rfl⟩ := φ.surjective v
    rw [hT, hT, hφ, hφ]
    simp only [GlobalTheory.ColAction.signed_sum_mul_transpose _ _ _ (hkJ g _)]
  have hmem : ∀ g, LinearMap.toMatrix' (T g) ∈ Matrix.symplecticGroup l ℝ := fun g =>
    GlobalTheory.ColAction.mem_symplecticGroup_of_sympl _
      (fun u v => by simpa only [LinearMap.toMatrix'_mulVec] using hsy g u v)
  have hTmul : ∀ g h, T (g * h) = T g ∘ₗ T h := by
    intro g h
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    show T (g * h) (φ c) = T g (T h (φ c))
    rw [hT, hT, hT]
    congr 1
    ext w : 1
    simp [map_mul, Pi.mul_apply, Matrix.transpose_mul, Matrix.mul_assoc]
  have hT1 : T 1 = LinearMap.id := by
    apply LinearMap.ext
    intro u
    obtain ⟨c, rfl⟩ := φ.surjective u
    rw [hT]
    simp
  let s : G →* Matrix.symplecticGroup l ℝ :=
    { toFun := fun g => ⟨LinearMap.toMatrix' (T g), hmem g⟩
      map_one' := by
        apply Subtype.ext
        simp only [hT1, LinearMap.toMatrix'_id]
        rfl
      map_mul' := fun g h => by
        apply Subtype.ext
        simp only [hTmul, LinearMap.toMatrix'_comp]
        rfl }
  refine ⟨s, ?_, fun g c => ?_⟩
  · apply Continuous.subtype_mk
    refine continuous_pi fun a => continuous_pi fun b => ?_
    have e : ∀ g, LinearMap.toMatrix' (T g) a b = φ (fun w => φ.symm (Pi.single b 1) w * (k g w)ᵀ) a := by
      intro g
      rw [LinearMap.toMatrix'_apply, ← hT, φ.apply_symm_apply]
    simp only [e]
    exact (continuous_apply a).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      (continuous_pi fun w => continuous_const.matrix_mul ((continuous_apply w).comp hk).matrix_transpose))
  · show LinearMap.toMatrix' (T g) *ᵥ φ c = _
    rw [LinearMap.toMatrix'_mulVec, hT]

end GlobalTheory.ColActionD
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticHomOfUnitaryTransposeActionStatement

section

@[expose] public section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_symplectic_hom_of_unitary_transpose_action : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ s : G →* Matrix.symplecticGroup l ℝ, Continuous s ∧
      ∀ g c, (s g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ φ c = φ fun w => c w * (k g w)ᵀ := by
  first | exact @GlobalTheory.ColActionD.exists_symplectic_hom_of_unitary_dep | exact GlobalTheory.ColActionD.exists_symplectic_hom_of_unitary_dep | (intros; apply GlobalTheory.ColActionD.exists_symplectic_hom_of_unitary_dep <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMetaplecticRepresentationHolds

section

@[expose] public section

theorem GlobalTheory.Published.realMetaplecticRepresentation_holds : GlobalTheory.Published.RealMetaplecticRepresentation :=
  CompanionTheory.ThKR.realMetaplecticRepresentation_holds
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzGenuineUnitaryRepSignatures

section

@[expose] public section

noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD GlobalTheory.RealWeil GlobalTheory.ArchUniq GlobalTheory.ArchRep

namespace GlobalTheory.ArchRepD

theorem archRepD :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines (σ := σ) JB, ∀ Y, IsGenD τ C γ Y → ∀ (T : TensD F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨n, θ, φ, φ₀, hp, hq, hφ, hφu⟩ := GlobalTheory.T.exists_archimedean_phaseSpace_coordinates_placeSignatures F E σ α β κ P Q R S τ JA JB d a b A C hCM hFr
  obtain ⟨k, hkc, hkC, hkJ, hcan⟩ := GlobalTheory.T.exists_continuous_hom_unitary_realPlaces_placewise_signature F E σ β R S τ JB b C hCM hFr.2.2
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨ω, hωc, hωi⟩ := GlobalTheory.T.exists_oscillator_action_normalising_schrodinger _ _ P Q R S φ hφ (GlobalTheory.T.continuous_rho_apply _) (UG (cA σ) JB) k hkc hkJ
  obtain ⟨s, hsc, hsφ⟩ := GlobalTheory.T.exists_symplectic_hom_of_unitary_transpose_action _ _ P Q R S φ hφ (UG (cA σ) JB) k hkc hkJ
  obtain ⟨ρ, η, hη1, hη2, hη3, hρi, hρu, hρc, hρd⟩ :=
    realRep GlobalTheory.Published.realMetaplecticRepresentation_holds s hsc ω hωc fun g w v => by
      obtain ⟨c, rfl⟩ := φ.surjective w
      rw [hsφ, hωi]
  obtain ⟨kk, hkk⟩ := GlobalTheory.T.deriv_continuous_character_real_unitary_one_parameter F E σ β R S τ JB b C hCM hFr.2.2 η (fun g h _ _ => hη1 g h) hη2.continuousOn
    fun g _ => hη3 g
  let toE : SInf F κ →L[ℂ] Sch (Fin n) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ.symm
  let toV : Sch (Fin n) →L[ℂ] SInf F κ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) θ
  have htoE : ∀ g, ⇑(toE g) = ⇑g ∘ ⇑θ.symm := fun g => rfl
  have htoV : ∀ h, ⇑(toV h) = ⇑h ∘ ⇑θ := fun h => rfl
  have hVE : ∀ g, toV (toE g) = g := fun g => by ext x; simp [htoE, htoV]
  have hEV : ∀ h, toE (toV h) = h := fun h => by ext x; simp [htoE, htoV]
  clear_value toE toV
  have hS := SchrTransport.schr_coords (trP F κ) θ φ₀ hp hq
  let ρ' : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ) :=
    { toFun := fun g => toV ∘L ρ g ∘L toE
      map_one' := ContinuousLinearMap.ext fun f => by
        rw [map_one]
        exact hVE f
      map_mul' := fun g h => ContinuousLinearMap.ext fun f => by
        simp only [map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.comp_apply, hEV] }
  have hρ' : ∀ g f, ρ' g f = toV (ρ g (toE f)) := fun _ _ => rfl
  clear_value ρ'
  refine ⟨ρ', fun w => kk w / 2, fun g _ => ⟨fun u hu f f₁ hf h => ?_, fun ν hν f₁ f₂ => ?_⟩, fun L f => ?_,
    fun γ hγ Y hY T L => ?_⟩
  · choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    obtain ⟨c, hc⟩ : ∃ c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ,
        ∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ :=
      ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, fun w => by
        have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
        simp only [Matrix.mul_assoc]
        rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    have hu' : At (evI F) (actB (cA σ) g u) := fun t ht => by
      rw [actB, ← Matrix.smul_mul, hu t ht, Matrix.zero_mul]
    have hc' : ∀ w, (actB (cA σ) g u).map (piInf (τ w)) = A w * (c w * (k g w)ᵀ) * (C w)ᵀ := fun w => by
      rw [actB, Matrix.map_mul, hc, Matrix.transpose_map, Matrix.mul_assoc, ← Matrix.transpose_mul, hkC,
        Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    have e1 : ⇑f₁ = schrF (trP F κ) (locV (d.e u).1, locV (d.e u).2) ⇑f := by
      funext y
      have := congrFun ((GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ u hu f fun _ => 1).symm.trans (hf fun _ => 1)) (liftV y)
      simp only [pureA, liftV, Prod.fst, RingEquiv.apply_symm_apply, mul_one] at this
      exact this.symm
    have e2 : ⇑(toE f₁) = rhoFun (φ c) ⇑(toE f) := by
      have := hS (locV (d.e u).1, locV (d.e u).2) ⇑(toE f)
      rw [← htoV, hVE, ← e1, ← hφu u c hu hc] at this
      rw [htoE, this]
      funext x
      simp
    have e3 := hρi g _ _ _ e2
    rw [hsφ, hφu _ _ hu' hc'] at e3
    rw [GlobalTheory.T.heisenbergOp_archimedean_vector_acts_by_schrodinger_trace F E σ α β κ ψ JA JB d hψ _ hu', hρ', hρ', htoV, htoV, hS, e3]
  · haveI : BorelSpace ({w : InfinitePlace F // w.IsReal} → ℝ) := Pi.borelSpace
    haveI : BorelSpace ({w : InfinitePlace F // w.IsComplex} → ℂ) := Pi.borelSpace
    haveI : BorelSpace (mixedEmbedding.mixedSpace F) := Prod.borelSpace
    haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := Pi.borelSpace
    obtain ⟨r, hr⟩ := haar_coords ν θ
    rw [hr, hr]
    congr 1
    simp only [hρ', htoV, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rw [hρu]
    simp only [htoE, Function.comp_apply]
  · simp only [hρ']
    exact (hρc (L ∘L toV) (toE f)).continuousOn
  · have hkY : ∀ (t : ℝ) w, k (γ (Multiplicative.ofAdd t)) w = NormedSpace.exp (t • Y w) := fun t w =>
      hcan w _ _ ((hkC _ w).symm.trans (hY t w))
    have hYu : ∀ w, Y w ∈ upq (R w) (S w) := fun w => GlobalTheory.RealLiftGen.mem_upq_of (Y w) fun t => by
      have := congrArg (fun X => X.map star) (hkJ (γ (Multiplicative.ofAdd t)) w)
      simp only [GlobalTheory.RealLiftGen.map_star_mul, GlobalTheory.RealLiftGen.Jm_map_star, hkY] at this
      refine Eq.trans ?_ this
      congr 2
      ext i j
      simp
    obtain ⟨Z, hZ, hZφ, hZe⟩ := GlobalTheory.T.exists_symplecticLie_right_action_realCoordinates _ _ P Q R S φ hφ Y hYu
    have hsZ : ∀ t : ℝ, (s (γ (Multiplicative.ofAdd t)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) =
        NormedSpace.exp (t • Z) := fun t => Matrix.toLin'.injective (LinearMap.ext fun v => by
      obtain ⟨c, rfl⟩ := φ.surjective v
      rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
      calc
        _ = φ (fun w => c w * (k (γ (Multiplicative.ofAdd t)) w)ᵀ) := hsφ _ _
        _ = _ := by simp only [hkY, ← hZe])
    have hd := hρd (fun t => γ (Multiplicative.ofAdd t)) (hγ.1.comp continuous_ofAdd) (by change γ 1 = 1; exact map_one γ) Z hZ hsZ _
      (hkk γ hγ Y hY) (L ∘L toV) (toE (Φ T))
    obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ α β κ ψ JA JB d hψ
    have hΨ : ∀ c T, (toE.toLinearMap ∘ₗ Φ) (sumPl (fun w => heisOp (c w)) T) = dRho (φ c) ((toE.toLinearMap ∘ₗ Φ) T) := by
      intro c T
      obtain ⟨u, ⟨hu, hc⟩, -⟩ := GlobalTheory.T.existsUnique_archimedeanMatrix_adeleExtension_of_components σ τ hCM fun w => A w * c w * (C w)ᵀ
      have e1 := (GlobalTheory.RealLift.actsLaws F κ (Φ T) _ _).2.2.2.2 _ (hΦ.2 u hu c hc T) (hD u hu (Φ T)).1
      ext x
      obtain ⟨y, rfl⟩ := θ.surjective x
      have e2 := SchrTransport.dRho_coords (trP F κ) θ φ₀ hp hq (locV (d.e u).1, locV (d.e u).2) (Φ T) (toE (Φ T))
        (by rw [← htoV, hVE]) y
      rw [← hφu u c hu hc] at e2
      simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe]
      rw [← e2, e1, htoE, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
      exact (hD u hu (Φ T)).2 y
    have e3 := GlobalTheory.T.fockAction_quadraticOperators_factorSignatures _ _ P Q R S φ hφ _ hΨ Y hYu Z hZφ T
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at e3
    have hf : (fun t : ℝ => L (ρ' (γ (Multiplicative.ofAdd t)) (Φ T))) =
        (fun t : ℝ => L (toV (ρ (γ (Multiplicative.ofAdd t)) (toE (Φ T))))) := by
      funext t
      exact congrArg L (hρ' (γ (Multiplicative.ofAdd t)) (Φ T))
    rw [hf]
    refine hd.congr_deriv ?_
    rw [e3, sumPl_add_smul]
    simp only [ContinuousLinearMap.comp_apply, hVE, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_add, map_smul, smul_eq_mul, Finset.sum_div]
    congr 2
    exact Finset.sum_congr rfl fun w _ => by ring

end GlobalTheory.ArchRepD

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzGenuineUnitaryRepSignaturesStatement

section

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open scoped Classical
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.archimedeanSchwartz_genuineUnitaryRep_signatures : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ρ : UG (cA σ) JB →* (SInf F κ →L[ℂ] SInf F κ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ u : Matrix α β (AE F E), At (evI F) u → ∀ f f₁ : SInf F κ,
          (∀ h : (κ → Af F) → ℂ, d.rho ψ u (pureA F f h) = pureA F f₁ h) →
            ∀ h : (κ → Af F) → ℂ, d.rho ψ (actB (cA σ) g u) (pureA F (ρ g f) h) = pureA F (ρ g f₁) h) ∧
        ∀ ν : Measure (κ → mixedEmbedding.mixedSpace F), ν.IsAddHaarMeasure → ∀ f₁ f₂ : SInf F κ,
          ∫ x, star (ρ g f₁ x) * ρ g f₂ x ∂ν = ∫ x, star (f₁ x) * f₂ x ∂ν) ∧
      (∀ (L : SInf F κ →L[ℂ] ℂ) (f : SInf F κ),
        ContinuousOn (fun g => L (ρ g f)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ∀ γ ∈ RLines (σ := σ) JB, ∀ Y, IsGenD τ C γ Y → ∀ (T : TensD F P Q R S) (L : SInf F κ →L[ℂ] ℂ),
        HasDerivAt (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T)))
          (L (Φ (sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • 1) T))) 0 := by
  first | exact @GlobalTheory.ArchRepD.archRepD | exact GlobalTheory.ArchRepD.archRepD | (intros; apply GlobalTheory.ArchRepD.archRepD <;> assumption)
end
end
