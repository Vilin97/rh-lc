module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSplittingsDifferByCharacterStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivContinuousCharacterRealUnitaryOneParameterStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanSchwartzGenuineUnitaryRepSignaturesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicRepExtendingArchimedeanSchwartzRepStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoArchimedeanAdelicPureTensorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergRhoSplitArchimedeanFiniteStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorUnitaryAdelicL2Statement
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenuineSplittingAdelicSchwartzPlaceSignatu

section

@[expose] public section

noncomputable section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.GenRepD

theorem rho_add' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) (φ₁ φ₂ : (κ → R) → ℂ) :
    d.rho ψ w (φ₁ + φ₂) = d.rho ψ w φ₁ + d.rho ψ w φ₂ := by
  funext x; simp [Darboux.rho, schr, mul_add]

theorem rho_smul' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) (c : ℂ) (φ : (κ → R) → ℂ) :
    d.rho ψ w (c • φ) = c • d.rho ψ w φ := by
  funext x; simp [Darboux.rho, schr]; ring

theorem rho_zero' {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (w : W) :
    d.rho ψ w 0 = 0 := by
  funext x; simp [Darboux.rho, schr]


open scoped Classical in
theorem genRepD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) ∧
      (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ActsByD τ C ω₀ Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c₀ := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ρ, c₀, hR, hcont, hder⟩ := GlobalTheory.T.archimedeanSchwartz_genuineUnitaryRep_signatures F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ω₀, hω⟩ := GlobalTheory.T.exists_adelicRep_extending_archimedeanSchwartzRep F κ (UG (cA σ) JB) ρ
  have hgen : ∀ g, ∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ := by
    intro g φ hφ
    unfold schA at hφ ⊢
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      rw [hω]
      exact Submodule.subset_span ⟨ρ g f, h, hh, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hact1 : ∀ x : Matrix α β (AE F E), actB (cA σ) (1 : UG (cA σ) JB) x = x := fun x => by simp [actB]
  refine ⟨ω₀, c₀, fun g hg => ⟨hgen g, fun w φ hφ => ?_, fun μ hμ φ hφ =>
    GlobalTheory.T.weil_operator_unitary_adelic_L2 F κ (ρ g).toLinearMap (ω₀ g) (hω g) (hR g hg).2 μ hμ φ hφ⟩, fun l hl φ hφ => ?_, ?_⟩
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨u, H, hu, hsplit⟩ := GlobalTheory.T.heisenbergRho_split_archimedean_finite F E σ α β κ ψ JA JB d w
      obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.heisenbergRho_archimedean_adelicPureTensor F E σ α β κ ψ JA JB d hψ u hu f
      have e1 : d.rho ψ w (pureA F f h) = pureA F f₁ (H h) := by
        have := hsplit 1 h1m f f₁ h (by simpa only [hact1] using hf₁)
        simpa only [hact1] using this
      rw [e1, hω, hω]
      exact (hsplit g hg (ρ g f) (ρ g f₁) h ((hR g hg).1 u hu f f₁ hf₁)).symm
    | zero => rw [rho_zero', map_zero, rho_zero']
    | add x y _ _ hx hy => rw [rho_add', map_add (f := _), map_add (f := _), hx, hy, rho_add']
    | smul c x _ hx => rw [rho_smul', map_smul, map_smul, hx, rho_smul']
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨T, hT⟩ := hl h hh
      have e : (fun g => l (ω₀ g (pureA F f h))) = fun g => T (ρ g f) := funext fun g => by rw [hω, hT]
      rw [e]
      exact hcont T f
    | zero => simp only [map_zero]; exact continuousOn_const
    | add x y _ _ hx hy => simp only [map_add (f := _)]; exact hx.add hy
    | smul c x _ hx => simp only [map_smul, smul_eq_mul]; exact continuousOn_const.mul hx
  · intro γ hγ Y hY T h hh l hl
    obtain ⟨L, hL⟩ := hl h hh
    show HasDerivAt (fun t : ℝ => l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) h))) _ 0
    have e : (fun t : ℝ => l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) h))) =
        (fun t : ℝ => L (ρ (γ (Multiplicative.ofAdd t)) (Φ T))) := by
      funext t
      exact (congrArg l (hω (γ (Multiplicative.ofAdd t)) (Φ T) h)).trans (hL _)
    rw [e, hL]
    exact hder γ hγ Y hY T L

end GlobalTheory.GenRepD

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenuineSplittingAdelicSchwartzPlaceSignatuStatement

section

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.exists_genuineSplitting_adelicSchwartz_placeSignature : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ →
    ∃ (ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) ∧
      (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ActsByD τ C ω₀ Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c₀ := by
  first | exact @GlobalTheory.GenRepD.genRepD | exact GlobalTheory.GenRepD.genRepD | (intros; apply GlobalTheory.GenRepD.genRepD <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweSplittingActsFockActionPlusTraceMultiples

section

@[expose] public section

noncomputable section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

namespace GlobalTheory.HoweD

theorem lieScalarD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    ∃ c, ActsByD τ C om Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ om hCM hψ hFr hΦ hom
  obtain ⟨ω₀, c₀, hH, hc, hact⟩ := GlobalTheory.T.exists_genuineSplitting_adelicSchwartz_placeSignature F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ν, hν, hmul, hνc, hν0⟩ := GlobalTheory.T.archimedean_splittings_differ_by_character F E σ α β κ ψ JA JB d om ω₀ hψ hom hH hc
  obtain ⟨k, hk⟩ := GlobalTheory.T.deriv_continuous_character_real_unitary_one_parameter F E σ β R S τ JB b C hCM hFr.2.2 ν hmul hνc hν0
  refine ⟨fun w => c₀ w + k w, ?_⟩
  intro γ hγ Y hY T g hg l hl
  have hH1 : ∀ t : ℝ, At (evI F) (((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)) - 1) := fun t => hγ.2 _
  have hpm : ∀ f : SInf F κ, pureA F f g ∈ schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have e1 : (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) =
      fun t => ν (γ (Multiplicative.ofAdd t)) * l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g)) := by
    funext t; rw [hν _ (hH1 t) _ (hpm _), map_smul, smul_eq_mul]
  show HasDerivAt (fun t : ℝ => l (om (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) g))) _ 0
  rw [e1]
  have h3 := (hk γ hγ Y hY).mul (hact γ hγ Y hY T g hg l hl)
  have hγ0 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by rw [ofAdd_zero, map_one]
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hν1 : ν 1 = 1 := by
    have := hmul 1 1 h1m h1m
    rw [mul_one] at this
    exact (mul_eq_left₀ (hν0 1 h1m)).mp this.symm
  beta_reduce at h3
  set_option backward.isDefEq.respectTransparency false in
    rw [hγ0, hν1, map_one, Module.End.one_apply, one_mul] at h3
  refine h3.congr_deriv ?_
  have e2 : sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) +
        (((fun w => c₀ w + k w) w) * (Y w).trace) • (1 : Module.End ℂ _)) =
      sumPl (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) +
        (∑ w, k w * (Y w).trace) • (1 : Module.End ℂ (TensD F P Q R S)) := by
    simp only [add_mul, add_smul, ← add_assoc]
    exact GlobalTheory.LieScal.sumPl_add_smul
      (fun w => fockAct2 (P w) (Q w) (R w) (S w) (Y w) + (c₀ w * (Y w).trace) • (1 : Module.End ℂ _)) _
  rw [e2, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add (f := _), map_smul]
  have key : ∀ (z : ℂ) (f f' : SInf F κ), pureA F ⇑(f' + z • f) g = z • pureA F ⇑f g + pureA F ⇑f' g := by
    intro z f f'; funext x; simp [pureA]; ring
  rw [key, map_add (f := _), map_smul, smul_eq_mul]

end GlobalTheory.HoweD

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweSplittingActsFockActionPlusTraceMultiplesStatement

section

@[expose] public section

open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

theorem _root_.GlobalTheory.T.howeSplitting_acts_fockAction_plus_traceMultiples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (Φ : TensD F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → IsStd ψ →
    FramedD τ JA JB a b A C → IsFockMapD ψ τ d A C Φ → IsUSplitting (adeleClass F) ψ d (actB (cA σ)) om →
    ∃ c, ActsByD τ C om Φ (fun w => fockAct2 (P w) (Q w) (R w) (S w)) c := by
  first | exact @GlobalTheory.HoweD.lieScalarD | exact GlobalTheory.HoweD.lieScalarD | (intros; apply GlobalTheory.HoweD.lieScalarD <;> assumption)
end
end
