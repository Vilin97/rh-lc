module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicIntegralFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFourierTransformSurjectiveIntegral
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierDoubleReflectionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchrodingerIntertwineStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchwartzStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIndicatorFourier
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatRestrictedProductCharStatement
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFourierTransformSurjectiveIntegralStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.finite_fourier_transform_surjective_integral : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ ei : SInf F κ →L[ℂ] SInf F κ, Function.Surjective ei ∧ (∀ f y, ei f y = ∫ x, f x * eInf x y ∂(measI F κ)) ∧
      ∀ (f : SInf F κ) y, Continuous (fun x => f x * eInf x y) ∧ Integrable (fun x => f x * eInf x y) (measI F κ) := by
  first | exact @GlobalTheory.WeylFour.exists_fourier_measI | exact GlobalTheory.WeylFour.exists_fourier_measI | (intros; apply GlobalTheory.WeylFour.exists_fourier_measI <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchwartzStableStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.local_fourier_schwartz_stable : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl (F := F), (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ],
    (∀ φ ∈ SB (κ → Fv F v), fourV ψ v φ ∈ SB (κ → Fv F v)) ∧
    (∀ φ ∈ SB (κ → Fv F v), ∀ χ ∈ SB (κ → Fv F v), fourV ψ v (φ + χ) = fourV ψ v φ + fourV ψ v χ) ∧
    ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ SB (κ → Fv F v) := by
  first | exact @GlobalTheory.WeylFour.fourV_sb | exact GlobalTheory.WeylFour.fourV_sb | (intros; apply GlobalTheory.WeylFour.fourV_sb <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIndicatorFourierStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.local_lattice_indicator_fourier : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl (F := F)) (κ : Type) [Fintype κ],
    GlobalTheory.SympChange.indO (κ := κ) v ∈ SB (κ → Fv F v) ∧
    (PsiUnr ψ v → fourV ψ v (GlobalTheory.SympChange.indO (κ := κ) v) = GlobalTheory.SympChange.indO v) := by
  first | exact @GlobalTheory.WeylFour.IndOSelf.indO_self_fourier | exact GlobalTheory.WeylFour.IndOSelf.indO_self_fourier | (intros; apply GlobalTheory.WeylFour.IndOSelf.indO_self_fourier <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.schrodinger_preserves_schwartz : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)), ∀ Φ ∈ schA F κ, schr ψ w Φ ∈ schA F κ := by
  first | exact @GlobalTheory.WeylFour.SchrKeep.schr_mem_schA | exact GlobalTheory.WeylFour.SchrKeep.schr_mem_schA | (intros; apply GlobalTheory.WeylFour.SchrKeep.schr_mem_schA <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylSpan

theorem pure_eq_pureA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) :
    pure f φ = pureA F (⇑f) (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) := by
  rfl

theorem schA_eq_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) ∧ Φ = pure f φ} := by
  intro F _ _ κ _
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, g, hg, rfl⟩
    let L : ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) →ₗ[ℂ] ((κ → AdeleRing (𝓞 F) F) → ℂ) :=
      { toFun := fun g => pureA F (⇑f) g
        map_add' := fun a b => by funext x; simp [pureA, mul_add]
        map_smul' := fun c a => by funext x; simp [pureA]; ring }
    have h := GlobalTheory.SBSpan.mem_span_restrictedProd F κ g hg
    have h2 : L g ∈ Submodule.map L (Submodule.span ℂ _) := Submodule.mem_map_of_mem h
    rw [Submodule.map_span] at h2
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨p, ⟨φ, hφ, hcof, rfl⟩, rfl⟩
    exact ⟨f, φ, hφ, hcof, (pure_eq_pureA f φ).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro Φ ⟨f, φ, hφ, hcof, rfl⟩
    refine Submodule.subset_span ⟨f, _, ?_, pure_eq_pureA f φ⟩
    exact ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ hcof,
      GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ hcof⟩

end GlobalTheory.WeylSpan

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPureStatement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

theorem _root_.GlobalTheory.T.schwartz_adelic_eq_span_pure : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    schA F κ = Submodule.span ℂ {Φ | ∃ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) ∧
      (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) ∧ Φ = pure f φ} := by
  first | exact @GlobalTheory.WeylSpan.schA_eq_span_pure | exact GlobalTheory.WeylSpan.schA_eq_span_pure | (intros; apply GlobalTheory.WeylSpan.schA_eq_span_pure <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForWeylElement

section

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny


open GlobalTheory.SympChange in
theorem GlobalTheory.WeylFour.weyl_hasOp : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) → (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  intro F _ _ ψ hψ hunr hnt κ _ _
  classical

  have hsp : ∀ {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)),
      spAct (weylM (F := F) (κ := κ)) w = (w.2, -w.1) := by
    intro R _ _ w
    ext k
    · simp [spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]
    · simp [spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]

  have hSB := fun v => GlobalTheory.T.local_fourier_schwartz_stable F ψ hψ v (hnt v) κ
  have hInv := fun v => GlobalTheory.T.local_fourier_double_reflection F ψ hψ v (hnt v) κ
  have hLaw := GlobalTheory.T.local_fourier_schrodinger_intertwine F ψ hψ
  have hInd := fun v => GlobalTheory.T.local_lattice_indicator_fourier F ψ hψ v κ
  have hsmV : ∀ v (c : ℂ) (φ : (κ → Fv F v) → ℂ), fourV ψ v (c • φ) = c • fourV ψ v φ := by
    intro v c φ; funext y
    simp only [fourV, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have h0V : ∀ v, fourV ψ v (0 : (κ → Fv F v) → ℂ) = 0 := by
    intro v; funext y; simp [fourV]
  choose C hC using fun v : Pl F => Submodule.exists_isCompl (SB (κ → Fv F v))
  let P : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := fun v =>
    (SB (κ → Fv F v)).subtype ∘ₗ Submodule.linearProjOfIsCompl _ (C v) (hC v)
  have hPmem : ∀ v φ, P v φ ∈ SB (κ → Fv F v) := fun v φ => (Submodule.linearProjOfIsCompl _ (C v) (hC v) φ).2
  have hPid : ∀ v, ∀ φ ∈ SB (κ → Fv F v), P v φ = φ := fun v φ hφ =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left (hC v) ⟨φ, hφ⟩)
  let ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := fun v =>
    { toFun := fun φ => fourV ψ v (P v φ)
      map_add' := fun φ χ => by
        rw [map_add (f := _)]; exact (hSB v).2.1 _ (hPmem v φ) _ (hPmem v χ)
      map_smul' := fun c φ => by
        rw [map_smul, RingHom.id_apply]; exact hsmV v c _ }
  have hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = fourV ψ v φ := fun v φ hφ => by
    show fourV ψ v (P v φ) = _
    rw [hPid v φ hφ]
  have hneg : ∀ v, ∀ φ ∈ SB (κ → Fv F v), (fun x => φ (-x)) ∈ SB (κ → Fv F v) := fun v φ hφ =>
    ⟨hφ.1.comp_continuous continuous_neg, hφ.2.comp_homeomorph (Homeomorph.neg _)⟩
  have hmap : ∀ v, (SB (κ → Fv F v)).map (ev v) = SB _ := by
    intro v
    apply le_antisymm
    · rintro _ ⟨φ, hφ, rfl⟩
      rw [hev v φ hφ]; exact (hSB v).1 φ hφ
    · intro φ hφ
      have h1 := hneg v φ hφ
      refine ⟨fourV ψ v (fun x => φ (-x)), (hSB v).1 _ h1, ?_⟩
      rw [hev v _ ((hSB v).1 _ h1), hInv v _ h1]
      simp
  have hinj : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0 := by
    intro v φ hφ h
    rw [hev v φ hφ] at h
    have h2 := hInv v φ hφ
    rw [h, h0V] at h2
    funext x
    have h3 := congrFun h2 (-x)
    simp only [Pi.zero_apply, neg_neg] at h3
    exact h3.symm

  obtain ⟨ei, hsurj, hei, hcont⟩ := GlobalTheory.T.finite_fourier_transform_surjective_integral F κ
  obtain ⟨μ, hμ, hprod⟩ := GlobalTheory.T.exists_haar_adelic_integral_formula F ψ hψ hunr hnt κ
  haveI := hμ
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hspan := GlobalTheory.T.schwartz_adelic_eq_span_pure F κ
  let fA : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ := fun Φ y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ
  have hpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = indO v) → ∀ y, Integrable (fun x => pure f φ x * ψ (x ⬝ᵥ y)) μ ∧
        fA (pure f φ) y = pure (ei f) (fun v => fourV ψ v (φ v)) y := by
    intro f φ hφ hae y
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.schwartz_bruhat_restricted_product_char F ψ hψ hunr κ f φ y hφ hae
    have e : (fun x => pure f φ x * ψ (x ⬝ᵥ y)) = fun x =>
        (fun z => f z * eInf z (fun i => evI F (y i))) (fun i => evI F (x i)) *
          ∏ᶠ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) (fun i => evFin F v (x i)) :=
      funext h3
    obtain ⟨hc, hi⟩ := hcont f (fun i => evI F (y i))
    obtain ⟨j1, j2⟩ := hprod _ _ hc hi h1 h2
    refine ⟨e ▸ j1, ?_⟩
    show (∫ x, pure f φ x * ψ (x ⬝ᵥ y) ∂μ) = _
    rw [e, j2, ← hei]
    rfl
  have hint : ∀ Φ ∈ schA F κ, ∀ y, Integrable (fun x => Φ x * ψ (x ⬝ᵥ y)) μ := by
    intro Φ hΦ y
    rw [hspan] at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, φ, hφ, hae, rfl⟩ := h
      exact (hpure f φ hφ hae y).1
    | zero => simp
    | add Φ Ψ _ _ h1 h2 =>
      refine (h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)
      simp [add_mul]
    | smul c Φ _ h => simpa [mul_assoc] using h.const_mul c
  have hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, fA (Φ + Ψ) = fA Φ + fA Ψ := by
    intro Φ hΦ Ψ hΨ; funext y
    simp only [fA, Pi.add_apply, add_mul]
    exact integral_add (hint Φ hΦ y) (hint Ψ hΨ y)
  have hsmul : ∀ (c : ℂ) (Φ : (κ → AF F) → ℂ), fA (c • Φ) = c • fA Φ := by
    intro c Φ; funext y
    simp only [fA, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have hkeep : ∀ Φ ∈ schA F κ, fA Φ ∈ schA F κ := by
    intro Φ hΦ
    rw [hspan] at hΦ ⊢
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, φ, hφ, hae, rfl⟩ := h
      have e : fA (pure f φ) = pure (ei f) (fun v => fourV ψ v (φ v)) := funext fun y => (hpure f φ hφ hae y).2
      rw [e]
      refine Submodule.subset_span ⟨ei f, fun v => fourV ψ v (φ v), fun v => (hSB v).1 _ (hφ v), ?_, rfl⟩
      filter_upwards [hae, hunr] with v h1 h2
      rw [h1, (hInd v).2 h2]
    | zero =>
      have : fA 0 = 0 := by funext y; simp [fA]
      rw [this]; exact zero_mem _
    | add Φ Ψ hΦ hΨ h1 h2 =>
      rw [hadd Φ (hspan ▸ hΦ) Ψ (hspan ▸ hΨ)]; exact add_mem h1 h2
    | smul c Φ _ h =>
      rw [hsmul]; exact Submodule.smul_mem _ c h
  have hlawA : ∀ w Φ, fA (schr ψ w Φ) = schr ψ (w.2, -w.1) (fA Φ) := by
    intro w Φ; funext y
    simp only [fA, schr]
    have h1 := integral_add_right_eq_self (μ := μ) (fun z => ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) *
      Φ z * ψ ((z - w.1) ⬝ᵥ y)) w.1
    simp only [add_sub_cancel_right] at h1
    rw [h1, ← integral_const_mul]
    congr 1; funext z
    have h2 : (⅟(2 : AF F)) + ⅟2 = 1 := invOf_two_add_invOf_two
    have key : ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (z - w.1) ⬝ᵥ y =
        (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) + z ⬝ᵥ (y + w.2) := by
      simp only [sub_dotProduct, dotProduct_add, dotProduct_neg]
      rw [dotProduct_comm w.2 w.1, dotProduct_comm y w.1]
      linear_combination (w.1 ⬝ᵥ w.2) * h2
    calc ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ z * ψ ((z - w.1) ⬝ᵥ y)
        = Φ z * ψ (((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (z - w.1) ⬝ᵥ y) := by
          rw [AddChar.map_add_eq_mul ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) ((z - w.1) ⬝ᵥ y)]; ring
      _ = _ := by
          rw [key, AddChar.map_add_eq_mul ψ (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) (z ⬝ᵥ (y + w.2))]; ring
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (schA F κ)
  let Q : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := (schA F κ).subtype ∘ₗ Submodule.linearProjOfIsCompl _ D hD
  have hQmem : ∀ Φ, Q Φ ∈ schA F κ := fun Φ => (Submodule.linearProjOfIsCompl _ D hD Φ).2
  have hQid : ∀ Φ ∈ schA F κ, Q Φ = Φ := fun Φ hΦ =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hD ⟨Φ, hΦ⟩)
  let e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ :=
    { toFun := fun Φ => fA (Q Φ)
      map_add' := fun Φ Ψ => by rw [map_add (f := _)]; exact hadd _ (hQmem Φ) _ (hQmem Ψ)
      map_smul' := fun c Φ => by rw [map_smul, RingHom.id_apply]; exact hsmul c _ }
  have he : ∀ Φ ∈ schA F κ, e Φ = fA Φ := fun Φ hΦ => by
    show fA (Q Φ) = _
    rw [hQid Φ hΦ]
  refine ⟨e, ei, ev, hsurj, fun Φ hΦ => ?_, fun w Φ hΦ => ?_, hmap, hinj, fun v w φ hφ => ?_, ?_, ?_⟩
  · rw [he Φ hΦ]; exact hkeep Φ hΦ
  · rw [he _ (GlobalTheory.T.schrodinger_preserves_schwartz F ψ hψ κ w Φ hΦ), he Φ hΦ, hlawA, hsp]
  · rw [hsp, hev v _ ((hSB v).2.2 w φ hφ), hev v φ hφ, hLaw v κ w φ]
  · filter_upwards [hunr] with v hv
    rw [hev v _ (hInd v).1, (hInd v).2 hv]
  · intro f φ hφ hae
    have hm : pure f φ ∈ schA F κ := by
      rw [hspan]; exact Submodule.subset_span ⟨f, φ, hφ, hae, rfl⟩
    have e2 : (fun v => ev v (φ v)) = fun v => fourV ψ v (φ v) := funext fun v => hev v _ (hφ v)
    rw [he _ hm, e2]
    exact funext fun y => (hpure f φ hφ hae y).2
end
end
