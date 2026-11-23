module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisThetaLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CmAdeleIdempotentOfPlacePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorPureTensorPlaceByPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedTensorBasePointNormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorMemSpanLocalHeisenbergTranslatesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaInnerProductHermitianStatement
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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorRealPlaceEqHeisenbergIntegralBaseStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorFinitePlaceHeisenbergSumBaseVector

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorFin

theorem isLocOp_of_mem_span {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hψ : IsStdChar D ψ (-1)) (hμ : IsCovolOne (ratL T S) μ 𝓕) {f₀ : WO S T → ℂ} (h₀ : IsThetaFunO ψ S T f₀) (p : Place D)
    {x : WO S T → ℂ} (hx : x ∈ Submodule.span ℂ (Set.range fun w : WO S T => heisO ψ S T (wAt p w) f₀)) :
    IsThetaFunO ψ S T x ∧ IsLocOp ψ S T μ 𝓕 f₀ p x := by
  have hh := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have ip := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    exact ⟨hh _ _ h₀, fun φ => φ w, fun _ _ => rfl, fun f hf => ⟨_, hh (wAt p w) f hf, fun _ _ => rfl⟩, fun _ _ => rfl⟩
  | zero =>
    have hz : ∀ g, ipO μ 𝓕 (0 : WO S T → ℂ) g = 0 := fun g => by simp [ipO]
    exact ⟨GlobalTheory.WeilVacMove.isTheta_zero, fun _ => 0, fun _ _ => by simp,
      fun f _ => ⟨0, GlobalTheory.WeilVacMove.isTheta_zero, fun g _ => hz g⟩, fun g _ => hz g⟩
  | add y z _ _ hy hz =>
    obtain ⟨ty, L, L1, L2, L3⟩ := hy
    obtain ⟨tz, M, M1, M2, M3⟩ := hz
    refine ⟨GlobalTheory.WeilVacMove.isTheta_add ty tz, fun φ => L φ + M φ, fun c φ => ?_, fun f hf => ?_, fun g hg => ?_⟩
    · simp only [L1, M1, mul_add]
    · obtain ⟨a, ta, ha⟩ := L2 f hf
      obtain ⟨b, tb, hb⟩ := M2 f hf
      refine ⟨a + b, GlobalTheory.WeilVacMove.isTheta_add ta tb, fun g hg => ?_⟩
      rw [((ip a g ta hg).2.2.2.1 b tb).1, ha g hg, hb g hg]
    · rw [((ip y g ty hg).2.2.2.1 z tz).1, L3 g hg, M3 g hg]
  | smul c y _ hy =>
    obtain ⟨ty, L, L1, L2, L3⟩ := hy
    refine ⟨GlobalTheory.WeilVacMove.isTheta_smul c ty, fun φ => c * L φ, fun d φ => ?_, fun f hf => ?_, fun g hg => ?_⟩
    · simp only [L1]
      ring
    · obtain ⟨a, ta, ha⟩ := L2 f hf
      refine ⟨c • a, GlobalTheory.WeilVacMove.isTheta_smul c ta, fun g hg => ?_⟩
      rw [((ip a g ta hg).2.2.1 c).1, ha g hg]
    · rw [((ip y g ty hg).2.2.1 c).1, L3 g hg]

theorem isLocOp_of_isLocal_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → IsLocOp ψ S T μ 𝓕 f₀ (.inl v) x :=
  fun D ψ θ S T sS sT ΛS ΛT f₀ _ _ hb hμ v x hx =>
    (isLocOp_of_mem_span (base_std hb) hμ (base_theta hb) (.inl v)
      (GlobalTheory.T.localFactor_mem_span_localHeisenbergTranslates D ψ θ S T sS sT ΛS ΛT f₀ hb v x hx)).2

end GlobalTheory.PlaceTensorFin
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFactorFinitePlaceHeisenbergSumBaseVectorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.local_factor_finite_place_heisenberg_sum_base_vector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : FinPl D) (x : WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT (.inl v) x → IsLocOp ψ S T μ 𝓕 f₀ (.inl v) x := by
  first | exact @GlobalTheory.PlaceTensorFin.isLocOp_of_isLocal_fin | exact GlobalTheory.PlaceTensorFin.isLocOp_of_isLocal_fin | (intros; apply GlobalTheory.PlaceTensorFin.isLocOp_of_isLocal_fin <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorUpdateFactorFromBaseVector

section

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorStep

theorem wAt_wAt_ne {D : D7} {m n : ℕ} {p q : Place D} (h : p ≠ q) (w : Mx D m n) : wAt p (wAt q w) = 0 := by
  have h0 : idem D p * idem D q = 0 := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q h
  funext i j
  show idem D p * (idem D q * w i j) = (0 : Mx D m n) i j
  rw [← mul_assoc, h0, zero_mul]
  rfl

theorem wAt_wAt_self {D : D7} {m n : ℕ} (p : Place D) (w : Mx D m n) : wAt p (wAt p w) = wAt p w := by
  have h1 : idem D p * idem D p = idem D p := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p
  funext i j
  show idem D p * (idem D p * w i j) = idem D p * w i j
  rw [← mul_assoc, h1]

theorem change_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (q : Place D), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → x q = f₀ → (∀ p, p ≠ q → x' p = x p) → IsLocal ψ θ S T sS sT ΛS ΛT q (x' q) → ∃ f', IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' f' ∧ ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → (∀ w : WO S T, ipO μ 𝓕 (heisO ψ S T (wAt q w) f) g = c * ipO μ 𝓕 (heisO ψ S T (wAt q w) f₀) g') → ipO μ 𝓕 f' g = c * ipO μ 𝓕 (x' q) g' := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x x' f q hf hxq hx' hloc

  have hop : IsLocOp ψ S T μ 𝓕 f₀ q (x' q) := by
    rcases q with v | τ
    · exact GlobalTheory.T.local_factor_finite_place_heisenberg_sum_base_vector D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v _ hloc
    · exact GlobalTheory.T.localFactorRealPlace_eq_heisenbergIntegral_base D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ τ _ hloc
  obtain ⟨L, hL, himg, hx'L⟩ := hop
  have hfpure := hf
  obtain ⟨hres, hfth, hprod⟩ := hf

  obtain ⟨f', hf'th, hf'⟩ := himg f hfth
  have hstd := GlobalTheory.PlaceTensor.base_std hB
  have hlaws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T
  have hthw : ∀ u, IsThetaFunO ψ S T (heisO ψ S T u f₀) := fun u => hlaws.1 u f₀ (GlobalTheory.PlaceTensor.base_theta hB)
  refine ⟨f', ⟨⟨?_, ?_⟩, hf'th, ?_⟩, ?_⟩
  · intro p
    by_cases hp : p = q
    · subst hp; exact hloc
    · rw [hx' p hp]; exact hres.1 p
  · refine (hres.2.union (Set.finite_singleton q)).subset ?_
    intro p hp
    by_cases hpq : p = q
    · exact Or.inr hpq
    · left
      have hp' : x' p ≠ f₀ := hp
      rw [hx' p hpq] at hp'
      exact hp'
  · intro w
    have hfin := (hprod w).1
    have hsupp : (Function.mulSupport fun p => ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)).Finite := by
      refine (hfin.union (Set.finite_singleton q)).subset ?_
      intro p hp
      by_cases hpq : p = q
      · exact Or.inr hpq
      · left
        rw [Function.mem_mulSupport] at hp ⊢
        rw [hx' p hpq] at hp
        exact hp
    refine ⟨hsupp, ?_⟩

    have hrest : (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)) =
        ∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀) :=
      finprod_congr fun p => finprod_congr fun hp => by rw [hx' p hp]

    have key : ∀ u, ipO μ 𝓕 (heisO ψ S T (wAt q u) f) (heisO ψ S T w f₀) =
        (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) *
          ipO μ 𝓕 (heisO ψ S T (wAt q u) f₀) (heisO ψ S T (wAt q w) f₀) := by
      intro u
      obtain ⟨-, -, hpu⟩ := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hfpure (wAt q u)
      obtain ⟨hfinu, hequ⟩ := hpu w
      rw [hequ, ← mul_finprod_cond_ne q hfinu]
      dsimp only
      rw [hxq, wAt_wAt_self, mul_comm]
      congr 1
      exact finprod_congr fun p => finprod_congr fun hp => by rw [wAt_wAt_ne hp, WeilVacMove.heisO_zero]
    rw [← mul_finprod_cond_ne q hsupp, hrest, hf' _ (hthw w)]
    simp_rw [key]
    rw [hL, hx'L _ (hthw _), mul_comm]
  · intro g g' c hg hg' hcoef
    rw [hf' g hg, hx'L g' hg']
    simp_rw [hcoef]
    exact hL c _

end GlobalTheory.PlaceTensorStep

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorUpdateFactorFromBaseVectorStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.pureTensor_update_factor_from_base_vector : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (q : Place D), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → x q = f₀ → (∀ p, p ≠ q → x' p = x p) → IsLocal ψ θ S T sS sT ΛS ΛT q (x' q) → ∃ f', IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' f' ∧ ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → (∀ w : WO S T, ipO μ 𝓕 (heisO ψ S T (wAt q w) f) g = c * ipO μ 𝓕 (heisO ψ S T (wAt q w) f₀) g') → ipO μ 𝓕 f' g = c * ipO μ 𝓕 (x' q) g' := by
  first | exact @GlobalTheory.PlaceTensorStep.change_factor | exact GlobalTheory.PlaceTensorStep.change_factor | (intros; apply GlobalTheory.PlaceTensorStep.change_factor <;> assumption)
end
end
