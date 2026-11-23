module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowStmt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIntAddConjEqOneOfBaseGoodKAlt
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.EventuallySelfDualLatticeIndicatorIsVacuum
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
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsIsVacAnyDarbouxK
public import Development.WeilBound.ThetaLifts.TowerModels.TwistedSums.ExistsRationalDarbouxHermitianTensorAdeles
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
public import Development.WeilBound.ThetaLifts.TowerModels.DetHerm
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.EventuallyIsVacIndicatorK

section

@[expose] public section



section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AdelicU GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F : Type} [Field F] [NumberField F]
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F : Type} [Field F] [NumberField F]
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F : Type} [Field F] [NumberField F]
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F : Type} [Field F] [NumberField F]
section AtLemmas
variable {v : HeightOneSpectrum (𝓞 F)}
end AtLemmas
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n d : ℕ}
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
section SympAdd
variable {R E' : Type} [CommRing R] [CommRing E'] [Algebra R E'] (c : E' →ₐ[R] E') (ξ : E')
  {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α E') (JB : Matrix β β E')
end SympAdd
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {n d : ℕ}
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem isVac_indicator_of_theta_k {σ : E →ₐ[F] E} (B : Base F E) (hB : _root_.UpperTheory.TP.W.GoodK σ B) {n d : ℕ} (X : Spc F E n)
    (Y : Spc F E d) (r s r' s' : ℕ) (hX : X.IsHerm σ B r s) (hY : Y.IsSkew σ B r' s')
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d))
    (hrat : ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)))
    (hθ : ∃ θ : 𝓞 E, (θ : E) + σ θ = 1) :
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  classical
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨G, hG⟩ := exists_gen X.L Y.L hX.lat.toIsLattice hY.lat.toIsLattice
  choose yc zc hc using hrat
  have e1 := eventually_psiLoc_eq_one B.ψ hB.std.1
  have e2 := eventually_int (F := F) (1 / 2)
  have e3 : ∀ᶠ v in cofinite, ∀ g ∈ G, ∀ k, algebraMap F (Fv F v) (yc g k) ∈ v.adicCompletionIntegers F ∧
      algebraMap F (Fv F v) (zc g k) ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all_finset G).2 fun g _ => Filter.eventually_all.2 fun k => ?_
    exact (eventually_int (yc g k)).and (eventually_int (zc g k))
  have e4 : ∀ᶠ v in cofinite, ∀ g ∈ G, ∀ g' ∈ G,
      algebraMap F (Fv F v) (symp σ (θ : E) X.J Y.J g g') ∈ v.adicCompletionIntegers F := by
    refine (Filter.eventually_all_finset G).2 fun g _ => (Filter.eventually_all_finset G).2 fun g' _ => ?_
    exact eventually_int _
  filter_upwards [e1, e2, e3, e4] with v h1 h2 h3 h4
  set O := v.adicCompletionIntegers F
  set T : Set (Matrix (Fin n) (Fin d) (AE F E)) :=
    {z | ∃ a : AF F, At (evFin F v) a ∧ evFin F v a ∈ O ∧ ∃ g ∈ G, z = a • incM F g} with hT
  have hA : ∀ z ∈ AddSubgroup.closure T, ∀ k, At (evFin F v) ((co.e z).1 k) ∧ At (evFin F v) ((co.e z).2 k) ∧
      evFin F v ((co.e z).1 k) ∈ O ∧ evFin F v ((co.e z).2 k) ∈ O := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hai, g, hg, rfl⟩ := hz
      intro k
      rw [map_smul, hc g]
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, evFin_algebraMap]
      exact ⟨at_mul_right ha, at_mul_right ha, mul_mem hai (h3 g hg k).1, mul_mem hai (h3 g hg k).2⟩
    | zero =>
      intro k
      simp only [map_zero, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply]
      exact ⟨at_zero, at_zero, zero_mem _, zero_mem _⟩
    | add z z' _ _ h h' =>
      intro k
      simp only [map_add (f := _), Prod.fst_add, Prod.snd_add, Pi.add_apply]
      exact ⟨at_add (h k).1 (h' k).1, at_add (h k).2.1 (h' k).2.1, add_mem (h k).2.2.1 (h' k).2.2.1,
        add_mem (h k).2.2.2 (h' k).2.2.2⟩
    | neg z _ h =>
      intro k
      simp only [map_neg, Prod.fst_neg, Prod.snd_neg, Pi.neg_apply]
      exact ⟨at_neg (h k).1, at_neg (h k).2.1, neg_mem (h k).2.2.1, neg_mem (h k).2.2.2⟩
  set S := symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F Y.J) with hS
  have hB1 : ∀ z ∈ T, ∀ z' ∈ AddSubgroup.closure T, At (evFin F v) (S z z') ∧ evFin F v (S z z') ∈ O := by
    intro z hz z' hz'
    obtain ⟨a, ha, hai, g, hg, rfl⟩ := hz
    induction hz' using AddSubgroup.closure_induction with
    | mem z' hz' =>
      obtain ⟨a', ha', hai', g', hg', rfl⟩ := hz'
      rw [hS, symp_smul_incM, map_mul, map_mul, evFin_algebraMap]
      exact ⟨at_mul_right (at_mul_right ha), mul_mem (mul_mem hai hai') (h4 g hg g' hg')⟩
    | zero => rw [hS, symp_zero_right, map_zero]; exact ⟨at_zero, zero_mem _⟩
    | add z₁ z₂ _ _ h h' => rw [hS, symp_add_right, map_add (f := _)]; exact ⟨at_add h.1 h'.1, add_mem h.2 h'.2⟩
    | neg z₁ _ h => rw [hS, symp_neg_right, map_neg]; exact ⟨at_neg h.1, neg_mem h.2⟩
  have hB2 : ∀ z ∈ AddSubgroup.closure T, ∀ z' ∈ AddSubgroup.closure T,
      At (evFin F v) (S z z') ∧ evFin F v (S z z') ∈ O := by
    intro z hz z' hz'
    induction hz using AddSubgroup.closure_induction with
    | mem z hz => exact hB1 z hz z' hz'
    | zero => rw [hS, symp_zero_left, map_zero]; exact ⟨at_zero, zero_mem _⟩
    | add z₁ z₂ _ _ h h' => rw [hS, symp_add_left, map_add (f := _)]; exact ⟨at_add h.1 h'.1, add_mem h.2 h'.2⟩
    | neg z₁ _ h => rw [hS, symp_neg_left, map_neg]; exact ⟨at_neg h.1, neg_mem h.2⟩
  refine ⟨indicator_int_mem_SB v, indicator_int_ne_zero v, θ, hθ, fun γ hγ => ?_⟩
  have hγ' := latAtV_le X Y G hG v hγ
  have hval : B.ψ (⅟(2 : AF F) * S γ γ) = 1 := by
    have hat := hB2 γ hγ' γ hγ'
    rw [psi_of_at B.ψ (at_mul_left hat.1)]
    refine h1 _ ?_
    rw [map_mul, invOf_two_eq, evFin_algebraMap]
    exact mul_mem h2 hat.2
  rw [← hS, hval, one_smul]
  exact acts_indicator co B.ψ v γ h1 h2 (fun k => (hA γ hγ' k).1) (fun k => (hA γ hγ' k).2.1)
    (fun k => (hA γ hγ' k).2.2.1) (fun k => (hA γ hγ' k).2.2.2)
end Tw.VacIndic
namespace Tw.VacIndic
open _root_.GlobalTheory
theorem eventually_isVac_indicator_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ᶠ v in Filter.cofinite, Model.IsVac (Model.mk (σ := σ) (X := X) (W := Y) co (fun _ => 0) 0 ∅) B.ψ v
      (Set.indicator {x | ∀ k, x k ∈ v.adicCompletionIntegers F} 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY co hrat
  exact _root_.Tw.VacIndic.isVac_indicator_of_theta_k B hB X Y r s r' s' hX hY co hrat (_root_.Tw.exists_int_add_conj_eq_one_of_base_good_k B hB)
end Tw.VacIndic
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsRationalDarbouxK

section

@[expose] public section



section
noncomputable section
namespace Tw.RatDarboux
open _root_.GlobalTheory
section General
open scoped TensorProduct
open Matrix Module GlobalTheory.WeilM
variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R]
end General
end Tw.RatDarboux
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory in
theorem Tw.RatDarboux.exists_rational_darboux_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), _root_.UpperTheory.TP.W.GoodK σ B → X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d),
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hB hX hY
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hX' : X.J.det ≠ 0 := fun h0 => by
    apply Tw.RatDarboux.det_ne_zero_of_isCartan (hX.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det X.J
    rw [h0, map_zero] at this
    exact this.symm
  have hY' : Y.J.det ≠ 0 := fun h0 => by
    apply Tw.RatDarboux.det_ne_zero_of_isCartan (hY.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det Y.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  exact Tw.RatDarboux.exists_darboux (AF F) hB.cm.2.2.1 σ hσ hX.herm hY.skew hX' hY'
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ExistsRationalDarbouxOfIsGoodK

section

@[expose] public section



section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem Tw.RatDarboux.exists_rational_darboux_of_isGood_k : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E), _root_.UpperTheory.TP.W.GoodK σ B → ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∃ co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (R := AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (-1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F X.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F Y.J)) (Fin n × Fin d), ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k)) :=
  fun B hB _ _ X Y r s r' s' hX hY => _root_.Tw.RatDarboux.exists_rational_darboux_k _ B X Y r s r' s' hB hX hY
end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowModel

section

@[expose] public section



section
noncomputable section
namespace PositivityTheory.ThKG.Tow
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem modelEx_k : _root_.PositivityTheory.ThKG.Tow.ModelEx_k := by
  intro F E _ _ _ _ _ σ B hB n d X W r s r' s' hX hW
  classical
  obtain ⟨co, hco⟩ := _root_.Tw.RatDarboux.exists_rational_darboux_of_isGood_k B hB X W r s r' s' hX hW
  obtain ⟨-, ⟨μ, 𝓕, hμ, h𝓕⟩, -⟩ := PositivityTheory.ThKF.unimodularity_holds F E σ hB.cm n X.J 1 (by simpa using hX.herm) (det_herm hX)
  have hS := _root_.Tw.VacIndic.eventually_isVac_indicator_k B hB X W r s r' s' hX hW co hco
  have hA := _root_.Tw.VacAny.exists_isVac_any_darboux_k B hB X W r s r' s' hX hW co
  let M₀ : Model σ X W := ⟨co, fun _ => 0, 0, ∅⟩
  let ind : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
  let vac : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v =>
    if M₀.IsVac B.ψ v (ind v) then ind v else (hA v).choose
  refine ⟨⟨co, vac, μ, 𝓕⟩, ⟨hco, fun v => ?_, ?_, hμ, h𝓕⟩⟩
  · show M₀.IsVac B.ψ v (vac v)
    by_cases h : M₀.IsVac B.ψ v (ind v)
    · simp only [vac, if_pos h]; exact h
    · simp only [vac, if_neg h]; exact (hA v).choose_spec
  · filter_upwards [hS] with v hv
    show vac v = ind v
    exact if_pos hv
end PositivityTheory.ThKG.Tow
end
end
end
end
