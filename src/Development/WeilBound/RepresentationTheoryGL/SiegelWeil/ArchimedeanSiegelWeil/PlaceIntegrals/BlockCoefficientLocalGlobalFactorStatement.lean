module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsBlockNFZeroOne
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.IsSchwartzBruhatOfProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSiegelWeilMeasureStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EulerProductAlmostAllStandardStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasuresStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorizableSiegelWeilFiniteSetStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSiegelWeilUnramifiedMeasureStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFactorizableDecomposition
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.BigCellDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzFunctionSchwartzBruhatStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilConvergentRangeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilOrbitalIntegralFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramNear
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasurableSetIntF
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.ReduceModChar
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.EulerFactorStandardMeasureIdentityStatement
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.AdelicSiegelWeilCoefficientEqStatement
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFactorizableDecompositionStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.schwartz_bruhat_factorizable_decomposition : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ → ∃ (k : ℕ) (φ : Fin k → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin k → (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.schwartzBruhat_eq_sum_pureN | exact GlobalTheory.CompanionTheory.WhitFree.schwartzBruhat_eq_sum_pureN | (intros; apply GlobalTheory.CompanionTheory.WhitFree.schwartzBruhat_eq_sum_pureN <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilOrbitalIntegralFormulaStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.siegel_weil_orbital_integral_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (T : Matrix (Fin n) (Fin n) E) (k : ℕ) (Φ : Fin k → (Fin n → Fin M → AF F ⊗[F] E) → ℂ), (∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (Φ i)) → coefN σ J ψ dx db (fun X => ∑ i, Φ i X) T = ∑ i, coefN σ J ψ dx db (Φ i) T := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.CoefSum.coefN_finset_sum | exact GlobalTheory.CompanionTheory.SiegelND.CoefSum.coefN_finset_sum | (intros; apply GlobalTheory.CompanionTheory.SiegelND.CoefSum.coefN_finset_sum <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilStabilizerIntegrable

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain
open scoped HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.CompanionTheory.WhitFree.CoefLim

theorem repr_map {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (f : A →ₐ[F] B) {d : ℕ} (b : Module.Basis (Fin d) F E) (y : A ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis A b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_linear (L : (R ⊗[F] E) →ₗ[R] R) : Continuous L := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap L

theorem continuous_entry (σ : E →ₐ[F] E) {n : ℕ} (a c : Fin n) :
    Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => (B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a c :=
  (continuous_id.matrix_elem a c).comp continuous_subtype_val

theorem continuous_trace_pair [FiniteDimensional F E] (σ : E →ₐ[F] E) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => Algebra.trace R (R ⊗[F] E)
      (Matrix.trace (T * (B : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) := by
  have h : (fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => Algebra.trace R (R ⊗[F] E)
      (Matrix.trace (T * (B : Matrix (Fin n) (Fin n) (R ⊗[F] E))))) =
      fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => ∑ a, ∑ c, (Algebra.trace R (R ⊗[F] E) ∘ₗ LinearMap.mulLeft R (T a c))
        ((B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) c a) := by
    funext B

    simp [Matrix.trace, Matrix.mul_apply, map_sum]
  rw [h]
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ =>
    (continuous_linear _).comp (continuous_entry σ c a)

end Cont

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mem_intH_iff (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) :
    B ∈ intH σ b S ↔ ∀ v, v ∉ S → ∀ a i k, (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
      ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (a i : Fin n) (k : Fin d),
      (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).repr
        (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin (fun a i => (B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i)) a i) k =
      (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v := by
    intro v a i k
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.projV, HeckeCharacterZeroLocus.SiegelWeilU.projFin]
    rw [repr_map, repr_map]
    rfl
  simp only [intH, HeckeCharacterZeroLocus.SiegelWeilU.latV, Set.mem_setOf_eq, key]

theorem measurableSet_intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (intH (n := n) σ b S) := by
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have hset : intH (n := n) σ b S = ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ _ : v ∉ S, ⋂ a : Fin n, ⋂ i : Fin n,
      ⋂ k : Fin d, {B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n | (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F} := by
    ext B
    simp only [mem_intH_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun a =>
    MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_
  have hO : IsOpen (v.adicCompletionIntegers F : Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)) := Valued.isOpen_valuationSubring _
  have hev : Continuous fun y : HeckeCharacterZeroLocus.SiegelWeilU.Af F => y v := RestrictedProduct.continuous_eval v
  have hsnd : Continuous (fun c : HeckeCharacterZeroLocus.SiegelWeilU.AF F => HeckeCharacterZeroLocus.SiegelWeilU.sndA F c) := continuous_snd
  have hc : Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n => (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
      ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v :=
    hev.comp (hsnd.comp ((continuous_linear (Finsupp.lapply k ∘ₗ
      (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr.toLinearMap)).comp (continuous_entry σ a i)))
  exact (hO.preimage hc).measurableSet

theorem eventually_mem_intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E) (B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in Filter.atTop, B ∈ intH σ b S := by
  have hfin : ∀ (a i : Fin n) (k : Fin d), {v : HeightOneSpectrum (𝓞 F) |
      ¬ (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F}.Finite :=
    fun a i k => (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)).2
  have hall : ∀ (a i : Fin n) (k : Fin d), ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in Filter.atTop,
      ∀ v, v ∉ S → (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F := by
    intro a i k
    filter_upwards [Filter.eventually_ge_atTop (hfin a i k).toFinset] with S hS v hv
    by_contra hcon
    exact hv (hS ((hfin a i k).mem_toFinset.2 hcon))
  have hall' := Filter.eventually_all.2 fun a : Fin n => Filter.eventually_all.2 fun i : Fin n =>
    Filter.eventually_all.2 fun k : Fin d => hall a i k
  filter_upwards [hall'] with S hS
  exact (mem_intH_iff σ b S B).2 fun v hv a i k => hS a i k v hv

end Adelic

theorem coefS_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ T : Matrix (Fin n) (Fin n) E, Filter.Tendsto (fun S => coefS σ J ψ dx db Φ T b S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ ψ hψ dx db d b Φ hI T
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  have hchar : Continuous fun B : HermR (AF F) σ n =>
      ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace (T.map (inclR (AF F)) * (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) :=
    hψc.comp ((continuous_const.mul (continuous_trace_pair σ _)).neg)
  have hf := hI.aestronglyMeasurable.mul hchar.aestronglyMeasurable
  unfold coefS coefN
  refine tendsto_integral_filter_of_dominated_convergence (fun B => ‖starN σ J ψ dx Φ B‖) ?_ ?_ hI.norm ?_
  · refine Filter.Eventually.of_forall fun S => ?_
    have hind : Measurable ((intH (n := n) σ b S).indicator (fun _ => (1 : ℂ))) :=
      measurable_const.indicator (measurableSet_intH σ b S)
    exact hind.aestronglyMeasurable.mul hf
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun B => ?_
    have h1 : ‖(intH (n := n) σ b S).indicator (fun _ => (1 : ℂ)) B‖ ≤ 1 := by
      by_cases h : B ∈ intH (n := n) σ b S <;> simp [h]
    rw [norm_mul, norm_mul, hψn, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · refine Filter.Eventually.of_forall fun B => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_intH σ b B] with S hS
    simp only [Set.indicator_of_mem hS, one_mul]
    rfl

end GlobalTheory.CompanionTheory.WhitFree.CoefLim
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilStabilizerIntegrableStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.siegel_weil_stabilizer_integrable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ T : Matrix (Fin n) (Fin n) E, Filter.Tendsto (fun S => coefS σ J ψ dx db Φ T b S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.CoefLim.coefS_tendsto | exact GlobalTheory.CompanionTheory.WhitFree.CoefLim.coefS_tendsto | (intros; apply GlobalTheory.CompanionTheory.WhitFree.CoefLim.coefS_tendsto <;> assumption)
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.BlockCoefficientLocalGlobalFactor

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.WhitFree

theorem pure_identity {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (hn : 0 < n) (hM : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v))
    (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf) (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HermR (Fv F v) σ n →
      Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hI : GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)))
    (S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (hφ : GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ)
    (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v)) (hAl : ∀ v, v ∉ S₀ → A v = latV b v) :
    Integrable (pureN φ A) I ∧ coefN σ J ψ dx db (pureN φ A) T = ∫ X, pureN φ A X ∂I := by
  classical
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.euler_product_almost_all_standard F E M n d b I 1 _ _ hI
  obtain ⟨S₂, hS₂⟩ := GlobalTheory.T.adelic_siegelWeil_coefficient_eq F E σ hCM M J hJ n hn hM ψ hψ dx hdx db hdb d b laminf lam hinf hlam minf hminf m hm T hT
  obtain ⟨hφm, hφi, -⟩ := GlobalTheory.T.archimedean_siegel_weil_measure F E σ hCM M J hJ n hn hM d b laminf hinf minf hminf (hermOf (Ainf F) σ T hT) φ hφ
  have hfin := fun v => GlobalTheory.T.local_siegel_weil_unramified_measure F E σ hCM M J hJ n hn hM d b v (lam v) (hlam v) (m v) (hm v)
    (hermOf (Fv F v) σ T hT) (A v) (hA v).1 (hA v).2
  have hΦSB : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A) :=
    GlobalTheory.T.factorizable_siegel_weil_finite_set F E σ hCM M J hJ n hn hM d b S₀ φ A hφ hA hAl
  have hstar : Integrable (starN σ J ψ dx (pureN φ A)) db :=
    GlobalTheory.T.siegel_weil_convergent_range F E σ hCM M J hJ n hM ψ hψ dx hdx db hdb _ hΦSB
  have hlimC := GlobalTheory.T.siegel_weil_stabilizer_integrable F E σ hCM M J hJ n hn hM ψ hψ dx db d b _ hstar T
  have htail := GlobalTheory.T.tendsto_tail_infinite_product_one _ hI.2.1
  have hev : ∀ᶠ S in Filter.atTop, S₀ ∪ S₁ ∪ S₂ ⊆ S := Filter.eventually_ge_atTop _
  obtain ⟨Sb, hSb⟩ : ∃ S, S₀ ∪ S₁ ∪ S₂ ⊆ S := ⟨_, subset_rfl⟩
  have hEu : ∀ S, S₀ ∪ S₁ ∪ S₂ ⊆ S → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = ((1 : NNReal) : ℂ) * (∫ X, φ X ∂(minf (hermOf (Ainf F) σ T hT))) *
      (∏ v ∈ S, ((m v (hermOf (Fv F v) σ T hT) (A v)).toReal : ℂ)) *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ) := by
    intro S hS
    have hs0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
    have hs1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
    exact hS₁ S hs1 φ hφm hφi A (fun v => (hfin v).1) (fun v => (hfin v).2.1)
      (fun v hv => hAl v fun h => hv (hs0 h))
  refine ⟨(hEu Sb hSb).1, ?_⟩
  have hlim2 : Filter.Tendsto (fun S => coefS σ J ψ dx db (pureN φ A) T b S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ))
      Filter.atTop (nhds (coefN σ J ψ dx db (pureN φ A) T * ((1 : ℝ) : ℂ))) :=
    hlimC.mul ((Complex.continuous_ofReal.tendsto _).comp htail)
  have hconst : ∀ᶠ S in Filter.atTop, coefS σ J ψ dx db (pureN φ A) T b S *
      ((∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal : ℝ) : ℂ) =
      ∫ X, pureN φ A X ∂I := by
    filter_upwards [hev] with S hS
    have hs0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
    have hs2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
    rw [hS₂ S hs2 φ hφ A hA (fun v hv => hAl v fun h => hv (hs0 h)), (hEu S hS).2]
    simp
  have := tendsto_nhds_unique (hlim2.congr' hconst) tendsto_const_nhds
  simpa using this

theorem coefN_eq_integral {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {n : ℕ} (hn : 0 < n) (hM : 2 * n < M) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ)
    (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hdx : SdW F E σ M J (AF F) ψ n dx)
    (db : Measure (HermR (AF F) σ n)) (hdb : SdHerm F E σ (AF F) ψ n db)
    (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F))
    (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v))
    (hinf : GlobalTheory.CompanionTheory.SW.IsStdInf laminf) (hlam : ∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v))
    (minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E))
    (hminf : IsGramFibFree (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf)
    (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), HermR (Fv F v) σ n →
      Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hm : ∀ v, IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b (lam v) n M)
      (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n) (m v))
    (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c)
    (I : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hI : GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (hermOf (Ainf F) σ T hT)) (fun v => m v (hermOf (Fv F v) σ T hT)))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ) :
    coefN σ J ψ dx db Φ T = ∫ X, Φ X ∂I := by
  obtain ⟨k, φ, A, S, hφ, hA, hAl, hsum⟩ := GlobalTheory.T.schwartz_bruhat_factorizable_decomposition F E σ hCM M J hJ n hn hM d b Φ hΦ
  have hSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN (φ i) (A i)) := fun i =>
    GlobalTheory.T.factorizable_siegel_weil_finite_set F E σ hCM M J hJ n hn hM d b S (φ i) (A i) (hφ i) (hA i) (hAl i)
  have hP := fun i => pure_identity σ hCM J hJ hn hM ψ hψ dx hdx db hdb d b laminf lam hinf hlam minf hminf m hm T hT I hI S
    (φ i) (hφ i) (A i) (hA i) (hAl i)
  have hΦe : Φ = fun X => ∑ i, pureN (φ i) (A i) X := funext hsum
  rw [hΦe, GlobalTheory.T.siegel_weil_orbital_integral_formula F E σ hCM M J hJ n hn hM ψ hψ dx hdx db hdb T k _ hSB, integral_finsetSum _ fun i _ => (hP i).1]
  exact Finset.sum_congr rfl fun i _ => (hP i).2

end GlobalTheory.CompanionTheory.WhitFree

namespace GlobalTheory.CompanionTheory.WhitFree

theorem whit_eq_integral : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → ∀ (d : ℕ) (b : Module.Basis (Fin d) D.host.F D.host.E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F)) (lamv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F ⊗[D.host.F] D.host.E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lamv v)) → IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) b laminf r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig b laminf r) minf → (∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) b (lamv v) r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig b (lamv v) r) (m v)) → ∀ I : Measure (Fin r → Fin V.rank → AE D), GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig β.1 (hermE_symm β))) (fun v => m v (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig β.1 (hermE_symm β))) → Integrable (fun X => φ (trM X)) I → W ψ V μ lam φ β = ∫ X, φ (trM X) ∂I := by
  intro D r V ψ θ μ lam ν φ hyp t β hβ d b laminf lamv minf m hinf hlamv hminf hm I hI _
  obtain ⟨hr, hψ, hθ, hμ, hlam, -, hφ, -⟩ := hyp
  have hCM := GlobalTheory.DefiniteQuotient.cmExt D
  have hJ := GlobalTheory.DefiniteQuotient.gram_hermND V
  obtain ⟨dx, db, hdx, hdb, hW⟩ := GlobalTheory.T.exists_self_dual_siegel_weil_measures D r V ψ hψ μ hμ lam hlam
  obtain ⟨ht, -⟩ := hβ
  rw [hW φ β]
  exact coefN_eq_integral D.sp.cm.sig hCM V.gram hJ (by omega) hr ψ hψ dx hdx db hdb d b laminf lamv hinf hlamv minf hminf
    m hm β.1 (hermE_symm β) I hI _ (GlobalTheory.T.schwartz_function_schwartz_bruhat D θ hθ V.rank r φ hφ)

end GlobalTheory.CompanionTheory.WhitFree
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.SiegelWeil.ArchimedeanSiegelWeil.PlaceIntegrals.BlockCoefficientLocalGlobalFactorStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.block_coefficient_local_global_factor : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ), Hyp D r V ψ θ μ lam ν φ → ∀ (t : ℕ) (β : HermE D r), GlobalTheory.CompanionTheory.WeilSiegel.Deg.IsBlockNF t β → ∀ (d : ℕ) (b : Module.Basis (Fin d) D.host.F D.host.E) (laminf : Measure (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F)) (lamv : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), Measure (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v)) (minf : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F ⊗[D.host.F] D.host.E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F), HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig r → Measure (Fin r → Fin V.rank → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lamv v)) → IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) b laminf r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig b laminf r) minf → (∀ v, IsGramFibFree (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig V.gram r (GlobalTheory.CompanionTheory.SW.coordW (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) b (lamv v) r V.rank) (GlobalTheory.CompanionTheory.SW.coordHerm (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig b (lamv v) r) (m v)) → ∀ I : Measure (Fin r → Fin V.rank → AE D), GlobalTheory.CompanionTheory.SW.IsEulerProd b I 1 (minf (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Ainf D.host.F) D.sp.cm.sig β.1 (hermE_symm β))) (fun v => m v (HeckeCharacterZeroLocus.SiegelWeilU.hermOf (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v) D.sp.cm.sig β.1 (hermE_symm β))) → Integrable (fun X => φ (trM X)) I → W ψ V μ lam φ β = ∫ X, φ (trM X) ∂I := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.whit_eq_integral | exact GlobalTheory.CompanionTheory.WhitFree.whit_eq_integral
end
end
