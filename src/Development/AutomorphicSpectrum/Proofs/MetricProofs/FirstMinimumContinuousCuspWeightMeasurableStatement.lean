module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousFirstMinimumFamilyStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousHermitianMatrixFamilyStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderIsometryStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBoundsStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndAction
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousCuspNormFamily

section

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.NzCont

section Emb

variable {E : Type} [Field E] [NumberField E]

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s := by
  have hc : (RingHom.ker s).comap (algebraMap ℤ (𝓞 E)) = ⊥ := by
    rw [RingHom.comap_ker]
    exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int _)
  exact (RingHom.injective_iff_ker_eq_bot s).2 (Ideal.eq_bot_of_comap_eq_bot hc)

def extEmb (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (emb_injective s)

theorem extEmb_apply (s : 𝓞 E →+* ℂ) (a : 𝓞 E) : extEmb s (algebraMap (𝓞 E) E a) = s a :=
  IsFractionRing.lift_algebraMap (emb_injective s) a

theorem extEmb_comp (s : 𝓞 E →+* ℂ) : (extEmb s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext (extEmb_apply s)

def charVec (a : 𝓞 E) : (E →+* ℂ) → ℂ := fun s => s (algebraMap (𝓞 E) E a)

def toChar (s : E →+* ℂ) : 𝓞 E →* ℂ := (s.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ)

theorem toChar_injective : Function.Injective (toChar (E := E)) := by
  intro s s' h
  refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => ?_)
  exact DFunLike.congr_fun h a

theorem span_charVec : Submodule.span ℂ (Set.range (charVec (E := E))) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
  apply hf0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ (toChar_injective (E := E))
  rw [Fintype.linearIndependent_iff] at li
  have hl := li (fun s => f fun j => if s = j then 1 else 0) (by
    funext a
    have h1 : f (charVec a) = 0 := hf (Submodule.subset_span ⟨a, rfl⟩)
    rw [LinearMap.pi_apply_eq_sum_univ] at h1
    simp only [Finset.sum_apply, Pi.smul_apply, Function.comp, smul_eq_mul, Pi.zero_apply]
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_eq_mul]
    exact mul_comm (_ : ℂ) _)
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.pi_apply_eq_sum_univ f v, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun s _ => (congrArg (v s • ·) (hl s)).trans (smul_zero _)


open Classical in
theorem exists_coeff (s : E →+* ℂ) : ∃ c : 𝓞 E →₀ ℂ, ∀ s' : E →+* ℂ,
    ∑ a ∈ c.support, c a * s' (algebraMap (𝓞 E) E a) = if s' = s then 1 else 0 := by
  have h : (Pi.single s 1 : (E →+* ℂ) → ℂ) ∈ Submodule.span ℂ (Set.range (charVec (E := E))) := by
    rw [span_charVec]
    trivial
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h
  refine ⟨c, fun s' => ?_⟩
  have h2 := congrFun hc s'
  simpa [Finsupp.sum, Finset.sum_apply, charVec, Pi.single_apply] using h2

end Emb

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

theorem mem_eigSp_iff (R : RiemLat E g Λ) {s : 𝓞 E →+* ℂ} {x : Fin g → ℂ} :
    x ∈ eigSp R.B s ↔ ∀ a, R.B a x = s a • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]


open Classical in
theorem eigComp_eq (R : RiemLat E g Λ) (s : E →+* ℂ) (c : 𝓞 E →₀ ℂ)
    (hc : ∀ s' : E →+* ℂ, ∑ a ∈ c.support, c a * s' (algebraMap (𝓞 E) E a) = if s' = s then 1 else 0)
    (u : Λ) :
    eigComp R.B (s.comp (algebraMap (𝓞 E) E)) (R.P u) = ∑ a ∈ c.support, c a • R.P (a • u) := by
  obtain ⟨-, -, h3, h4, -⟩ := GlobalTheory.T.riemann_lattice_eigen_projection E g Λ Unit R
  have hy : ∀ a : 𝓞 E, R.P (a • u) = ∑ s' : E →+* ℂ, s' (algebraMap (𝓞 E) E a) •
      eigComp R.B (s'.comp (algebraMap (𝓞 E) E)) (R.P u) := by
    intro a
    rw [R.act]
    conv_lhs => rw [← h4 (R.P u)]

    rw [map_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    exact (mem_eigSp_iff R).1 ((h3 _).1 _) a
  simp_rw [hy, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hc]
  simp [ite_smul]

variable {X : Type} [TopologicalSpace X]

theorem continuous_eigComp (R : X → RiemLat E g Λ) (hP : ∀ v, Continuous fun x => (R x).P v)
    (s : 𝓞 E →+* ℂ) (u : Λ) : Continuous fun x => eigComp (R x).B s ((R x).P u) := by
  classical
  obtain ⟨c, hc⟩ := exists_coeff (extEmb s)
  have h : ∀ x, eigComp (R x).B s ((R x).P u) = ∑ a ∈ c.support, c a • (R x).P (a • u) := by
    intro x
    have h1 := eigComp_eq (R x) (extEmb s) c hc u
    rwa [extEmb_comp] at h1
  simp_rw [h]
  exact continuous_finsetSum _ fun a _ => (hP (a • u)).const_smul (c a)

theorem continuous_ip (R : X → RiemLat E g Λ) (hH : Continuous fun x => (R x).Hm) {p q : X → Fin g → ℂ}
    (hp : Continuous p) (hq : Continuous q) : Continuous fun x => (R x).ip (p x) (q x) := by
  unfold RiemLat.ip
  exact hq.dotProduct (hH.matrix_mulVec (continuous_star.comp hp))

theorem continuous_nzOf {Ψ : Type} [Fintype Ψ] (R : X → RiemLat E g Λ)
    (hP : ∀ v, Continuous fun x => (R x).P v) (hH : Continuous fun x => (R x).Hm)
    (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ) {r : ℕ} (v : Fin r → Λ) :
    Continuous fun x => (R x).nzOf σ I v := by
  unfold RiemLat.nzOf
  refine Continuous.div_const (continuous_finsetProd _ fun τ _ => ?_) _
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine continuous_matrix fun a b => ?_
  exact continuous_ip R hH (continuous_eigComp R hP _ _) (continuous_eigComp R hP _ _)

theorem continuous_nz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ)
    (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), (∀ v, Continuous fun x => (R x).P v) →
    (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ I hP hH
  by_cases h : ∃ r v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsNzFamily I r v
  · have e : (fun x => (R x).nz σ I) = fun x => (R x).nzOf σ I h.choose_spec.choose := by
      funext x
      simp only [RiemLat.nz, dif_pos h]
    rw [e]
    exact continuous_nzOf R hP hH σ I _
  · have e : (fun x => (R x).nz σ I) = fun _ => 1 := by
      funext x
      simp only [RiemLat.nz, dif_neg h]
    rw [e]
    exact continuous_const

end GlobalTheory.CompanionTheory.Ar.Cusp.NzCont
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousCuspNormFamilyStatement

section

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.continuous_cusp_norm_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).nz σ I := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ I hP hH
  by_cases h : ∃ r v, GroundTheory.Heights₂.Heights.LowerBoundFree.IsNzFamily I r v
  · have hcont : Continuous fun x => (R x).nzOf σ I h.choose_spec.choose :=
      GlobalTheory.CompanionTheory.Ar.Cusp.NzCont.continuous_nzOf R hP hH σ I _
    simpa only [RiemLat.nz, dite_eq_left h] using hcont
  · simpa only [RiemLat.nz, dite_eq_right h] using
      (continuous_const : Continuous fun _ : X => (1 : ℝ))
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndActionStatement

section

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.isometry_preserves_hermitian_and_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (R R' : RiemLat E g Λ) (γ : Λ ≃ₗ[𝓞 E] Λ) (φ : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ x y, R'.form (γ x) (γ y) = R.form x y) → (∀ x, R'.P (γ x) = φ (R.P x)) → (∀ x y, R'.ip (φ x) (φ y) = R.ip x y) ∧ ∀ a x, φ (R.B a x) = R'.B a (φ x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes | exact GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.PeriodIso.isometry_and_commutes <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableCuspWeightFamilyStatement

section

@[expose] public section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

theorem _root_.GlobalTheory.T.measurable_cusp_weight_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [MeasurableSpace X] (R : X → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ), (∀ x, (R x).form = form) → (∀ I, Measurable fun x => (R x).nz σ I) → (∀ x, BddAbove {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)}) → Measurable fun x => (R x).cuspW σ := by
  intro E _ _ _ g Λ _ _ Ψ _ X _ R σ form hform hnz _
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · exact measurable_of_empty _
  have : Module.Free ℤ Λ := (R x₀).free
  have : Module.Finite ℤ Λ := (R x₀).fin
  have : Countable (Submodule (𝓞 E) Λ) := by
    have : Countable Λ :=
      (Module.finBasis ℤ Λ).equivFun.toEquiv.injective.countable
    have : Countable (Submodule ℤ Λ) := by
      have hspan : Function.Surjective (fun s : Finset Λ => Submodule.span ℤ (s : Set Λ)) := by
        intro N
        obtain ⟨s, hs⟩ := (IsNoetherian.noetherian N : N.FG)
        exact ⟨s, hs⟩
      exact hspan.countable
    exact (Submodule.restrictScalars_injective ℤ (𝓞 E) Λ).countable
  let C : Submodule (𝓞 E) Λ → Prop := fun I =>
    I ≠ ⊥ ∧ GroundTheory.Heights₂.Heights.LowerBoundFree.IsSaturated I ∧
      GroundTheory.Heights₂.Heights.LowerBoundFree.IsIsoSub form I
  have hC (x : X) (I : Submodule (𝓞 E) Λ) : (R x).IsCusp I ↔ C I := by
    simp only [RiemLat.IsCusp, C, hform x]
  have hset (x : X) : {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz σ I)} =
      Set.range fun I : {I // C I} => -Real.log ((R x).nz σ I.1) := by
    ext y
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨⟨I, (hC x I).1 hI⟩, rfl⟩
    · rintro ⟨I, rfl⟩
      exact ⟨I.1, (hC x I.1).2 I.2, rfl⟩
  have hsup : Measurable fun x => ⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1) :=
    Measurable.iSup fun I => (Real.measurable_log.comp (hnz I.1)).neg
  have heq : (fun x => (R x).cuspW σ) =
      fun x => max 0 (⨆ I : {I // C I}, -Real.log ((R x).nz σ I.1)) := by
    funext x
    simp only [RiemLat.cuspW, hset x, iSup]
  rw [heq]
  exact measurable_const.max hsup
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumContinuousCuspWeightMeasurable

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamilyMeas

theorem first_minimum_cusp_weight_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ), 1 ≤ j' → ContinuousOn (fun t => (F.R t).lam1) (ballDom F.q) ∧ Measurable ((ballDom F.q).indicator fun t => (F.R t).cuspW F.σ) ∧ IsOpen (ballDom F.q) ∧ ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → (F.R t).lam1 = (F.R t').lam1 ∧ (F.R t).cuspW F.σ = (F.R t').cuspW F.σ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F hj
  have hO : IsOpen (ballDom F.q) := BallInverse.isOpen_ballDom F.q
  let U := ↥(ballDom F.q)
  let R : U → RiemLat E g Λ := fun t => F.R t.1
  have hP : ∀ v, Continuous fun x : U => (R x).P v := fun v =>
    continuousOn_iff_continuous_restrict.1 (F.hol.2 v).continuousOn
  have hH : Continuous fun x : U => (R x).Hm := GlobalTheory.T.continuous_hermitian_matrix_family E g Λ U R F.form (fun x => F.form_eq _) hP
  have hlam : Continuous fun x : U => (R x).lam1 := GlobalTheory.T.continuous_first_minimum_family E g Λ U R hP hH
  have hnz : ∀ I, Continuous fun x : U => (R x).nz F.σ I := fun I => GlobalTheory.T.continuous_cusp_norm_family E g Λ Ψ U R F.σ I hP hH
  have hbdd : ∀ x : U, BddAbove {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz F.σ I)} := by
    intro x
    have hr : (R x).HasRank F.σ j' := fun τ => (F.sig x.1 x.2 τ).1
    obtain ⟨-, -, h3, -, -⟩ := GlobalTheory.T.first_minimum_and_cusp_weight_bounds E g Λ Ψ (R x) F.σ j' F.cm hr hj
    refine ⟨(R x).cuspW F.σ, ?_⟩
    rintro y ⟨I, hI, rfl⟩
    exact (h3 I hI).1
  have hcw : Measurable fun x : U => (R x).cuspW F.σ :=
    GlobalTheory.T.measurable_cusp_weight_family E g Λ Ψ U R F.σ F.form (fun x => F.form_eq _) (fun I => (hnz I).measurable) hbdd
  refine ⟨continuousOn_iff_continuous_restrict.2 hlam, ?_, hO, ?_⟩
  · classical
    have e : (ballDom F.q).indicator (fun t => (F.R t).cuspW F.σ) =
        fun t => if h : t ∈ ballDom F.q then (R ⟨t, h⟩).cuspW F.σ else 0 := by
      funext t
      by_cases h : t ∈ ballDom F.q <;> simp [h, R]
    rw [e]
    exact Measurable.dite (s := ballDom F.q) hcw measurable_const hO.measurableSet
  · rintro t ht t' ht' ⟨γ, hγ, φ, hφ⟩
    have hf : ∀ x y, (F.R t').form (γ x) (γ y) = (F.R t).form x y := fun x y => by
      rw [F.form_eq, F.form_eq]
      exact hγ x y
    obtain ⟨h1, h2⟩ := GlobalTheory.T.isometry_preserves_hermitian_and_action E g Λ (F.R t) (F.R t') γ φ hf hφ
    have himg : φ '' Set.range (F.R t).P = Set.range (F.R t').P := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨γ x, hφ x⟩
      · rintro ⟨y, rfl⟩
        refine ⟨_, ⟨γ.symm y, rfl⟩, ?_⟩
        rw [← hφ, γ.apply_symm_apply]
    obtain ⟨a, b, -⟩ := GlobalTheory.T.cusp_weight_invariant_under_isometry E g Λ Ψ (F.R t) F.σ g Λ (F.R t') φ F.cm himg h1 h2
    exact ⟨b.symm, a.symm⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FamilyMeas
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumContinuousCuspWeightMeasurableStatement

section

@[expose] public section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

theorem _root_.GlobalTheory.T.first_minimum_continuous_cusp_weight_measurable : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ), 1 ≤ j' → ContinuousOn (fun t => (F.R t).lam1) (ballDom F.q) ∧ Measurable ((ballDom F.q).indicator fun t => (F.R t).cuspW F.σ) ∧ IsOpen (ballDom F.q) ∧ ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → (F.R t).lam1 = (F.R t').lam1 ∧ (F.R t).cuspW F.σ = (F.R t').cuspW F.σ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamilyMeas.first_minimum_cusp_weight_regular | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamilyMeas.first_minimum_cusp_weight_regular | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamilyMeas.first_minimum_cusp_weight_regular <;> assumption)
end
end
