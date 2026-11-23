module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoverChartSmoothNormal
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveSpanOfIntegralClosure
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CupPair
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRingStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraClosurePropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraComapSpanEqTopStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmulStatement
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Algebraic.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanRegularFormsFiniteProjectiveSmoothStatement
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveSpanOfIntegralClosureStatement

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.finite_projective_span_of_integralClosure' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (A : Subalgebra k F) (B : Subalgebra k K), (∀ y : K, y ∈ B ↔ y ∈ integralClosure A K) → Module.Finite A (integralClosure A K) → Module.Projective A (integralClosure A K) → ∀ (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Module.Finite B (Submodule.span B S) → Module.Projective B (Submodule.span B S) → Module.Finite A (Submodule.span A S) ∧ Module.Projective A (Submodule.span A S) := by
  first | (exact @GlobalTheory.finite_projective_span_of_integralClosure) | (exact GlobalTheory.finite_projective_span_of_integralClosure) | (intros; apply GlobalTheory.finite_projective_span_of_integralClosure  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackFormsIntersectionEqChartLocalization

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_comap_loc : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (omB k K (rB k K x I) p).comap (e.restrictScalars k) = (Submodule.span (rA k x I) ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)).restrictScalars k := by
  intro k _ _ F K _ _ _ _ _ _ d x hx p W _ _ _ _ _ _ _ e I i hi
  have hloc := GlobalTheory.T.kahlerFormsOverSubalgebra_standardOpen_iff_pow_smul k F K d x hx I i hi p
  ext w
  rw [Submodule.restrictScalars_mem, Submodule.mem_comap, LinearMap.restrictScalars_apply]
  constructor
  · intro hw
    obtain ⟨N, hN⟩ := (hloc _).1 hw
    have hg : (∏ j ∈ I, x i / x j) ^ N ∈ rA k x I :=
      Subalgebra.pow_mem _ (Subalgebra.prod_mem _ fun j hj =>
        Algebra.subset_adjoin (s := {y | ∃ i ∈ I, ∃ j, y = x j / x i}) ⟨j, hj, i, rfl⟩) N
    have hfg : (∏ j ∈ I, x i / x j) ^ N * (∏ j ∈ I, x j / x i) ^ N = 1 := by
      rw [← mul_pow, ← Finset.prod_mul_distrib, Finset.prod_eq_one, one_pow]
      intro j _
      have h1 := hx.pd.ne i
      have h2 := hx.pd.ne j
      field_simp
    have hm : (∏ j ∈ I, x j / x i) ^ N • w ∈
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W) := by
      rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply,
        ← algebraMap_smul K, map_smul, map_pow]
      exact hN
    have := (Submodule.span (rA k x I) _).smul_mem ⟨_, hg⟩ (Submodule.subset_span hm)
    rwa [Subalgebra.smul_def, smul_smul, hfg, one_smul] at this
  · intro hw
    induction hw using Submodule.span_induction with
    | mem z hz =>
      refine (hloc _).2 ⟨0, ?_⟩
      rw [pow_zero, one_smul]
      exact hz
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [map_add (f := _)]; exact Submodule.add_mem _ ha hb
    | smul r a _ ha =>
      rw [Subalgebra.smul_def, ← algebraMap_smul K, map_smul]
      refine ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x I) p p).2.1 _ ha).2.2.2 _ ?_
      exact (integralClosure (rA k x I) K).algebraMap_mem r

end GlobalTheory.PD
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PulledBackFormsIntersectionEqChartLocalizationStatement

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.pulledBackForms_intersection_eq_chart_localization : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K) (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → (omB k K (rB k K x I) p).comap (e.restrictScalars k) = (Submodule.span (rA k x I) ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)).restrictScalars k := by
  first | (exact @GlobalTheory.PD.omB_comap_loc) | (exact GlobalTheory.PD.omB_comap_loc) | (intros; apply GlobalTheory.PD.omB_comap_loc  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfStableOfIsFractionRing

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory


open KaehlerDifferential in
theorem _root_.GlobalTheory.span_eq_top_of_stable_of_isFractionRing :
    ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k K] [Algebra F K] [FiniteDimensional F K] (B : Subalgebra k K) [IsFractionRing B K] (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Submodule.span K S = ⊤ → Submodule.span F S = ⊤ := by
  intro k F K _ _ _ _ _ _ B _ W _ _ _ _ S hS hspan
  set M := Submodule.span F S with hM
  let T : Subalgebra F K :=
    { carrier := {y | ∀ m ∈ M, y • m ∈ M}
      mul_mem' := fun {a b} ha hb m hm => by rw [mul_smul]; exact ha _ (hb m hm)
      one_mem' := fun m hm => by rwa [one_smul]
      add_mem' := fun {a b} ha hb m hm => by rw [add_smul]; exact M.add_mem (ha m hm) (hb m hm)
      zero_mem' := fun m _ => by rw [zero_smul]; exact M.zero_mem
      algebraMap_mem' := fun f m hm => by rw [algebraMap_smul]; exact M.smul_mem f hm }
  have hmemT : ∀ y : K, y ∈ T ↔ ∀ m ∈ M, y • m ∈ M := fun y => Iff.rfl
  have hB : ∀ c ∈ B, (c : K) ∈ T := by
    intro c hc m hm
    induction hm using Submodule.span_induction with
    | mem s hs => exact Submodule.subset_span (hS c hc s hs)
    | zero => rw [smul_zero]; exact M.zero_mem
    | add v w _ _ hv hw => rw [smul_add]; exact M.add_mem hv hw
    | smul f v _ hv => rw [smul_comm]; exact M.smul_mem f hv
  have hinv : ∀ y : K, y ∈ T → y⁻¹ ∈ T := by
    intro y hy
    exact T.inv_mem_of_algebraic (x := ⟨y, hy⟩) (Algebra.IsAlgebraic.isAlgebraic y)
  have hall : ∀ y : K, y ∈ T := by
    intro y
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := B) y
    rw [div_eq_mul_inv]
    exact T.mul_mem (hB _ a.2) (hinv _ (hB _ b.2))
  let MK : Submodule K W :=
    { carrier := M
      add_mem' := M.add_mem
      zero_mem' := M.zero_mem
      smul_mem' := fun c m hm => hall c m hm }
  have hle : Submodule.span K S ≤ MK := Submodule.span_le.mpr fun s hs => Submodule.subset_span hs
  rw [hspan] at hle
  exact eq_top_iff.mpr fun w _ => hle Submodule.mem_top

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanEqTopOfStableOfIsFractionRingStatement

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.span_eq_top_of_stable_of_isFractionRing' : ∀ (k F K : Type) [Field k] [Field F] [Field K] [Algebra k K] [Algebra F K] [FiniteDimensional F K] (B : Subalgebra k K) [IsFractionRing B K] (W : Type) [AddCommGroup W] [Module K W] [Module F W] [IsScalarTower F K W] (S : Set W), (∀ c ∈ B, ∀ w ∈ S, (c : K) • w ∈ S) → Submodule.span K S = ⊤ → Submodule.span F S = ⊤ := by
  first | (exact @GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (exact GlobalTheory.span_eq_top_of_stable_of_isFractionRing) | (intros; apply GlobalTheory.span_eq_top_of_stable_of_isFractionRing  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFormsIsBundleProjectiveCover

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem omB_isBundle : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → IsBundle k x fun I => (omB k K (rB k K x I) p).comap (e.restrictScalars k) := by
  intro k _ _ F K _ _ _ _ _ _ d x hx p W _ _ _ _ _ _ _ e he hr
  have hstab : ∀ I, ∀ c ∈ rB k K x I, ∀ w ∈ ((omB k K (rB k K x I) p).comap (e.restrictScalars k) : Set W),
      (c : K) • w ∈ ((omB k K (rB k K x I) p).comap (e.restrictScalars k) : Set W) := by
    intro I c hc w hw
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.restrictScalars_apply] at hw ⊢
    rw [map_smul]
    exact ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K _ p p).2.1 _ hw).2.2.2 c hc
  have key : ∀ i, Module.Finite (rA k x {i}) (Submodule.span (rA k x {i})
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)) ∧
      Module.Projective (rA k x {i}) (Submodule.span (rA k x {i})
        ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W)) := by
    intro i
    obtain ⟨hf1, hf2, hf3⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hx {i} (Finset.singleton_nonempty i)
    haveI := hf2
    haveI := hf3
    obtain ⟨hB1, hB2⟩ := GlobalTheory.T.span_regularForms_finite_projective_smooth k K (rB k K x {i}) p W e he hr
    exact GlobalTheory.T.finite_projective_span_of_integralClosure' k F K (rA k x {i}) (rB k K x {i}) (fun y => Iff.rfl) hf1 (GlobalTheory.T.integralClosure_projective_over_standardOpenRing k F K d x hx i) W _
      (hstab {i}) hB1 hB2
  refine ⟨fun i => ?_, fun i => (key i).2, fun I i hi => GlobalTheory.T.pulledBackForms_intersection_eq_chart_localization k F K d x hx p W e I i hi⟩
  obtain ⟨hfin, -⟩ := key i
  obtain ⟨-, hf2, -⟩ := GlobalTheory.T.finite_cover_chart_smooth_normal k F K d x hx {i} (Finset.singleton_nonempty i)
  haveI := hf2
  haveI : FiniteDimensional F K := hx.fin
  set S : Set W := ((omB k K (rB k K x {i}) p).comap (e.restrictScalars k) : Set W) with hSdef
  obtain ⟨s, hs⟩ := Module.Finite.iff_fg.1 hfin
  have hA : ∀ a : rA k x {i}, ∀ w ∈ S, a • w ∈ S := by
    intro a w hw
    rw [Subalgebra.smul_def, ← algebraMap_smul K (a : F) w]
    exact hstab {i} _ (Subalgebra.algebraMap_mem (integralClosure (rA k x {i}) K) a) w hw
  have hspan : (Submodule.span (rA k x {i}) S).restrictScalars k =
      (omB k K (rB k K x {i}) p).comap (e.restrictScalars k) := by
    apply le_antisymm
    · intro y hy
      change y ∈ Submodule.span (rA k x {i}) S at hy
      change y ∈ S
      induction hy using Submodule.span_induction with
      | mem z hz => exact hz
      | zero => exact Submodule.zero_mem _
      | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
      | smul a z _ hz => exact hA a z hz
    · exact fun y hy => Submodule.subset_span hy
  refine ⟨s, by rw [hs, hspan], ?_⟩
  have hK := GlobalTheory.T.kahlerFormsOverSubalgebra_comap_span_eq_top k K (rB k K x {i}) p W e he hr
  have hF := GlobalTheory.T.span_eq_top_of_stable_of_isFractionRing' k F K (rB k K x {i}) W S (hstab {i}) hK
  rw [eq_top_iff, ← hF, Submodule.span_le]
  intro w hw
  have : w ∈ Submodule.span (rA k x {i}) (s : Set W) := by rw [hs]; exact Submodule.subset_span hw
  exact Submodule.span_le_restrictScalars (rA k x {i}) F (s : Set W) this

end GlobalTheory.PD
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFormsIsBundleProjectiveCoverStatement

section

@[expose] public section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

theorem _root_.GlobalTheory.T.regularForms_isBundle_projectiveCover : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ (p : ℕ) (W : Type) [AddCommGroup W] [Module K W] [Module F W] [Module k W] [IsScalarTower F K W] [IsScalarTower k F W] [IsScalarTower k K W] (e : W →ₗ[K] DR k K), Function.Injective e → LinearMap.range e = ⋀[K]^p Ω[K⁄k] → IsBundle k x fun I => (omB k K (rB k K x I) p).comap (e.restrictScalars k) := by
  first | (exact @GlobalTheory.PD.omB_isBundle) | (exact GlobalTheory.PD.omB_isBundle) | (intros; apply GlobalTheory.PD.omB_isBundle  <;> assumption)
end
end
