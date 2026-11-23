module

public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormEqZpowOfMemMaxUnramifiedSubfield
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Algebra.Nonarchimedean.Completion
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegersCompletion
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NStageTrivialCharacterCoeffEqAlt
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureAdjoinUnitBallCoeffBound

section

@[expose] public section

open Polynomial

namespace GlobalTheory

theorem closure_adjoin_unitBall_coeff_bound : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (ζ : PadicAlgCl l), IsIntegral ℚ_[l] ζ → ∃ (n : ℕ) (C : ℝ), ∀ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))), ‖x‖ ≤ 1 → ∃ c : Fin n → ℂ_[l], (∀ i, c i ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖c i‖ ≤ C) ∧ x = ∑ i, c i * (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ (i : ℕ) := by
  intro l _ F ζ hζ
  set ι := algebraMap (PadicAlgCl l) ℂ_[l] with hι
  let F0 : Subfield ℂ_[l] := (F.toSubfield.map ι).topologicalClosure
  have hF0 : (F0 : Set ℂ_[l]) = closure (ι '' (F : Set (PadicAlgCl l))) := rfl
  have hmemF : ∀ y ∈ F, ι y ∈ F0 := fun y hy =>
    Subfield.le_topologicalClosure _ ⟨y, hy, rfl⟩
  obtain ⟨r, hr⟩ := NontriviallyNormedField.non_trivial (α := ℚ_[l])
  have hrmem : ι (algebraMap ℚ_[l] (PadicAlgCl l) r) ∈ F0 := hmemF _ (F.algebraMap_mem r)
  have hrnorm : ‖ι (algebraMap ℚ_[l] (PadicAlgCl l) r)‖ = ‖r‖ := by
    rw [← PadicComplex.coe_eq, PadicComplex.norm_extends]
    exact PadicAlgCl.norm_extends l r
  letI : NontriviallyNormedField F0 :=
    { SubfieldClass.toNormedField F0 with
      non_trivial := ⟨⟨_, hrmem⟩, by
        show 1 < ‖ι (algebraMap ℚ_[l] (PadicAlgCl l) r)‖
        rw [hrnorm]; exact hr⟩ }
  haveI : CompleteSpace F0 := (Subfield.isClosed_topologicalClosure _).completeSpace_coe
  letI : NormedSpace F0 ℂ_[l] :=
    { norm_smul_le := fun a b => by
        show ‖(a : ℂ_[l]) * b‖ ≤ ‖(a : ℂ_[l])‖ * ‖b‖
        exact (norm_mul _ _).le }
  set z := ι ζ with hz
  set q := minpoly ℚ_[l] ζ with hq
  set n := q.natDegree with hn
  let g : ℚ_[l] →+* F0 := (ι.comp (algebraMap ℚ_[l] (PadicAlgCl l))).codRestrict F0
    (fun r => hmemF _ (F.algebraMap_mem r))
  let Q : F0[X] := q.map g
  have hQmonic : Q.Monic := (minpoly.monic hζ).map g
  have hQdeg : Q.natDegree = n := (minpoly.monic hζ).natDegree_map g
  have hQroot : aeval z Q = 0 := by
    have h1 : (algebraMap F0 ℂ_[l]).comp g = ι.comp (algebraMap ℚ_[l] (PadicAlgCl l)) := by
      ext; rfl
    rw [aeval_def, eval₂_map, h1, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hQ1 : Q ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hQdeg, natDegree_one] at this
    exact (minpoly.natDegree_pos hζ).ne' this
  let φ : (Fin n → F0) →ₗ[F0] ℂ_[l] := Fintype.linearCombination F0 (fun i : Fin n => z ^ (i : ℕ))
  have hpoly : ∀ p : F0[X], aeval z p ∈ LinearMap.range φ := by
    intro p
    rw [← aeval_modByMonic_eq_self_of_root (p := p) hQroot]
    have hd : (p %ₘ Q).natDegree < n := hQdeg ▸ natDegree_modByMonic_lt p hQmonic hQ1
    rw [aeval_eq_sum_range' hd, ← Fin.sum_univ_eq_sum_range (fun i => (p %ₘ Q).coeff i • z ^ i)]
    exact ⟨fun i => (p %ₘ Q).coeff i, by rw [Fintype.linearCombination_apply]⟩
  have hadj : ∀ y ∈ Algebra.adjoin F0 {z}, y ∈ LinearMap.range φ := by
    intro y hy
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, rfl⟩ := hy
    exact hpoly p
  let B : Subalgebra ℚ_[l] (PadicAlgCl l) :=
    { (Algebra.adjoin F0 {z}).toSubsemiring.comap ι with
      algebraMap_mem' := fun r => by
        show ι (algebraMap ℚ_[l] _ r) ∈ Algebra.adjoin F0 {z}
        exact (Algebra.adjoin F0 {z}).algebraMap_mem (⟨_, hmemF _ (F.algebraMap_mem r)⟩ : F0) }
  have hsub : ∀ y ∈ (F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)),
      ι y ∈ Algebra.adjoin F0 {z} := by
    intro y hy
    have hle : (F ⊔ IntermediateField.adjoin ℚ_[l] {ζ}).toSubalgebra ≤ B := by
      rw [IntermediateField.sup_toSubalgebra_of_isAlgebraic_right]
      refine sup_le ?_ ?_
      · intro w hw
        exact (Algebra.adjoin F0 {z}).algebraMap_mem (⟨_, hmemF w hw⟩ : F0)
      · rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζ.isAlgebraic]
        refine Algebra.adjoin_le (Set.singleton_subset_iff.2 ?_)
        exact Algebra.subset_adjoin rfl
    exact hle hy
  have hclosed : IsClosed ((LinearMap.range φ : Submodule F0 ℂ_[l]) : Set ℂ_[l]) :=
    Submodule.closed_of_finiteDimensional _
  have hcl : closure (ι '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} :
      IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))) ⊆ LinearMap.range φ :=
    closure_minimal (by rintro _ ⟨y, hy, rfl⟩; exact hadj _ (hsub y hy)) hclosed
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (LinearMap.ker φ)
  have hψker : LinearMap.ker (φ.domRestrict W) = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun w hw => ?_
    exact Subtype.ext (Submodule.disjoint_def.1 hW.disjoint _ hw w.2)
  obtain ⟨C0, -, hC0⟩ := (φ.domRestrict W).exists_antilipschitzWith hψker
  refine ⟨n, C0, fun x hx hx1 => ?_⟩
  obtain ⟨v, hv⟩ := hcl hx
  obtain ⟨k, hk, w, hw, hkw⟩ := Submodule.mem_sup.1 (hW.sup_eq_top ▸ Submodule.mem_top (x := v))
  have hφw : φ w = x := by
    rw [← hv, ← hkw, map_add (f := _), LinearMap.mem_ker.1 hk, zero_add]
  have hwn : ‖w‖ ≤ C0 := by
    have h := hC0.le_mul_dist ⟨w, hw⟩ 0
    rw [map_zero, dist_zero_right, dist_zero_right] at h
    have h2 : ‖(φ.domRestrict W) ⟨w, hw⟩‖ = ‖x‖ := by
      rw [LinearMap.domRestrict_apply, hφw]
    rw [h2] at h
    calc ‖w‖ = ‖(⟨w, hw⟩ : W)‖ := rfl
      _ ≤ C0 * ‖x‖ := h
      _ ≤ C0 * 1 := mul_le_mul_of_nonneg_left hx1 C0.2
      _ = C0 := mul_one _
  refine ⟨fun i => (w i : ℂ_[l]), fun i => ⟨(w i).2, ?_⟩, ?_⟩
  · exact (norm_le_pi_norm w i).trans hwn
  · rw [← hφw, Fintype.linearCombination_apply]
    rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosureAdjoinUnitBallCoeffBoundStatement

section

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.exists_coeff_bounded_in_closure_of_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (ζ : PadicAlgCl l), IsIntegral ℚ_[l] ζ → ∃ (n : ℕ) (C : ℝ), ∀ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((F ⊔ IntermediateField.adjoin ℚ_[l] {ζ} : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))), ‖x‖ ≤ 1 → ∃ c : Fin n → ℂ_[l], (∀ i, c i ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖c i‖ ≤ C) ∧ x = ∑ i, c i * (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ (i : ℕ) := by
  first | exact @GlobalTheory.closure_adjoin_unitBall_coeff_bound | exact GlobalTheory.closure_adjoin_unitBall_coeff_bound | (intros; apply GlobalTheory.closure_adjoin_unitBall_coeff_bound <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicUnramifiedCompletedIntegers

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.CycClosure

variable {l : ℕ} [Fact l.Prime]

theorem mem_clC {F : IntermediateField ℚ_[l] (PadicAlgCl l)} {x : ℂ_[l]} :
    x ∈ clC l F ↔ x ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∧ ‖x‖ ≤ 1 := by
  simp only [clC, Subring.mem_inf]
  apply and_congr Iff.rfl
  change x ∈ PadicComplexInt l ↔ _
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff, PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).symm

theorem coe_clC (F : IntermediateField ℚ_[l] (PadicAlgCl l)) :
    (clC l F : Set ℂ_[l]) =
      closure ((fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1}) := by
  have hc : IsClopen (Metric.closedBall (0 : ℂ_[l]) 1) :=
    IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  have e : (fun y : PadicAlgCl l => (y : ℂ_[l])) '' {y | y ∈ F ∧ ‖y‖ ≤ 1} =
      (algebraMap (PadicAlgCl l) ℂ_[l] '' (F : Set (PadicAlgCl l))) ∩ Metric.closedBall 0 1 := by
    ext x
    constructor
    · rintro ⟨y, ⟨hy, h⟩, rfl⟩
      exact ⟨⟨y, hy, rfl⟩, by rw [mem_closedBall_zero_iff, PadicComplex.norm_extends]; exact h⟩
    · rintro ⟨⟨y, hy, rfl⟩, h⟩
      rw [mem_closedBall_zero_iff] at h
      exact ⟨y, ⟨hy, by rw [← PadicComplex.norm_extends]; exact h⟩, rfl⟩
  rw [e]
  apply Set.Subset.antisymm
  · intro x hx
    rw [SetLike.mem_coe, mem_clC] at hx
    exact hc.isOpen.closure_inter ⟨hx.1, by simpa using hx.2⟩
  · intro x hx
    have := closure_inter_subset_inter_closure _ _ hx
    rw [hc.isClosed.closure_eq] at this
    exact mem_clC.2 ⟨this.1, by simpa using this.2⟩

theorem clC_mono {F G : IntermediateField ℚ_[l] (PadicAlgCl l)} (h : F ≤ G) {x : ℂ_[l]}
    (hx : x ∈ clC l F) : x ∈ clC l G :=
  mem_clC.2 ⟨closure_mono (Set.image_mono h) (mem_clC.1 hx).1, (mem_clC.1 hx).2⟩

theorem clC_props (LL : Loc.FinExt l) (F : IntermediateField ℚ_[l] (PadicAlgCl l))
    (hF : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = F) :
    ∃ _ : IsDiscreteValuationRing ↥(clC l F),
      IsAlgClosed (IsLocalRing.ResidueField ↥(clC l F)) ∧
      IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l F)) ↥(clC l F) ∧
      IsAdic (IsLocalRing.maximalIdeal ↥(clC l F)) ∧
      (∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) := by
  subst hF
  obtain ⟨O, hdvr, -, -, hdiv, hres, hcomp, hadic, hO⟩ := GlobalTheory.BigInt.exists_integers_completion l LL
  have e : O = clC l (LL.1 ⊔ Loc.MaximalUnramifiedExtension l) := SetLike.coe_injective (hO.trans (coe_clC _).symm)
  subst e
  exact ⟨hdvr, hres, hcomp, hadic, hdiv⟩

theorem muK_spec (k : ℕ) : FiniteDimensional ℚ_[l] ↥(muK l k) ∧
    ∃ ζ : PadicAlgCl l, IsPrimitiveRoot ζ (l ^ k) ∧ muK l k = IntermediateField.adjoin ℚ_[l] {ζ} := by
  have hn : 0 < l ^ k := pow_pos (Fact.out : l.Prime).pos k
  haveI : NeZero (l ^ k) := ⟨hn.ne'⟩
  classical
  have hfin : ({x | x ^ (l ^ k) = 1} : Set (PadicAlgCl l)).Finite := by
    refine (Polynomial.nthRoots (l ^ k) (1 : PadicAlgCl l)).toFinset.finite_toSet.subset fun x hx => ?_
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
    exact hx
  haveI := hfin.to_subtype
  refine ⟨IntermediateField.finiteDimensional_adjoin fun x hx =>
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [show x ^ (l ^ k) = 1 from hx]⟩, ?_⟩
  have hdeg : (cyclotomic (l ^ k) (PadicAlgCl l)).degree ≠ 0 := by
    rw [degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.2 hn).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  have hp : IsPrimitiveRoot ζ (l ^ k) := (isRoot_cyclotomic_iff).1 hζ
  refine ⟨ζ, hp, le_antisymm ?_ ?_⟩
  · rw [muK, IntermediateField.adjoin_le_iff]
    intro x hx
    have hx' : x ^ (l ^ k) = 1 := hx
    obtain ⟨i, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hx'
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ) _
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact IntermediateField.subset_adjoin _ _ hp.pow_eq_one

end GlobalTheory.CycClosure

namespace GlobalTheory.CycClosure

theorem exists_cyclotomic_integers : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ), ∃ _ : IsDiscreteValuationRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), IsAlgClosed (IsLocalRing.ResidueField ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(clC l (Kt l K₀ L ⊔ muK l k))) ∧ (∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∀ y ∈ clC l (Kt l K₀ L ⊔ muK l k), ‖x‖ ≤ ‖y‖ → x / y ∈ clC l (Kt l K₀ L ⊔ muK l k)) ∧ muK l 0 = ⊥ ∧ (∃ T : Finset ℂ_[l], ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ Submodule.span ↥(clC l (Kt l K₀ L)) (T : Set ℂ_[l])) ∧ ∃ ζ ∈ clC l (Kt l K₀ L ⊔ muK l k), IsPrimitiveRoot ζ (l ^ k) ∧ ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ (p : Polynomial ↥(clC l (Kt l K₀ L))) (d : ↥(clC l (Kt l K₀ L))), d ≠ 0 ∧ x * (d : ℂ_[l]) = Polynomial.aeval ζ p := by
  intro l _ K₀ L k
  have hp : l.Prime := Fact.out
  obtain ⟨hfd, ζ, hζ, hmu⟩ := muK_spec (l := l) k
  let LL : Loc.FinExt l := ⟨K₀.1 ⊔ L.1 ⊔ muK l k, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  have hM : LL.1 ⊔ Loc.MaximalUnramifiedExtension l = Kt l K₀ L ⊔ muK l k := by
    simp only [LL, Kt]; exact sup_right_comm _ _ _
  let L0 : Loc.FinExt l := ⟨K₀.1 ⊔ L.1, by haveI := K₀.2; haveI := L.2; infer_instance⟩
  obtain ⟨hdvr, hres, hcomp, hadic, hdiv⟩ := clC_props LL _ hM
  obtain ⟨hdvr0, -, -, -, -⟩ := clC_props L0 (Kt l K₀ L) rfl
  have mu0 : muK l 0 = ⊥ := by
    rw [muK, eq_bot_iff, IntermediateField.adjoin_le_iff]
    intro x hx
    have : x = 1 := by simpa using hx
    rw [this]; exact one_mem _
  have hn : 0 < l ^ k := pow_pos hp.pos k
  have hint : IsIntegral ℚ_[l] ζ :=
    ⟨X ^ (l ^ k) - C 1, monic_X_pow_sub_C 1 hn.ne', by simp [hζ.pow_eq_one]⟩
  obtain ⟨n, Cb, hC⟩ := GlobalTheory.T.exists_coeff_bounded_in_closure_of_norm_le_one l (Kt l K₀ L) ζ hint
  have hB : ∀ x, x ∈ clC l (Kt l K₀ L ⊔ muK l k) ↔ x ∈ clC l (Kt l K₀ L ⊔ IntermediateField.adjoin ℚ_[l] {ζ}) := by
    intro x; rw [hmu]
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [← map_natCast (algebraMap (PadicAlgCl l) ℂ_[l])]
    refine lt_of_eq_of_lt (PadicComplex.norm_extends l (l : PadicAlgCl l)) ?_
    rw [GlobalTheory.UnramValue.norm_l]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hl0 : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < 1 / (max Cb 1) by positivity) hl
  have cmem : ∀ c ∈ closure (algebraMap (PadicAlgCl l) ℂ_[l] '' ((Kt l K₀ L : IntermediateField ℚ_[l] (PadicAlgCl l)) : Set (PadicAlgCl l))),
      ‖c‖ ≤ Cb → (l : ℂ_[l]) ^ N * c ∈ clC l (Kt l K₀ L) := by
    intro c hc hcb
    refine mem_clC.2 ⟨map_mem_closure (continuous_const.mul continuous_id) hc ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      refine ⟨(l : PadicAlgCl l) ^ N * z, mul_mem (pow_mem (natCast_mem _ _) _) hz, ?_⟩
      simp
    · rw [norm_mul, norm_pow]
      have h1 : ‖c‖ ≤ max Cb 1 := hcb.trans (le_max_left _ _)
      have h2 : (0 : ℝ) < max Cb 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      calc ‖(l : ℂ_[l])‖ ^ N * ‖c‖ ≤ ‖(l : ℂ_[l])‖ ^ N * max Cb 1 :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ 1 / max Cb 1 * max Cb 1 := mul_le_mul_of_nonneg_right hN.le h2.le
        _ = 1 := by field_simp
  set ζ' : ℂ_[l] := algebraMap (PadicAlgCl l) ℂ_[l] ζ with hζ'
  have hζn : ‖ζ‖ = 1 := by
    have := congrArg norm hζ.pow_eq_one
    rw [norm_pow, norm_one] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
  have hζB : ζ' ∈ clC l (Kt l K₀ L ⊔ muK l k) := by
    rw [hB]
    refine mem_clC.2 ⟨subset_closure ⟨ζ, (le_sup_right : IntermediateField.adjoin ℚ_[l] {ζ} ≤ _)
      (IntermediateField.mem_adjoin_simple_self ℚ_[l] ζ), rfl⟩, ?_⟩
    exact ((PadicComplex.norm_extends l ζ).trans hζn).le
  have hAB : ∀ x ∈ clC l (Kt l K₀ L), x ∈ clC l (Kt l K₀ L ⊔ muK l k) := fun x hx => clC_mono le_sup_left hx
  have hlN : (l : ℂ_[l]) ^ N ∈ clC l (Kt l K₀ L) := pow_mem (natCast_mem _ _) _
  have rep : ∀ x ∈ clC l (Kt l K₀ L ⊔ muK l k), ∃ c : Fin n → ℂ_[l],
      (∀ i, (l : ℂ_[l]) ^ N * c i ∈ clC l (Kt l K₀ L)) ∧ x = ∑ i, c i * ζ' ^ (i : ℕ) := by
    intro x hx
    rw [hB] at hx
    obtain ⟨c, hc, e⟩ := hC x (mem_clC.1 hx).1 (mem_clC.1 hx).2
    exact ⟨c, fun i => cmem _ (hc i).1 (hc i).2, e⟩
  refine ⟨hdvr, hres, hcomp, hadic, hdiv, mu0, ?_, ζ', hζB, hζ.map_of_injective (algebraMap (PadicAlgCl l) ℂ_[l]).injective, ?_⟩
  · classical
    let g : Fin n → ℂ_[l] := fun i => ((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ)
    let P : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] := Submodule.span ↥(clC l (Kt l K₀ L)) (Set.range g)
    let B' : Submodule ↥(clC l (Kt l K₀ L)) ℂ_[l] :=
      { carrier := (clC l (Kt l K₀ L ⊔ muK l k) : Set ℂ_[l])
        add_mem' := fun ha hb => add_mem ha hb
        zero_mem' := zero_mem _
        smul_mem' := fun a x hx => by
          rw [Subring.smul_def, smul_eq_mul]
          exact mul_mem (hAB _ a.2) hx }
    have hBP : B' ≤ P := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := rep x hx
      refine Submodule.sum_mem _ fun i _ => ?_
      have := Submodule.smul_mem P (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L)))
        (Submodule.subset_span ⟨i, rfl⟩ : g i ∈ P)
      convert this using 1
      rw [Subring.smul_def, smul_eq_mul]
      change c i * ζ' ^ (i : ℕ) = ((l : ℂ_[l]) ^ N * c i) * (((l : ℂ_[l]) ^ N)⁻¹ * ζ' ^ (i : ℕ))
      field_simp
    haveI : IsNoetherian ↥(clC l (Kt l K₀ L)) ↥P :=
      isNoetherian_of_fg_of_noetherian P (Submodule.fg_span (Set.finite_range g))
    have hfg : B'.FG := by
      have h1 : (B'.comap P.subtype).FG := IsNoetherian.noetherian _
      have h2 := h1.map P.subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.2 hBP] at h2
    obtain ⟨T, hT⟩ := hfg
    exact ⟨T, fun x => by rw [hT]; rfl⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := rep x hx
    refine ⟨∑ i : Fin n, monomial (i : ℕ) (⟨(l : ℂ_[l]) ^ N * c i, hc i⟩ : ↥(clC l (Kt l K₀ L))),
      ⟨(l : ℂ_[l]) ^ N, hlN⟩, fun h => pow_ne_zero N hl0 (congrArg Subtype.val h), ?_⟩

    simp only [map_sum, aeval_monomial, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    change c i * ζ' ^ (i : ℕ) * (l : ℂ_[l]) ^ N = ((l : ℂ_[l]) ^ N * c i) * ζ' ^ (i : ℕ)
    ring

end GlobalTheory.CycClosure
end
end
end
