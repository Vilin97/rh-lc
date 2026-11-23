module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableOfProjArithAmbientStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMatrixIsForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasChernIntegralLinearOfDensityEqSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqMultiDiff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianOfCombinationMetricLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReDetRelation
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Mathlib.RingTheory.PiTensorProduct

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralLinearRelationZero

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ChernLinRel

theorem restrict_finsetSum {α : Type} [MeasurableSpace α] {J : Type} (s : Finset J) (ν : J → Measure α) (S : Set α) :
    (∑ j ∈ s, ν j).restrict S = ∑ j ∈ s, (ν j).restrict S := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Measure.restrict_add, ih]

end GlobalTheory.ChernLinRel


open GlobalTheory.ChernLinRel in
theorem GlobalTheory.ChernLinRel.sum_chernInt_eq_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (D : ℕ) (J : Type) [Fintype J] (a : J → ℝ) (N : J → HermLB p), (∀ (c : AlgChart p σ D), ∀ y ∈ c.e.source, ∑ j, a j * c.chernDens ((N j).φ σ) y = 0) → ∀ (S : Set (CxPts p σ)) (g : CxPts p σ → ℝ), (∀ j, ((N j).φ σ).ChernIntegrableOn D S g) → ∑ j, a j * ((N j).φ σ).chernInt D S g = 0 := by
  intro k _ X p hp σ D J _ a N hlin S g hint
  classical
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  set P : J → ℤˣ → Measure (CxPts p σ) := fun j ε => ((N j).φ σ).chernPart D ε with hPdef
  let ap : J → ℝ := fun j => max (a j) 0
  let an : J → ℝ := fun j => max (-a j) 0
  let μ : (J → ℝ) → (J → ℝ) → Measure (CxPts p σ) := fun u w =>
    ∑ j, (ENNReal.ofReal (u j) • P j 1 + ENNReal.ofReal (w j) • P j (-1))

  have hcont : ∀ j (c : AlgChart p σ D), ContinuousOn (fun v => c.chernDens ((N j).φ σ) (c.e.symm v)) c.e.target :=
    fun j c => continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      ((Continuous.matrix_det continuous_id).comp_continuousOn
        ((GlobalTheory.MixDens.chernMat_isForm k X p σ D _ ((N j).φ σ) ((N j).cInf σ)).2.1 c)))

  have hchart : ∀ (u w : J → ℝ) (c : AlgChart p σ D) (A : Set (CxPts p σ)), MeasurableSet A → A ⊆ c.e.source →
      μ u w A = ∫⁻ v in c.e '' A, ∑ j, (ENNReal.ofReal (u j) * ENNReal.ofReal (1 * c.chernDens ((N j).φ σ) (c.e.symm v)) +
        ENNReal.ofReal (w j) * ENNReal.ofReal (-1 * c.chernDens ((N j).φ σ) (c.e.symm v))) := by
    intro u w c A hA hAc
    have hsub : c.e '' A ⊆ c.e.target := fun _ ⟨y, hy, e⟩ => e ▸ c.e.map_source (hAc hy)
    have hm : ∀ j (s : ℝ), AEMeasurable (fun v => ENNReal.ofReal (s * c.chernDens ((N j).φ σ) (c.e.symm v)))
        (volume.restrict (c.e '' A)) := fun j s =>
      ((((hcont j c).aemeasurable c.e.open_target.measurableSet).const_mul s).ennreal_ofReal).mono_measure
        (Measure.restrict_mono hsub le_rfl)
    have hP : ∀ j (ε : ℤˣ), P j ε A = ∫⁻ v in c.e '' A, ENNReal.ofReal ((ε : ℤ) * c.chernDens ((N j).φ σ) (c.e.symm v)) :=
      fun j ε => Weight.chernPart_apply ((N j).cInf σ) ε c hA hAc
    have hm2 : ∀ j ∈ (Finset.univ : Finset J), AEMeasurable (fun v => ENNReal.ofReal (u j) * ENNReal.ofReal (1 * c.chernDens ((N j).φ σ) (c.e.symm v)) +
        ENNReal.ofReal (w j) * ENNReal.ofReal (-1 * c.chernDens ((N j).φ σ) (c.e.symm v))) (volume.restrict (c.e '' A)) :=
      fun j _ => ((hm j 1).const_mul _).add ((hm j (-1)).const_mul _)
    rw [lintegral_finsetSum' _ hm2]
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lintegral_add_left' ((hm j 1).const_mul _), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hP, hP]
    simp

  set U : Set (CxPts p σ) := ⋃ c : AlgChart p σ D, c.e.source with hUdef
  have hUo : IsOpen U := isOpen_iUnion fun c => c.e.open_source
  have hzero : ∀ u w : J → ℝ, μ u w Uᶜ = 0 := by
    intro u w
    have h0 : ∀ j (ε : ℤˣ), P j ε Uᶜ = 0 := fun j ε =>
      Weight.chernPart_eq_zero ε hUo.measurableSet.compl fun c =>
        Set.disjoint_compl_right_iff_subset.2 (Set.subset_iUnion (fun c : AlgChart p σ D => c.e.source) c)
    simp [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.add_apply, Measure.smul_apply, h0]

  have hbal : μ ap an = μ an ap := by
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable (fun c : AlgChart p σ D => c.e.source)
      fun c => c.e.open_source
    let s : Option (AlgChart p σ D) → Set (CxPts p σ) := fun o => o.elim Uᶜ fun c => c.e.source
    refine Measure.ext_of_biUnion_eq_univ (S := insert none (some '' T)) (s := s) ((hTc.image _).insert _) ?_ ?_
    · refine Set.eq_univ_of_forall fun y => ?_
      by_cases hy : y ∈ U
      · rw [hUdef, ← hT] at hy
        obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.1 hy
        exact Set.mem_iUnion₂.2 ⟨some c, Set.mem_insert_of_mem _ ⟨c, hc, rfl⟩, hyc⟩
      · exact Set.mem_iUnion₂.2 ⟨none, Set.mem_insert _ _, hy⟩
    · rintro (_ | c) -
      · show (μ ap an).restrict Uᶜ = (μ an ap).restrict Uᶜ
        rw [Measure.restrict_eq_zero.2 (hzero _ _), Measure.restrict_eq_zero.2 (hzero _ _)]
      · show (μ ap an).restrict c.e.source = (μ an ap).restrict c.e.source
        ext B hB
        have hBs := hB.inter c.e.open_source.measurableSet
        rw [Measure.restrict_apply hB, Measure.restrict_apply hB, hchart _ _ c _ hBs Set.inter_subset_right,
          hchart _ _ c _ hBs Set.inter_subset_right]
        refine setLIntegral_congr_fun (GlobalTheory.ChartGlue.measurableSet_image _ hBs Set.inter_subset_right) fun v hv => ?_
        obtain ⟨y, hy, rfl⟩ := hv
        have h0 := hlin c (c.e.symm (c.e y)) (c.e.map_target (c.e.map_source hy.2))
        have := GlobalTheory.GoodMetric.ChernLin.ofReal_balance a fun j => c.chernDens ((N j).φ σ) (c.e.symm (c.e y))
        rw [h0, mul_zero, mul_zero, ENNReal.ofReal_zero, zero_add, zero_add] at this
        exact this.symm

  have hI : ∀ u w : J → ℝ, (∀ j, 0 ≤ u j) → (∀ j, 0 ≤ w j) → ∫ y in S, g y ∂μ u w =
      ∑ j, (u j * ∫ y in S, g y ∂P j 1 + w j * ∫ y in S, g y ∂P j (-1)) := by
    intro u w hu hw
    simp only [μ, restrict_finsetSum, Measure.restrict_add, Measure.restrict_smul]
    rw [integral_finsetSum_measure fun j _ => ((hint j).1.smul_measure ENNReal.ofReal_ne_top).add_measure
      ((hint j).2.smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_add_measure ((hint j).1.smul_measure ENNReal.ofReal_ne_top)
      ((hint j).2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
      ENNReal.toReal_ofReal (hu j), ENNReal.toReal_ofReal (hw j), smul_eq_mul, smul_eq_mul]
  have e := congrArg (fun m : Measure (CxPts p σ) => ∫ y in S, g y ∂m) hbal
  rw [hI _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _),
    hI _ _ (fun j => le_max_right _ _) (fun j => le_max_right _ _)] at e
  have key : ∑ j, a j * ((N j).φ σ).chernInt D S g =
      ∑ j, (ap j * ∫ y in S, g y ∂P j 1 + an j * ∫ y in S, g y ∂P j (-1)) -
      ∑ j, (an j * ∫ y in S, g y ∂P j 1 + ap j * ∫ y in S, g y ∂P j (-1)) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have ha : ap j - an j = a j := GlobalTheory.GoodMetric.ChernLin.max_sub_max_neg (a j)
    rw [Weight.chernInt]
    simp only [P]
    linear_combination (-(∫ y in S, g y ∂((N j).φ σ).chernPart D 1) + ∫ y in S, g y ∂((N j).φ σ).chernPart D (-1)) * ha
  rw [key, e, sub_self]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalArchIntegralChernPower

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixFun

theorem exists_linear_of_rel {α V : Type} [AddCommGroup V] [Module ℝ V] (v : α → V) (f : α → ℝ)
    (h : ∀ c : α →₀ ℝ, Finsupp.linearCombination ℝ v c = 0 → Finsupp.linearCombination ℝ f c = 0) :
    ∃ Ψ : V →ₗ[ℝ] ℝ, ∀ a, Ψ (v a) = f a := by
  set A := Finsupp.linearCombination ℝ v
  set F := Finsupp.linearCombination ℝ f
  have hker : LinearMap.ker A ≤ LinearMap.ker F := fun c hc => h c hc
  obtain ⟨g, hg⟩ := LinearMap.exists_extend
    (((LinearMap.ker A).liftQ F hker).comp A.quotKerEquivRange.symm.toLinearMap)
  refine ⟨g, fun a => ?_⟩
  have e1 : v a = A (Finsupp.single a 1) := by simp [A]
  have e2 := LinearMap.congr_fun hg ⟨A (Finsupp.single a 1), LinearMap.mem_range_self _ _⟩
  rw [e1]
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image, Submodule.liftQ_apply] at e2
  rw [e2]
  simp [F]

end GlobalTheory.MixFun

namespace GlobalTheory.MixFun

theorem exists_functional_archInt : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (e : ℕ) (ι : Type) [Fintype ι] (L : ι → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb L n).ArchIntegrable M e hr) → ∃ Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb L n).archInt M e hr := by
  intro k _ Y _ q hq e ι _ L M r hr hint
  classical
  have := hq.finite
  haveI : Finite (k →+* ℂ) := .of_equiv _ (RingHom.equivIntAlgHom k ℂ).symm
  letI := Fintype.ofFinite (k →+* ℂ)
  refine GlobalTheory.MixFun.exists_linear_of_rel (fun n : ι → ℤ => lin (fun i => (n i : ℝ)) ^ e)
    (fun n => (comb L n).archInt M e hr) ?_
  intro c hc
  rw [Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
  simp only [HermLB.archInt, finsum_eq_sum_of_fintype, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [← Finset.sum_coe_sort c.support]
  refine GlobalTheory.ChernLinRel.sum_chernInt_eq_zero k Y q hq.isProjOver σ e c.support (fun j => c j)
    (fun j => comb L j) ?_ _ _ (fun j => hint j σ)
  intro ch y hy
  have key : ∀ n : ι → ℤ, ch.chernDens ((comb L n).φ σ) y = e.factorial / Real.pi ^ e *
      (Matrix.det (∑ l, ((n l : ℝ) : ℂ) • ch.hess ((L l).φ σ) (pick ((L l).φ σ).isLB y) y)).re := by
    intro n
    rw [AlgChart.chernDens, GlobalTheory.Mean4O.ReadsProj.hess_comb L n σ ch hy _ (mem_pick _ y) _ (fun l => mem_pick _ y)]
  simp only [key]
  have hrel : ∑ j : c.support, MvPolynomial.C (c j) *
      (∑ i, MvPolynomial.C ((j.1 i : ℝ)) * MvPolynomial.X i : MvPolynomial ι ℝ) ^ e = 0 := by
    rw [← hc, ← Finset.sum_coe_sort c.support]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.C_mul']
    rfl
  have h0 := GlobalTheory.MxDet.re_det_relation ι c.support e (fun j => c j) (fun j i => (j.1 i : ℝ)) hrel
    (fun l => ch.hess ((L l).φ σ) (pick ((L l).φ σ).isLB y) y)
  simp_rw [mul_left_comm _ ((e.factorial : ℝ) / Real.pi ^ e)]
  rw [← Finset.mul_sum, h0, mul_zero]

end GlobalTheory.MixFun
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearFunctionalArchIntegralChernPowerStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

theorem _root_.GlobalTheory.T.exists_linear_functional_arch_integral_chern_power : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ (e : ℕ) (ι : Type) [Fintype ι] (L : ι → HermLB q) (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r), (∀ n, (comb L n).ArchIntegrable M e hr) → ∃ Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb L n).archInt M e hr := by
  first | exact @GlobalTheory.MixFun.exists_functional_archInt | exact GlobalTheory.MixFun.exists_functional_archInt | (intros; apply GlobalTheory.MixFun.exists_functional_archInt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchIntegralAdditiveAndDiagonal

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixAdd

variable {k : Type} [CommRing k] {Y : Scheme.{0}} [IsIntegral Y] {q : Y ⟶ Sp k}

theorem archInt_congr {A B : HermLB q} (h : A.Isometric B) (M : HermLB q) (e : ℕ) {r : M.B.ι → Y.functionFieldˣ}
    (hr : IsRatSec M.B r) : A.archInt M e hr = B.archInt M e hr := by
  simp only [HermLB.archInt, h.chernInt_eq]

theorem lin_comb {ι κ : Type} [Fintype ι] [Fintype κ] (m : κ → ι → ℤ) (n : κ → ℤ) :
    (lin fun i => ((∑ j, n j * m j i : ℤ) : ℝ)) = ∑ j, (n j : ℝ) • lin fun i => (m j i : ℝ) := by

  simp only [lin, Int.cast_sum, Int.cast_mul, map_sum, map_mul, Finset.sum_mul, smul_eq_C_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem lin_add {ι : Type} [Fintype ι] (m n : ι → ℤ) :
    (lin fun i => (((m + n) i : ℤ) : ℝ)) = (lin fun i => (m i : ℝ)) + lin fun i => (n i : ℝ) := by
  simp only [lin, Pi.add_apply, Int.cast_add, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem mixArch_eq {ι : Type} [Fintype ι] {e : ℕ} (F : ι → HermLB q) (M : HermLB q) {r : M.B.ι → Y.functionFieldˣ}
    (hr : IsRatSec M.B r) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ)
    (hΨ : ∀ n : ι → ℤ, Ψ (lin (fun i => (n i : ℝ)) ^ e) = (comb F n).archInt M e hr)
    (L : Fin e → HermLB q) (m : Fin e → ι → ℤ) (h : ∀ a, (comb F (m a)).Isometric (L a)) :
    mixArch L M hr = Ψ (∏ a, lin fun i => (m a i : ℝ)) := by
  have h₁ : (fun n => (comb L n).archInt M e hr) =
      fun n : Fin e → ℤ => Ψ ((∑ a, (n a : ℝ) • lin fun i => (m a i : ℝ)) ^ e) := by
    funext n
    rw [← lin_comb, hΨ]
    exact (archInt_congr ((isometric_comb_comb F m n).trans (isometric_comb_congr h n)) M e hr).symm
  rw [mixArch, h₁, FibreProj.pol_pow _ Ψ (Fintype.card_fin e), mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.2 e.factorial_ne_zero

theorem mixArch_add_diag : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k),
    IsAmb q → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r),
    (∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ (A B : HermLB q) (L : Fin e → HermLB q),
      mixArch (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr =
        mixArch (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + mixArch (Fin.cons B L : Fin (e + 1) → HermLB q) M hr) ∧
    ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ N : HermLB q,
      mixArch (fun _ : Fin e => N) M hr = N.archInt M e hr := by
  intro hI k _ Y _ q hq M r hr
  classical
  refine ⟨fun e he A B L => ?_, fun e he N => ?_⟩
  · let F : Bool ⊕ Fin e → HermLB q := Sum.elim (fun b => cond b A B) L
    obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_linear_functional_arch_integral_chern_power k Y q hq (e + 1) _ F M r hr
      fun n => GlobalTheory.T.archIntegrable_of_projArithAmbient hI k Y q hq (e + 1) he M _ r hr
    let u : Bool ⊕ Fin e → Bool ⊕ Fin e → ℤ := fun j => Pi.single j 1
    have key (C : HermLB q) (c : Bool ⊕ Fin e → ℤ) (hc : (comb F c).Isometric C) :
        mixArch (Fin.cons C L : Fin (e + 1) → HermLB q) M hr =
          Ψ ((lin fun i => (c i : ℝ)) * ∏ a : Fin e, lin fun i => (u (Sum.inr a) i : ℝ)) := by
      rw [mixArch_eq F M hr Ψ hΨ (Fin.cons C L) (Fin.cons c fun a => u (Sum.inr a)) (fun a => by
        cases a using Fin.cases with
        | zero => exact hc
        | succ a => exact isometric_comb_single F (Sum.inr a)), Fin.prod_univ_succ]
      rfl
    have hA : (comb F (u (Sum.inl true))).Isometric A := isometric_comb_single F (Sum.inl true)
    have hB : (comb F (u (Sum.inl false))).Isometric B := isometric_comb_single F (Sum.inl false)
    rw [key A _ hA, key B _ hB, key _ _ ((isometric_comb_add F _ _).trans (hA.tens hB)), lin_add, add_mul, map_add (f := _)]
  · let F : Unit → HermLB q := fun _ => N
    obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_linear_functional_arch_integral_chern_power k Y q hq e _ F M r hr fun n => GlobalTheory.T.archIntegrable_of_projArithAmbient hI k Y q hq e he M _ r hr
    have hN : (comb F (Pi.single () 1)).Isometric N := isometric_comb_single F ()
    rw [mixArch_eq F M hr Ψ hΨ _ (fun _ => Pi.single () 1) fun _ => hN, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, hΨ]
    exact archInt_congr hN M e hr

end GlobalTheory.MixAdd
end
end
end
