module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsPlaceWeightConjInvariantStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatTwistStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
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
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemOfAevalEqZero
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GreenCurrentIntegralFormulaStatement

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEqMulMultOfUnits

section

@[expose] public section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

open NumberField.InfinitePlace NumberField.Units NumberField.Units.dirichletUnitTheorem

theorem exists_eq_mul_mult_of_units (F : Type) [Field F] [NumberField F]
    (D : InfinitePlace F → ℝ)
    (h : ∀ u : (𝓞 F)ˣ, ∑ w : InfinitePlace F, Real.log (w ((u : 𝓞 F) : F)) * D w = 0) :
    ∃ c : ℝ, ∀ w, D w = c * (mult w : ℝ) := by
  classical
  have hsplit : ∀ f : InfinitePlace F → ℝ,
      ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)}, f v.1 = ∑ w, f w - f (w₀ : InfinitePlace F) := by
    intro f
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (w₀ : InfinitePlace F)), add_sub_cancel_right]
    exact (Finset.sum_subtype _ (fun w => by simp) f).symm
  let a : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ :=
    fun v => D v.1 / (mult v.1 : ℝ) - D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ)
  let φ : ({w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => ∑ v, x v * a v
      map_add' := fun x y => by simp [Finset.sum_add_distrib, add_mul]
      map_smul' := fun r x => by simp [Finset.mul_sum, mul_assoc] }
  have hφ : ∀ u : (𝓞 F)ˣ, φ (logEmbedding F (Additive.ofMul u)) = 0 := by
    intro u
    have e1 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
        Real.log (v.1 (algebraMap (𝓞 F) F u)) * D v.1
          = 0 - Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u)) * D (w₀ : InfinitePlace F) := by
      rw [← h u]
      exact hsplit (fun w => Real.log (w (algebraMap (𝓞 F) F u)) * D w)
    have e2 : ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
        (mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u))
          = 0 - (mult (w₀ : InfinitePlace F) : ℝ) * Real.log ((w₀ : InfinitePlace F) (algebraMap (𝓞 F) F u)) := by
      rw [← sum_mult_mul_log u]
      exact hsplit (fun w => (mult w : ℝ) * Real.log (w (algebraMap (𝓞 F) F u)))
    have hm0 : (mult (w₀ : InfinitePlace F) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
    show ∑ v, logEmbedding F (Additive.ofMul u) v * a v = 0
    simp only [logEmbedding_component]
    calc ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
          (mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u)) * a v
        = ∑ v : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)},
          (Real.log (v.1 (algebraMap (𝓞 F) F u)) * D v.1
            - D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ) * ((mult v.1 : ℝ) * Real.log (v.1 (algebraMap (𝓞 F) F u)))) := by
          apply Finset.sum_congr rfl
          intro v _
          have hm : (mult v.1 : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
          simp only [a]
          field_simp
          try ring
      _ = 0 := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2]
          field_simp
          try ring
  have hle : Submodule.span ℝ (unitLattice F : Set (logSpace F)) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨y, -, rfl⟩ := hx
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    exact hφ (Additive.toMul y)
  rw [unitLattice_span_eq_top F] at hle
  have ha : ∀ v, a v = 0 := by
    intro v
    have hv : (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) ∈ LinearMap.ker φ :=
      hle Submodule.mem_top
    rw [LinearMap.mem_ker] at hv
    have hφv : φ (Pi.single v (1 : ℝ)) = a v := by
      show ∑ v', (Pi.single v (1 : ℝ) : {w : InfinitePlace F // w ≠ (w₀ : InfinitePlace F)} → ℝ) v' * a v' = a v
      simp [Pi.single_apply]
    rw [← hφv]
    exact hv
  refine ⟨D (w₀ : InfinitePlace F) / (mult (w₀ : InfinitePlace F) : ℝ), fun w => ?_⟩
  have hm : (mult w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr mult_ne_zero
  by_cases hw : w = (w₀ : InfinitePlace F)
  · subst hw
    field_simp
  · have hv := ha ⟨w, hw⟩
    simp only [a, sub_eq_zero] at hv
    rw [← hv]
    field_simp

theorem sum_eq_mean_of_units :
    ∀ (F : Type) [Field F] [NumberField F] (d t : (F →+* ℂ) → ℝ),
      (∀ u : (𝓞 F)ˣ, ∑ σ : F →+* ℂ, Real.log ‖σ ((u : 𝓞 F) : F)‖ * d σ = 0) →
      (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) →
      ∑ σ : F →+* ℂ, t σ * d σ =
        (∑ σ : F →+* ℂ, t σ) / (Module.finrank ℚ F : ℝ) * ∑ σ : F →+* ℂ, d σ := by
  intro F _ _ d t hd ht
  classical
  have hfib : ∀ f : (F →+* ℂ) → ℝ, ∑ σ, f σ
      = ∑ w : InfinitePlace F, ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ :=
    fun f => (Finset.sum_fiberwise Finset.univ InfinitePlace.mk f).symm
  obtain ⟨c, hc⟩ := exists_eq_mul_mult_of_units F
    (fun w => ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), d σ) (by
      intro u
      have h1 := hd u
      rw [hfib] at h1
      refine Eq.trans ?_ h1
      apply Finset.sum_congr rfl
      intro w _
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hσ
      rw [InfinitePlace.apply])
  have ht' : ∀ σ : F →+* ℂ, t σ = t (InfinitePlace.mk σ).embedding := by
    intro σ
    have h2 : InfinitePlace.mk (InfinitePlace.mk σ).embedding = InfinitePlace.mk σ :=
      InfinitePlace.mk_embedding _
    rcases InfinitePlace.mk_eq_iff.mp h2 with h3 | h3
    · rw [h3]
    · have h4 := ht (InfinitePlace.mk σ).embedding
      rw [h3] at h4
      exact h4
  have hTfib : ∀ (w : InfinitePlace F) (f : (F →+* ℂ) → ℝ),
      ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), t σ * f σ
        = t w.embedding * ∑ σ ∈ Finset.univ.filter (fun σ => InfinitePlace.mk σ = w), f σ := by
    intro w f
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ hσ
    obtain ⟨-, rfl⟩ := Finset.mem_filter.mp hσ
    rw [← ht' σ]
  have hn : (Module.finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hsum_d : ∑ σ, d σ = c * (Module.finrank ℚ F : ℝ) := by
    rw [hfib, ← InfinitePlace.sum_mult_eq, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    exact hc w
  have hsum_t : ∑ σ, t σ = ∑ w : InfinitePlace F, t w.embedding * (w.mult : ℝ) := by
    rw [hfib]
    apply Finset.sum_congr rfl
    intro w _
    have h5 := hTfib w (fun _ => 1)
    simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h5
    rw [h5, InfinitePlace.card_filter_mk_eq]
  have hsum_td : ∑ σ, t σ * d σ = c * ∑ σ, t σ := by
    conv_lhs => rw [hfib]
    rw [hsum_t, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [hTfib w d]
    have h6 := hc w
    rw [h6]
    ring
  rw [hsum_td, hsum_d, div_mul_eq_mul_div, eq_div_iff hn]
  ring

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitConstant

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem notMem_mCoordIdeal_of_aeval_ne_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {h : MRing ι} (h0 : aeval y h ≠ 0) : h ∉ mCoordIdeal y := by
  intro hh
  apply h0
  have e := UnitChart.aeval_scaled y (fun _ => 1) h
  simp only [mul_one] at e
  rw [e, show mConeMap y h = 0 from hh, map_zero]

theorem exists_flatHerm_unit : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (α : (𝓞 F)ˣ), OverInt y φ → ∃ S : FlatHerm y φ (constLine (ι := ι) 0), S.M = 1 ∧ ∀ σ, S.κ σ = ‖σ ((α : 𝓞 F) : F)‖ := by
  intro K _ ι _ Ω _ F _ _ y φ α hO
  obtain ⟨hy, hR⟩ := hO
  choose c hc using id hy
  obtain ⟨m, G, hG, e⟩ := UnitChart.chart_form hc (hR c hc (α : 𝓞 F))
  have hα : ((α : 𝓞 F) : F) ≠ 0 := by
    simp
  have hφα : φ ((α : 𝓞 F) : F) ≠ 0 := (map_ne_zero φ).2 hα
  have hprod : (∏ k, y ⟨k, c k⟩ ^ m k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  have hg0 : aeval y (UnitChart.cMon c m) ≠ 0 := by rwa [UnitChart.aeval_cMon]
  have hG0 : aeval y G ≠ 0 := by rw [← e]; exact mul_ne_zero hφα hprod
  have e' : aeval y G = φ ((α : 𝓞 F) : F) * aeval y (UnitChart.cMon c m) := by
    rw [UnitChart.aeval_cMon, e]
  have hq : aeval y G / aeval y (UnitChart.cMon c m) = φ ((α : 𝓞 F) : F) := by
    rw [e', mul_div_cancel_right₀ _ hg0]
  have hinv : φ (((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = (φ ((α : 𝓞 F) : F))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← map_mul]
    have : (((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ((α : 𝓞 F) : F) = 1 := by
      have h1 : ((α⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * (α : 𝓞 F) = 1 := α.inv_mul
      have h2 := congrArg (algebraMap (𝓞 F) F) h1
      rw [map_mul, map_one] at h2
      exact h2
    rw [this, map_one]
  have hfn := notMem_mCoordIdeal_of_aeval_ne_zero hG0
  have hgn := notMem_mCoordIdeal_of_aeval_ne_zero hg0
  refine ⟨{ M := 1
            M_pos := one_pos
            f := G
            g := UnitChart.cMon c m
            df := m
            dg := m
            hf := hG
            hg := UnitChart.homog_cMon c m
            deg := fun k => by simp [constLine, HermLine.ofWeight]
            f_ne := hfn
            g_ne := hgn
            unit := ?_
            κ := fun σ => ‖σ ((α : 𝓞 F) : F)‖
            κ_pos := fun σ => norm_pos_iff.2 ((map_ne_zero σ).2 hα)
            κ_conj := fun σ => by simp [ComplexEmbedding.conjugate_coe_eq]
            norm := ?_ }, rfl, fun _ => rfl⟩
  · rw [isUnitSec_iff_chart K ι Ω y G _ m m hy hG (UnitChart.homog_cMon c m) hfn hgn]
    intro c' hc'
    simp only [sub_self, neg_zero, zpow_zero, Finset.prod_const_one, mul_one, hq]
    exact ⟨hR c' hc' _, hinv ▸ hR c' hc' _⟩
  · intro σ z hz
    rw [hz.2 _ m G _ hG (UnitChart.homog_cMon c m) e', norm_mul]
    simp [constLine, HermLine.ofWeight]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitConstantStatement

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.flat_herm_unit_constant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (α : (𝓞 F)ˣ), OverInt y φ → ∃ S : FlatHerm y φ (constLine (ι := ι) 0), S.M = 1 ∧ ∀ σ, S.κ σ = ‖σ ((α : 𝓞 F) : F)‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_flatHerm_unit <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyPlaceWeight

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem constLine_zero_tensor {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    (constLine (ι := ι) 0).tensor (constLine 0) = constLine 0 := by
  simp [HermLine.tensor, constLine, HermLine.ofWeight]

theorem ptsIntegral_eq_mean : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (d : ℕ) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) → (∀ σ z, PtOver y φ σ z → u z = t σ) → ptsIntegral W (pot L) u = meanEmb t * ptsIntegral W (pot L) (fun _ => 1) := by
  intro hPI K _ ι _ Ω _ F _ _ y φ I W n L d t u hI hd hO hle hW hL ht hu
  have hex := fun σ : F →+* ℂ => GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (Set.indicator {σ} 1) hO
  choose χ hχ _ using hex
  have hsplit : ∀ (t' : (F →+* ℂ) → ℝ) (u' : ((Σ k, ι k) → ℂ) → ℝ),
      (∀ σ z, PtOver y φ σ z → u' z = t' σ) →
      ptsIntegral W (pot L) u' = ∑ σ : F →+* ℂ, t' σ * ptsIntegral W (pot L) (χ σ) :=
    fun t' u' h => GlobalTheory.T.green_current_integral_formula hPI K ι Ω F y φ W n L t' u' χ hO hle hW hL h hχ
  have hc : IsSmoothHerm (constLine (ι := ι) 0) := contDiffOn_const
  have hzero : I W (n + 1) (Fin.snoc L (constLine 0)) = 0 := by
    have h := hI.2.1 W n L (constLine 0) (constLine 0) hW hL hc hc
    rw [constLine_zero_tensor] at h
    linarith
  have hunit : ∀ α : (𝓞 F)ˣ,
      ∑ σ : F →+* ℂ, Real.log ‖σ ((α : 𝓞 F) : F)‖ * ptsIntegral W (pot L) (χ σ) = 0 := by
    intro α
    obtain ⟨S, -, hκ⟩ := GlobalTheory.T.flat_herm_unit_constant K ι Ω F y φ α hO
    obtain ⟨v, hv, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (fun σ => Real.log (S.κ σ)) hO
    have h1 := GlobalTheory.T.intersection_family_flat_twist K ι Ω F y φ I W n L (constLine 0) S d v hI hd hO hle hW hL hc hv
    have h2 := hsplit (fun σ => Real.log (S.κ σ)) v fun σ z hz => (hv.near σ z hz).self_of_nhds
    simp only [hκ] at h2
    linarith
  have hmain := sum_eq_mean_of_units F (fun σ => ptsIntegral W (pot L) (χ σ)) t hunit ht
  have hone := hsplit (fun _ => 1) (fun _ => 1) fun _ _ _ => rfl
  simp only [one_mul] at hone
  rw [hsplit t u hu, hone, hmain]
  rfl

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyPlaceWeightStatement

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.intersection_family_place_weight : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (d : ℕ) (t : (F →+* ℂ) → ℝ) (u : ((Σ k, ι k) → ℂ) → ℝ), IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W → IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ σ, t (ComplexEmbedding.conjugate σ) = t σ) → (∀ σ z, PtOver y φ σ z → u z = t σ) → ptsIntegral W (pot L) u = meanEmb t * ptsIntegral W (pot L) (fun _ => 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_eq_mean | exact GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_eq_mean | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ptsIntegral_eq_mean <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionFamilyFlatHerm

section

@[expose] public section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem FlatHerm.inter_eq : PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω)
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (W : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ),
    IsIntersectionFamily I → IsArithVar (mCoordIdeal y) d → OverInt y φ → mCoordIdeal y ≤ W →
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    I W (n + 1) (Fin.snoc L A) = S.ht * ptsIntegral W (pot L) (fun _ => 1) := by
  intro hP K _ ι _ Ω _ F _ _ y φ I W n L A S d hI hY hO hyW hW hL hA
  obtain ⟨u, hu, -⟩ := GlobalTheory.T.exists_place_weight_conj_invariant K ι Ω F y φ (fun σ => Real.log (S.κ σ)) hO
  rw [GlobalTheory.T.intersection_family_flat_twist K ι Ω F y φ I W n L A S d u hI hY hO hyW hW hL hA hu,
    GlobalTheory.T.intersection_family_place_weight hP K ι Ω F y φ I W n L d (fun σ => Real.log (S.κ σ)) u hI hY hO hyW hW hL
      (fun σ => congrArg Real.log (S.κ_conj σ)) (fun σ z hz => (hu.near σ z hz).self_of_nhds),
    FlatHerm.ht, neg_mul]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
