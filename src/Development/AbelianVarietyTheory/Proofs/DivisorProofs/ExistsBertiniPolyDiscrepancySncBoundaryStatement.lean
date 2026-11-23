module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniCoordinateStrataEtaleChartCotangentStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDivisorEquation
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
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyLtAdaptedCoordsIndependentFunctionStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartSingleEquationStatement

-- Source module: Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.SncChartDivisorEquationStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
theorem _root_.GlobalTheory.T.snc_chart_divisor_equation : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ D : CartierDiv Y, D.supp ≤ B → D.IsEqn y (∏ j ∈ J, u j ^ D.mult (w j)) := by
  first | exact @_root_.GlobalTheory.Discrepancy.IsSncChart.isEqn_monomial | exact _root_.GlobalTheory.Discrepancy.IsSncChart.isEqn_monomial | (intros; apply _root_.GlobalTheory.Discrepancy.IsSncChart.isEqn_monomial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyEqFormOrderSubWeightedCoordOrders

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem DivOver.ord_zpow_int {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (f : X.functionFieldˣ) (r : ℤ) : E.ord (f ^ r) = r * E.ord f := by
  obtain ⟨m, rfl | rfl⟩ := r.eq_nat_or_neg
  · rw [zpow_natCast, E.ord_pow]
  · rw [zpow_neg, zpow_natCast, E.ord_inv, E.ord_pow]; ring

theorem DivOver.ord_finsetProd_zpow {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (E : DivOver p) {ι : Type} (s : Finset ι) (f : ι → X.functionFieldˣ)
    (e : ι → ℤ) : E.ord (∏ j ∈ s, f j ^ e j) = ∑ j ∈ s, e j * E.ord (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, E.ord_mul, ih, E.ord_zpow_int]

theorem DivOver.ord_eq_zero_of_unitAt_through {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    {p : X ⟶ Sp k} (E : DivOver p) {y : X} (hE : E.Through y) (v : X.functionFieldˣ)
    (h : UnitAt y (v : X.functionField)) : E.ord v = 0 := by
  obtain ⟨a, ha, e⟩ := h
  have h1 : (v : X.functionField) ∈ E.ring := hE _ ⟨a, e⟩
  have h2 : ((v⁻¹ : X.functionFieldˣ) : X.functionField) ∈ E.ring := by
    refine hE _ ⟨(ha.unit⁻¹ : (X.presheaf.stalk y)ˣ), ?_⟩
    rw [Units.val_inv_eq_inv_val, ← e]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  have a1 := (E.ord_nonneg_iff v).2 h1
  have a2 := (E.ord_nonneg_iff v⁻¹).2 h2
  rw [E.ord_inv] at a2
  omega

end GlobalTheory.Discrepancy

namespace GlobalTheory.Discrepancy

theorem IsSncChart.discrep_eq_formOrd_sub_sum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (g : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → (Θ + m • K).IsEqn y g → ∀ E : DivOver q, E.Through y → discrep E η m g = ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * E.ord (u j) := by
  intro Y _ _ q n _ B y U hy z J w u hc η K Θ m g hη hK hm hΘ hg E hE
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen ℂ _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)
  set ω := formOf U (gen_mem hy) (dOn q z) with hω
  have hgen := isFreeGen_formOf (gen_mem hy) hc.frame
  have h0 : ω ≠ 0 := fun h =>
    one_ne_zero (hgen.1 (a₁ := 1) (a₂ := 0) (by simp [← hω, h]))
  obtain ⟨c, hcη⟩ := hgen.2 η
  have hc0 : c ≠ 0 := fun h => hη (by rw [← hcη]; simp [h])
  set k0 : Y.functionFieldˣ := Units.mk0 c hc0 with hk0
  have hηk : η = (k0 : Y.functionField) • ω := by rw [hk0, Units.val_mk0]; exact hcη.symm
  have hKy : K.IsEqn y k0 := hK U (dOn q z) hc.frame y hy k0 hηk
  have hΘy := GlobalTheory.T.snc_chart_divisor_equation ℂ Y q n B y U hy z J w u hc Θ hΘ
  set M : Y.functionFieldˣ := ∏ j ∈ J, u j ^ Θ.mult (w j) with hM
  have hsum : (Θ + m • K).IsEqn y (M * k0 ^ m) := hΘy.add (hKy.nsmul m)
  set v : Y.functionFieldˣ := g * (M * k0 ^ m)⁻¹ with hv
  have hvu : UnitAt y (v : Y.functionField) := by
    have := hsum.iff_unitAt.1 hg
    rwa [hv, Units.val_mul, Units.val_inv_eq_inv_val, ← div_eq_mul_inv]
  have hv0 : E.ord v = 0 := E.ord_eq_zero_of_unitAt_through hE v hvu
  have hvo : E.ord v = E.ord g - (E.ord M + m * E.ord k0) := by
    rw [hv, E.ord_mul, E.ord_inv, E.ord_mul, E.ord_pow]; ring
  have hMo : E.ord M = ∑ j ∈ J, Θ.mult (w j) * E.ord (u j) := by
    rw [hM, E.ord_finsetProd_zpow]
  have hordg : E.ord g = ∑ j ∈ J, Θ.mult (w j) * E.ord (u j) + m * E.ord k0 := by
    rw [← hMo]; omega
  have hform : E.formOrd η = E.ord k0 + E.formOrd ω := by
    rw [hηk]; exact E.formOrd_smul hn h0 k0
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [discrep, hform, hordg]
  push_cast
  have hs : ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * (E.ord (u j) : ℚ) =
      (∑ j ∈ J, (Θ.mult (w j) : ℚ) * E.ord (u j)) / m := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun j _ => div_mul_eq_mul_div _ _ _
  rw [hs]
  unfold DivOver.formOrd
  field_simp
  ring

end GlobalTheory.Discrepancy
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyEqFormOrderSubWeightedCoordOrdersStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.discrepancy_eq_formOrder_sub_weighted_coordOrders : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (g : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → (Θ + m • K).IsEqn y g → ∀ E : DivOver q, E.Through y → discrep E η m g = ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, ((Θ.mult (w j) : ℚ) / m) * E.ord (u j) := by
  first | exact @GlobalTheory.Discrepancy.IsSncChart.discrep_eq_formOrd_sub_sum | exact GlobalTheory.Discrepancy.IsSncChart.discrep_eq_formOrd_sub_sum | (intros; apply GlobalTheory.Discrepancy.IsSncChart.discrep_eq_formOrd_sub_sum <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBertiniPolyDiscrepancySncBoundary

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Discrepancy

theorem exists_mvPolynomial_of_forall_nhds {X : Type} [TopologicalSpace X] [CompactSpace X]
    {ι : Type} (P : (ι → ℂ) → X → Prop)
    (h : ∀ x₀ : X, ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧
      ∀ c, MvPolynomial.eval c Q ≠ 0 → ∀ x ∈ W, P c x) :
    ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ c, MvPolynomial.eval c Q ≠ 0 → ∀ x, P c x := by
  classical
  choose W hW hxW Q hQ hP using h
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  refine ⟨∏ x ∈ t, Q x, Finset.prod_ne_zero_iff.2 fun x _ => hQ x, fun c hc y => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  rw [map_prod] at hc
  exact hP x c (Finset.prod_ne_zero_iff.1 hc x hx) y hy

theorem exists_poly_neg_one_lt_discrep_member : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) [Fintype ι] (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : Y.functionFieldˣ, (t : Y.functionField) = ∑ i, Cartier.constFn q (u i) * s i → ∀ y : Y, (∃ i, A.GeneratesAt y (s i)) → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (c : ℚ) (g f : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → c < 1 → (∀ w, w ⤳ y → Θ.mult w < m) → (Θ + m • K).IsEqn y g → (GlobalTheory.Cartier.CartierDiv.principal t + A).IsEqn y f → ∀ E : DivOver q, E.Through y → -1 < discrep E η m g - c * E.ord f := by
  intro Y _ _ q n _ hproj B hB A ι _ s hs
  haveI : IsProper q := ((isProjOver_iff_isProper_and_exists_isAmpleLB q).1 hproj).1
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace q
  refine (exists_mvPolynomial_of_forall_nhds (X := Y) (fun c y =>
    ∀ t : Y.functionFieldˣ, (t : Y.functionField) = ∑ i, Cartier.constFn q (c i) * s i →
    (∃ i, A.GeneratesAt y (s i)) → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (c' : ℚ)
      (g f : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → c' < 1 →
      (∀ w, w ⤳ y → Θ.mult w < m) → (Θ + m • K).IsEqn y g →
      (GlobalTheory.Cartier.CartierDiv.principal t + A).IsEqn y f → ∀ E : DivOver q, E.Through y →
      -1 < discrep E η m g - c' * E.ord f) fun y₀ => ?_).imp
    fun Q ⟨hQ, hQc⟩ => ⟨hQ, fun c hc t ht y => hQc c hc y t ht⟩
  obtain ⟨W, hW, z, w, u, e, f, hfr, he, hf, hch⟩ := GlobalTheory.T.exists_affine_snc_chart_cartier_single_equation Y q n B hB A ι s hs y₀
  obtain ⟨Q, hQ, hQc⟩ := GlobalTheory.T.bertini_coordinateStrata_etaleChart_cotangent Y q n W z hfr ι f
  refine ⟨W, W.isOpen, hW, Q, hQ, fun c hc y hy t ht hgen η K Θ m c' g f' hη hK hm hΘ hc' hmult
    hg hf' E hE => ?_⟩
  obtain ⟨J, hJ, hJz⟩ := hch y hy
  have hFv : fnOf W (gen_mem hy) (∑ i, algX q W (c i) * f i) = ((t * e : Y.functionFieldˣ) : Y.functionField) := by

    rw [Units.val_mul, ht, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hf i, ← RingHom.comp_apply, fnOf_comp_algX, mul_assoc]
  have hunit : UnitAt y ((f' : Y.functionField) / ((t * e : Y.functionFieldˣ) : Y.functionField)) :=
    ((CartierDiv.isEqn_principal t y).add (he y hy)).iff_unitAt.1 hf'
  have hbas : ∃ i, y ∈ Y.basicOpen (f i) := by
    obtain ⟨i, hi⟩ := hgen
    refine ⟨i, (unitAt_fnOf_iff hy (gen_mem hy) (f i)).1 ?_⟩
    rw [hf i]
    exact (he y hy).generatesAt_iff.1 hi
  rw [GlobalTheory.T.discrepancy_eq_formOrder_sub_weighted_coordOrders Y q n B y W hy z J w u hJ η K Θ m g hη hK hm hΘ hg E hE]
  exact GlobalTheory.T.discrepancy_lt_adaptedCoords_independent_function Y q n B y W hy z J w u hJ hJz _ (fun h => hQc c hc y hy hbas J h) (t * e) f'
    (fun j => (Θ.mult (w j) : ℚ) / m) c' hFv.symm hunit (fun j hj => by
      have := hmult (w j) (hJ.spec j hj)
      have hm' : (0 : ℚ) < m := by exact_mod_cast hm
      rw [div_lt_one hm']
      exact_mod_cast this) hc' E hE

end GlobalTheory.Discrepancy
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBertiniPolyDiscrepancySncBoundaryStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.exists_bertini_poly_discrepancy_snc_boundary : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], IsProjOver q → ∀ (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ (A : CartierDiv Y) (ι : Type) [Fintype ι] (s : ι → Y.functionField), (∀ i, s i ∈ A.sections) → ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ t : Y.functionFieldˣ, (t : Y.functionField) = ∑ i, Cartier.constFn q (u i) * s i → ∀ y : Y, (∃ i, A.GeneratesAt y (s i)) → ∀ (η : RatForms q n) (K Θ : CartierDiv Y) (m : ℕ) (c : ℚ) (g f : Y.functionFieldˣ), η ≠ 0 → IsDivOfForm K η → 0 < m → Θ.supp ≤ B → c < 1 → (∀ w, w ⤳ y → Θ.mult w < m) → (Θ + m • K).IsEqn y g → (GlobalTheory.Cartier.CartierDiv.principal t + A).IsEqn y f → ∀ E : DivOver q, E.Through y → -1 < discrep E η m g - c * E.ord f := by
  first | exact @GlobalTheory.Discrepancy.exists_poly_neg_one_lt_discrep_member | exact GlobalTheory.Discrepancy.exists_poly_neg_one_lt_discrep_member | (intros; apply GlobalTheory.Discrepancy.exists_poly_neg_one_lt_discrep_member <;> assumption)
end
end
