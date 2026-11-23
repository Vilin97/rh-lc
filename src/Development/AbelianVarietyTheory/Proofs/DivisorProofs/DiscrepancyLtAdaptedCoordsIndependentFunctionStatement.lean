module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentImagesLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModificationLineBundleGlobalSectionsDimPullEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import Mathlib.Tactic.Basify
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RingKrullDimOfEtaleMvPolynomial
import Mathlib.Tactic.Polynomial.Basic

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameFormsResidueIndependence

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndepDiscrep

theorem neg_one_lt_formOrd_sub_sum : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], topologicalKrullDim Y = n → ∀ (y : Y) (U : Y.Opens) (hy : y ∈ U) (ω : FormsOn q n U), IsFrame ω → ∀ (J : Type) [Fintype J] (a : J → Y.presheaf.stalk y) (ha : ∀ j, a j ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) (v : J → Y.functionFieldˣ) (c : J → ℚ), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨a j, ha j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) → (∀ j, (v j : Y.functionField) = algebraMap (Y.presheaf.stalk y) Y.functionField (a j)) → (∀ j, c j < 1) → ∀ E : DivOver q, E.Through y → -1 < ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) ω) : ℚ) - ∑ j, c j * E.ord (v j) := by
  classical
  intro Y _ _ q n _ hn y U hy ω hω J _ a ha v c hind hv hc E hE
  haveI := SmoothOfRelativeDimension.smooth n q
  haveI : GlobalTheory.IsNormalScheme Y := GlobalTheory.ModifSections.isNormalScheme_of_smooth q
  obtain ⟨U', hy', z, e, he, hze, hz⟩ :=
    GlobalTheory.AdaptedFrame.exists_adapted_frame (p := q) (n := n) y a ha hind
  have h0 : formOf U (gen_mem hy) ω ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy) hω).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have h0' : formOf U' (gen_mem hy') (dOn q z) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy') hz).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  obtain ⟨f, hf⟩ := (isFreeGen_formOf (gen_mem hy') hz).2 (formOf U (gen_mem hy) ω)
  have hf0 : f ≠ 0 := fun h => h0 (by rw [← hf, h]; exact zero_smul _ _)
  set u : Y.functionFieldˣ := Units.mk0 f hf0 with hu
  have hfu : ((u : Y.functionField) • formOf U' (gen_mem hy') (dOn q z)) = formOf U (gen_mem hy) ω :=
    by rw [hu, Units.val_mk0]; exact hf
  have hF (Fd : DivOver q) : Fd.formOrd (formOf U (gen_mem hy) ω) =
      Fd.ord u + Fd.formOrd (formOf U' (gen_mem hy') (dOn q z)) := by
    rw [← Fd.formOrd_smul hn h0' u, hfu]
  have h0z : ∀ w, w ⤳ y → ∀ Fd : DivOver q, Fd.IsAt w → Fd.ord u = 0 := by
    intro w hw Fd hFd
    have h1 := hF Fd
    have a1 := DivOver.formOrd_formOf_eq_zero (hw.mem_open U.isOpen hy) hFd hω
    have a2 := DivOver.formOrd_formOf_eq_zero (hw.mem_open U'.isOpen hy') hFd hz
    rw [a1, a2] at h1
    omega
  have reg : ∀ w : Y.functionFieldˣ,
      (∀ x, x ⤳ y → ∀ Fd : DivOver q, Fd.IsAt x → 0 ≤ Fd.ord w) → 0 ≤ E.ord w := fun w hw =>
    (E.ord_nonneg_iff w).2 (hE _ (regAt_of_forall_coheight_eq_one fun x hx h1 =>
      have ⟨Fd, hFd⟩ := DivOver.exists_isAt_of_coheight_eq_one (p := q) h1
      (hFd _).1 ((Fd.ord_nonneg_iff w).1 (hw x hx Fd hFd))))
  have hu1 := reg u fun x hx Fd hFd => (h0z x hx Fd hFd).ge
  have hu2 := reg u⁻¹ fun x hx Fd hFd => by rw [Fd.ord_inv, h0z x hx Fd hFd, neg_zero]
  rw [E.ord_inv] at hu2
  have hu0 : E.ord u = 0 := by omega
  have hA := DivOver.sum_ord_sub_one_le_formOrd_dOn hn E hy' hE z h0' e he v fun j => by
    rw [hv, ← hze j, algebraMap_germ]
  have hN := DivOver.formOrd_formOf_nonneg hn hy' hE (dOn q z) h0'
  have hnn : ∀ j, 0 ≤ E.ord (v j) := fun j => (E.ord_nonneg_iff _).2 (hE _ ⟨a j, (hv j).symm⟩)
  change -1 < (E.formOrd (formOf U (gen_mem hy) ω) : ℚ) - ∑ j, c j * E.ord (v j)
  rw [hF E, hu0, zero_add]
  have hAq : (∑ j, (E.ord (v j) : ℚ)) - 1 ≤ (E.formOrd (formOf U' (gen_mem hy') (dOn q z)) : ℚ) := by
    exact_mod_cast hA
  have hNq : (0 : ℚ) ≤ (E.formOrd (formOf U' (gen_mem hy') (dOn q z)) : ℚ) := by exact_mod_cast hN
  have hle : ∀ j, c j * (E.ord (v j) : ℚ) ≤ E.ord (v j) := fun j => by
    have : (0 : ℚ) ≤ E.ord (v j) := by exact_mod_cast hnn j
    nlinarith [hc j]
  by_cases h : ∃ j, 0 < E.ord (v j)
  · obtain ⟨j, hj⟩ := h
    have hlt : ∑ j, c j * (E.ord (v j) : ℚ) < ∑ j, (E.ord (v j) : ℚ) :=
      Finset.sum_lt_sum (fun j _ => hle j) ⟨j, Finset.mem_univ _, by
        have : (0 : ℚ) < E.ord (v j) := by exact_mod_cast hj
        nlinarith [hc j]⟩
    linarith
  · push_neg at h
    have h' : ∀ j, E.ord (v j) = 0 := fun j => le_antisymm (h j) (hnn j)
    simp only [h', Int.cast_zero, mul_zero, Finset.sum_const_zero, sub_zero]
    linarith

end GlobalTheory.IndepDiscrep
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartKltCriterion

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem IsSncChart.neg_one_lt_formOrd_sub_sum : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (E : DivOver q), E.Through y → ∀ a : Fin n → ℚ, ((∀ j ∈ J, a j < 1) → -1 < ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) ∧ ((∀ j ∈ J, a j ≤ 1) → -1 ≤ ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) := by
  intro k _ _ Y _ _ q n _ B y U hy z J w u hc E hE a
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen k _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)
  have h0 : formOf U (gen_mem hy) (dOn q z) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy) hc.frame).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have hnn : ∀ j ∈ J, 0 ≤ E.ord (u j) := fun j hj =>
    (E.ord_nonneg_iff _).2 (by rw [hc.val j hj]; exact hE _ (regAt_fnOf hy _ (z j)))
  have hA := DivOver.sum_ord_sub_one_le_formOrd_dOn hn E hy hE z h0 (J := {j // j ∈ J})
    Subtype.val Subtype.val_injective (fun j => u j.1) fun j => hc.val j.1 j.2
  rw [Finset.sum_coe_sort J (fun j => E.ord (u j))] at hA
  have hF := DivOver.formOrd_formOf_nonneg hn hy hE (dOn q z) h0
  set F := E.formOrd (formOf U (gen_mem hy) (dOn q z))
  have hAq : ∑ j ∈ J, (E.ord (u j) : ℚ) - 1 ≤ F := by exact_mod_cast hA
  have hFq : (0 : ℚ) ≤ F := by exact_mod_cast hF
  have hnq : ∀ j ∈ J, (0 : ℚ) ≤ E.ord (u j) := fun j hj => by exact_mod_cast hnn j hj
  have hle : (∀ j ∈ J, a j ≤ 1) → ∀ j ∈ J, a j * (E.ord (u j) : ℚ) ≤ E.ord (u j) :=
    fun ha j hj => by nlinarith [ha j hj, hnq j hj]
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · change -1 < (F : ℚ) - ∑ j ∈ J, a j * E.ord (u j)
    by_cases hz : ∀ j ∈ J, (E.ord (u j) : ℚ) = 0
    · rw [Finset.sum_eq_zero fun j hj => by rw [hz j hj, mul_zero]]
      linarith
    · push Not at hz
      obtain ⟨j, hj, hj0⟩ := hz
      have hpos : (0 : ℚ) < E.ord (u j) := lt_of_le_of_ne (hnq j hj) hj0.symm
      have := Finset.sum_lt_sum (hle fun j hj => (ha j hj).le)
        ⟨j, hj, by nlinarith [ha j hj]⟩
      linarith
  · change -1 ≤ (F : ℚ) - ∑ j ∈ J, a j * E.ord (u j)
    have := Finset.sum_le_sum (hle ha)
    linarith

end GlobalTheory.Discrepancy
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyLtAdaptedCoordsIndependentFunction

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → (∀ j ∈ J, y ∉ Y.basicOpen (z j)) → ∀ F : Γ(Y, U), (∀ h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨Y.presheaf.germ U y hy (j.elim F fun j => z j), h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y)))) → ∀ (φ f : Y.functionFieldˣ) (a : Fin n → ℚ) (c : ℚ), (φ : Y.functionField) = fnOf U (gen_mem hy) F → UnitAt y ((f : Y.functionField) / φ) → (∀ j ∈ J, a j < 1) → c < 1 → ∀ E : DivOver q, E.Through y → -1 < ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j) - c * E.ord f := by
  intro Y _ _ q n _ B y U hy z J w u hc hJ F hind φ f a c hφ hf ha hc1 E hE
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

  have hunit : ∀ g : Y.functionFieldˣ, UnitAt y (g : Y.functionField) → E.ord g = 0 := by
    rintro g ⟨b, hb, hbg⟩
    have h1 : (g : Y.functionField) ∈ E.ring := hE _ ⟨b, hbg⟩
    have h2 : ((g⁻¹ : Y.functionFieldˣ) : Y.functionField) ∈ E.ring := hE _ ⟨↑(hb.unit⁻¹), by
      rw [map_units_inv, IsUnit.unit_spec, hbg]; simp⟩
    have e1 := (E.ord_nonneg_iff g).2 h1
    have e2 := (E.ord_nonneg_iff _).2 h2
    rw [E.ord_inv] at e2
    omega
  have hfφ : E.ord f = E.ord φ := by
    have hg : UnitAt y ((f * φ⁻¹ : Y.functionFieldˣ) : Y.functionField) := by
      simpa [div_eq_mul_inv] using hf
    have h0 := hunit _ hg
    have : f = (f * φ⁻¹) * φ := by group
    rw [this, E.ord_mul, h0, zero_add]
  by_cases hyF : y ∈ Y.basicOpen F
  · have hφu : UnitAt y (φ : Y.functionField) := hφ ▸ (unitAt_fnOf_iff hy _ F).2 hyF
    have hfu : UnitAt y (f : Y.functionField) := by
      have := UnitAt.mul hf hφu
      rwa [div_mul_cancel₀ _ φ.ne_zero] at this
    have h0 := hunit f hfu
    have key := (IsSncChart.neg_one_lt_formOrd_sub_sum ℂ Y q n B y U hy z J w u hc E hE a).1 ha
    rw [h0]
    simpa using key
  · have hmax : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈
        IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
      rintro (_ | ⟨j, hj⟩)
      · exact (IsLocalRing.mem_maximalIdeal _).2
          (mem_nonunits_iff.2 fun h => hyF ((Scheme.mem_basicOpen Y F y hy).2 h))
      · exact (IsLocalRing.mem_maximalIdeal _).2
          (mem_nonunits_iff.2 fun h => hJ j hj ((Scheme.mem_basicOpen Y (z j) y hy).2 h))
    have hv : ∀ j : Option J, ((j.elim φ fun j => u j : Y.functionFieldˣ) : Y.functionField) =
        algebraMap (Y.presheaf.stalk y) Y.functionField
          (Y.presheaf.germ U y hy (j.elim F fun j => z j)) := by
      rintro (_ | ⟨j, hj⟩)
      · simp only [Option.elim]
        rw [hφ, algebraMap_germ]
      · simp only [Option.elim]
        rw [hc.val j hj, algebraMap_germ]
    have hc' : ∀ j : Option J, (j.elim c fun j => a j) < 1 := by
      rintro (_ | ⟨j, hj⟩)
      · exact hc1
      · exact ha j hj
    have key := GlobalTheory.IndepDiscrep.neg_one_lt_formOrd_sub_sum Y q n hn y U hy (dOn q z) hc.frame
      (Option J) (fun j => Y.presheaf.germ U y hy (j.elim F fun j => z j)) hmax
      (fun j => j.elim φ fun j => u j) (fun j => j.elim c fun j => a j) (hind hmax) hv hc' E hE
    rw [Fintype.sum_option] at key
    simp only [Option.elim] at key
    rw [Finset.sum_coe_sort J (fun j => a j * (E.ord (u j) : ℚ))] at key
    rw [hfφ]
    linarith

end GlobalTheory.Discrepancy
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscrepancyLtAdaptedCoordsIndependentFunctionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.discrepancy_lt_adaptedCoords_independent_function : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → (∀ j ∈ J, y ∉ Y.basicOpen (z j)) → ∀ F : Γ(Y, U), (∀ h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim F fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨Y.presheaf.germ U y hy (j.elim F fun j => z j), h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y)))) → ∀ (φ f : Y.functionFieldˣ) (a : Fin n → ℚ) (c : ℚ), (φ : Y.functionField) = fnOf U (gen_mem hy) F → UnitAt y ((f : Y.functionField) / φ) → (∀ j ∈ J, a j < 1) → c < 1 → ∀ E : DivOver q, E.Through y → -1 < ((fun ω => @dite ℤ (∃ a, E.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j) - c * E.ord f := by
  first | exact @GlobalTheory.Discrepancy.IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep | exact GlobalTheory.Discrepancy.IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep | (intros; apply GlobalTheory.Discrepancy.IsSncChart.neg_one_lt_formOrd_sub_sum_sub_ord_of_indep <;> assumption)
end
end
