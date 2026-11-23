module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismProjSpaceBasepointFreeSectionsStatement
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
import Mathlib.Tactic.Basify
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
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveSpaceOrderArithVarietyFubiniStudyDegreStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeGenericPointEqFinrankQuotientsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionQuotientsTranscendenceBasisBasepointFreeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotientSubfieldEqMulRankOrder

section

@[expose] public section

open GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem finrank_ratF_eq_mul_rank (k K : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [Field K] [CharZero K]
    (ι : k →+* K) (D : ℕ) (x : Fin (D + 1) → K) (hι : Function.Injective ι)
    (hy : AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0)) :
    Module.finrank (ratF x) K = Module.finrank (Subfield.closure (Set.range ι ∪ Set.range fun j : Fin D => x j.succ / x 0)) K * Module.finrank ℤ k ∧ Function.Injective (MvPolynomial.eval₂Hom ι fun j : Fin D => x j.succ / x 0) := by
  classical
  set y : Fin D → K := fun j => x j.succ / x 0 with hydef
  letI : Algebra k K := ι.toAlgebra
  have hyk : AlgebraicIndependent k y := hy.extendScalars_of_isIntegral k
  have hinj : Function.Injective (MvPolynomial.eval₂Hom ι y) := hyk
  refine ⟨?_, hinj⟩
  haveI : CharZero k := ι.charZero
  haveI : Module.Free ℤ k := Module.free_of_finite_type_torsion_free'
  set F : Subfield K := ratF x with hF
  have hyF : ∀ j, y j ∈ F := fun j => Subfield.subset_closure ⟨j, rfl⟩
  set n := Module.finrank ℤ k with hn
  let b := Module.finBasis ℤ k
  set R : Subring K := Subring.closure (Set.range y) with hRdef
  have hR : R ≤ (MvPolynomial.eval₂Hom (Int.castRingHom K) y).range :=
    (Subring.closure_le).2 (by rintro _ ⟨j, rfl⟩; exact ⟨MvPolynomial.X j, by simp⟩)
  have hli : LinearIndependent F (fun i => ι (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i₀
    have hg' : ∑ i, (g i : K) * ι (b i) = 0 := hg
    have hfrac : ∀ i, ∃ a ∈ R, ∃ c ∈ R, c ≠ 0 ∧ (g i : K) = a / c := by
      intro i
      obtain ⟨a, ha, c, hc, e⟩ := Subfield.mem_closure_iff.1 (g i).2
      by_cases h0 : c = 0
      · exact ⟨0, R.zero_mem, 1, R.one_mem, one_ne_zero, by rw [← e, h0, div_zero, zero_div]⟩
      · exact ⟨a, ha, c, hc, h0, e.symm⟩
    choose a ha c hc hc0 hgac using hfrac
    set Q : K := ∏ j, c j with hQdef
    have hQ : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hc0 j
    have hp : ∀ i, Q * (g i : K) = a i * ∏ j ∈ Finset.univ.erase i, c j := by
      intro i
      rw [hgac i, hQdef, ← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i)]
      field_simp [hc0 i]
    have hpR : ∀ i, Q * (g i : K) ∈ R := fun i => by
      rw [hp i]; exact R.mul_mem (ha i) (Subring.prod_mem _ fun j _ => hc j)
    choose P hP using fun i => hR (hpR i)
    have hsum : ∑ i, Q * (g i : K) * ι (b i) = 0 := by
      simp_rw [mul_assoc, ← Finset.mul_sum, hg', mul_zero]
    have hcomp : ι.comp (Int.castRingHom k) = Int.castRingHom K := RingHom.ext_int _ _
    have hev : MvPolynomial.eval₂Hom ι y
        (∑ i, MvPolynomial.C (b i) * MvPolynomial.map (Int.castRingHom k) (P i)) = 0 := by

      simp only [map_sum, map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_map_hom, hcomp, hP]
      refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
      ring
    have hP0 := hinj (hev.trans (map_zero _).symm)
    have hPi : ∀ i, P i = 0 := by
      intro i
      ext m
      have hm := congrArg (AddMonoidAlgebra.coeff · m) hP0
      simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
        MvPolynomial.coeff_zero, Finsupp.zero_apply, eq_intCast] at hm
      have hm' : ∑ j, AddMonoidAlgebra.coeff (P j) m • b j = 0 := by
        rw [← hm]; refine Finset.sum_congr rfl fun j _ => ?_
        rw [zsmul_eq_mul, mul_comm]
      rw [MvPolynomial.coeff_zero]
      exact Fintype.linearIndependent_iff.1 b.linearIndependent _ hm' i
    have h1 : Q * (g i₀ : K) = 0 := by rw [← hP i₀, hPi i₀, map_zero]
    exact Subtype.ext ((mul_eq_zero.1 h1).resolve_left hQ)
  have hV : Module.finrank F (Submodule.span F (Set.range fun i => ι (b i))) = n := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  let E : IntermediateField F K := IntermediateField.adjoin F (Set.range ι)
  have halg : ∀ z ∈ Set.range ι, IsAlgebraic F z := by
    rintro _ ⟨a, rfl⟩
    have h1 : IsIntegral ℤ (ι a) := (Algebra.IsIntegral.isIntegral (R := ℤ) a).map ι.toIntAlgHom
    exact (h1.tower_top (A := F)).isAlgebraic
  have hEsub : Subalgebra.toSubmodule E.toSubalgebra = Submodule.span F (Set.range fun i => ι (b i)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg, Algebra.adjoin_eq_span]
      refine Submodule.span_le.2 ?_
      intro z hz
      have hcl : Submonoid.closure (Set.range ι) ≤ MonoidHom.mrange ι :=
        Submonoid.closure_le.2 (by rintro _ ⟨a, rfl⟩; exact ⟨a, rfl⟩)
      obtain ⟨a, rfl⟩ := hcl hz
      have hsr := b.sum_repr a
      change ι a ∈ _

      rw [← hsr, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul]
      exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => ι (b i)) i)) _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      exact IntermediateField.subset_adjoin F _ ⟨b i, rfl⟩
  have hEF : Module.finrank F E = n := by
    have : Module.finrank F E = Module.finrank F (Subalgebra.toSubmodule E.toSubalgebra) := rfl
    rw [this, hEsub, hV]
  have hsub : E.toSubfield = Subfield.closure (Set.range ι ∪ Set.range y) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_toSubfield]
      refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
      · rintro _ ⟨z, rfl⟩
        exact (Subfield.closure_le.2 (Set.subset_union_right.trans Subfield.subset_closure)) z.2
      · exact Set.subset_union_left.trans Subfield.subset_closure
    · refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
      · exact fun z hz => IntermediateField.subset_adjoin F _ hz
      · rintro _ ⟨j, rfl⟩; exact E.algebraMap_mem ⟨y j, hyF j⟩
  have htow := Module.finrank_mul_finrank F E K
  have hEK : Module.finrank E.toSubfield K = Module.finrank E K := rfl
  rw [← hsub, hEK, ← htow, hEF, mul_comm]

end GlobalTheory.HSAmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotientSubfieldEqMulRankOrderStatement

section

@[expose] public section

open GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.finrank_quotientSubfield_eq_mul_rank_order : ∀ (k K : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [Field K] [CharZero K] (ι : k →+* K) (D : ℕ) (x : Fin (D + 1) → K), Function.Injective ι → AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → Module.finrank (ratF x) K = Module.finrank (Subfield.closure (Set.range ι ∪ Set.range fun j : Fin D => x j.succ / x 0)) K * Module.finrank ℤ k ∧ Function.Injective (MvPolynomial.eval₂Hom ι fun j : Fin D => x j.succ / x 0) := by
  first | exact @GlobalTheory.HSAmp.finrank_ratF_eq_mul_rank | exact GlobalTheory.HSAmp.finrank_ratF_eq_mul_rank | (intros; apply GlobalTheory.HSAmp.finrank_ratF_eq_mul_rank <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapGenericPointEqOfAlgIndependentQuotients

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.GenericImage

open scoped GlobalTheory.ProjSpace

theorem map_genericPoint_eq : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → Function.Injective (MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) fun j : Fin D => x j.succ / x 0) → π (genericPoint X) = genericPoint (PSpace k D) := by
  intro k _ X _ p D _ π hπ x hx0 ⟨h, hx⟩ hinj
  set W := π ⁻¹ᵁ ProjSpace.chart k D 0 with hW
  let Φ : Γ(PSpace k D, ProjSpace.chart k D 0) →+* X.functionField :=
    (X.presheaf.germ W (genericPoint X) h).hom.comp (π.appLE (ProjSpace.chart k D 0) W le_rfl).hom
  have hconst : (X.presheaf.germ W (genericPoint X) h).hom.comp
      (GlobalTheory.QCoh.Qcqs.baseRingHom (π ≫ PSpace.str k D) W).hom = GlobalTheory.toFunctionField p := by
    subst hπ
    refine RingHom.ext fun a => ?_
    simp only [GlobalTheory.QCoh.Qcqs.baseRingHom, GlobalTheory.toFunctionField, Scheme.Hom.appLE, CommRingCat.hom_comp,
      RingHom.comp_apply]
    exact TopCat.Presheaf.germ_res_apply X.presheaf _ _ _ _
  have key : ∀ a : Γ(PSpace k D, ProjSpace.chart k D 0), a ≠ 0 → Φ a ≠ 0 := by
    intro a ha
    obtain ⟨P, rfl⟩ := ProjSpace.aeval_ratio_surjective k D 0 a
    let s : Fin (D + 1) → MvPolynomial (Fin D) k := Fin.cons 1 MvPolynomial.X
    have e1 : ∀ (A : Type) [CommRing A] (c : k →+* A) (r : Fin (D + 1) → A), r 0 = 1 →
        MvPolynomial.eval₂Hom c r P =
          MvPolynomial.eval₂Hom c (fun j : Fin D => r j.succ) (MvPolynomial.bind₁ s P) := by
      intro A _ c r hr
      rw [MvPolynomial.eval₂Hom_bind₁]
      congr 2
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [s, hr]
      · simp [s]
    have e2 : Φ (MvPolynomial.aeval (ProjSpace.ratio k D 0) P) =
        MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) (fun j => x j / x 0) P := by
      have := congrArg (fun t => t P) (ProjSpace.appLE_comp_aeval_ratio (φ := π) (W := W) (i := 0) (hi := le_rfl))
      simp only [RingHom.comp_apply, RingHom.coe_coe] at this
      simp only [Φ, RingHom.comp_apply]
      erw [this]
      rw [MvPolynomial.map_eval₂Hom, hconst]
      congr 2
      funext j
      exact hx j
    rw [e2, e1 _ _ _ (div_self hx0)]
    intro h0
    have hQ : MvPolynomial.bind₁ s P = 0 := hinj (h0.trans (map_zero _).symm)
    apply ha
    rw [MvPolynomial.aeval_def, ← MvPolynomial.coe_eval₂Hom,
      e1 _ _ _ (by rw [ProjSpace.ratio, ProjSpace.ratioOn_self]), hQ, map_zero]
  have hmem : ∀ a : Γ(PSpace k D, ProjSpace.chart k D 0), a ≠ 0 →
      π (genericPoint X) ∈ (PSpace k D).basicOpen a := by
    intro a ha
    have h1 : genericPoint X ∈ X.basicOpen ((π.appLE (ProjSpace.chart k D 0) W le_rfl).hom a) := by
      rw [Scheme.mem_basicOpen X _ _ h]
      exact (key a ha).isUnit
    have h2 := (Scheme.basicOpen_appLE π W _ le_rfl a).le h1
    exact h2.2
  refine IsGenericPoint.eq ?_ (genericPoint_spec _)
  refine Dense.closure_eq (dense_iff_inter_open.2 fun U hU hne => ?_)
  obtain ⟨y, -, hyU, hyc⟩ := (IrreducibleSpace.isIrreducible_univ (PSpace k D)).2 U
    (ProjSpace.chart k D 0 : Set (PSpace k D)) hU (ProjSpace.chart k D 0).2
    (by simpa using hne) ⟨π (genericPoint X), trivial, h⟩
  obtain ⟨f, hf, hyf⟩ := (ProjSpace.isAffineOpen_chart k D 0).exists_basicOpen_le
    (V := ⟨U, hU⟩) ⟨y, hyU⟩ hyc
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyf
    exact hyf
  exact ⟨_, hf (hmem f hf0), rfl⟩

end GlobalTheory.GenericImage
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapGenericPointEqOfAlgIndependentQuotientsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.map_genericPoint_eq_of_algIndependent_quotients : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) [IsIntegral (PSpace k D)] (π : X ⟶ PSpace k D), π ≫ PSpace.str k D = p → ∀ x : Fin (D + 1) → X.functionField, x 0 ≠ 0 → (∃ h : genericPoint X ∈ π ⁻¹ᵁ ProjSpace.chart k D 0, ∀ j, X.presheaf.germ (π ⁻¹ᵁ ProjSpace.chart k D 0) (genericPoint X) h (ProjSpace.pullRatio π (π ⁻¹ᵁ ProjSpace.chart k D 0) 0 le_rfl j) = x j / x 0) → Function.Injective (MvPolynomial.eval₂Hom (GlobalTheory.toFunctionField p) fun j : Fin D => x j.succ / x 0) → π (genericPoint X) = genericPoint (PSpace k D) := by
  first | exact @GlobalTheory.GenericImage.map_genericPoint_eq | exact GlobalTheory.GenericImage.map_genericPoint_eq | (intros; apply GlobalTheory.GenericImage.map_genericPoint_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithCharZeroFunctionFieldInjectiveConstants

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory

theorem isArithVar_charZero_functionField_and_injective :
    ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
      IsArithVar p D → CharZero X.functionField ∧ Function.Injective (GlobalTheory.toFunctionField p) := by
  intro k _ X _ p D h
  have hΓ : CharZero Γ(X, ⊤) := h.charZero
  have hg : Function.Injective (X.presheaf.germ ⊤ (genericPoint X) trivial).hom :=
    germ_injective_of_isIntegral X _ _
  have hK : CharZero X.functionField := (RingHom.charZero_iff hg).1 hΓ
  refine ⟨hK, ?_⟩
  have := h.isDomain
  have := h.finite
  have hint : Algebra.IsIntegral ℤ k := inferInstance
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  have hker : RingHom.ker (GlobalTheory.toFunctionField p) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, algebraMap_int_eq, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  have : a ∈ RingHom.ker (GlobalTheory.toFunctionField p) := ha
  rw [hker] at this
  exact this

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithCharZeroFunctionFieldInjectiveConstantsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

theorem _root_.GlobalTheory.T.projArith_charZero_functionField_injective_constants : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → CharZero X.functionField ∧ Function.Injective (GlobalTheory.toFunctionField p) := by
  first | exact @GlobalTheory.isArithVar_charZero_functionField_and_injective | exact GlobalTheory.isArithVar_charZero_functionField_and_injective | (intros; apply GlobalTheory.isArithVar_charZero_functionField_and_injective <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsProjectiveSpaceMorphismOfGeneratingSection

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem toProj_gens : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → ∃ (_ : IsIntegral (PSpace k D)) (π : X ⟶ PSpace k D) (hπ : π ≫ PSpace.str k D = p), π (genericPoint X) = genericPoint (PSpace k D) ∧ π.residueDegree (genericPoint X) ≠ 0 ∧ π.residueDegree (genericPoint X) * Module.finrank ℤ k = Module.finrank (ratF x) X.functionField ∧ ∀ u : SmFn p, IsCan P e 1 x u → ((up P.L u).pow e).Isometric ((ProjSpace.hermitianTwistingSheaf k D).pull π hπ) := by
  intro k _ X _ p D hX P hA e x hg
  obtain ⟨hx, hind, hfin⟩ := GlobalTheory.T.sectionQuotients_transcendenceBasis_basepointFree k X p D hX P hA e x hg
  obtain ⟨hK, hι⟩ := GlobalTheory.T.projArith_charZero_functionField_injective_constants k X p D hX
  haveI := hX.isDomain
  haveI := hX.finite
  haveI : CharZero k := ⟨fun a b h => Nat.cast_injective (R := X.functionField) (by
    have := congrArg (GlobalTheory.toFunctionField p) h
    simpa only [map_natCast] using this)⟩
  obtain ⟨hP, -, -⟩ := GlobalTheory.T.projectiveSpace_order_arithVariety_fubiniStudyDegree k D
  haveI : IsIntegral (PSpace k D) := hP.isIntegral
  obtain ⟨hdeg, hev⟩ := GlobalTheory.T.finrank_quotientSubfield_eq_mul_rank_order k X.functionField (GlobalTheory.toFunctionField p) D x hι hind
  obtain ⟨π, hπ, hc, hiso⟩ := GlobalTheory.T.exists_morphism_projSpace_basepointFreeSections k X p D hX P e x hg (hx 0)
  have hgen := GlobalTheory.T.map_genericPoint_eq_of_algIndependent_quotients k X p D π hπ x (hx 0) hc hev
  have hr := GlobalTheory.T.residueDegree_genericPoint_eq_finrank_quotients k X p D π hπ x (hx 0) hc hgen
  refine ⟨inferInstance, π, hπ, hgen, ?_, ?_, hiso⟩
  · rw [hr]
    intro h0
    haveI := hfin
    have : 0 < Module.finrank (ratF x) X.functionField := Module.finrank_pos
    rw [hdeg, h0, zero_mul] at this
    exact lt_irrefl _ this
  · rw [hr, hdeg]

end GlobalTheory.HSAmp
end
end
