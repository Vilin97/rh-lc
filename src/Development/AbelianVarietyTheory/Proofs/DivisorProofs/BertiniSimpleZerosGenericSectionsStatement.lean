module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImageBirationalLinearSystemEqSelfInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEliminationFormGeneralLinearFormsConeStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomogeneousFormsQuotientBirationalSystemStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.Henselian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSectionEtaleOfSquarefreeChowFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSectionFiniteInOpenOffBadFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResultantDerivativeNeZero

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqHilbertDegreeOfIsChowForm

section

@[expose] public section

set_option autoImplicit false

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.ChowDegree

attribute [local instance] MvPolynomial.gradedAlgebra

theorem degree_eq_hilbertDegree_of_isChowForm : ∀ (F : Type) [Field F] [CharZero F] (D N δ : ℕ) (I : Ideal (MvPolynomial (Fin N) F)) (f : MvPolynomial (Fin (D + 1) × Fin N) F), IsChowForm I D δ f → I.IsPrime → (∀ g ∈ I, ∀ n : ℕ, homogeneousComponent n g ∈ I) → δ = hilbertDegree I := by
  intro F _ _ D N δ I f hf hp hI
  haveI := hp
  exact GlobalTheory.ChowExists.degree_eq_hilbertDegree (GlobalTheory.ChowExists.isHomogeneous_of_component hI)
    hf.isChowFormInt

end GlobalTheory.ChowDegree
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormFiniteFibresBirationalLinearSystem

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BirFiniteFibre

open GlobalTheory.Points

theorem aeval_smul_of_isHomogeneous {F K σ : Type} [CommRing F] [CommRing K] [Algebra F K] {d : ℕ}
    {p : MvPolynomial σ F} (hp : p.IsHomogeneous d) (c : K) (y : σ → K) :
    aeval (c • y) p = c ^ d * aeval y p := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have : a.degree = d := by rw [Finsupp.degree_eq_weight_one]; exact hp (mem_support_iff.1 ha)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [← this, Finsupp.degree_apply, mul_left_comm]

theorem compactSpace_Y {F : Type} [Field F] (S : LinSys F) (h : S.IsVariety) : CompactSpace S.Y := by
  obtain ⟨n, i, hi, e⟩ := h.proj
  have := isProper_str F n
  have : IsProper S.str := e ▸ inferInstance
  exact ⟨by simpa using QuasiCompact.isCompact_preimage (f := S.str) Set.univ isOpen_univ isCompact_univ⟩

theorem exists_finset_separating {F : Type} [Field F] (S : LinSys F) (h : S.IsVariety) (W : S.Y.Opens)
    (hW : IsAffineOpen W) : ∃ s : Finset Γ(S.Y, W), ∀ (K : Type) [Field K] [Algebra F K] (x x' : S.Pt K),
      ptOf x.1 ∈ W → ptOf x'.1 ∈ W → (∀ a ∈ s, valR x.1 W a = valR x'.1 W a) → x = x' := by
  obtain ⟨n, i, hi, e⟩ := h.proj
  have := isProper_str F n
  have : IsProper S.str := e ▸ inferInstance
  have hle : W ≤ S.str ⁻¹ᵁ ⊤ := le_top
  have hft : (S.str.appLE ⊤ W hle).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) S.str inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ hle
  letI := (S.str.appLE ⊤ W hle).hom.toAlgebra
  obtain ⟨s, hs⟩ : Algebra.FiniteType Γ(Sp F, ⊤) Γ(S.Y, W) := hft
  refine ⟨s, fun K _ _ x x' hx hx' H => Subtype.ext ?_⟩
  have h1 := (le_iff_ptOf_mem _ _).2 hx
  have h2 := (le_iff_ptOf_mem _ _).2 hx'
  refine ext_of_valR hW h1 h2 fun f => ?_
  have hf : f ∈ Algebra.adjoin Γ(Sp F, ⊤) (s : Set Γ(S.Y, W)) := hs ▸ Algebra.mem_top
  induction hf using Algebra.adjoin_induction with
  | mem a ha => exact H a ha
  | algebraMap r =>
    exact (valR_appLE x.1 S.str hle h1 r).trans
      ((congrArg (fun q => valR q ⊤ r) (x.2.trans x'.2.symm)).trans (valR_appLE x'.1 S.str hle h2 r).symm)
  | add a b _ _ ha hb => rw [valR_add _ _ h1, valR_add _ _ h2, ha, hb]
  | mul a b _ _ ha hb => rw [valR_mul _ _ h1, valR_mul _ _ h2, ha, hb]

theorem exists_form_finite_fibres : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → ∃ (d : ℕ) (g : MvPolynomial (Fin S.N) F), g.IsHomogeneous d ∧ g ∉ S.imageIdeal ∧ ∀ (K : Type) [Field K] [Algebra F K] (y : Fin S.N → K), {x : S.Pt K | aeval (S.coords x.1) g ≠ 0 ∧ ∃ c : K, S.coords x.1 = c • y}.Finite := by
  intro F _ S hV hb hB
  classical
  haveI := compactSpace_Y S hV
  haveI := HeightExists.isPrime_imageIdeal hV
  have hcov : ∀ y : S.Y, ∃ W : S.Y.Opens, IsAffineOpen W ∧ y ∈ W := fun y => by
    obtain ⟨W, hW, hy, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
    exact ⟨W, hW, hy⟩
  choose W hW hy using hcov
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set S.Y)) (fun y => (W y).isOpen)
    (fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩)
  choose s hs using fun z => exists_finset_separating S hV (W z) (hW z)
  choose d P Q hP hQ hQI _ hval using fun z a => GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system F S hV hb hB (W z) a
  refine ⟨∑ z ∈ t, ∑ a ∈ s z, d z a, ∏ z ∈ t, ∏ a ∈ s z, Q z a, ?_, ?_, fun K _ _ y => ?_⟩
  · exact IsHomogeneous.prod _ _ _ fun z _ => IsHomogeneous.prod _ _ _ fun a _ => hQ z a
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨z, -, hz⟩
    rw [Ideal.IsPrime.prod_mem_iff] at hz
    obtain ⟨a, -, ha⟩ := hz
    exact hQI z a ha
  · have key : ∀ z ∈ t, ∀ a ∈ s z, ∀ x : S.Pt K, ptOf x.1 ∈ W z →
        aeval (S.coords x.1) (∏ z ∈ t, ∏ a ∈ s z, Q z a) ≠ 0 → (∃ c : K, S.coords x.1 = c • y) →
        valR x.1 (W z) a = aeval y (P z a) / aeval y (Q z a) := by
      rintro z hz a ha x hx hg ⟨c, hc⟩
      have h1 : aeval (S.coords x.1) (Q z a) ≠ 0 := by
        rw [map_prod, Finset.prod_ne_zero_iff] at hg
        have := hg z hz
        rw [map_prod, Finset.prod_ne_zero_iff] at this
        exact this a ha
      have h2 := hval z a K x hx
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hb.coords_ne_zero x.1 (hc.trans (zero_smul _ _))
      rw [hc, aeval_smul_of_isHomogeneous (hQ z a)] at h1 h2
      rw [aeval_smul_of_isHomogeneous (hP z a), mul_left_comm] at h2
      rw [eq_div_iff (right_ne_zero_of_mul h1)]
      exact mul_left_cancel₀ (pow_ne_zero _ hc0) h2
    refine (t.finite_toSet.biUnion (t := fun z => {x : S.Pt K | ptOf x.1 ∈ W z ∧
      aeval (S.coords x.1) (∏ z ∈ t, ∏ a ∈ s z, Q z a) ≠ 0 ∧ ∃ c : K, S.coords x.1 = c • y})
      fun z hz => Set.Subsingleton.finite fun x hx x' hx' => ?_).subset fun x hx => ?_
    · exact hs z K x x' hx.1 hx'.1 fun a ha =>
        (key z hz a ha x hx.1 hx.2.1 hx.2.2).trans (key z hz a ha x' hx'.1 hx'.2.1 hx'.2.2).symm
    · obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ (ptOf x.1)))
      exact Set.mem_iUnion₂.2 ⟨z, hz, hxz, hx⟩

end GlobalTheory.BirFiniteFibre
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormFiniteFibresBirationalLinearSystemStatement

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.exists_form_finite_fibres_birational_linearSystem : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → ∃ (d : ℕ) (g : MvPolynomial (Fin S.N) F), g.IsHomogeneous d ∧ g ∉ S.imageIdeal ∧ ∀ (K : Type) [Field K] [Algebra F K] (y : Fin S.N → K), {x : S.Pt K | aeval (S.coords x.1) g ≠ 0 ∧ ∃ c : K, S.coords x.1 = c • y}.Finite := by
  first | exact @GlobalTheory.BirFiniteFibre.exists_form_finite_fibres | exact GlobalTheory.BirFiniteFibre.exists_form_finite_fibres | (intros; apply GlobalTheory.BirFiniteFibre.exists_form_finite_fibres <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOutsideImageIdealVanishingOnBoundary

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.BoundaryForm

theorem exists_local_fun {Y : Scheme.{0}} [IrreducibleSpace Y] (Z : TopologicalSpace.Closeds Y) (hZ : Z ≠ ⊤) (y : Y) :
    ∃ (W : Y.Opens) (a : Γ(Y, W)), y ∈ W ∧ a ≠ 0 ∧ ∀ z ∈ Y.basicOpen a, z ∉ Z := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hne : ((Z : Set Y)ᶜ).Nonempty := Set.nonempty_compl.2 fun h => hZ (SetLike.coe_injective h)
  obtain ⟨z, hzW, hzZ⟩ := nonempty_preirreducible_inter W.isOpen Z.isClosed.isOpen_compl ⟨y, hy⟩ hne
  obtain ⟨a, ha, hz⟩ := IsAffineOpen.exists_basicOpen_le hW (V := Z.compl) ⟨z, hzZ⟩ hzW
  refine ⟨W, a, hy, ?_, fun w hw => ha hw⟩
  rintro rfl
  rw [Scheme.basicOpen_zero] at hz
  exact hz

theorem exists_form_vanishing : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational →
    ∃ (d : ℕ) (g : MvPolynomial (Fin T.N) F), g.IsHomogeneous d ∧ g ∉ T.imageIdeal ∧
      ∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0 := by
  intro F _ _ T hG hB
  have hV := hG.alg.variety
  have := HeightExists.isIntegral hV
  have := isNoetherian_of_isProjOver hV.proj
  have hp := HeightExists.isPrime_imageIdeal hV
  choose W a hy ha hz using exists_local_fun T.bd hG.bd_ne
  choose d P Q hP _ _ hPn hval using fun y => GlobalTheory.T.exists_homogeneous_forms_quotient_birational_system F T.toLinSys hV hG.alg.bpf hB (W y) (a y)
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y => (W y : Set T.Y)) (fun y => (W y).isOpen)
    fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩
  refine ⟨∑ y ∈ s, d y, ∏ y ∈ s, P y, IsHomogeneous.prod s P d fun y _ => hP y, fun h => ?_, fun K _ _ x hx => ?_⟩
  · obtain ⟨y, -, h⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact hPn y (ha y) h
  · obtain ⟨y, hys, hxy⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ (ptOf x.1)))
    rw [map_prod]
    refine Finset.prod_eq_zero hys ?_
    have h0 : valR x.1 (W y) (a y) = 0 := by
      by_contra h
      exact hz y _ ((valR_ne_zero_iff x.1 hxy _).1 h) hx
    rw [← hval y K x hxy, h0, zero_mul]

end GlobalTheory.BoundaryForm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOutsideImageIdealVanishingOnBoundaryStatement

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.exists_form_outside_imageIdeal_vanishing_on_boundary : ∀ (F : Type) [Field F] [NumberField F] (T : Tuple F), T.IsGeometric → T.Birational → ∃ (d : ℕ) (g : MvPolynomial (Fin T.N) F), g.IsHomogeneous d ∧ g ∉ T.imageIdeal ∧ ∀ (K : Type) [Field K] [Algebra F K] (x : T.Pt K), ptOf x.1 ∈ T.bd → aeval (T.coords x.1) g = 0 := by
  first | exact @GlobalTheory.BoundaryForm.exists_form_vanishing | exact GlobalTheory.BoundaryForm.exists_form_vanishing | (intros; apply GlobalTheory.BoundaryForm.exists_form_vanishing <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniSimpleZerosGenericSections

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

set_option autoImplicit false

namespace GlobalTheory.BertiniTop

attribute [local instance] MvPolynomial.gradedAlgebra

theorem bertini : Quoted → Bertini := by
  intro hq F _ _ T hG hB δ f hf
  obtain ⟨-, hdeg, hdim⟩ :=
    GlobalTheory.ImageDegree.degree_image_eq_topSelf hq F T.toLinSys hG.alg.variety hG.alg.bpf hB
  have hprime : T.imageIdeal.IsPrime := HeightExists.isPrime_imageIdeal (S := T.toLinSys) hG.alg.variety
  have hhom : ∀ a ∈ T.imageIdeal, ∀ n : ℕ, homogeneousComponent n a ∈ T.imageIdeal := by
    intro a ha n
    have h := T.toLinSys.isHomogeneous_imageIdeal n ha
    rwa [show (DirectSum.decompose (homogeneousSubmodule (Fin T.N) F) a n : MvPolynomial (Fin T.N) F) =
      homogeneousComponent n a from MvPolynomial.decomposition.decompose'_apply a n] at h
  have hδ : (δ : ℤ) = T.del := by
    rw [GlobalTheory.ChowDegree.degree_eq_hilbertDegree_of_isChowForm F T.D T.N δ T.imageIdeal f hf hprime hhom]
    exact hdeg
  refine ⟨hδ, ?_⟩
  obtain ⟨d₁, g₁, hg₁, hg₁I, hg₁v⟩ := GlobalTheory.T.exists_form_outside_imageIdeal_vanishing_on_boundary F T hG hB
  obtain ⟨d₂, g₂, hg₂, hg₂I, hg₂f⟩ := GlobalTheory.T.exists_form_finite_fibres_birational_linearSystem F T.toLinSys hG.alg.variety hG.alg.bpf hB
  obtain ⟨Q₁, hQ₁, hQ₁v⟩ := GlobalTheory.T.exists_eliminationForm_generalLinearForms_cone F T.D T.N (d₁ + d₂) T.imageIdeal (g₁ * g₂) hG.alg.variety.one_le hprime hhom
    hdim (hg₁.mul hg₂) fun h => (hprime.mem_or_mem h).elim hg₁I hg₂I
  obtain ⟨Q₂, hQ₂, -, hQ₂n⟩ :=
    GlobalTheory.PencilDisc.exists_poly_noSquare F T.D T.N δ f hf.isChowFormInt.pos hf.homog hf.irred
  refine ⟨Q₁ * Q₂, mul_ne_zero hQ₁ hQ₂, fun E _ _ s hs => ?_⟩
  have hs' : aeval (fun p : Fin T.D × Fin T.N => algebraMap E (AlgebraicClosure E) (s p.1 p.2)) (Q₁ * Q₂) ≠ 0 := by
    have h := MvPolynomial.aeval_algebraMap_apply (AlgebraicClosure E)
      (fun p : Fin T.D × Fin T.N => s p.1 p.2) (Q₁ * Q₂)
    exact fun h0 => hs ((map_eq_zero (algebraMap E (AlgebraicClosure E))).1 (h.symm.trans h0))
  rw [map_mul] at hs'
  have hns : NoSquare (spec (fun i j => algebraMap E (AlgebraicClosure E) (s i j)) f) :=
    hQ₂n _ _ (right_ne_zero_of_mul hs')
  obtain ⟨hfin, hopen⟩ := GlobalTheory.T.linearSection_finite_inOpen_off_badForm F T hG δ f hf (g₁ * g₂)
    (fun K _ _ x hx => by rw [map_mul, hg₁v K x hx, zero_mul])
    (fun K _ _ y => (hg₂f K y).subset fun x hx => ⟨right_ne_zero_of_mul (by simpa only [map_mul] using hx.1), hx.2⟩)
    E s hns.1 fun x hx h0 => by
      refine left_ne_zero_of_mul hs' (hQ₁v (AlgebraicClosure E) (fun i j => algebraMap E _ (s i j)) _
        (hG.alg.bpf.coords_ne_zero _) (fun a ha => ?_) h0 ((T.toLinSys.mem_subPts_cut_baseChange_iff E s x).1 hx))
      have := T.toLinSys.eval₂_coords_eq_zero (LinSys.toBase x : T.Pt (AlgebraicClosure E)).1 ha
      rwa [LinSys.baseHom_ptOver] at this
  exact GlobalTheory.T.linearSection_etale_of_squarefree_chowForm F T hG δ f hf hδ E s hfin hopen hns

end GlobalTheory.BertiniTop
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniSimpleZerosGenericSectionsStatement

section

@[expose] public section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort

theorem _root_.GlobalTheory.T.bertini_simple_zeros_generic_sections : Quoted → Bertini := by
  first | exact @GlobalTheory.BertiniTop.bertini | exact GlobalTheory.BertiniTop.bertini | (intros; apply GlobalTheory.BertiniTop.bertini <;> assumption)
end
end
