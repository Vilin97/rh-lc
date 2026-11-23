module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.OrderOfVanishing.Basic
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentCotangentOfIsTopFormFrameOfVaniStatement
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientSpanRange
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CodimOneGenerizationStalk
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsSncChartStatement
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanPairIsPrimeHeightTwoOfCotangentIndependent

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PointSep

open IsLocalRing

theorem span_pair_isPrime_and_height_eq_two : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (a b : R) (ha : a ∈ IsLocalRing.maximalIdeal R) (hb : b ∈ IsLocalRing.maximalIdeal R), LinearIndependent (IsLocalRing.ResidueField R) (![(IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩, (IsLocalRing.maximalIdeal R).toCotangent ⟨b, hb⟩] : Fin 2 → IsLocalRing.CotangentSpace R) → (Ideal.span {a, b}).IsPrime ∧ (Ideal.span {a, b}).height = 2 := by
  intro R _ _ a b ha hb h
  classical
  have hdom : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hp := LinearIndependent.pair_iff.mp h
  have hsmul : ∀ (r : R) (x : maximalIdeal R),
      (maximalIdeal R).toCotangent (r • x) = (residue R r) • (maximalIdeal R).toCotangent x := by
    intro r x
    rw [map_smul]; rfl

  have ha2 : a ∉ maximalIdeal R ^ 2 := by
    intro h2
    have h0 : (maximalIdeal R).toCotangent ⟨a, ha⟩ = 0 := by
      rw [Ideal.toCotangent_eq_zero]; exact h2
    have := hp 1 0 (by simp [h0])
    exact one_ne_zero this.1
  have hpa : Prime a := ReciprocityTheory.AnForm.R.prime_of_not_mem_sq ha ha2
  have ha0 : a ≠ 0 := hpa.ne_zero

  have hba : b ∉ Ideal.span {a} := by
    intro hb'
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb'
    have heq : (⟨b, hb⟩ : maximalIdeal R) = r • ⟨a, ha⟩ := by
      ext; simp [hr]
    have := hp (-(residue R r)) 1 (by rw [heq, hsmul]; simp)
    exact one_ne_zero this.2

  have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  have hle := h.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  set n := Module.finrank (ResidueField R) (CotangentSpace R) with hn
  have hdim : ringKrullDim R = (((n - 2) + 2 : ℕ) : WithBot ℕ∞) := by
    rw [← hfin, Nat.sub_add_cancel hle]
  have hind : ∀ c : Fin 2 → R, ∑ i, c i * (![a, b] : Fin 2 → R) i ∈ maximalIdeal R ^ 2 →
      ∀ i, c i ∈ maximalIdeal R := by
    intro c hc
    have hc' : (maximalIdeal R).toCotangent (c 0 • ⟨a, ha⟩ + c 1 • ⟨b, hb⟩) = 0 := by
      rw [Ideal.toCotangent_eq_zero]
      simpa [Fin.sum_univ_two] using hc
    rw [map_add (f := _), hsmul, hsmul] at hc'
    obtain ⟨h0, h1⟩ := hp _ _ hc'
    intro i
    fin_cases i
    · exact (residue_eq_zero_iff _).mp h0
    · exact (residue_eq_zero_iff _).mp h1
  have hmem : ∀ i, (![a, b] : Fin 2 → R) i ∈ maximalIdeal R := by
    intro i; fin_cases i
    · exact ha
    · exact hb
  obtain ⟨hreg, -⟩ := GlobalTheory.RegularQuotient.quotient_span_range R (n - 2) 2 ![a, b] hdim hmem hind
  have hrange : Set.range (![a, b] : Fin 2 → R) = {a, b} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [hrange] at hreg
  have hqdom : IsDomain (R ⧸ Ideal.span {a, b}) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hP : (Ideal.span {a, b}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hqdom
  refine ⟨hP, le_antisymm ?_ ?_⟩
  · have hmin : Ideal.span {a, b} ∈ (Ideal.span ((({a, b} : Finset R)) : Set R)).minimalPrimes := by
      rw [Finset.coe_insert, Finset.coe_singleton, Ideal.minimalPrimes_eq_subsingleton_self]
      rfl
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans ?_
    exact_mod_cast Finset.card_le_two
  · have hPa : (Ideal.span {a}).IsPrime := (Ideal.span_singleton_prime ha0).mpr hpa
    have h1 : (⊥ : Ideal R) < Ideal.span {a} := by
      rw [bot_lt_iff_ne_bot]; simpa using ha0
    have h2 : Ideal.span {a} < Ideal.span {a, b} := by
      refine lt_of_le_of_ne (Ideal.span_mono (by simp)) ?_
      intro he
      exact hba (he ▸ Ideal.subset_span (by simp))
    have hlt1 := Ideal.height_strict_mono_of_isPrime h1
    have hlt2 := Ideal.height_strict_mono_of_isPrime h2
    have hne : (Ideal.span {a}).height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
    have e1 : (⊥ : Ideal R).height + 1 ≤ (Ideal.span {a}).height := Order.add_one_le_of_lt hlt1
    have e2 : (Ideal.span {a}).height + 1 ≤ (Ideal.span {a, b}).height := Order.add_one_le_of_lt hlt2
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal R).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ (Ideal.span {a}).height + 1 := by gcongr
      _ ≤ _ := e2

end GlobalTheory.PointSep
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanPairIsPrimeHeightTwoOfCotangentIndependentStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

theorem _root_.GlobalTheory.T.span_pair_isPrime_height_two_of_cotangent_independent : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (a b : R) (ha : a ∈ IsLocalRing.maximalIdeal R) (hb : b ∈ IsLocalRing.maximalIdeal R), LinearIndependent (IsLocalRing.ResidueField R) (![(IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩, (IsLocalRing.maximalIdeal R).toCotangent ⟨b, hb⟩] : Fin 2 → IsLocalRing.CotangentSpace R) → (Ideal.span {a, b}).IsPrime ∧ (Ideal.span {a, b}).height = 2 := by
  first | exact @GlobalTheory.PointSep.span_pair_isPrime_and_height_eq_two | exact GlobalTheory.PointSep.span_pair_isPrime_and_height_eq_two | (intros; apply GlobalTheory.PointSep.span_pair_isPrime_and_height_eq_two <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkEquivOfFromSpecStalk

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncMeet

open IsLocalRing

theorem exists_stalk_equiv_of_fromSpecStalk (X : Scheme.{0}) (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    ∃ (h : X.fromSpecStalk x p ⤳ x)
      (e : X.presheaf.stalk (X.fromSpecStalk x p) ≃+* Localization.AtPrime p.asIdeal),
      ∀ g, e ((X.presheaf.stalkSpecializes h).hom g) = algebraMap _ _ g := by
  obtain ⟨e, he⟩ := GlobalTheory.LocalRingGeneralisation.stalk_fromSpecStalk_equiv X x p.asIdeal
  have hs : X.fromSpecStalk x p ⤳ x := by
    have : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  refine ⟨hs, e, ?_⟩
  have hcomp : X.presheaf.stalkSpecializes hs ≫ CommRingCat.ofHom e.toRingHom =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk x) (Localization.AtPrime p.asIdeal)) := by
    apply TopCat.Presheaf.stalk_hom_ext
    intro U hxU
    ext s
    have h3 := congrArg (fun f => f.hom s) (TopCat.Presheaf.germ_stalkSpecializes X.presheaf hxU hs)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h3
    change e ((X.presheaf.stalkSpecializes hs).hom ((X.presheaf.germ U _ hxU).hom s)) =
      algebraMap _ (Localization.AtPrime p.asIdeal) ((X.presheaf.germ U _ hxU).hom s)
    rw [h3]
    exact he U _ hxU s
  intro g
  exact congrArg (fun f => f.hom g) hcomp

theorem mem_asIdeal_iff (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) (y : X)
    (hy : y ⤳ x) (hp : X.fromSpecStalk x p = y) (g : X.presheaf.stalk x) :
    g ∈ p.asIdeal ↔ (X.presheaf.stalkSpecializes hy).hom g ∈ maximalIdeal (X.presheaf.stalk y) := by
  subst hp
  obtain ⟨h, e, he⟩ := exists_stalk_equiv_of_fromSpecStalk X x p
  have h1 : g ∈ p.asIdeal ↔ algebraMap _ (Localization.AtPrime p.asIdeal) g ∈
      maximalIdeal (Localization.AtPrime p.asIdeal) := by
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p.asIdeal) p.asIdeal g).symm
  rw [h1, ← he g, mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    MulEquiv.isUnit_map]

theorem coheight_fromSpecStalk (X : Scheme.{0}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    Order.coheight (X.fromSpecStalk x p) = p.asIdeal.height := by
  obtain ⟨h, e, he⟩ := exists_stalk_equiv_of_fromSpecStalk X x p
  have h1 := ringKrullDim_stalk_eq_coheight (X.fromSpecStalk x p)
  rw [ringKrullDim_eq_of_ringEquiv e,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  exact_mod_cast h1.symm

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem ord_algebraMap_of_isUnit (x : X) (g : X.presheaf.stalk x) (hg : IsUnit g) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) x = 0 := by
  by_cases hx : Order.coheight x = 1
  · have hne : algebraMap (X.presheaf.stalk x) X.functionField g ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg.ne_zero
    rw [Scheme.ord_eq_iff hx hne]
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    change Ring.ordFrac _ _ = _
    rw [Ring.ordFrac_of_isUnit hg]
    rfl
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx _

theorem ord_algebraMap_ne_zero (x : X) (hx : Order.coheight x = 1) (g : X.presheaf.stalk x)
    (hg0 : g ≠ 0) (hg : g ∈ maximalIdeal (X.presheaf.stalk x)) :
    Scheme.ord (algebraMap (X.presheaf.stalk x) X.functionField g) x ≠ 0 := by
  haveI : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hne : algebraMap (X.presheaf.stalk x) X.functionField g ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hg0
  intro h0
  rw [Scheme.ord_eq_iff hx hne] at h0
  change Ring.ordFrac _ _ = _ at h0
  rw [Ring.ordFrac_eq_ord _] at h0
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hg0))
  rw [Ring.ordMonoidWithZeroHom_eq_coe _ (mem_nonZeroDivisors_of_ne_zero hg0) hm.symm] at h0
  have hm0 : m = 0 := by
    have h4 : (m : ℤ) = 0 := Multiplicative.ofAdd.injective (WithZero.coe_injective h0)
    exact_mod_cast h4
  subst hm0
  have h2 : Ring.ord (X.presheaf.stalk x) g = 0 := by rw [← hm]; rfl
  rw [Ring.ord] at h2
  rw [Module.length_eq_zero_iff, Ideal.Quotient.subsingleton_iff, Ideal.span_singleton_eq_top] at h2
  exact (mem_maximalIdeal g).1 hg h2


open IsLocalRing in
theorem exists_meet_point : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (B : Closeds Y), FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B) → ∀ v σ w : Y, v ∈ B → σ ∈ B → Order.coheight v = 1 → Order.coheight σ = 1 → v ≠ σ → v ⤳ w → σ ⤳ w → ∃ (w' : Y) (t u : Y.presheaf.stalk w'), w' ⤳ w ∧ v ⤳ w' ∧ σ ⤳ w' ∧ ringKrullDim (Y.presheaf.stalk w') = 2 ∧ Ideal.span {t, u} = IsLocalRing.maximalIdeal (Y.presheaf.stalk w') ∧ Scheme.ord (algebraMap (Y.presheaf.stalk w') Y.functionField t) σ = 1 ∧ Scheme.ord (algebraMap (Y.presheaf.stalk w') Y.functionField u) v = 1 ∧ ∀ v' ∈ B, Order.coheight v' = 1 → v' ⤳ w' → v' = v ∨ v' = σ := by
  classical
  intro Y _ _ q n _ B hB v σ w hvB hσB hv hσ hvσ hvw hσw
  obtain ⟨U, hwU, z, J, wf, uf, hc⟩ := GlobalTheory.T.exists_snc_chart ℂ Y q n B hB w
  obtain ⟨j', hj'J, rfl⟩ := (hc.mem v hvw hv).1 hvB
  obtain ⟨j, hjJ, rfl⟩ := (hc.mem σ hσw hσ).1 hσB
  have hjj : j ≠ j' := fun h => hvσ (by rw [h])
  haveI : IsRegularLocalRing (Y.presheaf.stalk w) := (hB w).1
  have hUmem : ∀ y : Y, y ⤳ w → y ∈ U := fun y hy => hy.mem_open U.isOpen hwU
  have hgerm : ∀ (y : Y) (hy : y ⤳ w) (i : Fin n),
      (Y.presheaf.stalkSpecializes hy).hom (Y.presheaf.germ U w hwU (z i)) =
        Y.presheaf.germ U y (hUmem y hy) (z i) := fun y hy i => by
    rw [← TopCat.Presheaf.germ_stalkSpecializes Y.presheaf hwU hy]; rfl
  have hfn : ∀ (y : Y) (hy : y ∈ U) (i : Fin n), i ∈ J →
      algebraMap (Y.presheaf.stalk y) Y.functionField (Y.presheaf.germ U y hy (z i)) =
        (uf i : Y.functionField) := fun y hy i hi => by
    rw [GlobalTheory.Cartier.algebraMap_germ hy, hc.val i hi]
  have hgne : ∀ (y : Y) (hy : y ∈ U) (i : Fin n), i ∈ J → Y.presheaf.germ U y hy (z i) ≠ 0 :=
    fun y hy i hi h0 => (uf i).ne_zero (by rw [← hfn y hy i hi, h0, map_zero])
  have hmy : ∀ i (hi : i ∈ J), Y.presheaf.germ U (wf i) (hUmem _ (hc.spec i hi)) (z i) ∈
      maximalIdeal (Y.presheaf.stalk (wf i)) := by
    intro i hi
    by_contra hnm
    have hu : IsUnit (Y.presheaf.germ U (wf i) (hUmem _ (hc.spec i hi)) (z i)) := by
      by_contra h'; exact hnm ((mem_maximalIdeal _).2 h')
    have h1 := GlobalTheory.SncMeet.ord_algebraMap_of_isUnit _ _ hu
    rw [hfn _ _ i hi, hc.ord_self i hi] at h1
    exact one_ne_zero h1
  have hm : ∀ i ∈ J, Y.presheaf.germ U w hwU (z i) ∈ maximalIdeal (Y.presheaf.stalk w) := by
    intro i hi
    by_contra hnm
    have hu : IsUnit (Y.presheaf.germ U w hwU (z i)) := by
      by_contra h'; exact hnm ((mem_maximalIdeal _).2 h')
    have hu' := hu.map (Y.presheaf.stalkSpecializes (hc.spec i hi)).hom
    rw [hgerm] at hu'
    exact (mem_maximalIdeal _).1 (hmy i hi) hu'
  have hli := GlobalTheory.T.linearIndependent_cotangent_of_isTopFormFrame_of_vanishing Y q n U z hc.frame w hwU J (fun i => hm i.1 i.2)

  have hi2 : Function.Injective (![⟨j, hjJ⟩, ⟨j', hj'J⟩] : Fin 2 → J) := by
    intro k l hkl
    fin_cases k <;> fin_cases l
    · rfl
    · exact (hjj (by simpa using congrArg Subtype.val hkl)).elim
    · exact (hjj (by simpa using (congrArg Subtype.val hkl).symm)).elim
    · rfl
  have hli2 := hli.comp _ hi2
  obtain ⟨hPp, hPh⟩ := GlobalTheory.T.span_pair_isPrime_height_two_of_cotangent_independent (Y.presheaf.stalk w) (Y.presheaf.germ U w hwU (z j))
    (Y.presheaf.germ U w hwU (z j')) (hm j hjJ) (hm j' hj'J) (by
      convert hli2 using 1
      funext k; fin_cases k <;> rfl)
  let pt : PrimeSpectrum (Y.presheaf.stalk w) :=
    ⟨Ideal.span {Y.presheaf.germ U w hwU (z j), Y.presheaf.germ U w hwU (z j')}, hPp⟩
  obtain ⟨hw', e, he⟩ := GlobalTheory.SncMeet.exists_stalk_equiv_of_fromSpecStalk Y w pt
  have K1 : ∀ i ∈ J, Y.presheaf.germ U w hwU (z i) ∈ pt.asIdeal →
      wf i ⤳ Y.fromSpecStalk w pt := by
    intro i hi hiP
    obtain ⟨Q, hQmin, hQle⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem _).2 hiP)
    have hQp : Q.IsPrime := hQmin.1.1
    have hbQ : Y.presheaf.germ U w hwU (z i) ∈ Q := hQmin.1.2 (Ideal.mem_span_singleton_self _)
    have hQh1 : Q.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ Q hQmin
    have hQ0 : Q ≠ ⊥ := fun h => hgne w hwU i hi (by rw [h] at hbQ; exact Ideal.mem_bot.1 hbQ)
    have hQh : Q.height = 1 := by
      refine le_antisymm hQh1 ?_
      rw [ENat.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact hQ0
    let pQ : PrimeSpectrum (Y.presheaf.stalk w) := ⟨Q, hQp⟩
    obtain ⟨hQw, -, -⟩ := GlobalTheory.SncMeet.exists_stalk_equiv_of_fromSpecStalk Y w pQ
    have hcoh : Order.coheight (Y.fromSpecStalk w pQ) = 1 := by
      rw [GlobalTheory.SncMeet.coheight_fromSpecStalk]; exact_mod_cast hQh
    have hsp : Y.fromSpecStalk w pQ ⤳ Y.fromSpecStalk w pt :=
      ((PrimeSpectrum.le_iff_specializes pQ pt).1 hQle).map (Y.fromSpecStalk w).continuous
    have hmem : Y.presheaf.germ U _ (hUmem _ hQw) (z i) ∈
        maximalIdeal (Y.presheaf.stalk (Y.fromSpecStalk w pQ)) := by
      rw [← hgerm _ hQw i]; exact (GlobalTheory.SncMeet.mem_asIdeal_iff Y w pQ _ hQw rfl _).1 hbQ
    have hord := GlobalTheory.SncMeet.ord_algebraMap_ne_zero _ hcoh _ (hgne _ _ i hi) hmem
    rw [hfn _ _ i hi] at hord
    have heq : Y.fromSpecStalk w pQ = wf i := by
      by_contra hne; exact hord (hc.ord_other i hi _ hQw hne)
    rw [← heq]; exact hsp
  have hPh' : pt.asIdeal.height = 2 := hPh
  have ht : ∀ g, (Y.presheaf.stalkSpecializes hw').hom g =
      e.symm (algebraMap _ (Localization.AtPrime pt.asIdeal) g) := fun g => by
    rw [← he g, RingEquiv.symm_apply_apply]
  refine ⟨Y.fromSpecStalk w pt, (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j)),
    (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j')), hw',
    K1 j' hj'J (Ideal.subset_span (by simp)), K1 j hjJ (Ideal.subset_span (by simp)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [ringKrullDim_eq_of_ringEquiv e,
      IsLocalization.AtPrime.ringKrullDim_eq_height pt.asIdeal, hPh']
    rfl
  · have h1 : Ideal.span {(Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j)),
        (Y.presheaf.stalkSpecializes hw').hom (Y.presheaf.germ U w hwU (z j'))} =
        Ideal.map e.symm (Ideal.map (algebraMap _ (Localization.AtPrime pt.asIdeal)) pt.asIdeal) := by
      rw [ht, ht]
      show _ = Ideal.map e.symm (Ideal.map _ (Ideal.span _))
      simp only [Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
    rw [h1, Localization.AtPrime.map_eq_maximalIdeal]
    exact IsLocalRing.eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e.symm)
  · rw [hgerm _ hw' j, hfn _ _ j hjJ]; exact hc.ord_self j hjJ
  · rw [hgerm _ hw' j', hfn _ _ j' hj'J]; exact hc.ord_self j' hj'J
  · intro v' hv'B hv'1 hv'w'
    have hv'w := hv'w'.trans hw'
    obtain ⟨i, hi, rfl⟩ := (hc.mem v' hv'w hv'1).1 hv'B
    by_contra hcon
    rw [not_or] at hcon
    have hij' : i ≠ j' := fun h => hcon.1 (by rw [h])
    have hij : i ≠ j := fun h => hcon.2 (by rw [h])
    obtain ⟨pi, hpi⟩ : wf i ∈ Set.range (Y.fromSpecStalk w) := by
      rw [Scheme.range_fromSpecStalk]; exact hv'w
    have hle : pi.asIdeal ≤ pt.asIdeal := by
      have h1 : Y.fromSpecStalk w pi ⤳ Y.fromSpecStalk w pt := hpi ▸ hv'w'
      exact (PrimeSpectrum.le_iff_specializes pi pt).2
        ((IsPreimmersion.isEmbedding (Y.fromSpecStalk w)).specializes_iff.1 h1)
    have hciP : Y.presheaf.germ U w hwU (z i) ∈ pt.asIdeal := by
      apply hle
      rw [GlobalTheory.SncMeet.mem_asIdeal_iff Y w pi (wf i) (hc.spec i hi) hpi, hgerm]
      exact hmy i hi
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.1 hciP
    refine hli.notMem_span_image (s := {⟨j, hjJ⟩, ⟨j', hj'J⟩}) (x := ⟨i, hi⟩) ?_ ?_
    · simp [Subtype.ext_iff, hij, hij']
    · have hsum : (⟨Y.presheaf.germ U w hwU (z i), hm i hi⟩ : maximalIdeal (Y.presheaf.stalk w)) =
          r • ⟨Y.presheaf.germ U w hwU (z j), hm j hjJ⟩ +
            s • ⟨Y.presheaf.germ U w hwU (z j'), hm j' hj'J⟩ := by
        ext; simp [← hrs, smul_eq_mul]
      show (maximalIdeal _).toCotangent ⟨_, _⟩ ∈ _
      rw [hsum, map_add (f := _), map_smul, map_smul]
      exact Submodule.add_mem _
        (Submodule.smul_of_tower_mem _ r (Submodule.subset_span ⟨⟨j, hjJ⟩, by simp, rfl⟩))
        (Submodule.smul_of_tower_mem _ s (Submodule.subset_span ⟨⟨j', hj'J⟩, by simp, rfl⟩))

end GlobalTheory.SncMeet
end
end
end
