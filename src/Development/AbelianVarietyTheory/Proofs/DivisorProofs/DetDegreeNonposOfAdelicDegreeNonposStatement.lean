module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
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
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetPowSectionRationalGenericPointStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPowIff
import Mathlib.Algebra.Order.Star.Int
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldFiniteSupportSumOrderEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceOrderCalculus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurvStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveClosedPointIsCentreOfPlace

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

theorem centre_place : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
    ∀ c : C, c ≠ x (IsLocalRing.closedPoint K) → ∃ (v : Place k K) (b : Sp v.O ⟶ C), spMap v.O.subtype ≫ b = x ∧ b (IsLocalRing.closedPoint v.O) = c := by
  intro k K _ _ _ _ _ C _ x hx c hc
  obtain ⟨hC, hg, hstr⟩ := hx
  haveI : IsIntegral C := GlobalTheory.LieSemineg.isIntegral_curve hC.1 hC.2.2
  haveI := hC.1
  haveI : Smooth (strHom k (X := C)) := SmoothOfRelativeDimension.smooth 1 _
  haveI : GlobalTheory.IsNormalScheme C := isNormalScheme_of_smooth (strHom k C)
  haveI : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  haveI := hg.2
  set p : Sp K := IsLocalRing.closedPoint K with hp
  have hη : x p = genericPoint C := by
    have hd : Dense (Set.range x) := hg.1.denseRange
    have hr : Set.range x = {x p} := by
      ext y
      exact ⟨by rintro ⟨q, rfl⟩; rw [Subsingleton.elim q p]; rfl, by rintro rfl; exact ⟨p, rfl⟩⟩
    rw [hr] at hd
    exact (IsGenericPoint.eq (isGenericPoint_def.2 hd.closure_eq) (genericPoint_spec C))
  have hco : Order.coheight c = 1 := by
    have hne : Order.coheight c ≠ 0 := by
      intro h0
      have hm : IsMax c := Order.coheight_eq_zero.1 h0
      have h3 : genericPoint C ⤳ c := genericPoint_specializes c
      apply hc
      rw [hη]
      exact ((show c ⤳ genericPoint C from hm (show c ≤ genericPoint C from h3)).antisymm h3).eq
    have hle : (Order.coheight c : WithBot ℕ∞) ≤ 1 := by
      haveI : Nonempty C := ⟨c⟩
      have hd := GlobalTheory.LieSemineg.dim_curve (k := k) (C := C) hC.1
      have h1 := (Order.coheight_le_krullDim c).trans (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))).ge
      rw [topologicalKrullDim] at hd
      rw [hd] at h1
      exact h1
    have hle' : Order.coheight c ≤ 1 := by exact_mod_cast hle
    exact le_antisymm hle' (ENat.one_le_iff_ne_zero.2 hne)
  haveI hdvr := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk hco

  set A := C.presheaf.stalk c
  let P : IsDedekindDomain.HeightOneSpectrum A := IsDiscreteValuationRing.maximalIdeal A
  let ic := C.presheaf.stalkCongr (Inseparable.of_eq hη.symm)
  let ψ : C.functionField →+* K := (ic.hom ≫ Scheme.stalkClosedPointTo x).hom
  have hψ : Function.Bijective ψ := by
    refine ⟨RingHom.injective ψ, ?_⟩
    have h1 : Function.Surjective ic.hom.hom :=
      ((ConcreteCategory.isIso_iff_bijective ic.hom).1 inferInstance).2
    have h2 : Function.Surjective (Scheme.stalkClosedPointTo x).hom := by
      have h3 := x.stalkMap_surjective p
      have h4 : Function.Surjective (stalkClosedPointIso (CommRingCat.of K)).hom.hom :=
        ((ConcreteCategory.isIso_iff_bijective (stalkClosedPointIso (CommRingCat.of K)).hom).1 inferInstance).2
      exact h4.comp h3
    exact h2.comp h1
  let e : C.functionField ≃+* K := RingEquiv.ofBijective ψ hψ
  let φ : A →+* K := ψ.comp (algebraMap A C.functionField)
  have hφ : spMap φ ≫ C.fromSpecStalk c = x := by
    have h1 : φ = (C.presheaf.stalkSpecializes (hη ▸ genericPoint_specializes c : x p ⤳ c) ≫ Scheme.stalkClosedPointTo x).hom := by
      show ψ.comp (C.presheaf.stalkSpecializes ((genericPoint_spec C).specializes trivial)).hom = _
      change (C.presheaf.stalkSpecializes _ ≫ ic.hom ≫ Scheme.stalkClosedPointTo x).hom = _
      rw [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc]
      erw [TopCat.Presheaf.stalkSpecializes_comp]
    rw [h1]
    change Spec.map (CommRingCat.ofHom _) ≫ _ = x
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  have hval : ∀ a : A, (P.valuation C.functionField) (e.symm (φ a)) = P.intValuation a := by
    intro a
    have : e.symm (φ a) = algebraMap A C.functionField a := e.symm_apply_apply _
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap P a

  have hk : ∀ t : k, algebraMap k K t = φ (C.presheaf.germ ⊤ c trivial (algebraMap k Γ(C, ⊤) t)) := by
    have h1 : x ≫ strHom k C = spMap ((φ.comp (C.presheaf.germ ⊤ c trivial).hom).comp (algebraMap k Γ(C, ⊤))) := by
      rw [← hφ, Category.assoc, strHom, ← Category.assoc (C.fromSpecStalk c), Scheme.fromSpecStalk_toSpecΓ]
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    have h2 := Spec.map_injective (hstr.symm.trans h1)
    intro t
    exact congrArg (fun f => f.hom t) h2
  let vK : Valuation K (WithZero (Multiplicative ℤ)) := (P.valuation C.functionField).comap e.symm.toRingHom
  have hvφ : ∀ a, vK (φ a) = P.intValuation a := fun a => hval a
  have hunit : ∀ a : A, IsUnit a → P.intValuation a = 1 := by
    intro a ha
    refine le_antisymm (P.intValuation_le_one a) (not_lt.1 fun h => ?_)
    exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ((P.intValuation_lt_one_iff_mem a).1 h) ha)
  let v : Place k K := ⟨vK, fun g => by
      obtain ⟨y, hy⟩ := P.valuation_surjective C.functionField g
      exact ⟨e y, by
        change P.valuation C.functionField (e.symm (e y)) = g
        rw [e.symm_apply_apply]; exact hy⟩,
    fun t ht => by
      rw [hk, hvφ]
      exact hunit _ (((Ne.isUnit ht).map (algebraMap k Γ(C, ⊤))).map _)⟩
  have hle : ∀ a : A, φ a ∈ v.O := fun a => by
    show vK (φ a) ≤ 1
    rw [hvφ]; exact P.intValuation_le_one a
  let ψO : A →+* v.O := φ.codRestrict v.O hle
  have hPm : P.asIdeal = IsLocalRing.maximalIdeal A := rfl
  haveI : IsLocalHom ψO := ⟨fun a ha => by
    by_contra hna
    have hm : a ∈ P.asIdeal := by rw [hPm]; exact hna
    have hlt : vK (φ a) < 1 := by rw [hvφ]; exact (P.intValuation_lt_one_iff_mem a).2 hm
    obtain ⟨u, hu⟩ := ha
    let w : v.O := ((u⁻¹ : v.Oˣ) : v.O)
    have hinv : vK (w : K) ≤ 1 := w.2
    have h1 : φ a * (w : K) = 1 := by
      have := congrArg (fun z : v.O => (z : K)) u.mul_inv
      have e1 : φ a = ((u : v.O) : K) := by rw [hu]; rfl
      rw [e1]
      exact this
    have h2 := congrArg vK h1
    rw [map_mul, map_one] at h2
    have : vK (φ a) * vK (w : K) < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right' hinv) hlt
    exact absurd h2 this.ne⟩
  refine ⟨v, spMap ψO ≫ C.fromSpecStalk c, ?_, ?_⟩
  · rw [← Category.assoc, ← hφ]
    congr 1
    change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    rfl
  · have : spMap ψO (IsLocalRing.closedPoint v.O) = IsLocalRing.closedPoint A :=
      IsLocalRing.comap_closedPoint ψO
    change C.fromSpecStalk c (spMap ψO (IsLocalRing.closedPoint v.O)) = c
    rw [this, Scheme.fromSpecStalk_closedPoint]

end GlobalTheory.Nef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveClosedPointIsCentreOfPlaceStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.curve_closedPoint_isCentreOfPlace : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ c : C, c ≠ x (IsLocalRing.closedPoint K) → ∃ (v : Place k K) (b : Sp v.O ⟶ C), spMap v.O.subtype ≫ b = x ∧ b (IsLocalRing.closedPoint v.O) = c := by
  first | exact @GlobalTheory.Nef.centre_place | exact GlobalTheory.Nef.centre_place | (intros; apply GlobalTheory.Nef.centre_place <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionVanishingDegreePos

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem exists_sec_lbPow_vanishing_of_degree_pos : ∀ (k : Type) [Field k] (C : Scheme.{0})
    [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ L : LB C, L.IsLB →
      0 < interNum k (GlobalTheory.structureModule C) ![L] →
      ∃ (m : ℕ) (σ : (lbPow L m).Sec) (c : C), 0 < m ∧ σ ≠ 0 ∧ c ∉ Out.nonzeroLocus σ := by
  intro k _ C _ hC L hL hpos
  have := LieSemineg.isIntegral_curve hC.1 hC.2.2
  have hd : topologicalKrullDim C = 1 := LieSemineg.dim_curve hC.1
  obtain ⟨hprop, H, hH⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB (strHom k C)).1 hC.2.1
  have := LocallyOfFiniteType.isLocallyNoetherian (strHom k C)
  set O := GlobalTheory.structureModule C with hO
  set d := interNum k O ![L] with hdd
  set f := chiPic k O with hf

  have hdeg : ∀ (M : LB C) (hM : M.IsLB), interNum k O ![M] = f 0 - f (-cls M hM) := by
    intro M hM
    rw [interNum_one k O hM, chi_twistZ k O hM, hf, chiPic_zero, neg_one_zsmul]

  have hchi : ∀ m : ℕ, f ((m : ℤ) • cls L hL) = f 0 + m * d := by
    intro m
    obtain ⟨N, hN, hc⟩ := cls_surj (-((m : ℤ) • cls L hL))
    have hLm := isLB_lbPow hL m
    have e : cls _ (LB.isLB_triv C) = cls N hN + cls _ hLm := by
      rw [hc, cls_lbPow hL m hLm, cls_triv, natCast_zsmul, neg_add_cancel]
    have hadd := interNum_one_of_cls_eq_add (k := k) hH hd (LB.isLB_triv C) hN hLm e
    rw [ArInt.interNum_one_lbPow_of_curve hH hd hL m, hdeg _ (LB.isLB_triv C), hdeg N hN, hc,
      cls_triv, neg_zero, neg_neg] at hadd
    have hd' : interNum k (GlobalTheory.structureModule C) ![L] = d := rfl
    linarith
  set m : ℕ := (f 0).natAbs + 1 with hm
  have hm0 : 0 < m := Nat.succ_pos _
  have hLm := isLB_lbPow hL m
  have hqc := Twist.isQuasicoherent_twist (F := O) hLm
  have hvan : ∀ n, 2 ≤ n → Subsingleton (coh (twist O (lbPow L m)) n) := by
    intro n hn
    refine hH.subsingleton_coh_of_dim_lt _ ?_
    rw [hd]
    exact_mod_cast (show (1 : ℕ) < n by omega)
  have hχ : chi k (twist O (lbPow L m)) = f 0 + m * d := by
    rw [← chiPic_cls k O hLm, cls_lbPow hL m hLm, ← natCast_zsmul, ← hf, hchi m]
  have hχpos : 0 < chi k (twist O (lbPow L m)) := by
    rw [hχ]
    have h1 : (1 : ℤ) ≤ d := hpos
    have h2 : -(f 0) ≤ ((f 0).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]; exact neg_le_abs (f 0)
    have h3 : (m : ℤ) = (f 0).natAbs + 1 := by rw [hm]; push_cast; ring
    nlinarith
  have hh0 : 0 < hdim k (twist O (lbPow L m)) 0 := by
    have := chi_eq_hdim_zero_sub_hdim_one k hvan
    omega
  have hnt : Nontrivial (coh (twist O (lbPow L m)) 0) := Module.nontrivial_of_finrank_pos hh0
  obtain ⟨σ, hσ⟩ := hasNonzeroSec_iff_nontrivial.2 hnt
  refine ⟨m, σ, ?_⟩
  by_contra! hall
  have htop : Out.nonzeroLocus σ = ⊤ := top_unique fun c _ ↦ (hall c hm0 hσ)
  have h0 : cls _ hLm = 0 := (cls_eq_zero_iff hLm).2 (exists_isGen_of_nonzeroLocus_eq_top σ htop)
  have hz := interNum_eq_zero_of_cls_eq_zero k O (isLB_vecOne hLm) 0 h0
  rw [ArInt.interNum_one_lbPow_of_curve hH hd hL m] at hz
  have : (0 : ℤ) < m * d := mul_pos (by exact_mod_cast hm0) hpos
  have hd' : interNum k (GlobalTheory.structureModule C) ![L] = d := rfl
  rw [hd'] at hz
  omega

end GlobalTheory.Nef
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePowSectionVanishingDegreePosStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.exists_lineBundle_pow_section_vanishing_degree_pos : ∀ (k : Type) [Field k] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)], IsCurve k C → ∀ L : LB C, L.IsLB → 0 < interNum k (GlobalTheory.structureModule C) ![L] → ∃ (m : ℕ) (σ : (lbPow L m).Sec) (c : C), 0 < m ∧ σ ≠ 0 ∧ c ∉ Out.nonzeroLocus σ := by
  first | exact @GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos | exact GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos | (intros; apply GlobalTheory.Nef.exists_sec_lbPow_vanishing_of_degree_pos <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDegreeNonposOfAdelicDegreeNonpos

section

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

theorem closedPoint_mem_nonzeroLocus {K : Type} [Field K] {C : Scheme.{0}} [IsIntegral C] (x : Sp K ⟶ C)
    [IsDominant x] {L : LB C} {σ : L.Sec} (hσ : σ ≠ 0) : x (IsLocalRing.closedPoint K) ∈ Out.nonzeroLocus σ := by
  have h : ∃ i, σ.f i ≠ 0 := by
    by_contra h
    push Not at h
    apply hσ
    obtain ⟨f, hf⟩ := σ
    obtain rfl : f = fun _ => 0 := funext h
    rfl
  obtain ⟨i, hi⟩ := h
  have hne : ((C.basicOpen (σ.f i) : C.Opens) : Set C).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro e
    exact hi ((basicOpen_eq_bot_iff _).1 (Opens.ext e))
  obtain ⟨y, hy⟩ := x.denseRange.exists_mem_open (C.basicOpen (σ.f i)).isOpen hne
  obtain rfl : y = IsLocalRing.closedPoint K := Subsingleton.elim _ _
  exact Opens.mem_iSup.2 ⟨i, hy⟩

theorem deg_pos_of_integral {k K : Type} [Field k] [IsAlgClosed k] [Field K] [Algebra k K] {r : ℕ}
    {g : Place k K → Matrix (Fin r) (Fin r) K} (hg : admitted g) {f : K} (hf : f ≠ 0)
    (hfin : {v : Place k K | v.1 f ≠ 1}.Finite) (hsum : ∑ᶠ v : Place k K, ord v f = 0) {m : ℕ}
    (hle : ∀ v : Place k K, v.1 (f * (g v).det ^ m) ≤ 1) {w : Place k K} (hlt : w.1 (f * (g w).det ^ m) < 1) :
    0 < deg g := by
  have hne : ∀ v, f * (g v).det ^ m ≠ 0 := fun v => mul_ne_zero hf (pow_ne_zero _ (hg.1 v))
  have hadd : ∀ v : Place k K, ord v (f * (g v).det ^ m) = ord v f + m * ord v (g v).det := fun v => by
    rw [(ord_calculus k K v).1 _ _ hf (pow_ne_zero _ (hg.1 v)), ← (ord_calculus k K v).2.1 _ (hg.1 v), zpow_natCast]
  have f₁ : (Function.support fun v : Place k K => ord v f).Finite :=
    hfin.subset fun v hv e => hv (((ord_calculus k K v).2.2.2.1 _ hf).1 e)
  have f₂ : (Function.support fun v : Place k K => ord v (g v).det).Finite :=
    hg.2.subset fun v hv e => hv (((ord_calculus k K v).2.2.2.1 _ (hg.1 v)).1 e.2)
  have f₃ : (Function.support fun v : Place k K => (m : ℤ) * ord v (g v).det).Finite :=
    f₂.subset fun v hv e => hv (by simp only [e, mul_zero])
  have hs : ∑ᶠ v : Place k K, ord v (f * (g v).det ^ m) = m * deg g := by
    simp only [hadd]
    rw [finsum_add_distrib f₁ f₃, hsum, zero_add, deg, mul_finsum' _ _ f₂]
  have h0 : ∀ v : Place k K, 0 ≤ ord v (f * (g v).det ^ m) := fun v =>
    ((ord_calculus k K v).2.2.1 _ (hne v)).1 (hle v)
  have hw : 0 < ord w (f * (g w).det ^ m) :=
    (h0 w).lt_of_ne fun e => hlt.ne (((ord_calculus k K w).2.2.2.1 _ (hne w)).2 e.symm)
  have f₄ : (Function.support fun v : Place k K => ord v (f * (g v).det ^ m)).Finite := by
    refine (f₁.union f₃).subset fun v hv => ?_
    by_contra h
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
    exact hv (by simp only [hadd, h.1, h.2, add_zero])
  have hpos : 0 < (m : ℤ) * deg g := by
    rw [← hs]
    exact hw.trans_le (single_le_finsum w f₄ h0)
  by_contra h
  exact absurd hpos (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg m) (not_lt.1 h)))

theorem interNum_det_nonpos_of_deg_nonpos : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → deg g ≤ 0 → interNum k (GlobalTheory.structureModule C) ![det W r] ≤ 0 := by
  intro k K _ _ _ _ _ C _ x hx W r hW V₀ s g hV hs hg hloc hdeg
  by_contra hpos
  have := LieSemineg.isIntegral_curve hx.1.1 hx.1.2.2
  have := hx.2.1.1
  obtain ⟨m, σ, c, -, hσ, hc⟩ := GlobalTheory.T.exists_lineBundle_pow_section_vanishing_degree_pos k C hx.1 (det W r) hW.isLB_det (not_le.1 hpos)
  obtain ⟨w, b, hb, hbc⟩ := GlobalTheory.T.curve_closedPoint_isCentreOfPlace k K C x hx c fun e => hc (e ▸ closedPoint_mem_nonzeroLocus x hσ)
  obtain ⟨f, hf, H⟩ := GlobalTheory.T.detPowSection_rational_genericPoint k K C x hx W r hW V₀ s hV hs m σ hσ
  obtain ⟨hfin, hsum⟩ := GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k K (GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve k K C x hx) f hf
  exact (deg_pos_of_integral hg hf hfin hsum (fun v => (H v _ (hloc v)).1)
    ((H w _ (hloc w)).2 b hb (hbc ▸ hc))).not_ge hdeg

end GlobalTheory.Nef
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetDegreeNonposOfAdelicDegreeNonposStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc


theorem _root_.GlobalTheory.T.detDegree_nonpos_of_adelicDegree_nonpos : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (W : C.Modules) (r : ℕ), IsVB W r → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)) (g : Place k K → Matrix (Fin r) (Fin r) K), (V₀ : Set C).Nonempty → IsFrame s → admitted g → (∀ v, LocFrame x s v (g v)) → deg g ≤ 0 → interNum k (GlobalTheory.structureModule C) ![det W r] ≤ 0 := by
  first | exact @GlobalTheory.Nef.interNum_det_nonpos_of_deg_nonpos | exact GlobalTheory.Nef.interNum_det_nonpos_of_deg_nonpos | (intros; apply GlobalTheory.Nef.interNum_det_nonpos_of_deg_nonpos <;> assumption)
end
end
