module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalBoundaryMetricData
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoIsMonHomOfIsGtOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H0NeBotOfHorizontalFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHolToOfOpenImmersion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Mathlib.Algebra.Azumaya.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafEqSpanOnBasicOpensOfStalkPrincipal
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSncCoordinatesComplexPointSmoothVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivLift
import Mathlib.RingTheory.TotallySplit
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WMultA
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorPotentialIsSNCBoundary

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O
open GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh

namespace GlobalTheory.DivSec

theorem exists_affine_germ_eq : ∀ (Y : Scheme.{0}) (y : Y) (n : ℕ) (r : Fin n → Y.presheaf.stalk y),
    ∃ (V : Y.affineOpens) (hy : y ∈ V.1) (F : Fin n → Γ(Y, V.1)), ∀ j, Y.presheaf.germ V.1 y hy (F j) = r j := by
  intro Y y n r
  classical
  choose U hU s hs using fun j => TopCat.Presheaf.germ_exist Y.presheaf (r j)
  have hmem : ∀ t : Finset (Fin n), y ∈ t.inf U := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert a t ha ih =>
      rw [Finset.inf_insert]
      exact ⟨hU a, ih⟩
  obtain ⟨V, hV, hyV, hVO⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (hmem Finset.univ)
  have hle : ∀ j, V ≤ U j := fun j => le_trans hVO (Finset.inf_le (Finset.mem_univ j))
  refine ⟨⟨V, hV⟩, hyV, fun j => resG Y (hle j) (s j), fun j => ?_⟩
  rw [← hs j]
  exact Y.presheaf.germ_res_apply (homOfLE (hle j)) y hyV (s j)

theorem isCompatChart_of_holAlong : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (n : ℕ)
    (B : FinHolAtlas n (CxPts p σ)), IsAlgAtlas B → ∀ (e : OpenPartialHomeomorph (CxPts p σ) (Fin n → ℂ)),
    (∀ j, HolAlong e.source fun x => e x j) → IsHolTo e.target (fun z => (e.symm z).1) → IsCompatChart B e := by
  intro k _ Y p σ n B hB e hhol hsymm j
  obtain ⟨c, hcj⟩ := hB j
  rw [hcj]
  constructor
  · refine (c.analyticOnNhd_finChart_iff e.open_source e).2 ?_
    refine differentiableOn_pi.2 fun i => ?_
    have hO := GlobalTheory.ChartGlue.isOpen_over c.e e.open_source
    exact hhol i _ _ c.e.symm hO (GlobalTheory.ShFam.Hor.Sec.isHolTo_symm c hO Set.inter_subset_left) (fun b hb => hb.2)
  · have hO : IsOpen (e.target ∩ e.symm ⁻¹' c.finChart.source) := e.isOpen_inter_preimage_symm c.finChart.open_source
    refine (SCV.analyticOnNhd_iff_differentiableOn hO).2 ?_
    intro b hb
    have h1 := GlobalTheory.TrueCx.TorHolo.differentiableAt_chart e.open_target hsymm c hb.1 hb.2
    exact ((EuclideanSpace.equiv (Fin n) ℂ).differentiable.differentiableAt.comp b h1).differentiableWithinAt

end GlobalTheory.DivSec
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealVanishingIdealClosure

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SncForm

theorem ideal_vanishingIdeal_closure {X : Scheme.{0}} (U : X.affineOpens) {η : X} (hη : η ∈ U.1) :
    (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})).ideal U =
      (U.2.primeIdealOf ⟨η, hη⟩).asIdeal := by
  have hU : IsAffineOpen U.1 := U.2
  have emb := hU.fromSpec.isOpenEmbedding
  have h1 : hU.fromSpec (hU.primeIdealOf ⟨η, hη⟩) = η := hU.fromSpec_primeIdealOf ⟨η, hη⟩
  have h2 : hU.fromSpec ⁻¹' ({η} : Set X) = {hU.primeIdealOf ⟨η, hη⟩} := by
    ext Q
    exact ⟨fun h => emb.injective (h.trans h1.symm), fun h => (congrArg _ h).trans h1⟩
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal]
  change PrimeSpectrum.vanishingIdeal (hU.fromSpec ⁻¹' closure ({η} : Set X)) = _
  have h3 := (emb.isOpenMap.preimage_closure_eq_closure_preimage emb.continuous {η}).trans
    (congrArg closure h2)
  exact (congrArg PrimeSpectrum.vanishingIdeal h3).trans
    ((PrimeSpectrum.vanishingIdeal_closure _).trans (PrimeSpectrum.vanishingIdeal_singleton _))

theorem exists_isLocalization_stalk {X : Scheme.{0}} (U : X.affineOpens) {y η : X} (hy : y ∈ U.1)
    (hη : η ∈ U.1) (hηy : η ⤳ y) (p : Ideal (X.presheaf.stalk y)) [p.IsPrime]
    (hp : FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {η})) y = p) :
    ∃ _ : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η),
      IsLocalization.AtPrime (X.presheaf.stalk η) p ∧ ∀ a : Γ(X, U.1),
        X.presheaf.germ U.1 η hη a =
          algebraMap (X.presheaf.stalk y) (X.presheaf.stalk η) (X.presheaf.germ U.1 y hy a) := by
  have hU : IsAffineOpen U.1 := U.2
  let yU : U.1 := ⟨y, hy⟩
  let algY : Algebra Γ(X, U.1) (X.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf yU
  have hlocY : IsLocalization.AtPrime (X.presheaf.stalk y) (hU.primeIdealOf yU).asIdeal :=
    hU.isLocalization_stalk yU
  set Py := hU.primeIdealOf yU with hPy
  let Pη := hU.primeIdealOf ⟨η, hη⟩
  have hfromη : hU.fromSpec Pη = η := hU.fromSpec_primeIdealOf ⟨η, hη⟩
  have hfromy : hU.fromSpec Py = y := hU.fromSpec_primeIdealOf yU
  have emb := hU.fromSpec.isOpenEmbedding
  have hspec : ∀ P Q : PrimeSpectrum Γ(X, U.1), hU.fromSpec P ⤳ hU.fromSpec Q ↔ P ≤ Q := by
    intro P Q
    rw [PrimeSpectrum.le_iff_specializes]
    exact emb.isInducing.specializes_iff
  have hle : Pη ≤ Py := (hspec _ _).mp (by rw [hfromη, hfromy]; exact hηy)
  have hdisj : Disjoint (Py.asIdeal.primeCompl : Set Γ(X, U.1)) Pη.asIdeal :=
    Set.disjoint_left.mpr fun x hx hx' => hx ((show Pη.asIdeal ≤ Py.asIdeal from hle) hx')
  rw [WMult.stalkId_eq_map_germ _ y U hy, ideal_vanishingIdeal_closure U hη] at hp
  have hPeq : Pη.asIdeal = p.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y)) := by
    rw [← hp]
    exact (IsLocalization.under_map_of_isPrime_disjoint Py.asIdeal.primeCompl
      (X.presheaf.stalk y) Pη.isPrime hdisj).symm
  let T := Localization.AtPrime p
  have hT : IsLocalization.AtPrime T (p.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y))) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (M := Py.asIdeal.primeCompl) (S := X.presheaf.stalk y) (T := T) p
  have hT' : IsLocalization Pη.asIdeal.primeCompl T := by
    have hsm : Pη.asIdeal.primeCompl =
        (Ideal.comap (algebraMap Γ(X, U.1) (X.presheaf.stalk y)) p).primeCompl := by
      ext x; rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hPeq]
    rw [hsm]; exact hT
  let ηU : U.1 := ⟨η, hη⟩
  let algη : Algebra Γ(X, U.1) (X.presheaf.stalk η) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ηU
  have hlocη : IsLocalization.AtPrime (X.presheaf.stalk η) Pη.asIdeal :=
    hU.isLocalization_stalk ηU
  let φ : X.presheaf.stalk η ≃ₐ[Γ(X, U.1)] T := IsLocalization.algEquiv Pη.asIdeal.primeCompl _ _
  let algYη : Algebra (X.presheaf.stalk y) (X.presheaf.stalk η) :=
    (φ.symm.toRingEquiv.toRingHom.comp (algebraMap (X.presheaf.stalk y) T)).toAlgebra
  refine ⟨algYη, (IsLocalization.isLocalization_iff_of_ringEquiv (M := p.primeCompl)
      (S := T) φ.symm.toRingEquiv).mp inferInstance, fun a => ?_⟩
  have h1 := (φ.symm.commutes a).symm
  rw [IsScalarTower.algebraMap_apply Γ(X, U.1) (X.presheaf.stalk y) T] at h1
  exact h1

theorem germ_eq_unit_mul_monomial : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (B : LB X) (hB : B.IsLB) (s : B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x → ∀ (i : B.ι) (hi : x ∈ B.U i), ∃ (n : ℕ) (g : Fin n → X.presheaf.stalk x) (e : {a : Fin r // x ∈ (Closeds.closure {z a})} ↪ Fin n) (u : (X.presheaf.stalk x)ˣ) (_ : Fintype {a : Fin r // x ∈ (Closeds.closure {z a})}), FinalTheorems.Rsp (X.presheaf.stalk x) n g ∧ (∀ a, FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a.1})) x = Ideal.span {g (e a)}) ∧ X.presheaf.germ _ x hi (s.f i) = u * ∏ a, g (e a) ^ ((divOfSec hB s hs).mult (z a.1)).toNat := by
  classical
  intro X _ _ B hB s hs r z _ hz hZ x hx i hi
  obtain ⟨hreg, n, g, e, hg, hI⟩ := hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVi⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
  let U : X.affineOpens := ⟨V, hV⟩
  have hVi' : V ≤ B.U i := hVi
  let t : Γ(X, V) := X.presheaf.map (homOfLE hVi').op (s.f i)
  have ht : ∀ (w : X) (hw : w ∈ V), X.presheaf.germ V w hw t =
      X.presheaf.germ _ w (hVi' hw) (s.f i) := fun w hw =>
    X.presheaf.germ_res_apply (homOfLE hVi') w hw _
  set γ := X.presheaf.germ _ x hi (s.f i) with hγ
  have hγ0 : γ ≠ 0 := fun h0 => fnOf_sec_ne_zero hs (gen_mem hi)
    ((algebraMap_germ hi (s.f i)).symm.trans ((congrArg _ h0).trans (map_zero _)))
  let J : Finset (Fin n) := Finset.univ.map e
  have hrad : (∏ j ∈ J, g j) ∈ (Ideal.span {γ}).radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro Q ⟨hQγ, hQ⟩
    let P : PrimeSpectrum Γ(X, V) := ⟨Q.comap (X.presheaf.germ V x hxV).hom, inferInstance⟩
    have htP : t ∈ P.asIdeal := by
      change X.presheaf.germ V x hxV t ∈ Q
      rw [ht]
      exact hQγ (Ideal.mem_span_singleton_self _)
    have hmem : hV.fromSpec P ∈ V := by
      have : hV.fromSpec P ∈ Set.range hV.fromSpec := ⟨P, rfl⟩
      rwa [hV.range_fromSpec] at this
    have hnz : hV.fromSpec P ∉ nonzeroLocus s := by
      rw [mem_nonzeroLocus_iff s i (hVi' hmem)]
      intro h
      have h' : hV.fromSpec P ∈ X.basicOpen t := by
        rw [Scheme.mem_basicOpen _ _ _ hmem, ht]
        exact (Scheme.mem_basicOpen _ _ _ _).1 h
      have h'' : P ∈ hV.fromSpec ⁻¹ᵁ X.basicOpen t := h'
      rw [hV.fromSpec_preimage_basicOpen] at h''
      exact h'' htP
    have hc : hV.fromSpec P ∈ ((nonzeroLocus s : Set X)ᶜ) := hnz
    rw [hZ] at hc
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hc
    have hPx : hV.fromSpec P ⤳ x := by
      have h1 : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
      have h2 : P ≤ hV.primeIdealOf ⟨x, hxV⟩ := by
        rw [hV.primeIdealOf_eq_map_closedPoint]
        exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ.ne_top)
      have h3 := ((PrimeSpectrum.le_iff_specializes _ _).1 h2).map hV.fromSpec.continuous
      rwa [h1] at h3
    have hxa : x ∈ Closeds.closure {z a} := hPx.mem_closed isClosed_closure ha
    have hsup : hV.fromSpec P ∈
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})).support : Set X) := by
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
      exact ha
    rw [WMult.mem_support_fromSpec_iff _ U hV] at hsup
    have h3 : Ideal.span {g (e ⟨a, hxa⟩)} ≤ Q := by
      rw [← hI ⟨a, hxa⟩, WMult.stalkId_eq_map_germ _ x U hxV]
      exact Ideal.map_le_iff_le_comap.mpr hsup
    exact Q.mem_of_dvd (Finset.dvd_prod_of_mem _ (Finset.mem_map_of_mem e (Finset.mem_univ _)))
      (h3 (Ideal.mem_span_singleton_self _))
  obtain ⟨u, m, -, hγu⟩ := eq_unit_mul_monomial g hg.1 hg.2 J hγ0 hrad
  refine ⟨n, g, e, u, inferInstance, hg, hI, ?_⟩
  have hord : ∀ a, ((divOfSec hB s hs).mult (z a.1)).toNat = m (e a) := by
    intro a
    have hsp : z a.1 ⤳ x := specializes_iff_mem_closure.2 a.2
    have hzV : z a.1 ∈ V := hsp.mem_open V.isOpen hxV
    have hpr : Prime (g (e a)) := prime_of_regular_params g hg.1 hg.2 _
    have hP : (Ideal.span {g (e a)}).IsPrime := (Ideal.span_singleton_prime hpr.ne_zero).mpr hpr
    obtain ⟨alg, hloc, hgerm⟩ := exists_isLocalization_stalk U hxV hzV hsp _ (hI a)
    have h := WMult.ord_isLocalization_eq_exponent g hg.1 hg.2 J u m (e a)
      (Finset.mem_map_of_mem e (Finset.mem_univ _)) (X.presheaf.stalk (z a.1))
    rw [← hγu, hγ, ← ht x hxV, ← hgerm t, ht] at h
    rw [mult_divOfSec (hz _) (hVi' hzV), Int.toNat_natCast]
    exact (congrArg ENat.toNat h).trans (ENat.toNat_natCast _)
  rw [hγu, Finset.prod_map]
  exact congrArg _ (Finset.prod_congr rfl fun a _ => by rw [hord])

end GlobalTheory.SncForm
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAnalyticSNCOfAlgebraicSNCSection

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecSnc

open GlobalTheory.ShFam (LiesIn ev_eq_zero_iff isOpen_not_liesIn)

section Local

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem eventually_ev_eq (x : CxPts p σ) {U V : X.Opens} (hU : x.1 (IsLocalRing.closedPoint ℂ) ∈ U)
    (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V) (f : Γ(X, U)) (g : Γ(X, V))
    (h : X.presheaf.germ U _ hU f = X.presheaf.germ V _ hV g) :
    ∀ᶠ y in 𝓝 x, ev p σ U f y = ev p σ V g y := by
  obtain ⟨W, hW, iU, iV, he⟩ := TopCat.Presheaf.germ_eq X.presheaf _ hU hV f g h
  have hWU : W ≤ U := leOfHom iU
  have hWV : W ≤ V := leOfHom iV
  have hres : resG X hWU f = resG X hWV g := he
  refine Filter.eventually_of_mem ((isOpen_ptsIn W).mem_nhds (mem_ptsIn.2 hW)) fun z hz => ?_
  rw [← ev_res hWU hz, ← ev_res hWV hz, hres]

theorem eventually_ev_ne_zero (x : CxPts p σ) {V : X.Opens} (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V)
    (g : Γ(X, V)) (h : IsUnit (X.presheaf.germ V _ hV g)) : ∀ᶠ y in 𝓝 x, ev p σ V g y ≠ 0 := by
  have hx : x ∈ ptsIn p σ (X.basicOpen g) := mem_ptsIn.2 ((X.mem_basicOpen g _ hV).2 h)
  refine Filter.eventually_of_mem ((isOpen_ptsIn _).mem_nhds hx) fun z hz => ?_
  exact (mem_ptsIn_basicOpen (ptsIn_mono (X.basicOpen_le g) hz) g).1 hz

theorem eventually_ev_eq_zero_iff [IsLocallyNoetherian X] (x : CxPts p σ) (V : X.affineOpens)
    (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V.1) (g : Γ(X, V.1)) (C : Closeds X)
    (h : FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal C) (x.1 (IsLocalRing.closedPoint ℂ)) =
      Ideal.span {X.presheaf.germ V.1 _ hV g}) :
    ∀ᶠ y in 𝓝 x, (ev p σ V.1 g y = 0 ↔ LiesIn y C) := by
  rw [WMult.stalkId_eq_map_germ _ _ V hV] at h
  obtain ⟨s, hs, H⟩ := GlobalTheory.IdealSpread.ideal_eq_span_of_germ X _ V _ hV g
    (IsLocallyNoetherian.component_noetherian V) h
  refine Filter.eventually_of_mem ((isOpen_ptsIn _).mem_nhds (mem_ptsIn.2 hs)) fun z hz => ?_
  rw [← ev_res (X.basicOpen_le s) hz]
  exact ev_eq_zero_iff (V := X.affineBasicOpen s) (H s le_rfl) hz

theorem mem_range_ptMap_closι (z : X) (y : CxPts p σ) :
    y ∈ Set.range (ptMap (closι z) rfl σ) ↔ LiesIn y (Closeds.closure {z}) := by
  have hr : Set.range (closι z) = (Closeds.closure {z} : Closeds X) :=
    (Scheme.IdealSheafData.range_subschemeι _).trans (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  constructor
  · rintro ⟨w, rfl⟩
    have : closι z (w.1 (IsLocalRing.closedPoint ℂ)) ∈ Set.range (closι z) := ⟨_, rfl⟩
    rw [hr] at this
    exact this
  · intro hy
    have : IsReduced (Sp ℂ) := inferInstanceAs (IsReduced (Spec _))
    have hle : Set.range y.1 ⊆ Set.range (closι z) := by
      rintro _ ⟨a, rfl⟩
      have ha : a = IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
      rw [hr, ha]
      exact hy
    have hk : (closι z).ker ≤ y.1.ker := ker_le_ker_of_range_subset_of_isReduced (closι z) y.1 hle
    have hl := IsClosedImmersion.lift_fac (closι z) y.1 hk
    exact ⟨⟨IsClosedImmersion.lift (closι z) y.1 hk, by rw [← Category.assoc, hl, y.2]⟩, Subtype.ext hl⟩

end Local

theorem exists_compatChart {F : Type} [Field F] {X : Scheme.{0}} {p : X ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ}
    [SmoothOfRelativeDimension D p] {A : FinHolAtlas D (CxPts p σ)} (hA : IsAlgAtlas A) (x : CxPts p σ)
    {N : Set (CxPts p σ)} (hN : N ∈ 𝓝 x) (V : X.affineOpens) (hV : x.1 (IsLocalRing.closedPoint ℂ) ∈ V.1) {n : ℕ}
    (G : Fin n → Γ(X, V.1))
    (hR : FinalTheorems.Rsp (X.presheaf.stalk (x.1 (IsLocalRing.closedPoint ℂ))) n (fun j => X.presheaf.germ V.1 _ hV (G j))) :
    ∃ (hn : n ≤ D) (ψ : OpenPartialHomeomorph (CxPts p σ) (Fin D → ℂ)), IsCompatChart A ψ ∧ x ∈ ψ.source ∧
      ψ.source ⊆ N ∧ ψ.source ⊆ ptsIn p σ V.1 ∧
      ∀ y ∈ ψ.source, ∀ j, ψ y (Fin.castLE hn j) = ev p σ V.1 (G j) y := by
  haveI : CharZero F := σ.charZero
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (D := D) (p := p) (σ := σ) x
  have hli := SncChart.linearIndependent_fderiv_params F X p D σ c x hc V hV n G hR
  have hxV : x ∈ ptsIn p σ V.1 := mem_ptsIn.2 hV
  have h0 : ∀ i, ev p σ V.1 (G i) x = 0 := by
    intro i
    by_contra hne
    have hb := mem_ptsIn.1 ((mem_ptsIn_basicOpen hxV (G i)).2 hne)
    rw [Scheme.mem_basicOpen _ _ _ hV] at hb
    have hmem : X.presheaf.germ V.1 _ hV (G i) ∈ IsLocalRing.maximalIdeal _ := by
      rw [← hR.1]; exact Ideal.subset_span ⟨i, rfl⟩
    exact hmem hb
  have hn : n ≤ D := by
    have := hli.fintype_card_le_finrank
    rw [← (LinearMap.toContinuousLinearMap (𝕜 := ℂ) (E := ReciprocityTheory.L2DbarEstimates.V D) (F' := ℂ)).finrank_eq,
      Module.finrank_linearMap, Module.finrank_self, _root_.mul_one] at this
    simpa [ReciprocityTheory.L2DbarEstimates.V] using this
  obtain ⟨e, hx0, hsub, -, hhol, hsymm, hev⟩ :=
    SncChart.exists_chart_of_fderiv F X p D σ c x hc V.1 hxV n G h0 hli
  obtain ⟨O, hON, hO, hxO⟩ := mem_nhds_iff.1 hN
  let ψ := e.restrOpen O hO
  have hψs : ψ.source = e.source ∩ O := e.restrOpen_source O hO
  refine ⟨hn, ψ, ?_, hψs ▸ ⟨hx0, hxO⟩, fun y hy => hON (hψs ▸ hy).2, fun y hy => hsub (hψs ▸ hy).1,
    fun y hy j => hev y (hψs ▸ hy).1 (Fin.castLE hn j) j.2⟩
  refine GlobalTheory.DivSec.isCompatChart_of_holAlong F X p σ D A hA ψ (fun j => ?_) ?_
  · intro V _ _ _ B' y hB' hy hm
    exact hhol j V B' y hB' hy (fun b hb => (hψs ▸ hm hb).1)
  · exact GlobalTheory.LocLift.isHolTo_mono hsymm ψ.open_target fun z hz => hz.1

theorem isSNC_locSec : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → IsSNC A M.φ.locPot (M.φ.locSec (secVal p σ s)) (fun a => ((divOfSec M.φ.isLB s hs).mult (z a)).toNat) (fun a => Set.range (ptMap (closι (z a)) rfl σ)) := by
  intro F _ X _ _ p σ D _ hsm A hA M s hs r z hz hco hzero hsnc x
  classical
  haveI := hsm
  have hxi := mem_pick (p := p) (σ := σ) M.φ.isLB x
  have hi := mem_ptsIn.1 hxi
  obtain ⟨n, g, e, u, inst, hR, hI, hf⟩ :=
    GlobalTheory.SncForm.germ_eq_unit_mul_monomial X M.B M.φ.isLB s hs r z hz hco hzero _ (hsnc _) (pick M.φ.isLB x) hi
  obtain ⟨V, hV, G', hG'⟩ := GlobalTheory.DivSec.exists_affine_germ_eq X (x.1 (IsLocalRing.closedPoint ℂ)) (n + 1)
    (Fin.cons (u : X.presheaf.stalk _) g)
  let G : Fin n → Γ(X, V.1) := fun j => G' j.succ
  have hG : ∀ j, X.presheaf.germ V.1 _ hV (G j) = g j := fun j => hG' j.succ
  have hU : X.presheaf.germ V.1 _ hV (G' 0) = u := hG' 0
  have e1 := eventually_ev_eq x hi hV (s.f (pick M.φ.isLB x))
    (G' 0 * ∏ a, G (e a) ^ ((divOfSec M.φ.isLB s hs).mult (z a.1)).toNat) (by
      rw [hf, map_mul, map_prod, hU]
      simp only [map_pow, hG])
  have e2 := eventually_ev_ne_zero x hV (G' 0) (hU ▸ u.isUnit)
  have e3 := Filter.eventually_all.2 fun a => eventually_ev_eq_zero_iff x V hV (G (e a)) _ (by rw [hG]; exact hI a)
  have e4 : ∀ᶠ y in 𝓝 x, ∀ a, ¬ LiesIn x (Closeds.closure {z a}) → ¬ LiesIn y (Closeds.closure {z a}) :=
    Filter.eventually_all.2 fun a => by
      by_cases h : LiesIn x (Closeds.closure {z a})
      · exact Filter.Eventually.of_forall fun _ h' => absurd h h'
      · exact Filter.eventually_of_mem ((isOpen_not_liesIn _).mem_nhds h) fun y hy _ => hy
  have e5 : ∀ᶠ y in 𝓝 x, y ∈ M.φ.locPot.U x := (M.φ.locPot.isOpen_U x).mem_nhds (M.φ.locPot.mem_U x)
  obtain ⟨hn, ψ, hψ, hxψ, hN, hψV, hev⟩ := exists_compatChart hA x (e1.and (e2.and (e3.and (e4.and e5)))) V hV G
    (by rw [funext hG]; exact hR)
  let τ : Fin r → Option (Fin D) := fun a =>
    if h : x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a} then some (Fin.castLE hn (e ⟨a, h⟩)) else none
  refine ⟨ψ, hψ, hxψ, fun y hy => (hN hy).2.2.2.2, τ, ?_, ?_, ev p σ V.1 (G' 0), ?_, fun y hy => (hN hy).2.1, ?_⟩
  · intro a a' i h1 h2
    simp only [τ] at h1 h2
    split_ifs at h1 h2 with ha ha'
    have := Fin.castLE_injective hn ((Option.some.inj h1).trans (Option.some.inj h2).symm)
    exact congrArg Subtype.val (e.injective this)
  · intro a
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_range_ptMap_closι]
    refine and_comm.trans (and_congr_right fun hy => ?_)
    by_cases h : x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a}
    · simp only [τ, dif_pos h, Option.some.injEq, exists_eq_left', hev y hy]
      exact ((hN hy).2.2.1 ⟨a, h⟩).symm
    · simp only [τ, dif_neg h, reduceCtorEq, false_and, exists_false, iff_false]
      exact (hN hy).2.2.2.1 a h
  · exact (hA.holoOn_iff hA.anRead ψ.open_source).2 ((hA.anRead.holoOn_ev V.1 (G' 0)).mono hψV)
  · intro y hy
    refine (hN hy).1.trans ?_
    rw [ev_mul, ev_eq (hψV hy) (∏ _, _), map_prod,
      ← Fintype.prod_subtype_mul_prod_subtype (fun a => x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a})]
    congr 1
    rw [Finset.prod_eq_one (s := Finset.univ)
      (f := fun a : {a // ¬ x.1 (IsLocalRing.closedPoint ℂ) ∈ Closeds.closure {z a}} => _)
      (fun a _ => by simp only [τ, dif_neg a.2]), mul_one]
    refine Finset.prod_congr (by ext; simp) fun a _ => ?_
    simp only [τ, dif_pos a.2, map_pow, hev y hy, ev_eq (hψV hy)]

end GlobalTheory.SecSnc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAnalyticSNCOfAlgebraicSNCSectionStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.isAnalyticSNC_of_algebraicSNC_section : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ (A : FinHolAtlas D (CxPts p σ)), IsAlgAtlas A → ∀ (M : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (r : ℕ) (z : Fin r → X), Function.Injective z → (∀ a, Order.coheight (z a) = 1) → ((nonzeroLocus s : Set X)ᶜ = ⋃ a, closure {z a}) → (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → IsSNC A M.φ.locPot (M.φ.locSec (secVal p σ s)) (fun a => ((divOfSec M.φ.isLB s hs).mult (z a)).toNat) (fun a => Set.range (ptMap (closι (z a)) rfl σ)) := by
  first | exact @GlobalTheory.SecSnc.isSNC_locSec | exact GlobalTheory.SecSnc.isSNC_locSec | (intros; apply GlobalTheory.SecSnc.isSNC_locSec <;> assumption)
end
end
