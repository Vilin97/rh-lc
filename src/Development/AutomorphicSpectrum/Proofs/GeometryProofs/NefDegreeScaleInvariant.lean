module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PGeoNumCut
import Mathlib.Algebra.Order.Star.Int
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitSectionDivisorEq

section

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

theorem length_localizedModule_quot_eq {R : Type*} [CommRing R] (W : Ideal R) [W.IsPrime] {J₁ J₂ : Ideal R}
    (h₁ : ∀ x ∈ J₁, ∃ s, s ∉ W ∧ s * x ∈ J₂) (h₂ : ∀ x ∈ J₂, ∃ s, s ∉ W ∧ s * x ∈ J₁) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₁)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₂)) := by
  have key : ∀ {A B : Ideal R}, (∀ x ∈ A, ∃ s, s ∉ W ∧ s * x ∈ B) →
      Submodule.localized W.primeCompl (M := R) A ≤ Submodule.localized W.primeCompl (M := R) B := by
    intro A B h y hy
    obtain ⟨m, hm, s, rfl⟩ := hy
    obtain ⟨t, ht, htm⟩ := h m hm
    refine ⟨t * m, htm, ⟨t, ht⟩ * s, ?_⟩
    exact IsLocalizedModule.mk'_cancel_left _ _ _ _
  have heq : Submodule.localized W.primeCompl (M := R) J₁ = Submodule.localized W.primeCompl (M := R) J₂ :=
    le_antisymm (key h₁) (key h₂)
  have e₁ := (localizedQuotientEquiv W.primeCompl (M := R) J₁).length_eq
  have e₂ := (localizedQuotientEquiv W.primeCompl (M := R) J₂).length_eq
  have e₃ := (Submodule.quotEquivOfEq _ _ heq).length_eq
  exact e₁.symm.trans (e₃.trans e₂)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem IsUnitSec.symm {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) : IsUnitSec P g f := by
  intro W hW hP hR
  obtain ⟨u, v, hu, hv, hm⟩ := h W hW hP hR
  refine ⟨v, u, hv, hu, ?_⟩
  have := P.neg_mem hm
  rwa [neg_sub] at this

theorem divSupp_subset_of_isUnitSec {P : Ideal (MRing ι)} {f g : MRing ι} (h : IsUnitSec P f g) :
    divSupp P f ⊆ divSupp P g := by
  rintro W ⟨hmin, hrel⟩
  have hWp : W.IsPrime := hmin.1.1
  have hP : P ≤ W := le_sup_left.trans hmin.1.2
  have hf : f ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨u, v, hu, hv, hm⟩ := h W hWp hP hrel
  have hvg : v * g ∈ W := by
    have e : v * g = u * f - (u * f - v * g) := by ring
    rw [e]
    exact W.sub_mem (W.mul_mem_left u hf) (hP hm)
  have hg : g ∈ W := (hWp.mem_or_mem hvg).resolve_left hv
  refine ⟨⟨⟨hWp, sup_le hP ((Ideal.span_singleton_le_iff_mem _).mpr hg)⟩, ?_⟩, hrel⟩
  rintro W' ⟨hW'p, hW'le⟩ hW'W
  have hP' : P ≤ W' := le_sup_left.trans hW'le
  have hg' : g ∈ W' := hW'le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have huf : u * f ∈ W' := by
    have e : u * f = (u * f - v * g) + v * g := by ring
    rw [e]
    exact W'.add_mem (hP' hm) (W'.mul_mem_left v hg')
  have hf' : f ∈ W' := (hW'p.mem_or_mem huf).resolve_left fun hu' => hu (hW'W hu')
  exact hmin.2 ⟨hW'p, sup_le hP' ((Ideal.span_singleton_le_iff_mem _).mpr hf')⟩ hW'W

theorem mul_mem_sup_span_of_sub_mem {R : Type*} [CommRing R] {P : Ideal R} {f g u v x : R}
    (hm : u * f - v * g ∈ P) (hx : x ∈ P ⊔ Ideal.span {f}) : u * x ∈ P ⊔ Ideal.span {g} := by
  obtain ⟨p, hp, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  have e : u * (p + a * f) = (u * p + a * (u * f - v * g)) + (a * v) * g := by ring
  rw [e]
  exact Ideal.add_mem _
    (Ideal.mem_sup_left (P.add_mem (P.mul_mem_left u hp) (P.mul_mem_left a hm)))
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))

theorem multAt_sup_span_eq_of_sub_mem {P W : Ideal (MRing ι)} (hW : W.IsPrime) {f g u v : MRing ι}
    (hu : u ∉ W) (hv : v ∉ W) (hm : u * f - v * g ∈ P) :
    multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
  have hm' : v * g - u * f ∈ P := by
    have := P.neg_mem hm
    rwa [neg_sub] at this
  haveI := hW
  unfold multAt
  rw [dite_eq_left hW, dite_eq_left hW,
    length_localizedModule_quot_eq W
      (fun x hx => ⟨u, hu, mul_mem_sup_span_of_sub_mem hm hx⟩)
      (fun x hx => ⟨v, hv, mul_mem_sup_span_of_sub_mem hm' hx⟩)]

theorem cycles_eq_of_isUnitSec :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (f g : MRing ι),
      IsUnitSec P f g → divSupp P f = divSupp P g ∧
        (∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W) ∧
        ∀ (n : ℕ) (L : Fin n → HermLine ι), vertR P L f = vertR P L g := by
  intro K _ ι _ P f g h
  have hsupp : divSupp P f = divSupp P g :=
    Set.Subset.antisymm (divSupp_subset_of_isUnitSec h) (divSupp_subset_of_isUnitSec h.symm)
  have hmult : ∀ W ∈ divSupp P f, multAt (P ⊔ Ideal.span {f}) W = multAt (P ⊔ Ideal.span {g}) W := by
    rintro W ⟨hmin, hrel⟩
    have hWp : W.IsPrime := hmin.1.1
    obtain ⟨u, v, hu, hv, hm⟩ := h W hWp (le_sup_left.trans hmin.1.2) hrel
    exact multAt_sup_span_eq_of_sub_mem hWp hu hv hm
  refine ⟨hsupp, hmult, fun n L => ?_⟩
  unfold vertR
  rw [← hsupp]
  refine finsum_mem_congr rfl fun W hW => ?_
  rw [hmult W hW]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PlurisubharmonicCones.NefFibresScaledLattice

section

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.TiePrimes

namespace LevelTowerAlt

namespace N1

section

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

theorem homog_sub {a b : MRing J} {d : K → ℕ} (ha : IsMultiHomog a d) (hb : IsMultiHomog b d) :
    IsMultiHomog (a - b) d := by
  have h := homog_add ha (homog_mul (homog_C (J := J) (-1)) hb |> fun h => (zero_add d) ▸ h)
  have e : a + C (-1) * b = a - b := by simp [sub_eq_add_neg]
  rwa [e] at h

theorem cMon_notMem {W : Ideal (MRing J)} (hW : W.IsPrime) {c : ∀ k, J k} (hc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W)
    (d : K → ℕ) : cMon c d ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hW)).1 h
  exact hc k (hW.mem_of_pow_mem _ hk)

theorem aeval_cMon (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (d : K → ℕ) :
    aeval y (cMon c d) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [cMon]

theorem exists_rep (y : (Σ k, J k) → Ω) (c : ∀ k, J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (lam : Ω) (hl : lam ≠ 0) (b : K → ℤ)
    (h1 : lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) ∈ (dh y c).range) (h2 : (lam * ∏ k, y ⟨k, c k⟩ ^ (-b k))⁻¹ ∈ (dh y c).range) :
    ∃ (F G : MRing J) (dF dG : K → ℕ), IsMultiHomog F dF ∧ IsMultiHomog G dG ∧ (∀ k, (dF k : ℤ) = dG k + b k) ∧
      aeval y F = lam * aeval y G ∧
      ∀ W : Ideal (MRing J), W.IsPrime → mCoordIdeal y ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → F ∉ W ∧ G ∉ W := by
  obtain ⟨f, hf⟩ := h1
  obtain ⟨f', hf'⟩ := h2
  obtain ⟨D, g, hg, e⟩ := exists_form_dh hc f
  obtain ⟨D', g', hg', e'⟩ := exists_form_dh hc f'
  replace e : dh y c g = lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) := e.trans hf
  replace e' : dh y c g' = (lam * ∏ k, y ⟨k, c k⟩ ^ (-b k))⁻¹ := e'.trans hf'
  have hw : lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) ≠ 0 :=
    mul_ne_zero hl (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k))
  refine ⟨g * cMon c (fun k => (b k).toNat), cMon c (D + fun k => (-b k).toNat), D + fun k => (b k).toNat, _,
    homog_mul hg (homog_cMon _ _), homog_cMon _ _, fun k => ?_, ?_, fun W hW hP hX => ⟨fun h => ?_, cMon_notMem hW hX _⟩⟩
  · simp only [Pi.add_apply]; push_cast; omega
  · rw [map_mul, aeval_eq_dh_mul y c hc hg, e, aeval_cMon, aeval_cMon, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k), ← zpow_add₀ (hc k)]
    congr 1
    simp only [Pi.add_apply]; push_cast; omega
  · have hgW : g ∈ W := (hW.mem_or_mem h).resolve_right (cMon_notMem hW hX _)
    have hm : g * g' - cMon c (D + D') ∈ mCoordIdeal y := by
      rw [mem_coord_iff y (homog_sub (homog_mul hg hg') (homog_cMon _ _)), map_sub, map_mul,
        aeval_eq_dh_mul y c hc hg, aeval_eq_dh_mul y c hc hg', e, e', aeval_cMon, mul_mul_mul_comm,
        mul_inv_cancel₀ hw, one_mul, ← Finset.prod_mul_distrib]
      simp [pow_add]
    refine cMon_notMem hW hX (D + D') ?_
    have : cMon c (D + D') = g * g' - (g * g' - cMon c (D + D')) := by ring
    rw [this]
    exact W.sub_mem (W.mul_mem_right _ hgW) (hP hm)

theorem geoNum_one_add (W : Ideal (MRing J)) (a b : K → ℤ) :
    geoNum 1 W (fun _ => a + b) = geoNum 1 W (fun _ => a) + geoNum 1 W (fun _ => b) := by
  simp only [geoNum]
  split_ifs with h
  · simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  · simp

theorem geoNum_eq_zero (y : (Σ k, J k) → Ω) (lam : Ω) (hl : lam ≠ 0) (b : K → ℤ)
    (h : ∀ c : ∀ k, J k, (∀ k, y ⟨k, c k⟩ ≠ 0) → lam * ∏ k, y ⟨k, c k⟩ ^ (-b k) ∈ (dh y c).range ∧
      (lam * ∏ k, y ⟨k, c k⟩ ^ (-b k))⁻¹ ∈ (dh y c).range)
    (W : Ideal (MRing J)) (hW : IsMultiProjPrime W) (hP : mCoordIdeal y ≤ W) (hch : charOf W ≠ 0)
    (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    geoNum 1 W (fun _ => b) = 0 := by
  classical
  have rep : ∀ U : Ideal (MRing J), U.IsPrime → mCoordIdeal y ≤ U → IsRelevant U →
      ∃ (F G : MRing J) (dF dG : K → ℕ), IsMultiHomog F dF ∧ IsMultiHomog G dG ∧ (∀ k, (dF k : ℤ) = dG k + b k) ∧
      aeval y F = lam * aeval y G ∧ F ∉ U ∧ G ∉ U := by
    intro U hU hPU hr
    choose c hc using hr
    have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (hPU ((mem_coord_iff y (homog_X ⟨k, c k⟩)).2 (by simpa using h0)))
    obtain ⟨F, G, dF, dG, h1, h2, h3, h4, h5⟩ := exists_rep y c hy lam hl b (h c hy).1 (h c hy).2
    exact ⟨F, G, dF, dG, h1, h2, h3, h4, h5 U hU hPU hc⟩
  obtain ⟨F, G, dF, dG, hF, hG, hd, hFG, hFW, hGW⟩ := rep W hW.1 hP hW.2.2
  have hu : Flat.IsUnitSec W F G := by
    intro U hU hWU hr
    obtain ⟨F', G', dF', dG', hF', hG', hd', hFG', hFU, hGU⟩ := rep U hU (hP.trans hWU) hr
    refine ⟨G', F', hGU, hFU, hP ?_⟩
    have e : dF' + dG = dG' + dF := funext fun k => by
      have := hd k; have := hd' k; simp only [Pi.add_apply]; omega
    rw [mem_coord_iff y (homog_sub (homog_mul hG' hF) (e ▸ homog_mul hF' hG)), map_sub, map_mul, map_mul, hFG, hFG']
    ring
  have hs : divSupp W F = divSupp W G :=
    Set.Subset.antisymm (GlobalTheory.CompanionTheory.Ar.Flat.divSupp_subset_of_isUnitSec hu)
      (GlobalTheory.CompanionTheory.Ar.Flat.divSupp_subset_of_isUnitSec
        (GlobalTheory.CompanionTheory.Ar.Flat.IsUnitSec.symm hu))
  have hm : ∀ U ∈ divSupp W F, multAt (W ⊔ Ideal.span {F}) U =
      multAt (W ⊔ Ideal.span {G}) U := by
    rintro U ⟨hmin, hrel⟩
    have hUp : U.IsPrime := hmin.1.1
    obtain ⟨s, t, hs, ht, hst⟩ := hu U hUp (le_sup_left.trans hmin.1.2) hrel
    exact GlobalTheory.CompanionTheory.Ar.Flat.multAt_sup_span_eq_of_sub_mem hUp hs ht hst
  have hp := PB.prime_charOf_of_ne_zero hW.1 hch
  have hD : ∀ (d : K → ℕ) (s : MRing J), IsMultiHomog s d → s ∉ W →
      geoNum 1 W (fun _ => fun k => (d k : ℤ)) =
        ∑ᶠ U ∈ divSupp W s, (multAt (W ⊔ Ideal.span {s}) U : ℤ) * geoNum 0 U (Fin.elim0 : Fin 0 → K → ℤ) := by
    intro d s hs hsW
    have hcut := GroundTheory.Heights₂.Heights.Inter.GeoNumCut.full K J W 0 Fin.elim0 d s hW hp (by rw [hdim]) hs hsW
    have hsn : (Fin.snoc (Fin.elim0 : Fin 0 → K → ℤ) (fun k => (d k : ℤ)) : Fin 1 → K → ℤ) =
        fun _ => fun k => (d k : ℤ) := by
      funext i
      rw [Fin.fin_one_eq_zero i]
      simp [Fin.snoc]
    rwa [hsn] at hcut
  have e1 : geoNum 1 W (fun _ => fun k => (dF k : ℤ)) = geoNum 1 W (fun _ => fun k => (dG k : ℤ)) := by
    rw [hD dF F hF hFW, hD dG G hG hGW, ← hs]
    exact finsum_mem_congr rfl fun U hU => by rw [hm U hU]
  have e2 : (fun k => (dF k : ℤ)) = (fun k => (dG k : ℤ)) + b := funext hd
  rw [e2, geoNum_one_add] at e1
  linarith

end

end N1

open N1

theorem nef_fibres_scaled_lattice : PB.Inputs → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (a a' : K → ℤ) (e e' u : Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → u ≠ 0 → L.IsDegOn Set.univ y a e → (L.scale u).IsDegOn Set.univ y a' e' → NefOnFibres (mCoordIdeal y) a → NefOnFibres (mCoordIdeal y) a' := by
  intro _ X Ω _ _ K _ J _ y ξ L a a' e e' u tie hu h h' hnef W hW hP hch hdim
  have hl : u * e / e' ≠ 0 := div_ne_zero (mul_ne_zero hu h.1) h'.1
  have h0 := geoNum_eq_zero y (u * e / e') hl (a' - a) (fun c hc => ?_) W hW hP hch hdim
  · have e2 : a' = a + (a' - a) := by abel
    rw [e2, geoNum_one_add, h0, add_zero]
    exact hnef W hW hP hch hdim
  have key : ∀ p : Cpt ξ, InChart ξ (seg y) c p →
      u * e / e' * ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k) ∈ regAt ξ p ∧
        (u * e / e' * ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k))⁻¹ ∈ regAt ξ p := by
    intro p hp
    have e1 := h.2 p trivial c hp
    have e2 := h'.2 p trivial c hp
    have e3 : Submodule.span (regAt ξ p) {u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)} =
        Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'} := by
      rw [← smul_eq_mul (∏ k, y ⟨k, c k⟩ ^ a' k), ← e2, Lat.scale, Lat.map, e1, Submodule.map_span, Set.image_singleton]
      rfl
    have n1 : ∏ k, y ⟨k, c k⟩ ^ a k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)
    have n2 : ∏ k, y ⟨k, c k⟩ ^ a' k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hc k)
    have e4 : ∏ k, y ⟨k, c k⟩ ^ (-(a' - a) k) = (∏ k, y ⟨k, c k⟩ ^ a k) / ∏ k, y ⟨k, c k⟩ ^ a' k := by
      rw [← Finset.prod_div_distrib]
      exact Finset.prod_congr rfl fun k _ => by rw [← zpow_sub₀ (hc k)]; simp
    have he := h.1
    have he' := h'.1
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (e3 ▸ Submodule.mem_span_singleton_self _ :
      u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e) ∈ Submodule.span (regAt ξ p) {(∏ k, y ⟨k, c k⟩ ^ a' k) * e'})
    obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.1 (e3.symm ▸ Submodule.mem_span_singleton_self _ :
      (∏ k, y ⟨k, c k⟩ ^ a' k) * e' ∈ Submodule.span (regAt ξ p) {u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)})
    replace hr : (r : Ω) * ((∏ k, y ⟨k, c k⟩ ^ a' k) * e') = u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e) := hr
    replace hr' : (r' : Ω) * (u * ((∏ k, y ⟨k, c k⟩ ^ a k) * e)) = (∏ k, y ⟨k, c k⟩ ^ a' k) * e' := hr'
    rw [e4]
    constructor
    · convert r.2 using 1
      field_simp
      linear_combination -hr
    · convert r'.2 using 1
      field_simp
      linear_combination -hr'
  rw [← adjoin_eq hc]
  exact ⟨(tie.ring c (seg_ne hc) _).2 fun p hp => (key p hp).1, (tie.ring c (seg_ne hc) _).2 fun p hp => (key p hp).2⟩

end LevelTowerAlt
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.NefDegreeScaleInvariant

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.CompanionTheory.Relay.nef_degree_scale_invariant : PB.Inputs → ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (ξ : Sp Ω ⟶ X) (L : Lat ξ Ω) (a a' : K → ℤ) (e e' u : Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → u ≠ 0 → L.IsDegOn Set.univ y a e → (L.scale u).IsDegOn Set.univ y a' e' → NefOnFibres (mCoordIdeal y) a → NefOnFibres (mCoordIdeal y) a' := by
  first | exact @LevelTowerAlt.nef_fibres_scaled_lattice | exact LevelTowerAlt.nef_fibres_scaled_lattice
end
end
