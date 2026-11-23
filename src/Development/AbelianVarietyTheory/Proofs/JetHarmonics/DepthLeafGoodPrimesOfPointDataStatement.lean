module

public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermCut
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPoint
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
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimeLeafStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FirstRowsBoundAndSizesBoundsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GoodPrimeWeightHypothesesOfDepthParametersStatement
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.ProjectiveLattices.CrudeVal
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotDvdDiscrHost
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabelBijectiveCardEqF
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegreeStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIntegralChartIntegralFramedPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

theorem _root_.GlobalTheory.T.exists_integral_chart_integral_framed_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], IntegralChartExists Xo c ∧ ((∀ a : 𝓞 E, star a = H.bar a) → IntChartEx Xo c) ∧ ((∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ C : IntegralChartA3 Xo c T io y, FrTrunc C.I.G (𝟙 (Sp T.V)) (chD C.ch) C.xT C.eT) := by
  first | exact @GlobalTheory.IntChartExists.intChart_exists | exact GlobalTheory.IntChartExists.intChart_exists | (intros; apply GlobalTheory.IntChartExists.intChart_exists <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.ComapLiesOver

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrobPlace

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem comap_liesOver {E K : Type} [Field E] [Field K] [NumberField K] (f : 𝓞 E →+* 𝓞 K)
    (la : HeightOneSpectrum (𝓞 K)) :
    (la.asIdeal.comap f).LiesOver (Ideal.span {((resCharOf la : ℕ) : ℤ)}) := by
  have hl := Crude.resCharOf_prime la
  have hP := la.isPrime
  have hmax : (Ideal.span {((resCharOf la : ℕ) : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl).irreducible
  have hle : Ideal.span {((resCharOf la : ℕ) : ℤ)} ≤ (la.asIdeal.comap f).under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show f (algebraMap ℤ (𝓞 E) ((resCharOf la : ℕ) : ℤ)) ∈ la.asIdeal
    rw [map_natCast, map_natCast]
    exact Crude.crv_char_mem la
  have hne : (la.asIdeal.comap f).under ℤ ≠ ⊤ := by
    intro h
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : ℤ) ∈ (la.asIdeal.comap f).under ℤ := by rw [h]; trivial
    change f (algebraMap ℤ (𝓞 E) 1) ∈ la.asIdeal at h1
    rwa [map_one, map_one] at h1
  exact ⟨hmax.eq_of_le hne hle⟩

theorem card_under {S : Type} [CommRing S] (p : ℕ) (Q : Ideal S) [h : Q.LiesOver (Ideal.span {(p : ℤ)})] :
    Nat.card (ℤ ⧸ Q.under ℤ) = p := by
  rw [← h.over, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]

theorem eTau_plOf (D : D7) (z : RPl D.R) :
    ((D.eTau (plOf D z) : D.R.Psi) : D.R.GG) =
      ((if z.1 then -1 else 1, 1), D.R.iota z.2) := by
  unfold plOf
  rw [Equiv.apply_symm_apply]
  cases z.1 <;> rfl

theorem inert_ne {N : NumDatum} {l : ℕ} (h : Inert N l) : l ∉ N.H.small ∧ l ≠ N.q ∧ l ≠ N.d := by
  unfold Inert NumDatum.cls primeClass at h
  refine ⟨fun h2 => ?_, fun hq => ?_, fun hd => ?_⟩
  · rw [if_pos h2] at h
    rcases h with h | h <;> cases h
  · rw [if_pos hq] at h
    split_ifs at h <;> rcases h with h | h <;> cases h
  · rw [if_pos hd] at h
    split_ifs at h <;> rcases h with h | h <;> cases h

theorem gal_step (D : D7) (L : SizeData₂ D) (p : ℕ) [Fact p.Prime] (hI : Inert (numOf D L) p)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) (z : RPl D.R) :
    ((D.eTau (plOf D ((numOf D L).pos p z 1)) : D.R.Psi) : D.R.GG) * D.R.cc =
      ((D.eTau (plOf D z) : D.R.Psi) : D.R.GG) *
        D.host.galE σ := by
  obtain ⟨h2, hq, hd⟩ := inert_ne hI
  have hN : ¬ p ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  have hc : p.Coprime D.host.condN := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hN
  have hC := factClassFrob D.R D.host p hN P σ hσ
  have hH : (D.host.galE σ).2 = D.R.iota ((numOf D L).hP p) := by
    have e1 := (D.host.toHostAx.frob_iff p hc P σ).1 hσ
    have e2 : (numOf D L).hP p = D.R.iotaInv (D.host.art (ZMod.unitOfCoprime p hc)).2 := dif_pos hc
    rw [e2, Formalism.HC.Frame.iota_iotaInv]
    exact congrArg Prod.snd e1
  have hcls : (numOf D L).cls p = D.host.cls p := rfl
  have hpos := eTau_plOf D
    (xor z.1 (decide (D.host.cls p = PrimeClass.signal ∧ Odd 1)), z.2 + 1 • (numOf D L).hP p)
  refine (congrArg (· * D.R.cc) hpos).trans ?_
  rw [eTau_plOf]
  refine Prod.ext ?_ ?_
  · rcases hI with h | h
    · rw [hcls] at h
      have h1 := hC.2.2.1 h
      simp only [Prod.fst_mul, h1, h, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
      cases z.1 <;> simp
    · rw [hcls] at h
      have h1 := hC.2.1.1 h
      simp only [Prod.fst_mul, h1, h, Formalism.HC.Frame.cc, Formalism.FrobeniusOrbits.c0]
      cases z.1 <;> simp
  · simp only [Prod.snd_mul, Formalism.HC.Frame.cc, mul_one, hH]
    rw [Formalism.HC.Frame.iota_add]
    exact congrArg (fun t => D.R.iota z.2 * D.R.iota t) (one_nsmul _)

theorem conj_emb {R : Ranks} (H : Formalism.BasicNotions.Host R) (g g' : R.GG) (σ : H.E ≃ₐ[ℚ] H.E)
    (h : g' * R.cc = g * H.galE σ) (x : H.E) :
    ComplexEmbedding.conjugate (H.emb g') x = H.emb g (σ x) := by
  have hg : ∀ g : R.GG, H.galE (H.sigmaOf g) = g := fun g => MulEquiv.apply_symm_apply _ _
  have he : H.sigmaOf g' * H.conj = H.sigmaOf g * σ := by
    apply H.galE_injective
    rw [H.galE_mul, H.galE_mul, hg, hg, H.galE_conjE, h]
  rw [ComplexEmbedding.conjugate_coe_eq, ← H.conjE_apply (H.emb g') x]
  change H.φ₀ ((H.sigmaOf g' * H.conj) x) = H.φ₀ ((H.sigmaOf g * σ) x)
  rw [he]

theorem frob_place : ∀ (D : D7) (L : SizeData₂ D) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (lv : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff lv) (la : HeightOneSpectrum (𝓞 c.F)), Inert (numOf D L) (resCharOf la) → ∀ (z : RPl D.R) (x : 𝓞 D.host.E),
  ∃ y ∈ la.asIdeal, ((y : 𝓞 c.F) : c.F) = embK c (ComplexEmbedding.conjugate (DV.tauEmb D (plOf D ((numOf D L).pos (resCharOf la) z 1)))) x - embK c (DV.tauEmb D (plOf D z)) x ^ resCharOf la := by
  intro D L H lv c la hI z x
  haveI : Fact (resCharOf la).Prime := ⟨Crude.resCharOf_prime la⟩
  obtain ⟨h2, hq, hd⟩ := inert_ne hI
  let f : 𝓞 D.host.E →+* 𝓞 c.F := RingOfIntegers.mapRingHom (embF c (DV.tauEmb D (plOf D z)))
  haveI := la.isPrime
  haveI := comap_liesOver f la
  have hN : ¬ resCharOf la ∣ D.host.condN := fun h => by
    rcases (D.host.toHostRaw.dvd_condN_iff_small Fact.out).1 h with h | h | h
    exacts [h2 h, hq h, hd h]
  obtain ⟨σ, hσ⟩ := (D.host.der.frob (resCharOf la) hN (la.asIdeal.comap f)).1
  have hg := gal_step D L (resCharOf la) hI (la.asIdeal.comap f) σ hσ z
  have h1 := hσ x
  rw [card_under (resCharOf la)] at h1
  refine ⟨_, h1, ?_⟩
  rw [map_sub, map_pow]
  push_cast
  congr 1
  apply Subtype.ext
  rw [embK_coe]
  exact (conj_emb D.host _ _ σ hg (x : D.host.E)).symm

end GlobalTheory.FrobPlace
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlacesMatchCmTypeFrobeniusOfParameters

section

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem placeTie_of_pins : ∀ (D : D7) (L : SizeData₂ D) (T : Core D), T.Q.Pins →
    PlaceTie (numOf D L) T.Q.c (fun z => DV.tauEmb D (plOf D z)) := by
  intro D L T hp
  have hh := hp.1
  refine ⟨?_, ?_, hh.1, D.host.hostE_isGalois, ?_, ?_, ?_⟩
  · intro z z' h
    exact (plOf_bijective_card D).1.1 (D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h)))
  · intro τ
    constructor
    · intro hτ
      have hex : ∃ t : D.what₂.Tau, τ = DV.tauEmb D t := by
        obtain ⟨g, hg⟩ := (factEmb D.R D.host).1.2 τ
        by_cases hgP : g ∈ D.R.Psi
        · obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D g).2 hgP
          exact ⟨t, hg.symm.trans ht⟩
        · exfalso
          have h2 : g * D.R.cc ∈ D.R.Psi := by
            by_contra h
            exact hgP ((Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem g).2 h)
          obtain ⟨t, ht⟩ := (Formalism.L2.Geo.exists_tauEmb_iff D (g * D.R.cc)).2 h2
          have h3 : DV.tauEmb D t (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hh.2.2.2 t
          rw [← ht, Formalism.L2.Geo.emb_mul_cc_comp, hg, RingHom.comp_apply] at h3
          have h4 : τ (D.host.conj (T.Q.H.rt : D.host.E)) = star (τ (T.Q.H.rt : D.host.E)) := Formalism.MainNotions.WeightFamilies.emb_conj D τ _
          have hτ' : τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
          have hc : (starRingEnd ℂ) T.Q.H.rt0 ≠ T.Q.H.rt0 := by
            intro he
            obtain ⟨x, hx⟩ := Complex.conj_eq_iff_real.1 he
            have hs := T.Q.H.sqrt_neg_disc_sq
            rw [hx] at hs
            have hs' : x ^ 2 = -(T.Q.H.d : ℝ) := by exact_mod_cast hs
            have hd : (0 : ℝ) < T.Q.H.d := by exact_mod_cast T.Q.H.d_prime.pos
            nlinarith [sq_nonneg x]
          apply hc
          calc star T.Q.H.rt0 = star (τ (T.Q.H.rt : D.host.E)) := by rw [hτ']
            _ = τ (D.host.conj (T.Q.H.rt : D.host.E)) := h4.symm
            _ = T.Q.H.rt0 := h3
      obtain ⟨t, ht⟩ := hex
      obtain ⟨z, hz⟩ := (plOf_bijective_card D).1.2 t
      exact ⟨z, by rw [ht, ← hz]⟩
    · rintro ⟨z, rfl⟩
      exact hh.2.2.2 _
  · intro σ τ
    exact D.host.galE_injective (by
      rw [D.host.galE_mul, D.host.galE_mul, mul_comm])
  · intro p hp h2 hq hd
    exact GlobalTheory.GoodDepth.not_dvd_discr_host D.R D.host p hp h2 hq hd
  · intro la hla z x
    exact GlobalTheory.FrobPlace.frob_place D L T.Q.H _ T.Q.c la hla z x

end GlobalTheory.GoodDepth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlacesMatchCmTypeFrobeniusOfParametersStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem _root_.GlobalTheory.T.realPlaces_match_cmTypeFrobenius : ∀ (D : D7) (L : SizeData₂ D) (T : Core D), T.Q.Pins → PlaceTie (numOf D L) T.Q.c (fun z => DV.tauEmb D (plOf D z)) := by
  first | exact @GlobalTheory.GoodDepth.placeTie_of_pins | exact GlobalTheory.GoodDepth.placeTie_of_pins | (intros; apply GlobalTheory.GoodDepth.placeTie_of_pins <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthLeafGoodPrimesOfPointData

section

@[expose] public section

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

namespace GlobalTheory.GoodDepth

theorem numOf_sizes_le (D : D7) (L : SizeData₂ D) (hk : (1 : ℝ) ≤ D.R.k) (hm : (1 : ℝ) ≤ D.R.m) :
    (numOf D L).Sc + (numOf D L).eta ≤ L.Sc + L.etaSz := by
  have hS := L.Sc_pos
  have hE := L.Sc_eq
  have he := L.etaSz_pos
  have hDel : (0 : ℝ) ≤ (D.s.Del : ℝ) := by
    by_contra hneg
    push Not at hneg
    have : (D.R.k : ℝ) * (4 * (D.s.Del : ℝ)) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  have h1 : (numOf D L).Sc ≤ L.Sc := by
    show (D.R.k : ℝ) * (4 * ((⌊(D.s.Del : ℝ)⌋₊ : ℕ) : ℝ)) ≤ L.Sc
    rw [hE]
    have := Nat.floor_le hDel
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : (numOf D L).eta ≤ L.etaSz := by
    show (D.R.m : ℝ) * ((⌊LevelStarExponents.h0 L⌋₊ : ℕ) : ℝ) ≤ L.etaSz
    have hm0 : (0 : ℝ) < D.R.m := by linarith
    have e : L.etaSz = D.R.m * LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; field_simp
    have h0 : 0 ≤ LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; positivity
    rw [e]
    exact mul_le_mul_of_nonneg_left (Nat.floor_le h0) hm0.le
  linarith

theorem card_RPl (R : Ranks) : Fintype.card (RPl R) = R.f := by
  simp [RPl, Ranks.f, Ranks.n, R.card_A]



theorem leafGood_run : ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → (∀ j, PkgSt (T.Q.Xo (ι j)) T.Q.c) → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.depthTable_goodPrimeLeaf 100 (by norm_num)
  refine ⟨C0, ?_⟩
  intro D L Pm Tp hK T hT EX _ K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm R hPk hC hPg hSz hCn hx5 hx hkb tF
  have hb : O.b = L.sc.b := by
    unfold OnObj.b OnObj.xe Scale.b Scale.L
    rw [R.x_eq, R.eps_eq]
  have hL : O.L = L.sc.L := by
    unfold OnObj.L
    rw [hb, Scale.b, Real.log_exp]
  have hb0 : 0 < L.sc.b := Real.exp_pos _
  have hk1 : (1 : ℝ) ≤ D.R.k := R.k_eq ▸ hPg.2.1
  have hm1 : (1 : ℝ) ≤ D.R.m := R.m_eq ▸ hPg.2.2.1
  have hf8 : (8 : ℝ) ≤ D.R.f := R.f_eq ▸ hPg.2.2.2.1
  have hlog : Real.log D.R.k ≤ L.sc.L := by
    have := hSz.2.2.2.2.2.2.1
    rwa [R.k_eq, hL] at this
  refine hC0 D.host.E T.Q.H T.Q.l T.Q.Dw T.Q.Xo T.Q.c (depOf T EX Tp hK) K Bs Df S P oc O ι Nm (numOf D L)
    (fun z => DV.tauEmb D (plOf D z)) hC R.E_eq R.σ_eq R.T_eq ⟨R.jets_eq_fact, R.g2_eq, R.cmQuadraticForm_eq_alternatingForm, R.dd_eq, R.sm_eq⟩
    (piSplit_depDataOf ..) (levelQ_depDataOf _ _ _ _ _ _ _ _ _ hT) R.star_eq
    (fun j => (GlobalTheory.T.exists_integral_chart_integral_framed_point _ _ _ _ _ _).2.1 R.star_eq) hPk (GlobalTheory.T.realPlaces_match_cmTypeFrobenius D L T hT.pins) (fun j => ?_) ?_ hPg tF
    ⟨R.jets_eq_fact, R.g2_eq, R.cmQuadraticForm_eq_alternatingForm, R.dd_eq, R.sm_eq⟩
  · have hj := R.inR j
    have hd := hT.pins.2.2.2 _ hj
    refine ⟨hj.1, hj.2, hd.1, hd.2.1, fun τ i i' h => (dom_wtA (lR Tp hK (ι j))).1 τ h, ?_⟩
    rw [hb, hL]
    exact GlobalTheory.T.goodPrimeWeightHypotheses_of_depthParameters D L Pm Tp hK T hT.pins hCn hx5 hx hkb hlog _ hj
  · refine ⟨R.k_eq, R.m_eq, R.f_eq, ?_, R.depthNumbers_threshold_eq, R.th_eq, R.ad_eq, fun j => ?_, fun j => ?_, fun j => ?_⟩
    · unfold OnObj.Se
      rw [R.Sc_eq, R.eta_eq]
      exact numOf_sizes_le D L hk1 hm1
    · rw [R.wt_eq]
      have h := (GlobalTheory.T.firstRows_bound_and_sizes_bounds D L Pm Tp hK (ι j) (R.inR j) hx hkb).2
      calc (∑ z, (numOf D L).w (ι j) z) ≤ ∑ _z : RPl D.R, 2 * L.sc.b := Finset.sum_le_sum fun z _ => (h z).2
        _ = 2 * (D.R.f : ℝ) * L.sc.b := by
          rw [Finset.sum_const, Finset.card_univ, card_RPl, nsmul_eq_mul]; ring
    · rw [R.wt_eq, hb]; nlinarith
    · have h := (GlobalTheory.T.weightExponents_embeddings_degree D T.Q hT.pins (ι j) (R.inR j) (lR Tp hK (ι j))).1
      have h2 := R.DF_ge j
      rw [← h] at h2
      exact h2

end GlobalTheory.GoodDepth
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthLeafGoodPrimesOfPointDataStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

theorem _root_.GlobalTheory.T.depthLeaf_goodPrimes_of_point_data : ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Core D), LawsM T → ∀ (EX : ErrX D) [StarRing (𝓞 D.host.E)] (K : Type) [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)] [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (oc : OnConst) (O : OnObj S P oc) (ι : Bs.J → ℕ) (Nm : IndefNum Bs),
  RunTie T EX Tp hK O ι → (∀ j, PkgSt (T.Q.Xo (ι j)) T.Q.c) → C0 ≤ oc.C → LeafPage O → LeafSizes O → 10 ≤ Pm.CnW → 3 ≤ L.sc.x ^ (L.sc.ez / 5) → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b →
  DepthCond.ContentEqualsDatumContent Nm (numOf D L) ι → LeafDepthGood Nm O := by
  first | exact @GlobalTheory.GoodDepth.leafGood_run | exact GlobalTheory.GoodDepth.leafGood_run | (intros; apply GlobalTheory.GoodDepth.leafGood_run <;> assumption)
end
end
