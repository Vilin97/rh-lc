module

public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsCmTypeEmbeddingsIntoValuationRingStatement
public import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsEigenBasisMapFlatBaseChangeStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextCoeffSecondLinear
public import Mathlib.RingTheory.Flat.TorsionFree

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsIsEigenBasis

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

theorem eigBasis_of_generic {V K : Type} [CommRing V] [IsDomain V] [Field K] [Algebra V K] [IsFractionRing V K]
    {A J : Type} [Fintype J] {m : J → ℕ} {d : ℕ} (M : A → Matrix (Fin d) (Fin d) V) (χ : J → A → K)
    (hsep : ∀ j j', j ≠ j' → ∃ a, χ j a ≠ χ j' a) (u : (Σ j, Fin (m j)) → Fin d → V)
    (heig : ∀ a ℓ i, ∑ k, algebraMap V K (M a i k) * algebraMap V K (u ℓ k) = χ ℓ.1 a * algebraMap V K (u ℓ i))
    (hbas : ∀ p : Fin d → K, ∃! b : (Σ j, Fin (m j)) → K, ∀ k, ∑ ℓ, b ℓ * algebraMap V K (u ℓ k) = p k)
    (τ : J) (t : A → V) (ht : ∀ a, algebraMap V K (t a) = χ τ a)
    (hsat : ∀ (v : Fin d → V) (a : V), a ≠ 0 →
      a • v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩) →
      v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩)) :
    (∀ i a, (M a).mulVec (u ⟨τ, i⟩) = t a • u ⟨τ, i⟩) ∧
      ∀ v : Fin d → V, (∀ a, (M a).mulVec v = t a • v) → ∃! c : Fin (m τ) → V, ∑ i, c i • u ⟨τ, i⟩ = v := by
  classical
  have hinj : Function.Injective (algebraMap V K) := IsFractionRing.injective V K
  have hext : ∀ (g : Fin (m τ) → K) (k : Fin d),
      ∑ ℓ : (Σ j, Fin (m j)), (if h : ℓ.1 = τ then g (h ▸ ℓ.2) else 0) * algebraMap V K (u ℓ k) =
        ∑ i, g i * algebraMap V K (u ⟨τ, i⟩ k) := by
    intro g k
    rw [Fintype.sum_sigma, Finset.sum_eq_single τ]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  refine ⟨fun i a => ?_, fun v hv => ?_⟩
  · funext k
    apply hinj
    have := heig a ⟨τ, i⟩ k

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, ht]
    exact this
  obtain ⟨b, hb, -⟩ := hbas fun k => algebraMap V K (v k)
  have hb0 : ∀ ℓ : (Σ j, Fin (m j)), ℓ.1 ≠ τ → b ℓ = 0 := by
    intro ℓ hℓ
    obtain ⟨a, ha⟩ := hsep _ _ hℓ
    have h1 : ∀ k, ∑ ℓ', (b ℓ' * χ ℓ'.1 a) * algebraMap V K (u ℓ' k) = χ τ a * algebraMap V K (v k) := by
      intro k
      have h2 := congrArg (algebraMap V K) (congrFun (hv a) k)

      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Pi.smul_apply, smul_eq_mul, ht] at h2
      rw [← h2]
      simp only [← hb, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ℓ' _ => ?_
      rw [mul_assoc, ← heig, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      ring
    have h2 : ∀ k, ∑ ℓ', (χ τ a * b ℓ') * algebraMap V K (u ℓ' k) = χ τ a * algebraMap V K (v k) := by
      intro k
      rw [← hb, Finset.mul_sum]
      simp only [mul_assoc]
    have h3 := congrFun ((hbas fun k => χ τ a * algebraMap V K (v k)).unique h1 h2) ℓ
    have h4 : b ℓ * (χ ℓ.1 a - χ τ a) = 0 := by
      rw [mul_sub, h3]; ring
    exact (mul_eq_zero.1 h4).resolve_right (sub_ne_zero.2 ha)
  have hb1 : ∀ k, ∑ i, b ⟨τ, i⟩ * algebraMap V K (u ⟨τ, i⟩ k) = algebraMap V K (v k) := by
    intro k
    rw [← hb k, Fintype.sum_sigma, Finset.sum_eq_single τ]
    · intro j _ hj
      exact Finset.sum_eq_zero fun i _ => by rw [hb0 ⟨j, i⟩ hj, zero_mul]
    · simp
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors V) fun i => b ⟨τ, i⟩
  choose g hg using hs
  have hmem : (s : V) • v ∈ Submodule.span V (Set.range fun i : Fin (m τ) => u ⟨τ, i⟩) := by
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨g, funext fun k => hinj ?_⟩

    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, hg, ← hb1, Finset.mul_sum]
    simp only [Algebra.smul_def, mul_assoc]
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1 (hsat v s (nonZeroDivisors.ne_zero s.2) hmem)
  refine ⟨c, hc, fun c' hc' => ?_⟩
  have hK : ∀ c : Fin (m τ) → V, ∑ i, c i • u ⟨τ, i⟩ = v → ∀ k,
      ∑ ℓ : (Σ j, Fin (m j)), (if h : ℓ.1 = τ then algebraMap V K (c (h ▸ ℓ.2)) else 0) * algebraMap V K (u ℓ k) =
        algebraMap V K (v k) := by
    intro c hc k
    rw [hext (fun i => algebraMap V K (c i)) k, ← hc]

    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  have h5 := (hbas fun k => algebraMap V K (v k)).unique (hK c' hc') (hK c hc)
  funext i
  apply hinj
  simpa using congrFun h5 ⟨τ, i⟩

theorem isEigBasis_uvecT : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing;
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ)
      (τT : 𝓞 E →+* T.V), (∀ a, algebraMap T.V T.Fr (τT a) = io (embK c τ a)) →
      IsEigBasis Ch.actT τT (fun i : Fin (Dw.mult τ) => Ch.uvecT ⟨τ, i⟩) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch τ τT hτ
  letI := io.toAlgebra
  have hu : ∀ ℓ i, Ch.ch.uvec ℓ i = algebraMap T.V T.Fr (Ch.uvecT ℓ i) := Ch.gen.1.2.2.2.2.2.2
  have hA : ∀ a j, Ch.ch.B.A.act a j = MvPowerSeries.map (algebraMap T.V T.Fr) (Ch.actT a j) := Ch.gen.1.2.1
  refine eigBasis_of_generic (K := T.Fr) (m := Dw.mult) (fun a => linPart (Ch.actT a))
    (fun τ a => io (embK c τ a)) ?_ Ch.uvecT ?_ ?_ τ τT hτ (SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ).2
  · intro j j' h
    obtain ⟨a, ha⟩ := GlobalTheory.EigDir.embK_sep c j j' h
    exact ⟨a, fun e => ha (io.injective e)⟩
  · intro a ℓ i
    have h := GlobalTheory.EigDir.linEig_holds E H Dw l Xo c T.Fr y.1 Ch.ch a ℓ i
    simp only [hu, ReciprocityTheory.ChartRestriction.G.TB.dLin, hA] at h
    exact h
  · intro p
    have h := Ch.ch.chart.basis p
    simp only [hu] at h
    exact h

end GlobalTheory.CharDepth
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsIsEigenBasisStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integral_chart_directions_isEigenBasis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (τ : E →+* ℂ) (τT : 𝓞 E →+* T.V), (∀ a, algebraMap T.V T.Fr (τT a) = io (embK c τ a)) → IsEigBasis Ch.actT τT (fun i : Fin (Dw.mult τ) => Ch.uvecT ⟨τ, i⟩) := by
  first | exact @GlobalTheory.CharDepth.isEigBasis_uvecT | exact GlobalTheory.CharDepth.isEigBasis_uvecT | (intros; apply GlobalTheory.CharDepth.isEigBasis_uvecT <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmTypeDirectionsEigenbasisValuedIntegers

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth.EigExt

theorem res_surjective_of_extends {R O : Type} [CommRing R] [CommRing O] (ι : R →+* O) {d s : ℕ}
    (u : Fin s → Fin d → R) (w : Fin d → Fin d → R) (emb : Fin s ↪ Fin d) (hw : ∀ i, w (emb i) = u i)
    (hb : ∀ v : Fin d → R, ∃! a : Fin d → R, ∀ j, ∑ k, a k * w k j = v j) :
    Function.Surjective (res (fun i j => ι (u i j))) := by
  classical
  have h1 : IsUnit (Matrix.of w) := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    intro v
    obtain ⟨a, ha, -⟩ := hb v
    exact ⟨a, funext fun j => ha j⟩
  have h2 : IsUnit (ι.mapMatrix (Matrix.of w)) := h1.map _
  rw [← Matrix.mulVec_surjective_iff_isUnit] at h2
  intro g
  obtain ⟨f, hf⟩ := h2 (Function.extend emb g 0)
  refine ⟨f, funext fun i => ?_⟩
  have h3 := congrFun hf (emb i)
  rw [emb.injective.extend_apply] at h3
  rw [← h3]
  show ∑ j, ι (u i j) * f j = ∑ j, ι (w (emb i) j) * f j
  rw [hw]

theorem ι_injective {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) : Function.Injective X.ι := by
  intro a b h
  apply IsFractionRing.injective T.V T.Fr
  apply X.ιF.injective
  rw [X.comp, X.comp, h]

theorem flat {T : CDVR} {p : ℕ} [Fact p.Prime] (X : ValExt T p) :
    letI := X.ι.toAlgebra; Module.Flat T.V X.O := by
  letI := X.ι.toAlgebra
  haveI : IsDomain X.O := Function.Injective.isDomain (algebraMap X.O X.C) X.ints.hom_inj
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : X.ι a * x = 0 := hx
  have ha' : X.ι a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (ι_injective X (h.trans (map_zero _).symm))
  exact (mul_eq_zero.1 hx').resolve_left ha'

theorem linPart_add {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)] {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}
    (Ch : IntegralChartA3 Xo c T io y) (a b : 𝓞 E) :
    linPart (Ch.actT (a + b)) = linPart (Ch.actT a) + linPart (Ch.actT b) := by
  letI := io.toAlgebra
  have key : ∀ a i j, ReciprocityTheory.ChartRestriction.G.TB.dAct T.Fr Ch.ch.B a i j = algebraMap T.V T.Fr (linPart (Ch.actT a) i j) := by
    intro a i j
    show MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1)
      (MvPowerSeries.map (algebraMap T.Fr T.Fr) (Ch.ch.B.A.act a i)) = _
    rw [MvPowerSeries.coeff_map, Ch.gen.1.2.1 a i, MvPowerSeries.coeff_map]
    rfl
  ext i j
  apply IsFractionRing.injective T.V T.Fr
  rw [Matrix.add_apply, map_add (f := _), ← key, ← key, ← key, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigA.dAct_add, Matrix.add_apply]

end GlobalTheory.CharDepth.EigExt


open GlobalTheory.CharDepth.EigExt in
theorem GlobalTheory.CharDepth.isEigBasis_valExt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (p : ℕ) [Fact p.Prime] (X : ValExt T p) (τO : (E →+* ℂ) → (𝓞 E →+* X.O)), IsTypes X io τO → ∀ τ : E →+* ℂ, IsEigBasis (fun a i => MvPowerSeries.map X.ι (Ch.actT a i)) (τO τ) (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j)) ∧ Function.Surjective (res (fun (i : Fin (Dw.mult τ)) j => X.ι (Ch.uvecT ⟨τ, i⟩ j))) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y Ch p _ X τO hτ τ
  constructor
  · obtain ⟨τT, hT, hT', -⟩ := GlobalTheory.T.exists_cmType_embeddings_into_valuation_ring E H l c T io p X
    have he : τO τ = X.ι.comp (τT τ) := by
      ext a
      apply X.ints.hom_inj
      rw [hτ τ a]
      exact (hT' τ a).symm
    letI := X.ι.toAlgebra
    haveI := flat X
    rw [he]
    exact GlobalTheory.T.isEigenBasis_map_flat_baseChange T.V X.O (𝓞 E) _ _ Ch.actT (linPart_add Ch) (τT τ) _
      (GlobalTheory.T.integral_chart_directions_isEigenBasis E H Dw l Xo c T io y Ch τ (τT τ) (hT τ))
  · obtain ⟨⟨w, emb, hw, hb⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y Ch τ
    exact res_surjective_of_extends X.ι _ w emb hw hb
end
end
