module

public import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
public import Mathlib.RingTheory.Kaehler.Basic
public import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.AlgebraicIndependentFreeVar
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AeEvalCircleMapNeZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AemeasurableFinsumSection
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenseMvPolynomialEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEmbeddingsOverInjective
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsMeasurableRootsEnumeration
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
public import Mathlib.RingTheory.Adjoin.Polynomial.Transcendental
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAdmissible
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteVerticalGaussValuations
public import Mathlib.FieldTheory.Separable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Topology.Algebra.MvPolynomial
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.PrimitiveElement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TotallySplit
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteNormDiscreteNeZeroOfIsDedekindDomain

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem finite_normDiscrete_ne_zero_of_isDedekindDomain {S L : Type*} [CommRing S]
    [IsDedekindDomain S] [Field L] [Algebra S L] [IsFractionRing S L] (g : L) (hg : g ≠ 0) :
    {w : AddValuation L (WithTop ℤ) |
      IsNormDiscrete w ∧ (∀ s : S, 0 ≤ w (algebraMap S L s)) ∧ w g ≠ 0}.Finite := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := S) g
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hb1 : algebraMap S L b ≠ 0 := fun h =>
    hb0 (IsFractionRing.injective S L (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hg
  have hI : Ideal.span {a * b} ≠ (⊥ : Ideal S) := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero ha0 hb0
  refine ((Ideal.finite_factors hI).image (ValPl.addv L)).subset ?_
  rintro w ⟨hw, h0, hwg⟩
  let Q : Ideal S :=
    { carrier := {b | 0 < w (algebraMap S L b)}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, map_add (f := _)] at ha hb ⊢
        exact lt_of_lt_of_le (lt_min ha hb) (w.map_add _ _)
      zero_mem' := by simp
      smul_mem' := fun c b hb => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul, AddValuation.map_mul] at hb ⊢
        exact lt_of_lt_of_le hb (le_add_of_nonneg_left (h0 c)) }
  have hz : ∀ s : S, s ∉ Q → w (algebraMap S L s) = 0 := fun s hs =>
    le_antisymm (not_lt.1 (hs : ¬ 0 < w (algebraMap S L s))) (h0 s)
  have hprime : Q.IsPrime := by
    refine ⟨fun htop => ?_, fun {a b} hab => ?_⟩
    · have h1 : (1 : S) ∈ Q := htop ▸ Submodule.mem_top
      simp [Q] at h1
    · change 0 < w (algebraMap _ L (a * b)) at hab
      rw [map_mul, AddValuation.map_mul] at hab
      by_contra hno
      rw [not_or] at hno
      rw [hz a hno.1, hz b hno.2, add_zero] at hab
      exact lt_irrefl _ hab
  have hab : a * b ∈ Q := by
    by_contra hno
    have ha := hz a fun h => hno (Q.mul_mem_right _ h)
    have hb := hz b fun h => hno (Q.mul_mem_left _ h)
    have h := w.map_mul (algebraMap S L a / algebraMap S L b) (algebraMap S L b)
    rw [div_mul_cancel₀ _ hb1, ha, hb, add_zero] at h
    exact hwg h.symm
  have hne : Q ≠ ⊥ := fun h => mul_ne_zero ha0 hb0 (by rwa [h, Ideal.mem_bot] at hab)
  refine ⟨⟨Q, hprime, hne⟩, ?_, (ValPl.eq_addv _ w hw h0 (fun s => Iff.rfl)).symm⟩
  exact Ideal.dvd_span_singleton.mpr hab


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem finite_zeros_poles_of_trdeg_one :
    ∀ (F Ω : Type) [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (t : Ω),
      (⊤ : IntermediateField F Ω).FG → Algebra.trdeg F Ω = 1 → Transcendental F t →
      ∀ g : Ω, g ≠ 0 → {v : AddValuation Ω (WithTop ℤ) |
        IsNormDiscrete v ∧ IsTrivOn F v ∧ 0 ≤ v t ∧ v g ≠ 0}.Finite := by
  open scoped IntermediateField.algebraAdjoinAdjoin in
  intro F Ω _ _ _ _ t hfg htr ht g hg
  have hind : AlgebraicIndependent F (fun _ : Unit => t) :=
    algebraicIndependent_unique_type_iff.mpr ht
  have hbasis : IsTranscendenceBasis F (fun _ : Unit => t) :=
    hind.isTranscendenceBasis_of_lift_trdeg_le_of_finite (by rw [htr]; simp)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin F ({t} : Set Ω)) Ω := by
    have h := hbasis.isAlgebraic_field
    rwa [Set.range_const] at h
  have : Algebra.EssFiniteType F Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType (IntermediateField.adjoin F ({t} : Set Ω)) Ω := .of_comp F _ _
  have : FiniteDimensional (IntermediateField.adjoin F ({t} : Set Ω)) Ω :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  have : IsPrincipalIdealRing (Algebra.adjoin F ({t} : Set Ω)) :=
    IsPrincipalIdealRing.of_surjective (Polynomial.algEquivOfTranscendental F t ht).toRingEquiv.toRingHom
      (Polynomial.algEquivOfTranscendental F t ht).surjective
  have : IsDedekindDomain (integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) :=
    integralClosure.isDedekindDomain _ (IntermediateField.adjoin F ({t} : Set Ω)) Ω
  have : IsFractionRing (integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) Ω :=
    integralClosure.isFractionRing_of_finite_extension (IntermediateField.adjoin F ({t} : Set Ω)) Ω
  refine (finite_normDiscrete_ne_zero_of_isDedekindDomain
    (S := integralClosure (Algebra.adjoin F ({t} : Set Ω)) Ω) g hg).subset ?_
  rintro w ⟨hw, hF, hwt, hwg⟩
  refine ⟨hw, fun b => ?_, hwg⟩
  have hA : ∀ x ∈ Algebra.adjoin F ({t} : Set Ω), x ∈ vRing w := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.mp hx]
      exact hwt
    | algebraMap r =>
      by_cases hr : r = 0
      · rw [hr, map_zero]; exact zero_mem _
      · exact (hF r hr).ge
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  have hb : IsIntegral (Algebra.adjoin F ({t} : Set Ω)) (b : Ω) := b.2
  let : Algebra (Algebra.adjoin F ({t} : Set Ω)) (vRing w) :=
    ((algebraMap (Algebra.adjoin F ({t} : Set Ω)) Ω).codRestrict (vRing w)
      (fun x => hA x x.2)).toAlgebra
  have : IsScalarTower (Algebra.adjoin F ({t} : Set Ω)) (vRing w) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hb' : IsIntegral (vRing w) (b : Ω) := hb.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hb'
  change 0 ≤ w (b : Ω)
  rw [← hy]
  exact y.2

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.MeasurableSumEmbeddingsOverGenericPoint

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory


open Polynomial in
theorem finsum_embeddings_over_eq_sum_roots {F L : Type} [Field F] [Field L] [Algebra F L]
    [Algebra.IsSeparable F L] (pb : PowerBasis F L) (τ : F →+* ℂ) {δ : ℕ} (r : Fin δ → ℂ)
    (hr : ∏ i, (X - C (r i)) = (minpoly F pb.gen).map τ) (g : (L →+* ℂ) → ℝ) (g' : ℂ → ℝ)
    (hg : ∀ P : L →+* ℂ, P.comp (algebraMap F L) = τ → g P = g' (P pb.gen)) :
    ∑ᶠ P ∈ {P : L →+* ℂ | P.comp (algebraMap F L) = τ}, g P = ∑ k, g' (r k) := by
  classical
  letI : Algebra F ℂ := τ.toAlgebra
  have hτ : algebraMap F ℂ = τ := rfl
  have hroot : ∀ k, aeval (r k) (minpoly F pb.gen) = 0 := by
    intro k
    rw [aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)
  have hsep : (∏ i, (X - C (r i))).Separable := by
    rw [hr]
    exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F pb.gen)
  have hinj : Function.Injective r := separable_prod_X_sub_C_iff.mp hsep
  let P : Fin δ → (L →+* ℂ) := fun k => (pb.lift (r k) (hroot k)).toRingHom
  have hPgen : ∀ k, P k pb.gen = r k := fun k => pb.lift_gen (r k) (hroot k)
  have hPinj : Function.Injective P := by
    intro k l h
    apply hinj
    rw [← hPgen, ← hPgen, h]
  have hPτ : ∀ k, (P k).comp (algebraMap F L) = τ := by
    intro k
    ext x
    exact (pb.lift (r k) (hroot k)).commutes x
  have hset : {P : L →+* ℂ | P.comp (algebraMap F L) = τ} = Set.range P := by
    ext Q
    constructor
    · intro hQ
      have hQ' : Q.comp (algebraMap F L) = τ := hQ
      let Q' : L →ₐ[F] ℂ := { Q with commutes' := fun x => by rw [hτ, ← hQ']; rfl }
      have h0 : aeval (Q' pb.gen) (minpoly F pb.gen) = 0 := by
        rw [aeval_algHom_apply, minpoly.aeval, map_zero]
      rw [aeval_def, eval₂_eq_eval_map, hτ, ← hr, eval_prod, Finset.prod_eq_zero_iff] at h0
      obtain ⟨k, -, hk⟩ := h0
      refine ⟨k, ?_⟩
      have hk' : Q' pb.gen = r k := by simpa [sub_eq_zero] using hk
      have : pb.lift (r k) (hroot k) = Q' := by
        apply pb.algHom_ext
        rw [pb.lift_gen, hk']
      show (pb.lift (r k) (hroot k)).toRingHom = Q
      rw [this]
    · rintro ⟨k, rfl⟩
      exact hPτ k
  rw [hset, finsum_mem_range hPinj, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hg _ (hPτ k), hPgen]

theorem measurable_sum_embeddings_over_generic_point :
    (∀ δ : ℕ, ∃ ρ : (Fin δ → ℂ) → (Fin δ → ℂ), Measurable ρ ∧ ∀ c : Fin δ → ℂ, ∏ i, (Polynomial.X - Polynomial.C (ρ c i)) = Polynomial.X ^ δ + ∑ i : Fin δ, Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) → ∀ (K : Type) [Field K] [CharZero K] (σ : Type) [Fintype σ] (L : Type) [Field L] [Algebra (FractionRing (MvPolynomial σ K)) L] [FiniteDimensional (FractionRing (MvPolynomial σ K)) L] (sg : K →+* ℂ) (m : ℕ) (b : Fin m → L) (Nf : (Fin m → ℂ) → ℝ), Measurable Nf → ∃ Φ : (σ → ℂ) → ℝ, Measurable Φ ∧ ∀ t : σ → ℂ, (∀ p : MvPolynomial σ K, p ≠ 0 → MvPolynomial.eval₂ sg t p ≠ 0) → Φ t = ∑ᶠ P ∈ {P : L →+* ℂ | ∀ p : MvPolynomial σ K, P (algebraMap (FractionRing (MvPolynomial σ K)) L (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)) = MvPolynomial.eval₂ sg t p}, Nf (fun i => P (b i)) := by
  intro hρ K _ _ σ _ L _ _ _ sg m b Nf hNf
  classical
  set R := MvPolynomial σ K with hR
  set F := FractionRing R with hF
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let pb : PowerBasis F L := Field.powerBasisOfFiniteOfSeparable F L
  obtain ⟨ρ, hρm, hρ⟩ := hρ pb.dim
  choose nu de hde hfr using fun z : F => IsFractionRing.div_surjective (A := R) z
  let ev : F → (σ → ℂ) → ℂ := fun f t =>
    MvPolynomial.eval₂ sg t (nu f) / MvPolynomial.eval₂ sg t (de f)
  have hpm : ∀ p : R, Measurable fun t : σ → ℂ => MvPolynomial.eval₂ sg t p := by
    intro p
    simp_rw [MvPolynomial.eval₂_eq_eval_map]
    exact (MvPolynomial.continuous_eval _).measurable
  have hev : ∀ f, Measurable (ev f) := fun f => (hpm _).div (hpm _)
  let cf : (σ → ℂ) → Fin pb.dim → ℂ := fun t i => ev ((minpoly F pb.gen).coeff i) t
  have hcf : Measurable cf := Measurable.of_eval fun i => hev _
  let G : (σ → ℂ) → ℂ → ℝ := fun t z =>
    Nf fun i => ∑ l : Fin pb.dim, ev (pb.basis.repr (b i) l) t * z ^ (l : ℕ)
  refine ⟨fun t => ∑ k, G t (ρ (cf t) k), ?_, ?_⟩
  · refine Finset.measurable_sum _ fun k _ => hNf.comp (Measurable.of_eval fun i => ?_)
    refine Finset.measurable_sum _ fun l _ => (hev _).mul (Measurable.pow_const ?_ _)
    exact (measurable_pi_apply k).comp (hρm.comp hcf)
  · intro t ht
    have hinj : Function.Injective (MvPolynomial.eval₂Hom sg t : R →+* ℂ) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro p hp
      by_contra h
      exact ht p h hp
    let τ : F →+* ℂ := IsFractionRing.lift hinj
    have hτa : ∀ p : R, τ (algebraMap R F p) = MvPolynomial.eval₂ sg t p := fun p =>
      IsFractionRing.lift_algebraMap hinj p
    have hτ : ∀ f, τ f = ev f t := by
      intro f
      conv_lhs => rw [← hfr f]
      rw [map_div₀, hτa, hτa]
    have hset : {P : L →+* ℂ | ∀ p : R, P (algebraMap F L (algebraMap R F p)) =
        MvPolynomial.eval₂ sg t p} = {P : L →+* ℂ | P.comp (algebraMap F L) = τ} := by
      ext P
      constructor
      · intro hP
        apply IsFractionRing.ringHom_ext (A := R)
        intro p
        rw [hτa]
        exact hP p
      · intro hP p
        have hP' : P.comp (algebraMap F L) = τ := hP
        rw [← hτa, ← hP']
        rfl
    rw [hset]
    symm
    refine finsum_embeddings_over_eq_sum_roots pb τ (ρ (cf t)) ?_ _ (G t) ?_
    · rw [hρ]
      have hmon : (minpoly F pb.gen).Monic := minpoly.monic pb.isIntegral_gen
      conv_rhs => rw [hmon.as_sum, pb.natDegree_minpoly]

      rw [Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
      Finset.sum_range]
      simp [cf, hτ]
    · intro P hP
      show Nf _ = Nf _
      congr 1
      funext i
      conv_lhs => rw [← pb.basis.sum_repr (b i)]

      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Algebra.smul_def, map_mul, pb.basis_eq_pow, map_pow, ← hτ, ← hP]
      rfl

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAndDensityAndAemeasurable

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem finite_support_and_density_and_aemeasurable :
    (∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, 1 ≤ d.D → (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → (∀ G, Module.finrank (Ω c) (𝒜 c G) = 1) → (∀ j, d.w j c ∈ 𝒜 c d.wL) → d.w (d.jc c) c ≠ 0 → ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c → (∀ g : Ω c, g ≠ 0 → {v | d.admitted c v ∧ v g ≠ 0}.Finite) ∧ ∀ (G : WT) (e : A c) (S : Finset (Ω c)), e ∈ 𝒜 c G → e ≠ 0 → (∀ v, d.admitted c v → ∀ a : Ω c, a ≠ 0 → ((d.ord c v G (a • e) : ℤ) : WithTop ℤ) = v a + (d.ord c v G e : WithTop ℤ)) → (∀ v, d.admitted c v → (∀ s ∈ S, 0 ≤ v s) → d.ord c v G e = 0) → ∀ f ∈ 𝒜 c G, f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite) ∧ (∀ (K A Ω : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra K Ω] [IsScalarTower K A Ω] (sg : K →+* ℂ) (φ : A →+* ℂ), φ.comp (algebraMap K A) = sg → ∀ (S : Finset A) (ε : ℝ), 0 < ε → ∃ P ∈ PT (Ω := Ω) sg, ∀ a ∈ S, ‖P (algebraMap A Ω a) - φ a‖ < ε) ∧ (∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 → (∃ J : Fin d.D → Fin d.N, LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) → ∀ (sg : K →+* ℂ) (m : ℕ) (a : Fin m → Ω c) (Nf : (Fin m → ℂ) → ℝ) (h : (Ω c →+* ℂ) → ℝ), Measurable Nf → (∀ P ∈ PT (Ω := Ω c) sg, h P = Nf (fun i => P (a i))) → AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 => ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j), h P) d.sphMeasure) :=
  ⟨finite_support_admissible finite_vertical_gauss_valuations finite_zeros_poles_of_trdeg_one,
    generic_points_dense exists_algIndep_tuple_near,
    aemeasurable_finsum_section ae_eval₂_ne_zero_pi_toSphere
      (measurable_sum_embeddings_over_generic_point exists_measurable_roots_enumeration)
      existsUnique_ringHom_OmS⟩

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.DivFinOfTrdeg

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

private theorem fg_lemma {F K : Type} [Field F] [Field K] [Algebra F K] (σ : Type) [Finite σ]
    (h : (⊤ : IntermediateField F K).FG) :
    (⊤ : IntermediateField F (FractionRing (MvPolynomial σ K))).FG := by
  rw [IntermediateField.fg_top_iff] at h ⊢
  haveI : Algebra.EssFiniteType K (FractionRing (MvPolynomial σ K)) :=
    Algebra.EssFiniteType.comp K (MvPolynomial σ K) _
  exact Algebra.EssFiniteType.comp F K _

private theorem trdeg_fractionRing_mvPolynomial {F K : Type} [Field F] [Field K] [Algebra F K] (σ : Type) [Finite σ] (n : ℕ)
    (h : Algebra.trdeg F K = n) :
    Algebra.trdeg F (FractionRing (MvPolynomial σ K)) = (n + Nat.card σ : ℕ) := by
  have h1 : Algebra.trdeg (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) = 0 :=
    trdeg_eq_zero_iff.2 (IsLocalization.isAlgebraic _ (nonZeroDivisors _))
  have h2 := trdeg_add_eq (A := FractionRing (MvPolynomial σ K)) K (MvPolynomial σ K)
  rw [h1, add_zero, MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id] at h2
  have h3 := trdeg_add_eq (A := FractionRing (MvPolynomial σ K)) F K
  rw [← h3, h, ← h2, Nat.cast_add, Nat.cast_card]

theorem divFin_of_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z)), 1 ≤ d.D → d.D = Dw.dim + Nat.card (FlagVar Dw) → (∀ Z j, d.w j Z ∈ AG Z d.wL) → (∀ Z, d.w (d.jc Z) Z ≠ 0) → (∀ Z, ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d Z) → DivFin d := by
  intro E _ _ _ H Dw l Xo c _ d hD hdim hw hjc htr Z r hr
  obtain ⟨hfg, htd⟩ := kap_fg_trdeg E H Dw l Xo c
  have hFG : (⊤ : IntermediateField c.F (Om Z)).FG := fg_lemma (FlagVar Dw) (hfg Z)
  have hT : Algebra.trdeg c.F (Om Z) = d.D := by
    rw [hdim]; exact trdeg_fractionRing_mvPolynomial (FlagVar Dw) Dw.dim (htd Z)
  have hrk : ∀ G, Module.finrank (Om Z) (AG Z G) = 1 := fun G =>
    finrank_span_singleton (AddMonoidAlgebra.single_ne_zero.mpr one_ne_zero)
  exact (GlobalTheory.finite_support_and_density_and_aemeasurable.1 c.F (Comp Xo c) (fun Z => Om Z) (WTZ E)
    (fun Z => AC Z) (fun Z G => AG Z G) d Z hD hFG hT hrk (hw Z) (hjc Z) (htr Z)).1 r hr

end GlobalTheory.Reg
end
end
