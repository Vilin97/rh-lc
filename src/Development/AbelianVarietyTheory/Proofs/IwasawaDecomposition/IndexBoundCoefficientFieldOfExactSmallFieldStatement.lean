module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldTies
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CmQuadraticFormEqAlternatingForm
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CmCurveTorsionDefinedOverOfWeberValues
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
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.NormComparisonConstants
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassNumberDvdHstar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RayFieldTheta
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.CompleteSplittingCompositumDegreeOnePrimeStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldComp
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ContainsRayFieldOfRay
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHost
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.PrincipalRayPrimesSplitCompletelyWeberValuesStatement
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFi
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesHasRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesRingOfIntegersFull
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
public import Formalism.LocalToGlobal.ProjectiveLattices.RecCond
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFOAssembledIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfOrderDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFieldDegreeRootDiscrBoundedByRingPolynomialStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootOneMemOfIsRayFieldIn

-- Source module: Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField

section

@[expose] public section

noncomputable section

namespace GlobalTheory.FieldSize

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2
open scoped IntermediateField

theorem curveOver_of_weberSet (D : D7) (F : IntermediateField ℚ ℂ) {n : ℕ} (hn : 0 < n)
    (h0 : D.host.φ₀ D.host.sqrtMinusD ∈ F)
    (h : ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔
      ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + D.host.φ₀ D.host.sqrtMinusD) / 2)) → weberSet L n ⊆ F) :
    GlobalTheory.CompRat.CurveOver (hostOfRecord D) F n :=
  (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn _ (hostOfRecord D) F n hn).1 h0 fun L hL =>
    ⟨h L hL (Set.mem_insert _ _), fun s hs =>
      h L hL (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩


end GlobalTheory.FieldSize
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContainsRayFieldSub

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberRay

theorem containsRayField_sub (P : Pre) (δ : FieldDat P) (K : IntermediateField ℚ ℂ) [NumberField K]
    (hKE : K ≤ P.host.φ₀.toRatAlgHom.fieldRange) (hKR : K ≤ δ.ray) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion hKR).toRingHom (modulus P) := by
  obtain ⟨hm, hNF, hray⟩ := δ.isRay
  letI := algOf P.host.φ₀ δ.ray hm
  obtain ⟨hab, hun, -, hart⟩ := hray
  haveI : IsGalois P.host.E δ.ray := hab.toIsGalois
  have hC : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (algebraMap P.host.E δ.ray) (modulus P) :=
    GlobalTheory.FieldSize.RayNorm.containsRayField_of_ray (modulus P) hun (fun I hI hc => (hart I hI hc).1)
  let e : P.host.E ≃ₐ[ℚ] P.host.φ₀.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField P.host.φ₀.toRatAlgHom
  let φKE : K →+* P.host.E :=
    ((e.symm : P.host.φ₀.toRatAlgHom.fieldRange ≃+* P.host.E) : P.host.φ₀.toRatAlgHom.fieldRange →+* P.host.E).comp
      (IntermediateField.inclusion hKE).toRingHom
  have hcomp : (algebraMap P.host.E δ.ray).comp φKE = (IntermediateField.inclusion hKR).toRingHom := by
    refine RingHom.ext fun x => Subtype.ext ?_
    have := congrArg Subtype.val (e.apply_symm_apply (IntermediateField.inclusion hKE x))
    exact this
  rw [← hcomp]
  exact GlobalTheory.RayDescent.containsRayField_comp K P.host.E δ.ray φKE _ _ hC

theorem weberSet_subset_ray : ∀ (P : Pre) (δ : FieldDat P) (L : PeriodPair), (∀ z, z ∈ L.lattice ↔ ∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + P.host.φ₀ P.host.sqrtMinusD) / 2)) → ∀ n : ℕ, Odd n → 3 ≤ n → n ∣ modulus P → weberSet L n ⊆ δ.ray := by
  intro P δ L hL n _ hn hdvd
  obtain ⟨K, hKN, hKT, h2, -, hd, hKE, hlat, -⟩ := GlobalTheory.FieldSize.exists_hostK P.R P.host
  have hP : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z := fun z => (hL z).trans (hlat z)
  have hKR : K ≤ δ.ray := fun z hz => by
    obtain ⟨x, rfl⟩ := hKE hz
    exact δ.isRay.emb_mem x
  have hCK := containsRayField_sub P δ K hKE hKR
  obtain ⟨inst, S, hS⟩ := GlobalTheory.T.principalRayPrimes_splitCompletely_weberValues K h2 hd L hP n hn
  haveI := GlobalTheory.FieldSize.WeberIn.numberField_adjoin K δ.ray (weberSet L n)
  have hm0 : ((modulus P : ℕ) : 𝓞 δ.ray) ≠ 0 := by
    exact_mod_cast modulus_ne_zero P
  haveI : NumberField (⊥ : IntermediateField δ.ray ℂ) := NumberField.of_module_finite δ.ray _
  have hle : IntermediateField.adjoin δ.ray (weberSet L n) ≤ ⊥ := by
    refine GlobalTheory.Bauer.le_of_finite_split_not_split δ.ray ℂ ⊥ (IntermediateField.adjoin δ.ray (weberSet L n)) ?_
    refine ((WeberIn.finite_mem hm0).union (WeberIn.finite_norm_mem S)).subset ?_
    rintro 𝔓 ⟨hp, -, hnot⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hc
    obtain ⟨f, α, hN, hα, h1⟩ := hCK 𝔓 hc.1
    have h1' : (n : 𝓞 K) ∣ α - 1 := (Nat.cast_dvd_cast hdvd).trans h1
    have hf : f = 1 := by
      have hp' := hp
      rw [hN] at hp'
      exact hp'.eq_one_of_pow
    subst hf
    rw [pow_one] at hN hα
    have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom) ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.absNorm_bot] at hN
      exact hp.ne_zero hN
    haveI := 𝔓.isPrime
    let 𝔭 : HeightOneSpectrum (𝓞 K) :=
      ⟨𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion hKR).toRingHom),
        Ideal.comap_isPrime _ _, hne⟩
    apply hnot
    refine GlobalTheory.T.completeSplitting_compositum_degreeOnePrime K δ.ray hKR (weberSet L n) 𝔭 𝔓 rfl hN ?_
    have h𝔭 : 𝔭.asIdeal = Ideal.span {α} := hα
    rw [h𝔭]
    exact hS α _ hp hc.2 (by rw [← hα, ← hN]) (Ideal.mem_span_singleton.2 h1')
  intro x hx
  have hx' := hle (IntermediateField.subset_adjoin δ.ray _ hx)
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx'
  exact y.2

end GlobalTheory.FieldSize.WeberRay
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianCodeWordStagesTypeNormsPrincipal

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.TypeNormPin

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.L2.Pj

section Push

variable {K F : Type} [Field K] [Field F] (φ : K →+* F)

theorem span_image_span (S : Set K) :
    Submodule.span (𝓞 F) (φ '' (Submodule.span (𝓞 K) S : Set K)) = Submodule.span (𝓞 F) (φ '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul b x _ hx =>
    have : φ (b • x) = RingOfIntegers.mapRingHom φ b • φ x := by
      change φ ((b : K) * x) = _
      rw [map_mul]; rfl
    rw [this]; exact Submodule.smul_mem _ _ hx

def extend : Submodule (𝓞 K) K →* Submodule (𝓞 F) F where
  toFun M := Submodule.span (𝓞 F) (φ '' M)
  map_one' := by rw [Submodule.one_eq_span, span_image_span, Set.image_singleton, map_one, Submodule.one_eq_span]
  map_mul' M N := by
    rw [Submodule.mul_eq_span_mul_set, span_image_span, Set.image_mul, Submodule.span_mul_span]

theorem extend_span (S : Set K) : extend φ (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 F) (φ '' S) :=
  span_image_span φ S

end Push

section Host

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem emb_sqrt_iff (g : R.GG) :
    H.emb g H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) ↔ g ∈ R.Psi :=
  (factEmb R H).2 g

theorem cmHostBaseEmbedding_sqrtMinusD : H.φ₀ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem conj_ne : starRingEnd ℂ (Complex.I * (Real.sqrt H.d : ℂ)) ≠ Complex.I * (Real.sqrt H.d : ℂ) := by
  intro h
  have h1 := congrArg Complex.im h
  have : 0 < Real.sqrt H.d := Real.sqrt_pos.2 (by exact_mod_cast H.hyp.2.1.pos)
  simp at h1
  linarith

theorem emb_sqrt_cases (σ : H.E →+* ℂ) : σ H.sqrtMinusD = Complex.I * (Real.sqrt H.d : ℂ) ∨
    starRingEnd ℂ (σ H.sqrtMinusD) = Complex.I * (Real.sqrt H.d : ℂ) := by
  have h0 : (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have h : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
    apply H.φ₀.injective
    rw [map_pow, cmHostBaseEmbedding_sqrtMinusD, h0]
    simp
  have h1 : σ H.sqrtMinusD ^ 2 = (Complex.I * (Real.sqrt H.d : ℂ)) ^ 2 := by
    rw [← map_pow, h, h0]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact Or.inl h2
  · right; rw [h2]; simp

def embSum : Tau R ⊕ Tau R → (H.E →+* ℂ) :=
  Sum.elim (fun g => H.emb g) (fun g => (starRingEnd ℂ).comp (H.emb g))

theorem embSum_bij : Function.Bijective (embSum H) := by
  refine ⟨?_, fun σ => ?_⟩
  · have hne : ∀ a b : Tau R, H.emb a ≠ (starRingEnd ℂ).comp (H.emb b) := fun a b h => by
      have h1 := DFunLike.congr_fun h H.sqrtMinusD
      rw [RingHom.comp_apply, (emb_sqrt_iff H _).2 a.2, (emb_sqrt_iff H _).2 b.2] at h1
      exact conj_ne H h1.symm
    rintro (a | a) (b | b) hab
    · exact congrArg _ (Subtype.ext ((factEmb R H).1.1 hab))
    · exact absurd hab (hne a b)
    · exact absurd hab.symm (hne b a)
    · refine congrArg _ (Subtype.ext ((factEmb R H).1.1 (RingHom.ext fun x => ?_)))
      exact (starRingEnd ℂ).injective (DFunLike.congr_fun hab x)
  · rcases emb_sqrt_cases H σ with h | h
    · obtain ⟨g, rfl⟩ := (factEmb R H).1.2 σ
      exact ⟨Sum.inl ⟨g, (emb_sqrt_iff H g).1 h⟩, rfl⟩
    · obtain ⟨g, hg⟩ := (factEmb R H).1.2 ((starRingEnd ℂ).comp σ)
      refine ⟨Sum.inr ⟨g, (emb_sqrt_iff H g).1 (by rw [hg]; exact h)⟩, RingHom.ext fun x => ?_⟩
      change starRingEnd ℂ (H.emb g x) = _
      rw [hg]; simp

theorem emb_conj (g : R.GG) (x : H.E) : H.emb g (H.conj x) = starRingEnd ℂ (H.emb g x) :=
  H.conjE_apply _ x

end Host

theorem exists_hom (X : Stages) (Q : Par X.toD7) (h : Q.PinField) :
    ∃ φ : X.B.Ks →+* Q.c.F, ∀ x : X.B.Ks, ((φ x : Q.c.F) : ℂ) = X.B.embLL x := by
  let e : 𝓞 Q.c.F ≃+* 𝓞 X.B.Ks := Q.eO
  have he : ∀ y : 𝓞 Q.c.F, X.B.embLL ((e y : X.B.Ks) : X.B.LL) = ((y : Q.c.F) : ℂ) := h
  let φ : X.B.Ks ≃+* Q.c.F := IsFractionRing.ringEquivOfRingEquiv e.symm
  have hφ : ∀ y : 𝓞 X.B.Ks, ((φ (algebraMap _ X.B.Ks y) : Q.c.F) : ℂ) =
      X.B.embLL ((algebraMap _ X.B.Ks y : X.B.Ks) : X.B.LL) := fun y => by
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  refine ⟨φ.toRingHom, fun x => ?_⟩
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 X.B.Ks) x
  change ((φ (_ / _) : Q.c.F) : ℂ) = _
  rw [map_div₀, IntermediateField.coe_div, hφ, hφ, IntermediateField.coe_div, map_div₀]

theorem kPsiIn_of_hom (B : Base) [IsCMField B.host.E] {Hh : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host B.host.E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level Hh} (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum Hh)
    {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ B.R.m) (hp : Dw.p = (B.R.sigW j).1) (hq : Dw.q = (B.R.sigW j).2)
    (h1 : (Hh.rt : B.host.E) = B.host.sqrtMinusD) (h2 : Hh.rt0 = B.host.φ₀ B.host.sqrtMinusD)
    (φ : B.Ks →+* c.F) (hφ : ∀ x : B.Ks, ((φ x : c.F) : ℂ) = B.embLL x) : KPsiIn (Dw := Dw) c := by
  intro 𝔞 h𝔞
  obtain ⟨β, hβ0, hβ, habs⟩ := B.kPsi j hj1 hj2 𝔞 h𝔞
  have hE : ∀ y, B.embLL (B.embE y) = B.host.φ₀ y := fun y => RingHom.congr_fun B.embE_φ₀ y
  have himg : ∀ (τ : B.host.E →+* ℂ) (f : B.host.E → B.host.E), (∀ a, B.host.φ₀ (f a) = τ a) →
      φ '' {x : B.Ks | ∃ a ∈ 𝔞, (x : B.LL) = B.embE (f (a : B.host.E))} =
        (embK c τ) '' (𝔞 : Set (𝓞 B.host.E)) := by
    intro τ f hf
    ext z
    constructor
    · rintro ⟨x, ⟨a, ha, hx⟩, rfl⟩
      refine ⟨a, ha, Subtype.ext ?_⟩
      rw [embK_coe, hφ, hx, hE, hf]
    · rintro ⟨a, ha, rfl⟩
      refine ⟨⟨_, B.E_le_Ks (f a)⟩, ⟨a, ha, rfl⟩, Subtype.ext ?_⟩
      rw [embK_coe, hφ, hE, hf]
  refine ⟨φ β, (map_ne_zero φ).2 hβ0, ?_, fun σ => ?_⟩
  · have := congrArg (extend φ) hβ
    rw [extend_span, Set.image_singleton, map_prod] at this
    rw [this, ← (embSum_bij B.host).prod_comp fun τ =>
      Submodule.span (𝓞 c.F) ((embK c τ) '' (𝔞 : Set (𝓞 B.host.E))) ^ Dw.mult τ,
      Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ => ?_
    have hs : B.host.emb g B.host.sqrtMinusD = Complex.I * (Real.sqrt B.host.d : ℂ) :=
      (emb_sqrt_iff B.host _).2 g.2
    have h0 : Hh.rt0 = Complex.I * (Real.sqrt B.host.d : ℂ) := h2.trans (cmHostBaseEmbedding_sqrtMinusD B.host)
    have m1 : Dw.mult (embSum B.host (Sum.inl g)) = (B.R.sigW j).1 := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_pos (by rw [h1, h0]; exact hs)]
      exact hp
    have m2 : Dw.mult (embSum B.host (Sum.inr g)) = (B.R.sigW j).2 := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum.mult, if_neg]
      · exact hq
      · rw [h1, h0]
        change ¬ starRingEnd ℂ (B.host.emb g B.host.sqrtMinusD) = _
        rw [hs]
        exact conj_ne B.host
    rw [map_mul, map_pow, map_pow, extend_span, extend_span, m1, m2,
      himg (embSum B.host (Sum.inl g)) (B.host.sigmaOf g) (fun _ => rfl),
      himg (embSum B.host (Sum.inr g)) (fun a => B.host.sigmaOf g (B.host.conj a))
        (fun a => emb_conj B.host g a)]
  · rw [hp, hq]
    exact habs (σ.comp φ)

theorem hermitianCodeWordStages_typeNorms_principal : ∀ X : Stages, OKPsi X.toD7 := by
  intro X Q hQ j hj
  obtain ⟨φ, hφ⟩ := exists_hom X Q hQ.2.2.1
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  obtain ⟨-, h1, h2, -⟩ := hQ.1
  exact @kPsiIn_of_hom X.B (instCMHost X.toD7) Q.H Q.l Q.c (Q.Dw j) j hj.1 hj.2 hp hq h1 h2 φ hφ

end GlobalTheory.Mem.TypeNormPin

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallField

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AtMember

open GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize

theorem odd_of_mem_levelPrimes (P : Pre) {p : ℕ} (hp : p ∈ P.host.levelPrimes) : Odd p := by
  have h := (P.level_cond p hp).2
  have h2 : (2 : ℕ) ∣ P.host.QS * P.host.q * P.host.d := ((((dvd_pow_self 2 (Nat.succ_ne_zero _)).trans P.host.tower_dvd).mul_right _).mul_right _)
  rw [Nat.odd_iff, ← Nat.mod_mod_of_dvd p h2, h]



theorem fieldTies_of_ksExact : GlobalTheory.NT.RayField → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : Fld.FieldDat X.B.toPre),
    X.B.KsExact δ f → FieldTies X.toD7 (Fr.at X f) := by
  intro hR X f δ hx
  have := GlobalTheory.Mem.FieldsEx.host_cplx X.B.toPre
  have hFO : FO X.toD7 = X.B.KsC := SetLike.ext fun z => (mem_FO_assembled_iff X z).trans (X.B.mem_KsC).symm
  have hxe : X.B.KsC = Fld.listField δ f := hx
  obtain ⟨hray, -, hchar, -⟩ := Base.KsExact.lower hx
  have key : ∀ p, (p = X.B.host.pde ∨ p = X.B.host.pde') → FieldOK0 X.toD7 p := by
    intro p hp
    have hpl : p ∈ X.B.host.levelPrimes := by
      rcases hp with rfl | rfl
      exacts [X.B.host.pde_level.1, X.B.host.pde_level.2]
    have hpp : p.Prime := (X.B.toPre.level_cond p hpl).1
    have hdvd : X.B.host.g 0 * X.B.host.g 1 * p ∣ Fld.modulus X.B.toPre := by
      rcases hp with rfl | rfl
      · exact dvd_mul_right _ _
      · exact ⟨X.B.host.pde, by unfold Fld.modulus; ring⟩
    have hpd : p ∣ Fld.modulus X.B.toPre := (dvd_mul_left p _).trans hdvd
    refine ⟨hp, hermitianCodeWordStages_ringOfIntegers_full _, hermitianCodeWordStages_has_rootOfUnity _, ?_, ?_, TypeNormPin.hermitianCodeWordStages_typeNorms_principal _,
      fun h => Nat.not_prime_zero (X.B.toPre.level_cond 0 h).1, ?_⟩
    · rw [hFO]
      exact hray (GlobalTheory.Mem.RayRoots.rootOne_mem_of_isRayFieldIn X.B.host.E X.B.host.φ₀ (Fld.modulus X.B.toPre) p δ.ray (Fld.modulus_ne_zero _) hpd δ.isRay)
    · have hn0 : 0 < X.B.host.g 0 * X.B.host.g 1 * p :=
        Nat.mul_pos (Nat.mul_pos (X.B.host.g_prime 0).pos (X.B.host.g_prime 1).pos) hpp.pos
      refine GlobalTheory.FieldSize.curveOver_of_weberSet X.toD7 _ hn0 ?_ fun L hL => ?_
      · rw [hFO]
        exact X.B.imField_le_KsC ⟨_, rfl⟩
      · have hodd : Odd (X.B.host.g 0 * X.B.host.g 1 * p) :=
          ((odd_of_mem_levelPrimes X.B.toPre (X.B.host.g_level 0)).mul
            (odd_of_mem_levelPrimes X.B.toPre (X.B.host.g_level 1))).mul (odd_of_mem_levelPrimes X.B.toPre hpl)
        have h3 : 3 ≤ X.B.host.g 0 * X.B.host.g 1 * p := by
          have a := (X.B.host.g_prime 0).two_le
          have b := (X.B.host.g_prime 1).two_le
          have c := hpp.two_le
          have := Nat.mul_le_mul (Nat.mul_le_mul a b) c
          omega
        rw [hFO]
        exact (GlobalTheory.FieldSize.WeberRay.weberSet_subset_ray X.B.toPre δ L hL _ hodd h3 hdvd).trans fun z hz => hray hz
    · rcases hp with rfl | rfl
      exacts [X.B.toPre.level_split _ X.B.host.pde_level.1, X.B.toPre.level_split _ X.B.host.pde_level.2]
  refine ⟨key _ (Or.inl rfl), key _ (Or.inr rfl), fun x => ?_, fun x => ?_, fun L hL => ?_⟩
  · rw [hFO]
    exact GlobalTheory.Mem.ValFin.mem_of_orderDvd X.B.host.E f.del X.B.KsC f.isDel.fin
      ((le_sup_right.trans (le_sup_left.trans le_sup_left)).trans hchar) x
  · rw [hFO]
    exact GlobalTheory.Mem.ValFin.mem_of_orderDvd X.B.host.E f.del' X.B.KsC f.isDel'.fin ((le_sup_right.trans le_sup_left).trans hchar) x
  · have hle : FO X.toD7 ≤ δ.Om := by
      rw [hFO, hxe]
      exact GlobalTheory.Mem.FieldsEx.listField_le_Om δ f
    exact GlobalTheory.FieldSize.sz_mono_and_of_le.2 _ _ _ _ hle (GlobalTheory.T.omegaField_degree_rootDiscr_bounded_by_ringPolynomial hR X.B.toPre δ L hL)

end GlobalTheory.AtMember

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IndexBoundCoefficientFieldOfExactSmallFieldStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Theta GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.AtMember
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.fieldTies_of_rayField_of_ksExact : GlobalTheory.NT.RayField → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : Fld.FieldDat X.B.toPre), X.B.KsExact δ f → FieldTies X.toD7 (Fr.at X f) := by
  first | exact @GlobalTheory.AtMember.fieldTies_of_ksExact | exact GlobalTheory.AtMember.fieldTies_of_ksExact | (intros; apply GlobalTheory.AtMember.fieldTies_of_ksExact <;> assumption)
end
end
