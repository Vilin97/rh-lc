module

public import Formalism.LocalToGlobal.ProjectiveLattices.NrmContPf
public import Formalism.LocalToGlobal.ProjectiveLattices.DivFinOfLawA3
public import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.DivFinOfTrdeg
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Topology.Separation.CompletelyRegular
public import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.AlgebraicIndependentFreeVar
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.Implicit
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AeEvalCircleMapNeZero
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AemeasurableFinsumSection
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsLinearIndependentDIffTrdegAdjoinEq
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IntegralAndRationalOfPolynomialGrowth
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.UniformSpace.Uniformizable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CastAddNeNatAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsLinearIndependentDIffTrdegAdjoinEq
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.ContDiffEvalFun

section

@[expose] public section

open Filter Topology

namespace GlobalTheory.SmoothPolynomialEvaluation

noncomputable def evalFun {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (v : (Fin d → ℂ) × ℂ) : ℂ :=
  Polynomial.eval v.2 (Polynomial.map (MvPolynomial.eval v.1) p)

lemma contDiff_mvEval {d : ℕ} (q : MvPolynomial (Fin d) ℂ) :
    ContDiff ℂ 1 (fun v : (Fin d → ℂ) × ℂ => MvPolynomial.eval v.1 q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    have hX : ContDiff ℂ 1 (fun v : (Fin d → ℂ) × ℂ => v.1 i) := (contDiff_apply ℂ (fun _ => ℂ) i).comp contDiff_fst
    simpa using hp.mul hX

lemma contDiff_evalFun {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) :
    ContDiff ℂ 1 (evalFun p) := by
  have h : evalFun p = fun v => ∑ i ∈ Finset.range (p.natDegree + 1),
      MvPolynomial.eval v.1 (p.coeff i) * v.2 ^ i := by
    funext v
    unfold evalFun
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le Polynomial.natDegree_map_le)]
    simp [Polynomial.coeff_map]
  rw [h]
  apply ContDiff.sum
  intro i _
  exact (contDiff_mvEval _).mul (contDiff_snd.pow i)

theorem main : ∀ {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x₀ : Fin d → ℂ) (a : ℂ),
    Polynomial.eval a (Polynomial.map (MvPolynomial.eval x₀) p) = (0 : ℂ) →
    Polynomial.eval a ((Polynomial.derivative : Polynomial ℂ → Polynomial ℂ)
      (Polynomial.map (MvPolynomial.eval x₀) p)) ≠ (0 : ℂ) →
    ∃ (y : (Fin d → ℂ) → ℂ), y x₀ = a ∧ (∃ s ∈ nhds x₀, ContinuousOn y s) ∧
      ∀ᶠ (x : Fin d → ℂ) in nhds x₀,
        Polynomial.eval (y x) (Polynomial.map (MvPolynomial.eval x) p) = (0 : ℂ) := by
  intro d p x₀ a h0 h1
  set q := Polynomial.map (MvPolynomial.eval x₀) p with hq
  have hFs : HasStrictFDerivAt (evalFun p) (fderiv ℂ (evalFun p) (x₀, a)) (x₀, a) :=
    (contDiff_evalFun p).contDiffAt.hasStrictFDerivAt_fderiv one_ne_zero
  have hder : fderiv ℂ (evalFun p) (x₀, a) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ
      = (1 : ℂ →L[ℂ] ℂ).smulRight (Polynomial.eval a (Polynomial.derivative q)) := by
    have h1' : HasFDerivAt (fun z => evalFun p (x₀, z))
        (fderiv ℂ (evalFun p) (x₀, a) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) a :=
      hFs.hasFDerivAt.comp a (hasFDerivAt_prodMk_right x₀ a)
    have h2' : HasFDerivAt (fun z => evalFun p (x₀, z))
        ((1 : ℂ →L[ℂ] ℂ).smulRight (Polynomial.eval a (Polynomial.derivative q))) a :=
      (Polynomial.hasDerivAt q a).hasFDerivAt
    exact h1'.unique h2'
  have hinv : (fderiv ℂ (evalFun p) (x₀, a) ∘L
      ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hder]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext; simp
  let φ := hFs.implicitFunctionDataOfProdDomain hinv
  refine ⟨fun x => (φ.toOpenPartialHomeomorph.symm (evalFun p (x₀, a), x)).2, ?_, ?_, ?_⟩
  · have := (hFs.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds
    simpa only [HasStrictFDerivAt.implicitFunctionOfProdDomain_def,
      ImplicitFunctionData.implicitFunction_apply] using this.mp rfl
  · refine ⟨{x | (evalFun p (x₀, a), x) ∈ φ.toOpenPartialHomeomorph.target}, ?_, ?_⟩
    · apply IsOpen.mem_nhds
      · exact φ.toOpenPartialHomeomorph.open_target.preimage (by fun_prop)
      · simpa only [Set.mem_setOf_eq, φ, HasStrictFDerivAt.pt_implicitFunctionDataOfProdDomain,
          HasStrictFDerivAt.leftFun_implicitFunctionDataOfProdDomain,
          HasStrictFDerivAt.rightFun_implicitFunctionDataOfProdDomain, Prod.fst] using
          φ.map_pt_mem_toOpenPartialHomeomorph_target
    · exact continuous_snd.comp_continuousOn
        (φ.toOpenPartialHomeomorph.continuousOn_symm.comp (by fun_prop) (fun x hx => hx))
  · have := hFs.eventually_apply_implicitFunctionOfProdDomain hinv
    filter_upwards [this] with x hx
    simpa only [HasStrictFDerivAt.implicitFunctionOfProdDomain_def,
      ImplicitFunctionData.implicitFunction_apply, evalFun] using hx.trans h0

end GlobalTheory.SmoothPolynomialEvaluation
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsContinuousOnEmbeddings

section

@[expose] public section

namespace GlobalTheory

namespace SectionLocal

open Filter Topology

theorem exists_continuousOn_root {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ))
    (x₀ : Fin d → ℂ) (a : ℂ) (ha : (p.map (MvPolynomial.eval x₀)).eval a = 0)
    (ha' : (p.map (MvPolynomial.eval x₀)).derivative.eval a ≠ 0) :
    ∃ y : (Fin d → ℂ) → ℂ, y x₀ = a ∧ (∃ s ∈ 𝓝 x₀, ContinuousOn y s) ∧
      ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (y x) = 0 :=
  _root_.GlobalTheory.SmoothPolynomialEvaluation.main p x₀ a ha ha'

theorem exists_continuousOn_roots {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (hp : p.Monic)
    (x₀ : Fin d → ℂ) (hs : (p.map (MvPolynomial.eval x₀)).Separable) :
    ∃ (y : Fin p.natDegree → (Fin d → ℂ) → ℂ) (V : Set (Fin d → ℂ)), V ∈ 𝓝 x₀ ∧
      (∀ i, ContinuousOn (y i) V) ∧
      ∀ x ∈ V, Function.Injective (fun i => y i x) ∧
        ∀ z, (p.map (MvPolynomial.eval x)).eval z = 0 ↔ ∃ i, y i x = z := by
  classical
  have hc := FiniteCoverGrowth.card_roots (hp.map (MvPolynomial.eval x₀)) hs
  rw [hp.natDegree_map] at hc
  let e := (Finset.equivFinOfCardEq hc).symm
  have hroot : ∀ i, (p.map (MvPolynomial.eval x₀)).eval (e i : ℂ) = 0 := fun i =>
    Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.1 (e i).2)
  choose y hy0 hyd hyr using fun i => exists_continuousOn_root p x₀ (e i) (hroot i)
    (by simpa using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := (e i : ℂ)) (by simpa using hroot i))
  choose s hs hyd using hyd
  have hne : ∀ᶠ x in 𝓝 x₀, ∀ i j, i ≠ j → y i x ≠ y j x := by
    simp only [eventually_all]
    intro i j hij
    refine (((hyd i).continuousAt (hs i)).ne_iff_eventually_ne ((hyd j).continuousAt (hs j))).1 ?_
    rw [hy0, hy0]
    exact fun h => hij (e.injective (Subtype.ext h))
  have hall := (hne.and (eventually_all.2 hyr)).and (eventually_all.2 hs)
  refine ⟨y, _, hall, fun i => (hyd i).mono fun x hx => hx.2 i, ?_⟩
  rintro x ⟨⟨h1, h2⟩, -⟩
  have hinj : Function.Injective (fun i => y i x) := fun i j h => by
    by_contra hij; exact h1 i j hij h
  have hset : (p.map (MvPolynomial.eval x)).roots.toFinset =
      Finset.univ.image (fun i => y i x) := by
    refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro a ha
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 ha
      exact Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hp.map _).ne_zero).2 (h2 i))
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
      refine (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans ?_)
      rw [hp.natDegree_map]
  refine ⟨hinj, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · have : z ∈ (p.map (MvPolynomial.eval x)).roots.toFinset :=
      Multiset.mem_toFinset.2 ((Polynomial.mem_roots (hp.map _).ne_zero).2 hz)
    rw [hset] at this
    simpa using this
  · rintro ⟨i, rfl⟩
    exact h2 i


open Polynomial in
theorem exists_embeddings_of_roots {F L : Type} [Field F] [Field L] [Algebra F L]
    (pb : PowerBasis F L) (τ : F →+* ℂ) {n : ℕ} (r : Fin n → ℂ)
    (hr : ∀ z, ((minpoly F pb.gen).map τ).eval z = 0 ↔ ∃ i, r i = z) :
    ∃ P : Fin n → (L →+* ℂ), (∀ k, P k pb.gen = r k) ∧
      Set.range P = {P : L →+* ℂ | P.comp (algebraMap F L) = τ} := by
  letI : Algebra F ℂ := τ.toAlgebra
  have hτ : algebraMap F ℂ = τ := rfl
  have hroot : ∀ k, aeval (r k) (minpoly F pb.gen) = 0 := by
    intro k
    rw [aeval_def, eval₂_eq_eval_map, hτ]
    exact (hr _).2 ⟨k, rfl⟩
  refine ⟨fun k => (pb.lift (r k) (hroot k)).toRingHom, fun k => pb.lift_gen (r k) (hroot k), ?_⟩
  ext Q
  constructor
  · rintro ⟨k, rfl⟩
    ext x
    exact (pb.lift (r k) (hroot k)).commutes x
  · intro hQ
    have hQ' : Q.comp (algebraMap F L) = τ := hQ
    let Q' : L →ₐ[F] ℂ := { Q with commutes' := fun x => by rw [hτ, ← hQ']; rfl }
    have h0 : aeval (Q' pb.gen) (minpoly F pb.gen) = 0 := by
      rw [aeval_algHom_apply, minpoly.aeval, map_zero]
    rw [aeval_def, eval₂_eq_eval_map, hτ] at h0
    obtain ⟨k, hk⟩ := (hr _).1 h0
    refine ⟨k, ?_⟩
    have : pb.lift (r k) (hroot k) = Q' := by
      apply pb.algHom_ext
      rw [pb.lift_gen, hk]
    show (pb.lift (r k) (hroot k)).toRingHom = Q
    rw [this]

theorem exists_continuousOn_embeddings (K : Type) [Field K] [CharZero K] (σ : Type) (L : Type)
    [Field L] [Algebra (FractionRing (MvPolynomial σ K)) L]
    [FiniteDimensional (FractionRing (MvPolynomial σ K)) L] (sg : K →+* ℂ)
    (G : Set (σ → ℂ))
    (hG : ∀ t ∈ G, ∀ p : MvPolynomial σ K, p ≠ 0 → MvPolynomial.eval₂ sg t p ≠ 0)
    (t₀ : σ → ℂ) (ht₀ : t₀ ∈ G) :
    ∃ U ∈ 𝓝 t₀, ∃ (n : ℕ) (Q : Fin n → (σ → ℂ) → (L →+* ℂ)),
      (∀ k a, ContinuousOn (fun t => Q k t a) (U ∩ G)) ∧
      ∀ t ∈ U ∩ G, Function.Injective (fun k => Q k t) ∧
        Set.range (fun k => Q k t) = {P : L →+* ℂ | ∀ p : MvPolynomial σ K,
          P (algebraMap (FractionRing (MvPolynomial σ K)) L
            (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)) =
            MvPolynomial.eval₂ sg t p} := by
  classical
  set R := MvPolynomial σ K with hR
  set F := FractionRing R with hF
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective R F)
  let pb : PowerBasis F L := Field.powerBasisOfFiniteOfSeparable F L
  choose nu de hde hfr using fun z : F => IsFractionRing.div_surjective (A := R) z
  let ev : F → (σ → ℂ) → ℂ := fun f t =>
    MvPolynomial.eval₂ sg t (nu f) / MvPolynomial.eval₂ sg t (de f)
  have hpc : ∀ p : R, Continuous fun t : σ → ℂ => MvPolynomial.eval₂ sg t p := by
    intro p
    simp_rw [MvPolynomial.eval₂_eq_eval_map]
    exact MvPolynomial.continuous_eval _
  have hev : ∀ f, ∀ t ∈ G, ContinuousAt (ev f) t := fun f t ht =>
    (hpc _).continuousAt.div (hpc _).continuousAt (hG t ht _ (nonZeroDivisors.ne_zero (hde f)))
  let cf : (σ → ℂ) → Fin pb.dim → ℂ := fun t i => ev ((minpoly F pb.gen).coeff i) t
  have hcf : ∀ t ∈ G, ContinuousAt cf t := fun t ht => continuousAt_pi.2 fun i => hev _ t ht
  let p : Polynomial (MvPolynomial (Fin pb.dim) ℂ) :=
    Polynomial.X ^ pb.dim + ∑ i : Fin pb.dim, Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ (i : ℕ)
  have hp : p.Monic := Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt _)
  have hτ : ∀ t ∈ G, ∃ τ : F →+* ℂ, (∀ q : R, τ (algebraMap R F q) = MvPolynomial.eval₂ sg t q) ∧
      (∀ f, τ f = ev f t) ∧ p.map (MvPolynomial.eval (cf t)) = (minpoly F pb.gen).map τ := by
    intro t ht
    have hinj : Function.Injective (MvPolynomial.eval₂Hom sg t : R →+* ℂ) := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro q hq
      by_contra h
      exact hG t ht q h hq
    have hτa : ∀ q : R, (IsFractionRing.lift hinj : F →+* ℂ) (algebraMap R F q) =
        MvPolynomial.eval₂ sg t q := fun q => IsFractionRing.lift_algebraMap hinj q
    have hτ : ∀ f, (IsFractionRing.lift hinj : F →+* ℂ) f = ev f t := by
      intro f
      conv_lhs => rw [← hfr f]
      rw [map_div₀, hτa, hτa]
    refine ⟨IsFractionRing.lift hinj, hτa, hτ, ?_⟩
    have hmon : (minpoly F pb.gen).Monic := minpoly.monic pb.isIntegral_gen
    conv_rhs => rw [hmon.as_sum, pb.natDegree_minpoly]

    rw [Polynomial.map_add (f := _), Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum,
    Finset.sum_range]
    simp [cf, hτ]
  obtain ⟨y, V, hV, hyc, hy⟩ := exists_continuousOn_roots p hp (cf t₀) (by
    obtain ⟨τ, -, -, h⟩ := hτ t₀ ht₀
    rw [h]
    exact Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F pb.gen))
  have key : ∀ t ∈ cf ⁻¹' V ∩ G, ∃ P : Fin p.natDegree → (L →+* ℂ),
      (∀ k, P k pb.gen = y k (cf t)) ∧ (∀ k f, P k (algebraMap F L f) = ev f t) ∧
      Set.range P = {P : L →+* ℂ | ∀ q : R, P (algebraMap F L (algebraMap R F q)) =
        MvPolynomial.eval₂ sg t q} := by
    intro t ht
    obtain ⟨τ, hτa, hτe, h⟩ := hτ t ht.2
    obtain ⟨P, hP, hPr⟩ := exists_embeddings_of_roots pb τ (fun k => y k (cf t))
      (by rw [← h]; exact (hy _ ht.1).2)
    refine ⟨P, hP, fun k f => ?_, ?_⟩
    · have hk : P k ∈ Set.range P := ⟨k, rfl⟩
      rw [hPr] at hk
      rw [← hτe]
      exact DFunLike.congr_fun hk f
    · rw [hPr]
      ext Q
      constructor
      · intro hQ q
        rw [← hτa]
        exact DFunLike.congr_fun hQ _
      · intro hQ
        apply IsFractionRing.ringHom_ext (A := R)
        intro q
        rw [hτa]
        exact hQ q
  have hU : cf ⁻¹' V ∈ 𝓝 t₀ := hcf t₀ ht₀ hV
  haveI : Nonempty (Fin p.natDegree → (L →+* ℂ)) :=
    ⟨(key t₀ ⟨mem_of_mem_nhds hU, ht₀⟩).choose⟩
  choose! P hP1 hP2 hP3 using key
  refine ⟨_, hU, p.natDegree, fun k t => P t k, fun k a => ?_, fun t ht => ⟨?_, hP3 t ht⟩⟩
  · have hc : ContinuousOn (fun t => ∑ l : Fin pb.dim,
        ev (pb.basis.repr a l) t * y k (cf t) ^ (l : ℕ)) (cf ⁻¹' V ∩ G) := by
      refine continuousOn_finsetSum _ fun l _ => ContinuousOn.mul
        (fun t ht => (hev _ t ht.2).continuousWithinAt) (ContinuousOn.pow ?_ _)
      exact (hyc k).comp (fun t ht => (hcf t ht.2).continuousWithinAt) fun t ht => ht.1
    refine hc.congr fun t ht => ?_
    show P t k a = _
    conv_lhs => rw [← pb.basis.sum_repr a]

    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Algebra.smul_def, map_mul, pb.basis_eq_pow, map_pow, hP1 t ht, hP2 t ht]
  · intro k l hkl
    apply (hy _ ht.1).1
    show y k (cf t) = y l (cf t)
    rw [← hP1 t ht, ← hP1 t ht]
    exact DFunLike.congr_fun hkl _


open MeasureTheory ReciprocityTheory.ChartRestriction.G.T0 SectionSum in
theorem exists_local_families (K Ω : Type) [Field K] [CharZero K] [Countable K] [Field Ω]
    [Algebra K Ω] (D N : ℕ) (j₀ : Fin (N + 1)) (w : Fin (N + 1) → Ω) (hw : w j₀ = 1)
    (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D)
    (hw' : Algebra.trdeg K (IntermediateField.adjoin K (Set.range w)) = D) (sg : K →+* ℂ) :
    ∃ S : Set (Fin D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1),
      MeasurableSet S ∧
      Measure.pi (fun _ => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere) S = 0 ∧
      ∀ t0 ∈ Sᶜ, ∃ U ∈ 𝓝 t0, ∃ (n : ℕ)
        (Q : Fin n → (Fin D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → (Ω →+* ℂ)),
        (∀ k (a : Ω), ContinuousOn (fun t => Q k t a) (U ∩ Sᶜ)) ∧
        ∀ t ∈ U ∩ Sᶜ, Function.Injective (fun k => Q k t) ∧
          Set.range (fun k => Q k t) = {P : Ω →+* ℂ | P ∈ PT sg ∧ ∀ i, ∑ j,
            (t i : EuclideanSpace ℂ (Fin (N + 1))) j * P (w j) = 0} := by
  let x : Fin N → Ω := fun k => w (j₀.succAbove k)
  have hadj : IntermediateField.adjoin K (Set.range w) = IntermediateField.adjoin K (Set.range x) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      obtain rfl | ⟨k, rfl⟩ := Fin.eq_self_or_eq_succAbove j₀ j
      · rw [hw]; exact one_mem _
      · exact IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨k, rfl⟩
      exact ⟨_, rfl⟩
  rw [hadj] at hw'
  have hJ := (exists_linearIndependent_D_iff_trdeg_adjoin_eq htr x).2 hw'
  obtain ⟨hinj, hfin⟩ := sImg_indep_finite K Ω D N j₀ x hfg htr hJ
  letI : Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := (liftS hinj).toAlgebra
  haveI := liftS_finite hinj hfin
  obtain ⟨s₀, hs₀⟩ := exists_ae_cons _ (Measure.toSphere_ne_zero _) D _
    (ae_eval₂_ne_zero_pi_toSphere K sg (D + 1) N)
  let F : (Fin D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → TVar D N → ℂ :=
    fun t q =>
      ((Fin.cons s₀ t : Fin (D + 1) → Metric.sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) q.1 :
        EuclideanSpace ℂ (Fin (N + 1))) q.2
  have hF : Continuous F := by
    refine continuous_pi fun q => ?_
    obtain ⟨i, j⟩ := q
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [F, Fin.cons_zero]
      exact continuous_const
    · simp only [F, Fin.cons_succ]
      fun_prop
  let G : Set (TVar D N → ℂ) :=
    {τ | ∀ p : MvPolynomial (TVar D N) K, p ≠ 0 → MvPolynomial.eval₂ sg τ p ≠ 0}
  have hGm : MeasurableSet G := by
    haveI := NPB.countable_mvPoly (σ := TVar D N) (R := K)
    have : G = ⋂ p : MvPolynomial (TVar D N) K, ⋂ _ : p ≠ 0,
        {τ | MvPolynomial.eval τ (MvPolynomial.map sg p) ≠ 0} := by
      ext τ
      simp only [G, Set.mem_setOf_eq, Set.mem_iInter, MvPolynomial.eval_map]
    rw [this]
    exact MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ =>
      (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const).measurableSet
  refine ⟨(F ⁻¹' G)ᶜ, (hF.measurable hGm).compl, hs₀, ?_⟩
  rw [compl_compl]
  intro t0 ht0
  obtain ⟨U, hU, n, Q, hQc, hQ⟩ := exists_continuousOn_embeddings K (TVar D N) (OmS Ω D N) sg G
    (fun _ h => h) (F t0) ht0
  refine ⟨F ⁻¹' U, hF.continuousAt hU, n,
    fun k t => (Q k (F t)).comp (algebraMap Ω (OmS Ω D N)), fun k a => ?_, fun t ht => ?_⟩
  · exact (hQc k (algebraMap Ω (OmS Ω D N) a)).comp hF.continuousOn fun t ht => ht
  have hb := bijOn_restrict (K := K) j₀ x sg (F t) (fun Q hQ hrel => by
    letI : Algebra K ℂ := sg.toAlgebra
    let φ : Ω →ₐ[K] ℂ := { Q with commutes' := fun r => DFunLike.congr_fun hQ r }
    refine existsUnique_ringHom_OmS K Ω ℂ D N j₀ x (F t) φ htr ?_ hrel
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra h0
    exact ht.2 p h0 hp)
  obtain ⟨hQi, hQr⟩ := hQ (F t) ht
  have hset : Set.range (fun k => Q k (F t)) = {P | ∀ p : MvPolynomial (TVar D N) K,
      P (sHom (K := K) j₀ x p) = MvPolynomial.eval₂ sg (F t) p} := by
    rw [hQr]
    ext P
    refine forall_congr' fun p => ?_
    rw [← liftS_algebraMap hinj p]
    rfl
  rw [← hset] at hb
  refine ⟨fun k l hkl => hQi (hb.injOn ⟨k, rfl⟩ ⟨l, rfl⟩ hkl), ?_⟩
  have := hb.image_eq
  rw [← Set.range_comp] at this
  refine Eq.trans this ?_
  ext P
  simp only [Set.mem_setOf_eq, F, Fin.cons_succ]
  refine and_congr_right fun _ => forall_congr' fun i => ?_
  rw [Fin.sum_univ_succAbove _ j₀, hw, map_one, mul_one]

end SectionLocal

end GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem stLoc_of_trdeg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c) (Dd N : ℕ) (uL : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)), FnFG Xo c → FnTrdeg Xo c Dd → (∀ Z, evC h Z (wR (jc Z)) ≠ 0) → (∀ Z, Algebra.trdeg c.F (IntermediateField.adjoin c.F (Set.range fun j => evC h Z (wR j) / evC h Z (wR (jc Z)))) = Dd) → STLoc h Dd N uL wR jc := by
  intro E _ _ _ H Dw l Xo c _ h Dd N uL wR jc hfg htr hw hw' _ _ _ Z sg
  haveI : Countable c.F := Countable.of_equiv _ (Module.finBasis ℚ c.F).equivFun.toEquiv.symm
  have hr : ∀ j, T0.ratio (Ω := Om Z) (valG h uL (wR j) Z) (valG h uL (wR (jc Z)) Z) =
      evC h Z (wR j) / evC h Z (wR (jc Z)) := by
    intro j
    apply T0.ValuationResidueLemmas.ratio_eq (valC_ne_zero (hw Z))
    simp only [valG, valC]
    rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ _ (hw Z)]
  simp only [hr]
  exact SectionLocal.exists_local_families c.F (Om Z) Dd N (jc Z)
    (fun j => evC h Z (wR j) / evC h Z (wR (jc Z))) (div_self (hw Z)) (hfg Z) (htr Z) (hw' Z) sg

end GlobalTheory.Reg
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapDivFinStLocDataOf

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.Reg

theorem kap_divFin_stLoc_dataOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ [Fintype (Comp Xo c)] (h : GenFrEx Xo c) (δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))) (Dd N T i g0 : ℕ) (cc : ℝ) (uL uF uka ude uet uta1 uta2 : WtR E) (wR : Fin (N + 1) → Rul Xo c) (jc : Comp Xo c → Fin (N + 1)) (np : ℕ) (thpR : Fin np → Rul Xo c) (n0 : ℕ) (th0R : Fin n0 → Rul Xo c) (uF0 : WtR E) (nk : ℕ) (thkR : Fin nk → Rul Xo c) (MR : Set (Rul Xo c)) (etR ta1R ta2R : Rul Xo c) (nu : HeightOneSpectrum (𝓞 c.F) → ℝ) (ip : (c.F →+* ℂ) → (∀ Z : Comp Xo c, AC Z) → (∀ Z : Comp Xo c, AC Z) → ℂ) (wsize : WTZ E → ℝ) (DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r : ℝ), 1 ≤ Dd → Dd = Dw.dim + Nat.card (FlagVar Dw) → (∀ Z, evC h Z (wR (jc Z)) ≠ 0) → A1Bigness (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) → KapFG Xo c ∧ KapTrdeg Xo c Dw.dim ∧ DivFin (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) ∧ STLoc h Dd N uL wR jc := by
  intro E _ _ _ H Dw l Xo c _ h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r hD hDd hjc hA
  obtain ⟨hfg, htr⟩ := kap_fg_trdeg E H Dw l Xo c
  have hFG : Formalism.L2.Pj.FnFG Xo c := fnFG_of Xo c hfg
  have hTr : Formalism.L2.Pj.FnTrdeg Xo c Dd := hDd ▸ fnTrdeg_of Xo c Dw.dim htr
  have hw : ∀ Z, (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).w ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).jc Z) Z ≠ 0 := fun Z => valC_ne_zero (hjc Z)
  have hT : ∀ Z, ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD (dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r) Z := fun Z =>
    ((GlobalTheory.differentials_iff_trdegD_and_genericSection _ _ _ _ _ (fun _ _ => ⊥) _ Z (hFG Z) (hTr Z) (hw Z)).1).1 (hA Z)
  refine ⟨hfg, htr, ?_, ?_⟩
  · exact divFin_of_trdeg E H Dw l Xo c _ hD hDd (fun Z j => valC_mem h uL.1 uL.2 (wR j) Z) hw hT
  · apply stLoc_of_trdeg E H Dw l Xo c h Dd N uL wR jc hFG hTr hjc
    intro Z
    have hZ := hT Z
    unfold ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD at hZ
    have key : (fun j => ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).w j Z) ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).w ((dataOf h δ fn yP Dd N T i g0 cc uL uF uka ude uet uta1 uta2 wR jc np thpR n0 th0R uF0 nk thkR MR etR ta1R ta2R nu ip wsize DF PN PQ tableDegreeThreeBase PP0' Pd Gc PI4 Pet tableLineDegreeFive tableLineDegreeTwo Prw PO f r).jc Z) Z)) =
        fun j => evC h Z (wR j) / evC h Z (wR (jc Z)) := by
      funext j
      refine ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.ratio_eq (valC_ne_zero (hjc Z)) ?_
      unfold dataOf valG valC
      simp [div_mul_cancel₀ _ (hjc Z)]
    rw [key] at hZ
    exact hZ


end GlobalTheory.Reg
end
end
