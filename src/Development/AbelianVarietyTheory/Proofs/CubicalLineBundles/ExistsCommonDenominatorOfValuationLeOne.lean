module

public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDetIdealLocalGenFullLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDvrModelLieBasisAtPrimeStatement
public import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ValuationLeIffExistsSmulMem
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyInNormalFormAndArchimedeanConstant
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSecGeneric
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsFibreOfIffIsPolFibre
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsModelAtIntegralIffMemLieLat
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KeyLocAtOfIsLocalModelStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegersStatement
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeOfIsLocalModelAtPrime
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFractionalIdealLocalGenOfValuation

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.L2.LamCM
open scoped nonZeroDivisors

namespace GlobalTheory.LamF

theorem exists_fractionalIdeal_isLocGen_of_valuation : ∀ (K : Type) [Field K] [NumberField K]
    (oa : HeightOneSpectrum (𝓞 K) → ℤ), (Function.support oa).Finite →
    ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧
      ∀ (p : HeightOneSpectrum (𝓞 K)) (a : K), p.valuation K a = WithZero.exp (-oa p) → IsLocGen p a I := by
  intro K _ _ oa hfin
  refine ⟨∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ oa v, ?_, fun p a ha => ?_⟩
  · refine finprod_induction (fun L : FractionalIdeal (𝓞 K)⁰ K => L ≠ 0) one_ne_zero
      (fun _ _ h h' => mul_ne_zero h h') fun v => ?_
    exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 v.ne_bot)
  · rw [isLocGen_iff_valuation_eq, FractionalIdeal.count_finprod K p oa, ha]
    exact hfin

end GlobalTheory.LamF
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFractionalIdealLocalGenOfValuationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_fractionalIdeal_localGen_of_valuation : ∀ (K : Type) [Field K] [NumberField K] (oa : HeightOneSpectrum (𝓞 K) → ℤ), (Function.support oa).Finite → ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K, I ≠ 0 ∧ ∀ (p : HeightOneSpectrum (𝓞 K)) (a : K), p.valuation K a = WithZero.exp (-oa p) → IsLocGen p a I := by
  first | exact @GlobalTheory.LamF.exists_fractionalIdeal_isLocGen_of_valuation | exact GlobalTheory.LamF.exists_fractionalIdeal_isLocGen_of_valuation | (intros; apply GlobalTheory.LamF.exists_fractionalIdeal_isLocGen_of_valuation <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosKeyArchAt

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.LamF.KeyArch

theorem pos_of_isArchNorm (hU : ThetaUnifAV) (x : KeyIn ℂ) {nth nη : ℝ} (h : KeyPow.IsArchNorm x nth nη) :
    0 < nth ∧ 0 < nη := by
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  obtain ⟨u', τ, M, a, b, c, -, -, -, -, -, -, -, -, -, -, e⟩ :=
    keyIn_normal_form_and_archimedean_constant hU x u Hm W χ θ Fd nth nη h₁ h₂ h₃ h₄ h₅ h₆ h₇
  have p₁ : 0 ≤ nth :=
    h₆ ▸ div_nonneg (MeasureTheory.integral_nonneg fun z => by positivity) ENNReal.toReal_nonneg
  have p₂ : 0 ≤ nη := h₇ ▸ by positivity
  have hne : ‖M.det ^ 4 / c ^ 8‖ * nth ^ 4 * nη ^ 2 ≠ 0 := by
    rw [e]; have := Real.pi_pos; positivity
  have q₁ := right_ne_zero_of_mul (left_ne_zero_of_mul hne)
  have q₂ := right_ne_zero_of_mul hne
  exact ⟨p₁.lt_of_ne' fun h0 => q₁ (by rw [h0]; norm_num), p₂.lt_of_ne' fun h0 => q₂ (by rw [h0]; norm_num)⟩

theorem exists_pos_keyArchAt : ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (σ : K →+* ℂ), ∃ t n : ℝ, 0 < t ∧ 0 < n ∧ ∀ T abelian₂ : MLine K, T.n σ = t → abelian₂.n σ = n → KeyArchAt x T abelian₂ σ := by
  intro hU K _ _ x σ
  obtain ⟨x', hx⟩ := KeyPow.exists_keyPB x σ
  obtain ⟨nth, nη, h⟩ := KeyPow.exists_isArchNorm hU x'
  obtain ⟨p₁, p₂⟩ := pos_of_isArchNorm hU x' h
  obtain ⟨u, Hm, W, χ, θ, Fd, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨Real.sqrt nth, Real.sqrt nη⁻¹, Real.sqrt_pos.2 p₁, Real.sqrt_pos.2 (inv_pos.2 p₂), fun T abelian₂ hT hL =>
    ⟨x', u, Hm, W, χ, θ, Fd, hx, h₁, h₂, h₃, h₄, h₅, ?_, ?_⟩⟩
  · rw [hT, Real.sq_sqrt p₁.le, h₆]
  · rw [hL, Real.sq_sqrt (inv_pos.2 p₂).le, h₇, inv_div]

end GlobalTheory.LamF.KeyArch
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPosKeyArchAtStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF


theorem _root_.GlobalTheory.T.exists_pos_keyArchAt' : ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (σ : K →+* ℂ), ∃ t n : ℝ, 0 < t ∧ 0 < n ∧ ∀ T abelian₂ : MLine K, T.n σ = t → abelian₂.n σ = n → KeyArchAt x T abelian₂ σ := by
  first | exact @GlobalTheory.LamF.KeyArch.exists_pos_keyArchAt | exact GlobalTheory.LamF.KeyArch.exists_pos_keyArchAt | (intros; apply GlobalTheory.LamF.KeyArch.exists_pos_keyArchAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeOfIsLocalModelAtPrimeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM


theorem _root_.GlobalTheory.T.lieLattice_of_isLocalModel_at_prime : HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (hg rig hr th hth) (𝔭 : HeightOneSpectrum (𝓞 K)) (a : K) (M : Matrix (Fin F.P₀.g) (Fin F.P₀.g) K), KeyPow.IsLocalModel (F.key hg rig hr th hth) 𝔭 a M → (∀ i, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • M i ∈ F.lieLat) ∧ ∀ c ∈ F.lieLat, ∃ s : 𝓞 K, s ∉ 𝔭.asIdeal ∧ s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i) := by
  first | exact @GlobalTheory.CM.lieLat_of_isLocalModel | exact GlobalTheory.CM.lieLat_of_isLocalModel | (intros; apply GlobalTheory.CM.lieLat_of_isLocalModel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommonDenominatorOfValuationLeOne

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_common_denominator_of_valuation_le_one {K : Type} [Field K] [NumberField K] (p : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (a : Fin n → K) (ha : ∀ m, p.valuation K (a m) ≤ 1) :
    ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ ∀ m, ∃ b : 𝓞 K, s • a m = algebraMap (𝓞 K) K b := by
  choose nn dd hnd using fun m => p.exists_primeCompl_mul_eq_of_integer (a m) (ha m)
  have hs : (∏ m, (dd m : 𝓞 K)) ∈ p.asIdeal.primeCompl := prod_mem fun m _ => (dd m).2
  refine ⟨∏ m, (dd m : 𝓞 K), hs, fun m => ?_⟩
  refine ⟨nn m * ∏ j ∈ Finset.univ.erase m, (dd j : 𝓞 K), ?_⟩
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), Algebra.smul_def]
  simp only [map_mul]
  rw [← hnd m]
  ring

theorem IsModelAt.rows_span_lieLat {K : Type} [Field K] [NumberField K] {A : Out.PolAV (Sp (𝓞 K))} {x : KeyIn K}
    {φ : x.P.A.left ⟶ A.A.left} (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) {p : HeightOneSpectrum (𝓞 K)}
    {M : Matrix (Fin x.P.g) (Fin x.P.g) K} (hM : IsModelAt A x φ p M) :
    (∀ i, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧ s • M i ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat) ∧
      ∀ c ∈ (GenFib.mk x.P φ hf x.v x.basis : GenFib A).lieLat, ∃ s : 𝓞 K, s ∉ p.asIdeal ∧
        s • c ∈ Submodule.span (𝓞 K) (Set.range fun i => M i) := by
  have hdet : M.det ≠ 0 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, -, -, -, h, -⟩ := hM
    exact h
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have key := isModelAt_integral_iff_mem_lieLat K A x φ hf p M hM
  refine ⟨fun i => (key (M i)).mp fun m => ?_, fun c hc => ?_⟩
  · have h1 : Matrix.vecMul (M i) M⁻¹ m = (1 : Matrix (Fin x.P.g) (Fin x.P.g) K) i m := by
      rw [← Matrix.mul_nonsing_inv (A := M) hu]
      rfl
    rw [h1, Matrix.one_apply]
    split_ifs <;> simp
  · have hone : (1 : 𝓞 K) ∉ p.asIdeal := fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    have hv := (key c).mpr ⟨1, hone, by simpa using hc⟩
    obtain ⟨s, hs, hb⟩ := exists_common_denominator_of_valuation_le_one p (Matrix.vecMul c M⁻¹) hv
    choose b hb using hb
    refine ⟨s, hs, ?_⟩
    have hc' : c = ∑ m, Matrix.vecMul c M⁻¹ m • M m := by
      rw [← Matrix.vecMul_eq_sum, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul (A := M) hu, Matrix.vecMul_one]
    rw [hc', Finset.smul_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [← smul_assoc, hb m, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

theorem exists_keyLines : Out.SecTwistSt → ThetaUnifAV → Out.Laws → HomExtDvr → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∃ T abelian₂ : MLine K, T.Good ∧ abelian₂.Good ∧ (∀ p, KeyLocAt x T abelian₂ p) ∧ (∀ σ, KeyArchAt x T abelian₂ σ) ∧ ∀ p, ∃ M, IsModelAt A x φ p M ∧ IsLocGen p M.det abelian₂.I := by
  intro hT hU _hL hH K _ _ A x φ hfib
  have hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ :=
    (isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) A x φ).mp hfib
  let F : GenFib A := GenFib.mk x.P φ hf x.v x.basis
  obtain ⟨hFG, hspan⟩ := GlobalTheory.T.lieLattice_fg_and_span_eq_top_ringOfIntegers K A F
  obtain ⟨IL, hIL0, hIL⟩ := GlobalTheory.T.exists_detIdeal_localGen_full_lattice K x.P.g F.lieLat hFG hspan
  obtain ⟨δ, oa, nth, hloc, -, hsupp, -⟩ :=
    GlobalTheory.ThetaDegree.exists_isThetaDeg hT hU K A F x.g_pos x.rig x.rig_gen x.th x.6
  obtain ⟨IT, hIT0, hIT⟩ := GlobalTheory.T.exists_fractionalIdeal_localGen_of_valuation K oa hsupp
  choose t n ht hn hArch using fun σ => GlobalTheory.T.exists_pos_keyArchAt' hU K x σ
  refine ⟨⟨IT, t⟩, ⟨IL, n⟩, And.intro hIT0 ht, And.intro hIL0 hn, fun p => ?_,
    fun σ => hArch σ _ _ rfl rfl, fun p => ?_⟩
  · obtain ⟨a, M, hM, hva⟩ := hloc p
    have hrows := GlobalTheory.T.lieLattice_of_isLocalModel_at_prime hH K A F x.g_pos x.rig x.rig_gen x.th x.6 p a M hM
    exact GlobalTheory.T.keyLocAt_of_isLocalModel' K x ⟨IT, t⟩ ⟨IL, n⟩ p a M hM (hIT p a hva) (hIL p M hrows.1 hrows.2)
  · obtain ⟨M, hM⟩ := GlobalTheory.T.exists_dvrModel_lieBasis_at_prime hT K A x φ hfib p
    have hrows := hM.rows_span_lieLat hf
    exact ⟨M, hM, hIL p M hrows.1 hrows.2⟩

end GlobalTheory.LamF
end
end
