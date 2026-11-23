module

public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.QatOfBridge
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNumberFieldFunctionalBoundedCompExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobSt
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.KerCorePf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.LocalQuotientRank

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNumberFieldFunctionalBoundedCompExtensionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries

theorem _root_.GlobalTheory.T.isNumberFieldFunctionalBounded_comp_extension : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] (M : Set V) (S : (K →+* ℂ) → V → ℝ) (be : HeightOneSpectrum (𝓞 K) → ℝ) (Carch Bdeg : ℝ) (K' K₁ : Type) [Field K'] [NumberField K'] [Algebra K K'] [Field K₁] [NumberField K₁] [Algebra K K₁] (f : K' →ₐ[K] K₁) (φ : V →ₗ[K] K'), NumGood M S be Carch Bdeg K' φ → NumGood M S be Carch Bdeg K₁ (f.toLinearMap.comp φ) := by
  first | exact @GlobalTheory.ArcCM.numGood_comp | exact GlobalTheory.ArcCM.numGood_comp | (intros; apply GlobalTheory.ArcCM.numGood_comp <;> assumption)
end
end

-- Source module: Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.DegreeInfimum.PlaceDegreeSums

section

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj.QAt.PlaceDegreeSums

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped nonZeroDivisors

variable {K : Type} [Field K] [NumberField K]

theorem sum_infinite_places_mult (f : InfinitePlace K → ℝ) :
    ∑ σ : InfinitePlace K, (σ.mult : ℝ) * f σ = ∑ τ : K →+* ℂ, f (InfinitePlace.mk τ) := by
  classical
  refine Eq.trans ?_ (Finset.sum_fiberwise Finset.univ (fun τ : K →+* ℂ => InfinitePlace.mk τ)
    (fun τ => f (InfinitePlace.mk τ)))
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f w) (fun τ hτ => by rw [(Finset.mem_filter.mp hτ).2]),
    Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

theorem sum_count_log_norm (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) :
    ∑ᶠ w : HeightOneSpectrum (𝓞 K), (FractionalIdeal.count K w I : ℝ) * logN w =
      Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) := by
  classical
  have h00 := FractionalIdeal.finite_factors I
  have hfs : {v : HeightOneSpectrum (𝓞 K) | ¬ FractionalIdeal.count K v I = 0}.Finite :=
    Filter.eventually_cofinite.mp h00
  have hN : ∀ v : HeightOneSpectrum (𝓞 K),
      ((FractionalIdeal.absNorm ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v I) : ℚ) : ℝ) =
        ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count K v I := by
    intro v
    simp [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
  have hNpos : ∀ v : HeightOneSpectrum (𝓞 K), (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
    intro v
    exact_mod_cast Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hprod : FractionalIdeal.absNorm I = ∏ v ∈ hfs.toFinset,
      FractionalIdeal.absNorm ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ FractionalIdeal.count K v I) := by
    conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
    rw [finprod_eq_prod_of_mulSupport_subset _ (by
      intro v hv
      by_contra h0
      apply hv
      have h0' : FractionalIdeal.count K v I = 0 := by
        by_contra hc
        exact h0 (Finset.mem_coe.mpr (hfs.mem_toFinset.mpr hc))
      simp [h0']), map_prod]
  have hterm : ∀ v : HeightOneSpectrum (𝓞 K), (FractionalIdeal.count K v I : ℝ) * logN v =
      Real.log ((FractionalIdeal.absNorm ((v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^
        FractionalIdeal.count K v I) : ℚ) : ℝ) := by
    intro v
    rw [hN, Real.log_zpow, logN]
  rw [finsum_eq_sum_of_support_subset _ (s := hfs.toFinset) ?_, hprod]
  · rw [Rat.cast_prod, Real.log_prod]
    · exact Finset.sum_congr rfl fun v _ => hterm v
    · intro v _
      rw [hN]
      exact (zpow_pos (hNpos v) _).ne'
  · intro v hv
    by_contra h0
    apply hv
    have h0' : FractionalIdeal.count K v I = 0 := by
        by_contra hc
        exact h0 (Finset.mem_coe.mpr (hfs.mem_toFinset.mpr hc))
    simp [h0']

end Formalism.L2.Pj.QAt.PlaceDegreeSums
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.QbridgeOfNumGood

section

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.BasicNotions Formalism.L2.LamCM GlobalTheory.ArcCM

namespace GlobalTheory.ArcCM

theorem ndeg_eq_places {K : Type} [Field K] [NumberField K] (N : MLine K) (hN : N.Good)
    (hc : ∀ σ : K →+* ℂ, N.n ((starRingEnd ℂ).comp σ) = N.n σ) :
    ((∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) -
      ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding)) / (Module.finrank ℚ K : ℝ) = N.ndeg := by
  have h1 : (∑ᶠ w : HeightOneSpectrum (𝓞 K), (-(FractionalIdeal.count K w N.I : ℝ)) * logN w) =
      -Real.log ((FractionalIdeal.absNorm N.I : ℚ) : ℝ) := by
    simp_rw [neg_mul]
    rw [finsum_neg_distrib, PlaceDegreeSums.sum_count_log_norm _ hN.1]
  have h2 : ∑ σ : InfinitePlace K, (σ.mult : ℝ) * Real.log (N.n σ.embedding) =
      ∑ τ : K →+* ℂ, Real.log (N.n τ) := by
    rw [PlaceDegreeSums.sum_infinite_places_mult (fun σ => Real.log (N.n σ.embedding))]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · rw [h]
    · rw [h]
      exact congrArg Real.log (hc τ)
  rw [h1, h2, MLine.ndeg, MLine.deg]

theorem qbridge_of_numGood : ∀ (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Ch Ah Cc Ac Tt cc : ℝ) (be : HeightOneSpectrum (𝓞 B.KO) → ℝ) (Carch Bdeg : ℝ), Submodule.IsFullLattice B.KO (B.Mlat j ka) → (∀ la, 0 ≤ be la) → (Function.support be).Finite → (∑ᶠ la, be la * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ τ F, B.supN j ka ((starRingEnd ℂ).comp τ) F = B.supN j ka τ F) → WeightFamilies.PPv D large₂ Ch Ah * ka.size + Carch + Bdeg + Real.log (WeightFamilies.rhoP B CR Tt cc j ka : ℝ) / 2 ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size → (∀ F : B.Cusp j ka, F ∉ WeightFamilies.MggK B CR Tt cc j ka → ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra B.KO K₁) (φ : B.Cusp j ka →ₗ[B.KO] K₁), WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧ φ F ≠ 0 ∧ NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ) → QBridgeAt large₂ B j ka CR Ch Ah Cc Ac Tt cc := by
  intro D large₂ B j ka CR Ch Ah Cc Ac Tt cc be Carch Bdeg hlat hbe hbefin hbesum hconj hroom hdet
  classical
  obtain ⟨K₁, _, _, _, ρ, g, cf, hfam, hcf, hker, hdim⟩ := kerCore_holds B.KO (B.Cusp j ka)
    (WeightFamilies.MggK B CR Tt cc j ka)
    (fun K₁ _ _ _ φ => WeightFamilies.MggK B CR Tt cc j ka ≤ LinearMap.ker φ ∧
      NumGood (B.Mlat j ka : Set (B.Cusp j ka)) (B.supN j ka) be Carch Bdeg K₁ φ)
    (fun _ _ _ _ _ h => h.1)
    (fun v hv => by
      by_contra hn
      obtain ⟨K₁, _, _, _, φ, h1, h2, h3⟩ := hdet v hn
      exact h2 (hv K₁ φ ⟨h1, h3⟩))
    (fun K' K₁ _ _ _ _ _ _ e f hf => ⟨e.toLinearMap.comp f, ⟨fun v hv => by
      have := LinearMap.mem_ker.1 (hf.1 hv)
      simp [LinearMap.mem_ker, this], GlobalTheory.T.isNumberFieldFunctionalBounded_comp_extension _ _ _ _ _ _ _ K' K₁ e f hf.2⟩, fun _ => rfl⟩)
  let _ := hlat
  have hrk : WeightFamilies.rhoP B CR Tt cc j ka + Module.finrank B.KO (WeightFamilies.MggK B CR Tt cc j ka) =
      Module.finrank B.KO (B.Cusp j ka) :=
    LocalQuotientRank.rank_QuotMW (K := B.KO) (B.Mlat j ka) hlat.fg (Submodule.IsFullLattice.span_eq_top (A := B.KO) (M := B.Mlat j ka)) (WeightFamilies.MggK B CR Tt cc j ka)
  have hρ : ρ = WeightFamilies.rhoP B CR Tt cc j ka := by omega
  subst hρ
  choose N hG hd hc hint harch using fun i => (hfam i).2
  refine ⟨K₁, inferInstance, inferInstance, inferInstance, cf, be,
    fun i w => -(FractionalIdeal.count K₁ w (N i).I : ℝ), fun i σ => Real.log ((N i).n σ.embedding), Carch, Bdeg,
    hker, hbe, hbefin, hbesum, fun i => ?_, fun la w hw i F hF hne => ?_, hconj, fun σ i F hF hne => ?_,
    fun i => ?_, hroom⟩
  · refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors (N i).I)).subset fun w hw h => hw ?_
    simp [h]
  · rw [hcf] at hne ⊢
    exact (hint i la w hw F hF hne).trans_eq (sub_eq_add_neg _ _)
  · rw [hcf] at hne ⊢
    rw [← InfinitePlace.norm_embedding_eq]
    exact harch i σ.embedding F hF hne
  · rw [ndeg_eq_places (N i) (hG i) (hc i)]
    exact hd i

end GlobalTheory.ArcCM
end
end
