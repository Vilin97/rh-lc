module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegFunctionFieldEq
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsAddEquivOfSurjectiveOfKerIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegLeSuccOfEmbeddingRatFunc

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc :
    ∀ (F k L : Type) [Field F] [Field k] [Field L] [Algebra F k] [Algebra F L] (α : k →+* L)
      (j : L →+* RatFunc k) (d : ℕ), α.comp (algebraMap F k) = algebraMap F L →
      j.comp α = algebraMap k (RatFunc k) → Algebra.trdeg F k = d →
      Algebra.trdeg F L ≤ (d + 1 : ℕ) := by
  intro F k L _ _ _ _ _ α j d hα hj hd
  let jF : L →ₐ[F] RatFunc k :=
    { j with
      commutes' := fun x => by
        show j (algebraMap F L x) = algebraMap k (RatFunc k) (algebraMap F k x)
        rw [← hα, ← hj]; rfl }
  have h1 : Algebra.trdeg F L ≤ Algebra.trdeg F (RatFunc k) :=
    trdeg_le_of_injective jF j.injective
  have hR : Algebra.trdeg k (RatFunc k) = 1 := by
    have : Algebra.IsAlgebraic (Polynomial k) (RatFunc k) :=
      IsLocalization.isAlgebraic (RatFunc k) (nonZeroDivisors (Polynomial k))
    rw [← trdeg_add_eq k (Polynomial k), trdeg_eq_zero (R := Polynomial k) (A := RatFunc k),
      add_zero, Polynomial.trdeg_of_isDomain]
  have h2 := trdeg_add_eq F k (A := RatFunc k)
  calc Algebra.trdeg F L ≤ Algebra.trdeg F (RatFunc k) := h1
    _ = ((d + 1 : ℕ) : Cardinal) := by rw [← h2, hR, hd]; push_cast; rfl
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegLeSuccOfEmbeddingRatFuncStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.trdeg_le_succ_of_embedding_ratFunc : ∀ (F k L : Type) [Field F] [Field k] [Field L] [Algebra F k] [Algebra F L] (α : k →+* L) (j : L →+* RatFunc k) (d : ℕ), α.comp (algebraMap F k) = algebraMap F L → j.comp α = algebraMap k (RatFunc k) → Algebra.trdeg F k = d → Algebra.trdeg F L ≤ (d + 1 : ℕ) := by
  first | exact @GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc | exact GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc | (intros; apply GlobalTheory.FlagPush.trdeg_le_succ_of_ratFunc <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSmallOfFunctionFieldEmbedsRatFunc

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

namespace GlobalTheory.FlagPush.SmallPf

theorem exists_dim (F : Type) [Field F] {Z : Scheme.{0}} [IsIntegral Z] (f : Z ⟶ Sp F) [LocallyOfFiniteType f] :
    ∃ d : ℕ, topologicalKrullDim Z = d := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint Z)) isOpen_univ
  have hU : IsAffineOpen U := hU
  obtain ⟨d, h₁, -⟩ := GlobalTheory.OpenDim.ringKrullDim_affineOpen F f hU ⟨_, hxU⟩
  refine ⟨d, ?_⟩
  rw [← GlobalTheory.OpenDim.topologicalKrullDim_open F f U ⟨_, hxU⟩, ← h₁, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec

theorem main : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ j : W.Z.functionField →+* RatFunc Y.Fn, j.comp W.α₁ = algebraMap Y.Fn (RatFunc Y.Fn) → W.Small := by
  intro F _ Y W j hj
  have hp := W.proj
  have hlft : LocallyOfFiniteType (W.p₁ ≫ Y.str) := by
    obtain ⟨N, i, hi, hcomp⟩ := hp
    haveI : IsProper (PSpace.str F N) := isProper_str F N
    rw [← hcomp]; infer_instance
  obtain ⟨d, hd⟩ := exists_dim F (W.p₁ ≫ Y.str)
  have hY : Y.X.fromSpecStalk (genericPoint Y.X) ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
  have hZ : W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁ ≫ Y.str = spMap (W.α₁.comp (algebraMap F Y.Fn)) := by
    have h1 : spMap W.α₁ ≫ Y.X.fromSpecStalk (genericPoint Y.X) = W.Z.fromSpecStalk (genericPoint W.Z) ≫ W.p₁ :=
      specMap_functionFieldMap W.p₁
    rw [← Category.assoc, ← h1, Category.assoc, hY]
    exact (Spec.map_comp (CommRingCat.ofHom (algebraMap F Y.Fn)) (CommRingCat.ofHom W.α₁)).symm
  have t₁ := GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F Y.X Y.str Y.dim Y.isProjOver Y.topologicalKrullDim_eq _ hY
  have t₂ := GlobalTheory.FunctionFieldTrdeg.trdeg_functionField_eq F W.Z _ d W.proj hd _ hZ
  have t₃ := @GlobalTheory.T.trdeg_le_succ_of_embedding_ratFunc F Y.Fn W.Z.functionField _ _ _ (algebraMap F Y.Fn).toAlgebra
    (W.α₁.comp (algebraMap F Y.Fn)).toAlgebra W.α₁ j Y.dim rfl hj t₁
  rw [t₂] at t₃
  have : d ≤ Y.dim + 1 := by exact_mod_cast t₃
  unfold Dbl.Small
  rw [hd]
  exact_mod_cast this

end GlobalTheory.FlagPush.SmallPf
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleSpaceSmallOfFunctionFieldEmbedsRatFuncStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical

theorem _root_.GlobalTheory.T.doubleSpace_small_of_functionField_embeds_ratFunc : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), ∀ j : W.Z.functionField →+* RatFunc Y.Fn, j.comp W.α₁ = algebraMap Y.Fn (RatFunc Y.Fn) → W.Small := by
  first | exact @GlobalTheory.FlagPush.SmallPf.main | exact GlobalTheory.FlagPush.SmallPf.main | (intros; apply GlobalTheory.FlagPush.SmallPf.main <;> assumption)
end
end
