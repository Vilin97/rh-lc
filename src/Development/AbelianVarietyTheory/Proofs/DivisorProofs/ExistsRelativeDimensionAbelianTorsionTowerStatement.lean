module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeBaseChangeRigid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToRigidifiedExtensionBijectivePNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearCanonicalMapPrimitiveDeRhamRigExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDual
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfForallField

section

@[expose] public section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)

namespace GlobalTheory.FibreDim

theorem smoothOfRelativeDimension_of_forall_field : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (g : ℕ), Smooth X.hom → (∀ (k : Type) [Field k] [Algebra R k], SmoothOfRelativeDimension g (Limits.pullback.snd X.hom (spMap (algebraMap R k)))) → SmoothOfRelativeDimension g X.hom := by
  intro R _ X g hs h
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have hn : ∀ x, n x = g := fun x => by
    let p : PrimeSpectrum R := X.hom x
    have hk := h p.asIdeal.ResidueField
    let t := spMap (algebraMap R p.asIdeal.ResidueField)
    obtain ⟨y, hy⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R p.asIdeal.ResidueField)) := by
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      exact Ideal.ker_algebraMap_residueField p.asIdeal
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (n x)
    have h1 : SmoothOfRelativeDimension (n x) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) :=
      this.of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t) (hd x)
    have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) := by
      rw [← Limits.pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance
    obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t)
      ⟨x, hW x⟩ y hy.symm
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← hn x]; exact hd x

end GlobalTheory.FibreDim
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianTorsionTower

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TowerDim

theorem exists_smoothOfRelativeDimension_of_hodgeDeRham : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]
    (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ G : PDivGroup p R, G.TorsionTower A → ∃ g, SmoothOfRelativeDimension g A.hom := by
  intro hH p _ R _ hp A _ hA G t
  have hF : GlobalTheory.Published.AbelianDeRham.Free := (GlobalTheory.abelianDeRham_free_baseChange_rigid hH).1
  have hs := hA.smooth
  refine ⟨G.height / 2, GlobalTheory.FibreDim.smoothOfRelativeDimension_of_forall_field R A _ hs fun k _ _ ↦ ?_⟩
  have hk : IsNilpotent (p : k) := by simpa using hp.map (algebraMap R k)
  have hk0 : (p : k) = 0 := hk.eq_zero
  letI : GrpObj ((Over.pullback (spMap (algebraMap R k))).obj A) := Functor.grpObjObj
  have h := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback A (spMap (algebraMap R k))
  have hAk : IsAbelianScheme ((Over.pullback (spMap (algebraMap R k))).obj A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ A hA
  obtain ⟨gk, hgk⟩ := GlobalTheory.AbelianDim.exists_relDim k ((Over.pullback (spMap (algebraMap R k))).obj A) hAk
  let tk := t.baseChange h
  obtain ⟨L, hL⟩ := GlobalTheory.PtExt.exists_canMap k ((Over.pullback (spMap (algebraMap R k))).obj A) p
    (G.baseChange k) tk hAk
  have hbij : Function.Bijective L :=
    GlobalTheory.T.deRham_to_rigidified_extension_bijective_p_nilpotent hH p k hk _ gk hAk hgk (G.baseChange k) tk L fun c ↦ (hL c (L c)).2 rfl
  obtain ⟨hfin, hprj, hrk⟩ := hF.prim hAk hgk
  have h1 : Module.finrank k (primDR ((Over.pullback (spMap (algebraMap R k))).obj A)) = 2 * gk := by
    have := hrk ⊥
    rwa [Module.rankAtStalk_eq_finrank_of_free] at this
  have h2 : Module.finrank k (G.baseChange k).RigExt = G.height :=
    (GlobalTheory.PDivGroup.finrank_rigExt_omega p k hk0 (G.baseChange k)).2.2.1
  have h3 : 2 * gk = G.height := by
    rw [← h1, ← h2]; exact (LinearEquiv.ofBijective L hbij).finrank_eq
  have h4 : G.height / 2 = gk := by omega
  rw [h4]
  exact hgk

end GlobalTheory.TowerDim
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRelativeDimensionAbelianTorsionTowerStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_relativeDimension_abelian_torsionTower : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ G : PDivGroup p R, G.TorsionTower A → ∃ g, SmoothOfRelativeDimension g A.hom := by
  first | exact @GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham | exact GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham | (intros; apply GlobalTheory.TowerDim.exists_smoothOfRelativeDimension_of_hodgeDeRham <;> assumption)
end
end
