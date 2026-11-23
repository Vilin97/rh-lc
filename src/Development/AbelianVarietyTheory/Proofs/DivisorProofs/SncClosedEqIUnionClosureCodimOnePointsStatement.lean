module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsBasicOpenCover
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsNonzeroLocusEqAffineOpenLocallyFactorial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromSpecStalkMemZeroLocusIff
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Monomial
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoices
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromSpecStalkMemZeroLocusIff
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.DetJacMatCoordsEqTransitionJacobianDet

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncComponentsLocalSnc

section

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

open ReciprocityTheory.AnForm.R

namespace GlobalTheory.SncLocal

theorem mem_comps_of_compList {X : Scheme.{0}} {B : Set X} {m : ℕ} {C : Fin m → Closeds X}
    (hC : FinalTheorems.CompList B C) (i : Fin m) : (C i : Set X) ∈ ReciprocityTheory.AnForm.R.comps B := by
  classical
  refine ⟨⟨hC.1 i, hC.2.1 ▸ Set.subset_iUnion (fun j => (C j : Set X)) i⟩, fun D hD hiD => ?_⟩
  obtain ⟨z, hz, hDz⟩ := (isIrreducible_iff_sUnion_isClosed.1 hD.1)
    (Finset.univ.image fun j => (C j : Set X))
    (fun z hz => by
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
      exact (C j).isClosed)
    (by
      refine hD.2.trans (hC.2.1 ▸ Set.iUnion_subset fun j => ?_)
      exact Set.subset_sUnion_of_mem (Finset.mem_coe.2 (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
  have hij : i = j := hC.2.2 i j (hiD.trans hDz)
  subst hij
  exact hDz

theorem lSncAt_of_snc (X : Scheme.{0}) [IsNoetherian X] (B : Closeds X) (m : ℕ) (C : Fin m → Closeds X)
    (hB : Snc (Scheme.IdealSheafData.vanishingIdeal B)) (hC : CompList (B : Set X) C) (x : X) :
    LSncAt X C x := by
  obtain ⟨hreg, U, hx, n, f, J, hrsp, hZU⟩ := hB x
  haveI := hreg
  have hs : ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) = B := by simp
  obtain ⟨O, hxO, -, hO⟩ := exists_open_comps x U hx f J hrsp hZU
  have key : ∀ i : {i : Fin m // x ∈ C i}, ∃ j ∈ J,
      ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) (f j) x (C i.1) ∧
      stalkId (Scheme.IdealSheafData.vanishingIdeal (C i.1)) x =
        Ideal.span {X.presheaf.germ U.1 x hx (f j)} := by
    rintro ⟨i, hxi⟩
    have hCi : ((C i : Closeds X) : Set X) ∈
        ReciprocityTheory.AnForm.R.comps ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X) :=
      hs ▸ mem_comps_of_compList hC i
    have hO' := hO _ hCi
    have hq : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ (C i : Set X) ↔
        ∃ j ∈ J, ReciprocityTheory.AnForm.R.IsBranch ((Scheme.IdealSheafData.vanishingIdeal B).support : Set X)
          (f j) x (C i) ∧ X.presheaf.germ U.1 x hx (f j) ∈ q.asIdeal := by
      intro q
      have hqO : X.fromSpecStalk x q ∈ (O : Set X) := by
        have h : X.fromSpecStalk x q ∈ Set.range (X.fromSpecStalk x) := ⟨q, rfl⟩
        rw [Scheme.range_fromSpecStalk] at h
        exact Specializes.mem_open h O.isOpen hxO
      have h := Set.ext_iff.1 hO' (X.fromSpecStalk x q)
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hqO, and_true, true_and,
        GlobalTheory.SncComponents.fromSpecStalk_mem_zeroLocus_iff U x hx] at h
      exact h
    obtain ⟨j, hj, hbj, -⟩ := (hq (IsLocalRing.closedPoint _)).1
      (by rw [Scheme.fromSpecStalk_closedPoint]; exact hxi)
    refine ⟨j, hj, hbj, ?_⟩
    have hCC : (C i).compl.compl = C i := SetLike.coe_injective (compl_compl _)
    have hp : Prime (X.presheaf.germ U.1 x hx (f j)) :=
      prime_of_regular_params (fun i => X.presheaf.germ U.1 x hx (f i)) hrsp.1 hrsp.2 j
    have h := GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl (C i).compl x
      (X.presheaf.germ U.1 x hx (f j)) fun q => by
        refine not_congr ((hq q).trans ⟨?_, fun h => ⟨j, hj, hbj, h⟩⟩)
        rintro ⟨k, hk, hbk, h⟩
        by_cases hjk : j = k
        · exact hjk ▸ h
        · exact absurd rfl (branch_ne x U hx f J hrsp hZU hj hk hjk hbj hbk)
    rw [hCC] at h
    rw [h]
    exact ((Ideal.span_singleton_prime hp.ne_zero).2 hp).radical
  choose g hgJ hgb hgs using key
  refine ⟨hreg, n, fun k => X.presheaf.germ U.1 x hx (f k), ⟨g, fun a b hab => ?_⟩, hrsp, hgs⟩
  have h1 := hgb a
  rw [hab] at h1
  obtain ⟨D, -, hD⟩ := existsUnique_branch x U hx f J hrsp hZU (g b) (hgJ b)
  have e : (C a.1 : Set X) = C b.1 := (hD _ h1).trans (hD _ (hgb b)).symm
  exact Subtype.ext (hC.2.2 _ _ e.le)

theorem lSncAt_of_snc' : ∀ (X : Scheme.{0}) [IsNoetherian X] (B : Closeds X) (m : ℕ) (C : Fin m → Closeds X), Snc (Scheme.IdealSheafData.vanishingIdeal B) → CompList (B : Set X) C → ∀ x : X, LSncAt X C x :=
  fun X _ B m C hB hC x => lSncAt_of_snc X B m C hB hC x

end GlobalTheory.SncLocal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncClosedEqIUnionClosureCodimOnePoints

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.SncGenericPoints

theorem mem_vanishingIdeal_closure {X : Scheme.{0}} (x : X) (U : X.affineOpens) (hx : x ∈ U.1)
    (s : Γ(X, U.1)) (hs : ¬ IsUnit (X.presheaf.germ U.1 x hx s)) :
    s ∈ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal U := by
  rw [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro q hq
  by_contra hsq
  have hp : q ∈ U.2.fromSpec ⁻¹ᵁ X.basicOpen s := by
    rw [U.2.fromSpec_preimage_basicOpen]; exact hsq
  have hq' : U.2.fromSpec q ∈ closure ({x} : Set X) := hq
  have hsp : x ⤳ U.2.fromSpec q := specializes_iff_mem_closure.2 hq'
  have hxs : x ∈ X.basicOpen s := hsp.mem_open (X.basicOpen s).isOpen hp
  exact hs ((X.mem_basicOpen s x hx).1 hxs)

theorem maximalIdeal_le_stalkId {X : Scheme.{0}} (x : X) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤
      FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})) x := by
  intro a ha
  obtain ⟨V, hxV, f, rfl⟩ := X.presheaf.exists_germ_eq a
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxV V.isOpen
  have hle : W ≤ V := hWV
  have e : X.presheaf.germ W x hxW (X.presheaf.map (homOfLE hle).op f) = X.presheaf.germ V x hxV f :=
    X.presheaf.germ_res_apply (homOfLE hle) x hxW f
  rw [← e] at ha ⊢
  generalize X.presheaf.map (homOfLE hle).op f = g at ha ⊢
  have hu : ¬ IsUnit (X.presheaf.germ W x hxW g) :=
    mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 ha)
  have hm := mem_vanishingIdeal_closure x ⟨W, hW⟩ hxW g hu
  have h1 : Ideal.map (X.presheaf.germ W x hxW).hom
      ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal ⟨W, hW⟩) ≤
      FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})) x :=
    le_iSup₂_of_le (f := fun (U : X.affineOpens) (hx : x ∈ U.1) =>
      Ideal.map (X.presheaf.germ U.1 x hx).hom
        ((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {x})).ideal U)) ⟨W, hW⟩ hxW le_rfl
  exact h1 (Ideal.mem_map_of_mem _ hm)

theorem coheight_eq_one_of_lSncAt {X : Scheme.{0}} {r : ℕ} (z : Fin r → X) (a : Fin r)
    (h : FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) (z a)) : Order.coheight (z a) = 1 := by
  obtain ⟨hreg, n, t, e, ht, hI⟩ := h
  have ha : z a ∈ (Closeds.closure {z a} : Closeds X) := subset_closure (Set.mem_singleton _)
  have hn : 1 ≤ n := (e ⟨a, ha⟩).pos
  have hm : IsLocalRing.maximalIdeal (X.presheaf.stalk (z a)) = Ideal.span {t (e ⟨a, ha⟩)} := by
    refine le_antisymm ((maximalIdeal_le_stalkId (z a)).trans (hI ⟨a, ha⟩).le) ?_
    rw [← ht.1]
    exact Ideal.span_mono (Set.singleton_subset_iff.2 ⟨_, rfl⟩)
  have hmin : IsLocalRing.maximalIdeal (X.presheaf.stalk (z a)) ∈
      (Ideal.span {t (e ⟨a, ha⟩)}).minimalPrimes := by
    rw [← hm, Ideal.minimalPrimes_eq_subsingleton_self]
    rfl
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmin
  have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := X.presheaf.stalk (z a))
  have h2 := ringKrullDim_stalk_eq_coheight (z a)
  have h3 : (IsLocalRing.maximalIdeal (X.presheaf.stalk (z a))).height = Order.coheight (z a) :=
    WithBot.coe_eq_coe.1 (h1.trans h2)
  have h4 : ((n : ℕ∞)) = Order.coheight (z a) := WithBot.coe_eq_coe.1 (ht.2.trans h2)
  refine le_antisymm (h3 ▸ hle) ?_
  rw [← h4]
  exact_mod_cast hn

theorem exists_genericPoints : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ T : Closeds X, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → ∃ (r : ℕ) (z : Fin r → X), Function.Injective z ∧ (∀ a, Order.coheight (z a) = 1) ∧ (T : Set X) = ⋃ a, closure {z a} ∧ (∀ w : X, w ∈ T → Order.coheight w = 1 → ∃ a, w = z a) ∧ ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
  intro F _ X _ p D hp hs T hT
  haveI : QuasiCompact p := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    haveI : IsProper (PSpace.str F N) := isProper_str F N
    infer_instance
  haveI : Smooth p := SmoothOfRelativeDimension.smooth D p
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  haveI : IsNoetherian X := {}
  obtain ⟨m, C, hC, -⟩ := GlobalTheory.SncComponents.exists_compList_effCartier F X p D T hT
  have hL := GlobalTheory.SncLocal.lSncAt_of_snc' X T m C hT hC
  have hz : ∀ a, ∃ z : X, closure {z} = (C a : Set X) := fun a =>
    QuasiSober.sober (hC.1 a) (C a).isClosed
  choose z hz using hz
  have hCz : (fun a => (Closeds.closure {z a} : Closeds X)) = C :=
    funext fun a => SetLike.coe_injective (hz a)
  have hL' : ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
    rw [hCz]; exact hL
  have hco : ∀ a, Order.coheight (z a) = 1 := fun a => coheight_eq_one_of_lSncAt z a (hL' _)
  have hU : (T : Set X) = ⋃ a, closure {z a} := by
    rw [← hC.2.1]; simp only [hz]
  refine ⟨m, z, fun a b hab => hC.2.2 a b ?_, hco, hU, fun w hw hw1 => ?_, hL'⟩
  · rw [← hz, ← hz, hab]
  · have hw' : w ∈ (T : Set X) := hw
    rw [hU] at hw'
    obtain ⟨a, ha⟩ := Set.mem_iUnion.1 hw'
    have hsp : z a ⤳ w := specializes_iff_mem_closure.2 ha
    refine ⟨a, ?_⟩
    by_contra hne
    have hlt : w < z a := lt_of_le_not_ge hsp fun h =>
      hne ((show w ⤳ z a from h).antisymm hsp).eq
    have := Order.coheight_strictAnti hlt (by rw [hco a]; exact ENat.natCast_lt_top 1)
    rw [hco a, hw1] at this
    exact lt_irrefl _ this

end GlobalTheory.SncGenericPoints
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncClosedEqIUnionClosureCodimOnePointsStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.snc_closed_eq_iUnion_closure_codim_one_points : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (D : ℕ), IsProjOver p → SmoothOfRelativeDimension D p → ∀ T : Closeds X, FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal T) → ∃ (r : ℕ) (z : Fin r → X), Function.Injective z ∧ (∀ a, Order.coheight (z a) = 1) ∧ (T : Set X) = ⋃ a, closure {z a} ∧ (∀ w : X, w ∈ T → Order.coheight w = 1 → ∃ a, w = z a) ∧ ∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x := by
  first | exact @GlobalTheory.SncGenericPoints.exists_genericPoints | exact GlobalTheory.SncGenericPoints.exists_genericPoints | (intros; apply GlobalTheory.SncGenericPoints.exists_genericPoints <;> assumption)
end
end
