module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentVarUnit
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPrimitiveVectorCompactRescale
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleDescentDegreeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentClassFromIntegralStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCohomologyInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictlyHenselianLocalRingAcyclicEverySheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
public import Mathlib.Tactic.Linter.HaveILetI
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOfEtaleOfIsIndEtale
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StrictlyHenselianIsColimit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsCohomologyBijective
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassZeroOfGeometricPoints

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.class_zero_of_geometric_points : ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R], IsUnit (q : R) → ∀ (j : ℤ) (a : Ht q (sp R) 0 j), (∀ (K : Type) [Field K] [IsAlgClosed K] (f : R →+* K), pull _ (spMap f) _ 0 a = 0) → a = 0 := by
  first | (exact @GlobalTheory.EtC.GeomZero.eq_zero_of_geom) | (exact GlobalTheory.EtC.GeomZero.eq_zero_of_geom) | (intros; apply GlobalTheory.EtC.GeomZero.eq_zero_of_geom  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescentEqualizerDegreeZero

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.descent_equalizer_degree_zero : ∀ (q : ℕ) [NeZero q] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'], Algebra.IsIntegral A A' → RingHom.ker (algebraMap A A') ≤ nilradical A → IsUnit (q : A) → ∀ (j : ℤ) (b : Ht q (sp A') 0 j), pull _ (spMap (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b = pull _ (spMap (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom) _ 0 b → ∃ a : Ht q (sp A) 0 j, pull _ (spMap (algebraMap A A')) _ 0 a = b := by
  first | (exact @GlobalTheory.EtC.DescZero.desc_zero) | (exact GlobalTheory.EtC.DescZero.desc_zero) | (intros; apply GlobalTheory.EtC.DescZero.desc_zero  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaCountCompactFinite

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EtC.GmPhiNoeth

theorem coeff_laurentMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (p : LaurentPolynomial R) (n : ℤ) :
    (laurentMap f p).coeff n = f (p.coeff n) := by
  simp [laurentMap]

theorem laurentMap_id (R : Type) [CommRing R] : laurentMap (RingHom.id R) = RingHom.id _ :=
  RingHom.ext fun p => AddMonoidAlgebra.ext (Finsupp.ext fun n => by rw [coeff_laurentMap]; rfl)

def laurentFunctor : CommRingCat.{0} ⥤ CommRingCat.{0} where
  obj R := CommRingCat.of (LaurentPolynomial R)
  map f := CommRingCat.ofHom (laurentMap f.hom)
  map_id R := by
    change CommRingCat.ofHom (laurentMap (RingHom.id R)) = _
    rw [laurentMap_id]; rfl
  map_comp f g := by
    change CommRingCat.ofHom (laurentMap (g.hom.comp f.hom)) = _
    rw [GmPhiNat.laurentMap_comp]; rfl

def isColimit_laurent {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}
    (hc : IsColimit c) : IsColimit (laurentFunctor.mapCocone c) := by
  haveI : ReflectsColimitsOfShape J (forget CommRingCat.{0}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  have hc' : IsColimit ((forget CommRingCat.{0}).mapCocone c) := isColimitOfPreserves _ hc

  have hsurj : ∀ a : c.pt, ∃ j, ∃ b : D.obj j, (c.ι.app j).hom b = a := fun a =>
    Types.jointly_surjective_of_isColimit hc' a

  have hker : ∀ j (b : D.obj j), (c.ι.app j).hom b = 0 → ∃ k, ∃ f : j ⟶ k, (D.map f).hom b = 0 := by
    intro j b hb
    have h := (Types.FilteredColimit.isColimit_eq_iff' hc' b 0).1 (by
      change (c.ι.app j).hom b = (c.ι.app j).hom 0
      rw [hb, map_zero])
    obtain ⟨k, f, hf⟩ := h
    refine ⟨k, f, ?_⟩
    change (D.map f).hom b = (D.map f).hom 0 at hf
    rw [hf, map_zero]
  have hw : ∀ {j k : J} (f : j ⟶ k) (y : LaurentPolynomial (D.obj j)),
      laurentMap (c.ι.app k).hom (laurentMap (D.map f).hom y) = laurentMap (c.ι.app j).hom y := by
    intro j k f y
    rw [← RingHom.comp_apply, ← GmPhiNat.laurentMap_comp, ← CommRingCat.hom_comp, c.w f]
  refine isColimitOfReflects (forget CommRingCat.{0})
    (Types.FilteredColimit.isColimitOf _ ((forget CommRingCat.{0}).mapCocone (laurentFunctor.mapCocone c)) ?_ ?_)
  · intro (x : LaurentPolynomial c.pt)
    suffices h : ∃ j, ∃ y : LaurentPolynomial (D.obj j), laurentMap (c.ι.app j).hom y = x by
      obtain ⟨j, y, hy⟩ := h
      exact ⟨j, y, hy.symm⟩
    induction x using LaurentPolynomial.induction_on' with
    | add p p' hp hp' =>
      obtain ⟨j, y, rfl⟩ := hp
      obtain ⟨j', y', rfl⟩ := hp'
      refine ⟨IsFiltered.max j j', laurentMap (D.map (IsFiltered.leftToMax j j')).hom y +
        laurentMap (D.map (IsFiltered.rightToMax j j')).hom y', ?_⟩
      rw [map_add (f := _), hw, hw]
    | C_mul_T n a =>
      obtain ⟨j, b, rfl⟩ := hsurj a
      refine ⟨j, LaurentPolynomial.C b * LaurentPolynomial.T n, ?_⟩
      rw [map_mul, GmPhiNat.laurentMap_T, ← RingHom.comp_apply, GmPhiNat.laurentMap_C, RingHom.comp_apply]
  · intro i j (xi : LaurentPolynomial (D.obj i)) (xj : LaurentPolynomial (D.obj j)) h
    change laurentMap (c.ι.app i).hom xi = laurentMap (c.ι.app j).hom xj at h
    let m := IsFiltered.max i j
    let fi := IsFiltered.leftToMax i j
    let fj := IsFiltered.rightToMax i j
    let z : LaurentPolynomial (D.obj m) := laurentMap (D.map fi).hom xi - laurentMap (D.map fj).hom xj
    have hz : laurentMap (c.ι.app m).hom z = 0 := by
      simp only [z, map_sub, hw, h, sub_self]

    have hfin : ∀ s : Finset ℤ, ∃ k, ∃ h : m ⟶ k, ∀ n ∈ s, (D.map h).hom (z.coeff n) = 0 := by
      intro s
      classical
      induction s using Finset.induction_on with
      | empty => exact ⟨m, 𝟙 m, fun n hn => absurd hn (Finset.notMem_empty n)⟩
      | insert n s _ ih =>
        obtain ⟨k₁, h₁, hk₁⟩ := ih
        have hn : (c.ι.app m).hom (z.coeff n) = 0 := by
          rw [← coeff_laurentMap, hz]; rfl
        obtain ⟨k₂, h₂, hk₂⟩ := hker m _ hn
        obtain ⟨k, g₁, g₂, hg⟩ := IsFiltered.span h₁ h₂
        refine ⟨k, h₁ ≫ g₁, fun n' hn' => ?_⟩
        rcases Finset.mem_insert.1 hn' with rfl | hn'
        · rw [hg, D.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hk₂, map_zero]
        · rw [D.map_comp, CommRingCat.hom_comp, RingHom.comp_apply, hk₁ n' hn', map_zero]
    obtain ⟨k, hmk, hk⟩ := hfin z.coeff.support
    have hz0 : laurentMap (D.map hmk).hom z = 0 := by
      refine AddMonoidAlgebra.ext (Finsupp.ext fun n => ?_)
      rw [coeff_laurentMap]
      by_cases hn : n ∈ z.coeff.support
      · exact hk n hn
      · rw [Finsupp.notMem_support_iff.1 hn, map_zero]; rfl
    refine ⟨k, fi ≫ hmk, fj ≫ hmk, ?_⟩
    change laurentMap (D.map (fi ≫ hmk)).hom xi = laurentMap (D.map (fj ≫ hmk)).hom xj
    rw [D.map_comp, D.map_comp, CommRingCat.hom_comp, CommRingCat.hom_comp, GmPhiNat.laurentMap_comp,
      GmPhiNat.laurentMap_comp, RingHom.comp_apply, RingHom.comp_apply, ← sub_eq_zero, ← map_sub]
    exact hz0

end GlobalTheory.EtC.GmPhiNoeth


open GlobalTheory.EtC.GmPhiNoeth in
theorem GlobalTheory.EtC.gmPhi_surjective_of_noetherian : ∀ (q : ℕ) [NeZero q],
    (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
      Function.Surjective (gmPhi q A i)) →
    ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i) := by
  intro q _ hN A _ hSH hq i x
  obtain ⟨hH, hsep⟩ := hSH
  obtain ⟨J, _, _, D, ι, hc, hl, hst, hqj, -, -⟩ :=
    GlobalTheory.SHColim.strictlyHenselian_isColimit q A ⟨hH, hsep⟩ hq
  have hqL : IsUnit (q : LaurentPolynomial A) := by
    simpa using hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)
  obtain ⟨j, y, hy⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (D ⋙ laurentFunctor) _ (isColimit_laurent hc) 1 i).1 x hqL
  obtain ⟨B, _, _, s, hs⟩ := hst j
  haveI := hl j
  haveI : IsNoetherianRing (D.obj j) := GlobalTheory.StalkNoeth.isNoetherianRing_of_isStalk B (D.obj j) s hs
  obtain ⟨b, hb⟩ := hN (D.obj j) hs.1 (hqj j) i y
  have hn := gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q (A := D.obj j) (B := A) (ι.app j).hom (hqj j) i b
  rw [hb] at hn
  exact ⟨_, hn.symm.trans hy⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveOfNoetherianCase

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

theorem _root_.GlobalTheory.T.surjective_of_noetherian_case : ∀ (q : ℕ) [NeZero q], (∀ (A : Type) [CommRing A] [IsNoetherianRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i)) → ∀ (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Surjective (gmPhi q A i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_surjective_of_noetherian) | (exact GlobalTheory.EtC.gmPhi_surjective_of_noetherian) | (intros; apply GlobalTheory.EtC.gmPhi_surjective_of_noetherian  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenselia

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.EtC.GmPhiBij

theorem inj (q : ℕ) [NeZero q] (R : Type) [CommRing R] (hq : IsUnit (q : R)) (i : ℤ) : Function.Injective (gmPhi q R i) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  refine GlobalTheory.T.class_zero_of_geometric_points q R hq (i - 1) a fun K _ _ f => ?_
  have hqK : IsUnit (q : K) := by simpa using hq.map f
  have hK : AIC K := fun p _ hd => IsAlgClosed.exists_root p (Polynomial.natDegree_pos_iff_degree_pos.mp hd).ne'
  apply (GlobalTheory.T.units_cohomology_bijective q K hK hqK i).1
  rw [map_zero, ← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q f hq, ha, map_zero]

theorem surj_noeth (q : ℕ) [NeZero q] (A : Type) [CommRing A] [IsNoetherianRing A] (hA : SH A) (hq : IsUnit (q : A)) (i : ℤ) :
    Function.Surjective (gmPhi q A i) := by
  intro x
  obtain ⟨A', _, _, hint, hker, a', ha'⟩ := GlobalTheory.T.laurent_class_from_integral q A hA hq i x
  have hq' : IsUnit (q : A') := by simpa using hq.map (algebraMap A A')
  set L := (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A').toRingHom with hLdef
  set R := (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A').toRingHom with hRdef
  have hLR : L.comp (algebraMap A A') = R.comp (algebraMap A A') := by
    refine RingHom.ext fun a => ?_
    change (Algebra.TensorProduct.includeLeft : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a) =
      (Algebra.TensorProduct.includeRight : A' →ₐ[A] A' ⊗[A] A') (algebraMap A A' a)
    rw [AlgHom.commutes, AlgHom.commutes]
  have hq2 : IsUnit (q : A' ⊗[A] A') := by simpa using hq'.map L
  have heq : pull _ (spMap L) _ 0 a' = pull _ (spMap R) _ 0 a' := by
    apply inj q _ hq2 i
    rw [← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q L hq', ← gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q R hq', ← ha', ← GmPhiNat.pull_spMap_comp,
      ← GmPhiNat.pull_spMap_comp, ← GmPhiNat.laurentMap_comp, ← GmPhiNat.laurentMap_comp, hLR]
  obtain ⟨a, ha⟩ := GlobalTheory.T.descent_equalizer_degree_zero q A A' hint hker hq (i - 1) a' heq
  refine ⟨a, ?_⟩
  have hsub : gmPhi q A i a - x = 0 := by
    apply GlobalTheory.T.laurent_cohomology_injective q A A' hint hker hq (fun j => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) A hA (tw q j) 1 one_pos) i
    rw [map_sub, gmPhi_nat GlobalTheory.T.cup_chern_kummer_pullback_naturality q (algebraMap A A') hq, ha, ha', sub_self]
  exact sub_eq_zero.mp hsub

end GmPhiBij

theorem gmPhi_bijective : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ,
    Function.Bijective (gmPhi q A i) := by
  intro q _ A _ hA hq i
  exact ⟨GmPhiBij.inj q A hq i, GlobalTheory.T.surjective_of_noetherian_case q (fun B _ _ hB hqB j => GmPhiBij.surj_noeth q B hB hqB j) A hA hq i⟩

end GlobalTheory.EtC

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentKummerCupProductBijectiveStrictlyHenseliaStatement

section

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Bijective (gmPhi q A i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_bijective) | (exact GlobalTheory.EtC.gmPhi_bijective) | (intros; apply GlobalTheory.EtC.gmPhi_bijective  <;> assumption)
end
end
