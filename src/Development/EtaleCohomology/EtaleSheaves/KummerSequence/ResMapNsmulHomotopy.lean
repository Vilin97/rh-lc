module

public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.KummerH0Surjection
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuInjPf
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.EtaleCohomology.TateTwists.EtaleLocalPropertyBasicClosureProperties
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuMapPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPf
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPrimPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafUnitRootPf
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.TwLocGenPfSec
import Mathlib.Tactic.Linter.HaveILetI
public import Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumSecSurjPf

-- Source module: Development.EtaleCohomology.EtaleSheaves.KummerSequence.GmSepPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.GmSepPf

def ev (V : Scheme.{0}) (a : Γ(V, ⊤)) : CommRingCat.of (Polynomial ℤ) ⟶ Γ(V, ⊤) :=
  CommRingCat.ofHom (Polynomial.eval₂RingHom (Int.castRingHom _) a)

def lineMap (V : Scheme.{0}) (a : Γ(V, ⊤)) : V ⟶ Spec (CommRingCat.of (Polynomial ℤ)) :=
  ΓSpec.adjunction.homEquiv V (op (CommRingCat.of (Polynomial ℤ))) (ev V a).op

theorem lineMap_inj (V : Scheme.{0}) (a b : Γ(V, ⊤)) (h : lineMap V a = lineMap V b) : a = b := by
  have h1 := (ΓSpec.adjunction.homEquiv _ _).injective h
  have h2 := congrArg (fun f => f.hom Polynomial.X) (Quiver.Hom.op_inj h1)
  simpa [ev] using h2

theorem ev_comp {W V : Scheme.{0}} (g : W ⟶ V) (a : Γ(V, ⊤)) : ev V a ≫ g.appTop = ev W (g.appTop a) := by
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro n; simp [ev]
  · simp [ev]

theorem lineMap_nat {W V : Scheme.{0}} (g : W ⟶ V) (a : Γ(V, ⊤)) :
    g ≫ lineMap V a = lineMap W (g.appTop a) := by
  unfold lineMap
  refine (ΓSpec.adjunction.homEquiv_naturality_left g (ev V a).op).symm.trans ?_
  congr 1
  apply Quiver.Hom.unop_inj
  exact ev_comp g a

theorem gamma_sep (V : Scheme.{0}) (S : Sieve V) (hS : S ∈ Scheme.etaleTopology V) (a b : Γ(V, ⊤))
    (h : ∀ (W : Scheme.{0}) (g : W ⟶ V), S.arrows g → g.appTop a = g.appTop b) : a = b := by
  have : Scheme.etaleTopology.{0}.Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le Scheme.etaleTopology_le_proetaleTopology
  have hsh := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (J := Scheme.etaleTopology.{0})
    (yoneda.obj (Spec (CommRingCat.of (Polynomial ℤ))))
  apply lineMap_inj
  refine (hsh S hS).isSeparatedFor.ext (fun W g hg => ?_)
  change g ≫ lineMap V a = g ≫ lineMap V b
  rw [lineMap_nat, lineMap_nat, h W g hg]

theorem gmSep : LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.GmSep := by
  intro V u h
  have h0 : ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op V)).hom (ULift.up (Additive.ofMul u))
      = ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)).app (op V)).hom 0 := by
    rw [map_zero]; exact h
  have hm := Presheaf.equalizerSieve_mem Scheme.etaleTopology
    (toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ unitsF)) (X := op V)
    (ULift.up (Additive.ofMul u) : (Scheme.Γ ⋙ unitsF).obj (op V)) 0 h0
  apply Units.ext
  refine gamma_sep V _ hm u.1 (1 : Γ(V, ⊤)) (fun W g hg => ?_)
  have h1 := congrArg (fun z : (Scheme.Γ ⋙ unitsF).obj (op W) => ((Additive.toMul z.down : (Γ(W, ⊤))ˣ) : Γ(W, ⊤))) hg
  exact h1

theorem GmSep_of : LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.GmSep := gmSep

end LateralTheory.E.H2CurveOrder.GmSepPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuInjPfGlue

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC Polynomial

namespace LateralTheory.E.H2CurveOrder.LeafKumMuInjPfGlue
open LateralTheory.E.H2CurveOrder.LeafKumMuInjPf

theorem cycPow : CycPow := by
  intro q A _ ζ
  obtain ⟨hq, hz⟩ := ζ.2
  rcases Nat.eq_zero_or_pos q with rfl | hq0
  · have : Subsingleton A := by
      simp at hz
      exact subsingleton_of_zero_eq_one hz.symm
    exact ⟨1, Subsingleton.elim _ _, fun _ _ => Or.inr this⟩
  have hqz : ζ.1 ^ q = 1 := by
    obtain ⟨G, hG⟩ := cyclotomic.dvd_X_pow_sub_one q ℤ
    have := congrArg (aeval ζ.1) hG
    simp [hz] at this
    exact sub_eq_zero.1 this
  have h1 : ζ.1 * ζ.1 ^ (q - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel hq0]; exact hqz
  have hu : IsUnit ζ.1 := ⟨⟨ζ.1, ζ.1 ^ (q - 1), h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine ⟨hu.unit, rfl, fun c hc => ?_⟩
  have hc' : ζ.1 ^ c = 1 := by simpa using congrArg Units.val hc
  set d := Nat.gcd c q with hd
  have hdz : ζ.1 ^ d = 1 := pow_gcd_eq_one.2 ⟨hc', hqz⟩
  by_cases hdq : d = q
  · left; rw [← hdq]; exact Nat.gcd_dvd_left c q
  right
  obtain ⟨G, hG⟩ := X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℤ (Nat.mem_properDivisors.2 ⟨Nat.gcd_dvd_right c q, lt_of_le_of_ne (Nat.le_of_dvd hq0 (Nat.gcd_dvd_right c q)) hdq⟩)
  have hG' := congrArg (Polynomial.map (Int.castRingHom A)) hG
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
    map_cyclotomic] at hG'
  have r1 : (X - C ζ.1) ∣ (X ^ d - 1 : A[X]) := dvd_iff_isRoot.2 (by simp [hdz])
  have r2 : (X - C ζ.1) ∣ cyclotomic q A := dvd_iff_isRoot.2 (by
    have := hz
    rwa [aeval_def, eval₂_eq_eval_map, map_cyclotomic] at this)
  obtain ⟨a, ha⟩ := r1
  obtain ⟨b, hb⟩ := r2
  have hE : (X ^ q - 1 : A[X]) = (X - C ζ.1) ^ 2 * (a * b * G.map (Int.castRingHom A)) := by
    rw [hG', ha, hb]; ring
  have hD := congrArg (fun p => eval ζ.1 (derivative p)) hE
  simp [derivative_mul, derivative_pow] at hD
  have hu' : IsUnit ((q : A) * ζ.1 ^ (q - 1)) := hq.mul (hu.pow _)
  have h0 : (q : A) * ζ.1 ^ (q - 1) = 0 := by simpa using hD
  rw [h0] at hu'
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp hu')

theorem emptySec : EmptySec := by
  intro R _ F V hs y
  have : IsEmpty V := by
    refine ⟨fun x => ?_⟩
    have h1 : (1 : V.presheaf.stalk x) = 0 := by
      rw [← map_one (V.presheaf.germ ⊤ x trivial).hom, Subsingleton.elim (1 : Γ(V, ⊤)) 0, map_zero]
    exact one_ne_zero h1
  exact LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.shfSep R F V y (LateralTheory.EtaleFoundations.LocBasicPf.loc_empty V _)

theorem LeafKumMuInj_of (hL : TwLocGen) (hG : GmSep) : LateralTheory.E.H2CurveOrder.LeafKumMuUnitsPf.LeafKumMuInj :=
  LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.LeafKumMuInj_of hL hG cycPow emptySec

end LateralTheory.E.H2CurveOrder.LeafKumMuInjPfGlue
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.KummerSequence.LeafKumMuSurjPowPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4 LateralTheory.E.H2CurveOrder.LeafKumMuSurjPf

namespace LateralTheory.E.H2CurveOrder.LeafKumMuSurjPowPf

def powCof {A : Type*} [CommRing A] (u v : A) (q : ℕ) : A := ∑ i ∈ Finset.range q, u ^ i * v ^ (q - 1 - i)

theorem powCof_mul {A : Type*} [CommRing A] (u v : A) (q : ℕ) : powCof u v q * (u - v) = u ^ q - v ^ q :=
  geom_sum₂_mul u v q

theorem powCof_map {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (u v : A) (q : ℕ) :
    φ (powCof u v q) = powCof (φ u) (φ v) q := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [powCof, map_sum, map_mul, map_pow]

theorem powCof_self {A : Type*} [CommRing A] (v : A) (q : ℕ) : powCof v v q = (q : A) * v ^ (q - 1) := by
  unfold powCof
  rw [Finset.sum_congr rfl (g := fun _ => v ^ (q - 1))]
  · simp
  · intro i hi
    rw [← pow_add]; congr 1; have := Finset.mem_range.1 hi; omega

theorem field_step {K : Type} [Field K] (q : ℕ) [NeZero q] (hq : (q : K) ≠ 0) (z w : K)
    (hz : Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0) (hw : w ^ q = 1) :
    ∃ a : Fin q, powCof w (z ^ (a : ℕ)) q ≠ 0 := by
  have : NeZero (q : K) := ⟨hq⟩
  have hroot : Polynomial.IsRoot (Polynomial.cyclotomic q K) z := by
    rw [← Polynomial.map_cyclotomic_int, Polynomial.IsRoot, Polynomial.eval_map]
    rw [Polynomial.aeval_def, algebraMap_int_eq] at hz
    exact hz
  have hp : IsPrimitiveRoot z q := (Polynomial.isRoot_cyclotomic_iff).1 hroot
  obtain ⟨i, hi, hzi⟩ := hp.eq_pow_of_pow_eq_one hw
  refine ⟨⟨i, hi⟩, ?_⟩
  rw [← hzi, powCof_self]
  have hz0 : z ≠ 0 := fun h => by
    have := hp.pow_eq_one; rw [h, zero_pow (NeZero.ne q)] at this; exact zero_ne_one this
  exact mul_ne_zero hq (pow_ne_zero _ (pow_ne_zero _ hz0))

theorem isUnit_of_basicOpen_top {V : Scheme.{0}} (t : Γ(V, ⊤)) (h : V.basicOpen t = ⊤) : IsUnit t := by
  apply V.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  have hx' : x ∈ V.basicOpen t := by rw [h]; trivial
  exact (V.mem_basicOpen_top t x).1 hx'

theorem pow_pf : LeafKumMuSurjPow := by
  intro q _ U ζ u hu
  let s : Fin q → Γ(U, ⊤) := fun a => powCof (u : Γ(U, ⊤)) (ζ.1 ^ (a : ℕ)) q
  have hcov : TopologicalSpace.IsOpenCover (fun a => U.basicOpen (s a)) := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    rintro x -
    rw [TopologicalSpace.Opens.mem_iSup]
    let φ := (U.Γevaluation x).hom
    have hq : (q : U.residueField x) ≠ 0 := by
      have := ζ.2.1.map φ
      simpa using this.ne_zero
    have hz : Polynomial.aeval (φ ζ.1) (Polynomial.cyclotomic q ℤ) = 0 := by
      have := Polynomial.aeval_algHom_apply φ.toIntAlgHom ζ.1 (Polynomial.cyclotomic q ℤ)
      rw [ζ.2.2, map_zero] at this
      exact this
    have hw : (φ (u : Γ(U, ⊤))) ^ q = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, map_one]
    obtain ⟨a, ha⟩ := field_step q hq _ _ hz hw
    refine ⟨a, ?_⟩
    rw [← Scheme.evaluation_ne_zero_iff_mem_basicOpen (X := U) (U := ⊤) x trivial]
    show φ (s a) ≠ 0
    simp only [s]
    rw [powCof_map, map_pow]
    exact ha
  let 𝒰 := U.openCoverOfIsOpenCover _ hcov
  refine ⟨Sieve.ofArrows 𝒰.X 𝒰.f,
    Scheme.zariskiTopology_le_etaleTopology _ (Scheme.Cover.mem_grothendieckTopology 𝒰), ?_⟩
  intro V f hf
  obtain ⟨a', g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hf
  let a : Fin q := a'
  refine ⟨(a : ℕ), ?_⟩
  have hunit : IsUnit ((g ≫ 𝒰.f a).appTop (s a)) := by
    apply isUnit_of_basicOpen_top
    rw [← Scheme.preimage_basicOpen_top, eq_top_iff]
    intro x _
    show (U.basicOpen (s a)).ι.base (g.base x) ∈ U.basicOpen (s a)
    exact (g.base x).2
  have hzero : s a * ((u : Γ(U, ⊤)) - ζ.1 ^ (a : ℕ)) = 0 := by
    simp only [s]
    rw [powCof_mul, ← Units.val_pow_eq_pow_val, hu, Units.val_one, ← pow_mul, mul_comm, pow_mul,
      prim_pow_q ζ, one_pow, sub_self]
  have key : ∀ ψ : Γ(U, ⊤) →+* Γ(V, ⊤), IsUnit (ψ (s a)) → ψ u = ψ ζ.1 ^ (a : ℕ) := fun ψ h => by
    have h2 := congrArg ψ hzero
    rw [map_mul, map_zero] at h2
    rw [← map_pow]
    exact sub_eq_zero.1 ((h.mul_right_eq_zero).1 (by rw [← map_sub]; exact h2))
  apply key
  exact hunit

theorem LeafKumMuSurjPow_of : LeafKumMuSurjPow := pow_pf

end LateralTheory.E.H2CurveOrder.LeafKumMuSurjPowPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.KummerSequence.TwLocGenPf

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.H2CurveOrder.TwLocGenPf
open LateralTheory.E.H2CurveOrder.TwLocGenPfSec

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (h : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (h ≫ g) y = Sec.res h (Sec.res g y) := by
  simp only [Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

theorem TwLocGen_of : LateralTheory.E.H2CurveOrder.LeafKumMuInjPf.TwLocGen := by
  intro q _ U y
  have hT := TwSecLoc_of_alg AlgPow_of
  refine loc_bind (loc_surj (twF q 1) U y) ?_
  rintro V g ⟨x, hx⟩
  by_cases hP : Nonempty (Prim q Γ(V, ⊤))
  · obtain ⟨ζ⟩ := hP
    refine loc_mono (hT q 1 V ζ (Sec.res g y)) ?_
    rintro W h ⟨c, hc⟩
    right
    exact ⟨ζ.map h.appTop.hom, c, by rw [res_comp]; exact hc⟩
  · have hx0 : x = 0 := by
      haveI : IsEmpty (Prim q Γ(V, ⊤)) := not_nonempty_iff.mp hP
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have : z = 0 := Subsingleton.elim _ _
      rw [this]; rfl
    refine loc_mono (loc_true V) ?_
    intro W h _
    left
    have hx' : Sec.res (F := tw q 1) g y = ofRings.sec (twF q 1) V x := hx
    rw [res_comp, hx', hx0]
    have h0 : ofRings.sec (twF q 1) V 0 = 0 :=
      map_zero ((toSheafify Scheme.etaleTopology (Scheme.Γ ⋙ twF q 1)).app (op V)).hom
    rw [h0]
    exact map_zero _

end LateralTheory.E.H2CurveOrder.TwLocGenPf
end
end
end

-- Source module: Development.EtaleCohomology.EtaleSheaves.KummerSequence.ResMapNsmulHomotopy

section

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CochainComplex CochainComplex.HomComplex

namespace LateralTheory.E.H2CurveOrder

open LateralTheory.E.E4 LeafKumSeqPf KummerH0Surjection

theorem muUnits : LeafKumMuPf.LeafKumMuUnits := by
  have hI := LeafKumMuInjPfGlue.LeafKumMuInj_of TwLocGenPf.TwLocGen_of GmSepPf.GmSep_of
  exact LeafKumMuUnitsPf.LeafKumMuUnits_of LeafKumMuMapPf.LeafKumMuMap_of hI
    (LeafKumMuSurjPf.etale_mu_twist_sections_surj_of_prim_root_pow_inj LeafKumMuSurjPrimPf.LeafKumMuSurjPrim_of
      LeafKumMuSurjPowPf.LeafKumMuSurjPow_of hI)

theorem kumSecSurj : LeafKumSecSurj := LeafKumSecSurjPf.LeafKumSecSurj_of LeafUnitRootPf.LeafUnitRoot_of

end LateralTheory.E.H2CurveOrder

end
end
end
