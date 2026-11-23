module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorIntegralModelNonemptyStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOneTrivialOnAxis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSiegelObjectPolarisationKernelKilled
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionOfBirigidifiedBundleTrivialOnSliceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.NormNum.Parity
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveWeightSection

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

noncomputable section

namespace GlobalTheory.UPel.HT.GenKer

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R' : Type} [CommRing R'] [Algebra ℚ R'] {S : Scheme.{0}}

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (u : Sp B ⟶ Sp A) : ∃ β : A →+* B, u = spMap β :=
  ⟨(Spec.preimage u).hom, by simp [spMap]⟩

theorem charZero_of_hom {k : Type} [Field k] (β : R' →+* k) : CharZero k :=
  charZero_of_injective_ringHom (β.comp (algebraMap ℚ R')).injective

theorem pow_eq_one_geom {gb : GBase D.toG R'} {N : ℕ} {t : S ⟶ Sp R'} (o : GObj gb N t) (e : ℕ)
    (hEF : ∀ f : D.La →ₗ[ℤ] ℤ, ∃ x, D.EF x = e • f) (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S)
    (g : Over.mk x₀ ⟶ o.A) (M : ℕ) (hM : 0 < M) (hn : g ^ M = 1)
    (hg : ∃ u : (o.P.pull (lift (snd o.A (Over.mk x₀) ≫ g) (fst o.A (Over.mk x₀))).left).Gen, u.IsGen) :
    g ^ e = 1 := by
  obtain ⟨β, hβ⟩ := exists_spMap (x₀ ≫ t)
  haveI := charZero_of_hom β
  obtain ⟨I, -⟩ := o.geom k x₀ β hβ
  obtain ⟨y, hy⟩ : ∃ y : D.La, I.ev M y = g := (I.onto M hM g).1 hn
  have key : ∀ z : D.La, (M : ℤ) ∣ D.EF y z := by
    intro z
    have hm : 0 < M * 2 := by omega
    have ha : I.ev (M * 2) y ^ 2 = g := by rw [I.tower M 2 hM two_pos y, hy]
    have hc := GlobalTheory.WeilSqKer.weilIs_eq_one S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample k x₀ (M * 2)
      (Nat.cast_ne_zero.2 hm.ne') _ _ ((I.onto _ hm _).2 ⟨y, rfl⟩) ((I.onto _ hm _).2 ⟨z, rfl⟩) (ha ▸ hg) _
      (I.isom _ hm y z)
    have h1 : I.ζ (M * 2) ^ (2 * D.EF y z) = 1 :=
      GlobalTheory.Ex.Specialise.unitOn_bijective.1 (hc.trans (map_one _).symm)
    have h3 := ((I.ζ_prim (M * 2) hm).zpow_eq_one_iff_dvd _).1 h1
    have h4 : (M : ℤ) * 2 ∣ D.EF y z * 2 := by
      rw [mul_comm (D.EF y z)]; exact_mod_cast h3
    exact (mul_dvd_mul_iff_right (by norm_num : (2 : ℤ) ≠ 0)).1 h4
  let f : D.La →ₗ[ℤ] ℤ :=
    { toFun := fun z => D.EF y z / M
      map_add' := fun u v => by
        rw [map_add (f := _), Int.add_ediv_of_dvd_left (key u)]
      map_smul' := fun r u => by
        rw [map_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, Int.mul_ediv_assoc _ (key u)] }
  have hf : ∀ z, (M : ℤ) * f z = D.EF y z := fun z => Int.mul_ediv_cancel' (key z)
  obtain ⟨w, hw⟩ := hEF f
  have hyw : e • y = M • w := by
    apply D.nondeg
    ext z
    have hwz : D.EF w z = e • f z := by rw [hw]; rfl
    simp only [map_nsmul, LinearMap.smul_apply, hwz, nsmul_eq_mul]
    rw [← hf z]; ring
  calc g ^ e = I.ev M y ^ e := by rw [hy]
    _ = I.ev M (e • y) := (KerBy.ev_nsmul (La := D.La) _ (I.add M) e y).symm
    _ = 1 := (I.ker M hM _).2 ⟨w, hyw⟩

theorem exists_coprime_pow_eq_one (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R']
    (gb : GBase D.toG R') (N : ℕ) (_hN : 3 ≤ N) (S : Scheme.{0}) (t : S ⟶ Sp R') (o : GObj gb N t) :
    ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ u : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, u.IsGen) → x ^ e = 1 := by
  obtain ⟨e, he, hEF⟩ := D.perfP
  refine ⟨e, he, fun T x hx => ?_⟩
  apply Over.OverMorphism.ext
  refine T.left.affineCover.hom_ext _ _ fun i => ?_
  obtain ⟨B, ⟨u⟩⟩ : ∃ B : CommRingCat.{0}, Nonempty (T.left.affineCover.X i ≅ Spec B) :=
    ⟨_, ⟨(T.left.affineCover.X i).isoSpec⟩⟩
  rw [← cancel_epi u.inv]
  let a : Sp B ⟶ T.left := u.inv ≫ T.left.affineCover.f i
  let a' : Over.mk (a ≫ T.hom) ⟶ T := Over.homMk a rfl
  have hx' := KerBy.gen_comp S o.A o.P T _ a' x hx
  obtain ⟨M, hM, hxM⟩ := GlobalTheory.T.isTorsion_of_birigidified_bundle_trivial_on_slice S o.A o.P o.ab o.isLB o.rig₁ o.rig₂ o.symm o.ample B (a ≫ T.hom) _ hx'
  have hu : IsUnit ((M : ℕ) : Γ(S, ⊤)) := by
    have h0 : IsUnit ((M : ℕ) : R') := by
      simpa using (IsUnit.mk0 (M : ℚ) (Nat.cast_ne_zero.2 hM.ne')).map (algebraMap ℚ R')
    simpa using (h0.map (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom).map t.appTop.hom
  have h := GlobalTheory.TorsGeomPow.pow_eq_one_of_geometric_points S o.A o.ab M hu _ _ hxM e fun k _ _ ξ =>
    pow_eq_one_geom o e hEF k _ _ M hM (by rw [← MonObj.comp_pow, hxM, MonObj.comp_one])
      (KerBy.gen_comp S o.A o.P _ _ _ _ hx')
  have h' : a' ≫ x ^ e = a' ≫ 1 := by rw [MonObj.comp_pow, h, MonObj.comp_one]
  have h'' : a ≫ (x ^ e).left = a ≫ (1 : T ⟶ o.A).left := congrArg (fun z => z.left) h'
  exact (Category.assoc _ _ _).symm.trans (h''.trans (Category.assoc _ _ _))

end GlobalTheory.UPel.HT.GenKer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionOfGeneratingSection

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

theorem _root_.GlobalTheory.T.torsion_of_generating_section : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [Algebra ℚ R] (gb : GBase D.toG R) (N : ℕ), 3 ≤ N → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GObj gb N s), ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | (exact @GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one) | (exact GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one) | (intros; apply GlobalTheory.UPel.HT.GenKer.exists_coprime_pow_eq_one <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharZeroGenericModelNonempty

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}}

def GBase.toBaseAt (gb : GBase D.toG R) : Base D R where
  unit k hk := by
    have hk0 : (k : ℚ) ≠ 0 := by
      rintro h
      have : k = 0 := by exact_mod_cast h
      subst this
      exact (Fact.out : p.Prime).one_lt.ne' (by simpa using hk)
    simpa using (IsUnit.mk0 _ hk0).map (algebraMap ℚ R)
  ρ := gb.ρ
  ρ_root := gb.ρ_root
  t := gb.t
  t_ω := gb.t_ω
  comax := gb.comax
  apart i j _ k _ _ β := by
    exfalso
    have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have h := ((IsUnit.mk0 _ hp).map (algebraMap ℚ R)).map β
    simp at h

theorem fullTate (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) {s : S ⟶ Sp R} (o : Obj gb.toBaseAt N s)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : R →+* k) (h : x ≫ s = spMap β) :
    ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
        (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  haveI : CharZero k := by
    letI : Algebra ℚ k := (β.comp (algebraMap ℚ R)).toAlgebra
    exact algebraRat.charZero k
  exact GlobalTheory.T.exists_tate_module_iso p D R gb.toBaseAt N h3 hN S s o k x β h

theorem kerPrimeTo {gb : GBase D.toG R} {N : ℕ} (h3 : 3 ≤ N) {s : S ⟶ Sp R} (o : GObj gb N s) :
    ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over S) (x : T ⟶ o.A),
      (∃ t : (o.P.pull (lift (snd o.A T ≫ x) (fst o.A T)).left).Gen, t.IsGen) → x ^ e = 1 :=
  GlobalTheory.T.torsion_of_generating_section p D R gb N h3 S s o

def GTateIso.toPrimeTo {k : Type} [Field k] {Q : Type} [Group Q] {act : D.O → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso D.toG k Q act e) : TateIsoO D k Q act e where
  ζ := I.ζ
  ζ_prim n h _ := I.ζ_prim n h
  ζ_pow n m h h' _ := I.ζ_pow n m h h'
  ev := I.ev
  add := I.add
  lin := I.lin
  ker n h _ := I.ker n h
  onto n h _ := I.onto n h
  tower n m h h' _ := I.tower n m h h'
  isom n h _ := I.isom n h

def GBase.ofObjAt (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) {s : S ⟶ Sp R}
    (o : Obj gb.toBaseAt N s) : GObj gb N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom := fullTate gb h3 hN o

def GObj.toObjAt {gb : GBase D.toG R} {N : ℕ} {s : S ⟶ Sp R} (o : GObj gb N s) (h3 : 3 ≤ N) :
    Obj gb.toBaseAt N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := kerPrimeTo h3 o
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom k _ _ x β h := by
    obtain ⟨I, hI⟩ := o.geom k x β h
    exact ⟨I.toPrimeTo, hI⟩

def GBase.genModelOf (gb : GBase D.toG R) {N : ℕ} (h3 : 3 ≤ N) (hN : N.Coprime p) (M : Model gb.toBaseAt N) :
    GenModel gb N where
  X := M.X
  s := M.s
  univ := gb.ofObjAt h3 hN M.univ
  rep S s' o := by
    obtain ⟨f, ⟨hf, ⟨m⟩⟩, hu⟩ := M.rep S s' (o.toObjAt h3)
    refine ⟨f, ⟨hf, ⟨⟨m.φ, m.φ₂, m.cart, m.sq, m.act, m.pol, m.eta⟩⟩⟩, ?_⟩
    rintro g ⟨hg, ⟨n⟩⟩
    exact hu g ⟨hg, ⟨⟨n.φ, n.φ₂, n.cart, n.sq, n.act, n.pol, n.eta⟩⟩⟩

theorem genModel_nonempty (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R']
    [IsNoetherianRing R'] (gb : GBase D.toG R') (N : ℕ) (h3 : 3 ≤ N) (hN : N.Coprime p) :
    Nonempty (GenModel gb N) := by
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R' gb.toBaseAt N h3 hN
  exact ⟨gb.genModelOf h3 hN M⟩

end GlobalTheory.UPel.HT.Gen
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCharZeroGenericModelNonemptyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen

theorem _root_.GlobalTheory.T.unitaryCharZeroGenericModel_nonempty : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R' : Type) [CommRing R'] [Algebra ℚ R'] [IsNoetherianRing R'] (gb : GBase D.toG R') (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (GenModel gb N) := by
  first | (exact @GlobalTheory.UPel.HT.Gen.genModel_nonempty) | (exact GlobalTheory.UPel.HT.Gen.genModel_nonempty) | (intros; apply GlobalTheory.UPel.HT.Gen.genModel_nonempty  <;> assumption)
end
end
