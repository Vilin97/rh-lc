module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondOntoStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelKernelUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleTorsionSubgroupUniversal
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFiniteFlat
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
public import Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalModuleActionLaws
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondInjectiveGeom

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem clopenCond_injective_geom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r) := by
  intro p _ D R _ b N w0 r hw S _ s o K κ hKf hKe hκ hrep Z et hZf hZe hadd hlin hvan
  have hkill : ∀ y, ∀ c ∈ w0 ^ r, et y ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro y c hc
    rw [← hlin]
    exact hvan _ (Submodule.subset_span ⟨c, hc, y, rfl⟩)
  have h0 : et 0 = 1 := hvan 0 (Submodule.zero_mem _)
  have hE : ∀ y, GlobalTheory.LevCover.ClopenCond Z fun _ h => h ≫ et y = 1 := by
    intro y
    obtain ⟨u, hu, -⟩ := hrep Z (et y) (hkill y)
    obtain ⟨u0, hu0, -⟩ := hrep Z (et 0) (hkill 0)
    refine (GlobalTheory.LevCover.clopenCond_eq u u0).congr fun T' h => ⟨fun H => ?_, fun H => ?_⟩
    · have hk : ∀ c ∈ w0 ^ r, (h ≫ et y) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
        rw [Category.assoc, hkill y c hc, MonObj.comp_one]
      refine (hrep T' (h ≫ et y) hk).unique ?_ ?_
      · rw [Category.assoc, hu]
      · rw [Category.assoc, hu0, h0, MonObj.comp_one, H]
    · rw [← hu, ← Category.assoc, H, Category.assoc, hu0, h0, MonObj.comp_one]
  have hP : ∀ y, GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k]
      (x : Sp k ⟶ T'.left),
      (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r := by
    intro y
    by_cases hy : y ∈ wSub D w0 r
    · exact ⟨⊤, isClosed_univ, fun T' h => ⟨fun _ => by simp, fun _ _ _ _ _ _ => hy⟩⟩
    · obtain ⟨U, hU, H⟩ := hE y
      refine ⟨⟨(U : Set Z.left)ᶜ, hU.isOpen_compl⟩, U.isOpen.isClosed_compl, fun T' h =>
        ⟨fun P => ?_, fun hsub k _ _ x hx => ?_⟩⟩
      · rintro _ ⟨t, rfl⟩ ht
        obtain ⟨k, _, _, a, ha⟩ := FinEt.exists_algClosed_point T'.left t
        apply hy
        refine P k a ?_
        rw [← Category.assoc]
        refine (H _ _).2 ?_
        rintro _ ⟨q, rfl⟩
        have haq : a q = t := (ha ▸ Set.mem_range_self q : a q ∈ ({t} : Set T'.left))
        simp only [Over.comp_left, Over.homMk_left, Scheme.Hom.comp_apply, haq]
        exact ht
      · rw [← Category.assoc] at hx
        have hr := (H _ _).1 hx
        obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
        exact (hsub ⟨x q, rfl⟩ (hr ⟨q, by simp⟩)).elim
  haveI := D.freeLa
  haveI := D.finLa
  have hpos : 0 < p ^ r := pow_pos (Fact.out : p.Prime).pos r
  obtain ⟨κ', _, q, hq⟩ := GlobalTheory.LevCover.exists_finite_mod D.La hpos
  have hpr : ∀ c : D.La, (p ^ r) • c ∈ wSub D w0 r := by
    intro c
    refine Submodule.subset_span ⟨(p : 𝓞 D.F) ^ r, Ideal.pow_mem_pow hw.2.1 r, c, ?_⟩
    rw [map_pow, map_natCast, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  refine (GlobalTheory.LevCover.ClopenCond.forall_of_finite q hP ?_).congr fun T' h => ?_
  · intro i j hij T' h Pi k _ _ x hx
    obtain ⟨c, rfl⟩ := hq i j hij
    have he : et (i + p ^ r • c) = et i := by rw [hadd, hvan _ (hpr c), _root_.mul_one]
    rw [he] at hx
    exact (wSub D w0 r).add_mem (Pi k x hx) (hpr c)
  · exact ⟨fun H y k _ _ x => H k x y, fun H k _ _ x y => H y k x⟩

end GlobalTheory.UPel.HT.EtLev
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClopenCondInjectiveGeomStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.clopenCond_injective_geom_alt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) (κ : K ⟶ o.A), IsFinite K.hom → Etale K.hom → (∀ c ∈ w0 ^ r, κ ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ K, y ≫ κ = x) → ∀ (Z : Over S) (et : D.La → (Z ⟶ o.A)), IsFinite Z.hom → Etale Z.hom → (∀ x y, et (x + y) = et x * et y) → (∀ (c : D.O) x, et (c • x) = et x ≫ o.act.act c) → (∀ x ∈ wSub D w0 r, et x = 1) → GlobalTheory.LevCover.ClopenCond Z fun T' h => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T'.left), (∀ y, (Over.homMk x rfl : Over.mk (x ≫ T'.hom) ⟶ T') ≫ h ≫ et y = 1 → y ∈ wSub D w0 r) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom) | (exact GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom) | (intros; apply GlobalTheory.UPel.HT.EtLev.clopenCond_injective_geom <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerSeriesPowPFrobenius

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPel.HT.PrimTors

theorem exists_finite_flat_wPow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (r : ℕ), ∃ r' : ℕ, r ≤ r' ∧ ∃ (H : Over S) (i : H ⟶ o.A), IsFinite H.hom ∧ Flat H.hom ∧ (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x := by
  intro p _ D R _ b N w0 _ hp S _ s o r
  have hw0 : w0 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hp
  have hwr : w0 ^ r ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot] at *
    exact pow_ne_zero r hw0
  obtain ⟨K, _, i, -, _, hfin, hflat, hK⟩ :=
    GlobalTheory.IwLevel.HTTorsionFF.exists_torsion_finite_flat p D R b N (w0 ^ r) S s o hwr
  have key : ∀ (T : Over S) (x : T ⟶ o.A),
      GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) ((w0 ^ r).map (algebraMap (𝓞 D.F) D.O)) x ↔
        ∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T x
    unfold Ideal.map
    rw [GlobalTheory.IwLevel.killedBy_span]
    constructor
    · intro h c hc
      exact h _ ⟨c, hc, rfl⟩
    · rintro h _ ⟨c, hc, rfl⟩
      exact h c hc
  refine ⟨r, le_rfl, K, i, hfin, hflat, (key _ i).1 ((hK _ i).1 ⟨𝟙 _, Category.id_comp _⟩), fun T x hx => ?_⟩
  obtain ⟨y, hy⟩ := (hK T x).2 ((key T x).2 hx)
  exact ⟨y, hy, fun y' hy' => (cancel_mono i).1 (hy'.trans hy.symm)⟩

end GlobalTheory.UPel.HT.PrimTors
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFlatTorsionSubgroup

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.finite_flat_torsion_subgroup : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (r : ℕ), ∃ r' : ℕ, r ≤ r' ∧ ∃ (H : Over S) (i : H ⟶ o.A), IsFinite H.hom ∧ Flat H.hom ∧ (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x := by
  first | (exact @GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow) | (exact GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow) | (intros; apply GlobalTheory.UPel.HT.PrimTors.exists_finite_flat_wPow  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitesimalPointTrivial

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.infinitesimal_point_trivial : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1 := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.TanKill.tan_eq_one_of_etPlace) | (exact GlobalTheory.UPel.HT.EtLev.TanKill.tan_eq_one_of_etPlace) | (intros; apply GlobalTheory.UPel.HT.EtLev.TanKill.tan_eq_one_of_etPlace  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaEquivariantFrobenius

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem etale_of_killed_tangent_trivial : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Flat H.hom → (∀ c ∈ w0 ^ r, i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1) → Etale H.hom := by
  intro p _ D R _ b N w0 r S _ s o H i hfin hflat hkill hrep htan
  haveI := hfin
  haveI := hflat
  haveI : LocallyOfFinitePresentation H.hom := inferInstance
  have hinv : ∀ {T : Over S} (a : T ⟶ o.A) (f : o.A ⟶ o.A) [IsMonHom f], a⁻¹ ≫ f = (a ≫ f)⁻¹ := by
    intro T a f _
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← mul_comp, inv_mul_cancel, one_comp]
  haveI : FormallyUnramified H.hom := by
    refine TangentCrit.formallyUnramified_of_tangent H.hom fun k _ _ w hw => ?_
    let x : Sp k ⟶ S := TangentCrit.dualPt k ≫ w ≫ H.hom
    let W : epsPtR x ⟶ H := Over.homMk w hw
    let U : epsPtR x ⟶ H := Over.homMk (TangentCrit.dualBase k ≫ TangentCrit.dualPt k ≫ w)
      (by simp only [Category.assoc]; rfl)
    let e : Over.mk x ⟶ epsPtR x := Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
      (TangentCrit.dualPt_dualBase_assoc k _)
    have heU : e ≫ W = e ≫ U := by
      ext1
      exact (TangentCrit.dualPt_dualBase_assoc k (TangentCrit.dualPt k ≫ w)).symm
    have hv : (W ≫ i) * (U ≫ i)⁻¹ = 1 := by
      refine htan k x _ ?_ ?_
      · have h1 : e ≫ ((W ≫ i) * (U ≫ i)⁻¹) = 1 := by
          rw [comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, heU, mul_inv_cancel]
        exact congrArg (fun q => q.left) h1
      · intro c hc
        haveI := o.act.hom (algebraMap (𝓞 D.F) D.O c)
        rw [mul_comp, hinv, Category.assoc, Category.assoc, hkill c hc, comp_one, comp_one, inv_one, _root_.mul_one]
    have hWU : W ≫ i = U ≫ i := mul_inv_eq_one.1 hv
    have hk : ∀ c ∈ w0 ^ r, (W ≫ i) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, hkill c hc, comp_one]
    obtain ⟨y, -, hy⟩ := hrep _ (W ≫ i) hk
    have hW := hy W rfl
    have hU := hy U hWU.symm
    exact congrArg (fun q => q.left) (hW.trans hU.symm)
  exact Etale.of_formallyUnramified_of_flat H.hom

end GlobalTheory.UPel.HT.EtLev
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSubgroupUniversal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.torsion_subgroup_universal : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (H : Over S) (i : H ⟶ o.A), IsFinite H.hom → Flat H.hom → (∀ c ∈ w0 ^ r, i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → (∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (v : epsPtR x ⟶ o.A), spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ o.A).left → (∀ c ∈ w0 ^ r, v ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → v = 1) → Etale H.hom := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial) | (exact GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial) | (intros; apply GlobalTheory.UPel.HT.EtLev.etale_of_killed_tangent_trivial <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSchemeRepresentingEtaleLevels

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory.UPel.HT.EtLev

theorem exists_etLevScheme : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Scheme.{0}) (π : Y ⟶ S) (lu : D.La → (Over.mk π ⟶ o.A)), IsFinite π ∧ Etale π ∧ IsEtLevOver o w0 r lu ∧ ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o w0 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y := by
  intro p _ D R _ b N w0 r _hNp hw S _ s o
  obtain ⟨r', hrr', H, i, hHf, hHfl, hHk, hHu⟩ := GlobalTheory.T.finite_flat_torsion_subgroup p D R b N w0 hw.1 hw.2.1 S s o r
  have hHe : Etale H.hom := GlobalTheory.T.torsion_subgroup_universal p D R b N w0 r' S s o H i hHf hHfl hHk hHu
    (fun k _ _ x v h0 hv => GlobalTheory.T.infinitesimal_point_trivial p D R b N w0 r' hw S s o k x v h0 hv)
  obtain ⟨K, κ, hKf, hKe, hKk, hKu⟩ := GlobalTheory.T.etale_torsion_subgroup_universal p D R b N w0 r r' hrr' S s o H i hHf hHe hHk hHu
  obtain ⟨Z, et, hZf, hZe, eadd, elin, eker, huniv⟩ := GlobalTheory.T.etale_level_kernel_universal p D R b N w0 r hw S s o K κ hKf hKe hKk hKu
  have c1 := GlobalTheory.T.clopenCond_injective_geom_alt p D R b N w0 r hw S s o K κ hKf hKe hKk hKu Z et hZf hZe eadd elin eker
  have c2 := GlobalTheory.T.clopenCond_onto_alt p D R b N w0 r hw S s o K κ hKf hKe hKk hKu Z et hZf hZe eadd elin eker
  obtain ⟨U, hU, HU⟩ := c1.and c2
  haveI := hZf
  haveI := hZe
  obtain ⟨V, j, hV1, hV2, hmono, Hj⟩ := GlobalTheory.LevCover.exists_sub U hU
  have hPV := (HU V j).2 ((Hj V j).2 ⟨𝟙 V, Category.id_comp j⟩)
  refine ⟨V.left, V.hom, fun y => j ≫ et y, hV1, hV2, ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_,
    fun k _ _ x => ⟨hPV.1 k x, hPV.2 k x⟩⟩, fun T l hl => ?_⟩
  · beta_reduce
    rw [eadd, MonObj.comp_mul]
  · beta_reduce
    rw [elin, Category.assoc]
  · beta_reduce
    rw [eker x hx, MonObj.comp_one]
  obtain ⟨hadd, hlin, hker, hgeo⟩ := hl
  obtain ⟨h, hh, hu⟩ := huniv T l hadd hlin hker
  have hP : (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
      ∀ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ h ≫ et y = 1 → y ∈ wSub D w0 r) ∧
      (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
        ∀ g : Over.mk (x ≫ T.hom) ⟶ o.A, (∀ c ∈ w0 ^ r, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) →
          ∃ y, (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ h ≫ et y = g) := by
    refine ⟨fun k _ _ x y hy => (hgeo k x).1 y (by rw [← hh y]; exact hy), fun k _ _ x g hg => ?_⟩
    obtain ⟨y, hy⟩ := (hgeo k x).2 g hg
    exact ⟨y, by rw [hh y]; exact hy⟩
  obtain ⟨h', hh'⟩ := (Hj T h).1 ((HU T h).1 hP)
  refine ⟨h', fun y => ?_, fun g hg => ?_⟩
  · beta_reduce
    rw [← Category.assoc, hh', hh]
  · have : g ≫ j = h := hu _ fun y => by rw [Category.assoc]; exact hg y
    exact (cancel_mono j).1 (this.trans hh'.symm)

end GlobalTheory.UPel.HT.EtLev
end
end
end
