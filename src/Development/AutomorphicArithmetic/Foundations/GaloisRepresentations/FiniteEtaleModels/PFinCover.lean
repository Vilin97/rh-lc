module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassifyingMapSymplecticLevelEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueOfBaseEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevIffIsEtLevOverStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtLevRelExistsUnique

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

theorem exists_unique_quotAut {O M G : Type*} [Ring O] [AddCommGroup M] [Module O M] [Group G]
    (W : Submodule O M) (act : O → G → G) (L L' : M → G)
    (hadd : ∀ a b, L (a + b) = L a * L b) (hadd' : ∀ a b, L' (a + b) = L' a * L' b)
    (hsm : ∀ (c : O) a, L (c • a) = act c (L a)) (hsm' : ∀ (c : O) a, L' (c • a) = act c (L' a))
    (hker : ∀ a, L a = 1 ↔ a ∈ W) (hker' : ∀ a, L' a = 1 ↔ a ∈ W)
    (hsurj : ∀ a, ∃ b, L b = L' a) (hsurj' : ∀ a, ∃ b, L' b = L a) :
    ∃! g : (M ⧸ W) ≃ₗ[O] (M ⧸ W),
      ∀ y, L (Function.surjInv (Submodule.mkQ_surjective W) (g (W.mkQ y))) = L' y := by
  have key : ∀ {L : M → G}, (∀ a b, L (a + b) = L a * L b) → (∀ a, L a = 1 ↔ a ∈ W) →
      ∀ a b, L a = L b ↔ W.mkQ a = W.mkQ b := by
    intro L hadd hker a b
    have h : L a = L (a - b) * L b := by rw [← hadd, sub_add_cancel]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hker, h]
    constructor
    · intro e
      exact mul_right_cancel (e.trans (_root_.one_mul _).symm)
    · intro e
      rw [e, _root_.one_mul]
  have eq := key hadd hker
  choose z hz using hsurj
  let f₀ : M →ₗ[O] M ⧸ W :=
    { toFun := fun y => W.mkQ (z y)
      map_add' := fun a b => by
        rw [← map_add (f := _), ← eq, hadd, hz, hz, hz, hadd']
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← LinearMap.map_smul, ← eq, hsm, hz, hz, hsm'] }
  have hf₀ : W ≤ LinearMap.ker f₀ := by
    intro y hy
    rw [LinearMap.mem_ker]
    show W.mkQ (z y) = 0
    rw [← map_zero W.mkQ, ← eq, hz, (hker' y).2 hy, (hker 0).2 W.zero_mem]
  let f := W.liftQ f₀ hf₀
  have hf : ∀ y, f (W.mkQ y) = W.mkQ (z y) := fun y => rfl
  have bij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨y, rfl⟩ := W.mkQ_surjective q
      rw [hf, ← map_zero W.mkQ, ← eq, hz, (hker 0).2 W.zero_mem, hker'] at hq
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hq
    · intro q
      obtain ⟨a, rfl⟩ := W.mkQ_surjective q
      obtain ⟨y, hy⟩ := hsurj' a
      exact ⟨W.mkQ y, by rw [hf, ← eq, hz, hy]⟩
  refine ⟨LinearEquiv.ofBijective f bij, ?_, ?_⟩
  · intro y
    rw [← hz y, eq, Function.surjInv_eq (Submodule.mkQ_surjective W)]
    rfl
  · intro g hg
    refine LinearEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := W.mkQ_surjective q
    rw [LinearEquiv.ofBijective_apply, hf, ← Function.surjInv_eq (Submodule.mkQ_surjective W) (g (W.mkQ y)),
      ← eq, hg y, hz]

theorem etLev_rel_existsUnique (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S) (l l' : D.La → (Over.mk x ⟶ o.A)) :
    IsEtLevOver o w0 r l → IsEtLevOver o w0 r l' → ∃! g : LevGrp D w0 r, ∀ y, l (levAct g y) = l' y := by
  intro hl hl'
  obtain ⟨hinj, hsur⟩ := hl.2.2.2 k (𝟙 _)
  obtain ⟨hinj', hsur'⟩ := hl'.2.2.2 k (𝟙 _)
  have canc : ∀ u v : Over.mk x ⟶ o.A,
      (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ u =
        (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ v → u = v := by
    intro u v h
    ext
    have := congrArg CommaMorphism.left h
    simpa using this
  have killed : ∀ (l₁ : D.La → (Over.mk x ⟶ o.A)), IsEtLevOver o w0 r l₁ → ∀ a, ∀ c ∈ w0 ^ r,
      ((Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ l₁ a) ≫
        o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro l₁ h₁ a c hc
    rw [Category.assoc, ← h₁.2.1, h₁.2.2.1 _ (Submodule.subset_span ⟨c, hc, a, rfl⟩), comp_one]
  exact exists_unique_quotAut (wSub D w0 r) (fun c g => g ≫ o.act.act c) l l' hl.1 hl'.1 hl.2.1 hl'.2.1
    (fun a => ⟨fun h => hinj a (by rw [h, comp_one]), fun h => hl.2.2.1 a h⟩)
    (fun a => ⟨fun h => hinj' a (by rw [h, comp_one]), fun h => hl'.2.2.1 a h⟩)
    (fun a => by
      obtain ⟨y, hy⟩ := hsur _ (killed l' hl' a)
      exact ⟨y, canc _ _ hy⟩)
    (fun a => by
      obtain ⟨y, hy⟩ := hsur' _ (killed l hl a)
      exact ⟨y, canc _ _ hy⟩)

end GlobalTheory.UPel.HT.EtLev
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtLevRelExistsUniqueStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.existsUnique_levGrp_of_isEtLevOver : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (l l' : D.La → (Over.mk x ⟶ o.A)), IsEtLevOver o w0 r l → IsEtLevOver o w0 r l' → ∃! g : LevGrp D w0 r, ∀ y, l (levAct g y) = l' y := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique) | (exact GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique) | (intros; apply GlobalTheory.UPel.HT.EtLev.etLev_rel_existsUnique  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LebesgueSelfdualForDotCharacter

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section
namespace GlobalTheory.UPel.HT.EtLev

theorem isEtLevOver_eq_of_mkQ_eq {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R}
    {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {w0 : Ideal (𝓞 D.F)} {r : ℕ} {T : Over S}
    {l : D.La → (T ⟶ o.A)} (h : IsEtLevOver o w0 r l) {z z' : D.La}
    (hz : (wSub D w0 r).mkQ z = (wSub D w0 r).mkQ z') : l z = l z' := by
  have hm : z - z' ∈ wSub D w0 r := by
    rw [← Submodule.Quotient.mk_eq_zero]; simpa [sub_eq_zero] using hz
  have := h.1 z' (z - z')
  rw [add_sub_cancel, h.2.2.1 _ hm, _root_.mul_one] at this
  exact this

theorem isEtLevOver_levAct (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ)
    (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T : Over S)
    (l : D.La → (T ⟶ o.A)) (g : LevGrp D w0 r) (h : IsEtLevOver o w0 r l) :
    IsEtLevOver o w0 r (fun y => l (levAct g y)) := by
  have hq := fun {z z' : D.La} (hz : (wSub D w0 r).mkQ z = (wSub D w0 r).mkQ z') =>
    isEtLevOver_eq_of_mkQ_eq h hz
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ⟨fun y hy => ?_, fun gg hgg => ?_⟩⟩
  · rw [← h.1]; apply hq
    simp only [mkQ_levAct, map_add (f := _)]
  · rw [← h.2.1]; apply hq
    simp only [mkQ_levAct, map_smul]
  · have : levAct g x ∈ wSub D w0 r := by
      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, mkQ_levAct,
        Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 hx, map_zero]
    exact h.2.2.1 _ this
  · have h1 := (h.2.2.2 k x).1 _ hy
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, mkQ_levAct] at h1
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    exact (LinearEquiv.map_eq_zero_iff g).1 h1
  · obtain ⟨y, hy⟩ := (h.2.2.2 k x).2 gg hgg
    refine ⟨levAct g.symm y, ?_⟩
    rw [← hy]; congr 1; apply hq
    simp only [mkQ_levAct, LinearEquiv.apply_symm_apply]

end GlobalTheory.UPel.HT.EtLev
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLevelGroupAction

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.etale_level_group_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (T : Over S) (l : D.La → (T ⟶ o.A)) (g : LevGrp D w0 r), IsEtLevOver o w0 r l → IsEtLevOver o w0 r (fun y => l (levAct g y)) := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct) | (exact GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct) | (intros; apply GlobalTheory.UPel.HT.EtLev.isEtLevOver_levAct <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private theorem level_congr {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {𝔞 : Ideal (𝓞 D.F)} {r : ℕ} {T : Over S}
    {l : D.La → (T ⟶ o.A)} (hl : IsEtLevOver o 𝔞 r l) {u v : D.La}
    (e : (wSub D 𝔞 r).mkQ u = (wSub D 𝔞 r).mkQ v) : l u = l v := by
  have hmem : u - v ∈ wSub D 𝔞 r := (Submodule.Quotient.eq _).mp e
  have h1 : l (u - v) = 1 := hl.2.2.1 _ hmem
  calc l u = l ((u - v) + v) := by rw [sub_add_cancel]
    _ = l (u - v) * l v := hl.1 _ _
    _ = l v := by rw [h1, _root_.one_mul]

private theorem rep_ext {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {o : Obj b N s} {𝔞 : Ideal (𝓞 D.F)} {r : ℕ} {Y : Scheme.{0}} {π : Y ⟶ S}
    {lu : D.La → (Over.mk π ⟶ o.A)} (hlu : IsEtLevOver o 𝔞 r lu)
    (hrep : ∀ (T : Over S) (l : D.La → (T ⟶ o.A)), IsEtLevOver o 𝔞 r l → ∃! f : T ⟶ Over.mk π, ∀ y, f ≫ lu y = l y)
    {T : Over S} {f f' : T ⟶ Over.mk π} (h : ∀ y, f ≫ lu y = f' ≫ lu y) : f = f' := by
  obtain ⟨g, -, huniq⟩ := hrep T (fun y => f ≫ lu y)
    (GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu f hlu)
  rw [huniq f (fun y => rfl), huniq f' (fun y => (h y).symm)]

theorem UpperTheory.Gal.FiniteEtaleModels.finCover_holds :
    RepAll → PtAll → GrpFin → FinCover := by
  intro hRep hPt hGrp p _ D R _ b N 𝔞 r hN hcop het S _ s o
  obtain ⟨Y, π, lu, hfin, het', hlu, hrep⟩ := hRep p D R b N 𝔞 r hcop het S s o
  obtain ⟨o', ⟨m⟩⟩ := GlobalTheory.HTPull.exists_objMap_pull p D R b N S Y s π o
  have hpb := m.cart.1
  have hluw : ∀ y, (lu y).left ≫ o.A.hom = 𝟙 Y ≫ π := fun y => by
    rw [Category.id_comp]; exact Over.w (lu y)
  let lv : D.La → (𝟙_ (Over Y) ⟶ o'.A) := fun y =>
    Over.homMk (hpb.lift (lu y).left (𝟙 Y) (hluw y)) (by rw [hpb.lift_snd]; rfl)
  have hlv : ∀ y, (lv y).left ≫ m.φ = (lu y).left := fun y => hpb.lift_fst _ _ _
  have hlv2 : ∀ y, (lv y).left ≫ o'.A.hom = 𝟙 Y := fun y => hpb.lift_snd _ _ _
  have hpt : ∀ y, ptOf m (lv y) = lu y := fun y => by
    ext1; exact hlv y
  have hcomp : ∀ (a c : LevGrp D 𝔞 r) (y : D.La), lu (levAct a (levAct c y)) = lu (levAct (a * c) y) :=
    fun a c y => level_congr hlu (by rw [mkQ_levAct, mkQ_levAct, mkQ_levAct]; rfl)
  have hone : ∀ y, lu (levAct (1 : LevGrp D 𝔞 r) y) = lu y :=
    fun y => level_congr hlu (by rw [mkQ_levAct]; rfl)
  have hact : ∀ g : LevGrp D 𝔞 r, ∃ f : Over.mk π ⟶ Over.mk π, ∀ y, f ≫ lu y = lu (levAct g y) :=
    fun g => (hrep _ _ (GlobalTheory.T.etale_level_group_action p D R b N S s o 𝔞 r _ lu g hlu)).exists
  choose fg hfg using hact
  have hfgeq : ∀ (f : Over.mk π ⟶ Over.mk π) (g : LevGrp D 𝔞 r),
      (∀ y, f ≫ lu y = lu (levAct g y)) → f = fg g :=
    fun f g hf => rep_ext hlu hrep (fun y => by rw [hf, hfg])
  refine ⟨Y, π, o', m, lv, fun g => (fg g).left, ?_, ?_, ?_⟩
  · rw [GlobalTheory.T.isEtLev_iff_isEtLevOver' p D R b N S Y s π (π ≫ s) o o' m 𝔞 r lv]
    simpa only [hpt] using hlu
  · refine ⟨(hGrp p D 𝔞 r het.1).2, ?_, ?_, ?_, hfin, het', ?_, ?_⟩
    · show (fg 1).left = 𝟙 Y
      rw [← hfgeq (𝟙 _) 1 (fun y => by rw [Category.id_comp, hone])]
      rfl
    · intro a c
      show (fg (a * c)).left = (fg a).left ≫ (fg c).left
      rw [← hfgeq (fg a ≫ fg c) (a * c) (fun y => by rw [Category.assoc, hfg, hfg, hcomp])]
      rfl
    · intro a
      exact Over.w (fg a)
    · constructor
      intro x
      obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point S x
      obtain ⟨l, hl⟩ := hPt p D R b N 𝔞 r hcop het S s o k a
      obtain ⟨f, -, -⟩ := hrep _ l hl
      have hx : x ∈ Set.range ⇑a := by rw [ha]; rfl
      obtain ⟨q, hq⟩ := hx
      have hw : f.left ≫ π = a := Over.w f
      refine ⟨f.left q, ?_⟩
      rw [← hq, ← Scheme.Hom.comp_apply, hw]
    · intro K _ _ y y' hyy
      let j : Over.mk (y ≫ π) ⟶ Over.mk π := Over.homMk y rfl
      let j' : Over.mk (y ≫ π) ⟶ Over.mk π := Over.homMk y' hyy.symm
      have hl := GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu j hlu
      have hl' := GlobalTheory.T.etale_level_base_change p D R b N S s o 𝔞 r _ _ lu j' hlu
      obtain ⟨g, hg, hguniq⟩ := GlobalTheory.T.existsUnique_levGrp_of_isEtLevOver p D R b N S s o 𝔞 r K (y ≫ π) _ _ hl hl'
      refine ⟨g, ?_, ?_⟩
      · have : j ≫ fg g = j' := rep_ext hlu hrep (fun z => by rw [Category.assoc, hfg]; exact hg z)
        exact congrArg (fun q => Over.Hom.left q) this
      · intro a ha
        apply hguniq
        intro z
        show j ≫ lu (levAct a z) = j' ≫ lu z
        have : j ≫ fg a = j' := by ext1; exact ha
        rw [← hfg, ← Category.assoc, this]
  · intro T t o₁ m₁ l hl
    have hl' := (GlobalTheory.T.isEtLev_iff_isEtLevOver' p D R b N S T s t (t ≫ s) o o₁ m₁ 𝔞 r l).mp hl
    obtain ⟨g, hg, hguniq⟩ := hrep (Over.mk t) _ hl'
    have hgw : g.left ≫ π = t := Over.w g
    have hφ : ∀ (f : T ⟶ Y) (_ : f ≫ π = t) (m₃ : GlobalTheory.UPel.HT.ObjMap o₁ o (f ≫ π)), m₃.φ = m₁.φ :=
      fun f hf m₃ => Rigid.objMap_phi_unique p D R b N hN hcop S T s (t ≫ s) o o₁ (f ≫ π) t m₃ m₁ hf
    have hgl : ∀ y, (l y).left ≫ m₁.φ = g.left ≫ (lu y).left := fun y => by
      have := congrArg (fun q => Over.Hom.left q) (hg y)
      exact this.symm
    refine ⟨g.left, ⟨hgw, ?_⟩, ?_⟩
    · obtain ⟨m₂, hm₂⟩ := GlobalTheory.HTSympCover.exists_objMap_cancel_φ
        (by rw [hgw]; exact m₁ : GlobalTheory.UPel.HT.ObjMap o₁ o (g.left ≫ π)) m
      refine ⟨m₂, fun y => ?_⟩
      apply hpb.hom_ext
      · rw [Category.assoc, hm₂, hφ _ hgw, Category.assoc, hlv, hgl]
      · rw [Category.assoc, m₂.cart.1.w, ← Category.assoc, Over.w (l y), Category.assoc, hlv2,
          Category.comp_id]
        exact Category.id_comp _
    · rintro f' ⟨hf', m₂', hm₂'⟩
      obtain ⟨m₃, hm₃⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ m₂' m
      have : (Over.homMk f' hf' : Over.mk t ⟶ Over.mk π) = g := by
        apply hguniq
        intro y
        ext1
        show f' ≫ (lu y).left = (l y).left ≫ m₁.φ
        rw [← hlv, ← Category.assoc, ← hm₂' y, Category.assoc, ← hm₃, hφ f' hf' m₃]
      exact congrArg (fun q => Over.Hom.left q) this
end
end
