module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LocalComponentsSurjective
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrIsGenAt
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CiEigVal
public import Development.WeilBound.CoreStatements.HodgeTatePoints.CiGrAlg
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.LieValAtBase

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

theorem exists_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {A R : Type} [CommRing A] [CommRing R] (φ : A →+* R)
    (x : Spec (CommRingCat.of A) ⟶ S) (z : Spec (CommRingCat.of R) ⟶ S)
    (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {E F : Type} [AddCommGroup E] [Module A E] [AddCommGroup F]
    [Module R F] (M : LieModel G x E) (N : LieModel G z F) :
    ∃ j : E →+ F, (∀ e, N.pt (j e) = LieTangent.epsBase φ hz ≫ M.pt e) ∧
      (∀ (a : A) e, j (a • e) = φ a • j e) ∧
      (Smooth G.hom → ∀ (n : ℕ) (b : Module.Basis (Fin n) A E),
        ∃ b' : Module.Basis (Fin n) R F, ∀ k, b' k = j (b k)) := by
  subst hz
  letI := φ.toAlgebra
  obtain ⟨j, h1, h2, h3⟩ := PositivityTheory.HtPt.Htat.lie_bc S G A R x E F M N
  refine ⟨j, fun e => Over.OverMorphism.ext (h1 e), h2, fun hs n b => ?_⟩
  exact ⟨Module.Basis.mk (h3 hs n b).1 (h3 hs n b).2.ge, fun k => Module.Basis.mk_apply _ _ _⟩

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem lieValAt_base (hξ : IsCptGen ξ) {M : LieModel G ξ V} {R R' : Type} [CommRing R] [IsLocalRing R]
    [CommRing R'] [IsLocalRing R'] (φ : R →+* R') {x : Spec (CommRingCat.of R) ⟶ X}
    {z : Spec (CommRingCat.of R') ⟶ X} (hz : Spec.map (CommRingCat.ofHom φ) ≫ x = z) {e : V} {w : epsAt x ⟶ G}
    (h : M.ValAt x e w) : M.ValAt z e (LieTangent.epsBase φ hz ≫ w) := by
  subst hz
  rw [LieModel.valAt_iff] at h ⊢
  obtain ⟨hc, v, hv, rfl⟩ := h
  have hsp := LieTangent.centre_specializes φ x
  have hc' := LieTangent.specializes_of_injective (hξ.inj ⟨_, hc⟩) hsp
  have F1 : Spec.map (CommRingCat.ofHom (X.presheaf.stalkSpecializes hsp).hom) ≫ X.fromSpecStalk (centre x) =
      X.fromSpecStalk (centre (Spec.map (CommRingCat.ofHom φ) ≫ x)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hd : ∀ {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D),
      (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
    intro A B D _ _ _ f g
    refine RingHom.ext fun a => ?_
    ext <;> simp
  rw [LieModel.extends_iff] at hv
  refine ⟨hc', LieTangent.epsBase (X.presheaf.stalkSpecializes hsp).hom F1 ≫ v,
    (M.extends_iff _ _ _).2 ⟨LieTangent.isTanAt_base _ _ hv.1, ?_⟩, ?_⟩
  · rw [hv.2, ← Category.assoc]
    congr 1
    refine Over.OverMorphism.ext ?_
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [LieTangent.spec_comp, hd]
    congr 3
    exact RingHom.ext fun s => (LieTangent.genMap_specializes ⟨_, hc⟩ hc' hsp s).symm
  · rw [← Category.assoc, ← Category.assoc]
    congr 1
    refine Over.OverMorphism.ext ?_
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [LieTangent.spec_comp, hd, LieTangent.spec_comp, hd]
    congr 3
    exact (congrArg CommRingCat.Hom.hom (LieTangent.stalk_base φ x)).symm

theorem frame_basis [IsCommMonObj G] (hξ : IsCptGen ξ) (hs : Smooth G.hom) (M : LieModel G ξ V) {R : Type}
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) {ER : Type}
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) {n : ℕ} {b : Fin n → V}
    (hb : M.lat.IsFrameAt b ⟨centre z, h⟩) :
    ∃ bz : Module.Basis (Fin n) R ER, ∀ q, M.ValAt z (b q) (MR.pt (bz q)) := by
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, -, hjb⟩ := exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, his, -⟩ := exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M
  have hext : ∀ a, M.Extends ⟨centre z, h⟩ (i a) (MA.pt a) := fun a =>
    (M.extends_iff _ _ _).2 ⟨MA.tan a, hi a⟩
  have hinj : ∀ a b, i a = i b → a = b := fun a b hab =>
    MA.inj ((hext a).unique (hξ.inj _) (hab ▸ hext b))
  have hsurj : ∀ e ∈ M.lat ⟨centre z, h⟩, ∃ a, i a = e := by
    intro e he
    obtain ⟨v, hv⟩ := (M.mem_lat_iff _ _).1 he
    obtain ⟨a, rfl⟩ := MA.onto v hv.1
    exact ⟨a, M.inj ((hi a).trans ((M.extends_iff _ _ _).1 hv).2.symm)⟩
  choose a ha using fun q => hsurj (b q) (by rw [hb.2]; exact Submodule.subset_span ⟨q, rfl⟩)
  have hsum : ∀ c : Fin n → X.presheaf.stalk (centre z),
      i (∑ q, c q • a q) = ∑ q, genMap ξ ⟨centre z, h⟩ (c q) • b q := by
    intro c

    rw [map_sum]
    exact Finset.sum_congr rfl fun q _ => by rw [his, ha]
  have li : LinearIndependent (X.presheaf.stalk (centre z)) a := by
    rw [Fintype.linearIndependent_iff]
    intro c hc q
    have h1 := hsum c
    rw [hc, map_zero] at h1
    exact hξ.inj ⟨_, h⟩ ((Fintype.linearIndependent_iff.1 hb.1 _ h1.symm q).trans (map_zero _).symm)
  have sp : ⊤ ≤ Submodule.span (X.presheaf.stalk (centre z)) (Set.range a) := by
    intro e _
    have h1 : i e ∈ M.lat ⟨centre z, h⟩ := (M.mem_lat_iff _ _).2 ⟨_, hext e⟩
    rw [hb.2, Submodule.mem_span_range_iff_exists_fun] at h1
    obtain ⟨c, hc⟩ := h1
    choose s hs using fun q => (c q).2
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨s, hinj _ _ ?_⟩
    rw [hsum, ← hc]
    exact Finset.sum_congr rfl fun q _ => by rw [hs]; rfl
  obtain ⟨bz, hbz⟩ := hjb hs n (Module.Basis.mk li sp)
  refine ⟨bz, fun q => (M.valAt_iff _ _ _).2 ⟨h, MA.pt (a q), ha q ▸ hext (a q), ?_⟩⟩
  rw [hbz, hj, Module.Basis.mk_apply]

theorem frame_lat [IsCommMonObj G] (hξ : IsCptGen ξ) (hs : Smooth G.hom) (M : LieModel G ξ V) {K : Type} [Field K]
    {C : ACurve K} {z : Spec (CommRingCat.of K) ⟶ X} (Y : CurveIn C z) {Vz : Type} [AddCommGroup Vz] [Module K Vz]
    (Mz : LieModel G z Vz) {n : ℕ} {b : Fin n → V} (i : C.I) (h : genPt ξ ⤳ centre (Y.x i))
    (hb : M.lat.IsFrameAt b ⟨centre (Y.x i), h⟩) :
    ∃ bz : Module.Basis (Fin n) K Vz, (∀ q, M.ValAt z (b q) (Mz.pt (bz q))) ∧ IsLatOf C i bz (Y.lieLat Mz i) := by
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists X G _ (Y.x i)
  obtain ⟨bR, hbR⟩ := frame_basis hξ hs M (Y.x i) h MR hb
  obtain ⟨j, hj, hjs, hjb⟩ := exists_base (C.v i).valuationSubring.subtype _ z (Y.gen i) MR Mz
  obtain ⟨bz, hbz⟩ := hjb hs n bR
  refine ⟨bz, fun q => ?_, fun x => ?_⟩
  · rw [hbz, hj]
    exact lieValAt_base hξ _ _ (hbR q)
  · have hr : Y.lieLat Mz i = j.range := by
      refine le_antisymm ((AddSubgroup.closure_le _).2 ?_) ?_
      · rintro e ⟨v, hv, he⟩
        obtain ⟨u, rfl⟩ := MR.onto v hv
        exact ⟨u, Mz.inj ((hj u).trans (Over.OverMorphism.ext he.symm))⟩
      · rintro _ ⟨u, rfl⟩
        exact AddSubgroup.subset_closure ⟨MR.pt u, MR.tan u, congrArg (fun q => q.left) (hj u)⟩
    have hsum : ∀ c : Fin n → (C.v i).valuationSubring, j (∑ q, c q • bR q) = ∑ q, (c q : K) • bz q := by
      intro c

      rw [map_sum]
      exact Finset.sum_congr rfl fun q _ => by rw [hjs, hbz]; rfl
    rw [hr]
    constructor
    · rintro ⟨u, rfl⟩ q
      rw [← bR.sum_repr u, hsum, bz.repr_sum_self]
      exact (bR.repr u q).2
    · intro hx
      exact ⟨∑ q, (⟨bz.repr x q, hx q⟩ : (C.v i).valuationSubring) • bR q, by rw [hsum]; exact bz.sum_repr x⟩

end PositivityTheory.HtPt.Ci
end
end
end

-- Source module: Development.WeilBound.CoreStatements.HodgeTatePoints.CiGrDeg

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem valAt_zero' {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X}
    (h : genPt ξ ⤳ centre z) : ValAt ξ z 0 0 :=
  ⟨h, 0, map_zero _, map_zero _⟩

theorem lieValAt_sum {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {ER : Type} [AddCommGroup ER] [Module R ER]
    {MR : LieModel G z ER} {ι : Type} (T : Finset ι) {e : ι → V} {v : ι → ER}
    (hv : ∀ k, M.ValAt z (e k) (MR.pt (v k))) : M.ValAt z (∑ k ∈ T, e k) (MR.pt (∑ k ∈ T, v k)) := by
  classical
  induction T using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, MR.pt_zero]; exact M.valAt_zero h
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, MR.add]; exact (hv a).add ih

theorem val_coords (hξ : IsCptGen ξ) {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {ER : Type} [AddCommGroup ER] [Module R ER]
    {MR : LieModel G z ER} {n : ℕ} {B : Fin n → V} (hB : M.lat.IsFrameAt B ⟨centre z, h⟩)
    {bz : Module.Basis (Fin n) R ER} (hbz : ∀ q, M.ValAt z (B q) (MR.pt (bz q))) {e : V} {v : ER}
    (hv : M.ValAt z e (MR.pt v)) : ∃ c : Fin n → Ω, e = ∑ k, c k • B k ∧ ∀ k, ValAt ξ z (c k) (bz.repr v k) := by
  obtain ⟨_, he⟩ := (M.exists_valAt_iff z e).1 ⟨_, hv⟩
  rw [hB.2, Submodule.mem_span_range_iff_exists_fun] at he
  obtain ⟨c, hc⟩ := he
  choose s hs using fun q => (c q).2
  have hval : ∀ k, ValAt ξ z (c k : Ω) ((Scheme.stalkClosedPointTo z).hom (s k)) := fun k => ⟨h, s k, hs k, rfl⟩
  have h1 := lieValAt_sum h Finset.univ fun k => lieValAt_smul (hbz k) (hval k)
  have he : e = ∑ k, (c k : Ω) • B k := hc.symm
  rw [← he] at h1
  refine ⟨fun k => c k, he, fun k => ?_⟩
  rw [MR.inj (hv.unique hξ h1), bz.repr_sum_self]
  exact hval k

theorem coord_zero {n : ℕ} {B : Fin n → V} (hB : LinearIndependent Ω B) {c : Fin n → Ω} {T : Set (Fin n)}
    (h : ∑ k, c k • B k ∈ Submodule.span Ω (B '' T)) {l : Fin n} (hl : l ∉ T) : c l = 0 := by
  obtain ⟨φ, h1, h0⟩ := FlagGrGen.exists_coord hB l
  have h2 : Submodule.span Ω (B '' T) ≤ LinearMap.ker φ := Submodule.span_le.2 (by
    rintro _ ⟨k, hk, rfl⟩
    exact h0 k fun e => hl (e ▸ hk))
  have h3 : φ (∑ k, c k • B k) = 0 := h2 h

  rw [map_sum, Finset.sum_eq_single l (fun k _ hk => by rw [map_smul, h0 k hk, smul_zero]) (by simp)] at h3
  simpa [h1] using h3

theorem flagStep_of_append {r r' : ℕ} {b : Fin r → V} {B : Fin (r + r') → V} (hB : ∀ k, B (Fin.castAdd r' k) = b k)
    {s : ℕ} (hs : s ≤ r) : flagStep Ω b s = Submodule.span Ω (B '' {k | (k : ℕ) < s}) := by
  unfold flagStep
  congr 1
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨Fin.castAdd r' k, hk, hB k⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, lt_of_lt_of_le hk hs⟩, hk, (hB _).symm⟩

theorem exists_frame {S : Set (Cpt ξ)} {Λ L L' : Lat ξ V} {r r' : ℕ} {b₀ : Fin r → V} {U' : Submodule Ω V}
    (hL : L.IsFlagVBOn S b₀) (hL' : L'.IsVBOn S r' U') (hc : IsCompl (Submodule.span Ω (Set.range b₀)) U')
    (hΛ : ∀ q ∈ S, Λ q = L q ⊔ L' q) {p : Cpt ξ} (hp : p ∈ S) :
    ∃ U : X.Opens, p.1 ∈ U ∧ ∃ (b : Fin r → V) (B : Fin (r + r') → V), (∀ k, B (Fin.castAdd r' k) = b k) ∧
      (∀ s, flagStep Ω b s = flagStep Ω b₀ s) ∧ ∀ q ∈ S, q.1 ∈ U → L.IsFrameAt b q ∧ Λ.IsFrameAt B q := by
  obtain ⟨U₁, h1, b, hb, hb'⟩ := hL p hp
  obtain ⟨U₂, h2, c, hc1, hc'⟩ := hL' p hp
  have hr : ∀ b : Fin r → V, flagStep Ω b r = Submodule.span Ω (Set.range b) := fun b => by
    unfold flagStep
    congr 1
    ext x
    simp
  have e : Fin.append b c = Sum.elim b c ∘ finSumFinEquiv.symm := by
    funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp
  refine ⟨U₁ ⊓ U₂, ⟨h1, h2⟩, b, Fin.append b c, fun k => Fin.append_left _ _ _, hb, fun q hq hU => ?_⟩
  have f1 := hb' q hq hU.1
  have f2 := hc' q hq hU.2
  refine ⟨f1, ?_, ?_⟩
  · rw [e]
    refine (f1.1.sum_type f2.1 ?_).comp _ finSumFinEquiv.symm.injective
    rw [← hr, hb, hr, hc1]
    exact hc.disjoint
  · rw [hΛ q hq, f1.2, f2.2, e, finSumFinEquiv.symm.surjective.range_comp, Set.Sum.elim_range, Submodule.span_union]

theorem gr_deg : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ)) (L L' : Lat ξ V) (r r' : ℕ) (b₀ : Fin r → V) (U' : Submodule Ω V), IsCptGen ξ → Smooth G.hom → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → LinearIndependent Ω b₀ → L.IsFlagVBOn S b₀ → L'.IsVBOn S r' U' → IsCompl (Submodule.span Ω (Set.range b₀)) U' → (∀ q ∈ S, M.lat q = L q ⊔ L' q) → ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W r = Submodule.span K {v | ∃ e ∈ L ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} ∧ ∀ s : Fin r, Y.IsDeg (L.gr b₀ s) (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) := by
  intro X Ω _ ξ K _ C z Y G _ _ V _ _ M Vz _ _ _ Mz h₀ h S L L' r r' b₀ U' hξ hs hz hS hb₀ hL hL' hc hΛ
  obtain ⟨U, hU, b, B, hB, hb, hfr⟩ := exists_frame hL hL' hc hΛ hz
  obtain ⟨fb, fB⟩ := hfr _ hz hU
  obtain ⟨β, hβ⟩ := frame_basis hξ hs M z h₀ Mz fB
  have hloc : ∀ i, ∃ (b : Fin r → V) (B : Fin (r + r') → V), (∀ k, B (Fin.castAdd r' k) = b k) ∧
      (∀ s, flagStep Ω b s = flagStep Ω b₀ s) ∧ L.IsFrameAt b ⟨_, h i⟩ ∧ M.lat.IsFrameAt B ⟨_, h i⟩ := fun i => by
    obtain ⟨U, hU, b, B, hB, hb, hfr⟩ := exists_frame hL hL' hc hΛ (hS i)
    exact ⟨b, B, hB, hb, hfr _ (hS i) hU⟩
  choose bi Bi hBi hbi fbi fBi using hloc
  choose βi hβi hlat using fun i => frame_lat hξ hs M Y Mz i (h i) (fBi i)
  have hbun : IsBun C (Y.lieLat Mz) := by
    have hn : Module.finrank K Vz = r + r' := by rw [Module.finrank_eq_card_basis β, Fintype.card_fin]
    rw [IsBun, hn]
    refine ⟨fun i => ⟨_, hlat i⟩, β, (Y.ae U hU).subset fun i hi hiU => hi ?_⟩
    obtain ⟨β', h1, h2⟩ := frame_lat hξ hs M Y Mz i (h i) (hfr _ (hS i) hiU).2
    have : β' = β := Module.Basis.eq_of_apply_eq fun q => Mz.inj ((h1 q).unique hξ (hβ q))
    exact this ▸ h2
  refine ⟨fun s => Submodule.span K (β '' {k | (k : ℕ) < s}), by simp, le_antisymm ?_ ?_, fun s => ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨B k, ?_, hβ k⟩
    rw [fb.2]
    exact Submodule.subset_span ⟨⟨k, hk⟩, (hB _).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro v ⟨e, he, hv⟩
    obtain ⟨c, hc1, hc2⟩ := val_coords hξ h₀ fB hβ hv
    have h1 : e ∈ flagStep Ω b r := by
      rw [fb.2] at he
      refine Submodule.span_subset_span _ Ω _ (Submodule.span_mono ?_ he)
      rintro _ ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    rw [flagStep_of_append hB le_rfl, hc1] at h1
    refine β.mem_span_image.2 fun l hl => ?_
    by_contra hcon
    have h2 := hc2 l
    rw [coord_zero fB.1 h1 hcon] at h2
    exact Finsupp.mem_support_iff.1 hl (LieTangent.valAt_unique hξ h2 (valAt_zero' h₀))
  · choose c hc1 hc2 using fun i k => val_coords hξ h₀ fB hβ (hβi i k)
    have hcz : ∀ i (k : Fin r) (l : Fin (r + r')), (k : ℕ) < l → c i (Fin.castAdd r' k) l = 0 := by
      intro i k l hl
      have h1 : bi i k ∈ flagStep Ω (bi i) (k + 1) := Submodule.subset_span ⟨k, Nat.lt_succ_self _, rfl⟩
      rw [hbi, ← hb, flagStep_of_append hB k.2, ← hBi, hc1] at h1
      exact coord_zero fB.1 h1 (Nat.not_lt.2 hl)
    obtain ⟨d1, d2, d3⟩ := subDeg_succ C hbun β βi hlat (Fin.castAdd r' s) fun i k l hk hl => by
      have h2 := hc2 i k l
      have hk' : (k : ℕ) < r := Nat.lt_of_le_of_lt hk s.2
      rw [show c i k l = 0 from hcz i ⟨k, hk'⟩ l hl] at h2
      exact LieTangent.valAt_unique hξ h2 (valAt_zero' h₀)
    obtain ⟨t, ht⟩ : ∃ t : Ω, b s - t • b₀ s ∈ flagStep Ω b₀ s := by
      have h1 : b s ∈ flagStep Ω b (s + 1) := Submodule.subset_span ⟨s, Nat.lt_succ_self _, rfl⟩
      have e : {k : Fin r | (k : ℕ) < s + 1} = insert s {k : Fin r | (k : ℕ) < s} := by
        ext k
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
        omega
      rw [hb, flagStep, e, Set.image_insert_eq, Submodule.mem_span_insert] at h1
      obtain ⟨t, y, hy, h1⟩ := h1
      exact ⟨t, by rw [h1, add_sub_cancel_left]; exact hy⟩
    have g0 := FlagGrGen.gr_isGenAt X Ω ξ V L r b₀ b _ s t hb₀ hb fb ht
    refine ⟨h₀, h, t, fun i => c i (Fin.castAdd r' s) (Fin.castAdd r' s) * t,
      fun i => β.repr (βi i (Fin.castAdd r' s)) (Fin.castAdd r' s), g0, fun i => ?_, fun i => ⟨d1 i, ?_⟩, d2, d3⟩
    · refine FlagGrGen.gr_isGenAt X Ω ξ V L r b₀ (bi i) _ s _ hb₀ (hbi i) (fbi i) ?_
      have h1 : bi i s - c i (Fin.castAdd r' s) (Fin.castAdd r' s) • b s ∈ flagStep Ω b₀ s := by
        rw [← hb, flagStep_of_append hB s.2.le, ← hBi, ← hB]
        nth_rw 1 [hc1]
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Fin.castAdd r' s)), add_sub_cancel_left]
        refine sum_mem fun l hl => ?_
        by_cases hls : (l : ℕ) < s
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, hls, rfl⟩)
        · have : (l : ℕ) ≠ s := fun e => (Finset.mem_erase.1 hl).1 (Fin.ext e)
          rw [hcz i s l (by omega), zero_smul]
          exact zero_mem _
      have h2 := add_mem h1 (Submodule.smul_mem _ (c i (Fin.castAdd r' s) (Fin.castAdd r' s)) ht)
      rwa [smul_sub, sub_add_sub_cancel, smul_smul] at h2
    · rw [mul_div_cancel_right₀ _ g0.1]
      exact hc2 i _ _

end PositivityTheory.HtPt.Ci
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieLatticeDegree

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace GlobalTheory.CompanionTheory.Ar.GrDeg

theorem grLine_deg_eq_sub : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ)) (L L' : Lat ξ V) (r r' : ℕ) (b₀ : Fin r → V) (U' : Submodule Ω V), IsCptGen ξ → Smooth G.hom → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → LinearIndependent Ω b₀ → L.IsFlagVBOn S b₀ → L'.IsVBOn S r' U' → IsCompl (Submodule.span Ω (Set.range b₀)) U' → (∀ q ∈ S, M.lat q = L q ⊔ L' q) → ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W r = Submodule.span K {v | ∃ e ∈ L ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} ∧ ∀ s : Fin r, Y.IsDeg (L.gr b₀ s) (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) :=
  PositivityTheory.HtPt.Ci.gr_deg

end GlobalTheory.CompanionTheory.Ar.GrDeg
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveLieLatticeDegreeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem _root_.GlobalTheory.T.curve_lie_lattice_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Field K] (C : ACurve K) (z : Spec (CommRingCat.of K) ⟶ X) (Y : CurveIn C z) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] [FiniteDimensional K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (h : ∀ i, genPt ξ ⤳ centre (Y.x i)) (S : Set (Cpt ξ)) (L L' : Lat ξ V) (r r' : ℕ) (b₀ : Fin r → V) (U' : Submodule Ω V), IsCptGen ξ → Smooth G.hom → (⟨centre z, h₀⟩ : Cpt ξ) ∈ S → (∀ i, (⟨centre (Y.x i), h i⟩ : Cpt ξ) ∈ S) → LinearIndependent Ω b₀ → L.IsFlagVBOn S b₀ → L'.IsVBOn S r' U' → IsCompl (Submodule.span Ω (Set.range b₀)) U' → (∀ q ∈ S, M.lat q = L q ⊔ L' q) → ∃ W : ℕ → Submodule K Vz, W 0 = ⊥ ∧ W r = Submodule.span K {v | ∃ e ∈ L ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} ∧ ∀ s : Fin r, Y.IsDeg (L.gr b₀ s) (subDeg C (Y.lieLat Mz) (W (s + 1)) - subDeg C (Y.lieLat Mz) (W s)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub | exact GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub | (intros; apply GlobalTheory.CompanionTheory.Ar.GrDeg.grLine_deg_eq_sub <;> assumption)
end
end
