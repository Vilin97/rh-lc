module

public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartSplitsByIdempotentMatricesDomainStatement
public import Mathlib.LinearAlgebra.Matrix.Rank
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.LocalRing.Module
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.DiagZEqNegAddY
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentCoordsBaseChangeSmoothCommGroupStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankCommonEigenspaceCoords
import Mathlib.Tactic.TypeStar

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankIdempotentMatrixLocalRingMapField

section

@[expose] public section

open Matrix

namespace GlobalTheory.IdemRankLocal

theorem exists_conj_diag (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ)
    (p : Matrix (Fin n) (Fin n) W) (hp : p * p = p) :
    ∃ (r : ℕ) (P P' : Matrix (Fin n) (Fin n) W), P * P' = 1 ∧
    p = P * Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) * P' := by
  classical
  set f : (Fin n → W) →ₗ[W] (Fin n → W) := Matrix.toLin' p with hfdef
  have hf : IsIdempotentElem f := by
    show f * f = f
    rw [Module.End.mul_eq_comp, hfdef, ← Matrix.toLin'_mul, hp]
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  haveI : Module.Projective W (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc x)
  haveI : Module.Projective W (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc.symm x)
  haveI : Module.Finite W (LinearMap.range f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc)
      (Submodule.linearProjOfIsCompl_surjective hc)
  haveI : Module.Finite W (LinearMap.ker f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (Submodule.linearProjOfIsCompl_surjective hc.symm)
  haveI : Module.Free W (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free W (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
  set r := Module.finrank W (LinearMap.range f)
  set s := Module.finrank W (LinearMap.ker f)
  let b1 := Module.finBasis W (LinearMap.range f)
  let b2 := Module.finBasis W (LinearMap.ker f)
  let bs : Module.Basis (Fin r ⊕ Fin s) W (Fin n → W) :=
    (b1.prod b2).map (Submodule.prodEquivOfIsCompl _ _ hc)
  have hrs : r + s = n := by
    have := Module.finrank_eq_card_basis bs
    simpa [Fintype.card_sum] using this.symm
  have hbs1 : ∀ i, f (bs (Sum.inl i)) = bs (Sum.inl i) := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
    obtain ⟨y, hy⟩ := (b1 i).2
    rw [← hy]
    exact LinearMap.congr_fun hf y
  have hbs2 : ∀ i, f (bs (Sum.inr i)) = 0 := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
  let b : Module.Basis (Fin n) W (Fin n → W) := bs.reindex (finSumFinEquiv.trans (finCongr hrs))
  have hb : ∀ j : Fin n, f (b j) = (if j.val < r then (1 : W) else 0) • b j := by
    intro j
    have hj : b j = bs ((finSumFinEquiv.trans (finCongr hrs)).symm j) := Module.Basis.reindex_apply _ _ _
    rw [hj]
    by_cases h : j.val < r
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inl ⟨j, h⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp
      rw [this, if_pos h, one_smul, hbs1]
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inr ⟨j.val - r, by omega⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp; omega
      rw [this, if_neg h, zero_smul, hbs2]
  have hdiag : LinearMap.toMatrix b b f = Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb j, map_smul, b.repr_self]
    by_cases hij : i = j
    · subst hij; simp; split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ hij, Finsupp.single_apply, Ne.symm hij]
      split_ifs <;> simp [Finsupp.single_apply, Ne.symm hij]
  let e := Pi.basisFun W (Fin n)
  refine ⟨r, e.toMatrix b, b.toMatrix e, ?_, ?_⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip e b
  · have := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e b e b f
    rw [← hdiag, this, LinearMap.toMatrix_eq_toMatrix', hfdef, LinearMap.toMatrix'_toLin']

theorem rank_map_const : ∀ (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ) (Q : Matrix (Fin n) (Fin n) W),
    Q * Q = Q → ∃ r : ℕ, ∀ (k : Type) [Field k] (β : W →+* k), (Q.map β).rank = r := by
  intro W _ _ n Q hQ
  classical
  obtain ⟨r, P, P', hPP', hQeq⟩ := exists_conj_diag W n Q hQ
  refine ⟨Fintype.card {i : Fin n // i.val < r}, fun k _ β => ?_⟩
  have hm : P.map β * P'.map β = 1 := by
    rw [← Matrix.map_mul, hPP', Matrix.map_one _ β.map_zero β.map_one]
  have hP : IsUnit (P.map β).det := Matrix.isUnit_det_of_right_inverse hm
  have hP' : IsUnit (P'.map β).det := Matrix.isUnit_det_of_left_inverse hm
  rw [hQeq, Matrix.map_mul, Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hP',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP, Matrix.diagonal_map β.map_zero,
    Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by split_ifs with h <;> simp [h]))

end GlobalTheory.IdemRankLocal
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankIdempotentMatrixLocalRingMapFieldStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.exists_rank_idempotent_matrix_local_ring_map_field : ∀ (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ) (Q : Matrix (Fin n) (Fin n) W), Q * Q = Q → ∃ r : ℕ, ∀ (k : Type) [Field k] (β : W →+* k), (Q.map β).rank = r := by
  first | exact @GlobalTheory.IdemRankLocal.rank_map_const | exact GlobalTheory.IdemRankLocal.rank_map_const | (intros; apply GlobalTheory.IdemRankLocal.rank_map_const <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultIffFinrankCommonEigenspaceCoordsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.lieMult_iff_finrank_common_eigenspace_coords : ∀ (W : Type) [CommRing W] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G] (O : Type) [CommRing O] (act : OAct O G) (n : ℕ) (k : Type) [Field k] (β : W →+* k) (T : (Fin n → k) → (epsPtR (spMap β) ⟶ G)) (A : O → Matrix (Fin n) (Fin n) k), Function.Injective T → (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) → (∀ c c', T (c + c') = T c * T c') → (∀ (s : k) c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) → (∀ a c, T c ≫ act.act a = T ((A a).mulVec c)) → ∀ (τ : O →+* k) (N : ℕ), LieMult act (spMap β) τ N ↔ Module.finrank k (⨅ a, LinearMap.ker (Matrix.mulVecLin (A a) - τ a • LinearMap.id) : Submodule k (Fin n → k)) = N := by
  first | (exact @GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig) | (exact GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig) | (intros; apply GlobalTheory.LieCoordMult.lieMult_iff_finrank_eig  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionExtendsAbelianSchemeDvr

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieExt

theorem prod_ofFn_eq {X : Type*} [Monoid X] {V : Type*} [AddCommMonoid V] (T : V → X)
    (h0 : T 0 = 1) (hadd : ∀ c c', T (c + c') = T c * T c') :
    ∀ {a : ℕ} (w : Fin a → V), (List.ofFn (fun i => T (w i))).prod = T (∑ i, w i)
  | 0, w => by simp [h0]
  | a + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_eq T h0 hadd (fun i => w i.succ), Fin.sum_univ_succ, hadd]

theorem lie_ext : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (ρ : W) (t : Fin D.a → (𝓞 D.F →+* W)), (∀ i, t i D.ω = ρ) → ρ ^ 2 - D.tr * ρ + D.nm = 0 → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((D.tr ^ 2 - 4 * D.nm : ℤ) : W) → (∀ (R' : Type) [CommRing R'] (β : L →+* R'), ∀ v : epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O D.ω) (β (algebraMap W L ρ)) v → ∃ w : Fin D.a → (epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O c) (β (algebraMap W L (t i c))) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k) i, LieMult (act.toF D) (spMap (β.comp (algebraMap W L))) ((β.comp (algebraMap W L)).comp (t i)) D.m) → (∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∀ v : epsPtR (spMap β) ⟶ G, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O D.ω) (β ρ) v → ∃ w : Fin D.a → (epsPtR (spMap β) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) (β (t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k) i, LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m := by
  intro p _ D W L _ _ _ _ _ _ G _ _ hab act ρ t htω hρ hcomax hdisc hgen hrank
  have hsm : Smooth G.hom := hab.smooth
  obtain ⟨n, M, hM⟩ := GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group W G hsm

  have hT0 : ∀ {X : Type} [Group X] {V : Type} [AddCommMonoid V] (T : V → X),
      (∀ c c', T (c + c') = T c * T c') → T 0 = 1 := fun T h => by
    have := h 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  obtain ⟨T₀, hinj₀, -, hadd₀, -, heq₀⟩ := hM W (RingHom.id W)
  have hmap : ∀ X : Matrix (Fin n) (Fin n) W, X.map (RingHom.id W) = X := fun X => by ext; simp
  have hext : ∀ X Y : Matrix (Fin n) (Fin n) W, (∀ c, T₀ (X.mulVec c) = T₀ (Y.mulVec c)) → X = Y := by
    intro X Y h
    ext i j
    have := congrFun (hinj₀ (h (Pi.single j 1))) i
    simpa [Matrix.mulVec_single_one] using this
  let Am : 𝓞 D.F → Matrix (Fin n) (Fin n) W := fun c => M (act.act (algebraMap (𝓞 D.F) D.O c))
  have hAm : ∀ c x, T₀ x ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T₀ ((Am c).mulVec x) := fun c x => by
    simpa [hmap] using heq₀ _ (act.hom _) x
  let A : 𝓞 D.F →+* Matrix (Fin n) (Fin n) W := RingHom.mk'
    { toFun := Am
      map_one' := hext _ _ fun x => by
        rw [Matrix.one_mulVec, ← hAm, map_one, act.one, Category.comp_id]
      map_mul' := fun c d => hext _ _ fun x => by
        rw [← hAm, map_mul, act.mul, ← Category.assoc, hAm, hAm, Matrix.mulVec_mulVec] }
    (fun c d => hext _ _ fun x => by
      show T₀ ((Am (c + d)).mulVec x) = T₀ ((Am c + Am d).mulVec x)
      rw [← hAm, map_add (f := _), act.add, MonObj.comp_mul, hAm, hAm, ← hadd₀, Matrix.add_mulVec])
  have hA : ∀ c, A c = M (act.act (algebraMap (𝓞 D.F) D.O c)) := fun c => rfl

  have tanT : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (T : (Fin n → R') → (epsPtR (spMap β) ⟶ G)),
      Function.Injective T →
      (∀ (s : R') c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) →
      (∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c)) →
      (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
        (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) →
      ∀ (c : 𝓞 D.F) (s : R') (x : Fin n → R'),
        IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) s (T x) ↔ ((A c).map β).mulVec x = s • x := by
    intro R' _ β T hinj hscale heq hrange c s x
    have hact : T x ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T (((A c).map β).mulVec x) :=
      heq _ (act.hom _) x
    constructor
    · rintro ⟨-, h2⟩
      refine hinj (Over.OverMorphism.ext ?_)
      rw [← hact, h2, hscale]
    · intro hx
      refine ⟨(hrange _).2 ⟨x, rfl⟩, ?_⟩
      rw [hact, hx, hscale]
  have hωroot : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hβL : (RingHom.id L).comp (algebraMap W L) = algebraMap W L := RingHom.id_comp _
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := GlobalTheory.T.eigenPart_splits_by_idempotent_matrices_domain W L (𝓞 D.F) n D.a A D.ω D.tr D.nm ρ t hωroot hρ htω hcomax hdisc
    (by
      intro v hv
      obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM L ((RingHom.id L).comp (algebraMap W L))
      have tv := (tanT L _ T hinj hscale heq hrange D.ω ((RingHom.id L) (algebraMap W L ρ)) v).2
        (by rw [hβL, RingHom.id_apply]; exact hv)
      obtain ⟨w, hw, hvw⟩ := hgen L (RingHom.id L) (T v) tv
      have hy : ∀ i, ∃ y, w i = T y := fun i => by obtain ⟨y, h⟩ := (hrange _).1 (hw i 0).1; exact ⟨y, h.symm⟩
      choose y hy using hy
      refine ⟨y, fun i c => ?_, ?_⟩
      · have := (tanT L _ T hinj hscale heq hrange c _ (y i)).1 (by rw [← hy]; exact hw i c)
        rwa [hβL, RingHom.id_apply] at this
      · apply hinj
        rw [hvw, ← prod_ofFn_eq T (hT0 T hadd) hadd]
        exact congrArg List.prod (congrArg List.ofFn (funext hy)))
  have hmapsmul : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (s : W) (X : Matrix (Fin n) (Fin n) W),
      (s • X).map β = β s • X.map β := fun R' _ β s X => by ext; simp
  have heig : ∀ (R' : Type) [CommRing R'] (β : W →+* R') i c (x : Fin n → R'),
      ((A c).map β).mulVec (((Q i).map β).mulVec x) = β (t i c) • (((Q i).map β).mulVec x) := by
    intro R' _ β i c x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQ2, hmapsmul, Matrix.smul_mulVec]

  have rk : ∀ (k : Type) [Field k] (β : W →+* k) i,
      LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m ↔ ((Q i).map β).rank = D.m := by
    intro k _ β i
    obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM k β
    rw [GlobalTheory.T.lieMult_iff_finrank_common_eigenspace_coords W G (𝓞 D.F) (act.toF D) n k β T (fun c => (A c).map β) hinj hrange hadd hscale
      (fun c x => heq _ (act.hom _) x)]
    have hsub : (⨅ c, LinearMap.ker (Matrix.mulVecLin ((A c).map β) - (β.comp (t i)) c • LinearMap.id) :
        Submodule k (Fin n → k)) = LinearMap.range ((Q i).map β).mulVecLin := by
      ext y
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range, RingHom.comp_apply]
      constructor
      · intro h
        exact ⟨y, hQ4 k β i y h⟩
      · rintro ⟨z, rfl⟩ c
        exact heig k β i c z
    rw [hsub, Matrix.finrank_range_mulVecLin]
  refine ⟨fun R' _ β v hv => ?_, fun k _ _ β i => ?_⟩
  · obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM R' β
    obtain ⟨x, rfl⟩ := (hrange v).1 hv.1
    have hx := (tanT R' β T hinj hscale heq hrange D.ω (β ρ) x).1 hv
    refine ⟨fun i => T (((Q i).map β).mulVec x), fun i c =>
      (tanT R' β T hinj hscale heq hrange c _ _).2 (heig R' β i c x), ?_⟩
    rw [prod_ofFn_eq T (hT0 T hadd) hadd, ← hQ3 R' β x hx]
  · obtain ⟨r, hr⟩ := GlobalTheory.T.exists_rank_idempotent_matrix_local_ring_map_field W n (Q i) (hQ1 i)
    refine (rk k β i).2 ?_
    rw [hr, ← hr (AlgebraicClosure L) ((algebraMap L (AlgebraicClosure L)).comp (algebraMap W L))]
    exact (rk _ _ i).1 (hrank (AlgebraicClosure L) (algebraMap L (AlgebraicClosure L)) i)

end GlobalTheory.LieExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionExtendsAbelianSchemeDvrStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_extends_abelianScheme_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (ρ : W) (t : Fin D.a → (𝓞 D.F →+* W)), (∀ i, t i D.ω = ρ) → ρ ^ 2 - D.tr * ρ + D.nm = 0 → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((D.tr ^ 2 - 4 * D.nm : ℤ) : W) → (∀ (R' : Type) [CommRing R'] (β : L →+* R'), ∀ v : epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O D.ω) (β (algebraMap W L ρ)) v → ∃ w : Fin D.a → (epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O c) (β (algebraMap W L (t i c))) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k) i, LieMult (act.toF D) (spMap (β.comp (algebraMap W L))) ((β.comp (algebraMap W L)).comp (t i)) D.m) → (∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∀ v : epsPtR (spMap β) ⟶ G, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O D.ω) (β ρ) v → ∃ w : Fin D.a → (epsPtR (spMap β) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) (β (t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k) i, LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m := by
  first | exact @GlobalTheory.LieExt.lie_ext | exact GlobalTheory.LieExt.lie_ext | (intros; apply GlobalTheory.LieExt.lie_ext <;> assumption)
end
end
