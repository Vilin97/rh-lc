module

public import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionIsoOfGroupPullbackGeneric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PullQkSurjective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecScalOneVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEquivPoints

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LabMove

theorem exists_mulEquiv_points {S K K' X : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over K} [GrpObj A] {A' : Over K'}
    [GrpObj A'] {g : K ⟶ S} {g' : K' ⟶ S} {α : A.left ⟶ G.left} {α' : A'.left ⟶ G.left}
    (h : IsGrpPullback A G g α) (h' : IsGrpPullback A' G g' α') (t : X ⟶ K) (t' : X ⟶ K')
    (f : (Over.mk t' ⊗ A').left ⟶ (Over.mk t ⊗ A).left)
    (hf₁ : f ≫ (fst (Over.mk t) A).left = (fst (Over.mk t') A').left)
    (hf₂ : f ≫ (snd (Over.mk t) A).left ≫ α = (snd (Over.mk t') A').left ≫ α') :
    ∃ e : (Over.mk t' ⟶ A') ≃* (Over.mk t ⟶ A), ∀ x', (e x').left ≫ α = x'.left ≫ α' ∧
      (ptSecT A' x').left ≫ f = (ptSecT A (e x')).left := by
  have s₁ : ∀ {B : Scheme.{0}} {T Y : Over B} (x : T ⟶ Y), (ptSecT Y x).left ≫ (fst T Y).left = 𝟙 _ := fun x => by
    rw [← Over.comp_left, ptSecT, lift_fst]; rfl
  have s₂ : ∀ {B : Scheme.{0}} {T Y : Over B} (x : T ⟶ Y), (ptSecT Y x).left ≫ (snd T Y).left = x.left := fun x => by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have w : (snd (Over.mk t) A).left ≫ A.hom = (fst (Over.mk t) A).left ≫ t :=
    (Over.w (snd (Over.mk t) A)).trans (Over.w (fst (Over.mk t) A)).symm
  have w' : (snd (Over.mk t') A').left ≫ A'.hom = (fst (Over.mk t') A').left ≫ t' :=
    (Over.w (snd (Over.mk t') A')).trans (Over.w (fst (Over.mk t') A')).symm
  have hu : t' ≫ g' = t ≫ g := by
    have e := congrArg (fun q => (ptSecT A' (1 : Over.mk t' ⟶ A')).left ≫ q ≫ G.hom) hf₂
    simp only [Category.assoc] at e
    rw [h.1.w, h'.1.w, reassoc_of% w, reassoc_of% w', reassoc_of% hf₁, reassoc_of% (s₁ (1 : Over.mk t' ⟶ A')),
      reassoc_of% (s₁ (1 : Over.mk t' ⟶ A'))] at e
    exact e.symm
  obtain ⟨e, he⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback h t (t ≫ g) rfl
  obtain ⟨e', he'⟩ := GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback h' t' (t ≫ g) hu
  have key : ∀ x', ((e'.trans e.symm) x').left ≫ α = x'.left ≫ α' := fun x' => by
    rw [← he, ← he', MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  refine ⟨e'.trans e.symm, fun x' => ⟨key x', ?_⟩⟩
  have a₁ : ((ptSecT A' x').left ≫ f) ≫ (fst (Over.mk t) A).left =
      (ptSecT A ((e'.trans e.symm) x')).left ≫ (fst (Over.mk t) A).left := by
    rw [Category.assoc, hf₁, s₁, s₁]; rfl
  have a₂ : ((ptSecT A' x').left ≫ f) ≫ (snd (Over.mk t) A).left =
      (ptSecT A ((e'.trans e.symm) x')).left ≫ (snd (Over.mk t) A).left := by
    refine h.1.hom_ext ?_ ?_
    · rw [s₂, key, Category.assoc, Category.assoc, hf₂, reassoc_of% (s₂ x')]
    · rw [Category.assoc, w, Category.assoc _ _ A.hom, w, ← Category.assoc, a₁, Category.assoc]
  exact pullback.hom_ext a₁ a₂

end GlobalTheory.Mum.LabMove

namespace GlobalTheory.Mum

theorem Trait.exists_lab_push : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → (∀ x : TFK (R := W) F ⟶ T.A.A, x ^ (C.n ^ j) = 1 ↔ ∃ p', lab' p' = x) → ∃ lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A), LabExt em (C.lab j) lab ∧ (∀ x : TFK (R := R) F ⟶ C.A.A, x ^ (C.n ^ j) = 1 ↔ ∃ p, lab p = x) ∧ ∀ (p : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), p'.y = T.hD.xe.symm p.y → IsPullGtF T.φ T.hD F p.g p'.g → (ptSecT T.A.A (lab' p')).left ≫ f = (ptSecT C.A.A (lab p)).left := by
  intro R _ _ _ _ D C j W _ _ _ T F _ _ _ _ em hF f _ hf₁ hf₂ lab' hext honto
  have := T.U.gen_hom
  have : IsMonHom T.U.gen.symm.hom := by show IsMonHom T.U.gen.inv; infer_instance
  have gT : IsGrpPullback T.A.A C.G (jK W ≫ T.ξ) (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β) :=
    ((isGrpPullback_of_iso T.U.gen.symm).comp ((isGrpPullback_pullback T.G (jK W)).comp T.cart)).congr
      (Category.id_comp _) rfl
  obtain ⟨e, he⟩ := LabMove.exists_mulEquiv_points C.α_cart gT (jFK (R := R) F) (jFK (R := W) F) f hf₁ hf₂
  let P : QkPt D.toPre F (C.n ^ j) → QkPt T.D'.toPre F (C.n ^ j) :=
    GlobalTheory.ArcPull.pullQk T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  have hP : ∀ p p', p' = P p ↔ p'.y = T.hD.xe.symm p.y ∧ IsPullGtF T.φ T.hD F p.g p'.g :=
    GlobalTheory.ArcPull.eq_pullQk_iff T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  have hs : Function.Surjective P :=
    GlobalTheory.ArcPull.pullQk_surjective T.hD GlobalTheory.globalFns_holds hF D.tau_bimult T.D'.tau_bimult
  refine ⟨fun p => e (lab' (P p)), fun p p₁ hp => ?_, fun x => ?_, fun p p' hy hg => ?_⟩
  · refine C.α_cart.1.hom_ext ?_ ?_
    · rw [Category.assoc]
      exact (he _).1.trans (hext p p₁ (P p₁) hp ((hP _ _).1 rfl).1 ((hP _ _).1 rfl).2)
    · rw [Category.assoc, Over.w, Over.w]
      simp only [TFK, Over.mk_hom, jFK]
      rw [← Spec.map_comp]
      congr 1
      ext x
      simp
  · obtain ⟨x', rfl⟩ := e.surjective x
    rw [← map_pow, MulEquiv.map_eq_one_iff, honto, hs.exists]
    exact exists_congr fun p => e.injective.eq_iff.symm
  · obtain rfl := (hP p p').2 ⟨hy, hg⟩
    exact (he _).2

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitTransport

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open TopologicalSpace

namespace GlobalTheory.Mum.SecMove

section General

variable {X X' B : Scheme.{0}} {L : LB X} {L' : LB X'} {I : Type}

def Intertwine (L : LB X) (L' : LB X') (a : B ⟶ X) (a' : B ⟶ X') (pj : I → L.ι) (pk : I → L'.ι) (V : I → B.Opens)
    (u : ∀ i, Γ(B, V i)ˣ) : Prop :=
  (∀ i b, b ∈ V i → a b ∈ L.U (pj i) ∧ a' b ∈ L'.U (pk i)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ B) (z : Z) i i', r z ∈ V i → r z ∈ V i' →
      gm r z (V i) (u i) = gm (r ≫ a) z (L.U (pj i) ⊓ L.U (pj i')) (L.g (pj i) (pj i')) *
        (gm (r ≫ a') z (L'.U (pk i) ⊓ L'.U (pk i')) (L'.g (pk i) (pk i')))⁻¹ * gm r z (V i') (u i')

theorem Intertwine.symm {a : B ⟶ X} {a' : B ⟶ X'} {pj : I → L.ι} {pk : I → L'.ι} {V : I → B.Opens}
    {u : ∀ i, Γ(B, V i)ˣ} (H : Intertwine L L' a a' pj pk V u) : Intertwine L' L a' a pk pj V (fun i => (u i)⁻¹) := by
  refine ⟨fun i b hb => (H.1 i b hb).symm, fun Z r z i i' hi hi' => ?_⟩
  rw [map_inv, map_inv, H.2 Z r z i i' hi hi']
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem mem_one {Y : Scheme.{0}} {φ : Y ⟶ X} {y : Y} {j : Fin 1 → L.ι} :
    y ∈ LB.wchart L (fun _ : Fin 1 => φ) j ↔ φ y ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by rw [Subsingleton.elim k 0]; exact h⟩

theorem trF_one {Y Z : Scheme.{0}} (φ : Y ⟶ X) (N : ℕ) (r : Z ⟶ Y) (z : Z) (j j' : Fin 1 → L.ι) :
    trF (fun _ : Fin 1 => φ) (fun _ => (N : ℤ)) r z j j' =
      gm (r ≫ φ) z (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ N := by
  rw [trF, Fin.prod_univ_one, zpow_natCast]

theorem exists_move (hL : L.IsLB) {a : B ⟶ X} {a' : B ⟶ X'} {pj : I → L.ι} {pk : I → L'.ι} {V : I → B.Opens}
    {u : ∀ i, Γ(B, V i)ˣ} (H : Intertwine L L' a a' pj pk V u) (cov : ∀ b, ∃ i, b ∈ V i)
    {T S : Scheme.{0}} (m : T ⟶ B) (k : T ⟶ S) {ψ : T ⟶ X} {ψ' : S ⟶ X'} (hψ : m ≫ a = ψ) (hψ' : m ≫ a' = k ≫ ψ')
    (N : ℕ) (s : SecK L' ψ' N) : ∃ t : SecK L ψ N, ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) i, m (r z) ∈ V i →
      gs r z (LB.wchart L (fun _ : Fin 1 => ψ) (fun _ => pj i)) (t.f (fun _ => pj i)) =
        (gm (r ≫ m) z (V i) (u i) ^ N).val *
          gs (r ≫ k) z (LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i)) (s.f (fun _ => pk i)) := by
  have m₁ : ∀ i (y : T), m y ∈ V i → y ∈ LB.wchart L (fun _ : Fin 1 => ψ) (fun _ => pj i) := fun i y hy => by
    rw [mem_one, ← hψ]; exact (H.1 i _ hy).1
  have m₂ : ∀ i (y : T), m y ∈ V i → k y ∈ LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i) := fun i y hy => by
    rw [mem_one]
    have := (H.1 i _ hy).2
    rwa [show a' (m y) = ψ' (k y) from congrArg (fun q => q y) hψ'] at this
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) i i', m (r z) ∈ V i → m (r z) ∈ V i' →
      (gm (r ≫ m) z (V i) (u i) ^ N).val *
          gs (r ≫ k) z (LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i)) (s.f (fun _ => pk i)) =
      (trF (fun _ : Fin 1 => ψ) (fun _ => (N : ℤ)) r z (fun _ => pj i) (fun _ => pj i')).val *
        ((gm (r ≫ m) z (V i') (u i') ^ N).val *
          gs (r ≫ k) z (LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i')) (s.f (fun _ => pk i'))) := by
    intro Z r z i i' hi hi'
    rw [sec_trans s (r ≫ k) z (m₂ i _ hi) (m₂ i' _ hi'), trF_one, trF_one, H.2 Z (r ≫ m) z i i' hi hi',
      Category.assoc, Category.assoc, Category.assoc, hψ, hψ', ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
      ← Units.val_mul, ← mul_pow, ← mul_pow, mul_right_comm, inv_mul_cancel_right]
  have glue : ∀ p : Fin 1 → L.ι, ∃ t : Γ(T, LB.wchart L (fun _ : Fin 1 => ψ) p), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) i,
      r z ∈ LB.wchart L (fun _ : Fin 1 => ψ) p → m (r z) ∈ V i →
      gs r z _ t = (trF (fun _ : Fin 1 => ψ) (fun _ => (N : ℤ)) r z p (fun _ => pj i)).val *
        ((gm (r ≫ m) z (V i) (u i) ^ N).val *
          gs (r ≫ k) z (LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i)) (s.f (fun _ => pk i))) := by
    intro p
    let W : I → T.Opens := fun i => LB.wchart L (fun _ : Fin 1 => ψ) p ⊓ m ⁻¹ᵁ V i
    have l₁ : ∀ i, W i ≤ LB.wchart L (fun _ : Fin 1 => ψ) p ⊓ LB.wchart L (fun _ : Fin 1 => ψ) (fun _ => pj i) :=
      fun i y hy => ⟨hy.1, m₁ i y hy.2⟩
    have l₂ : ∀ i, W i ≤ k ⁻¹ᵁ LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i) := fun i y hy => m₂ i y hy.2
    obtain ⟨v, hv⟩ : ∃ v : ∀ i, Γ(T, W i), ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) i, r z ∈ W i →
        gs r z (W i) (v i) = (trF (fun _ : Fin 1 => ψ) (fun _ => (N : ℤ)) r z p (fun _ => pj i)).val *
        ((gm (r ≫ m) z (V i) (u i) ^ N).val *
          gs (r ≫ k) z (LB.wchart L' (fun _ : Fin 1 => ψ') (fun _ => pk i)) (s.f (fun _ => pk i))) :=
      ⟨fun i => (res (l₁ i) ((LB.LinComb L (fun _ : Fin 1 => ψ) (fun _ => (N : ℤ))).g p (fun _ => pj i))).val *
          ((res (inf_le_right : W i ≤ m ⁻¹ᵁ V i) (pullU m _ (u i)) ^ N).val *
            (T.presheaf.map (homOfLE (l₂ i)).op).hom ((k.app _).hom (s.f (fun _ => pk i)))),
        fun Z r z i hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_unit r z _ hz _).trans (congrArg Units.val ((gm_res r z _ hz _).trans
            (gm_linComb L _ _ r z _ _ (l₁ i hz).1 (l₁ i hz).2))))
          ((gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
            ((gs_unit r z _ hz _).trans (congrArg Units.val ((map_pow _ _ _).trans (congrArg (· ^ N)
              ((gm_res r z _ hz _).trans (gm_pull r m z _ hz.2 _))))))
            ((gs_res r z (l₂ i) hz _).trans (gs_pull r k z _ (l₂ i hz) _)))))⟩
    obtain ⟨t, ht, -⟩ := T.sheaf.existsUnique_gluing' W (LB.wchart L (fun _ : Fin 1 => ψ) p)
      (fun q => homOfLE inf_le_left) (fun y hy => by
        obtain ⟨i, hi⟩ := cov (m y)
        exact Opens.mem_iSup.2 ⟨i, hy, hi⟩) v
      (fun q q' => fn_ext (V := W q ⊓ W q') fun y hy => by
        refine (gs_res (𝟙 T) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 T) y inf_le_right hy _).symm)
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, key _ (𝟙 T) y q q' hy.1.2 hy.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          trF_trans hL _ _ (𝟙 T) y hy.1.1 (l₁ q hy.1).2 (l₁ q' hy.2).2])
    refine ⟨t, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gs_res r z inf_le_left hz t).symm.trans ((congrArg (gs r z (W q)) (ht q)).trans (hv Z r z q hz))
  choose t ht using glue
  refine ⟨⟨t, fun j j' => fn_ext fun y hy => ?_⟩, fun Z r z i hi => ?_⟩
  · obtain ⟨i, hi⟩ := cov (m y)
    refine (gs_res (𝟙 T) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 T) y _ hy _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 T) y _ hy _).trans (congrArg Units.val (gm_linComb L _ _ (𝟙 T) y j j' hy.1 hy.2)))
      (gs_res (𝟙 T) y _ hy _))).symm)
    refine (ht j _ (𝟙 T) y i hy.1 hi).trans (Eq.trans ?_ (congrArg _ (ht j' _ (𝟙 T) y i hy.2 hi)).symm)
    rw [← trF_trans hL _ _ (𝟙 T) y hy.1 hy.2 (m₁ i y hi), Units.val_mul, _root_.mul_assoc]; rfl
  · refine (ht _ Z r z i (m₁ i _ hi) hi).trans ?_
    rw [trF_self hL _ _ r z (m₁ i _ hi), Units.val_one, _root_.one_mul]

theorem exists_transport (hL : L.IsLB) (hL' : L'.IsLB) {Y : Scheme.{0}} (f : B ⟶ Y) [IsIso f] {φ : Y ⟶ X} {φ' : B ⟶ X'}
    {pj : I → L.ι} {pk : I → L'.ι} {V : I → B.Opens} {u : ∀ i, Γ(B, V i)ˣ} (H : Intertwine L L' (f ≫ φ) φ' pj pk V u)
    (cov : ∀ b j k, φ (f b) ∈ L.U j → φ' b ∈ L'.U k → ∃ i, pj i = j ∧ pk i = k ∧ b ∈ V i) (N : ℕ) :
    ∃ Tr : SecK L' φ' N → SecK L φ N, Function.Bijective Tr ∧
      (∀ σ σ' σ'' : SecK L' φ' N, (∀ i, σ''.f i = σ.f i + σ'.f i) → ∀ i, (Tr σ'').f i = (Tr σ).f i + (Tr σ').f i) ∧
      (∀ (e : Γ(Y, ⊤)) (σ σ' : SecK L' φ' N),
        (∀ i, σ'.f i = (B.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom e) * σ.f i) →
        ∀ i, (Tr σ').f i = (Y.presheaf.map (homOfLE le_top).op).hom e * (Tr σ).f i) ∧
      ∀ (σ : SecK L' φ' N) (Z : Scheme.{0}) (r : Z ⟶ B) (z : Z) i, r z ∈ V i →
        gs (r ≫ f) z (LB.wchart L (fun _ : Fin 1 => φ) (fun _ => pj i)) ((Tr σ).f (fun _ => pj i)) =
          (gm r z (V i) (u i) ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => φ') (fun _ => pk i)) (σ.f (fun _ => pk i)) := by
  have cov₀ : ∀ b, ∃ i, b ∈ V i := fun b => by
    obtain ⟨j, hj⟩ := exists_chart hL (φ (f b))
    obtain ⟨k, hk⟩ := exists_chart hL' (φ' b)
    obtain ⟨i, -, -, hi⟩ := cov b j k hj hk
    exact ⟨i, hi⟩
  have fi : ∀ b : B, (inv f) (f b) = b := fun b => congrArg (fun q => q b) (IsIso.hom_inv_id f)
  have fi' : ∀ y : Y, f ((inv f) y) = y := fun b => congrArg (fun q => q b) (IsIso.inv_hom_id f)
  choose Tr hT using fun σ : SecK L' φ' N => exists_move hL H cov₀ (inv f) (inv f) (ψ := φ) (ψ' := φ')
    (IsIso.inv_hom_id_assoc f φ) rfl N σ
  have hT' : ∀ (σ : SecK L' φ' N) (Z : Scheme.{0}) (r : Z ⟶ B) (z : Z) i, r z ∈ V i →
        gs (r ≫ f) z (LB.wchart L (fun _ : Fin 1 => φ) (fun _ => pj i)) ((Tr σ).f (fun _ => pj i)) =
          (gm r z (V i) (u i) ^ N).val * gs r z (LB.wchart L' (fun _ : Fin 1 => φ') (fun _ => pk i)) (σ.f (fun _ => pk i)) := by
    intro σ Z r z i hi
    have := hT σ Z (r ≫ f) z i (by show (inv f) (f (r z)) ∈ V i; rw [fi]; exact hi)
    rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at this
  have ext : ∀ (J : Fin 1 → L.ι) (s t : Γ(Y, LB.wchart L (fun _ : Fin 1 => φ) J)),
      (∀ (y : Y) i, (fun _ => pj i) = J → (inv f) y ∈ V i → gs (inv f ≫ f) y _ s = gs (inv f ≫ f) y _ t) → s = t := by
    intro J s t h
    refine fn_ext fun y hy => ?_
    obtain ⟨k, hk⟩ := exists_chart hL' (φ' (inv f y))
    obtain ⟨i, e, -, hi⟩ := cov (inv f y) (J 0) k (by rw [fi']; exact mem_one.1 hy) hk
    have := h y i (funext fun a => by rw [e, Subsingleton.elim a 0]) hi
    rwa [IsIso.inv_hom_id] at this
  have m₁ : ∀ i (y : Y), (inv f) y ∈ V i → (inv f ≫ f) y ∈ LB.wchart L (fun _ : Fin 1 => φ) (fun _ => pj i) :=
    fun i y hy => mem_one.2 (H.1 i _ hy).1
  have m₂ : ∀ i (b : B), b ∈ V i → b ∈ LB.wchart L' (fun _ : Fin 1 => φ') (fun _ => pk i) :=
    fun i y hy => mem_one.2 (H.1 i _ hy).2
  have sx : ∀ {T : Scheme.{0}} {M : LB T} (s t : LB.Sec M), s.f = t.f → s = t := by
    rintro T M ⟨s, _⟩ ⟨t, _⟩ h
    cases h; rfl
  refine ⟨Tr, ⟨fun σ σ' e => sx _ _ (funext fun J => fn_ext fun b hb => ?_), fun τ => ?_⟩,
    fun σ σ' σ'' h J => ext J _ _ ?_, fun e σ σ' h J => ext J _ _ ?_, hT'⟩
  · obtain ⟨j, hj⟩ := exists_chart hL (φ (f b))
    obtain ⟨i, -, ek, hi⟩ := cov b j (J 0) hj (mem_one.1 hb)
    obtain rfl : (fun _ => pk i) = J := funext fun a => by rw [ek, Subsingleton.elim a 0]
    have h₁ := hT' σ _ (𝟙 B) b i hi
    rw [e, hT' σ' _ (𝟙 B) b i hi] at h₁
    exact ((Units.mul_right_inj _).1 h₁).symm
  · obtain ⟨σ, hσ⟩ := exists_move hL' H.symm cov₀ (𝟙 B) f (ψ := φ') (ψ' := φ) (Category.id_comp _)
      (Category.id_comp _) N τ
    refine ⟨σ, sx _ _ (funext fun J => ext J _ _ ?_)⟩
    rintro y i rfl hi
    refine (hT' σ _ (inv f) y i hi).trans ?_
    rw [hσ _ (inv f) y i hi, Category.comp_id, map_inv, inv_pow, Units.mul_inv_cancel_left]
  · rintro y i rfl hi
    refine (hT' σ'' _ (inv f) y i hi).trans (Eq.trans ?_ (gs_add _ y _ (m₁ i y hi) _ _).symm)
    rw [hT' σ _ (inv f) y i hi, hT' σ' _ (inv f) y i hi, ← mul_add]
    exact congrArg _ ((congrArg _ (h _)).trans (gs_add _ y _ (m₂ i _ hi) _ _))
  · rintro y i rfl hi
    refine (hT' σ' _ (inv f) y i hi).trans (Eq.trans ?_ (gs_mul _ y _ (m₁ i y hi) _ _).symm)
    rw [hT' σ _ (inv f) y i hi, mul_left_comm]
    refine congrArg _ ((congrArg _ (h _)).trans ((gs_mul _ y _ (m₂ i _ hi) _ _).trans (congrArg₂ (· * ·) ?_ rfl)))
    exact (gs_res _ y _ (m₂ i _ hi) _).trans ((gs_pull (inv f) f y ⊤ trivial e).trans (gs_res _ y _ (m₁ i y hi) _).symm)

theorem exists_chain {XA XP XG XK Xt : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {Lt : LB Xt}
    {α : XA ⟶ XP} {β : XG ⟶ XP} {π : XK ⟶ XG} {gn : XK ⟶ Xt} {wA : LB.Iso LA (LP.pull α)} {ℓ : LB.Iso LG (LP.pull β)}
    {w₀ : LB.Iso (Lt.pull gn) (LG.pull π)} (hA : PGen wA) (hℓ : PGen ℓ) (h₀ : PGen w₀) (a : B ⟶ XA) (g : B ⟶ XK)
    (a' : B ⟶ Xt) (hgn : g ≫ gn = a') (hc : a ≫ α = g ≫ π ≫ β) :
    ∃ (V : LA.ι × LP.ι × LG.ι × Lt.ι → B.Opens) (u : ∀ i, Γ(B, V i)ˣ),
      Intertwine LA Lt a a' (fun i => i.1) (fun i => i.2.2.2) V u ∧
      (∀ i b, b ∈ V i ↔ a b ∈ LA.U i.1 ∧ α (a b) ∈ LP.U i.2.1 ∧ π (g b) ∈ LG.U i.2.2.1 ∧ a' b ∈ Lt.U i.2.2.2) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ B) (z : Z) i, r z ∈ V i → gm r z (V i) (u i) =
        (gw wA (r ≫ a) z i.2.1 i.1)⁻¹ * (gw ℓ (r ≫ g ≫ π) z i.2.1 i.2.2.1 * gw w₀ (r ≫ g) z i.2.2.1 (fun _ => i.2.2.2)) := by
  subst hgn
  have pc : ∀ b, α (a b) = β (π (g b)) := fun b => congrArg (fun q => q b) hc
  obtain ⟨V, hV⟩ : ∃ V : LA.ι × LP.ι × LG.ι × Lt.ι → B.Opens, ∀ i b,
      b ∈ V i ↔ a b ∈ LA.U i.1 ∧ α (a b) ∈ LP.U i.2.1 ∧ π (g b) ∈ LG.U i.2.2.1 ∧ (g ≫ gn) b ∈ Lt.U i.2.2.2 :=
    ⟨fun i => a ⁻¹ᵁ LA.U i.1 ⊓ (a ⁻¹ᵁ (α ⁻¹ᵁ LP.U i.2.1) ⊓ (g ⁻¹ᵁ (π ⁻¹ᵁ LG.U i.2.2.1) ⊓ (g ≫ gn) ⁻¹ᵁ Lt.U i.2.2.2)),
      fun _ _ => Iff.rfl⟩
  have l₁ : ∀ i, V i ≤ a ⁻¹ᵁ ((LP.pull α).U (fun _ => i.2.1) ⊓ LA.U i.1) := fun i x hx =>
    ⟨mem_pull.2 ((hV i x).1 hx).2.1, ((hV i x).1 hx).1⟩
  have l₂ : ∀ i, V i ≤ (g ≫ π) ⁻¹ᵁ ((LP.pull β).U (fun _ => i.2.1) ⊓ LG.U i.2.2.1) := fun i x hx =>
    ⟨mem_pull.2 (by have := ((hV i x).1 hx).2.1; rw [pc] at this; exact this), ((hV i x).1 hx).2.2.1⟩
  have l₃ : ∀ i, V i ≤ g ⁻¹ᵁ ((LG.pull π).U (fun _ => i.2.2.1) ⊓ (Lt.pull gn).U (fun _ => i.2.2.2)) := fun i x hx =>
    ⟨mem_pull.2 ((hV i x).1 hx).2.2.1, mem_pull.2 ((hV i x).1 hx).2.2.2⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ i, Γ(B, V i)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ B) (z : Z) i, r z ∈ V i → gm r z (V i) (u i) =
      (gw wA (r ≫ a) z i.2.1 i.1)⁻¹ * (gw ℓ (r ≫ g ≫ π) z i.2.1 i.2.2.1 * gw w₀ (r ≫ g) z i.2.2.1 (fun _ => i.2.2.2)) :=
    ⟨fun i => (res (l₁ i) (pullU a _ (wA.s (fun _ => i.2.1, i.1))))⁻¹ *
        (res (l₂ i) (pullU (g ≫ π) _ (ℓ.s (fun _ => i.2.1, i.2.2.1))) *
          res (l₃ i) (pullU g _ (w₀.s (fun _ => i.2.2.1, fun _ => i.2.2.2)))),
      fun Z r z i hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z (l₁ i) hz _).trans (gm_pull r a z _ (l₁ i hz) _))))
        ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z (l₂ i) hz _).trans (gm_pull r (g ≫ π) z _ (l₂ i hz) _))
          ((gm_res r z (l₃ i) hz _).trans (gm_pull r g z _ (l₃ i hz) _)))))⟩
  refine ⟨V, u, ⟨fun i b hb => ⟨((hV i b).1 hb).1, ((hV i b).1 hb).2.2.2⟩, fun Z r z i i' hi hi' => ?_⟩, hV, hu⟩
  have e₁ := hA Z (r ≫ a) z i.2.1 i'.2.1 i.1 i'.1 (mem_pull.1 (l₁ i hi).1) (mem_pull.1 (l₁ i' hi').1) (l₁ i hi).2 (l₁ i' hi').2
  have e₂ := hℓ Z (r ≫ g ≫ π) z i.2.1 i'.2.1 i.2.2.1 i'.2.2.1 (mem_pull.1 (l₂ i hi).1) (mem_pull.1 (l₂ i' hi').1)
    (l₂ i hi).2 (l₂ i' hi').2
  have e₃ := h₀ Z (r ≫ g) z i.2.2.1 i'.2.2.1 (fun _ => i.2.2.2) (fun _ => i'.2.2.2) (mem_pull.1 (l₃ i hi).1)
    (mem_pull.1 (l₃ i' hi').1) (l₃ i hi).2 (l₃ i' hi').2
  have e₄ := gm_linComb Lt (fun _ : PUnit => gn) (fun _ => 1) (r ≫ g) z (fun _ => i.2.2.2) (fun _ => i'.2.2.2)
    (l₃ i hi).2 (l₃ i' hi').2
  rw [Fintype.prod_unique, zpow_one, Category.assoc] at e₄
  replace e₃ := e₃.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl (congrArg (·⁻¹) e₄)) rfl)
  simp only [Category.assoc] at e₁ e₂ e₃
  rw [hc] at e₁
  rw [hu Z r z i hi, hu Z r z i' hi', e₁, e₂, e₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end General

theorem exists_trait_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∃ Tr : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j), Function.Bijective Tr ∧ (∀ σ σ' σ'' : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ i, σ''.f i = σ.f i + σ'.f i) → ∀ i, (Tr σ'').f i = (Tr σ).f i + (Tr σ').f i) ∧ (∀ (c : F) (σ σ' : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j)), (∀ i, σ'.f i = liftFun T.A.A _ (fnF (R := W) F c) * σ.f i) → ∀ i, (Tr σ').f i = liftFun C.A.A _ (fnF (R := R) F c) * (Tr σ).f i) ∧ ∀ σ : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (Tr σ) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) := by
  intro R _ _ _ _ D C j wA hwA W _ _ _ T F _ _ _ _ _ f _ hf hc w₀ hw₀
  have hg : ((snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) ≫ T.U.gen.hom.left = (snd (TFK (R := W) F) T.A.A).left := by
    rw [Category.assoc, ← Over.comp_left, Iso.inv_hom_id]; exact Category.comp_id _
  obtain ⟨V, u, H, hV, hu⟩ := exists_chain ((isGen_iff _).1 hwA) ((isGen_iff _).1 T.ℓ_gen) ((isGen_iff _).1 hw₀)
    (f ≫ (snd (TFK (R := R) F) C.A.A).left) ((snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) _ hg
    ((Category.assoc _ _ _).trans (hc.trans (Category.assoc _ _ _).symm))
  obtain ⟨Tr, h₁, h₂, h₃, h₄⟩ := exists_transport C.A.isLB T.A.isLB f H (fun b a t ha ht => by
    obtain ⟨p, hp⟩ := exists_chart C.P.L.isLB (C.α ((f ≫ (snd (TFK (R := R) F) C.A.A).left) b))
    obtain ⟨g, hg⟩ := exists_chart T.U.LG.isLB
      (pullback.fst T.G.hom (jK W) (((snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) b))
    exact ⟨(a, p, g, t), rfl, rfl, (hV _ b).2 ⟨ha, hp, hg, ht⟩⟩) (C.n ^ j)
  refine ⟨Tr, h₁, h₂, fun c σ σ' h => h₃ ((fst (TFK (R := R) F) C.A.A).left.appTop.hom (fnF (R := R) F c)) σ σ' (fun i => ?_), ?_⟩
  · refine (h i).trans (congrArg₂ (· * ·) ?_ rfl)
    exact (congrArg (fun q => ((TFK (R := W) F ⊗ T.A.A).left.presheaf.map (homOfLE le_top).op).hom
      (q.appTop.hom (fnF (R := W) F c))) hf).symm
  rintro σ Z p _ q rfl hp hq z JP JA JG Jt hP hA hG ht
  have e₀ : p ≫ T.β = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β :=
    hp.trans ((Category.assoc _ _ _).trans (congrArg (q ≫ ·) hc))
  obtain rfl : p = q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) := by
    refine T.cart.1.hom_ext (by simpa only [Category.assoc] using e₀) (hq.trans ?_)
    have c₁ : T.U.gen.inv.left ≫ pullback.snd T.G.hom (jK W) = T.A.A.hom := Over.w T.U.gen.inv
    have c₂ : (fst (TFK (R := W) F) T.A.A).left ≫ jFK (R := W) F = (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom :=
      pullback.condition
    have c₃ : pullback.fst T.G.hom (jK W) ≫ T.G.hom = pullback.snd T.G.hom (jK W) ≫ jK W := pullback.condition
    simp only [Category.assoc]
    rw [spMap_comp, c₃, reassoc_of% c₁, reassoc_of% c₂]
  have k₁ : (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.β =
      q ≫ (f ≫ (snd (TFK (R := R) F) C.A.A).left) ≫ C.α := by
    rw [hp]; simp only [Category.assoc]
  have hi := (hV (JA ((q ≫ f) ≫ (snd (TFK (R := R) F) C.A.A).left), JP ((q ≫ (snd (TFK (R := W) F) T.A.A).left ≫
    T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.β), JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫
    T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)), Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) (q z)).2
    ⟨hA _, by rw [k₁]; exact hP _, hG _, ht _⟩
  have e := h₄ σ Z q z _ hi
  rw [hu Z q z _ hi] at e
  refine (congrArg _ e).trans ?_
  simp only [Category.assoc, mul_pow, inv_pow, Units.val_mul]
  rw [_root_.mul_assoc, Units.mul_inv_cancel_left]
  rfl

end GlobalTheory.Mum.SecMove
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitEquivariantBijectionTransportCover

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem trait_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), Eqv T.D'.toPre T.A F (C.n ^ j) lab' E' → ∃ (lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A)) (E : Fam D.toPre F (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)) (Φ : Fam D.toPre F (C.n ^ j) → Fam T.D'.toPre F (C.n ^ j)), LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ (∀ (s : Fam D.toPre F (C.n ^ j)) (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)), F₀.Over s → (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((Φ s).s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1)) ∧ ∀ (s : Fam D.toPre F (C.n ^ j)) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' (Φ s)) q z Jt := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ em hc f hf hfst hα w₀ hw₀ lab' hlab' E' hE'
  obtain ⟨Φ, hΦb, hΦa, hΦs, hΦP, hΦp, hΦf⟩ := GlobalTheory.FamPull.fam_transport R D W T.φ T.D' T.hD F hc (C.n ^ j)
  obtain ⟨lab, hLE, hon, hlr⟩ := GlobalTheory.Mum.Trait.exists_lab_push R hR D C j W T F em hc f hf hfst hα lab' hlab' hE'.onto
  obtain ⟨Tr, hTb, hTa, hTs, hTv⟩ := GlobalTheory.Mum.SecMove.exists_trait_transport R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  have hC2 := GlobalTheory.T.transport_symmetric_lifts_theta_group_trait R hR D C j wA hwA W T F hc f hf hfst hα w₀ hw₀
  refine ⟨lab, fun s => Tr (E' (Φ s)), Φ, hLE, ⟨?_, ?_, ?_, hon, ?_, ?_, ?_⟩, hΦP, fun s => hTv (E' (Φ s))⟩
  · exact hTb.comp (hE'.bij.comp hΦb)
  · intro s s' s'' h i
    exact hTa _ _ _ (hE'.add _ _ _ (hΦa s s' s'' h)) i
  · intro c s s' h i
    exact hTs c _ _ (hE'.smul c _ _ (hΦs c s s' h)) i
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hΦf p p' hy hg).1 (hE'.frame p')
  · intro p
    obtain ⟨p', hy, hg⟩ := hΦp p
    exact (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).1 (hE'.lift p')
  · intro p w θ s s' hw hθ hr
    obtain ⟨p', hy, hg⟩ := hΦp p
    obtain ⟨w', hw', hr'⟩ := (hΦf p p' hy hg).2 w hw
    obtain ⟨θ', hθ', hact⟩ := (hC2 _ _ (hlr p p' hy hg) ((hE'.onto _).2 ⟨p', rfl⟩)).2 θ hθ
    exact hact _ _ _ _ (hTv _) (hTv _) (hE'.act p' w' θ' _ _ hw' hθ' (hr' s s' hr))

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitEquivariantBijectionTransportCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.trait_equivariant_bijection_transport_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F] (em : Kb R →ₐ[FractionRing R] F), (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ lab' : QkPt T.D'.toPre F (C.n ^ j) → (TFK (R := W) F ⟶ T.A.A), (∀ (p : QkPt D.toPre (Kb R) (C.n ^ j)) (p₁ : QkPt D.toPre F (C.n ^ j)) (p' : QkPt T.D'.toPre F (C.n ^ j)), QkExt em.toRingHom p p₁ → p'.y = T.hD.xe.symm p₁.y → IsPullGtF T.φ T.hD F p₁.g p'.g → (lab' p').left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β = spMap em.toRingHom ≫ (C.lab j p).left ≫ C.α) → ∀ E' : Fam T.D'.toPre F (C.n ^ j) → SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j), Eqv T.D'.toPre T.A F (C.n ^ j) lab' E' → ∃ (lab : QkPt D.toPre F (C.n ^ j) → (TFK (R := R) F ⟶ C.A.A)) (E : Fam D.toPre F (C.n ^ j) → SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)) (Φ : Fam D.toPre F (C.n ^ j) → Fam T.D'.toPre F (C.n ^ j)), LabExt em (C.lab j) lab ∧ Eqv D.toPre C.A F (C.n ^ j) lab E ∧ (∀ (s : Fam D.toPre F (C.n ^ j)) (F₀ : IntFam (maximalIdeal R) D.toPre (C.n ^ j)), F₀.Over s → (∀ f' : ∀ x, T.D'.toPre.SecB (C.n ^ j) x, (∀ x, PullB T.hD x (F₀.f (T.hD.xe x)) (f' x)) → ∀ x, GeneratorPullback.SecScal T.D'.toPre.P.L (DegPre.famφ T.D'.toPre F x) (DegPre.famε (C.n ^ j)) ((Φ s).s x) (T.D'.toPre.famφB x) (DegPre.famε (C.n ^ j)) (f' x) (DegPre.prB T.D'.toPre F).left 1)) ∧ ∀ (s : Fam D.toPre F (C.n ^ j)) (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval (E s) p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval (E' (Φ s)) q z Jt := by
  first | exact @GlobalTheory.Mum.trait_transport | exact GlobalTheory.Mum.trait_transport | (intros; apply GlobalTheory.Mum.trait_transport <;> assumption)
end
end
