module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsAbelianTripleIsoOfSamePointValuesStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFptsPull
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRigidifiedIsoAgreeAbelianFibresStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ObjMapUniqueOfIsDominant
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RepTransport
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOfSameRatios
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
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ObjMapIdCompCancel

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TripleIsoRespectsLevelRatioPoints

section

@[expose] public section

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.LevelRespect

open GlobalTheory.FibrePull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]

theorem valR_zero {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) : valR x U 0 = 0 := by
  unfold valR
  split_ifs
  · rw [map_zero, map_zero]
  · rfl

theorem sval_of_zero {A : Type} [CommRing A] {X Z : Scheme.{0}} {L : LB Z} {π : X ⟶ Z} {n : ℕ} (u : SecP L π n)
    (hu : ∀ i, u.f i = 0) (x : Sp A ⟶ X) (j : L.ι) : ArcPts.sval u x j = 0 :=
  (congrArg (valR x _) (hu fun _ => j)).trans (valR_zero _ _)

section One
variable {S : Scheme.{0}} {t : SAB H S} {F : Type} [Field F] {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V}
  {I : ℕ → Type} {φ : ∀ j, I j → V → F} {y : Sp F ⟶ S}

omit [StarRing (𝓞 E)] in
theorem fib_fst (a : Over.mk y ⟶ t.G) : fib a ≫ pullback.fst t.G.hom y = a.left := pullback.lift_fst _ _ _


omit [StarRing (𝓞 E)] in
theorem sval_eq_sum (Θ : FPts act t y φ) {k : ℕ} (hk : 1 ≤ k) (s : SecP t.PP.L (pullback.fst t.G.hom y) k) {n : ℕ}
    (r : Fin n → F) (i : Fin n → I k) (hs : ∀ v, HasVal s (fib (Θ.x v)) (Θ.τ v) (∑ a, r a * φ k (i a) v))
    (q : Over.mk y ⟶ t.G) (j : t.PP.L.ι) (hj : ⊤ ≤ q.left ⁻¹ᵁ t.PP.L.U j) :
    ArcPts.sval s (fib q) j = ∑ a, r a * ArcPts.sval (Θ.sig k (i a)) (fib q) j := by
  have key : ∀ (q : Over.mk y ⟶ t.G) (j : t.PP.L.ι), ⊤ ≤ (fib q ≫ pullback.fst t.G.hom y) ⁻¹ᵁ t.PP.L.U j →
      ArcPts.sval (FibreFrame.comb (pullback.snd t.G.hom y) (Fin.cons (-1) r : Fin (n + 1) → F)
        (Fin.cons s fun a => Θ.sig k (i a)) : SecP t.PP.L (pullback.fst t.G.hom y) k) (fib q) j =
      ∑ a, r a * ArcPts.sval (Θ.sig k (i a)) (fib q) j - ArcPts.sval s (fib q) j := fun q j hj => by
    rw [FibreFrame.sval_comb _ _ _ (RingHom.id F) (fib q)
      ((pullback.lift_snd _ _ _).trans (Spec.map_id _).symm) hj, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, RingHom.id_apply]
    ring
  have h0 := Θ.sep k hk _ fun v j hj => by
    rw [key _ j hj, hs v j hj, Finset.sum_mul, MulZeroClass.zero_mul, sub_eq_zero]
    exact Finset.sum_congr rfl fun a _ => by rw [Θ.val k hk (i a) v j hj, _root_.mul_assoc]
  have e := key q j (by rw [fib_fst]; exact hj)
  rw [sval_of_zero _ h0] at e
  exact (sub_eq_zero.1 e.symm).symm


omit [StarRing (𝓞 E)] in
theorem sval_lev (Θ : FPts act t y φ) {k : ℕ} (hk : 1 ≤ k) {p : Over.mk y ⟶ t.G} {ψ : I k → V → F}
    (hp : Θ.Lev k p ψ) (s : SecP t.PP.L (pullback.fst t.G.hom y) k) {n : ℕ}
    (r : Fin n → F) (i : Fin n → I k) (hs : ∀ v, HasVal s (fib (Θ.x v)) (Θ.τ v) (∑ a, r a * φ k (i a) v))
    (i₀ : I k) (z : V) (j : t.PP.L.ι) (hj : ⊤ ≤ (Θ.x z * p).left ⁻¹ᵁ t.PP.L.U j) :
    ArcPts.sval s (fib (Θ.x z * p)) j * ψ i₀ z =
      ArcPts.sval (Θ.sig k i₀) (fib (Θ.x z * p)) j * ∑ a, r a * ψ (i a) z := by
  rw [sval_eq_sum Θ hk s r i hs _ j hj, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by rw [_root_.mul_assoc, hp.2.2 (i a) i₀ z j hj]; ring

end One

theorem level_eq (h₁ : Out.Laws) (h₂ : Out.Laws2) {D : Datum H} {l : Level H} {B : Type} [CommRing B] {bb : Base l B}
    {S S' : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l bb s) {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' o.t f)
    (w : LB.Iso t'.PP.L (o.t.PP.L.pull m.φ)) (hw : w.IsGen) {F : Type} [Field F] [IsAlgClosed F] [CharZero F]
    {V : Type} [AddCommGroup V] {act : 𝓞 E → V → V} {I : ℕ → Type} {φ : ∀ j, I j → V → F} (y' : Sp F ⟶ S')
    (y : Sp F ⟶ S) (hy : y' ≫ f = y) (Θ' : FPts act t' y' φ) (Θ : FPts act o.t y φ) {k : ℕ} (hk : 1 ≤ k)
    {ψ : I k → V → F} {p' : Over.mk y' ⟶ t'.G} {p : Over.mk y ⟶ o.t.G}
    (rel : ∀ v, (Θ'.x v).left ≫ m.φ = (Θ.x v).left ∧ ∀ j j',
        ⊤ ≤ (Θ'.x v).left ⁻¹ᵁ (LB.div (o.t.PP.L.pull m.φ) t'.PP.L).U (fun _ => j, j') →
        Θ.τ v j = valR (Θ'.x v).left _ (w.s (fun _ => j, j')).val * Θ'.τ v j')
    (l' : Θ'.Lev k p' ψ) (l₀ : Θ.Lev k p ψ) : p'.left ≫ m.φ = p.left := by
  subst hy
  have hL := o.t.PP.isLB
  have hL' := t'.PP.isLB
  let ρ : (Over.mk y' ⟶ t'.G) →* (Over.mk (y' ≫ f) ⟶ o.t.G) := pushHom m.cart (Over.mk y')
  have ρl : ∀ x, (ρ x).left = x.left ≫ m.φ := fun _ => rfl
  have hx : ∀ v, ρ (Θ'.x v) = Θ.x v := fun v => Over.OverMorphism.ext (rel v).1
  have sq : IsPullback (pullback.fst t'.G.hom y' ≫ m.φ) (pullback.snd t'.G.hom y') o.t.G.hom (y' ≫ f) :=
    (IsPullback.of_hasPullback t'.G.hom y').paste_horiz m.cart.1
  let h : pullback t'.G.hom y' ⟶ pullback o.t.G.hom (y' ≫ f) := sq.isoPullback.hom
  have hp : pullback.fst t'.G.hom y' ≫ m.φ = h ≫ pullback.fst o.t.G.hom (y' ≫ f) := sq.isoPullback_hom_fst.symm
  have fh : ∀ a : Over.mk y' ⟶ t'.G, fib a ≫ h = fib (ρ a) := fun a => pullback.hom_ext
    (by rw [Category.assoc, ← hp, ← Category.assoc, fib_fst]; exact (pullback.lift_fst _ _ _).symm)
    (by rw [Category.assoc, sq.isoPullback_hom_snd]
        exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm)
  have hv : ∀ {a : SecP t'.PP.L (pullback.fst t'.G.hom y') k} {b : SecP o.t.PP.L (pullback.fst o.t.G.hom (y' ≫ f)) k},
      TransportedAlt w a b h → ∀ v c, HasVal a (fib (Θ'.x v)) (Θ'.τ v) c ↔ HasVal b (fib (Θ.x v)) (Θ.τ v) c := fun T v c => by
    rw [← hx v, ← fh]
    exact T.hasVal_iff hL hL' hp _ (by
      rw [fib_fst]; exact fun j j' hj hj' => (rel v).2 j j' ((le_div_iff _ j j').2 ⟨hj, hj'⟩)) c
  obtain ⟨-, i₀, i₁, hgood, z₀, hz₀⟩ := l₀.2.1
  have main := LevelUnique.torsion_eq_of_same_ratios h₁ h₂ E H D l B bb S s o F (y' ≫ f) V Θ.x k (ρ p') p
    (fun z => ψ i₀ z ≠ 0) (Θ.sig k i₁) hk (by rw [← map_pow, l'.1, map_one]) l₀.1
    (fun n hn u hu => Θ.sep n hn u fun v j hj => by
      rw [MulZeroClass.zero_mul]; exact hu v j (by rwa [fib_fst] at hj))
    (by
      by_contra hne
      push_neg at hne
      obtain ⟨j, hj⟩ := exists_chart_pt hL (Θ.x z₀).left
      have e := Θ.val k hk i₁ z₀ j (by rw [fib_fst]; exact hj)
      rw [sval_of_zero _ hne] at e
      exact mul_ne_zero hz₀ (pow_ne_zero _ ((Θ.frm z₀).1 j hj).ne_zero) e.symm)
    (fun v j hj hne => hgood v fun h0 => hne (by
      rw [Θ.val k hk i₁ v j (by rw [fib_fst]; exact hj), h0, MulZeroClass.zero_mul]))
    (fun z hz t₁ t₂ j j₂ hj hj₂ => by
      obtain ⟨j', hj'⟩ := exists_chart_pt hL' (Θ'.x z * p').left
      have hj₁ : ⊤ ≤ ((fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') ≫ m.φ) ⁻¹ᵁ o.t.PP.L.U j := by
        rw [fib_fst, ← ρl, map_mul, hx]; exact hj
      have hj₃ : ⊤ ≤ (fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') ⁻¹ᵁ t'.PP.L.U j' := by rw [fib_fst]; exact hj'
      have both : ∀ b : SecP o.t.PP.L (pullback.fst o.t.G.hom (y' ≫ f)) k, ∃ c : F,
          ArcPts.sval b (fib (Θ.x z * ρ p')) j * ψ i₀ z =
            wv w (fib (Θ'.x z * p') ≫ pullback.fst t'.G.hom y') j j' ^ k *
              ArcPts.sval (Θ'.sig k i₀) (fib (Θ'.x z * p')) j' * c ∧
          ArcPts.sval b (fib (Θ.x z * p)) j₂ * ψ i₀ z = ArcPts.sval (Θ.sig k i₀) (fib (Θ.x z * p)) j₂ * c := fun b => by
        obtain ⟨n, r, i, hi⟩ := Θ.span k hk b
        obtain ⟨a, ha⟩ := ConstFam.exists_secThrough (K := Fin 1) (φ' := fun _ => pullback.fst t'.G.hom y')
          hw hL hL' (fun _ => hp) b
        refine ⟨∑ a, r a * ψ (i a) z, ?_, sval_lev Θ hk l₀ b r i hi i₀ z j₂ hj₂⟩
        rw [← hx, ← map_mul, ← fh, TransportedAlt.sval_eq hp ha _ hj₁ hj₃, _root_.mul_assoc,
          sval_lev Θ' hk l' a r i (fun v => (hv ha v _).2 (hi v)) i₀ z j' hj', _root_.mul_assoc]
      obtain ⟨c₁, a₁, b₁⟩ := both t₁
      obtain ⟨c₂, a₂, b₂⟩ := both t₂
      refine mul_right_cancel₀ (mul_ne_zero hz hz) ?_
      rw [_root_.mul_mul_mul_comm, a₁, b₂, _root_.mul_mul_mul_comm (ArcPts.sval t₂ _ j), a₂, b₁]
      ring)
  exact congrArg (fun q => q.left) main

theorem level_pt_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ) (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)) (k : ℕ) (ψ : I k → V → F) (p₁ : Over.mk (𝟙 (Sp F)) ⟶ o₁.t.G) (p₂ : Over.mk (𝟙 (Sp F)) ⟶ o₂.t.G), 1 ≤ k → w.IsGen → (∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j') → Θ₁.Lev k p₁ ψ → Θ₂.Lev k p₂ ψ → p₁.left ≫ m.φ = p₂.left := by
  intro h₁ h₂ E _ _ _ H _ D l B _ bb F _ _ _ V _ act I φ s o₁ o₂ Θ₁ Θ₂ m w k ψ p₁ p₂ hk hw rel l₁ l₂
  exact level_eq h₁ h₂ o₂ m w hw (𝟙 _) (𝟙 _) (Category.id_comp _) Θ₁ Θ₂ hk rel l₁ l₂

end GlobalTheory.LevelRespect
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TripleIsoRespectsLevelRatioPointsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.triple_iso_respects_level_ratio_points : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (s : Sp F ⟶ Sp B) (o₁ o₂ : Obj D l bb s) (Θ₁ : FPts act o₁.t (𝟙 _) φ) (Θ₂ : FPts act o₂.t (𝟙 _) φ) (m : SABMap o₁.t o₂.t (𝟙 _)) (w : LB.Iso o₁.t.PP.L (o₂.t.PP.L.pull m.φ)) (k : ℕ) (ψ : I k → V → F) (p₁ : Over.mk (𝟙 (Sp F)) ⟶ o₁.t.G) (p₂ : Over.mk (𝟙 (Sp F)) ⟶ o₂.t.G), 1 ≤ k → w.IsGen → (∀ v, (Θ₁.x v).left ≫ m.φ = (Θ₂.x v).left ∧ ∀ j j', ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull m.φ) o₁.t.PP.L).U (fun _ => j, j') → Θ₂.τ v j = valR (Θ₁.x v).left _ (w.s (fun _ => j, j')).val * Θ₁.τ v j') → Θ₁.Lev k p₁ ψ → Θ₂.Lev k p₂ ψ → p₁.left ≫ m.φ = p₂.left := by
  first | exact @GlobalTheory.LevelRespect.level_pt_eq | exact GlobalTheory.LevelRespect.level_pt_eq | (intros; apply GlobalTheory.LevelRespect.level_pt_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointFamiliesEqOfValuesLevelsUniversalFamily

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.FamilyUnique

theorem isRigIso_iff {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G]
    [IsCommMonObj G] (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F)) :
    IsRigIso m L' L w ↔ PGen w ∧
      PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig m.e :=
  and_congr (isGen_iff w)
    (maps_iff w _ (fun _ => eSec G) _ L'.rig L.rig m.e _ (rigPull_le m.F m.e m.e_comm L.L) (fun _ => rfl))

theorem exists_rigIso_comp {S S' S'' : Scheme.{0}} {G'' : Over S''} {G' : Over S'} {G : Over S} [GrpObj G'']
    [IsCommMonObj G''] [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (m : CubeMap G' G)
    (m' : CubeMap G'' G') (n : CubeMap G'' G) (hF : n.F = m'.F ≫ m.F) (he : n.e = m'.e ≫ m.e)
    (L'' : RigLB G'') (L' : RigLB G') (L : RigLB G) (w : LB.Iso L'.L (L.L.pull m.F))
    (w' : LB.Iso L''.L (L'.L.pull m'.F)) (hw : IsRigIso m L' L w) (hw' : IsRigIso m' L'' L' w') :
    ∃ w'' : LB.Iso L''.L (L.L.pull n.F), IsRigIso n L'' L w'' ∧
      ∀ (F : Type) [Field F] (x : Sp F ⟶ G''.left) (x' : Sp F ⟶ G'.left) (j : L.L.ι) (i : L'.L.ι) (k : L''.L.ι),
        x ≫ m'.F = x' →
        ⊤ ≤ x' ⁻¹ᵁ (LB.div (L.L.pull m.F) L'.L).U (fun _ => j, i) →
        ⊤ ≤ x ⁻¹ᵁ (LB.div (L'.L.pull m'.F) L''.L).U (fun _ => i, k) →
        valR x _ (w''.s (fun _ => j, k)).val =
          valR x' _ (w.s (fun _ => j, i)).val * valR x _ (w'.s (fun _ => i, k)).val := by
  obtain ⟨Fn, F3, e, hec, hp⟩ := n
  dsimp only at hF he
  subst hF he
  rw [isRigIso_iff] at hw hw'
  obtain ⟨g, r⟩ := hw
  obtain ⟨g', r'⟩ := hw'
  obtain ⟨w'', T⟩ := exists_comp L'.isLB w w' g g' L.isLB L''.isLB
  refine ⟨w'', (isRigIso_iff _ _ _ _).2 ⟨T.pgen_comp L'.isLB g g', T.pmaps_comp L'.isLB (fun _ => m'.e_comm) r r'⟩, ?_⟩
  rintro F _ x x' j i k rfl h₁ h₂
  have a₁ := h₁ (show cpt F ∈ (⊤ : (Sp F).Opens) from trivial)
  have a₂ := h₂ (show cpt F ∈ (⊤ : (Sp F).Opens) from trivial)
  have hj : m.F (m'.F (x (cpt F))) ∈ L.L.U j := mem_pull.1 a₁.1
  have h₃ : ⊤ ≤ x ⁻¹ᵁ (LB.div (L.L.pull (m'.F ≫ m.F)) L''.L).U (fun _ => j, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull₂.2 hj, a₂.2⟩
  apply toStkA_injective
  rw [map_mul]
  exact (toStkA_valR x _ _ h₃ _).trans ((congrArg Units.val (T _ x (cpt F) j i k hj a₁.2 a₂.2)).trans
    (congrArg₂ (· * ·) (toStkA_valR _ _ _ h₁ _).symm (toStkA_valR _ _ _ h₂ _).symm))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_objMap_eq {D : Datum H} {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}}
    {s : S ⟶ Sp B} (o₁ o₂ : Obj D l b s) (m : SABMap o₁.t o₂.t (𝟙 S))
    (h₁ : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o₁.eta a).left ≫ m.φ = (o₂.eta a).left)
    (h₂ : ∀ a, (o₁.etaA a).left ≫ m.φ = (o₂.etaA a).left) : ∃ n : ObjMap o₁ o₂ (𝟙 S), n.toSABMap = m := by
  refine ⟨⟨m, fun a => ?_, fun a => (h₂ a).trans (Category.id_comp _).symm⟩, rfl⟩
  have ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]
    trivial
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.1 ha
  rw [o₁.eta_add, o₂.eta_add, o₁.eta_ker x hx, o₂.eta_ker x hx, _root_.one_mul, _root_.one_mul]
  exact (h₁ y hy).trans (Category.id_comp _).symm

theorem points_frames_eq : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (y₁ y₂ : Sp F ⟶ Xo.X) (Θ₁ : FPts act Xo.univ.t y₁ φ) (Θ₂ : FPts act Xo.univ.t y₂ φ), y₁ ≫ Xo.s = y₂ ≫ Xo.s → (∀ v, ∃ ψ, Θ₁.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ ∧ Θ₂.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ) → (∀ v ∈ idealPart D l, ∃ ψ, Θ₁.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ ∧ Θ₂.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ) → ∀ v, (Θ₁.x v).left = (Θ₂.x v).left ∧ ∀ j, ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Θ₁.τ v j = Θ₂.τ v j := by
  intro hL hL2 E _ _ _ H _ D l Xo F _ _ _ V _ act I φ y₁ y₂ Θ₁ Θ₂ hy hA hM
  obtain ⟨o₁, m₁, w₁, Θ₁', rw₁, p₁, lev₁⟩ :=
    GlobalTheory.FibrePull.exists_fpts_pull hL hL2 E H D l _ (baseKA l) F V act I φ _ Xo.s Xo.univ y₁ _ Θ₁ hy
  obtain ⟨o₂, m₂, w₂, Θ₂', rw₂, p₂, lev₂⟩ :=
    GlobalTheory.FibrePull.exists_fpts_pull hL hL2 E H D l _ (baseKA l) F V act I φ _ Xo.s Xo.univ y₂ _ Θ₂ rfl
  obtain ⟨m, w, rw₀, p⟩ := GlobalTheory.T.exists_abelianTriple_iso_of_same_point_values hL hL2 E H D l _ (baseKA l) F V act I φ _ o₁ o₂ Θ₁' Θ₂'
  have key : ∀ (k : ℕ) (x₁ : 𝟙_ (Over (Sp F)) ⟶ o₁.t.G) (x₂ : 𝟙_ (Over (Sp F)) ⟶ o₂.t.G)
      (x : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G), 1 ≤ k → x₁.left ≫ m₁.φ = y₁ ≫ x.left → x₂.left ≫ m₂.φ = y₂ ≫ x.left →
      (∃ ψ, Θ₁.Lev k (toUnit _ ≫ x) ψ ∧ Θ₂.Lev k (toUnit _ ≫ x) ψ) → x₁.left ≫ m.φ = x₂.left := by
    rintro k x₁ x₂ x hk k₁ k₂ ⟨ψ, a₁, a₂⟩
    exact GlobalTheory.T.triple_iso_respects_level_ratio_points hL hL2 E H D l _ (baseKA l) F V act I φ _ o₁ o₂ Θ₁' Θ₂' m w k ψ x₁ x₂ hk rw₀.1 p
      (lev₁ k ψ _ x₁ hk k₁ a₁) (lev₂ k ψ _ x₂ hk k₂ a₂)
  obtain ⟨n, rfl⟩ := exists_objMap_eq o₁ o₂ m
    (fun a ha => key l.M _ _ _ (le_trans (by norm_num) l.three_le) (m₁.eta a) (m₂.eta a) (hM a ha))
    (fun a => key l.A _ _ _ l.A_pos (m₁.etaA a) (m₂.etaA a) (hA a))
  obtain ⟨n', hn'⟩ := ObjComp.objMap_comp m₂ n
  have e : y₁ = 𝟙 _ ≫ y₂ := (Xo.rep _ _ inferInstance o₁).unique ⟨hy, ⟨m₁⟩⟩ ⟨by rw [Category.id_comp], ⟨n'⟩⟩
  subst e
  have hφ : m₁.toSABMap.φ = n.toSABMap.φ ≫ m₂.toSABMap.φ := (objMap_unique_of_field hL.serre m₁ n').trans hn'
  obtain ⟨w', rw', hval⟩ := exists_rigIso_comp m₂.cm n.cm m₁.cm hφ
    (m₁.base.trans (congrArg₂ (· ≫ ·) n.base m₂.base).symm) _ _ _ w₂ w rw₂ rw₀
  intro v
  have hx : (Θ₁.x v).left = (Θ₂.x v).left := by
    rw [← (p₁ v).1, ← (p₂ v).1, ← (p v).1, hφ, Category.assoc]
  refine ⟨hx, fun j hj => ?_⟩
  obtain ⟨k, hk⟩ := exists_chart o₁.t.PP.isLB ((Θ₁'.x v).left (cpt F))
  obtain ⟨i, hi⟩ := exists_chart o₂.t.PP.isLB ((Θ₂'.x v).left (cpt F))
  have hj₀ := (top_le_iff_cpt _ _).1 hj
  have c₁ : ⊤ ≤ (Θ₁'.x v).left ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull m₁.toSABMap.φ) o₁.t.PP.L).U (fun _ => j, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [← (p₁ v).1] at hj₀; exact hj₀), hk⟩
  have c₂ : ⊤ ≤ (Θ₂'.x v).left ⁻¹ᵁ (LB.div (Xo.univ.t.PP.L.pull m₂.toSABMap.φ) o₂.t.PP.L).U (fun _ => j, i) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [hx, ← (p₂ v).1] at hj₀; exact hj₀), hi⟩
  have c : ⊤ ≤ (Θ₁'.x v).left ⁻¹ᵁ (LB.div (o₂.t.PP.L.pull n.toSABMap.φ) o₁.t.PP.L).U (fun _ => i, k) :=
    (top_le_iff_cpt _ _).2 ⟨mem_pull.2 (by rw [← (p v).1] at hi; exact hi), hk⟩
  have := o₁.proper
  have u := (GlobalTheory.T.exists_rigidifiedIso_agree_abelianFibres hL hL2 E H _ _ Xo.univ.t o₁.t _ m₁.toSABMap).2 w₁ w' rw₁ rw' F (𝟙 _) (Θ₁'.x v)
    inferInstance j k c₁
  rw [(p₁ v).2 j k c₁, (p₂ v).2 j i c₂, (p v).2 i k c, ← _root_.mul_assoc]
  exact congrArg (· * _) (u.trans (hval F _ _ j i k (p v).1 c₂ c))

end GlobalTheory.FamilyUnique
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PointFamiliesEqOfValuesLevelsUniversalFamilyStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem _root_.GlobalTheory.T.pointFamilies_eq_of_values_levels_universalFamily : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (F : Type) [Field F] [IsAlgClosed F] [CharZero F] (V : Type) [AddCommGroup V] (act : 𝓞 E → V → V) (I : ℕ → Type) (φ : ∀ j, I j → V → F) (y₁ y₂ : Sp F ⟶ Xo.X) (Θ₁ : FPts act Xo.univ.t y₁ φ) (Θ₂ : FPts act Xo.univ.t y₂ φ), y₁ ≫ Xo.s = y₂ ≫ Xo.s → (∀ v, ∃ ψ, Θ₁.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ ∧ Θ₂.Lev l.A (toUnit _ ≫ Xo.univ.etaA v) ψ) → (∀ v ∈ idealPart D l, ∃ ψ, Θ₁.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ ∧ Θ₂.Lev l.M (toUnit _ ≫ Xo.univ.eta v) ψ) → ∀ v, (Θ₁.x v).left = (Θ₂.x v).left ∧ ∀ j, ⊤ ≤ (Θ₁.x v).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → Θ₁.τ v j = Θ₂.τ v j := by
  first | exact @GlobalTheory.FamilyUnique.points_frames_eq | exact GlobalTheory.FamilyUnique.points_frames_eq | (intros; apply GlobalTheory.FamilyUnique.points_frames_eq <;> assumption)
end
end
