module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsAdditiveLiStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfMemHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffPointwiseCoboundary

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullback

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem ev_triv_congr {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} (f : Z1 (O (dp0 R) s))
    {D D' : Type} [CommRing D] [CommRing D'] (i j : Algebra R D) (i' j' : Algebra R D') (hi : i = j) (hi' : i' = j')
    (x : Sp D ⟶ X) (x₁ x₂ : Sp D' ⟶ X) (hx₁ : x₁ = x₂)
    (hx : x ≫ s = spMap (@algebraMap R D _ _ i)) (hxj : x ≫ s = spMap (@algebraMap R D _ _ j))
    (hx' : x₁ ≫ s = spMap (@algebraMap R D' _ _ i')) (hxj' : x₂ ≫ s = spMap (@algebraMap R D' _ _ j'))
    (a : @Thick.triv R _ X s D _ i x hx ⟶ @Thick.triv R _ X s D' _ i' x₁ hx')
    (b : @Thick.triv R _ X s D _ j x hxj ⟶ @Thick.triv R _ X s D' _ j' x₂ hxj')
    (h : ∀ r, a.φ r = b.φ r) : ev f a = ev f b := by
  subst hi hi' hx₁
  have : a = b := Thick.Hom.ext' (AlgHom.ext h)
  subst this
  rfl

theorem ev_functor_map_trivMap {R : Type} [CommRing R] {X Y : Over (Sp R)} (q : Y ⟶ X)
    (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) q.left)
    (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [j : Algebra R D] (D' : Type) [CommRing D']
    [j' : Algebra R D'] (φ : D →ₐ[R] D') (y : Pt Y D) :
    ev f (m.functor.map (trivMap φ y)) = ev f (trivMap φ (y ≫ q)) := by
  let y' : Pt Y D' := spOver φ ≫ y
  have h : (y' ≫ q).left = (spOver φ ≫ y ≫ q).left :=
    congrArg (fun p : Pt X D' ↦ p.left) (Category.assoc (spOver φ) y q)
  exact ev_triv_congr f (((algebraMap R D).comp (RingHom.id R)).toAlgebra) j
    (((algebraMap R D').comp (RingHom.id R)).toAlgebra) j' (Algebra.algebra_ext _ _ fun _ ↦ rfl)
    (Algebra.algebra_ext _ _ fun _ ↦ rfl) (y ≫ q).left (y' ≫ q).left
    (spOver φ ≫ y ≫ q).left h (m.obj (trivAt y)).w (Pt.w (y ≫ q))
    (m.obj (trivAt y')).w (Pt.w (spOver φ ≫ y ≫ q))
    (m.functor.map (trivMap φ y)) (trivMap φ (y ≫ q)) fun _ ↦ rfl

theorem fv_pullbackOneCocycle_eq_pull : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (q : Y ⟶ X) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) q.left) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (m.coef.pullbackOneCocycle f) = (fv f).pull q := by
  intro R _ X Y q m f
  funext D _ _ D' _ _ φ y
  change ev f (m.functor.map (trivMap φ y)) = ev f (trivMap φ (y ≫ q))
  exact ev_functor_map_trivMap q m f D D' φ y

end GlobalTheory.PtExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnTrivialThickeningsPullbackStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback : ∀ (R : Type) [CommRing R] (X Y : Over (Sp R)) (q : Y ⟶ X) (m : IsMor (dp0 R) (X.hom ≫ 𝟙 _) (dp0 R) (Y.hom ≫ 𝟙 _) (RingHom.id R) q.left) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))), fv (m.coef.pullbackOneCocycle f) = (fv f).pull q := by
  first | exact @GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_pull | exact GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_pull | (intros; apply GlobalTheory.PtExt.fv_pullbackOneCocycle_eq_pull <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupPullbackCocyclesPointValue

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.cupZ_pull_apply_fv : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), (cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)).1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) = ψ (fv a E E' φ (z ≫ fst A B)) * fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
  intro R _ A B m₁ m₂ a b E _ _ E' _ _ E'' _ _ φ ψ z
  have e1 : fv (m₁.coef.pullbackOneCocycle a) E E' φ z = fv a E E' φ (z ≫ fst A B) := by
    rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback R A (A ⊗ B) (fst A B) m₁ a]; rfl
  have e2 : fv (m₂.coef.pullbackOneCocycle b) E' E'' ψ (spOver φ ≫ z) = fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
    rw [GlobalTheory.T.crystallineCocycleOnTrivialThickenings_pullback R B (A ⊗ B) (snd A B) m₂ b]; simp only [Fn1.pull, Category.assoc]
  rw [cupZ_apply]
  change ψ (fv (m₁.coef.pullbackOneCocycle a) E E' φ z) *
    fv (m₂.coef.pullbackOneCocycle b) E' E'' ψ (spOver φ ≫ z) = _
  rw [e1, e2]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupPullbackCocyclesPointValueStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.cup_pullback_cocycles_pointValue : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left) (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left) (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), (cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)).1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) = ψ (fv a E E' φ (z ≫ fst A B)) * fv b E' E'' ψ (spOver φ ≫ z ≫ snd A B) := by
  exact GlobalTheory.PtExt.cupZ_pull_apply_fv
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointwiseCochainCoboundaryEqChernCocycleAl

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem commAlgFunctorCoboundaryOne_apply_of_eq_sub_vanishing {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
    {m : C1 F} {z z' : C2 F} (h : d1 F m = z - z') {T T' T'' : C} (a : T ⟶ T') (b : T' ⟶ T'')
    (h0 : z' T T' T'' a b = 0) :
    mp F b (m T T' a) - m T T'' (a ≫ b) + m T' T'' b = z T T' T'' a b := by
  rw [← d1_apply, h]
  simp only [Pi.sub_apply, h0, sub_zero]

theorem exists_crystallineCochain_coboundary_eq_chernCocycle {R : Type} [CommRing R] {I : Ideal R} {g : DividedPowers I} {X : Scheme.{0}}
    {s : X ⟶ Sp R} {L : LB X} {w : Z2 (O g s)} (hw : IsChern g s L (CatCoh.H2.mk _ w)) :
    ∃ V : C1 (O g s), ∀ (T T' T'' : Thick g s) (a : T ⟶ T') (b : T' ⟶ T''), IsSmall g s L.U T → T''.J = ⊥ →
      d1 _ V T T' T'' a b = w.1 T T' T'' a b := by
  obtain ⟨i, hi, u, ℓ, hu, hℓ, hz⟩ := hw
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hz
  obtain ⟨m, hm⟩ := hz
  classical
  have sm : ∀ {T T' : Thick g s} (_ : T ⟶ T'), IsSmall g s L.U T → IsSmall g s L.U T' := by
    rintro T T' a ⟨j, hj⟩
    exact ⟨j, a.le_preimage hj⟩
  refine ⟨fun T T' a ↦ if h : IsSmall g s L.U T then m ⟨T, h⟩ ⟨T', sm a h⟩ (ObjectProperty.homMk a) else 0, ?_⟩
  intro T T' T'' a b h hJ
  have h1 := sm a h
  have h2 := sm b h1
  rw [d1_apply]
  simp only [dite_eq_left h, dite_eq_left h1]
  refine commAlgFunctorCoboundaryOne_apply_of_eq_sub_vanishing hm (T := ⟨T, h⟩) (T' := ⟨T', h1⟩) (T'' := ⟨T'', h2⟩) (ObjectProperty.homMk a)
    (ObjectProperty.homMk b) ?_
  have := (hℓ ⟨T, h⟩ ⟨T', h1⟩ ⟨T'', h2⟩ (ObjectProperty.homMk a) (ObjectProperty.homMk b)).1
  exact Ideal.mem_bot.1 (hJ.le this)

theorem exists_pt_d_eq_chern {R : Type} [CommRing R] {X : Over (Sp R)} {L : LB X.left}
    {w : Z2 (O (dp0 R) (X.hom ≫ 𝟙 _))} (hw : IsChern (dp0 R) _ L (CatCoh.H2.mk _ w)) :
    ∃ V : ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (z : Pt X E) (z' : Pt X E'),
      (trivAt z ⟶ trivAt z') → E',
      ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E'']
        [Algebra R E''] (z : Pt X E) (z' : Pt X E') (z'' : Pt X E'') (a : trivAt z ⟶ trivAt z')
        (b : trivAt z' ⟶ trivAt z'') (ψ : E' →ₐ[R] E''), b.φ = ψ → Sm L.U z →
        ψ (V E E' z z' a) - V E E'' z z'' (a ≫ b) + V E' E'' z' z'' b = w.1 _ _ _ a b := by
  obtain ⟨V, hV⟩ := exists_crystallineCochain_coboundary_eq_chernCocycle hw
  refine ⟨fun E _ _ E' _ _ z z' a ↦ V _ _ a, ?_⟩
  intro E _ _ E' _ _ E'' _ _ z z' z'' a b ψ hb hz
  subst ψ
  exact hV _ _ _ a b hz rfl

theorem exists_pointwiseCochain_coboundary_eq_chernCocycle : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (L : LB X.left) (w : Z2 (O (dp0 R) (X.hom ≫ 𝟙 _))), IsChern (dp0 R) _ L (CatCoh.H2.mk _ w) → ∃ n : Fn1 X, ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E''] [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt X E), Sm L.U z → ψ (n E E' φ z) - n E E'' (ψ.comp φ) z + n E' E'' ψ (spOver φ ≫ z) = w.1 _ _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) := by
  intro R _ X L w hw
  obtain ⟨V, hV⟩ := exists_pt_d_eq_chern hw
  refine ⟨fun E _ _ E' _ _ φ z ↦ V E E' z _ (trivMap φ z), ?_⟩
  intro E _ _ E' _ _ E'' _ _ φ ψ z hz
  have gen : ∀ (y : Pt X E'') (_ : y = spOver (ψ.comp φ) ≫ z) (f : trivAt z ⟶ trivAt y),
      (∀ c, f.φ c = ψ (φ c)) → V E E'' z _ (trivMap (ψ.comp φ) z) = V E E'' z y f := by
    intro y hy f hf
    subst hy
    exact congrArg (V E E'' z _) (Thick.Hom.ext' (AlgHom.ext fun c ↦ (hf c).symm))
  have hc := gen (spOver ψ ≫ spOver φ ≫ z) (by rw [← Category.assoc, spOver_comp])
    (trivMap φ z ≫ trivMap ψ (spOver φ ≫ z)) fun _ ↦ rfl
  have key := hV E E' E'' z _ _ (trivMap φ z) (trivMap ψ (spOver φ ≫ z)) ψ rfl hz
  rw [← hc] at key
  exact key

end GlobalTheory.PtExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationsOrthogonalLineBundlePairingProdu

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.HodgeOrth

theorem fv_sum {R : Type} [CommRing R] {X : Over (Sp R)} {J : Type} (s : Finset J) (c : J → R)
    (α : J → Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D']
    [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (∑ i ∈ s, c i • α i) D D' φ x = ∑ i ∈ s, fv (α i) D D' φ x * algebraMap R D' (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert i s hi ih =>
    obtain ⟨hadd, hsmul, _⟩ := GlobalTheory.T.crystallineCocycleOnTrivialThickenings_additive_linear R X
    rw [Finset.sum_insert hi, Finset.sum_insert hi, hadd, Fn1.add, hsmul, ih,
      mul_comm (algebraMap R D' (c i))]

theorem commAlgFunctorCocyclesTwo_finsetSum_apply {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) {J : Type}
    (s : Finset J) (w : J → Z2 F) (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    (∑ i ∈ s, w i).1 T T' T'' φ ψ = ∑ i ∈ s, (w i).1 T T' T'' φ ψ := by
  simp only [Submodule.coe_sum, Finset.sum_apply]

theorem sum_cup_eq_mk {R : Type} [CommRing R] {A B : Over (Sp R)} {N : ℕ}
    (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
    (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Fin N → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    (∑ k, cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ (α k)))
      (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ (β k)))) =
      CatCoh.H2.mk _ (∑ k, cupZ _ (m₁.coef.pullbackOneCocycle (α k)) (m₂.coef.pullbackOneCocycle (β k))) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← cup_mk]
  rfl

theorem exists_isCupCob {R : Type} [CommRing R] {A B : Over (Sp R)} {N : ℕ} (P : LB (A ⊗ B).left)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (β : Fin N → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (hc : IsChern (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) P
      (∑ k, cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ (α k)))
        (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ (β k))))) :
    ∃ n, IsCupCob P.U (fun i ↦ fv (α i)) (fun i ↦ fv (β i)) n := by
  have m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  rw [sum_cup_eq_mk m₁ m₂] at hc
  obtain ⟨n, hn⟩ := GlobalTheory.PtExt.exists_pointwiseCochain_coboundary_eq_chernCocycle R (A ⊗ B) P _ hc
  refine ⟨n, ?_⟩
  intro E _ _ E' _ _ E'' _ _ φ ψ z hz
  rw [hn E E' E'' φ ψ z hz, commAlgFunctorCocyclesTwo_finsetSum_apply]
  exact Finset.sum_congr rfl fun k _ ↦ GlobalTheory.T.cup_pullback_cocycles_pointValue R A B m₁ m₂ _ _ E E' E'' φ ψ z

theorem sum_mem_F1prim {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {N : ℕ} (a : Fin N → primDR A)
    (α : Fin N → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (hα : ∀ i, CatCoh.H1.mk _ (α i) = (a i).1) (c : Fin N → R)
    (k : Fn0 A)
    (hk : IsCob (whole A) (fun D _ _ D' _ _ φ x ↦ ∑ i, fv (α i) D D' φ x * algebraMap R D' (c i)) k) :
    ∑ i, c i • a i ∈ PrimitiveSubmodule A := by
  have hF : CatCoh.H1.mk _ (∑ i, c i • α i) ∈ F1 (A.hom ≫ 𝟙 _) := by
    have hfv : fv (∑ i, c i • α i) =
        ((fun D _ _ D' _ _ φ x ↦ ∑ i, fv (α i) D D' φ x * algebraMap R D' (c i)) : Fn1 A) := by
      funext D _ _ D' _ _ φ x
      exact fv_sum Finset.univ c α D D' φ x
    apply (mem_hodgeFiltration_iff_pointwiseCoboundary R A _).2
    rw [hfv]
    exact ⟨k, hk⟩

  rw [map_sum] at hF
  simp only [map_smul, hα] at hF

  rw [PrimitiveSubmodule, Submodule.mem_comap, map_sum]
  exact hF

theorem fil_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  intro H R _ A B _ _ g _ hB _ gB P hP φ hP' x hx y hy
  obtain ⟨N, a, b, hc, hφ⟩ := hP'
  choose α hα using fun k ↦ CatCoh.H1.mk_surjective _ (a k).1
  choose β hβ using fun k ↦ CatCoh.H1.mk_surjective _ (b k).1
  obtain ⟨n, hcup⟩ := exists_isCupCob P α β (by simp only [hα, hβ]; exact hc)
  have hβ' : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B := fun i ↦ by rw [hβ]; exact (b i).2
  obtain ⟨k, hk⟩ := GlobalTheory.PtExt.OrthPt.exists_isCob_of_mem_fil H R A B g hB gB _ P.U hP.cover (Fin N) _ β hβ' n
    (fun i ↦ (fv_isCoc_and_ev_eq R A (α i)).1) hcup y hy
  have eb : ∀ i, (⟨_, hβ' i⟩ : primDR B) = b i := fun i ↦ Subtype.ext (hβ i)
  have h0 := (Submodule.mem_dualAnnihilator _).1 hx _ (sum_mem_F1prim a α hα _ k hk)

  rw [hφ, ← h0, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [map_smul, smul_eq_mul, mul_comm, eb]

end GlobalTheory.PtExt.HodgeOrth
end
end
end
