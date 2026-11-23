module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.IsTautologicalLineAt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeometricGenericComponents
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocExactC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdealStatement
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.CechDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.RSubOneMem
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PowKNeZeroOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ResidStmt

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocExactB

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.LX

variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C]
  {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

def epsE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c c' : C} (φ : c ⟶ c') : (g.obj c').Bˣ :=
  Λ.w φ ^ e * v c' * (Units.map (g.map φ).φ.toMonoidHom (v c))⁻¹

def bE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) : CH.Cn (g ⋙ O (smFun X q)) 1 :=
  fun τ => (show (g.obj (τ.obj (Fin.last 1))).B from
    plogK (g.obj (τ.obj (Fin.last 1))).δ s (((epsE Λ v e (τ.map' 0 1) : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
      (g.obj (τ.obj (Fin.last 1))).B) - 1))

theorem grpE_add {G : Type} [AddCommGroup G] (a b c x y z : G) (e : ℕ) :
    e • a + y + -z + (e • b + x + -y) + -(e • c + x + -z) = e • (a + b + -c) := by
  simp only [smul_add, smul_neg]; abel

theorem grpE {G : Type} [CommGroup G] (a b c x y z : G) (e : ℕ) :
    a ^ e * y * z⁻¹ * (b ^ e * x * y⁻¹) * (c ^ e * x * z⁻¹)⁻¹ = (a * b * c⁻¹) ^ e :=
  @grpE_add (Additive G) _ a b c x y z e

theorem grpS_add {G : Type} [AddCommGroup G] (a x x' y y' : G) :
    (a + x + -y) + -(a + x' + -y') = (x + -x') + -(y + -y') := by abel

theorem grpS {G : Type} [CommGroup G] (a x x' y y' : G) :
    (a * x * y⁻¹) * (a * x' * y'⁻¹)⁻¹ = (x * x'⁻¹) * (y * y'⁻¹)⁻¹ :=
  @grpS_add (Additive G) _ a x x' y y'

theorem plog_pow [CharZero K] (T : Thick (smFun X q)) (s : ℕ) (hs : T.pdPow s = ⊥) (a : T.Bˣ)
    (ha : (a : T.B) - 1 ∈ T.J) (n : ℕ) :
    ((a ^ n : T.Bˣ) : T.B) - 1 ∈ T.J ∧
      plogK T.δ s (((a ^ n : T.Bˣ) : T.B) - 1) = n • plogK T.δ s ((a : T.B) - 1) := by
  induction n with
  | zero => simp [GlobalTheory.CompanionTheory.ConeZcls.plogK_zero, T.J.zero_mem]
  | succ n ih =>
    rw [pow_succ]
    refine ⟨GlobalTheory.CompanionTheory.ConeZcls.mul_sub_mem T _ _ ih.1 ha, ?_⟩
    rw [GlobalTheory.CompanionTheory.ConeZcls.plog_mul T s hs _ _ ih.1 ha, ih.2, succ_nsmul]

theorem epsE_rr (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂)
    (χ : c₀ ⟶ c₂) (hχ : χ = φ ≫ ψ) :
    Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) * epsE Λ v e ψ * (epsE Λ v e χ)⁻¹ =
      GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ ^ e := by
  subst hχ
  have h : Units.map (g.map (φ ≫ ψ)).φ.toMonoidHom (v c₀) =
      Units.map (g.map ψ).φ.toMonoidHom (Units.map (g.map φ).φ.toMonoidHom (v c₀)) := by
    rw [g.map_comp]; rfl
  unfold epsE GlobalTheory.CompanionTheory.ConeZcls.rr
  rw [h]
  simp only [map_mul, map_inv, map_pow]
  exact grpE _ _ _ _ _ _ e

def lE (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) {c c' : C} (φ : c ⟶ c') : (g.obj c').B :=
  plogK (g.obj c').δ s (((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1)

theorem log_rr [CharZero K] (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    {c₀ c₁ c₂ : C} (φ : c₀ ⟶ c₁) (ψ : c₁ ⟶ c₂) (χ : c₀ ⟶ c₂) (hχ : χ = φ ≫ ψ)
    (hr : ((GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈ (g.obj c₂).J) :
    e • plogK (g.obj c₂).δ s (((GlobalTheory.CompanionTheory.ConeZcls.rr Λ φ ψ χ : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1) =
      (g.map ψ).φ (lE Λ v e s φ) + lE Λ v e s ψ - lE Λ v e s χ := by
  have e0 := hε φ
  have e1 := hε ψ
  have e2 := hε χ
  have e0' : ((Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) : (g.obj c₂).Bˣ) : (g.obj c₂).B) - 1 ∈ (g.obj c₂).J := by
    have := (g.map ψ).hle e0
    simpa using this
  have hm : plogK (g.obj c₂).δ s (((Units.map (g.map ψ).φ.toMonoidHom (epsE Λ v e φ) : (g.obj c₂).Bˣ) :
      (g.obj c₂).B) - 1) = (g.map ψ).φ (lE Λ v e s φ) := by
    unfold lE
    rw [GlobalTheory.CompanionTheory.ConeZcls.plogK_map (g.map ψ) s e0]
    simp
  rw [← (plog_pow (g.obj c₂) s (hs _) _ hr e).2, ← epsE_rr Λ v e φ ψ χ hχ,
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ (GlobalTheory.CompanionTheory.ConeZcls.mul_sub_mem _ _ _ e0' e1)
      (GlobalTheory.CompanionTheory.ConeZcls.inv_sub _ _ e2),
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ e0' e1, GlobalTheory.CompanionTheory.ConeZcls.plog_inv _ s (hs _) _ e2, hm]
  unfold lE
  ring

theorem epsE_div (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e : ℕ) {c c' : C} (φ : c ⟶ c') :
    epsE Λ v e φ * (epsE Λ v' e φ)⁻¹ =
      (v c' * (v' c')⁻¹) * (Units.map (g.map φ).φ.toMonoidHom (v c * (v' c)⁻¹))⁻¹ := by
  unfold epsE
  simp only [map_mul, map_inv]
  exact grpS _ _ _ _ _

theorem lE_sub [CharZero K] (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    {c c' : C} (φ : c ⟶ c')
    (e1 : ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (e2 : ((epsE Λ v' e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J) :
    lE Λ v e s φ - lE Λ v' e s φ =
      plogK (g.obj c').δ s (((v c' * (v' c')⁻¹ : (g.obj c').Bˣ) : (g.obj c').B) *
        Ring.inverse ((g.map φ).φ (((v c * (v' c)⁻¹ : (g.obj c).Bˣ) : (g.obj c).B))) - 1) := by
  have hR : Ring.inverse ((g.map φ).φ (((v c * (v' c)⁻¹ : (g.obj c).Bˣ) : (g.obj c).B))) =
      (((Units.map (g.map φ).φ.toMonoidHom (v c * (v' c)⁻¹))⁻¹ : (g.obj c').Bˣ) : (g.obj c').B) := by
    rw [← Ring.inverse_unit]; rfl
  unfold lE
  rw [hR, ← Units.val_mul, ← epsE_div Λ v v' e φ,
    GlobalTheory.CompanionTheory.ConeZcls.plog_mul _ s (hs _) _ _ e1 (GlobalTheory.CompanionTheory.ConeZcls.inv_sub _ _ e2),
    GlobalTheory.CompanionTheory.ConeZcls.plog_inv _ s (hs _) _ e2, sub_eq_add_neg]

theorem zK_smul_eq_d [CharZero K] (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J) :
    e • zK Λ s = CH.d _ 1 (bE Λ v e s) := by
  funext σ
  have hr : ((GlobalTheory.CompanionTheory.ConeZcls.rr Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) : (g.obj (σ.obj (Fin.last 2))).Bˣ) :
      (g.obj (σ.obj (Fin.last 2))).B) - 1 ∈ (g.obj (σ.obj (Fin.last 2))).J := GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ
  have key := log_rr Λ v e s hs hε (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) (GlobalTheory.CompanionTheory.ConeZcls.composable_arrows_map_zero_two σ) hr
  have h0 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 0 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 0 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from lE Λ v e s (σ.map' 1 2)) :=
    GlobalTheory.CompanionTheory.ConeZcls.map_self (g ⋙ O (smFun X q)) σ (Fin.last 2) _ _
  have h1 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 1 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 1 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from lE Λ v e s (σ.map' 0 2)) :=
    GlobalTheory.CompanionTheory.ConeZcls.map_self (g ⋙ O (smFun X q)) σ (Fin.last 2) _ _
  have h2 : ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast 2 σ)).hom (bE Λ v e s (GlobalTheory.CatH.face 2 σ)) =
      (show (g.obj (σ.obj (Fin.last 2))).B from (g.map (σ.map' 1 2)).φ (lE Λ v e s (σ.map' 0 1))) := rfl
  have hd : CH.d (g ⋙ O (smFun X q)) 1 (bE Λ v e s) σ =
      ∑ i : Fin 3, (-1 : ℤ) ^ (i : ℕ) • ((g ⋙ O (smFun X q)).map (GlobalTheory.CatH.toLast i σ)).hom
        (bE Λ v e s (GlobalTheory.CatH.face i σ)) := rfl
  rw [Pi.smul_apply, hd, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_smul, neg_smul, even_two, Even.neg_pow, one_pow]
  rw [h0, h1, h2]
  refine key.trans ?_
  have fin : ∀ a b c : (g.obj (σ.obj (Fin.last 2))).B, a + b - c = b + -c + a := fun a b c => by abel
  exact fin _ _ _

theorem bE_mem (Λ : CLiftK g D) (v : ∀ c, (g.obj c).Bˣ) (e s : ℕ)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (τ : ComposableArrows C 1) : (show (g.obj (τ.obj (Fin.last 1))).B from bE Λ v e s τ) ∈ (g.obj (τ.obj (Fin.last 1))).J := by
  change plogK (g.obj (τ.obj (Fin.last 1))).δ s (((epsE Λ v e (τ.map' 0 1) : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
    (g.obj (τ.obj (Fin.last 1))).B) - 1) ∈ _
  exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ ((g.obj (τ.obj (Fin.last 1))).δ.dpow_mem (Nat.succ_ne_zero k)
    (hε (τ.map' 0 1)))

theorem bE_sub [CharZero K] (Λ : CLiftK g D) (v v' : ∀ c, (g.obj c).Bˣ) (e s : ℕ) (hs : ∀ c, (g.obj c).pdPow s = ⊥)
    (hε : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (hε' : ∀ {c c' : C} (φ : c ⟶ c'), ((epsE Λ v' e φ : (g.obj c').Bˣ) : (g.obj c').B) - 1 ∈ (g.obj c').J)
    (τ : ComposableArrows C 1) :
    (show (g.obj (τ.obj (Fin.last 1))).B from bE Λ v e s τ - bE Λ v' e s τ) =
      plogK (g.obj (τ.obj (Fin.last 1))).δ s
        (((v (τ.obj (Fin.last 1)) * (v' (τ.obj (Fin.last 1)))⁻¹ : (g.obj (τ.obj (Fin.last 1))).Bˣ) :
            (g.obj (τ.obj (Fin.last 1))).B) *
          Ring.inverse (show (g.obj (τ.obj (Fin.last 1))).B from (g.map (τ.map' 0 1)).φ
            (((v (τ.obj 0) * (v' (τ.obj 0))⁻¹ : (g.obj (τ.obj 0)).Bˣ) : (g.obj (τ.obj 0)).B))) - 1) :=
  lE_sub Λ v v' e s hs (τ.map' 0 1) (hε (τ.map' 0 1)) (hε' (τ.map' 0 1))

end CrystallineSemistableComparison.Pb.LX
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocExact

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace CrystallineSemistableComparison.Pb

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ}

namespace LX

section Fam
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {N : ℕ} {D : E.LineData X}
  (i : X ⟶ PSpace K N) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e) (s : ℕ)
  (hD : IsTautologicalLineAt D N i) (Λ : CLiftK (wU q i y s).ι D)

def vV (k : Fin m) (V : ObjectProperty (Thick (smFun X q))) (hV : V ≤ wU q i y s) (hk : ∀ T, V T → InU (uy i y k) T) :
    ∀ c : V.FullSubcategory, ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c).Bˣ :=
  fun c => vv i y hy s hD Λ k ((ObjectProperty.ιOfLE hV).obj c) (hk _ c.property)

theorem vV_eps (k : Fin m) (V : ObjectProperty (Thick (smFun X q))) (hV : V ≤ wU q i y s)
    (hk : ∀ T, V T → InU (uy i y k) T) {c c' : V.FullSubcategory} (φ : c ⟶ c') :
    ((epsE (Λ.precomp (ObjectProperty.ιOfLE hV)) (vV i y hy s hD Λ k V hV hk) e φ :
        ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').Bˣ) : ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').B) - 1 ∈
      ((ObjectProperty.ιOfLE hV ⋙ (wU q i y s).ι).obj c').J :=
  eps_mem i y hy s hD Λ k ((ObjectProperty.ιOfLE hV).map φ) (hk _ c.property) (hk _ c'.property)

end Fam

theorem evalAt_comp_appLE {A : Type} [CommRing A] {Y Z : Scheme.{0}} (x : Spec (CommRingCat.of A) ⟶ Y) (f : Y ⟶ Z)
    (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ (f ⁻¹ᵁ U)) (h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ U) (a : Γ(Z, U)) :
    GlobalTheory.Cris.evalAt (x ≫ f) U h' a = GlobalTheory.Cris.evalAt x (f ⁻¹ᵁ U) h (f.appLE U (f ⁻¹ᵁ U) le_rfl a) := by
  unfold GlobalTheory.Cris.evalAt
  rw [← Scheme.Hom.appLE_comp_appLE x f U (f ⁻¹ᵁ U) ⊤ le_rfl h]
  rfl

theorem mem_pdP_one {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) {x : B} (hx : x ∈ J) : x ∈ pdP δ 1 := by
  have h := dpow_mem_pdP δ 1 hx
  rwa [δ.dpow_one hx] at h

theorem mem_thFil_one {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
    {T : Thick (smFun X q)} {x : T.B} (hx : x ∈ T.J) :
    (show (thA (smFun X q)).obj T from x) ∈ (thFil (smFun X q) 1).S T :=
  mem_pdP_one T.δ hx

end LX

open LX

theorem firstChern_local_exact [CharZero K] (q : X ⟶ Spec (CommRingCat.of K)) (D : E.LineData X) (i : X ⟶ PSpace K N)
    (hD : IsTautologicalLineAt D N i) {m e : ℕ} (y : Fin m → MvPolynomial (Fin (N + 1)) K) (hy : ∀ k, (y k).IsHomogeneous e)
    (s : ℕ) (Λ : CLiftK (ObjectProperty.ι fun T : Thick (smFun X q) => ∃ k, wK q i y s k T) D) :
    ∃ b : ∀ k, CH.Cn (CH.modF ((wK q i y s k).ι ⋙ thA (smFun X q))) 1,
      (∀ k σ, b k σ ∈ (thFil (smFun X q) 1).S _) ∧
      (∀ k, resB (thA (smFun X q)) (fun T h => ⟨k, h⟩ : wK q i y s k ≤ fun T : Thick (smFun X q) => ∃ k', wK q i y s k' T)
        (e • zK Λ s) = CH.d _ 1 (b k)) ∧
      ∀ k k', ∃ ĝ : ∀ T : (capS (wK q i y s) {k, k'}).FullSubcategory, T.obj.B,
        (∀ T (h : InU (uy i y k') T.obj),
          Ideal.Quotient.mk _ (ĝ T) = ev T.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k'))) ∧
        resB (thA (smFun X q)) (fun T h => h k (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k) (b k) -
          resB (thA (smFun X q)) (fun T h => h k' (by simp) : capS (wK q i y s) {k, k'} ≤ wK q i y s k') (b k') =
          dlogC (capS (wK q i y s) {k, k'}) s ĝ := by
  classical
  have hsk : ∀ k (c : (wK q i y s k).FullSubcategory), c.obj.pdPow s = ⊥ := fun k c => (wK_tf i y s c.property).1
  refine ⟨fun k => bE (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s, ?_, ?_, ?_⟩
  · intro k σ
    exact mem_thFil_one (bE_mem (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s
      (vV_eps i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) σ)
  · intro k
    exact zK_smul_eq_d (Λ.precomp (ObjectProperty.ιOfLE (wK_le_wU i y s k)))
      (vV i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h)) e s (hsk k)
      (vV_eps i y hy s hD Λ k (wK q i y s k) (wK_le_wU i y s k) (fun T h => wK_uy i y s h))
  · intro k k'
    have hkk : k ∈ ({k, k'} : Finset (Fin m)) := by simp
    have hkk' : k' ∈ ({k, k'} : Finset (Fin m)) := by simp
    have hcU : capS (wK q i y s) {k, k'} ≤ wU q i y s := fun T h => wK_le_wU i y s k T (h k hkk)
    have hc1 : ∀ T, capS (wK q i y s) {k, k'} T → InU (uy i y k) T := fun T h => wK_uy i y s (h k hkk)
    have hc2 : ∀ T, capS (wK q i y s) {k, k'} T → InU (uy i y k') T := fun T h => wK_uy i y s (h k' hkk')
    refine ⟨fun T => (show T.obj.B from ((vV i y hy s hD Λ k _ hcU hc1 T * (vV i y hy s hD Λ k' _ hcU hc2 T)⁻¹ :
        ((ObjectProperty.ιOfLE hcU ⋙ (wU q i y s).ι).obj T).Bˣ) : ((ObjectProperty.ιOfLE hcU ⋙ (wU q i y s).ι).obj T).B)),
      ?_, ?_⟩
    · intro T h
      set c : (wU q i y s).FullSubcategory := (ObjectProperty.ιOfLE hcU).obj T
      have h1 := vv_spec i y hy s hD Λ k c (hc1 _ T.property)
      have h2 := vv_spec i y hy s hD Λ k' c (hc2 _ T.property)
      have hq : lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k) =
          lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
            ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) := by
        refine (liftA_yx_quot (pt c.obj ≫ i) y hy (jc i y s c) k k' (hjc i y s c) h).trans ?_
        congr 1
        exact evalAt_comp_appLE (pt c.obj) i _ h h _
      change Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k c (hc1 _ T.property) *
        (vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)) = _
      rw [Units.val_mul, map_mul, h1]
      have h3 : Ideal.Quotient.mk c.obj.J ((vv i y hy s hD Λ k' c (hc2 _ T.property) : c.obj.Bˣ) : c.obj.B) *
          Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [h2] at h3
      unfold μ at h3 ⊢
      rw [hq]
      calc lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
              ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) *
              (((AU i y s hD Λ c)⁻¹ ^ e : (c.obj.B ⧸ c.obj.J)ˣ) : c.obj.B ⧸ c.obj.J) *
            Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)
          = ev c.obj h ((i.appLE _ (uy i y k') le_rfl).hom (yQ y hy k k')) *
            (lj i c.obj (jc i y s c) (hjc i y s c) (yx y hy (jc i y s c) k') *
              (((AU i y s hD Λ c)⁻¹ ^ e : (c.obj.B ⧸ c.obj.J)ˣ) : c.obj.B ⧸ c.obj.J) *
            Ideal.Quotient.mk c.obj.J (((vv i y hy s hD Λ k' c (hc2 _ T.property))⁻¹ : c.obj.Bˣ) : c.obj.B)) := by ring
        _ = _ := by rw [h3, mul_one]; rfl
    · funext τ
      exact bE_sub (Λ.precomp (ObjectProperty.ιOfLE hcU)) (vV i y hy s hD Λ k _ hcU hc1) (vV i y hy s hD Λ k' _ hcU hc2)
        e s (fun c => (wK_tf i y s (c.property k hkk)).1)
        (vV_eps i y hy s hD Λ k _ hcU hc1) (vV_eps i y hy s hD Λ k' _ hcU hc2) τ

end CrystallineSemistableComparison.Pb
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.PowTop

section

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Pb

theorem powK_ne_zero_main {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [ConnectedSpace X] (d : ℕ) [SmoothOfRelativeDimension d q] (D : E.LineData X) (hD : IsTautologicalLine q D) (c : HdR q 2)
    (hc : IsFirstChernDeRham q D c) : powK q c d ≠ 0 :=
  powK_ne_zero_of (by intro K _ _ X q _ n _ N i hci hiq; exact geo_setup q n N i hci hiq) resid_alg
    (by intro K _ X N _ q D i hD m e y hy s Λ; exact firstChern_local_exact q D i hD y hy s Λ) q d D hD c hc

end CrystallineSemistableComparison.Pb
end
end
end
