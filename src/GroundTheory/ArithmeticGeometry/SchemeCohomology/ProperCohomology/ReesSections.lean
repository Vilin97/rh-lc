module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackBaseChange
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.TwistingSheaf
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesScheme
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.PullbackGamma
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Module.Basic
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesSheafBase

-- Source module: GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesRing

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {V : X.Opens}

abbrev polyRing (I : Ideal A) (V : X.Opens) : CommRingCat.{u} :=
  Γ(reesPolyScheme I X, reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V))

abbrev polyInl (I : Ideal A) (V : X.Opens) : Γ(X, V) ⟶ polyRing I V :=
  (reesPr I X).app V ≫ (reesPolyMap I X).app _

lemma polyDesc_w : CommRingCat.ofHom (algV (A := A) X V) ≫ CommRingCat.ofHom Polynomial.C =
    CommRingCat.ofHom (Polynomial.C (R := A)) ≫
      CommRingCat.ofHom (Polynomial.mapRingHom (algV (A := A) X V)) := by
  ext a
  simp

def polyRingHom (hV : IsAffineOpen V) : polyRing I V →+* Polynomial Γ(X, V) :=
  ((isPushout_reesPoly (I := I) hV).desc (CommRingCat.ofHom Polynomial.C)
    (CommRingCat.ofHom (Polynomial.mapRingHom (algV (A := A) X V))) polyDesc_w).hom

lemma polyRingHom_inl (hV : IsAffineOpen V) (c : Γ(X, V)) :
    polyRingHom hV (polyInl I V c) = Polynomial.C c := by
  have := congrArg (fun f : Γ(X, V) ⟶ CommRingCat.of (Polynomial Γ(X, V)) => f.hom c)
    (IsPushout.inl_desc (isPushout_reesPoly (I := I) hV) _ _ polyDesc_w)
  exact this

lemma polyRingHom_inr (hV : IsAffineOpen V) (p : Polynomial A) :
    polyRingHom hV (polyInr (I := I) V p) = p.map (algV (A := A) X V) := by
  have := congrArg
    (fun f : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial Γ(X, V)) => f.hom p)
    (IsPushout.inr_desc (isPushout_reesPoly (I := I) hV) _ _ polyDesc_w)
  exact this

def polyRingInv : Polynomial Γ(X, V) →+* polyRing I V :=
  Polynomial.eval₂RingHom (polyInl I V).hom (polyInr (I := I) V Polynomial.X)

lemma polyInr_eq_eval₂ (hV : IsAffineOpen V) (p : Polynomial A) :
    polyInr (I := I) V p =
      p.eval₂ ((polyInl I V).hom.comp (algV (A := A) X V)) (polyInr (I := I) V Polynomial.X) := by
  have hw := (isPushout_reesPoly (I := I) hV).w
  have h : (polyInr (I := I) V).hom =
      Polynomial.eval₂RingHom ((polyInl I V).hom.comp (algV (A := A) X V))
        (polyInr (I := I) V Polynomial.X) := by
    apply Polynomial.ringHom_ext
    · intro a
      have := congrArg (fun f => f.hom a) hw
      simpa using this.symm
    · simp
  exact congrArg (fun f => f p) h

def polyRingEquiv (hV : IsAffineOpen V) : polyRing I V ≃+* Polynomial Γ(X, V) :=
  RingEquiv.ofRingHom (polyRingHom hV) (polyRingInv (I := I) (V := V))
    (by
      apply Polynomial.ringHom_ext
      · intro c
        change polyRingHom hV ((polyRingInv (I := I) (V := V)) (Polynomial.C c)) = Polynomial.C c
        rw [polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
        exact polyRingHom_inl hV c
      · change polyRingHom hV ((polyRingInv (I := I) (V := V)) Polynomial.X) = Polynomial.X
        rw [polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, polyRingHom_inr,
          Polynomial.map_X])
    (by
      have h := (isPushout_reesPoly (I := I) hV).hom_ext
        (k := CommRingCat.ofHom ((polyRingInv (I := I) (V := V)).comp (polyRingHom hV)))
        (l := 𝟙 _) (by
          ext c
          change (polyRingInv (I := I) (V := V)) (polyRingHom hV (polyInl I V c)) = polyInl I V c
          rw [polyRingHom_inl, polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]) (by
          refine CommRingCat.hom_ext (RingHom.ext fun p => ?_)
          change (polyRingInv (I := I) (V := V)) (polyRingHom hV (polyInr (I := I) V p)) =
            polyInr (I := I) V p
          rw [polyRingHom_inr, polyRingInv, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
          exact (polyInr_eq_eval₂ hV p).symm)
      exact congrArg CommRingCat.Hom.hom h)


lemma reesInr_comp (hV : IsAffineOpen V) :
    reesInr (I := I) V ≫ (reesPolyMap I X).app _ =
      CommRingCat.ofHom (algebraMap (reesAlgebra I) (Polynomial A)) ≫ polyInr (I := I) V := by
  have hw := (isPushout_app_of_isPullback (isPullback_reesPoly I X) (hV.preimage (reesPr I X))).w
  rw [reesInr, polyInr, Category.assoc, hw, ← Category.assoc, ← Category.assoc,
    Scheme.ΓSpecIso_inv_naturality]

def reesRingHom (hV : IsAffineOpen V) : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) →+* Polynomial Γ(X, V) :=
  (polyRingHom hV).comp ((reesPolyMap I X).app (reesPr I X ⁻¹ᵁ V)).hom

lemma reesRingHom_inl (hV : IsAffineOpen V) (c : Γ(X, V)) :
    reesRingHom hV ((reesPr I X).app V c) = Polynomial.C c :=
  polyRingHom_inl hV c

lemma reesRingHom_inr (hV : IsAffineOpen V) (r : reesAlgebra I) :
    reesRingHom hV (reesInr (I := I) V r) = (r : Polynomial A).map (algV (A := A) X V) := by
  have := congrArg (fun f : CommRingCat.of (reesAlgebra I) ⟶ polyRing I V => f.hom r)
    (reesInr_comp (I := I) hV)
  change polyRingHom hV (((reesInr (I := I) V ≫ (reesPolyMap I X).app _)).hom r) = _
  rw [this]
  exact polyRingHom_inr hV _


variable (I X V) in
def reesCoeffRing : Subring (Polynomial Γ(X, V)) where
  carrier := {p | ∀ n, p.coeff n ∈ (I.map (algV (A := A) X V)) ^ n}
  one_mem' n := by
    change _root_.AddMonoidAlgebra.coeff (M := ℕ) 1 n ∈ _
    rw [Polynomial.coeff_one]
    split_ifs with h
    · subst h
      simp
    · exact zero_mem _
  mul_mem' {p q} hp hq n := by
    change (p * q).coeff n ∈ _
    rw [Polynomial.coeff_mul]
    refine Ideal.sum_mem _ fun x hx => ?_
    have hx : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
    rw [← hx, pow_add]
    exact Ideal.mul_mem_mul (hp x.1) (hq x.2)
  zero_mem' n := by simp
  add_mem' {p q} hp hq n := by
    change (p + q).coeff n ∈ _
    rw [Polynomial.coeff_add]
    exact add_mem (hp n) (hq n)
  neg_mem' {p} hp n := by
    change (-p).coeff n ∈ _
    rw [Polynomial.coeff_neg]
    exact neg_mem (hp n)

lemma C_mem_reesCoeffRing (c : Γ(X, V)) : Polynomial.C c ∈ reesCoeffRing I X V := by
  intro n
  rw [Polynomial.coeff_C]
  split_ifs with h
  · subst h
    simp
  · exact zero_mem _

lemma map_mem_reesCoeffRing (r : reesAlgebra I) :
    (r : Polynomial A).map (algV (A := A) X V) ∈ reesCoeffRing I X V := by
  intro n
  rw [Polynomial.coeff_map, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ((mem_reesAlgebra_iff I _).1 r.2 n)

theorem reesRingHom_mem (hV : IsAffineOpen V) (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)) :
    reesRingHom hV s ∈ reesCoeffRing I X V := by
  let l : Γ(X, V) ⟶ CommRingCat.of (reesCoeffRing I X V) :=
    CommRingCat.ofHom ((Polynomial.C).codRestrict (reesCoeffRing I X V) C_mem_reesCoeffRing)
  let r : CommRingCat.of (reesAlgebra I) ⟶ CommRingCat.of (reesCoeffRing I X V) :=
    CommRingCat.ofHom (((Polynomial.mapRingHom (algV (A := A) X V)).comp (reesAlgebra I).val.toRingHom)
      |>.codRestrict (reesCoeffRing I X V) map_mem_reesCoeffRing)
  have hw' : CommRingCat.ofHom (algV (A := A) X V) ≫ l =
      CommRingCat.ofHom (algebraMap A (reesAlgebra I)) ≫ r := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => Subtype.ext ?_)
    simp [l, r]
  let d := (isPushout_rees (I := I) hV).desc l r hw'
  have h : (CommRingCat.ofHom (reesRingHom hV) :
      Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) ⟶ CommRingCat.of (Polynomial Γ(X, V))) =
      d ≫ CommRingCat.ofHom (reesCoeffRing I X V).subtype := by
    apply (isPushout_rees (I := I) hV).hom_ext
    · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      have := congrArg (fun f : Γ(X, V) ⟶ CommRingCat.of (reesCoeffRing I X V) =>
        (f.hom c : Polynomial Γ(X, V))) (IsPushout.inl_desc (isPushout_rees (I := I) hV) l r hw')
      exact (reesRingHom_inl hV c).trans this.symm
    · refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      have := congrArg (fun f : CommRingCat.of (reesAlgebra I) ⟶ CommRingCat.of (reesCoeffRing I X V) =>
        (f.hom x : Polynomial Γ(X, V))) (IsPushout.inr_desc (isPushout_rees (I := I) hV) l r hw')
      exact (reesRingHom_inr hV x).trans this.symm
  have := congrArg (fun f : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) ⟶
    CommRingCat.of (Polynomial Γ(X, V)) => f.hom s) h
  change reesRingHom hV s ∈ _
  rw [show reesRingHom hV s = ((d.hom s : reesCoeffRing I X V) : Polynomial Γ(X, V)) from this]
  exact (d.hom s).2

end

end GroundTheory.Arith.SchemeCoh
end
end

-- Source module: GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ReesSections

section

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

noncomputable section

variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {F : X.Modules} {V : X.Opens}


variable (I F V) in
abbrev unitPr : Γ(F, V) →+ Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) :=
  Etale.pullbackUnitApp (reesPr I X) F V


variable (I F V) in
abbrev unitB : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →+
    Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) :=
  Etale.pullbackUnitApp (reesPolyMap I X) ((Scheme.Modules.pullback (reesPr I X)).obj F)
    (reesPr I X ⁻¹ᵁ V)

variable (hF : IsCoherent F) (hV : IsAffineOpen V)

include hF hV in
lemma isBaseChangeAt_reesPr : IsBaseChangeAt (reesPr I X) F V := by
  have := hF.1
  exact isBaseChangeAt_of_isAffineOpen _ F hV (hV.preimage _)

include hF hV in
lemma isBaseChangeAt_reesPolyMap :
    IsBaseChangeAt (reesPolyMap I X) ((Scheme.Modules.pullback (reesPr I X)).obj F)
      (reesPr I X ⁻¹ᵁ V) := by
  have := (isCoherent_pullback_reesPr (I := I) hF).1
  exact isBaseChangeAt_of_isAffineOpen _ _ (hV.preimage _) ((hV.preimage _).preimage _)

lemma single_zero_smul_compat (a : Γ(X, V)) (m : Γ(F, V)) :
    PolynomialModule.single Γ(X, V) 0 (a • m) =
      reesRingHom (I := I) hV ((reesPr I X).app V a) • PolynomialModule.single Γ(X, V) 0 m := by
  rw [reesRingHom_inl, ← Polynomial.monomial_zero_left, PolynomialModule.monomial_smul_single,
    zero_add]

include hF in
lemma exists_theta₁ : ∃ θ : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →+
    PolynomialModule Γ(X, V) Γ(F, V),
    (∀ m, θ (unitPr I F V m) = PolynomialModule.single Γ(X, V) 0 m) ∧
    (∀ (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)) y, θ (s • y) = reesRingHom (I := I) hV s • θ y) := by
  let _ : Module Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) (PolynomialModule Γ(X, V) Γ(F, V)) :=
    Module.compHom _ (reesRingHom (I := I) hV)
  obtain ⟨θ, hθ, -⟩ := isBaseChangeAt_reesPr (I := I) hF hV _
    (PolynomialModule.lsingle Γ(X, V) 0 : Γ(F, V) →ₗ[Γ(X, V)] _).toAddMonoidHom
    (fun a m => single_zero_smul_compat hV a m)
  exact ⟨θ.toAddMonoidHom, hθ, fun s y => θ.map_smul s y⟩

def theta₁ : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →+
    PolynomialModule Γ(X, V) Γ(F, V) :=
  (exists_theta₁ hF hV).choose

lemma theta₁_unitPr (m : Γ(F, V)) :
    theta₁ hF hV (unitPr I F V m) = PolynomialModule.single Γ(X, V) 0 m :=
  (exists_theta₁ hF hV).choose_spec.1 m

lemma theta₁_smul (s : Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V))
    (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    theta₁ hF hV (s • y) = reesRingHom (I := I) hV s • theta₁ hF hV y :=
  (exists_theta₁ hF hV).choose_spec.2 s y

include hF in
lemma exists_theta : ∃ θ : Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) →+
    PolynomialModule Γ(X, V) Γ(F, V),
    (∀ y, θ (unitB I F V y) = theta₁ hF hV y) ∧
    (∀ (s : polyRing I V) x, θ (s • x) = polyRingHom (I := I) hV s • θ x) := by
  let _ : Module (polyRing I V) (PolynomialModule Γ(X, V) Γ(F, V)) :=
    Module.compHom _ (polyRingHom (I := I) hV)
  obtain ⟨θ, hθ, -⟩ := isBaseChangeAt_reesPolyMap (I := I) hF hV _ (theta₁ hF hV)
    (fun s y => theta₁_smul hF hV s y)
  exact ⟨θ.toAddMonoidHom, hθ, fun s x => θ.map_smul s x⟩

def thetaMap : Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V)) →+
    PolynomialModule Γ(X, V) Γ(F, V) :=
  (exists_theta hF hV).choose

lemma thetaMap_unitB (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    thetaMap hF hV (unitB I F V y) = theta₁ hF hV y :=
  (exists_theta hF hV).choose_spec.1 y

lemma polyRingInv_polyRingHom (s : polyRing I V) :
    polyRingInv (I := I) (V := V) (polyRingHom hV s) = s :=
  (polyRingEquiv hV).symm_apply_apply s

lemma thetaMap_smul (s : polyRing I V) (x : Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V))) :
    thetaMap hF hV (s • x) = polyRingHom (I := I) hV s • thetaMap hF hV x :=
  (exists_theta hF hV).choose_spec.2 s x


variable (I F V) in
abbrev polySec := Γ((Scheme.Modules.pullback (reesPolyMap I X)).obj
      ((Scheme.Modules.pullback (reesPr I X)).obj F), reesPolyMap I X ⁻¹ᵁ (reesPr I X ⁻¹ᵁ V))


variable (I F V) in
def lambdaMap : PolynomialModule Γ(X, V) Γ(F, V) →+ polySec I F V where
  toFun q := q.coeff.sum fun n m =>
    (polyRingInv (I := I) (V := V) (Polynomial.X ^ n)) • unitB I F V (unitPr I F V m)
  map_zero' := by simp
  map_add' q q' := by
    simp only [PolynomialModule.coeff_add]
    rw [Finsupp.sum_add_index']
    · intro n
      simp
    · intro n m m'
      rw [map_add (f := _), map_add (f := _), smul_add]

lemma lambdaMap_single (n : ℕ) (m : Γ(F, V)) :
    lambdaMap I F V (PolynomialModule.single Γ(X, V) n m) =
      (polyRingInv (I := I) (V := V) (Polynomial.X ^ n)) • unitB I F V (unitPr I F V m) := by
  simp [lambdaMap, Finsupp.sum_single_index]

lemma unitB_unitPr_smul (c : Γ(X, V)) (m : Γ(F, V)) :
    unitB I F V (unitPr I F V (c • m)) = polyInl I V c • unitB I F V (unitPr I F V m) := by
  rw [unitPr, pullbackUnitApp_smul_at, unitB, pullbackUnitApp_smul_at]
  rfl

lemma lambdaMap_smul (p : Polynomial Γ(X, V)) (q : PolynomialModule Γ(X, V) Γ(F, V)) :
    lambdaMap I F V (p • q) = polyRingInv (I := I) (V := V) p • lambdaMap I F V q := by
  induction p using Polynomial.induction_on' with
  | add p p' hp hp' => rw [add_smul, map_add (f := _), hp, hp', map_add (f := _), add_smul]
  | monomial i c =>
    induction q using PolynomialModule.induction_linear with
    | zero => simp
    | add q q' h h' => rw [smul_add, map_add (f := _), h, h', map_add (f := _), smul_add]
    | single j m =>
      rw [PolynomialModule.monomial_smul_single, lambdaMap_single, lambdaMap_single,
        unitB_unitPr_smul, smul_smul, smul_smul, polyRingInv, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X_pow,
        Polynomial.eval₂_X_pow, Polynomial.eval₂_monomial, pow_add]
      congr 1
      ring

include hF hV in
lemma lambdaMap_theta₁ (y : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V)) :
    lambdaMap I F V (theta₁ hF hV y) = unitB I F V y := by
  let _ : Module Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V) (polySec I F V) :=
    Module.compHom _ ((reesPolyMap I X).app (reesPr I X ⁻¹ᵁ V)).hom
  let L1 : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →ₗ[
      Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)] polySec I F V :=
    { toFun := fun y => lambdaMap I F V (theta₁ hF hV y)
      map_add' := fun y y' => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun s y => by
        rw [theta₁_smul, lambdaMap_smul, reesRingHom, RingHom.comp_apply,
          polyRingInv_polyRingHom]
        rfl }
  let L2 : Γ((Scheme.Modules.pullback (reesPr I X)).obj F, reesPr I X ⁻¹ᵁ V) →ₗ[
      Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)] polySec I F V :=
    { toFun := unitB I F V
      map_add' := map_add _
      map_smul' := fun s y => pullbackUnitApp_smul_at _ _ _ s y }
  obtain ⟨ψ, -, huniq⟩ := isBaseChangeAt_reesPr (I := I) hF hV (polySec I F V)
    ((unitB I F V).comp (unitPr I F V)) (fun a m => unitB_unitPr_smul a m)
  have e1 := huniq L1 (fun m => by
    change lambdaMap I F V (theta₁ hF hV (unitPr I F V m)) = _
    rw [theta₁_unitPr, lambdaMap_single, pow_zero, map_one, one_smul]
    rfl)
  have e2 := huniq L2 (fun m => rfl)
  exact congrArg (fun L : _ →ₗ[Γ(reesScheme I X, reesPr I X ⁻¹ᵁ V)] polySec I F V => L y)
    (e1.trans e2.symm)


include hF hV in
theorem lambdaMap_thetaMap (x : polySec I F V) : lambdaMap I F V (thetaMap hF hV x) = x := by
  let L3 : polySec I F V →ₗ[polyRing I V] polySec I F V :=
    { toFun := fun x => lambdaMap I F V (thetaMap hF hV x)
      map_add' := fun x x' => by rw [map_add (f := _), map_add (f := _)]
      map_smul' := fun s x => by
        rw [thetaMap_smul, lambdaMap_smul, polyRingInv_polyRingHom]
        rfl }
  obtain ⟨ψ, -, huniq⟩ := isBaseChangeAt_reesPolyMap (I := I) hF hV (polySec I F V)
    (unitB I F V) (fun s y => pullbackUnitApp_smul_at _ _ _ s y)
  have e1 := huniq L3 (fun y => by
    change lambdaMap I F V (thetaMap hF hV (unitB I F V y)) = _
    rw [thetaMap_unitB, lambdaMap_theta₁])
  have e2 := huniq LinearMap.id (fun y => rfl)
  exact congrArg (fun L : polySec I F V →ₗ[polyRing I V] polySec I F V => L x) (e1.trans e2.symm)

include hF hV in
lemma thetaMap_injective : Function.Injective (thetaMap (I := I) hF hV) :=
  Function.LeftInverse.injective (lambdaMap_thetaMap hF hV)

end

end GroundTheory.Arith.SchemeCoh
end
end
