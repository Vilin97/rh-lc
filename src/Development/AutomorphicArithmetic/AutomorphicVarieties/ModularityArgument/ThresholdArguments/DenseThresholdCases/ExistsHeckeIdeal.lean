module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
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
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.HeckePolCoeff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiAlgUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AuTeichEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CLocConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.EqOnTors
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeDeterminantSatisfiesDeformationRelations
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdCoreH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TDenseU

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.HeckePolynomialTorsion.MapOfRel

section

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

theorem UpperTheory.V.Hi.JEx.map_of_rel {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) {T : Type} [CommRing T] [Algebra O T]
    [IsCO O T] (φ : Λ.Λ →ₐ[O] T) (D : GDet n T F.G₀) (ψ : ∀ v, Fin n → F.Gv v →* Tˣ) (hc : D.IsCont (maximalIdeal T))
    (hred : D.map (res O T : T →+* ResidueField O) = r.Dbar)
    (hpsi : ∀ v i, r.IsPsi v i (ψ v i) ∧ pushCh (φ : Λ.Λ →+* T) (Λ.κ v i) = (ψ v i).comp (F.Iv v).subtype)
    (hrel : (∀ i g, D.lam i (F.star O T n (MonoidAlgebra.single g 1)) = D.lam i (MonoidAlgebra.single g 1)) ∧
      (∀ v (g : Fin n → F.Gv v) (h : F.G₀), D.tr (MonoidAlgebra.single h 1 * F.oEl v (ψ v) g) = 0) ∧
      ∀ u, ∀ g ∈ r.Ip u, ∀ h : F.G₀, D.tr (MonoidAlgebra.single h 1 * (MonoidAlgebra.single g 1 - 1)) = 0) :
    ∃ f : B.B →ₐ[O] T, B.u.D.map f.toRingHom = D ∧ (∀ v i, pushCh f.toRingHom (B.u.ψ v i) = ψ v i) ∧
      ∀ b, f (Λ.toPair B.u b) = φ b := by
  let p : Pair r T := ⟨D, ψ, hc, hred, fun v i => (hpsi v i).1, hrel.1, hrel.2.1, hrel.2.2⟩
  obtain ⟨f, hf, -⟩ := B.univ T p
  refine ⟨f, hf.1, hf.2, ?_⟩
  let κ' : ∀ v, Fin n → F.Iv v →* Tˣ := fun v i => (ψ v i).comp (F.Iv v).subtype
  have hin : IsInert r κ' := fun v i => ⟨ψ v i, (hpsi v i).1, rfl⟩
  obtain ⟨g, -, hu⟩ := Λ.univ T κ' hin
  have h1 : ∀ v i, pushCh ((f.comp (Λ.toPair B.u) : Λ.Λ →ₐ[O] T) : Λ.Λ →+* T) (Λ.κ v i) = κ' v i := by
    intro v i
    have e1 := LamObj.toPair_spec r Λ B.u v i
    have e2 := hf.2 v i
    calc pushCh ((f.comp (Λ.toPair B.u) : Λ.Λ →ₐ[O] T) : Λ.Λ →+* T) (Λ.κ v i)
        = pushCh (f : B.B →+* T) (pushCh ((Λ.toPair B.u : Λ.Λ →ₐ[O] B.B) : Λ.Λ →+* B.B) (Λ.κ v i)) := by
          ext s
          rfl
      _ = pushCh (f : B.B →+* T) ((B.u.ψ v i).comp (F.Iv v).subtype) := by rw [e1]
      _ = (pushCh (f : B.B →+* T) (B.u.ψ v i)).comp (F.Iv v).subtype := by
          ext s
          rfl
      _ = κ' v i := by rw [e2]
  have h2 : ∀ v i, pushCh (φ : Λ.Λ →+* T) (Λ.κ v i) = κ' v i := fun v i => (hpsi v i).2
  have heq := (hu _ h1).trans (hu _ h2).symm
  intro b
  exact DFunLike.congr_fun heq b
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.DeformationRingToHeckeAlgebraSurjective

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField


theorem UpperTheory.V.Hi.deformationRing_to_heckeAlgebra_surjective :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A T B : Type) [CommRing A] [CommRing T] [Algebra c.O T] [Algebra A T] [CommRing B] [Algebra c.O B] (gen : H.Op → T) (D₀ : W.GDet n B H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Bˣ) (f : B →ₐ[c.O] T),
    (∀ (w : H.Wp) (P : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver P w.1 → IsFrob P (normV w.1) σ →
      (D₀.map f.toRingHom).chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
    (∀ v (j : Fin n) (x : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)), (g : G L Ω) = (x : G L Ω) → H.art v x = unif _ →
      ((∏ i with i ≤ j, W.pushCh f.toRingHom (ψ₀ v i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
    ∀ j : A → B, (∀ b, f (j b) = algebraMap A T b) → Algebra.adjoin A (Set.range gen) = ⊤ → Function.Surjective f := by
  intro L Ω _ _ _ _ _ l _ n c H hH A T B _ _ _ _ _ _ gen D₀ ψ₀ f h1 h2 j hj htop
  have hgen : ∀ i, gen i ∈ f.range := by
    rintro (⟨w, k⟩ | ⟨v, k⟩)
    · obtain ⟨P, hP⟩ := exists_isPlaceOver Ω w.1
      obtain ⟨σ, hσ⟩ := exists_isFrob hP
      have hq : IsUnit ((normV w.1 : ℕ) : c.O) := by
        have h0 := (cycZ L Ω l σ).isUnit.map (algebraMap ℤ_[l] c.O)
        rwa [cycZ_of_isFrob (hH.Wp_away w.1 w.2) hP hσ, map_natCast] at h0
      obtain ⟨u, hu⟩ := hq.exists_left_inv
      have huT : algebraMap c.O T u * ((normV w.1 : ℕ) : T) = 1 := by
        rw [← map_natCast (algebraMap c.O T), ← map_mul, hu, map_one]
      have e := JEx.heckePol_coeff n (normV w.1)
        (fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) (k + 1) k.2
      rw [← h1 w P σ hP hσ, dite_eq_left ⟨Nat.succ_pos _, k.2⟩] at e
      have e2 : (D₀.map f.toRingHom).chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) =
          (D₀.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1)).map f.toRingHom := by
        let y := MonoidAlgebra.single (H.prj σ⁻¹) (1 : B)
        have he (z : MonoidAlgebra B H.Gq) : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C
            (MonoidAlgebra.mapRingHom H.Gq f.toRingHom z) =
            MonoidAlgebra.mapRingHom H.Gq (Polynomial.mapRingHom f.toRingHom)
              (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C z) := by
          rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
            ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
            ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
        let : Algebra B T[X] := ((algebraMap T T[X]).comp f.toRingHom).toAlgebra
        have hn := D₀.nat B[X] T[X]
          { toRingHom := Polynomial.mapRingHom f.toRingHom
            commutes' := fun a => by change (Polynomial.mapRingHom f.toRingHom) (C a) = C (f a); simp }
          (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom H.Gq C y)
        change (D₀.map f.toRingHom).D T[X] _ = _
        rw [← show MonoidAlgebra.mapRingHom H.Gq f.toRingHom y =
          MonoidAlgebra.single (H.prj σ⁻¹) 1 by simp [y], he y]
        exact hn
      rw [e2, coeff_map] at e
      have e3 : gen (.inl (w, k)) = algebraMap c.O T u ^ ((k + 1) * (k + 1 - 1) / 2 : ℕ) *
          ((-1) ^ ((k : ℕ) + 1) * f ((D₀.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1)).coeff (n - (k + 1)))) := by
        refine Eq.trans ?_ (congrArg _ e.symm)
        rw [← mul_assoc, ← mul_pow, huT, one_pow, one_mul]
        rfl
      rw [e3]
      exact mul_mem (pow_mem (f.range.algebraMap_mem u) _)
        (mul_mem (pow_mem (neg_mem (one_mem _)) _) (f.mem_range_self _))
    · obtain ⟨y, hy⟩ := (hH.art_spec v).surj (unif _)
      rw [← h2 v k y (Subgroup.inclusion (Weil_le_Dec (H.ovr v)) y) rfl hy, Units.coe_prod]
      refine prod_mem fun i _ => ?_
      rw [Units.val_mul, Units.val_pow_eq_pow_val]
      exact mul_mem (f.mem_range_self _) (pow_mem (f.range.algebraMap_mem _) _)
  intro t
  have ht : t ∈ Algebra.adjoin A (Set.range gen) := htop ▸ Algebra.mem_top
  change t ∈ f.range
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact hgen i
  | algebraMap r => exact ⟨j r, hj r⟩
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsOrdinaryCharactersHeckeAlgebra

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Hi.exists_ordinaryCharacters_heckeAlgebra' :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ), (hset Q R.τ₀).Ax →
    ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (φ : Λ.Λ →ₐ[c.O] T) (gen : (hset Q R.τ₀).Op → T), (∀ i, gen i - algebraMap c.O T (R.a i) ∈ maximalIdeal T) →
    ∀ ψ : ∀ v : V.frame.Vl, Fin n → Dec (F := L) (s.A v.1) →* Tˣ, (∀ v i, Alg.AdicCont (maximalIdeal T) fun g => (ψ v i g : T)) →
    (∀ (v : V.frame.Vl) (i : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)) (y : Uo ((s.w v.1).adicCompletion L)), (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = y →
      (ψ v i g * (hset Q R.τ₀).epsV T v g ^ (i : ℕ) : Tˣ) * φ (R.θ (eV n (hset Q R.τ₀).Sl v i y)) = 1) →
    (∀ (v : V.frame.Vl) (j : Fin n) (x : Weil (s.hw v.1)) (g : Dec (F := L) (s.A v.1)), (g : G L Ω) = (x : G L Ω) → artOf (s.hw v.1) x = unif _ →
      ((∏ i with i ≤ j, ψ v i g * (hset Q R.τ₀).epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
    ∀ v i, r.IsPsi v i (ψ v i) ∧ W.pushCh (φ : Λ.Λ →+* T) (Λ.κ v i) = (ψ v i).comp (V.frame.Iv v).subtype := by
  intro l _ L Ω _ _ _ _ _ _ s n V Q c r ι Λ R hAx T _ _ _ φ gen hgen ψ hc hu hϖ v
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : Finite (ResidueField T) := Finite.of_surjective _ (Alg.resMap_bijective c.O T).2
  have ha : IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := hAx.art_spec v
  have hI : ∀ i (g : Dec (F := L) (s.A v.1)) (hg : g ∈ V.frame.Iv v), (ψ v i g : T) = φ (Λ.κ v i ⟨g, hg⟩) := by
    intro i g hg
    have h1 := hu v i (ineIncl (s.hw v.1) ⟨g, hg⟩) g ⟨_, JEx.art_ine _ ha ⟨g, hg⟩⟩ rfl rfl
    have h2 := congrArg (fun z : Λ.Λˣ => φ z) (R.theta v i (ineIncl (s.hw v.1) ⟨g, hg⟩) g hg ⟨_, JEx.art_ine _ ha ⟨g, hg⟩⟩ rfl rfl)
    have h3 : φ ((hset Q R.τ₀).epsV Λ.Λ v g) = (hset Q R.τ₀).epsV T v g := φ.commutes _
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_one, map_one, h3, mul_assoc] at h1 h2
    exact (left_inv_eq_right_inv h1 ((mul_comm _ _).trans h2))
  choose ψ₀ hψ₀ hκ using Λ.inert v
  have hI' : ∀ i (g : Dec (F := L) (s.A v.1)), (g : G L Ω) ∈ Ine (F := L) (s.A v.1) → (ψ v i g : T) = φ (ψ₀ i g) := by
    intro i g hg
    rw [hI i g hg, hκ]
    rfl
  obtain ⟨x, hx⟩ := ha.surj (unif _)
  let p : T →+* ResidueField c.O := Alg.res c.O T
  have hx' : ∀ i, W.pushCh p (ψ v i) (Subgroup.inclusion (Weil_le_Dec _) x) = r.psib v i (Subgroup.inclusion (Weil_le_Dec _) x) := by
    intro i
    refine mul_right_cancel (JEx.eq_of_prod
      (fun i : Fin n => W.pushCh p (ψ v i) (Subgroup.inclusion (Weil_le_Dec _) x) *
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) ^ (i : ℕ))
      (fun i : Fin n => r.psib v i (Subgroup.inclusion (Weil_le_Dec _) x) *
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) ^ (i : ℕ)) (fun j => Units.ext ?_) i)
    have h1 := congrArg p (hϖ v j x (Subgroup.inclusion (Weil_le_Dec _) x) rfl hx)
    have h2 := R.res.unif v j x (Subgroup.inclusion (Weil_le_Dec _) x) rfl hx
    have h3 := (Alg.res_eq_zero_iff c.O T _).2 (hgen (.inr (v, j)))
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h3
    have h4 : p ((hset Q R.τ₀).epsV T v (Subgroup.inclusion (Weil_le_Dec _) x)) =
        (hset Q R.τ₀).epsV (ResidueField c.O) v (Subgroup.inclusion (Weil_le_Dec _) x) := (Alg.res c.O T).commutes _
    refine Eq.trans ?_ ((h1.trans h3).trans h2.symm)
    simp only [Units.coe_prod, map_prod, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
    exact Finset.prod_congr rfl fun k _ => congrArg₂ (· * ·) rfl (congrArg (· ^ (k : ℕ)) h4.symm)
  intro i
  refine ⟨⟨hc v i, fun g => ?_, fun g => ?_⟩, MonoidHom.ext fun g => Units.ext (hI i g.1 g.2).symm⟩
  · have h1 : IsLocallyConstant (W.pushCh p (ψ v i)) :=
      IsLocallyConstant.desc _ Units.val (JEx.res_lc (O := c.O) (hc v i)) Units.val_injective
    let β : Dec (F := L) (s.A v.1) →* (ResidueField c.O)ˣ := r.psib v i
    have h2 : IsLocallyConstant β := JEx.lc_of_open _ (r.psib_open v i)
    have h3 := JEx.char_triv (s.hw v.1) ha (W.pushCh p (ψ v i) / β) (h1.div h2) (fun y hy => by
      rw [MonoidHom.div_apply, div_eq_one]
      refine Units.ext ?_
      exact (congrArg p (hI' i y hy)).trans ((Alg.res_map φ _).trans ((hψ₀ i).red y))) x hx (by rw [MonoidHom.div_apply, div_eq_one]; exact hx' i)
    have h4 : W.pushCh p (ψ v i) g / β g = 1 := DFunLike.congr_fun h3 g
    exact congrArg Units.val (div_eq_one.1 h4)
  · obtain ⟨k, hk⟩ := g.2
    have h1 := JEx.eq_on_tors (s.hw v.1) (ψ v i) (W.pushCh (φ : Λ.Λ →+* T) (ψ₀ i)) (hc v i) (JEx.cont_map φ (hψ₀ i).cont)
      (fun y hy => Units.ext (hI' i y hy)) g.1 (l ^ k) (pow_pos (Fact.out : l.Prime).pos k)
      ((QuotientGroup.eq_one_iff _).1 ((map_pow (QuotientGroup.mk' _) _ _).trans hk))
    exact (congrArg Units.val h1).trans ((congrArg φ ((hψ₀ i).mu g)).trans (φ.commutes _))
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckeDeterminantReductionEqResidual

section

@[expose] public section




section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Hi.heckeDeterminant_reduction_eq_residual_alt :
    ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (V : s.Lev) (Q : QData V) (c : Coef l) (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ), (hset Q R.τ₀).Ax →
    ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (gen : (hset Q R.τ₀).Op → T), (∀ i, gen i - algebraMap c.O T (R.a i) ∈ maximalIdeal T) →
    ∀ D : W.GDet n T V.frame.G₀, D.IsCont (maximalIdeal T) →
    (∀ (w : (hset Q R.τ₀).Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
      D.chi (MonoidAlgebra.single (V.pr σ⁻¹) 1) = heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
    D.map (Alg.res c.O T : T →+* ResidueField c.O) = r.Dbar := by
  intro l _ L Ω _ _ _ _ _ _ s n V Q c r ι Λ R hA T _ _ _ gen hgen D hD hF
  refine JEx.red_eq r D hD _ hA.dense ?_
  rintro g ⟨w, hw, B, σ, hB, hσ, rfl⟩
  have h1 := hF ⟨w, hw⟩ B σ hB hσ
  have h2 := R.res.frob ⟨w, hw⟩ B σ hB hσ
  refine (congrArg (Polynomial.map _) h1).trans (Eq.trans ?_ h2.symm)
  rw [JEx.heckePol_map]
  congr 1
  funext j
  split_ifs with h
  · have h3 := (Alg.res_eq_zero_iff c.O T _).2 (hgen (.inl (⟨w, hw⟩, ⟨j - 1, h.2⟩)))
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h3
    exact h3
  · exact map_one _
end
end
end

-- Source module: Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsHeckeIdeal

section

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000 in
private theorem absH (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {l : ℕ} [Fact l.Prime] {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (hA : H.Ax)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hθ : H.IsWt θ)
    (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) (hAut : H.AutomorphicHeckeSet ι P)
    (lam : Wt L l n) (hl : lam ∈ H.admitted) (hd : H.DenseWt θ lam) (a : H.Op → c.O) (K : H.Lev)
    {B : Type} [CommRing B] [Algebra c.O B] (D₀ : W.GDet n B H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Bˣ)
    (j : A →ₐ[c.O] B)
    (key : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (φ : A →ₐ[c.O] T) (gen : H.Op → T),
      (∀ i, gen i - algebraMap c.O T (a i) ∈ maximalIdeal T) →
      ∀ (D : W.GDet n T H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Tˣ), D.IsCont (maximalIdeal T) →
      (∀ v i, Alg.AdicCont (maximalIdeal T) fun g => (ψ v i g : T)) →
      (∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
        D.chi (MonoidAlgebra.single (H.prj σ⁻¹) 1) =
          heckePol n (normV w.1) fun j => if h : 0 < j ∧ j - 1 < n then gen (.inl (w, ⟨j - 1, h.2⟩)) else 1) →
      (∀ v i (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)) (y : Uo ((H.Sl v).adicCompletion L)),
        (g : G L Ω) = (s : G L Ω) → H.art v s = y →
        (ψ v i g * H.epsV T v g ^ (i : ℕ) : Tˣ) * φ (θ (eV n H.Sl v i y)) = 1) →
      (∀ v (j : Fin n) (s : Weil (H.ovr v)) (g : Dec (F := L) (H.pl v)), (g : G L Ω) = (s : G L Ω) → H.art v s = Hi.unif _ →
        ((∏ i with i ≤ j, ψ v i g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = gen (.inr (v, j))) →
      ∀ Gd : (T →ₐ[c.O] Qbar l) → Prop, (∀ t : T, (∀ x, Gd x → x t = 0) → t = 0) →
      (∀ x, Gd x → ∃ ρ : H.Gq →* GL (Fin n) (Qbar l), P lam ρ ∧ D.map x.toRingHom = W.GDet.ofRep (W.mat ρ) ∧
        ∀ v, W.HasFlag (ρ.comp (H.dec v)) fun i => W.pushCh x.toRingHom (ψ v i)) →
      ∃ f : B →ₐ[c.O] T, D₀.map f.toRingHom = D ∧ (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = ψ v i) ∧ ∀ b, f (j b) = φ b) :
    ∃ J : Ideal B, H.IsJ θ a K D₀ ψ₀ j J := by
  by_cases hne : H.MK θ a K = ⊥
  · exact ⟨⊤, Or.inl ⟨hne, rfl⟩⟩
  haveI hF : Fact (CommOn (H.MK θ a K) (H.op A)) := ⟨((hiComm L Ω l n c _ hA A θ hθ K).2.2.2 a).1⟩
  obtain ⟨hCO, -, -, hres, -, hgen⟩ := hiAlg L Ω l n c _ hA A θ hθ a K hne
  obtain ⟨D, ψ, hU⟩ := _root_.UpperTheory.V.Hi.coreDet_alt hN L Ω l n c _ hA A θ hθ ι _ hAut lam hl hd a K
  have hO := _root_.UpperTheory.V.Z.Ord.core_hecke_of_automorphic_hecke_dense_weight hN L Ω l n c _ hA A θ hθ ι _ hAut lam hl hd a K D ψ hU
  obtain ⟨f, h1, h2, h3⟩ := key (H.TK θ a K) (IsScalarTower.toAlgHom c.O A _) (H.gen θ a K) hres D ψ hU.cont hU.ψ_cont
    hU.frob hU.ψ_unit hU.ψ_unif (fun x => H.Good θ (x.toRingHom.comp (algebraMap A _)) lam) (hO.sep lam hl hd)
    fun x hx => by
      obtain ⟨ρ, -, -, e1, e2, e3⟩ := hO.pt lam hl x hx.2.1
      exact ⟨ρ, e1, e2, fun v => (e3 hx v).1⟩
  have h2' : (fun v i => W.pushCh f.toRingHom (ψ₀ v i)) = ψ := funext fun v => funext fun i => h2 v i
  have hU' : H.IsMap θ a K D₀ ψ₀ f := by
    unfold HSet.IsMap
    rw [h1, h2']
    exact hU
  exact ⟨RingHom.ker f, Or.inr ⟨hF, hCO, f, hne, hU',
    deformationRing_to_heckeAlgebra_surjective L Ω l n c _ hA A _ B (H.gen θ a K) D₀ ψ₀ f hU'.frob hU'.ψ_unif _ h3 hgen, h3, rfl⟩⟩
theorem UpperTheory.V.Hi.exists_hecke_ideal :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), ∃ J : Ideal B.B, R.IsJ B K J := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K
  have hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis := hP.litN
  have hA : (hset Q R.τ₀).Ax := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V Q c R.m R.τ₀
  have hAut := _root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor hP l L Ω s n hn V Q c r ι R.m R.τ₀ R.type
  let lam : Wt L l n := fun _ => ⟨0, fun _ _ _ => le_rfl⟩
  have hd : (hset Q R.τ₀).DenseWt R.θ lam := (_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta hN l L Ω s n hn V Q c R.m R.τ₀ r Λ R.θ R.theta).2 lam
  refine absH hN (hset Q R.τ₀) hA Λ.Λ R.θ R.isWt ι _ hAut lam (Set.mem_univ _) hd R.a K B.u.D B.u.ψ (Λ.toPair B.u) ?_
  intro T _ _ _ φ gen hres D ψ hc hψ hfr hun huf Gd hsep hpt
  exact JEx.map_of_rel B Λ φ D ψ hc (_root_.UpperTheory.V.Hi.heckeDeterminant_reduction_eq_residual_alt l L Ω s n V Q c r ι Λ R hA T gen hres D hc hfr)
    (_root_.UpperTheory.V.Hi.exists_ordinaryCharacters_heckeAlgebra' l L Ω s n V Q c r ι Λ R hA T φ gen hres ψ hψ hun huf)
    (_root_.UpperTheory.V.Hi.heckeDeterminant_satisfies_deformation_relations_alt l L Ω s n hn V c r ι lam T D ψ Gd hsep hpt)
end
end
end
