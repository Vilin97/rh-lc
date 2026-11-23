module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubRedMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseParamTaylorShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAnalyticChartsRealizationOfAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallChartPairAlongLinearMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTaylorAlgHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Functor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicPointExtOfIsSeparated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfComap
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraMulOfProdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodClassInjectiveOfRichChartsStatement
import Mathlib.Algebra.Module.StablyFree.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorHolomorphicExtOfValues
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Polynomial.Basic
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdEqZeroOfSuccLe

section

@[expose] public section

open Filter Topology

namespace GlobalTheory.PeriodFamily

theorem prod_eq_zero_of_succ_le {I : Type} {D : Type} [CommRing D] (N : ℕ) (t : I → D)
    (h : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) (k : ℕ) (hk : N + 1 ≤ k) (s : Fin k → I) :
    ∏ a, t (s a) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [Fin.prod_univ_add, h (fun a => s (Fin.castAdd j a)), zero_mul]

theorem taylor_eq_of_le : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (N' : ℕ), N ≤ N' → ∀ f : (I → ℂ) → ℂ, GlobalTheory.PeriodFamily.taylor N' t f = GlobalTheory.PeriodFamily.taylor N t f := by
  intro I _ _ D _ _ N t h N' hN f
  induction N', hN using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    rw [← ih]
    unfold taylor
    rw [Finset.sum_range_succ _ (n + 1)]
    simp [prod_eq_zero_of_succ_le N t h (n + 1) (by omega)]

end GlobalTheory.PeriodFamily
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TenContractTmul

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct

namespace GlobalTheory.AnPer

open GlobalTheory.CatCoh

attribute [local instance] Charts.Obj.cAlg

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}
  {D : Type} [CommRing D] [Algebra ℂ D]

def Charts.Obj.tenContract (ℓ : D →ₗ[ℂ] ℂ) (T : K.Obj) : T.ten D →ₗ[ℂ] T.C :=
  (TensorProduct.lid ℂ T.C).toLinearMap ∘ₗ LinearMap.rTensor T.C ℓ

theorem Charts.Obj.tenContract_tmul (ℓ : D →ₗ[ℂ] ℂ) (T : K.Obj) (d : D) (c : T.C) :
    T.tenContract ℓ (d ⊗ₜ c) = ℓ d • c := rfl

theorem Charts.Hom.tenContract_ten (ℓ : D →ₗ[ℂ] ℂ) {T T' : K.Obj} (f : T ⟶ T') (x : T.ten D) :
    T'.tenContract ℓ (Charts.Hom.ten D f x) = f.φ (T.tenContract ℓ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul d c =>
    rw [Charts.Hom.ten_tmul, Charts.Obj.tenContract_tmul, Charts.Obj.tenContract_tmul]
    exact (map_smul (Charts.Hom.φc f) (ℓ d) c).symm

theorem Charts.tenZ_eq_zero (K : Charts F) (hK : K.Rich) (hz : ∃ z, z ∈ F.V) {D : Type} [CommRing D] [Algebra ℂ D]
    (p : Λ →+ D) (h : H1.mk _ (K.tenZ p) = 0) : p = 0 := by
  obtain ⟨z, hz⟩ := hz
  obtain ⟨G, hG⟩ := H1.mk_eq_zero.1 h
  refine AddMonoidHom.ext fun l ↦ (Module.forall_dual_apply_eq_zero_iff ℂ (p l)).1 fun ℓ ↦ ?_
  let q : Λ →+ Hol F.V := ((algebraMap ℂ (Hol F.V)).toAddMonoidHom.comp ℓ.toAddMonoidHom).comp p
  have h0 : K.perZ 0 = 0 := Subtype.ext (by
    funext T T' f
    exact map_zero (algebraMap (Hol F.V) T'.C))
  have hq : K.perCl q = K.perCl 0 := by
    unfold Charts.perCl
    rw [h0, map_zero]
    refine H1.mk_eq_zero.2 ⟨fun T ↦ T.tenContract ℓ (G T), ?_⟩
    funext T T' f
    have e : G T' - Charts.Hom.ten D f (G T) = (p f.deg ⊗ₜ[ℂ] (1 : T'.C) : T'.ten D) :=
      congrFun (congrFun (congrFun hG T) T') f
    have e' := congrArg (T'.tenContract ℓ) e
    rw [map_sub, Charts.Hom.tenContract_ten, Charts.Obj.tenContract_tmul, ← Algebra.algebraMap_eq_smul_one] at e'
    exact e'
  have h1 : algebraMap ℂ (Hol F.V) (ℓ (p l)) = 0 := DFunLike.congr_fun (GlobalTheory.T.periodClass_injective_of_rich_charts K hK q 0 hq) l
  have h2 := congrArg (Hol.ev z hz) h1
  rwa [AlgHom.commutes, map_zero] at h2

end GlobalTheory.AnPer
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TenFib

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] Charts.Obj.cAlg

namespace GlobalTheory.AnPer.TenFib

open GlobalTheory.CatCoh

variable {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} (D : Type) [CommRing D]
  [Algebra ℂ D] {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀)

def inc (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) : CoefMap (algebraMap ℂ D) (O (dp0 ℂ) s₀) (K₀.Ten D) where
  G := r₀.functor
  α T := (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom
  naturality _ _ := rfl
  smul T a b := by
    subst hσ
    change ((1 : D) ⊗ₜ[ℂ] (a • (show T.C from b)) : T.ten D) = algebraMap ℂ D a • ((1 : D) ⊗ₜ[ℂ] (show T.C from b) : T.ten D)
    rw [tmul_smul, algebraMap_smul]

theorem ten_fib : ∀ {I₀ : Type} [Fintype I₀] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F₀ : Fam I₀ g Λ} {K₀ : Charts F₀} {D : Type} [CommRing D] [Algebra ℂ D] (π : D →ₐ[ℂ] ℂ) {X₀ : Scheme.{0}} {s₀ : X₀ ⟶ Sp ℂ} {σ₀ : ℂ →+* Hol F₀.V} (r₀ : Real K₀ s₀ σ₀) (hσ : σ₀ = algebraMap ℂ (Hol F₀.V)) {D₀ : Type} [CommRing D₀] {π₀ : D₀ →+* ℂ} (κ : DividedPowers (RingHom.ker π₀)) {s' : X₀ ⟶ Sp D₀} (hs : s' = s₀ ≫ spMap π₀) (io : D₀ →+* D) (hio : ∀ d, π (io d) = π₀ d) (hπ : IsNilpotent (RingHom.ker π)) (j₀ : ℂ →+* D₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' j₀ φ), (∀ a, io (j₀ a) = algebraMap ℂ D a) → ∀ (c : FirstDeRham s₀) (p : Λ → ℂ) (per : Λ →+ Hol F₀.V) (q : Λ →+ D), (∀ l, per l = algebraMap ℂ _ (p l)) → (∀ l, q l = algebraMap ℂ D (p l)) → r₀.coef.pull1 c = K₀.perCl per → (r₀.tenCoef π hσ κ hs io hio hπ).pull1 (k.pull1 c) = GlobalTheory.CatCoh.H1.mk _ (K₀.tenZ q) := by
  intro I₀ _ g Λ _ F₀ K₀ D _ _ π X₀ s₀ σ₀ r₀ hσ D₀ _ π₀ κ s' hs io hio hπ j₀ φ hφ k hj c p per q hper hq hc
  subst hφ
  let θ : (inc D r₀ hσ).G ⟶ (k.coef.comp (r₀.tenCoef π hσ κ hs io hio hπ)).G :=
    { app := fun T ↦
        { φ := { (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom with
            commutes' := fun a ↦ by
              subst hσ
              change (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D) (algebraMap ℂ T.C a) =
                algebraMap D (T.ten D) (io (j₀ a))
              rw [AlgHom.commutes, hj, ← IsScalarTower.algebraMap_apply] }
          φ₀ := RingHom.id (T.C ⧸ T.J)
          comm := fun b ↦ congrArg (Ideal.Quotient.mk T.J) (by
            change (show T.C from b) = T.red π (1 ⊗ₜ (show T.C from b))
            rw [Charts.Obj.red_tmul, map_one, map_one, _root_.one_mul])
          dp := letI := T.tenRat (D := D); isDPMorphism_of_rat T.δ (T.tenδ π)
            (Algebra.TensorProduct.includeRight : T.C →ₐ[ℂ] T.ten D).toRingHom fun b hb ↦ by
              change T.red π (1 ⊗ₜ b) ∈ T.J
              rwa [Charts.Obj.red_tmul, map_one, map_one, _root_.one_mul]
          pt := by
            change spMap (RingHom.id (T.C ⧸ T.J)) ≫ (r₀.obj T).x = (r₀.obj T).x ≫ 𝟙 X₀
            rw [Cris.spMap_id]
            exact (Category.id_comp _).trans (Category.comp_id _).symm }
      naturality := fun _ _ _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  have e := (inc D r₀ hσ).pullCohomologyOne_eq_of_natTrans _ θ (fun _ _ ↦ rfl) c
  rw [CoefMap.pullCohomologyOne_comp] at e
  refine e.symm.trans ?_
  obtain ⟨f, rfl⟩ := CatCoh.H1.mk_surjective _ c
  obtain ⟨G, hG⟩ := CatCoh.H1.mk_eq_mk.1 hc
  refine CatCoh.H1.mk_eq_mk.2 ⟨fun T ↦ ((1 : D) ⊗ₜ[ℂ] (show T.C from G T) : T.ten D), ?_⟩
  funext T T' ψ
  have h1 := congrFun (congrFun (congrFun hG T) T') ψ
  have h2 : ((1 : D) ⊗ₜ[ℂ] ((show T'.C from G T') - ψ.φ (G T)) : T'.ten D) = (1 : D) ⊗ₜ[ℂ] (show T'.C from f.1 _ _ (r₀.functor.map ψ)) -
      (1 : D) ⊗ₜ[ℂ] (algebraMap (Hol F₀.V) T'.C (per ψ.deg)) := by
    rw [← tmul_sub]; exact congrArg _ h1
  refine (tmul_sub _ _ _).symm.trans (h2.trans ?_)
  congr 1
  change _ = algebraMap D (T'.ten D) (q ψ.deg)
  rw [hper, hq]
  exact (Algebra.TensorProduct.includeRight : T'.C →ₐ[ℂ] T'.ten D).commutes (p ψ.deg)

end GlobalTheory.AnPer.TenFib
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNilpotentOfIsNilDP

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.TaylorCore

open GlobalTheory.PeriodFamily GlobalTheory.CatCoh

theorem isNilpotent_of_isNilDP {D : Type} [CommRing D] {J : Ideal D} {κ : DividedPowers J} (h : IsNilDP κ) : IsNilpotent J := by
  obtain ⟨N, hN⟩ := h
  have key : ∀ (n : ℕ) (l : List D), (∀ x ∈ l, x ∈ J) → N ≤ l.length + n → ∀ y ∈ J ^ n, l.prod * y = 0 := by
    intro n
    induction n with
    | zero =>
      intro l hl hn y _
      have := hN (l.map fun x => (1, x)) (by simpa using hl) (by simpa [Function.comp_def] using hn)
      rw [List.map_map, List.map_congr_left (f := (fun p : ℕ × D ↦ κ.dpow p.1 p.2) ∘ fun x ↦ (1, x)) (g := id)
        fun x hx => κ.dpow_one (hl x hx), List.map_id] at this
      rw [this, zero_mul]
    | succ n ih =>
      intro l hl hn y hy
      rw [pow_succ'] at hy
      refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) fun a b ha hb => by rw [mul_add, ha, hb, add_zero]
      have := ih (a :: l) (by simpa [ha] using hl) (by simp; omega) b hb
      rw [List.prod_cons] at this
      linear_combination this
  exact ⟨N, eq_bot_iff.2 fun y hy => by simpa using key N [] (by simp) (by simp) y hy⟩

def tayHom {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D)
    (ht : ∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) {V : Opens (I → ℂ)} (h0 : (0 : I → ℂ) ∈ V) : Hol V →+* D where
  toFun f := PeriodFamily.taylor N t f.fn
  map_one' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun _ => 1) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using by rw [← Hol.ev_apply z hz, map_one]),
      (taylor_formal_properties N t).2.2.1, map_one]
  map_zero' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun _ => 0) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using by rw [← Hol.ev_apply z hz, map_zero]),
      (taylor_formal_properties N t).2.2.1, map_zero]
  map_mul' f f' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun z => f.fn z * f'.fn z) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using Hol.fn_mul _ _ hz),
      taylor_mul_of_prod_eq_zero N t ht _ _ (f.analytic _ h0) (f'.analytic _ h0)]
  map_add' f f' := by
    rw [(taylor_formal_properties N t).2.2.2.1 _ (fun z => f.fn z + f'.fn z) (by
      filter_upwards [V.isOpen.mem_nhds h0] with z hz using Hol.fn_add _ _ hz),
      (taylor_formal_properties N t).1 _ _ (f.analytic _ h0) (f'.analytic _ h0)]

theorem ev_red {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {D : Type} [CommRing D] [Algebra ℂ D]
    (π : D →ₐ[ℂ] ℂ) (p : E) (hp : p ∈ W) (x : D ⊗[ℂ] Hol W) :
    Hol.ev p hp (Algebra.TensorProduct.lift ((Algebra.ofId ℂ (Hol W)).comp π) (AlgHom.id ℂ (Hol W))
      (fun _ _ ↦ Commute.all _ _) x) =
    π (Algebra.TensorProduct.lift (AlgHom.id ℂ D) ((Algebra.ofId ℂ D).comp (Hol.ev p hp)) (fun _ _ ↦ Commute.all _ _) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul d c =>
    simp only [Algebra.TensorProduct.lift_tmul, map_mul, AlgHom.comp_apply, AlgHom.id_apply, Algebra.ofId_apply,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

theorem main : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} {B : Type} [CommRing B] {X X₀ : Scheme.{0}} {s : X ⟶ Sp B} {s₀ : X₀ ⟶ Sp ℂ} {σ : B →+* Hol F.V} (e : Unif F s σ) (e₀ : Unif F₀ s₀ (algebraMap ℂ (Hol F₀.V))), X.IsSeparated → X₀.IsSeparated → (0 : I → ℂ) ∈ F.V → (∃ z, z ∈ F₀.V) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (φ₀ : X₀ ⟶ X), (∀ p : Tot Empty g, p.1 ∈ F₀.V → e₀.E p ≫ φ₀ = e.E (0, p.2)) → ∀ (D : Type) [CommRing D] [Algebra ℂ D] (π : D →+* ℂ) (κ : DividedPowers (RingHom.ker π)), IsNilDP κ → (∀ a : ℂ, π (algebraMap ℂ D a) = a) → ∀ (N : ℕ) (t : I → D), (∀ i, π (t i) = 0) → (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ (j : B →+* D), (∀ b, j b = GlobalTheory.PeriodFamily.taylor N t (σ b).fn) → ∀ (s' : X₀ ⟶ Sp D), s' = s₀ ≫ spMap π → ∀ (n : IsMor (dp0 B) s κ s' j φ₀) (φ : X₀ ⟶ X₀), φ = 𝟙 X₀ → ∀ (k : IsMor (dp0 ℂ) s₀ κ s' (algebraMap ℂ D) φ) (c : FirstDeRham s) (per : Λ →+ Hol F.V), IsPeriod e c per → ∀ (m : ℕ) (d : Fin m → D) (cs : Fin m → FirstDeRham s₀) (p : Fin m → Λ → ℂ) (ps : Fin m → Λ →+ Hol F₀.V), (∀ i l, ps i l = algebraMap ℂ _ (p i l)) → (∀ i, IsPeriod e₀ (cs i) (ps i)) → n.pull1 c = ∑ i, d i • k.pull1 (cs i) → ∀ l, ∑ i, d i * algebraMap ℂ D (p i l) = GlobalTheory.PeriodFamily.taylor N t (per l).fn := by
  intro I _ _ g Λ _ F F₀ B _ X X₀ s s₀ σ e e₀ hX hX₀ h0 hV₀ hτ φ₀ hφ₀ D _ _ π κ hκ hπ N t ht htN j hj s' hs' n φ hφ k c per hper
    m d cs p ps hps hcs hdec l
  let πa : D →ₐ[ℂ] ℂ := { π with commutes' := hπ }
  obtain ⟨D', _, _, io, π', nn, hio, hpio, hnil, hn0, hn2, hnt⟩ := SquareZeroSum.exists_sum_sq_zero N D πa t
    (isNilpotent_of_isNilDP hκ) ht htN
  obtain ⟨M, hM⟩ := id hnil
  have hJ : ∀ s : Fin (N + M + 1) → D', (∀ a, s a ∈ RingHom.ker π') → ∏ a, s a = 0 := fun s hs => by
    have h1 : ∏ a, s a ∈ ∏ _a : Fin (N + M + 1), RingHom.ker π' := Ideal.prod_mem_prod fun a _ => hs a
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := Ideal.pow_le_pow_right (show M ≤ N + M + 1 by omega) h1
    rwa [hM, Ideal.zero_eq_bot, Ideal.mem_bot] at h2
  have ht0 : ∀ i, π' (io (t i)) = 0 := fun i => (hpio _).trans (ht i)
  have ht' : ∀ s : Fin (N + M + 1) → I, ∏ a, io (t (s a)) = 0 := fun s => hJ _ fun a => ht0 _
  have hT : ∀ f, PeriodFamily.taylor (N + M) (fun i => io (t i)) f = io (PeriodFamily.taylor N t f) := fun f => by
    rw [← (taylor_formal_properties (N + M) t).2.2.2.2.1 D' io f, taylor_eq_of_le N t htN _ (Nat.le_add_right _ _)]
  have hred : ∀ f, π' (PeriodFamily.taylor (N + M) (fun i => io (t i)) f) = f 0 := fun f => by
    have h1 : PeriodFamily.taylor (N + M) (fun i => io (t i)) f - algebraMap ℂ D' (f 0) ∈ RingHom.ker π' :=
      (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact ht0 i)) ((taylor_formal_properties (N + M) _).2.2.2.2.2 f)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero, AlgHom.commutes] at h1
    exact h1
  obtain ⟨K₀, K, ν, hrich, hK₀, hK, hW, hν⟩ := ChartPair.exists_pair e₀ e (fun _ => 0) analyticOnNhd_const (fun _ _ => h0)
    LinearMap.id (AddMonoidHom.id Λ) fun l z _ => (hτ l z).symm
  obtain ⟨r₀, hr₀, -⟩ := exists_real_isFor e₀ hX₀ K₀ hK₀
  obtain ⟨r, hr, -⟩ := exists_real_isFor e hX K hK
  choose Ta hTa hTd using fun k => TaylorHom.exists_taylor_algHom (N + M) (fun i => io (t i)) ht' (K.W (ν k)) (K₀.W k) (hW k)
  let τV : Hol F.V →+* D' := tayHom (N + M) (fun i => io (t i)) ht' h0
  have hfam := TenFam.main π' r₀ rfl κ hs' (io : D →+* D') hpio hnil K r ν hν Ta τV
    (fun k f => tensor_hol_ext_of_values _ _ _ _ fun q hq => by
      rw [hTa k _ q hq, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      refine (taylor_formal_properties _ _).2.2.2.1 _ _ ?_
      have hc : Continuous fun z : I → ℂ => ((z, q.2) : Tot I g) := by fun_prop
      filter_upwards [hc.continuousAt.preimage_mem_nhds ((K.W (ν k)).isOpen.mem_nhds (hW k q hq))] with z hz
      exact K.fn_cst _ f hz)
    hTd (fun l k' k h₀ => close_paramTaylor_shift F F₀ h0 hτ _ (N + M) hJ _ N nn hn0 hn2 hnt K K₀ l _ _ k k' (hν l k' k h₀) h₀
      (hW k') (Ta k) (Ta k') (hTa k) (hTa k')) φ₀
    (fun k => point_hol_ext_of_isSeparated _ hX _ _ fun q hq => by
      rw [← Category.assoc, ← Category.assoc, hr₀ k q hq, hφ₀ q (K₀.base k q hq), ← hr (ν k) (0, q.2) (hW k q hq),
        ← Cris.spMap_comp]
      refine congrArg (fun ψ => spMap ψ ≫ r.x (ν k)) (RingHom.ext fun h => ?_)
      refine (ev_red π' q hq (Ta k h)).trans ?_
      rw [hTa k h q hq, hred]
      exact (Hol.ev_apply _ _ _).symm)
    j n (fun b => (congrArg io (hj b)).trans (hT _).symm) c per (τV.toAddMonoidHom.comp per) (fun _ => rfl) (hper K r hr)
  obtain ⟨z₀, hz₀⟩ := hV₀
  let q : Fin m → Λ →+ D' := fun i => ((algebraMap ℂ D').comp (Hol.ev z₀ hz₀).toRingHom).toAddMonoidHom.comp (ps i)
  have hq : ∀ i l, q i l = algebraMap ℂ D' (p i l) := fun i l =>
    congrArg (algebraMap ℂ D') ((congrArg (Hol.ev z₀ hz₀) (hps i l)).trans ((Hol.ev z₀ hz₀).commutes _))
  have hfib := fun i => TenFib.ten_fib π' r₀ rfl κ hs' (io : D →+* D') hpio hnil (algebraMap ℂ D) φ hφ k io.commutes (cs i) (p i)
    (ps i) (q i) (hps i) (hq i) (hcs i K₀ r₀ hr₀)

  rw [hdec, map_sum] at hfam
  simp only [LinearMap.map_smulₛₗ, hfib] at hfam
  have hz : K₀.tenZ (∑ i, io (d i) • q i - τV.toAddMonoidHom.comp per) =
      ∑ i, io (d i) • K₀.tenZ (q i) - K₀.tenZ (τV.toAddMonoidHom.comp per) := by
    let Z : (Λ →+ D') →ₗ[D'] Z1 (K₀.Ten D') :=
      { toFun := K₀.tenZ
        map_add' := fun a b => Subtype.ext (by funext T T' f; exact map_add (algebraMap D' (T'.ten D')) _ _)
        map_smul' := fun a b => Subtype.ext (by
          funext T T' f
          exact (map_mul (algebraMap D' (T'.ten D')) _ _).trans (Algebra.smul_def _ _).symm) }
    change Z _ = ∑ i, io (d i) • Z _ - Z _

    simp only [map_sub, map_sum, map_smul]
  have := Charts.tenZ_eq_zero K₀ hrich ⟨z₀, hz₀⟩ (∑ i, io (d i) • q i - τV.toAddMonoidHom.comp per) (by

    rw [hz, map_sub, ← hfam, map_sum]
    simp only [map_smul]
    exact sub_self _)
  have h1 := DFunLike.congr_fun (sub_eq_zero.1 this) l
  refine hio ?_

  rw [← hT, map_sum]
  refine Eq.trans ?_ h1
  change _ = (AddMonoidHom.eval l) (∑ i, io (d i) • q i)
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => by
    change io (d i * algebraMap ℂ D (p i l)) = (io (d i) • q i) l
    rw [map_mul, io.commutes, AddMonoidHom.smul_apply, hq, smul_eq_mul]

end GlobalTheory.AnPer.TaylorCore
end
end
end
