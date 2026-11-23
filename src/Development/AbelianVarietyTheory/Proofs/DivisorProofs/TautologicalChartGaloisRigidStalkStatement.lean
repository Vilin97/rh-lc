module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartEqOfSameGenericPoint

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemPowOfMemMaximalIdeal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtUniq

theorem sub_mem_pow_of_mem_maximalIdeal {O W V : Type} [CommRing O] [IsLocalRing O] [CommRing W]
    [IsLocalRing W] [CommRing V] [IsLocalRing V] (φ : O →+* W)
    (hm : (maximalIdeal O).map φ = maximalIdeal W)
    (θ₁ θ₂ : W →+* V) [IsLocalHom θ₂] (hO : θ₁.comp φ = θ₂.comp φ) (k : ℕ)
    (hk : ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1)) :
    ∀ x ∈ maximalIdeal W, θ₁ x - θ₂ x ∈ maximalIdeal V ^ (k + 2) := by
  intro x hx
  rw [← hm] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    have := congrArg (fun f => f a) hO
    simp only [RingHom.comp_apply] at this
    rw [this, sub_self]; exact zero_mem _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), map_add (f := _), add_sub_add_comm]; exact add_mem hx hy
  | smul a x hx' hx =>
    have hx'' : x ∈ maximalIdeal W := by rw [← hm]; exact hx'
    have h2 : θ₂ x ∈ maximalIdeal V :=
      (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 hx'' (isUnit_of_map_unit θ₂ x h)
    simp only [smul_eq_mul, map_mul]
    have e : θ₁ a * θ₁ x - θ₂ a * θ₂ x = θ₁ a * (θ₁ x - θ₂ x) + (θ₁ a - θ₂ a) * θ₂ x := by ring
    rw [e]
    refine add_mem (Ideal.mul_mem_left _ _ hx) ?_
    rw [show k + 2 = (k + 1) + 1 from rfl, pow_succ]
    exact Ideal.mul_mem_mul (hk a) h2

abbrev Gr (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ) : Type :=
  ↥(maximalIdeal V ^ (k + 1)) ⧸ (maximalIdeal V • (⊤ : Submodule V ↥(maximalIdeal V ^ (k + 1))))

noncomputable instance (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ) : Module (ResidueField V) (Gr V k) :=
  inferInstanceAs (Module (V ⧸ maximalIdeal V) (Gr V k))

noncomputable abbrev grModule {W V : Type} [CommRing W] [IsLocalRing W] [CommRing V] [IsLocalRing V]
    (θ : W →+* V) [IsLocalHom θ] (k : ℕ) : Module (ResidueField W) (Gr V k) :=
  Module.compHom _ (ResidueField.map θ)

theorem gr_mk_eq_zero_iff (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ)
    (v : ↥(maximalIdeal V ^ (k + 1))) :
    (Submodule.Quotient.mk v : Gr V k) = 0 ↔ (v : V) ∈ maximalIdeal V ^ (k + 2) := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_top_iff, Ideal.smul_eq_mul, ← pow_succ']

theorem gr_mk_eq_mk (V : Type) [CommRing V] [IsLocalRing V] (k : ℕ)
    (u v : ↥(maximalIdeal V ^ (k + 1))) (h : (u : V) - v ∈ maximalIdeal V ^ (k + 2)) :
    (Submodule.Quotient.mk u : Gr V k) = Submodule.Quotient.mk v := by
  rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, gr_mk_eq_zero_iff]; simpa using h

theorem sub_mem_pow_succ {O W V : Type} [CommRing O] [IsLocalRing O] [CommRing W]
    [IsLocalRing W] [CommRing V] [IsLocalRing V] (φ : O →+* W)
    (hm : (maximalIdeal O).map φ = maximalIdeal W)
    (hu : ((residue W).comp φ).FormallyUnramified)
    (θ₁ θ₂ : W →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂] (hO : θ₁.comp φ = θ₂.comp φ) (k : ℕ)
    (hk : ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1)) :
    ∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 2) := by
  have hW := sub_mem_pow_of_mem_maximalIdeal φ hm θ₁ θ₂ hO k hk
  letI : Algebra O (ResidueField W) := ((residue W).comp φ).toAlgebra
  haveI : Algebra.FormallyUnramified O (ResidueField W) := hu
  letI : Module (ResidueField W) (Gr V k) := grModule θ₁ k
  letI : Module O (Gr V k) := Module.compHom _ (algebraMap O (ResidueField W))
  haveI : IsScalarTower O (ResidueField W) (Gr V k) := ⟨fun a b x => by
    show ResidueField.map θ₁ (a • b) • x = ResidueField.map θ₁ (algebraMap O _ a) • (ResidueField.map θ₁ b • x)
    rw [Algebra.smul_def, map_mul, mul_smul]⟩
  let δ₀ : W → Gr V k := fun w => Submodule.Quotient.mk ⟨θ₁ w - θ₂ w, hk w⟩
  have hsm : ∀ (c : W) (v : ↥(maximalIdeal V ^ (k + 1))), residue W c • (Submodule.Quotient.mk v : Gr V k) =
      Submodule.Quotient.mk (θ₁ c • v) := by
    intro c v
    show ResidueField.map θ₁ (residue W c) • (Submodule.Quotient.mk v : Gr V k) = _
    rw [ResidueField.map_residue]
    rfl
  let s := Function.surjInv (residue_surjective (R := W))
  have hs : ∀ w, δ₀ (s (residue W w)) = δ₀ w := by
    intro w
    refine gr_mk_eq_mk V k _ _ ?_
    have hmem : s (residue W w) - w ∈ maximalIdeal W := by
      rw [← Ideal.Quotient.eq]
      exact Function.surjInv_eq _ _
    have := hW _ hmem
    simp only [map_sub] at this ⊢
    convert this using 1; ring
  let D : Derivation O (ResidueField W) (Gr V k) :=
    { toFun := fun x => δ₀ (s x)
      map_add' := by
        intro x y
        obtain ⟨a, rfl⟩ := residue_surjective x
        obtain ⟨b, rfl⟩ := residue_surjective y
        rw [← map_add (f := _), hs, hs, hs, ← Submodule.Quotient.mk_add]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_add, map_add (f := _)]
        convert zero_mem (maximalIdeal V ^ (k + 2)) using 1; ring
      map_smul' := by
        intro c x
        obtain ⟨a, rfl⟩ := residue_surjective x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, show algebraMap O (ResidueField W) c = residue W (φ c) from rfl,
          ← map_mul, hs, hs]
        show _ = residue W (φ c) • δ₀ a
        rw [hsm]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_smul, smul_eq_mul, map_mul]
        have := congrArg (fun f => f c) hO
        simp only [RingHom.comp_apply] at this
        rw [this]
        convert zero_mem (maximalIdeal V ^ (k + 2)) using 1; ring
      map_one_eq_zero' := by
        show δ₀ (s 1) = 0
        rw [← map_one (residue W), hs]
        show (Submodule.Quotient.mk _ : Gr V k) = 0
        rw [gr_mk_eq_zero_iff]; simp
      leibniz' := by
        intro x y
        obtain ⟨a, rfl⟩ := residue_surjective x
        obtain ⟨b, rfl⟩ := residue_surjective y
        show δ₀ (s _) = residue W a • δ₀ (s _) + residue W b • δ₀ (s _)
        rw [← map_mul, hs, hs, hs, hsm, hsm, ← Submodule.Quotient.mk_add]
        refine gr_mk_eq_mk V k _ _ ?_
        simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul, map_mul]
        have e : θ₁ a * θ₁ b - θ₂ a * θ₂ b - (θ₁ a * (θ₁ b - θ₂ b) + θ₁ b * (θ₁ a - θ₂ a)) =
            (θ₁ a - θ₂ a) * (θ₂ b - θ₁ b) := by ring
        rw [e, show k + 2 = (k + 1) + 1 from rfl, pow_succ]
        refine Ideal.mul_mem_mul (hk a) ?_
        have := Ideal.pow_le_self (n := k + 1) (I := maximalIdeal V) (by omega) (hk b)
        rw [← neg_sub]; exact neg_mem this }
  have hD : ∀ x, D x = 0 := by
    intro x
    rw [← Derivation.liftKaehlerDifferential_comp_D D x,
      Subsingleton.elim (KaehlerDifferential.D O (ResidueField W) x) 0, map_zero]
  intro w
  have h1 : δ₀ w = 0 := by
    rw [← hs]
    exact hD (residue W w)
  exact (gr_mk_eq_zero_iff V k _).1 h1

theorem localHom_ext : ∀ (O W V : Type) [CommRing O] [IsLocalRing O] [CommRing W] [IsLocalRing W] [IsNoetherianRing W] [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (φ : O →+* W), IsAdicComplete (maximalIdeal W) W → IsEtaleCompletion φ → ((residue W).comp φ).FormallyUnramified → ∀ θ₁ θ₂ : W →+* V, IsLocalHom θ₁ → IsLocalHom θ₂ → θ₁.comp φ = θ₂.comp φ → (∀ w, θ₁ w - θ₂ w ∈ maximalIdeal V) → θ₁ = θ₂ := by
  intro O W V _ _ _ _ _ _ _ _ φ _ hφ hu θ₁ θ₂ h₁ h₂ hO hres
  have hk : ∀ k w, θ₁ w - θ₂ w ∈ maximalIdeal V ^ (k + 1) := by
    intro k
    induction k with
    | zero => simpa using hres
    | succ k ih => exact sub_mem_pow_succ φ hφ.2.1 hu θ₁ θ₂ hO k ih
  ext w
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal V).ne_top, Ideal.mem_iInf]
  intro i
  cases i with
  | zero => simp
  | succ i => exact hk i w

end GlobalTheory.EtUniq
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartEqOfSameGenericPointStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

theorem _root_.GlobalTheory.T.tautologicalChart_eq_of_same_genericPoint : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (θ₁ θ₂ : C.R →+* R'), IsCN R' → Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ (κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing C.R)), κ₁ ≫ jK C.R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK C.R = jK R' ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → spMap (θ₁.comp C.iw) ≫ C.u = spMap (θ₂.comp C.iw) ≫ C.u ∧ (θ₁.comp C.iw = θ₂.comp C.iw → ∀ k, θ₁ (C.s k) = θ₂ (C.s k)) := by
  first | exact @GlobalTheory.TInj.tautChart_eq_of_genPt | exact GlobalTheory.TInj.tautChart_eq_of_genPt | (intros; apply GlobalTheory.TInj.tautChart_eq_of_genPt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartGaloisRigidStalk

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.Inj

theorem spMap_comp_eq {S : Scheme.{0}} {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] (ξ : Sp R ⟶ S)
    (ρ₁ ρ₂ : R →+* R') (h : ρ₁.comp (Scheme.stalkClosedPointTo ξ).hom = ρ₂.comp (Scheme.stalkClosedPointTo ξ).hom) :
    spMap ρ₁ ≫ ξ = spMap ρ₂ ≫ ξ := by
  rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp]
  congr 2
  ext a
  exact congrArg (fun f => f a) h

theorem genPt_eq {X S : Scheme.{0}} (j : X ⟶ S) [Mono j] {R R' : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [CommRing R'] [IsDomain R'] (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X) (hy : y ≫ j = jK R ≫ ξ)
    (ρ₁ ρ₂ : R →+* R') (h : ρ₁.comp (Scheme.stalkClosedPointTo ξ).hom = ρ₂.comp (Scheme.stalkClosedPointTo ξ).hom)
    (κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R)) (h₁ : κ₁ ≫ jK R = jK R' ≫ spMap ρ₁)
    (h₂ : κ₂ ≫ jK R = jK R' ≫ spMap ρ₂) : κ₁ ≫ y = κ₂ ≫ y := by
  rw [← cancel_mono j, Category.assoc, Category.assoc, hy, ← Category.assoc, ← Category.assoc, h₁, h₂,
    Category.assoc, Category.assoc, spMap_comp_eq ξ ρ₁ ρ₂ h]

theorem stalk_comp_eq {X : Scheme.{0}} {W V : Type} [CommRing W] [IsLocalRing W] [CommRing V] [IsLocalRing V]
    (u : Sp W ⟶ X) (g₁ g₂ : W →+* V) [IsLocalHom g₁] [IsLocalHom g₂] (hu : spMap g₁ ≫ u = spMap g₂ ≫ u) :
    g₁.comp (Scheme.stalkClosedPointTo u).hom = g₂.comp (Scheme.stalkClosedPointTo u).hom := by
  have l : ∀ (g : W →+* V) [IsLocalHom g], IsLocalHom (Scheme.stalkClosedPointTo u ≫ CommRingCat.ofHom g).hom := by
    intro g _
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom]; infer_instance
  have e : ∀ (g : W →+* V) [IsLocalHom g], spMap g ≫ u = (SpecToEquivOfLocalRing X (.of V)).symm
      ⟨u (closedPoint W), Scheme.stalkClosedPointTo u ≫ CommRingCat.ofHom g, l g⟩ := by
    intro g _
    rw [SpecToEquivOfLocalRing_symm_apply, Spec.map_comp_assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have hinj := (SpecToEquivOfLocalRing X (.of V)).symm.injective ((e g₁).symm.trans (hu.trans (e g₂)))
  obtain ⟨h₁, h₂⟩ := SpecToEquivOfLocalRing_eq_iff.mp hinj
  simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp] at h₂
  ext a
  have := congrArg (fun q => q.hom a) h₂
  simpa using this

theorem base_eq {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ) {V : Type}
    [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (θ₁ θ₂ : C.R →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂]
    (hu : spMap (θ₁.comp C.iw) ≫ C.u = spMap (θ₂.comp C.iw) ≫ C.u) (hm : ∀ r, θ₁ r - θ₂ r ∈ maximalIdeal V) :
    θ₁.comp C.iw = θ₂.comp C.iw := by
  haveI : IsLocalHom C.iw := C.ψ_loc
  haveI : IsNoetherianRing C.W := C.noeth
  have hO := stalk_comp_eq C.u (θ₁.comp C.iw) (θ₂.comp C.iw) hu
  exact GlobalTheory.EtUniq.localHom_ext _ _ _ _ C.complete C.u_et C.u_sep _ _ inferInstance inferInstance hO (fun w => hm _)

theorem eq_of_base_coord {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {φ : InvFun ℤ} (C : Taut ζ g n φ) {V : Type}
    [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (θ₁ θ₂ : C.R →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂]
    (hW : θ₁.comp C.iw = θ₂.comp C.iw) (hs : ∀ k, θ₁ (C.s k) = θ₂ (C.s k)) : θ₁ = θ₂ := by
  refine GlobalTheory.TChart.cuniq _ _ _ C.ψ C.compl θ₁ θ₂ inferInstance inferInstance ?_
  apply MvPolynomial.ringHom_ext
  · intro w
    exact congrArg (fun f => f w) hW
  · intro k
    exact hs k

end GlobalTheory.TChart.Inj


open GlobalTheory.TChart.Inj in
theorem GlobalTheory.TChart.galRigid_stalk_of_isFam : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j], ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → GalRigid (Scheme.stalkClosedPointTo ξ).hom := by
  intro g n φ hn F S j _ C G₁ _ _ y α₁ ξ hF hy R' _ _ _ θ σ hR' hθ hfin hσ hfix hres
  haveI : IsNoetherianRing R' := hR'.1
  haveI : IsLocalHom θ := RingHom.IsIntegral.isLocalHom hfin.to_isIntegral hθ
  haveI : IsLocalHom ((σ : R' →+* R').comp θ) := by
    haveI : IsLocalHom (σ : R' →+* R') := inferInstance
    infer_instance
  obtain ⟨κ₁, hκ₁⟩ := GlobalTheory.PolDeg.exists_genericMap hθ
  obtain ⟨κ₂, hκ₂⟩ := GlobalTheory.PolDeg.exists_genericMap (ρ := (σ : R' →+* R').comp θ) (σ.injective.comp hθ)
  have hf : θ.comp (Scheme.stalkClosedPointTo ξ).hom =
      ((σ : R' →+* R').comp θ).comp (Scheme.stalkClosedPointTo ξ).hom :=
    RingHom.ext fun a => (hfix a).symm
  have hyy := genPt_eq j ξ y hy _ _ hf κ₁ κ₂ hκ₁ hκ₂
  have hm : ∀ r, θ r - ((σ : R' →+* R').comp θ) r ∈ maximalIdeal R' := fun r => by
    rw [← neg_sub]; exact neg_mem (hres r)
  obtain ⟨hu, hs'⟩ := GlobalTheory.T.tautologicalChart_eq_of_same_genericPoint hn F C G₁ y α₁ hF R' θ ((σ : R' →+* R').comp θ) hR' hθ (σ.injective.comp hθ)
    inferInstance inferInstance κ₁ κ₂ hκ₁ hκ₂ hyy
  have hW := base_eq C θ ((σ : R' →+* R').comp θ) hu hm
  have e := eq_of_base_coord C θ ((σ : R' →+* R').comp θ) hW (hs' hW)
  intro r
  exact (congrArg (fun f => f r) e).symm
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalChartGaloisRigidStalkStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.tautologicalChart_galois_rigid_stalk : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (S : Scheme.{0}) (j : F.X ⟶ S) [IsOpenImmersion j], ∀ (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left) (ξ : Sp C.R ⟶ S), C.IsFam F G₁ y α₁ → y ≫ j = jK C.R ≫ ξ → GalRigid (Scheme.stalkClosedPointTo ξ).hom := by
  first | exact @GlobalTheory.TChart.galRigid_stalk_of_isFam | exact GlobalTheory.TChart.galRigid_stalk_of_isFam | (intros; apply GlobalTheory.TChart.galRigid_stalk_of_isFam <;> assumption)
end
end
