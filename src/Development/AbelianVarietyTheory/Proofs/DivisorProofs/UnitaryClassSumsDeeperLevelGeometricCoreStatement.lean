module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CPtEqOfNormValLtOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumNormEqOfUniqueLeast
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepEqOfCongMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeeperUnitaryLevelGaloisActsOnLabelsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfClassSumApprox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsUnitaryClassicalTraitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivLabelledLatticesUnitaryTraitsStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntClosureAutExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureStalkFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliPointCompCompactificationStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryThetaFourierClassSumsDeeperIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsExtendToDeeperLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernel

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassLimitNormLe

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem class_limit_norm_le : ∀ (p : ℕ) [Fact p.Prime] (X Y : Type) [AddCommGroup X] [AddCommGroup Y] (e : X ≃+ Y) (β : LinearMap.BilinForm ℤ X) (be : LinearMap.BilinForm ℤ Y) (sc sc' : ℝ), 0 < sc → (∀ a b, sc * (β a b : ℝ) = sc' * (be (e a) (e b) : ℝ)) → ∀ (m : ℕ) (t : Y → PadicAlgCl p), (∀ μ, ‖t μ‖ ≤ Real.exp (-(sc' * (be μ μ : ℝ) / 2))) → ∀ (v : PadicAlgCl p) (ν : Y), (∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset Y, ∀ S : Finset Y, (∀ μ ∈ S, CongMod m μ ν) → (∀ μ ∈ S₀, CongMod m μ ν → μ ∈ S) → ‖v - ∑ μ ∈ S, t μ‖ ≤ δ) → ∀ μ : X, CongMod m (e μ) ν → (∀ μ' : X, CongMod m μ' μ → β μ μ ≤ β μ' μ') → ‖v‖ ≤ Real.exp (-(sc * (β μ μ : ℝ)) / 2) := by
  intro p _ X Y _ _ e β be sc sc' hsc hid m t ht v ν hv μ hμν hmin
  set R := Real.exp (-(sc * (β μ μ : ℝ)) / 2) with hR
  have hR0 : 0 ≤ R := (Real.exp_pos _).le
  have hterm : ∀ μ' : Y, CongMod m μ' ν → ‖t μ'‖ ≤ R := by
    intro μ' h'
    obtain ⟨w1, hw1⟩ := h'
    obtain ⟨w2, hw2⟩ := hμν
    have hc : CongMod m (e.symm μ') μ := by
      refine ⟨e.symm (w1 - w2), ?_⟩
      have : μ' = e μ + m • (w1 - w2) := by rw [hw1, hw2, smul_sub]; abel
      rw [this, map_add (f := _), map_nsmul, AddEquiv.symm_apply_apply]
    have hle := hmin _ hc
    have hle' : sc * (β μ μ : ℝ) ≤ sc' * (be μ' μ' : ℝ) := by
      have h2 := hid (e.symm μ') (e.symm μ')
      rw [AddEquiv.apply_symm_apply] at h2
      rw [← h2]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) hsc.le
    refine (ht μ').trans ?_
    rw [hR]
    apply Real.exp_le_exp.mpr
    linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨S₀, hS₀⟩ := hv δ hδ
  have h1 := hS₀ (S₀.filter (fun x => CongMod m x ν)) (fun x hx => (Finset.mem_filter.mp hx).2)
    (fun x hx hc => Finset.mem_filter.mpr ⟨hx, hc⟩)
  have h2 : ‖∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ ≤ R :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR0 fun x hx => hterm x (Finset.mem_filter.mp hx).2
  calc ‖v‖ = ‖(v - ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x) + ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ := by
          rw [sub_add_cancel]
    _ ≤ ‖v - ∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ + ‖∑ x ∈ S₀.filter (fun x => CongMod m x ν), t x‖ := norm_add_le _ _
    _ ≤ R + δ := by linarith

end GlobalTheory.UPoinc
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatForcesCongMod

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UPoinc.compat_forces_congMod : ∀ (G₁ G Y : Type) [AddCommGroup G₁] [AddCommGroup G] [AddCommGroup Y] (L₁ L K : ℕ), K * L₁ = L → 0 < L → (∀ (n : ℕ) (x : Y), 0 < n → n • x = 0 → x = 0) → ∀ (lab : G₁ →+ G) (yy₁ : G₁ →+ ModN L₁ Y), Function.Surjective yy₁ → ∀ (yy yy' : G →+ ModN L Y), (∀ a μ, yy₁ a = QuotientAddGroup.mk μ → yy (lab a) = QuotientAddGroup.mk (K • μ)) → (∀ a μ, yy₁ a = QuotientAddGroup.mk μ → yy' (lab a) = QuotientAddGroup.mk (K • μ)) → ∀ g : Y →+ Y, (∀ a μ, yy a = QuotientAddGroup.mk μ → yy' a = QuotientAddGroup.mk (g μ)) → ∀ x, CongMod L₁ (g x) x := by
  intro G₁ G Y _ _ _ L₁ L K hKL hL htf lab yy₁ hsurj yy yy' h1 h2 g hg x
  obtain ⟨b, hb⟩ := hsurj (QuotientAddGroup.mk x)
  have e1 := h1 b x hb
  have e2 := h2 b x hb
  have e3 := hg (lab b) (K • x) e1
  rw [e2, map_nsmul] at e3
  rw [QuotientAddGroup.eq] at e3
  obtain ⟨w, hw⟩ := e3
  simp only [nsmulAddMonoidHom_apply] at hw
  have hK : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; omega
    · exact h
  refine ⟨w, ?_⟩
  apply sub_eq_zero.mp
  apply htf K _ hK
  rw [smul_sub, smul_add, smul_smul, hKL, hw]
  abel
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdDetSubOneOfCongModThreeLe

section

@[expose] public section

open GlobalTheory.Poinc
open GlobalTheory
open Classical

theorem GlobalTheory.UPoinc.dvd_det_sub_one_of_congMod_three_le (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (L N : ℕ) (hL : 3 ≤ L)
    (γ : X ≃ₗ[ℤ] X) (hγ : ∀ x, CongMod L (γ x) x) : (N : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
  set b := Module.Free.chooseBasis ℤ X
  have hdet : LinearMap.det (γ : X →ₗ[ℤ] X) = (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)).det :=
    (LinearMap.det_toMatrix b _).symm
  have hmap : (Int.castRingHom (ZMod L)).mapMatrix (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X)) = 1 := by
    ext i j
    obtain ⟨w, hw⟩ := hγ (b j)
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, LinearEquiv.coe_coe, hw,
      map_add, map_nsmul, Module.Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply, Matrix.one_apply]
    rw [Finsupp.single_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, add_zero]
    by_cases h : j = i
    · subst h; simp
    · simp [h, Ne.symm h]
  have hcast : ((LinearMap.det (γ : X →ₗ[ℤ] X) : ℤ) : ZMod L) = 1 := by
    rw [hdet]
    have := RingHom.map_det (Int.castRingHom (ZMod L)) (LinearMap.toMatrix b b (γ : X →ₗ[ℤ] X))
    simp only [eq_intCast] at this
    rw [this, hmap, Matrix.det_one]
  have hdvd : (L : ℤ) ∣ LinearMap.det (γ : X →ₗ[ℤ] X) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hcast, sub_self]
  rcases Int.isUnit_iff.mp (LinearEquiv.isUnit_det' γ) with h | h
  · rw [h, sub_self]; exact dvd_zero _
  · exfalso
    rw [h] at hdvd
    have h2 : (L : ℤ) ∣ 2 := by
      have : (2 : ℤ) = -(-1 - 1) := by norm_num
      rw [this]; exact (dvd_neg).2 hdvd
    have : L ∣ 2 := by exact_mod_cast h2
    have := Nat.le_of_dvd (by norm_num) this
    omega
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTie

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem UDeep.exists_tie (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (_hpq : 1 ≤ Dw.p + Dw.q) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf)
    (X₁ : USetup C) (D : UDeep X₁) (w₁ : UWit X₁) : ∃ w₂ : UWit D.X, D.Comparison₂ w₁ w₂ := by
  obtain ⟨P₀, a, a', ha, ha', hL, hL', hpt⟩ := D.same
  have e : spMap (algebraMap X₁.Ω₁ D.X.Ω₁) ≫ spMap X₁.S.R.val.toRingHom =
      spMap ((algebraMap X₁.Ω₁ D.X.Ω₁).comp X₁.S.R.val.toRingHom) := by
    rw [← Spec.map_comp]; rfl
  have w : a ≫ X₁.ρ.P.A.hom = (P₀.A.hom ≫ spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) ≫ spMap X₁.S.R.val.toRingHom := by
    rw [Category.assoc, e]; exact ha.1.w
  have e₁ := w₁.hα.1.lift_fst _ _ w
  let m : P₀.A.left ⟶ w₁.G.left := w₁.hα.1.lift _ _ w
  have hm : IsGrpPullback P₀.A w₁.G (spMap (algebraMap X₁.Ω₁ D.X.Ω₁)) m :=
    w₁.hα.cancel (ha.congr e.symm e₁.symm) (w₁.hα.1.lift_snd _ _ w)
  have hβ : IsGrpPullback P₀.A Xo.univ.t.G (D.X.uΩ ≫ pullback.fst _ _) (m ≫ w₁.β) :=
    (hm.comp w₁.hβ).congr (by rw [D.pt]; simp only [USetup.uΩ, Category.assoc]) rfl
  have hLβ : LBIso (D.X.ρ.P.L.pull a') (Xo.univ.t.PP.L.pull (m ≫ w₁.β)) :=
    LBIso.trans (pull_isLB D.X.ρ.P.isLB _) P₀.isLB (pull_isLB Xo.univ.t.PP.isLB _) hL'.symm
      (LBIso.trans P₀.isLB (pull_isLB X₁.ρ.P.isLB _) (pull_isLB Xo.univ.t.PP.isLB _) hL
        (GenSpread.lbIso_pull_comp m e₁.symm rfl w₁.hL))
  refine ⟨{ G := P₀.A, α := a', β := m ≫ w₁.β, hα := ha', hβ := hβ, hL := hLβ }, m, hm, rfl, fun x => ?_⟩
  obtain ⟨v, hv, hv'⟩ := hpt x
  refine ⟨v, ?_, hv'⟩
  show v ≫ m ≫ w₁.α = _
  rw [e₁, hv, ← Category.assoc, e]

end GlobalTheory.UPoinc
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelGeometricCore

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UCore

theorem qW_one {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X) (μ : Fin 1 → X) :
    qW !![(1 : ℤ)] β μ = β (μ 0) (μ 0) := by
  simp [qW]

theorem classSums_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ p _ z₁ Φ hΦ y₀ N₀
  choose ct hct using hΦ
  have hev : ∀ y a, Φ.ev y a = (ct y).val a := fun y => (hct y).1
  choose e he using fun y => (hct y).2
  obtain ⟨D, hD, hproj⟩ := GlobalTheory.UPoinc.UDeepP.exists_udeep_proj E H Dw hpq l Xo cf C X₁ N₀
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := fun x => ⟨D.X.normal.isDomain_stalk x, D.X.normal.isIntegrallyClosed_stalk x⟩
  obtain ⟨w₁⟩ := nonempty_uWit X₁
  obtain ⟨w₂, htie⟩ := GlobalTheory.UPoinc.UDeep.exists_tie E H Dw hpq l Xo cf C X₁ D w₁
  refine ⟨D.m, hD, D.dvd, D.X.Ω₁, inferInstance, D.alg, D.fd, D.gal, ?_⟩
  intro 𝔷 h𝔷 ev' hev' hle hlt
  obtain ⟨hB, hmax, -, hlift⟩ := GlobalTheory.Poinc.integralClosure_stalk_fibre X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q
    hN D.fin D.gen z₁
  obtain ⟨z₂, hz₂, h𝔷z⟩ := hmax 𝔷 h𝔷
  haveI := D.fd
  haveI := D.gal
  letI : Algebra (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ := ((algebraMap X₁.Ω₁ D.X.Ω₁).comp (X₁.M.stalkHom z₁)).toAlgebra
  have hl : ∀ y, ∃ y₂ : Sp (OO p) ⟶ D.X.M.Z, y₂ ≫ D.q = (ct y).y ∧
      ∀ b, ev' y b = D.X.M.val (gPt p ≫ y₂) (b : D.X.Ω₁) :=
    fun y => hlift p (ct y).y (ct y).cen (ev' y) (fun a => by rw [hev', hev]; rfl)
  choose y₂ hq hval using hl
  have hcen : ∀ y, y₂ y (cPt p) = z₂ := by
    intro y
    refine GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q hN D.fin D.gen z₁ 𝔷 h𝔷 z₂ hz₂ h𝔷z p (y₂ y) ?_ ?_
    · rw [← Scheme.Hom.comp_apply, hq]; exact (ct y).cen
    · intro b hb; rw [← hval]; exact hlt y b hb
  let ct₂ : ∀ y, UCTrait D.X p z₂ := fun y => { D.lift (ct y) (y₂ y) (hq y) with cen := hcen y }
  choose yy₁ hyy₁ using fun y => GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C X₁ w₁ p z₁ (ct y)
  choose yy hyy hcomp using fun y => GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ (ct y) (yy₁ y) (hyy₁ y) (y₂ y) (hq y)
  have hyy₂ : ∀ y, UIsLabW D.X w₂ (ct₂ y) (yy y) := fun y => hyy y
  choose d hd using fun y => GlobalTheory.T.exists_linearEquiv_labelledLattices_unitaryTraits E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ (ct₂ y₀) (ct₂ y) (yy y₀) (yy y) (hyy₂ y₀) (hyy₂ y)
  let k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y := fun y =>
    if h : y = y₀ then (by subst h; exact LinearEquiv.refl _ _) else (e y₀).trans ((d y).trans (e y).symm)
  have hk0 : k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) := by simp [k]
  have hk : ∀ y a x, yy y₀ a = QuotientAddGroup.mk (e y₀ x) → yy y a = QuotientAddGroup.mk (e y (k y x)) := by
    intro y a x hax
    by_cases h : y = y₀
    · subst h; simpa [hk0] using hax
    · simp only [k, dif_neg h, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
      exact hd y a _ hax
  have hsurj := (GlobalTheory.UPoinc.uIsLab_onto_and_ker E H Dw hpq l Xo cf C D.X p z₂ (ct₂ y₀) (yy y₀) (hyy₂ y₀).uIsLab).1
  choose A hA using fun x : (ct y₀).T.P.D.toPre.X =>
    hsurj (QuotientAddGroup.mk x : ModN (D.X.S.r * D.X.S.N) (ct y₀).T.P.D.toPre.X)
  obtain ⟨f, t, hfO, hft⟩ := GlobalTheory.T.unitary_thetaFourier_classSums_deeper_integral E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂
  have hfapp : (∀ (ct : UCTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) ct.T.P.D.toPre.X), UIsLab X₁ ct yy₁ → ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X, UIsLab D.X (D.lift ct y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset ct.T.P.D.toPre.X, ∀ S : Finset ct.T.P.D.toPre.X, (∀ μ ∈ S, CongMod D.m μ ν) → (∀ μ ∈ S₀, CongMod D.m μ ν → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (f a κ) - ∑ μ ∈ S, t ct yy₁ μ κ‖ ≤ δ) := fun ct yy₁ h1 => (hft ct yy₁ h1).2.2
  let F : (Fin 1 → Φ.X y₀) → ↥(X₁.S.HH X₁.M z₁) → integralClosure (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁ :=
    fun c κ => ⟨f (A (e y₀ (c 0))) κ, (hB _).2 fun z' hz' => hfO _ κ z' hz'⟩
  have hF : ∀ c κ, ((F c κ : integralClosure (X₁.M.Z.presheaf.stalk z₁) D.X.Ω₁) : D.X.Ω₁) = f (A (e y₀ (c 0))) κ :=
    fun _ _ => rfl
  refine ⟨k, ↥(X₁.S.HH X₁.M z₁), F, hk0, ?_, ?_, ?_, ?_⟩
  ·
    intro c c' κ hcc
    apply Subtype.ext
    rw [hF, hF]
    obtain ⟨w, hw⟩ := hcc 0
    refine GlobalTheory.UPoinc.DeepSame.deep_eq_of_congMod E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂ f t hfO hfapp w₁ w₂ htie hproj (ct₂ y₀) (yy y₀) (hyy₂ y₀) _ _ _ _
      (hA _) (hA _) ⟨e y₀ w, ?_⟩ κ
    rw [hw, map_add (f := _), map_nsmul]
  ·
    intro y c κ μ hμ hmin
    rw [hval y, qW_one]
    obtain ⟨hle_t, -, -⟩ := hft (ct y) (yy₁ y) (hyy₁ y).uIsLab
    have hyyA : yy y (A (e y₀ (c 0))) = QuotientAddGroup.mk (e y (k y (c 0))) := hk y _ _ (hA _)
    refine GlobalTheory.UPoinc.class_limit_norm_le p (Φ.X y) (ct y).T.P.D.toPre.X (e y).toAddEquiv (Φ.β y) (ct y).T.be (Φ.sc y) (ct y).sc
      (Φ.sc_pos y) (he y) D.m (fun μ' => t (ct y) (yy₁ y) μ' κ) (fun μ' => hle_t μ' κ) _ _
      (hfapp (ct y) (yy₁ y) (hyy₁ y).uIsLab (y₂ y) (hq y) (hcen y) (yy y) (hyy y).uIsLab (hcomp y) _ _ κ hyyA) (μ 0) ?_ ?_
    · obtain ⟨w, hw⟩ := hμ 0
      exact ⟨e y w, by simp [hw, map_add (f := _), map_nsmul]⟩
    · intro x' hx'
      have := hmin (fun _ => x') (fun u => by rw [Subsingleton.elim u 0]; exact hx')
      simpa [qW_one] using this
  ·
    intro y μ huniq
    obtain ⟨-, heq_t, -⟩ := hft (ct y) (yy₁ y) (hyy₁ y).uIsLab
    obtain ⟨κ, hκ⟩ := heq_t (e y (μ 0))
    refine ⟨fun u => (k y).symm (μ u), κ, fun u => ⟨0, by simp⟩, ?_⟩
    rw [hval y, qW_one]
    have hyyA : yy y (A (e y₀ ((k y).symm (μ 0)))) = QuotientAddGroup.mk (e y (μ 0)) := by
      simpa using hk y _ _ (hA (e y₀ ((k y).symm (μ 0))))
    refine GlobalTheory.UPoinc.classSum_norm_eq_of_unique_least p (Φ.X y) (ct y).T.P.D.toPre.X (e y).toAddEquiv (Φ.β y) (ct y).T.be (Φ.sc y) (ct y).sc
      (Φ.sc_pos y) (he y) D.m (fun μ' => t (ct y) (yy₁ y) μ' κ) (fun μ' => (hft (ct y) (yy₁ y) (hyy₁ y).uIsLab).1 μ' κ) _ _
      (hfapp (ct y) (yy₁ y) (hyy₁ y).uIsLab (y₂ y) (hq y) (hcen y) (yy y) (hyy y).uIsLab (hcomp y) _ _ κ hyyA) (μ 0)
      ⟨0, by simp⟩ hκ ?_
    intro x' hx' hne
    have := huniq (fun _ => x') (fun u => by rw [Subsingleton.elim u 0]; exact hx')
      (fun h => hne (congrFun h 0))
    simpa [qW_one] using this
  ·
    intro σ hσ
    obtain ⟨σ', hσ'⟩ := GlobalTheory.UPoinc.intClosure_aut_extends X₁.o₁ X₁.Ω₁ D.X.Ω₁ X₁.M z₁ σ
    obtain ⟨s, hs_pt, hs_q, hs_val⟩ := GlobalTheory.Poinc.GalAut.autAct X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q
      hN D.fin D.gen σ'
    have hcs : (y₂ y₀ ≫ s) (cPt p) = z₂ := by
      refine GlobalTheory.UPoinc.cPt_eq_of_norm_val_lt_one X₁.o₁ X₁.Ω₁ D.X.o₁ D.X.Ω₁ X₁.M D.X.M D.q hN D.fin D.gen z₁ 𝔷 h𝔷 z₂ hz₂ h𝔷z p _ ?_ ?_
      · rw [← Scheme.Hom.comp_apply, Category.assoc, hs_q, hq]; exact (ct y₀).cen
      · intro b hb
        rw [← Category.assoc, hs_val, hσ', ← hval]
        apply hlt y₀
        have h2 : b ∈ 𝔷.comap σ := by rw [hσ]; exact hb
        exact h2
    have hsz : s z₂ = z₂ := by
      have h3 := hcs
      rw [Scheme.Hom.comp_apply, hcen y₀] at h3
      exact h3
    obtain ⟨aσ, -, haσ⟩ := GlobalTheory.T.deeperUnitaryLevel_galois_acts_on_labels E H Dw hpq l Xo cf C X₁ D σ' s hs_pt
    have hqs : (y₂ y₀ ≫ s) ≫ D.q = (ct y₀).y := by rw [Category.assoc, hs_q, hq]
    obtain ⟨yy', hyy', hcomp'⟩ := GlobalTheory.T.unitary_trait_labels_extend_to_deeper_level E H Dw hpq l Xo cf C X₁ D w₁ w₂ htie p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀) (y₂ y₀ ≫ s) hqs
    let ct₂' : UCTrait D.X p z₂ := { D.lift (ct y₀) (y₂ y₀ ≫ s) hqs with cen := hcs }
    have hyy'₂ : UIsLabW D.X w₂ ct₂' yy' := hyy'
    obtain ⟨g, hg⟩ := GlobalTheory.T.exists_linearEquiv_labelledLattices_unitaryTraits E H Dw hpq l Xo cf C D.X w₂ hproj p z₂ (ct₂ y₀) ct₂' (yy y₀) yy' (hyy₂ y₀) hyy'₂
    have hrel : ∀ x, yy' x = yy y₀ (aσ x) :=
      haσ p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀).uIsLab (y₂ y₀) (hq y₀) hqs (yy y₀) yy' (hyy y₀).uIsLab (hcomp y₀) hyy'.uIsLab hcomp'
    let γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀ := (e y₀).trans (g.trans (e y₀).symm)
    have hL : 3 ≤ X₁.S.r * X₁.S.N := by
      have h6 := X₁.big.2.2
      have : 1 ≤ X₁.S.N ^ X₁.S.g * X₁.S.g.factorial :=
        Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (by have := X₁.S.N_ge; omega)) (Nat.factorial_ne_zero _))
      omega
    have hdvd : X₁.S.r * X₁.S.N ∣ D.X.S.r * D.X.S.N := by
      rw [D.sq]; exact D.dvd.trans ((dvd_pow_self _ two_ne_zero).trans (dvd_mul_left _ _))
    have hLpos : 0 < D.X.S.r * D.X.S.N :=
      Nat.mul_pos (by have := D.X.S.r_pos; omega) (by have := D.X.S.N_ge; omega)
    have htf : ∀ (n : ℕ) (x : (ct y₀).T.P.D.toPre.X), 0 < n → n • x = 0 → x = 0 := by
      intro n x hn hx
      have h1 : ((n : ℤ)) • (e y₀).symm x = 0 := by
        rw [natCast_zsmul, ← map_nsmul, hx, map_zero]
      rcases smul_eq_zero.1 h1 with h | h
      · omega
      · simpa using congrArg (e y₀) h
    have hcongY := GlobalTheory.UPoinc.compat_forces_congMod X₁.S.Gam D.X.S.Gam (ct y₀).T.P.D.toPre.X (X₁.S.r * X₁.S.N) (D.X.S.r * D.X.S.N)
      (D.X.S.r * D.X.S.N / (X₁.S.r * X₁.S.N)) (Nat.div_mul_cancel hdvd) hLpos htf D.lab (yy₁ y₀)
      (GlobalTheory.UPoinc.uIsLab_onto_and_ker E H Dw hpq l Xo cf C X₁ p z₁ (ct y₀) (yy₁ y₀) (hyy₁ y₀).uIsLab).1 (yy y₀) yy' (hcomp y₀) hcomp'
      g.toLinearMap.toAddMonoidHom (fun a μ h => hg a μ h)
    have hcong : ∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x := by
      intro x
      obtain ⟨w, hw⟩ := hcongY (e y₀ x)
      have hw' : g (e y₀ x) = e y₀ x + (X₁.S.r * X₁.S.N) • w := hw
      refine ⟨(e y₀).symm w, ?_⟩
      simp only [γ, LinearEquiv.trans_apply]
      rw [hw', map_add (f := _), map_nsmul, LinearEquiv.symm_apply_apply]
    refine ⟨γ, GlobalTheory.UPoinc.dvd_det_sub_one_of_congMod_three_le (Φ.X y₀) (X₁.S.r * X₁.S.N) D.m hL (γ.restrictScalars ℤ) hcong, hcong, ?_⟩
    · intro c κ
      apply Subtype.ext
      rw [← hσ']
      show σ' (f (A (e y₀ (c 0))) κ) = f (A (e y₀ (γ (c 0)))) κ
      refine GlobalTheory.UPoinc.GalLab.main E H Dw hpq l Xo cf C X₁ D p z₁ z₂ hz₂ f t hfO hfapp w₁ w₂ htie hproj σ' s hs_q hs_val hsz aσ
        (fun ct yy₁ h1 y h h' yy yy' h2 h3 h4 h5 => haσ p z₁ ct yy₁ h1 y h h' yy yy' h2 h3 h4 h5)
        (ct₂ y₀) (yy y₀) (hyy₂ y₀) _ _ _ _ (by rw [← hrel]; exact hg _ _ (hA _)) (hA _) ⟨0, ?_⟩ κ
      simp [γ]

end GlobalTheory.UPoinc.UCore
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassSumsDeeperLevelGeometricCoreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.unitary_classSums_deeper_level_geometric_core : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (Φ : FPre (H.bar : 𝓞 E → 𝓞 E) (min Dw.p Dw.q) p (X₁.M.Z.presheaf.stalk z₁)), (∀ y, ∃ t : UCTrait X₁ p z₁, (∀ a, Φ.ev y a = t.val a) ∧ ∃ e : Φ.X y ≃ₗ[𝓞 E] t.T.P.D.toPre.X, ∀ a b, Φ.sc y * Φ.β y a b = t.sc * t.T.be (e a) (e b)) → ∀ (y₀ : Φ.Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ (X₁.S.r * X₁.S.N) ∣ N ∧ ∃ (Ω₂ : Type) (_ : Field Ω₂) (_ : Algebra X₁.Ω₁ Ω₂) (_ : FiniteDimensional X₁.Ω₁ Ω₂) (_ : IsGalois X₁.Ω₁ Ω₂), letI : Algebra (X₁.M.Z.presheaf.stalk z₁) Ω₂ := ((algebraMap X₁.Ω₁ Ω₂).comp (X₁.M.stalkHom z₁)).toAlgebra; ∀ 𝔷 : Ideal (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.IsMaximal → ∀ ev' : Φ.Y → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) →+* PadicAlgCl p, (∀ y a, ev' y (algebraMap (X₁.M.Z.presheaf.stalk z₁) (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) a) = Φ.ev y a) → (∀ y b, ‖ev' y b‖ ≤ 1) → (∀ y, ∀ b ∈ 𝔷, ‖ev' y b‖ < 1) → ∃ (k : ∀ y, Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y) (Q : Type) (F : (Fin 1 → Φ.X y₀) → Q → (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂)), k y₀ = LinearEquiv.refl (𝓞 E) (Φ.X y₀) ∧ (∀ c c' κ, (∀ u, CongMod N (c u) (c' u)) → F c κ = F c' κ) ∧ (∀ y c κ (μ : Fin 1 → Φ.X y), (∀ u, CongMod N (μ u) (k y (c u))) → (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → qW !![(1 : ℤ)] (Φ.β y) μ ≤ qW !![(1 : ℤ)] (Φ.β y) μ') → ‖ev' y (F c κ)‖ ≤ Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ (∀ y (μ : Fin 1 → Φ.X y), (∀ μ' : Fin 1 → Φ.X y, (∀ u, CongMod N (μ' u) (μ u)) → μ' ≠ μ → qW !![(1 : ℤ)] (Φ.β y) μ < qW !![(1 : ℤ)] (Φ.β y) μ') → ∃ c κ, (∀ u, CongMod N (μ u) (k y (c u))) ∧ ‖ev' y (F c κ)‖ = Real.exp (-(Φ.sc y * qW !![(1 : ℤ)] (Φ.β y) μ) / 2)) ∧ ∀ σ : (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂) ≃ₐ[(X₁.M.Z.presheaf.stalk z₁)] (integralClosure (X₁.M.Z.presheaf.stalk z₁) Ω₂), 𝔷.comap σ = 𝔷 → ∃ γ : Φ.X y₀ ≃ₗ[𝓞 E] Φ.X y₀, (N : ℤ) ∣ LinearMap.det (γ.toLinearMap.restrictScalars ℤ) - 1 ∧ (∀ x, CongMod (X₁.S.r * X₁.S.N) (γ x) x) ∧ ∀ c κ, σ (F c κ) = F (fun u => γ (c u)) κ := by
  first | exact @GlobalTheory.UPoinc.UCore.classSums_core | exact GlobalTheory.UPoinc.UCore.classSums_core | (intros; apply GlobalTheory.UPoinc.UCore.classSums_core <;> assumption)
end
end
