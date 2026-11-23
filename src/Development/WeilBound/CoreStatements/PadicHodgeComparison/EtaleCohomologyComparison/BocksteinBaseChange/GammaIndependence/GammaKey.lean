module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ThetaSetupAlgebraMaps
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.RegularLocalRing.Defs

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.HomApply

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CrystallineSemistableComparison.Gam

variable {A B : Type*} [CommRing A] [Field B] (i : A →+* B) (t : A)
  {H N Q : Type*} [AddCommGroup H] [Module A H] [AddCommGroup N] [Module A N] [AddCommGroup Q]
  (β : H →ₗ[A] N) (κ : H →+ (Q →+ B))

def F (n : ℕ) (x : N → H) (y : N) (φ : Q) : B := (i t ^ n)⁻¹ * κ (x y) φ

variable {i t β κ}

theorem key (hlin : ∀ (c : A) (x : H) (φ : Q), κ (c • x) φ = i c * κ x φ) (ht : i t ≠ 0)
    (hinj : ∃ n₀ : ℕ, ∀ x, β x = 0 → t ^ n₀ • x = 0) {n : ℕ} {x : N → H} (hx : ∀ y, β (x y) = t ^ n • y)
    {c : A} {x' : H} {y : N} (h : β x' = c • y) (φ : Q) : κ x' φ = i c * F i t κ n x y φ := by
  obtain ⟨n₀, h₀⟩ := hinj
  have h1 : β (t ^ n • x' - c • x y) = 0 := by
    rw [map_sub, map_smul, map_smul, h, hx, smul_smul, smul_smul, mul_comm, sub_self]
  have h2 : κ (t ^ n₀ • (t ^ n • x' - c • x y)) φ = 0 := by rw [h₀ _ h1]; simp
  simp only [smul_sub, map_sub, AddMonoidHom.sub_apply, hlin, map_pow] at h2
  have hn0 : i t ^ n₀ ≠ 0 := pow_ne_zero _ ht
  have hn : i t ^ n ≠ 0 := pow_ne_zero _ ht
  have h3 : i t ^ n * κ x' φ = i c * κ (x y) φ := by
    apply mul_left_cancel₀ hn0; linear_combination h2
  unfold F
  field_simp
  linear_combination h3

def hom (hlin : ∀ (c : A) (x : H) (φ : Q), κ (c • x) φ = i c * κ x φ) (ht : i t ≠ 0)
    (hinj : ∃ n₀ : ℕ, ∀ x, β x = 0 → t ^ n₀ • x = 0) (n : ℕ) (x : N → H) (hx : ∀ y, β (x y) = t ^ n • y) :
    N →+ (Q →+ B) :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun φ => F i t κ n x y φ) (by intro a b; simp [F, mul_add]))
    (by
      intro y y'
      ext φ
      have e := key hlin ht hinj hx (x' := x y + x y') (c := t ^ n) (y := y + y') (by simp [hx, smul_add]) φ
      have hn : i t ^ n ≠ 0 := pow_ne_zero _ ht
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [map_add (f := _), AddMonoidHom.add_apply, map_pow] at e
      unfold F at e ⊢
      field_simp
      field_simp at e
      linear_combination -e)

theorem hom_key (hlin : ∀ (c : A) (x : H) (φ : Q), κ (c • x) φ = i c * κ x φ) (ht : i t ≠ 0)
    (hinj : ∃ n₀ : ℕ, ∀ x, β x = 0 → t ^ n₀ • x = 0) (n : ℕ) (x : N → H) (hx : ∀ y, β (x y) = t ^ n • y)
    {c : A} {x' : H} {y : N} (h : β x' = c • y) (φ : Q) : κ x' φ = i c * hom hlin ht hinj n x hx y φ :=
  key hlin ht hinj hx h φ

end CrystallineSemistableComparison.Gam
end
end
end

-- Source module: Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.GammaKey

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false


noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {R : Per l K} {G : Model l K → Prop}
  {D : Dat R}

def gN (β : BMap G D) {M : Model l K} (a : D.Ch M) (hM : G M) (j : ℕ) : ℕ := (β.surj a hM j).choose

def gX (β : BMap G D) {M : Model l K} (a : D.Ch M) (hM : G M) (j : ℕ) (y : (D.A a).N j) : (D.H a).N j :=
  ((β.surj a hM j).choose_spec y).choose

theorem gX_fil (β : BMap G D) {M : Model l K} (a : D.Ch M) (hM : G M) (j : ℕ) (y : (D.A a).N j) :
    D.fil a j (gN β a hM j) (gX β a hM j y) := ((β.surj a hM j).choose_spec y).choose_spec.1

theorem gX_spec (β : BMap G D) {M : Model l K} (a : D.Ch M) (hM : G M) (j : ℕ) (y : (D.A a).N j) :
    β.β a j (gX β a hM j y) = R.t ^ gN β a hM j • y := ((β.surj a hM j).choose_spec y).choose_spec.2


open Classical in
def gamma (hF : R.Facts) (β : BMap G D) (κ : PMap G D) {M : Model l K} (a : D.Ch M) (j : ℕ) :
    (D.A a).N j →+ (Module.Dual K (HdR M.q j) →+ R.B) :=
  if hM : G M then Gam.hom (κ.lin a hM j) hF.t_ne (β.inj a hM j) (gN β a hM j) (gX β a hM j) (gX_spec β a hM j) else 0

theorem t_pow_ne (hF : R.Facts) (n : ℕ) : R.i (R.t ^ n) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hF.t_ne

variable (hF : R.Facts) (β : BMap G D) (κ : PMap G D)

theorem gamma_key {M : Model l K} {a : D.Ch M} (hM : G M) {j : ℕ} {c : R.A} {x : (D.H a).N j} {y : (D.A a).N j}
    (h : β.β a j x = c • y) (φ : Module.Dual K (HdR M.q j)) : κ.κ a j x φ = R.i c * gamma hF β κ a j y φ := by
  rw [gamma, dite_eq_left hM]
  exact Gam.hom_key _ _ _ _ _ _ h φ

theorem gamma_key' {M : Model l K} {a : D.Ch M} (hM : G M) {j : ℕ} (y : (D.A a).N j) (φ : Module.Dual K (HdR M.q j)) :
    κ.κ a j (gX β a hM j y) φ = R.i (R.t ^ gN β a hM j) * gamma hF β κ a j y φ :=
  gamma_key hF β κ hM (gX_spec β a hM j y) φ

theorem gamma_smul {M : Model l K} {a : D.Ch M} (hM : G M) {j : ℕ} (c : R.A) (y : (D.A a).N j)
    (φ : Module.Dual K (HdR M.q j)) : gamma hF β κ a j (c • y) φ = R.i c * gamma hF β κ a j y φ := by
  have h1 := gamma_key hF β κ hM (x := c • gX β a hM j y) (c := R.t ^ gN β a hM j) (y := c • y)
    (by rw [map_smul, gX_spec, smul_comm]) φ
  rw [κ.lin a hM, gamma_key' hF β κ hM] at h1
  apply mul_left_cancel₀ (t_pow_ne hF (gN β a hM j))
  linear_combination -h1

theorem gamma_lin' {M : Model l K} {a : D.Ch M} (hM : G M) {j : ℕ} (y : (D.A a).N j) (k : K)
    (φ : Module.Dual K (HdR M.q j)) : gamma hF β κ a j y (k • φ) = R.o k * gamma hF β κ a j y φ := by
  have h1 := gamma_key' hF β κ hM y (k • φ)
  rw [κ.lin' a hM, gamma_key' hF β κ hM] at h1
  apply mul_left_cancel₀ (t_pow_ne hF (gN β a hM j))
  linear_combination -h1

theorem gamma_act (hL : D.Laws G) {M : Model l K} {a : D.Ch M} (hM : G M) {j : ℕ} (σ : K.fixingSubgroup)
    (y : (D.A a).N j) (φ : Module.Dual K (HdR M.q j)) :
    gamma hF β κ a j ((D.A a).act j σ y) φ = R.σ σ (gamma hF β κ a j y φ) := by
  have h1 := gamma_key hF β κ hM (x := (D.H a).act j σ (gX β a hM j y)) (c := R.σA σ (R.t ^ gN β a hM j))
    (y := (D.A a).act j σ y) (by rw [β.act a hM, gX_spec, hL.act_smul]) φ
  rw [κ.act a hM, gamma_key' hF β κ hM, map_mul, hF.i_σ] at h1
  have ht : R.σ σ (R.i (R.t ^ gN β a hM j)) ≠ 0 := (map_ne_zero _).2 (t_pow_ne hF _)
  exact (mul_left_cancel₀ ht h1).symm

theorem gamma_nat {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : D.Ch M} {b : D.Ch N}
    (m : D.Mo u hu a b) (hM : G M) (hN : G N) (j : ℕ) (y : (D.A b).N j) (φ : Module.Dual K (HdR M.q j)) :
    gamma hF β κ a j (D.pullA m j y) φ =
      gamma hF β κ b j y (φ ∘ₗ pullR j (Model.genMap u hu) (Model.genMap_q u hu)) := by
  have h1 := gamma_key hF β κ hM (x := D.pullH m j (gX β b hN j y)) (c := R.t ^ gN β b hN j) (y := D.pullA m j y)
    (by rw [β.nat m hM hN, gX_spec, map_smul]) φ
  rw [κ.nat m hM hN, gamma_key' hF β κ hN] at h1
  exact (mul_left_cancel₀ (t_pow_ne hF _) h1).symm

theorem gamma_fil {M : Model l K} {a : D.Ch M} (hM : G M) (j r : ℕ) (y : (D.A a).N j) (φ : Module.Dual K (HdR M.q j))
    (hφ : ∀ h ∈ FilR M.q j (r + 1), φ h = 0) : R.tB ^ r * gamma hF β κ a j y φ ∈ R.P := by
  obtain ⟨z, hz, e⟩ := κ.fil a hM j (gN β a hM j) r (gX β a hM j y) φ (gX_fil β a hM j y) hφ
  rw [gamma_key' hF β κ hM, map_pow] at e
  have ht : R.tB ^ gN β a hM j ≠ 0 := pow_ne_zero _ hF.t_ne
  have : R.tB ^ r * gamma hF β κ a j y φ = z := by
    apply mul_left_cancel₀ ht
    have e' : R.tB ^ r * (R.tB ^ gN β a hM j * gamma hF β κ a j y φ) = R.tB ^ gN β a hM j * z := e
    linear_combination e'
  rw [this]; exact hz

theorem gamma_cup (hL : D.Laws G) {M : Model l K} {a : D.Ch M} (hM : G M) {i j : ℕ} (y₁ : (D.A a).N i)
    (y₂ : (D.A a).N j) (y₃ : (D.A a).N (i + j)) (hc : (D.A a).cup y₁ y₂ y₃) {m m' : ℕ}
    (b : Module.Basis (Fin m) K (HdR M.q i)) (b' : Module.Basis (Fin m') K (HdR M.q j))
    (φ : Module.Dual K (HdR M.q (i + j))) :
    gamma hF β κ a (i + j) y₃ φ = ∑ s, ∑ s', gamma hF β κ a i y₁ (b.coord s) * gamma hF β κ a j y₂ (b'.coord s') *
      R.o (φ (κ.cupR M i j (b s) (b' s'))) := by
  obtain ⟨z, hz⟩ := hL.cup_ex a (gX β a hM i y₁) (gX β a hM j y₂)
  have hc' := β.cup a hM _ _ z hz
  rw [gX_spec, gX_spec] at hc'
  have e := hL.cup_uniq a _ _ _ _ hc' (hL.cup_smul a _ _ y₁ y₂ y₃ hc)
  have h1 := gamma_key hF β κ hM e φ
  rw [κ.cup a hM _ _ z hz b b' φ] at h1
  simp only [gamma_key' hF β κ hM] at h1
  have ht := mul_ne_zero (t_pow_ne hF (gN β a hM i)) (t_pow_ne hF (gN β a hM j))
  apply mul_left_cancel₀ ht
  rw [← map_mul, ← h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [map_mul]
  ring

end CrystallineSemistableComparison
end
end
end
