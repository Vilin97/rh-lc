module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfIsDominant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaSectionsThickeningCover
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
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatioGenerationModMaxIdealOfClosedFibreStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteThetaSectionsThickeningCoverStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_finite_theta_sections_thickening_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k → ∃ (n : ℕ) (τ : Fin n → H0 U.LG.L k), ∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → U.LG.L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  first | exact @GlobalTheory.Mum.exists_ratio_gen_closed | exact GlobalTheory.Mum.exists_ratio_gen_closed | (intros; apply GlobalTheory.Mum.exists_ratio_gen_closed <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGenerationRatiosClosedFibreAnyUnitSection

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.AnySec

open MvPolynomial

theorem exists_homog {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ} (x : Fin n → S) (j : Fin n) (v : S)
    (hv : x j * v = 1) (F : MvPolynomial (Fin n) R) :
    ∃ (F' : MvPolynomial (Fin n) R) (d : ℕ), eval₂ f (fun l => x l * v) F * x j ^ d = eval₂ f x F' := by
  induction F using MvPolynomial.induction_on with
  | C a => exact ⟨C a, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨p', dp, ep⟩ := hp
    obtain ⟨q', dq, eq⟩ := hq
    refine ⟨p' * X j ^ dq + q' * X j ^ dp, dp + dq, ?_⟩
    simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X]
    rw [← ep, ← eq]; ring
  | mul_X p l hp =>
    obtain ⟨p', dp, ep⟩ := hp
    refine ⟨p' * X l, dp + 1, ?_⟩
    simp only [eval₂_mul, eval₂_X]
    linear_combination (x l * v * x j) * ep + (x l * eval₂ f x p') * hv

variable {X Y : Scheme.{0}}

theorem isUnit_of_gs {N : X.Opens} (a : Γ(X, N)) (h : ∀ y ∈ N, IsUnit (gs (𝟙 X) y N a)) : IsUnit a :=
  X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
    have := h y hy
    rw [gs_eq (𝟙 X) y N hy] at this
    exact this

theorem gs_rs_app (p : X ⟶ Y) {U : Y.Opens} {N : X.Opens} (hle : N ≤ p ⁻¹ᵁ U) {y : X} (hy : y ∈ N) (a : Γ(Y, U)) :
    gs (𝟙 X) y N (GlobalTheory.AbLaw.rs X hle ((p.app U).hom a)) = gs p y U a := by
  rw [gs_res (𝟙 X) y hle hy, gs_pull (𝟙 X) p y U (hle hy) a, Category.id_comp]

theorem rs_comp_cst {R : Type} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R)) {N N₁ : X.Opens} (hle : N ≤ N₁) :
    (GlobalTheory.AbLaw.rs X hle).comp (GlobalTheory.AbLaw.cst q N₁) = GlobalTheory.AbLaw.cst q N := by
  ext c
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.Mum.AnySec

namespace GlobalTheory.Mum.AnySec
open MvPolynomial
variable {X Y : Scheme.{0}}

theorem locGen_anySec_gen {R : Type} [CommRing R] (q : X ⟶ Spec (CommRingCat.of R)) (p : X ⟶ Y) (L : LB Y)
    (k n : ℕ) (τ : Fin n → H0 L k)
    (H : ∀ w : X, ∃ (j : Fin n) (i : Fin 1 → L.ι) (N : X.Opens) (r : Fin n → Γ(X, N)), w ∈ N ∧ IsAffineOpen N ∧
      N ≤ p ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm p y (τ j) i) ∧
        ∀ l, secGerm p y (τ l) i = gs (𝟙 _) y N (r l) * secGerm p y (τ j) i) ∧
      ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (eval₂ (GlobalTheory.AbLaw.cst q N) r Q) ∧
        g * eval₂ (GlobalTheory.AbLaw.cst q N) r Q = eval₂ (GlobalTheory.AbLaw.cst q N) r P)
    (s₀ : H0 L k) (i : Fin 1 → L.ι) (w : X) (hw : p w ∈ secChart L i) (hs : IsUnit (secGerm p w s₀ i)) :
    ∃ (N : X.Opens) (r : Fin n → Γ(X, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ p ⁻¹ᵁ secChart L i ∧
      (∀ y ∈ N, IsUnit (secGerm p y s₀ i) ∧ ∀ l, secGerm p y (τ l) i = gs (𝟙 _) y N (r l) * secGerm p y s₀ i) ∧
      ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (eval₂ (GlobalTheory.AbLaw.cst q N) r Q) ∧
        g * eval₂ (GlobalTheory.AbLaw.cst q N) r Q = eval₂ (GlobalTheory.AbLaw.cst q N) r P := by
  obtain ⟨j, i', N₁, ρ, hwN, hN₁, hN₁le, hgerm, hgen⟩ := H w
  let V : X.Opens := p ⁻¹ᵁ secChart L i ⊓ X.basicOpen ((p.app (secChart L i)).hom (s₀.f i))
  have hwV : w ∈ V := by
    refine ⟨hw, (Scheme.mem_basicOpen X _ w hw).2 ?_⟩
    have e : secGerm p w s₀ i = _ := gs_eq p w (secChart L i) hw (s₀.f i)
    rw [e] at hs
    exact hs
  obtain ⟨h, hhV, hwh⟩ := hN₁.exists_basicOpen_le ⟨w, hwV⟩ hwN
  have hNN₁ : X.basicOpen h ≤ N₁ := X.basicOpen_le h
  have hNi : X.basicOpen h ≤ p ⁻¹ᵁ secChart L i := hhV.trans inf_le_left
  have hNs : X.basicOpen h ≤ X.basicOpen ((p.app (secChart L i)).hom (s₀.f i)) := hhV.trans inf_le_right
  have hsN : ∀ y ∈ X.basicOpen h, IsUnit (secGerm p y s₀ i) := fun y hy => by
    have := (Scheme.mem_basicOpen _ _ _ (hNi hy)).1 (hNs hy)
    have e : secGerm p y s₀ i = _ := gs_eq p y (secChart L i) (hNi hy) (s₀.f i)
    rw [e]
    exact this
  have hu₀ : IsUnit (GlobalTheory.AbLaw.rs X hNi ((p.app (secChart L i)).hom (s₀.f i))) :=
    isUnit_of_gs _ fun y hy => by rw [gs_rs_app p hNi hy (s₀.f i)]; exact hsN y hy
  obtain ⟨r, hr_def⟩ : ∃ r : Fin n → Γ(X, X.basicOpen h), r = fun l =>
      GlobalTheory.AbLaw.rs X hNi ((p.app (secChart L i)).hom ((τ l).f i)) * (hu₀.unit⁻¹ : (Γ(X, X.basicOpen h))ˣ).val :=
    ⟨_, rfl⟩
  have hr : ∀ y ∈ X.basicOpen h, ∀ l, secGerm p y (τ l) i = gs (𝟙 X) y _ (r l) * secGerm p y s₀ i := by
    intro y hy l
    rw [secGerm, secGerm, ← gs_rs_app p hNi hy ((τ l).f i), ← gs_rs_app p hNi hy (s₀.f i), ← gs_mul _ _ _ hy]
    congr 1
    simp only [hr_def, _root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
  refine ⟨X.basicOpen h, r, hwh, hN₁.basicOpen h, hNi, fun y hy => ⟨hsN y hy, hr y hy⟩, fun g => ?_⟩

  have key : ∀ y ∈ X.basicOpen h, ∀ l, gs (𝟙 X) y _ (r l) = gs (𝟙 X) y _ (GlobalTheory.AbLaw.rs X hNN₁ (ρ l) * r j) ∧
      IsUnit (gs (𝟙 X) y _ (r j)) := by
    intro y hy l
    have hy₁ := hNN₁ hy
    obtain ⟨c, hc⟩ := exists_unit_secGerm k p y (hNi hy) (hN₁le hy₁)
    have gρ : gs (𝟙 X) y _ (GlobalTheory.AbLaw.rs X hNN₁ (ρ l)) = gs (𝟙 X) y N₁ (ρ l) := gs_res _ _ hNN₁ hy _
    have e1 := hr y hy l
    have e2 := hr y hy j
    have e3 := (hgerm y hy₁).2 l
    have hcl := hc (τ l)
    have hcj := hc (τ j)
    refine ⟨?_, ?_⟩
    · rw [gs_mul _ _ _ hy, gρ]
      apply (hsN y hy).mul_right_cancel
      linear_combination (-1 : _) * e1 + gs (𝟙 X) y N₁ (ρ l) * e2 + hcl - gs (𝟙 X) y N₁ (ρ l) * hcj + c.val * e3
    · have : IsUnit (gs (𝟙 X) y _ (r j) * secGerm p y s₀ i) := by
        rw [← e2, hcj]; exact c.isUnit.mul (hgerm y hy₁).1
      exact isUnit_of_mul_isUnit_left this
  have hrel : ∀ l, r l = GlobalTheory.AbLaw.rs X hNN₁ (ρ l) * r j := fun l => fn_ext fun y hy => (key y hy l).1
  have huj : IsUnit (r j) := isUnit_of_gs _ fun y hy => (key y hy j).2
  let v : Γ(X, X.basicOpen h) := (huj.unit⁻¹ : (Γ(X, X.basicOpen h))ˣ).val
  have hv : r j * v = 1 := IsUnit.mul_val_inv huj
  have hρ : (fun l => GlobalTheory.AbLaw.rs X hNN₁ (ρ l)) = fun l => r l * v := by
    funext l; rw [hrel l, _root_.mul_assoc, hv, _root_.mul_one]

  have hev : ∀ F : MvPolynomial (Fin n) R, GlobalTheory.AbLaw.rs X hNN₁ (eval₂ (GlobalTheory.AbLaw.cst q N₁) ρ F) =
      eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) F := fun F => by
    rw [eval₂_comp_left, rs_comp_cst, ← hρ]; rfl
  haveI := hN₁.isLocalization_basicOpen h
  obtain ⟨⟨a, ⟨_, t, rfl⟩⟩, hga⟩ := IsLocalization.surj (Submonoid.powers h) g
  have hhu : IsUnit (GlobalTheory.AbLaw.rs X hNN₁ h) := IsLocalization.Away.algebraMap_isUnit h
  obtain ⟨Pa, Qa, hQa, ea⟩ := hgen a
  obtain ⟨Ph, Qh, hQh, eh⟩ := hgen h
  have ea' := congrArg (GlobalTheory.AbLaw.rs X hNN₁) ea
  have eh' := congrArg (GlobalTheory.AbLaw.rs X hNN₁) eh
  rw [map_mul, hev, hev] at ea' eh'
  have hQh' := hQh.map (GlobalTheory.AbLaw.rs X hNN₁)
  rw [hev] at hQh'
  have hga' : g * GlobalTheory.AbLaw.rs X hNN₁ h ^ t = GlobalTheory.AbLaw.rs X hNN₁ a := by
    rw [← map_pow]; exact hga
  obtain ⟨A', d3, eA⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Pa
  obtain ⟨B', d2, eB⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Qa
  obtain ⟨C', d1, eC⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Ph
  obtain ⟨D', d4, eD⟩ := exists_homog (GlobalTheory.AbLaw.cst q (X.basicOpen h)) r j v hv Qh
  refine ⟨A' * D' ^ t * MvPolynomial.X j ^ (d1 * t + d2), C' ^ t * B' * MvPolynomial.X j ^ (d3 + d4 * t), ?_, ?_⟩
  · simp only [eval₂_mul, eval₂_pow, eval₂_X]
    rw [← eB, ← eC, ← eh']
    have hQa' := hQa.map (GlobalTheory.AbLaw.rs X hNN₁)
    rw [hev] at hQa'
    exact ((((hhu.mul hQh').mul (huj.pow _)).pow _).mul (hQa'.mul (huj.pow _))).mul (huj.pow _)
  · simp only [eval₂_mul, eval₂_pow, eval₂_X]
    rw [← eA, ← eB, ← eC, ← eD, ← eh', ← ea']
    linear_combination (eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) Qa *
      eval₂ (GlobalTheory.AbLaw.cst q (X.basicOpen h)) (fun l => r l * v) Qh ^ t * r j ^ (d1 * t + d2 + d3 + d4 * t)) * hga'

end GlobalTheory.Mum.AnySec

theorem GlobalTheory.Mum.locGen_ratio_anySec : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k n : ℕ) (τ : Fin n → H0 L k), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (s₀ : H0 L k) (i : Fin 1 → L.ι) (w : (thickObj R (maximalIdeal R) 0 G).left), (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  intro R _ _ _ G L k n τ H s₀ i w hw hs
  obtain ⟨N, r, h1, h2, h3, h4, h5⟩ :=
    GlobalTheory.Mum.AnySec.locGen_anySec_gen ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) _ L k n τ H s₀ i w hw hs
  exact ⟨N, n, τ, r, h1, h2, h3, h4, h5⟩
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalGenerationRatiosClosedFibreAnyUnitSectionStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.localGeneration_ratios_closedFibre_any_unit_section : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (L : LB G.left) (k n : ℕ) (τ : Fin n → H0 L k), (∀ w : (thickObj R (maximalIdeal R) 0 G).left, ∃ (j : Fin n) (i : Fin 1 → L.ι) (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (r : Fin n → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (τ j) i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin n) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P) → ∀ (s₀ : H0 L k) (i : Fin 1 → L.ι) (w : (thickObj R (maximalIdeal R) 0 G).left), (fstG (maximalIdeal R) 0 G).left w ∈ secChart L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) 0 G).left.Opens) (m : ℕ) (σ : Fin m → H0 L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) 0 G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) 0 G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) 0 G).left) ((fstG (maximalIdeal R) 0 G).left ≫ G.hom) N) r P := by
  first | exact @GlobalTheory.Mum.locGen_ratio_anySec | exact GlobalTheory.Mum.locGen_ratio_anySec | (intros; apply GlobalTheory.Mum.locGen_ratio_anySec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionRatiosGenerateModMaximal

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.exists_ratio_gen_mod : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  intro R _ _ _ hBase D A G _ _ hG U
  obtain ⟨k₀, hk₀, hA⟩ := GlobalTheory.T.exists_finite_theta_sections_thickening_cover R hBase D A G hG U
  refine ⟨k₀, hk₀, fun e k hk s₀ i w hw hu => ?_⟩
  obtain ⟨n, τ, hτ⟩ := hA k hk
  exact GlobalTheory.T.ratioGeneration_mod_maxIdeal_of_closedFibre R G U.LG.L k s₀ i (GlobalTheory.T.localGeneration_ratios_closedFibre_any_unit_section R G U.LG.L k n τ hτ s₀ i) e w hw hu
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionRatiosGenerateModMaximalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_section_ratios_generate_mod_maximal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k) (r : Fin m → Γ((thickObj R (maximalIdeal R) e G).left, N)), w ∈ N ∧ IsAffineOpen N ∧ N ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i ∧ (∀ y ∈ N, IsUnit (secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ l, secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y (σ l) i = gs (𝟙 _) y N (r l) * secGerm (Y := (thickObj R (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left y s₀ i) ∧ ∀ g : Γ((thickObj R (maximalIdeal R) e G).left, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r Q - MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) r P ∈ Ideal.map (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) := by
  first | exact @GlobalTheory.Mum.exists_ratio_gen_mod | exact GlobalTheory.Mum.exists_ratio_gen_mod | (intros; apply GlobalTheory.Mum.exists_ratio_gen_mod <;> assumption)
end
end
