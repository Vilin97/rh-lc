module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverTraitExpansionScaleBothScalars
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecKRatioTraitDescendsToFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombEqZeroIffExpansionCombEqZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransferOfRelationGenericFibre

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Trait.gs_scal_base {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {C : LabCover D} {W : Type} [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) {Z : Scheme.{0}}
    (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left) (h : p ≫ T.β = p' ≫ C.α) (z : Z) (c : R) :
    gs p z ⊤ (scal T.G.hom (T.φ c)) = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) c)) := by
  have hc : ∀ {A B : Type} [CommRing A] [CommRing B] {Y : Scheme.{0}} (q : Y ⟶ Sp B) (φ : A →+* B) (x : A),
      scal q (φ x) = scal (q ≫ spMap φ) x := by
    intro A B _ _ Y q φ x
    have e := congrArg (fun g => g.hom x) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    simp only [scal, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
    rw [e]
  rw [hc, hc]
  have hg : ∀ {A : Type} [CommRing A] {Y : Scheme.{0}} (f : Z ⟶ Y) (q : Y ⟶ Sp A) (x : A),
      gs f z ⊤ (scal q x) = gs (f ≫ q) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom x) :=
    fun f q x => gs_pull f q z ⊤ trivial _
  rw [hg, hg]
  have e : p ≫ T.G.hom ≫ spMap T.φ = p' ≫ C.A.A.hom ≫ spMap (algebraMap R (FractionRing R)) := by
    have h1 : T.β ≫ C.G.hom = T.G.hom ≫ T.ξ := T.cart.1.w
    have h2 : C.α ≫ C.G.hom = C.A.A.hom ≫ C.gp := C.α_cart.1.w
    have h3 : C.gp ≫ C.π = spMap (algebraMap R (FractionRing R)) := C.gp_π
    rw [← T.ξ_π, ← h3, ← Category.assoc T.G.hom, ← h1, ← Category.assoc C.A.A.hom, ← h2]
    simp only [← Category.assoc, h]
  rw [e]

theorem Trait.exp_transfer : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (r t : R) (u : W), (∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J) → T.Exp 1 u s₂ F → T.Exp (T.φ t) (T.φ r * u) s₁ F := by
  intro R _ _ _ D C W _ _ _ T k F s₁ s₂ r t u hrel hExp
  have h1 := GlobalTheory.Mum.Trait.exp_mul_left R D C W T k s₂ F 1 u (T.φ r) hExp
  rw [_root_.mul_one] at h1
  obtain ⟨σ, hσ, hs⟩ := h1
  refine ⟨σ, hσ, ?_⟩
  intro Z p p' hp z J hJ
  rw [hs Z p p' hp z J hJ, T.gs_scal_base p p' hp z r, T.gs_scal_base p p' hp z t]
  exact (hrel Z p' z J hJ).symm

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionTransferOfRelationGenericFibreStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.expansion_transfer_of_relation_genericFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ) (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (r t : R) (u : W), (∀ (Z : Scheme.{0}) (p' : Z ⟶ C.A.A.left) (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) t)) * sval s₁ p' z J = gs p' z ⊤ (scal C.A.A.hom (algebraMap R (FractionRing R) r)) * sval s₂ p' z J) → T.Exp 1 u s₂ F → T.Exp (T.φ t) (T.φ r * u) s₁ F := by
  first | exact @GlobalTheory.Mum.Trait.exp_transfer | exact GlobalTheory.Mum.Trait.exp_transfer | (intros; apply GlobalTheory.Mum.Trait.exp_transfer <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionsSameFamilyProportional

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

theorem Trait.exp_pair : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (a₁ b₁ a₂ b₂ : W), T.Exp a₁ b₁ s₁ F → T.Exp a₂ b₂ s₂ F → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom (b₂ * a₁)) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom (b₁ * a₂)) * sval s₂ p' z J := by
  intro R _ _ _ hB D C W _ _ _ T k hk F s₁ s₂ a₁ b₁ a₂ b₂ h₁ h₂ Z p p' hpp' z J hJ
  obtain ⟨σ₁, ⟨τ₁, f₁, hc₁, hp₁, he₁⟩, hg₁⟩ := h₁
  obtain ⟨σ₂, ⟨τ₂, f₂, hc₂, hp₂, he₂⟩, hg₂⟩ := h₂
  have hf : f₁ = f₂ := funext fun x =>
    (SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB T.D'.toPre.P.isLB T.hD.w T.hD.w_gen (Fin 4)
      (T.D'.toPre.famφB x) (D.toPre.famφB (T.hD.xe x)) (DegPre.famε k) _ (ExpGTrans.famφB_pull T.hD x)
      (F.f (T.hD.xe x))).unique (hp₁ x) (hp₂ x)
  subst hf
  have hW := T.cdvr
  have := hW.1
  have := hW.2.2
  have bW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hGs : IsSemiAbelian T.G := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso T.cart (isGrpPullback_pullback C.G T.ξ)
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback T.ξ C.G C.semi)
  have hGc := hGs.geomConnected
  have H := (comb_eq_zero_iff_expansion_comb_eq_zero W _ bW T.D' T.A T.G T.U.toUnifPre k 2 ![1, -1] ![τ₁, τ₂]
    ![f₁, f₁] (fun i => by fin_cases i; exacts [he₁, he₂])).2 hGc (fun α j => by simp [Fin.sum_univ_two, Out.scal])
  have hτ : τ₁ = τ₂ := SecOps.sec_ext fun j => by
    have := H j
    simpa [Fin.sum_univ_two, Out.scal, add_neg_eq_zero] using this
  subst hτ
  choose J' hJ' using fun ψ : Z ⟶ T.G.left => exists_chart T.U.LG.isLB (ψ z)
  have c₁ := hc₁ Z p z J J' hJ hJ'
  have c₂ := hc₂ Z p z J J' hJ hJ'
  have g₁ := hg₁ Z p p' hpp' z J hJ
  have g₂ := hg₂ Z p p' hpp' z J hJ
  have m : ∀ a b : W, gs p z ⊤ (scal T.G.hom (a * b)) = gs p z ⊤ (scal T.G.hom a) * gs p z ⊤ (scal T.G.hom b) :=
    fun a b => by
      rw [show scal T.G.hom (a * b) = scal T.G.hom a * scal T.G.hom b by simp only [scal, map_mul]]
      exact gs_mul p z ⊤ (show p z ∈ (⊤ : T.G.left.Opens) from trivial) _ _
  have key : gs p z ⊤ (scal T.G.hom b₂) * sval σ₁ p z J = gs p z ⊤ (scal T.G.hom b₁) * sval σ₂ p z J := by
    rw [c₁, c₂]; ring
  rw [g₁, g₂] at key
  rw [m, m]
  linear_combination key

end GlobalTheory.Mum
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitExpansionsSameFamilyProportionalStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.traitExpansions_same_family_proportional : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (k : ℕ), 1 ≤ k → ∀ (F : IntFam (maximalIdeal R) D.toPre k) (s₁ s₂ : SecK C.P.L.L C.α k) (a₁ b₁ a₂ b₂ : W), T.Exp a₁ b₁ s₁ F → T.Exp a₂ b₂ s₂ F → ∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ C.A.A.left), p ≫ T.β = p' ≫ C.α → ∀ (z : Z) (J : (Z ⟶ C.G.left) → C.P.L.L.ι), Good C.P.L.L z J → gs p z ⊤ (scal T.G.hom (b₂ * a₁)) * sval s₁ p' z J = gs p z ⊤ (scal T.G.hom (b₁ * a₂)) * sval s₂ p' z J := by
  first | exact @GlobalTheory.Mum.Trait.exp_pair | exact GlobalTheory.Mum.Trait.exp_pair | (intros; apply GlobalTheory.Mum.Trait.exp_pair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioOfExpansionsProportionalAtTrait

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_ratio_of_exp_one_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (G : IntFam (maximalIdeal R) D.toPre k) (S Ψ : SecK C.P.L.L C.α k), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u Ψ G) → ∀ (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsLocalRing W₀] (T₀ : Trait C W₀) (a₀ b₀ : W₀), a₀ ≠ 0 → b₀ ≠ 0 → T₀.Exp a₀ b₀ S G → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp (T.φ t) (T.φ r * u) S G := by
  intro R _ _ _ hB D C k hk G S Ψ hΨ W₀ _ _ _ T₀ a₀ b₀ ha hb hS
  obtain ⟨u₀, hu₀⟩ := hΨ W₀ T₀
  have hp := GlobalTheory.T.traitExpansions_same_family_proportional R hB D C W₀ T₀ k hk G S Ψ a₀ b₀ 1 (u₀ : W₀) hS hu₀
  obtain ⟨r, t, hr, ht, hrt⟩ := GlobalTheory.T.secK_ratio_trait_descends_to_fractionField R hB D C W₀ T₀ k S Ψ ((u₀ : W₀) * a₀) (b₀ * 1)
    (mul_ne_zero u₀.ne_zero ha) (by rw [_root_.mul_one]; exact hb) hp
  refine ⟨r, t, hr, ht, fun W _ _ _ T => ?_⟩
  obtain ⟨u, hu⟩ := hΨ W T
  exact ⟨u, GlobalTheory.T.expansion_transfer_of_relation_genericFibre R D C W T k G S Ψ r t (u : W) hrt hu⟩

end GlobalTheory.Mum
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioOfExpansionsProportionalAtTraitStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_ratio_of_expansions_proportional_at_trait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (k : ℕ), 1 ≤ k → ∀ (G : IntFam (maximalIdeal R) D.toPre k) (S Ψ : SecK C.P.L.L C.α k), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u Ψ G) → ∀ (W₀ : Type) [CommRing W₀] [IsDomain W₀] [IsLocalRing W₀] (T₀ : Trait C W₀) (a₀ b₀ : W₀), a₀ ≠ 0 → b₀ ≠ 0 → T₀.Exp a₀ b₀ S G → ∃ r t : R, r ≠ 0 ∧ t ≠ 0 ∧ ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp (T.φ t) (T.φ r * u) S G := by
  first | exact @GlobalTheory.Mum.exists_ratio_of_exp_one_trait | exact GlobalTheory.Mum.exists_ratio_of_exp_one_trait | (intros; apply GlobalTheory.Mum.exists_ratio_of_exp_one_trait <;> assumption)
end
end
