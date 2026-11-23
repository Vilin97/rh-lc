module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfThickeningsOfSection
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.StalkMapInjectiveOfFlat
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
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
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RepSymInv
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordinateSumDifferenceAdditionFactor
import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAdditionFactorGeneratorTransported
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePower
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralAdditionFormulaGroupStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniquePullB
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PullBValues

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecFinsum

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.WeightTwo

theorem exists_sec_finsum {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {I : Type} (s : Finset I) (d : I → LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval t r z J = ∑ i ∈ s, sval (d i) r z J := by
  refine ⟨⟨fun j => ∑ i ∈ s, (d i).f j, fun j j' => ?_⟩, fun Z r z J hJ => ?_⟩

  · rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (d i).compat j j'
  · exact DVR.gs_fsum r z _ (hJ.mem φ r) _ _

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem formEq_cancel (k l : ℕ) (α β : D.X) :
    FormEq (Sum.elim (fun a => (D.P.A ◁ g.pG).left ≫ Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
        (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i) a)
        (fun a => (snd D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.Oφ g.pG β a))
      (Sum.elim (Sum.elim (DegPre.famε k) (DegPre.famε l)) Oinvε)
      (Sum.elim (fun i => (fst D.P.A ((Over.map (thick R I e)).obj (thickObj R I e G))).left ≫ D.famφB α i)
        (fun _ : Unit => (snd D.P.A _ ≫ g.pG).left))
      (Sum.elim (DegPre.famε k) (fun _ => (l : ℤ))) := by
  intro U _ h
  have e₁ : (D.P.A ◁ g.pG).left ≫ (fst D.P.A D.P.A).left = (fst D.P.A _).left := by
    rw [← Over.comp_left, whiskerLeft_fst]
  have e₂ : (D.P.A ◁ g.pG).left ≫ (snd D.P.A D.P.A).left = (snd D.P.A _).left ≫ g.pG.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]
  have f₀ : g.pG.left ≫ D.famφB β 0 = g.pG.left := Category.comp_id _
  have f₁ : g.pG.left ≫ D.famφB β 1 = D.Oφ g.pG β 0 := by
    change (g.pG ≫ padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c β)).left = (padd D.P.A g.pG (toUnit _ ≫ D.c β)).left
    congr 1
    simp only [padd, comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
  have f₂ : g.pG.left ≫ D.famφB β 2 = D.Oφ g.pG β 1 := by
    change (g.pG ≫ toUnit _ ≫ D.c β).left = (toUnit _ ≫ D.c β).left
    rw [comp_toUnit_assoc]
  have f₃ : g.pG.left ≫ D.famφB β 3 = D.Oφ g.pG β 3 := by
    change (g.pG ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit _ ≫ η[D.P.A]).left
    rw [comp_toUnit_assoc]
  have f₄ : D.Oφ g.pG β 2 = g.pG.left := rfl
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, reassoc_of% e₁, reassoc_of% e₂,
    Finset.univ_unique, Finset.prod_singleton]
  rw [_root_.mul_assoc]
  congr 1
  rw [Fin.prod_univ_four, Fin.prod_univ_four, f₀, f₁, f₂, f₃, f₄, Over.comp_left _ _ _ (snd D.P.A _) g.pG]
  generalize h (_ ≫ g.pG.left) = a
  generalize h (_ ≫ D.Oφ g.pG β 0) = b
  generalize h (_ ≫ D.Oφ g.pG β 1) = c
  generalize h (_ ≫ D.Oφ g.pG β 3) = d
  change a ^ ((l : ℤ) - 1) * b ^ (1 : ℤ) * c ^ (-1 : ℤ) * d ^ (1 : ℤ) *
    (b ^ (-1 : ℤ) * c ^ (1 : ℤ) * a ^ (1 : ℤ) * d ^ (-1 : ℤ)) = a ^ (l : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem level (k l : ℕ) (d : ∀ p : D.X × D.X, LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4)
      (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i))
      (Sum.elim (DegPre.famε k) (DegPre.famε l)))) (s : Finset D.X)
    (H : ∀ (T : Over (Spec (CommRingCat.of R))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj R I e G).left),
      xe ≫ g.pG.left = x.left → ye ≫ g.pG.left = y.left →
      xe ≫ (thickObj R I e G).hom = ye ≫ (thickObj R I e G).hom → ∀ (z : T.left) (J), Good D.P.L z J →
      ∑ α ∈ s, ∑ β ∈ s, sval (d (α, β)) (lift x y).left z J *
        ((val (g.t α) xe z J).val * (val (g.t β) ye z J).val) = 0)
    (α : D.X) (hα : α ∈ s) (β : D.X) (hβ : β ∈ s) (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ D.P.A).left)
    (hr : ∃ ρ : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ρ ≫ thick R I e = r ≫ (D.P.A ⊗ D.P.A).hom)
    (z : Z) (J) (hJ : Good D.P.L z J) : sval (d (α, β)) r z J = 0 := by
  let Ge := (Over.map (thick R I e)).obj (thickObj R I e G)
  have hcl : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have ex : ∀ α : D.X, ∃ t : LB.Sec (LB.LinComb D.P.L
      (Sum.elim (fun i => (fst D.P.A Ge).left ≫ D.famφB α i) (fun _ : Unit => (snd D.P.A Ge ≫ g.pG).left))
      (Sum.elim (DegPre.famε k) (fun _ => (l : ℤ)))), ∀ (Z : Scheme.{0}) (r : Z ⟶ (D.P.A ⊗ Ge).left) (z : Z) (J),
      Good D.P.L z J → sval t r z J = ∑ β ∈ s, sval (d (α, β)) (r ≫ (D.P.A ◁ g.pG).left) z J *
        (val (g.t β) (r ≫ (snd D.P.A Ge).left) z J).val := by
    intro α
    choose u hu using fun β : D.X => exists_sec D.P.isLB (formEq_cancel g k l α β)
      (pullMulSec (d (α, β)) (D.P.A ◁ g.pG).left (LB.pullGen D.P.L _ _ (g.t β) (snd D.P.A Ge).left)
        (DVR.pullGen_isGen D.P.L _ _ _ (g.t_gen β) _))
    obtain ⟨t, ht⟩ := exists_sec_finsum s u
    refine ⟨t, fun Z r z J hJ => (ht Z r z J hJ).trans (Finset.sum_congr rfl fun β _ => ?_)⟩
    rw [hu β Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, val_pull hJ]
  choose t ht using ex
  have h₁ := sval_eq_zero_of_sum_mul_coord R I D e G g (D.P.A ⊗ Ge) (fst _ _) _ _ _ t s (by
    intro Z x r hx z J hJ
    let r' : Over.mk (r ≫ (D.P.A ⊗ Ge).hom) ⟶ D.P.A ⊗ Ge := Over.homMk r rfl
    have E := H _ (r' ≫ fst _ _) (r' ≫ snd _ _ ≫ g.pG) x (r ≫ (snd D.P.A Ge).left) hx.symm
      (Category.assoc _ _ _) (by
        rw [← cancel_mono (thick R I e), Category.assoc, Category.assoc, Category.assoc]
        have w₁ : g.pG.left ≫ D.P.A.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w g.pG
        have w₂ : (snd D.P.A Ge).left ≫ (thickObj R I e G).hom ≫ thick R I e = (D.P.A ⊗ Ge).hom :=
          Over.w (snd D.P.A Ge)
        rw [w₂, ← w₁, ← Category.assoc, ← hx, Category.assoc, Over.w]) z J hJ
    have e₁ : lift (r' ≫ fst _ _) (r' ≫ snd _ _ ≫ g.pG) = r' ≫ D.P.A ◁ g.pG := by
      ext1 <;> simp
    rw [e₁] at E
    refine Eq.trans (Finset.sum_congr rfl fun α _ => ?_) E
    rw [ht α Z r z J hJ, Finset.sum_mul]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [_root_.mul_assoc, mul_comm (val (g.t β) _ z J).val]
    rfl) α hα
  have h₂ := LiftTest.main R I D e G g (D.P.A ⊗ Ge) (fst _ _) _ D.P.L D.P.isLB _ _ _ (t α) h₁
  have h₃ := sval_eq_zero_of_sum_mul_coord R I D e G g (D.P.A ⊗ D.P.A) (snd _ _) _
    (fun β => Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
      (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i)) _ (fun β => d (α, β)) s (by
    intro Z y r hy z J hJ
    let r' : Over.mk (r ≫ (D.P.A ⊗ D.P.A).hom) ⟶ D.P.A ⊗ D.P.A := Over.homMk r rfl
    let y' : Over.mk (r ≫ (D.P.A ⊗ D.P.A).hom) ⟶ Ge := Over.homMk y (by
      change y ≫ Ge.hom = r ≫ (D.P.A ⊗ D.P.A).hom
      rw [← Over.w g.pG, ← Category.assoc, ← hy, Category.assoc, Over.w])
    have hy' : r' ≫ snd _ _ = y' ≫ g.pG := Over.OverMorphism.ext hy
    have e₁ : lift (r' ≫ fst _ _) y' ≫ D.P.A ◁ g.pG = r' := by
      ext1
      · simp
      · rw [hy', Category.assoc, whiskerLeft_snd, lift_snd_assoc]
    have e₂ : (lift (r' ≫ fst _ _) y').left ≫ (D.P.A ◁ g.pG).left = r := congrArg CommaMorphism.left e₁
    have e₃ : (lift (r' ≫ fst _ _) y').left ≫ (snd D.P.A Ge).left = y :=
      congrArg CommaMorphism.left (lift_snd (r' ≫ fst _ _) y')
    have E := h₂ Z (lift (r' ≫ fst _ _) y').left ⟨y ≫ (thickObj R I e G).hom, by
      rw [Over.w, Category.assoc]
      exact Over.w y'⟩ z J hJ
    rw [ht α _ _ z J hJ, e₂, e₃] at E
    exact E) β hβ
  exact LiftTest.main R I D e G g (D.P.A ⊗ D.P.A) (snd _ _) _ D.P.L D.P.isLB _ _ _ (d (α, β)) h₃ Z r hr z J hJ

theorem main : (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (k l : ℕ) (d : ∀ p : D.X × D.X, LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i)) (Sum.elim (DegPre.famε k) (DegPre.famε l)))), (∀ e : ℕ, ∃ s₀ : Finset D.X, ∀ s : Finset D.X, s₀ ⊆ s → ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (xe ye : T.left ⟶ (thickObj V (IsLocalRing.maximalIdeal V) e G).left), xe ≫ (U.gt e).pG.left = x.left → ye ≫ (U.gt e).pG.left = y.left → xe ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom = ye ≫ (thickObj V (IsLocalRing.maximalIdeal V) e G).hom → ∀ (z : T.left) (J), Good D.P.L z J → ∑ α ∈ s, ∑ β ∈ s, sval (d (α, β)) (lift x y).left z J * ((val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val) = 0) → ∀ p j, (d p).f j = 0) := by
  classical
  intro V _ _ _ hV D A G _ _ U k l d H p j
  have := hV.1
  have := D.P.isAb.smooth
  have := D.P.isAb.geomConnected
  have : Smooth (D.P.A ⊗ D.P.A).hom := inferInstanceAs (Smooth (pullback.fst D.P.A.hom D.P.A.hom ≫ D.P.A.hom))
  have : GeometricallyConnected (D.P.A ⊗ D.P.A).hom := by
    change GeometricallyConnected (pullback.fst D.P.A.hom D.P.A.hom ≫ D.P.A.hom)
    exact GeometricallyConnected.comp _ _
  refine sec_eq_zero_of_thickenings_of_section V (IsLocalRing.maximalIdeal V)
    (IsLocalRing.maximalIdeal_le_jacobson _) (D.P.A ⊗ D.P.A) (lift η[D.P.A] η[D.P.A]) _
    (DVR.linComb_isLB D.P.L D.P.isLB _ _) (d p) (fun e j => app_sec_eq_zero_of_sval D.P.isLB (d p) _ ?_ j) j
  obtain ⟨s₀, hs⟩ := H e
  exact level (U.gt e) k l d (insert p.1 (insert p.2 s₀))
    (hs _ ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))) p.1 (Finset.mem_insert_self _ _) p.2
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) _ _
    ⟨pullback.snd _ _, pullback.condition.symm⟩

end GlobalTheory.WeightTwo
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaCoefficientsAbelianSquare

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddCoeff
open ReciprocityTheory.ChartRestriction.G.DVR

theorem sum_diff_inj {X : Type} [AddCommGroup X] [Module.Free ℤ X] {a b a' b' : X} (h₁ : a + b = a' + b')
    (h₂ : a - b = a' - b') : a = a' ∧ b = b' := by
  have e : (2 : ℤ) • a = (2 : ℤ) • a' := by
    rw [two_smul, two_smul]
    calc a + a = (a + b) + (a - b) := by abel
      _ = a' + a' := by rw [h₁, h₂]; abel
  have ha : a = a' := smul_right_injective X two_ne_zero e
  subst ha
  exact ⟨rfl, add_left_cancel h₁⟩

theorem reindex {X R : Type} [AddCommGroup X] [Module.Free ℤ X] [CommRing R] (s₀ s : Finset X)
    (hs : ∀ a ∈ s₀, ∀ b ∈ s₀, a + b ∈ s ∧ a - b ∈ s) (F g c : X → X → R)
    (hF : ∀ a b, a ∉ s₀ ∨ b ∉ s₀ → F a b = 0) (g₁ : ∀ a b, g (a + b) (a - b) = F a b)
    (g₀ : ∀ α β, (¬ ∃ a b, α = a + b ∧ β = a - b) → g α β = 0) :
    ∑ α ∈ s, ∑ β ∈ s, g α β * c α β = ∑ a ∈ s₀, ∑ b ∈ s₀, F a b * c (a + b) (a - b) := by
  classical
  rw [← Finset.sum_product', ← Finset.sum_product']
  symm
  refine Finset.sum_of_injOn (fun p : X × X => (p.1 + p.2, p.1 - p.2)) ?_ ?_ ?_ ?_
  · intro p _ q _ h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    exact Prod.ext (sum_diff_inj h₁ h₂).1 (sum_diff_inj h₁ h₂).2
  · intro p hp
    obtain ⟨h₁, h₂⟩ := Finset.mem_product.1 hp
    exact Finset.mem_product.2 (hs _ h₁ _ h₂)
  · rintro ⟨α, β⟩ _ hp
    by_cases h : ∃ a b, α = a + b ∧ β = a - b
    · obtain ⟨a, b, rfl, rfl⟩ := h
      have : a ∉ s₀ ∨ b ∉ s₀ := by
        by_contra hc
        push Not at hc
        exact hp ⟨(a, b), Finset.mem_coe.2 (Finset.mem_product.2 hc), rfl⟩
      simp only [g₁, hF a b this, zero_mul]
    · simp only [g₀ α β h, zero_mul]
  · intro p _
    simp only [g₁]

section
variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem sval_zero_of (s : LB.Sec (LB.LinComb L φ ε)) (h : ∀ j, s.f j = 0) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    sval s r z J = 0 := by
  refine (congrArg (gs r z (LB.wchart L φ (fun k => J (r ≫ φ k)))) (h _)).trans ((gs_eq r z _ (hJ.mem φ r) _).trans ?_)
  exact (congrArg _ (map_zero _)).trans (map_zero _)

theorem gs_scal {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z) (c : R) :
    gs r z ⊤ (scal p c) = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := by
  calc gs r z ⊤ (scal p c) = gs (𝟙 _ ≫ r) z ⊤ (scal p c) := by rw [Category.id_comp]
    _ = gs (𝟙 _) z (r ⁻¹ᵁ ⊤) ((r.app ⊤).hom (scal p c)) := (gs_pull (𝟙 _) r z ⊤ (by trivial) _).symm
    _ = gs (𝟙 _) z ⊤ (scal (r ≫ p) c) := rfl

theorem exists_sub_scale (s t : LB.Sec (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)) : ∃ d : LB.Sec (LB.LinComb L φ ε),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval s r z J - gs r z ⊤ c * sval t r z J := by
  refine ⟨SecOps.secAdd s (SecOps.secNeg (SecOps.secScale c t)), fun Z r z J hJ => ?_⟩
  have hm := hJ.mem φ r
  have e : sval (SecOps.secScale c t) r z J = gs r z ⊤ c * sval t r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg (· * _) (gs_res r z le_top hm c))
  have e' : ∀ u : LB.Sec (LB.LinComb L φ ε), sval (SecOps.secNeg u) r z J = - sval u r z J := fun u =>
    (gs_eq r z _ hm _).trans (((congrArg _ (map_neg _ _)).trans (map_neg _ _)).trans
      (congrArg Neg.neg (gs_eq r z _ hm _).symm))
  refine (gs_add r z _ hm _ _).trans ?_
  rw [sub_eq_add_neg, ← e, ← e']
  rfl
end

theorem main : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α), U.AddG θ r σ σ' → U.ExpT (𝟙_ _) 1 θ f₀ → (∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) → AddB D (𝟙_ _) f₀ r f f') := by
  classical
  intro hGF V _ _ _ hV D A G _ _ U θ f₀ r n σ σ' f f' hA hθ hσ
  have hlev := GlobalTheory.addition_formula_expanded_at_level hGF V hV D A G U θ f₀ r n σ σ' f f' hA hθ hσ
  have hbox := GlobalTheory.UU.BoxSec.main V D (𝟙_ _) (toUnit _)
  have hd : ∀ p : D.X × D.X, ∃ d : LB.Sec (LB.LinComb D.P.L (K := Fin 4 ⊕ Fin 4) (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB p.1 i) (fun i => (snd D.P.A D.P.A).left ≫ D.famφB p.2 i)) (Sum.elim (DegPre.famε 2) (DegPre.famε 2))),
      ∀ (T : Over (Spec (CommRingCat.of V))) (x y : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        (∀ a b, p.1 = a + b → p.2 = a - b → sval d (lift x y).left z J =
          ∑ i, sval (f i p.1) (lift (toUnit T) x).left z J * sval (f' i p.2) (lift (toUnit T) y).left z J -
          gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val *
            (sval (f₀ a) (lift (toUnit T) (x * y)).left z J * sval (f₀ b) (lift (toUnit T) (x * y⁻¹)).left z J)) ∧
        ((¬ ∃ a b, p.1 = a + b ∧ p.2 = a - b) → sval d (lift x y).left z J =
          ∑ i, sval (f i p.1) (lift (toUnit T) x).left z J * sval (f' i p.2) (lift (toUnit T) y).left z J) := by
    rintro ⟨α, β⟩
    obtain ⟨d₁, h₁⟩ := (hbox α β).1 n (fun i => f i α) (fun i => f' i β)
    simp only [comp_toUnit] at h₁
    by_cases h : ∃ a b, α = a + b ∧ β = a - b
    · obtain ⟨a, b, ha, hb⟩ := h
      obtain ⟨d₂, h₂⟩ := (hbox α β).2 a b (f₀ a) (f₀ b) ha hb
      simp only [comp_toUnit] at h₂
      obtain ⟨d, hd⟩ := exists_sub_scale d₁ d₂ (scal (D.P.A ⊗ D.P.A).hom r)
      refine ⟨d, fun T x y z J hJ => ⟨fun a' b' ha' hb' => ?_, fun h => absurd ⟨a, b, ha, hb⟩ h⟩⟩
      obtain ⟨rfl, rfl⟩ := sum_diff_inj (ha.symm.trans ha') (hb.symm.trans hb')
      rw [hd _ _ z J hJ, h₁ T x y z J hJ, h₂ T x y z J hJ, gs_scal, Over.w, _root_.mul_assoc]
    · exact ⟨d₁, fun T x y z J hJ => ⟨fun a b ha hb => absurd ⟨a, b, ha, hb⟩ h, fun _ => h₁ T x y z J hJ⟩⟩
  choose d hd using hd
  have h0 := GlobalTheory.WeightTwo.main V hV D A G U 2 2 d (fun e => by
    obtain ⟨s₀, H⟩ := hlev e
    refine ⟨s₀ ∪ Finset.image₂ (· + ·) s₀ s₀ ∪ Finset.image₂ (· - ·) s₀ s₀,
      fun s hs T x y xe ye hx hy hxy z J hJ => ?_⟩
    obtain ⟨H₁, H₂⟩ := H T x y xe ye hx hy hxy z J hJ
    have hs₀ : s₀ ⊆ s := (Finset.subset_union_left.trans Finset.subset_union_left).trans hs
    have R := reindex s₀ s (fun a ha b hb =>
        ⟨hs (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image₂_of_mem ha hb))),
          hs (Finset.mem_union_right _ (Finset.mem_image₂_of_mem ha hb))⟩)
      (fun a b => gs (𝟙 _) z ⊤ (scal T.hom r) * (kapV D a b z J x y).val *
        (sval (f₀ a) (lift (toUnit T) (x * y)).left z J * sval (f₀ b) (lift (toUnit T) (x * y⁻¹)).left z J))
      (fun α β => ∑ i, sval (f i α) (lift (toUnit T) x).left z J * sval (f' i β) (lift (toUnit T) y).left z J -
        sval (d (α, β)) (lift x y).left z J)
      (fun α β => (val ((U.gt e).t α) xe z J).val * (val ((U.gt e).t β) ye z J).val)
      (by
        rintro a b (h | h)
        · rw [(H₁ a h).1, zero_mul, mul_zero]
        · rw [(H₁ b h).2, mul_zero, mul_zero])
      (fun a b => by rw [(hd (a + b, a - b) T x y z J hJ).1 a b rfl rfl, sub_sub_cancel])
      (fun α β h => by rw [(hd (α, β) T x y z J hJ).2 h, sub_self])
    rw [← H₂ s hs₀] at R
    simp only [sub_mul, Finset.sum_sub_distrib] at R
    exact sub_eq_self.1 R)
  intro T ρ x y z J hJ
  obtain rfl : ρ = toUnit T := toUnit_unique _ _
  refine ⟨fun a b α β hα hβ => ?_, fun α β h => ?_⟩
  · exact sub_eq_zero.1 (((hd (α, β) T x y z J hJ).1 a b hα hβ).symm.trans (sval_zero_of _ (h0 _) _ z hJ))
  · exact ((hd (α, β) T x y z J hJ).2 h).symm.trans (sval_zero_of _ (h0 _) _ z hJ)

end GlobalTheory.AddCoeff
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaCoefficientsAbelianSquareStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.additionFormula_coefficients_abelian_square : GlobalFnsSt → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (θ : U.SecGT (𝟙_ _) 1) (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (r : V) (n : ℕ) (σ σ' : Fin n → U.SecGT (𝟙_ _) 2) (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α), U.AddG θ r σ σ' → U.ExpT (𝟙_ _) 1 θ f₀ → (∀ i, U.ExpT (𝟙_ _) 2 (σ i) (f i) ∧ U.ExpT (𝟙_ _) 2 (σ' i) (f' i)) → AddB D (𝟙_ _) f₀ r f f') := by
  first | exact @GlobalTheory.AddCoeff.main | exact GlobalTheory.AddCoeff.main | (intros; apply GlobalTheory.AddCoeff.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AdditionFormulaAlgClosureWithExpansions

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.AddClosure

theorem addB_of_pull {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (f₀ : ∀ α, SecBT D (𝟙_ _) 1 α) (s₀ : Raw D F 1) (r : R) {n : ℕ}
    (f f' : Fin n → ∀ α, SecBT D (𝟙_ _) 2 α) (s s' : Fin n → Raw D F 2)
    (h₀ : PullB D F (toUnit _) 1 f₀ s₀) (h : ∀ i, PullB D F (toUnit _) 2 (f i) (s i))
    (h' : ∀ i, PullB D F (toUnit _) 2 (f' i) (s' i)) (hB : AddB D (𝟙_ _) f₀ r f f') :
    AddB D (TF (R := R) F) s₀ r s s' := by
  intro T ρ x y z J hJ
  obtain ⟨h1, h2⟩ := hB T (ρ ≫ toUnit _) x y z J hJ
  have e₀ := fun α w => GlobalTheory.pullB_values R D F _ _ 1 f₀ s₀ h₀ α T ρ w z J hJ
  have e := fun i α w => GlobalTheory.pullB_values R D F _ _ 2 (f i) (s i) (h i) α T ρ w z J hJ
  have e' := fun i α w => GlobalTheory.pullB_values R D F _ _ 2 (f' i) (s' i) (h' i) α T ρ w z J hJ
  refine ⟨fun a b α β ha hb => ?_, fun α β hn => ?_⟩
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) ((h1 a b α β ha hb).trans ?_)
    · exact congrArg₂ (· * ·) (e i α x) (e' i β y)
    · exact congrArg _ (congrArg₂ (· * ·) (e₀ a _).symm (e₀ b _).symm)
  · refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (h2 α β hn)
    exact congrArg₂ (· * ·) (e i α x) (e' i β y)

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ θ f, U.Theta θ f → ∀ (th : LB.Sec (LPow A.A A.L ((1 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s₀ : Raw D (Kbar V) 1), U.PullG (Kbar V) (toUnit _) 1 θ th → PullB D (Kbar V) (toUnit _) 1 f s₀ → ∃ (r : V) (n : ℕ) (t t' : Fin n → LB.Sec (LPow A.A A.L ((2 : ℕ) : ℤ) (TFK (R := V) (Kbar V)))) (s s' : Fin n → Raw D (Kbar V) 2), r ≠ 0 ∧ (∀ i, U.ExpF (Kbar V) 2 (t i) (s i) ∧ U.ExpF (Kbar V) 2 (t' i) (s' i)) ∧ AddA A (TFK (R := V) (Kbar V)) th t t' ∧ AddB D (TF (R := V) (Kbar V)) s₀ r s s') := by
  intro hL hL2 V _ _ _ hV D A G _ _ U θ f hθ th s₀ hth hs₀
  obtain ⟨r, n, σ, σ', hr, hG⟩ := GlobalTheory.T.exists_integral_addition_formula_group V hV D A G U θ
  have hexp := GlobalTheory.BaseExpansionExists.main hL hL2 V hV D A G U 2 (by norm_num)
  choose g hg using hexp
  obtain ⟨hpG, hpB⟩ := GlobalTheory.UU.PullSec.pullEx V hV D A G U (Kbar V) (𝟙_ _) (toUnit _) 2
  choose pt hpt using fun σ => (hpG σ).exists
  choose ps hps using fun f => (hpB f).exists
  have hB := GlobalTheory.T.additionFormula_coefficients_abelian_square hL.globalFns V hV D A G U θ f r n σ σ' (fun i => g (σ i)) (fun i => g (σ' i)) hG hθ.1
    (fun i => ⟨hg _, hg _⟩)
  refine ⟨r, n, fun i => pt (σ i), fun i => pt (σ' i), fun i => ps (g (σ i)), fun i => ps (g (σ' i)), hr,
    fun i => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 2 _ _ _ _ (hg _) (hpt _) (hps _)
  · exact GlobalTheory.expF_of_pull V D _ A G U (Kbar V) 2 _ _ _ _ (hg _) (hpt _) (hps _)
  · exact GlobalTheory.AddGeneric.addA_of_addG V D _ A G U (Kbar V) θ r n σ σ' th _ _ hr hG hth (fun i => ⟨hpt _, hpt _⟩)
  · exact addB_of_pull D (Kbar V) f s₀ r _ _ _ _ hs₀ (fun i => hps _) (fun i => hps _) hB

end GlobalTheory.AddClosure
end
end
