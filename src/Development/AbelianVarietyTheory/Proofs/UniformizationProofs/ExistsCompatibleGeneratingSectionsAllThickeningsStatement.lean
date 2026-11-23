module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGradedRingKernelLift
public import Mathlib.Tactic.Monotonicity.Lemmas
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SerreVanishingVeryAmpleStatement
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLeChart
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProjStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBase
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SectionPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPull
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsH1VanishesGeneratedPullbackPowTensorDual

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.TwistPair
variable {X W W₁ : Scheme.{0}}

theorem firstCohomologyVanishes_of_refines {M N : LB X} (c : M.ι → N.ι) (le : ∀ k, M.U k ≤ N.U (c k))
    (hg : ∀ k l, M.g k l = res (inf_le_inf (le k) (le l)) (N.g (c k) (c l))) (h : FirstCohomologyVanishes N) :
    FirstCohomologyVanishes M := by
  intro I V d hV hc φ hφ
  have e : ∀ (a b : I) {U : X.Opens} (h₁ : U ≤ M.U (d a) ⊓ M.U (d b)),
      rs X h₁ (M.g (d a) (d b)).val =
        rs X (h₁.trans (inf_le_inf (le _) (le _))) (N.g (c (d a)) (c (d b))).val := fun a b U h₁ => by
    rw [hg]
    exact rs_rs _ _ _
  obtain ⟨ψ, hψ⟩ := h I V (fun a => c (d a)) (fun a => (hV a).trans (le _)) hc φ (fun a b b' => by
    have := hφ a b b'
    rw [e] at this
    exact this)
  refine ⟨ψ, fun a b => ?_⟩
  rw [e]
  exact hψ a b

def secRefine {M N : LB X} (c : M.ι → N.ι) (le : ∀ k, M.U k ≤ N.U (c k))
    (hg : ∀ k l, M.g k l = res (inf_le_inf (le k) (le l)) (N.g (c k) (c l))) (s : LB.Sec N) :
    LB.Sec M where
  f := fun k => rs X (le k) (s.f (c k))
  compat := fun k l => by
    have h := congrArg (rs X (inf_le_inf (le k) (le l))) (s.compat (c k) (c l))
    rw [hg]
    rw [map_mul] at h
    refine (rs_rs _ _ _).trans (((rs_rs _ _ _).symm.trans h).trans ?_)
    exact congrArg₂ (· * ·) rfl ((rs_rs _ _ _).trans (rs_rs _ _ _).symm)

theorem nonzeroLocus_le_secRefine {M N : LB X} (c : M.ι → N.ι) (le : ∀ k, M.U k ≤ N.U (c k))
    (hg : ∀ k l, M.g k l = res (inf_le_inf (le k) (le l)) (N.g (c k) (c l))) (hM : M.IsLB)
    (s : LB.Sec N) : nonzeroLocus s ≤ nonzeroLocus (secRefine c le hg s) := by
  intro x hx
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  obtain ⟨k, hk⟩ := exists_chart hM x
  refine Opens.mem_iSup.2 ⟨k, ?_⟩
  have h₁ : x ∈ X.basicOpen (rs X (inf_le_left : N.U i ⊓ N.U (c k) ≤ N.U i) (s.f i)) := by
    have := Scheme.basicOpen_res X (s.f i) (homOfLE (inf_le_left : N.U i ⊓ N.U (c k) ≤ N.U i)).op
    exact this.ge ⟨⟨X.basicOpen_le _ hi, le k hk⟩, hi⟩
  have h₂ : x ∈ X.basicOpen (rs X (inf_le_right : N.U i ⊓ N.U (c k) ≤ N.U (c k)) (s.f (c k))) := by
    have := (congrArg X.basicOpen (s.compat i (c k))).le h₁
    rw [Scheme.basicOpen_mul] at this
    exact this.2
  have h₃ := (Scheme.basicOpen_res X (s.f (c k))
    (homOfLE (inf_le_right : N.U i ⊓ N.U (c k) ≤ N.U (c k))).op).le h₂
  exact (Scheme.basicOpen_res X (s.f (c k)) (homOfLE (le k)).op).ge ⟨hk, h₃.2⟩

theorem gm_tw (H : LB X) (a b : W ⟶ X) (t : ℤ) (y : W) (i j i' j' : H.ι)
    (hi : a y ∈ H.U i) (hj : b y ∈ H.U j) (hi' : a y ∈ H.U i') (hj' : b y ∈ H.U j') :
    gm (𝟙 W) y _ ((tw (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (H.pull a) t).g
      (fun _ => j, fun _ => i) (fun _ => j', fun _ => i')) =
      gm a y _ (H.g i i') ^ t * gm b y _ (H.g j j') ^ (-1 : ℤ) := by
  have m : ∀ (e : W ⟶ X) (k : H.ι), e y ∈ H.U k → (𝟙 W : W ⟶ W) y ∈ LB.wchart H (K := PUnit) (fun _ => e) (fun _ => k) :=
    fun e k h => Set.mem_iInter.2 fun _ => h
  refine (gm_div (pw (H.pull a) (-t)) (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (𝟙 W) y
    (fun _ => j, fun _ => i) (fun _ => j', fun _ => i') ⟨⟨m b j hj, m a i hi⟩, m b j' hj', m a i' hi'⟩).trans ?_
  have e₁ := gm_linComb H (K := PUnit) (fun _ => b) (fun _ => -1) (𝟙 W) y (fun _ => j) (fun _ => j')
    (m b j hj) (m b j' hj')
  have e₂ := gm_pull_g H a (𝟙 W) y (fun _ => i) (fun _ => i') (m a i hi) (m a i' hi')
  rw [Fintype.prod_unique, Category.id_comp] at e₁
  rw [Category.id_comp] at e₂
  refine (congrArg₂ (fun u v => u * v⁻¹) e₁ ((map_zpow _ _ _).trans (congrArg (· ^ (-t)) e₂))).trans ?_
  simp only [zpow_neg, inv_inv]
  exact mul_comm _ _

theorem gm_pair (H : LB X) (a b : W₁ ⟶ X) (t : ℤ) (σ : W ⟶ W₁) (y : W) (j j' : Fin 2 → H.ι)
    (hj : σ y ∈ LB.wchart H ![a, b] j) (hj' : σ y ∈ LB.wchart H ![a, b] j') :
    gm σ y _ ((LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]).g j j') =
      gm (σ ≫ a) y _ (H.g (j 0) (j' 0)) ^ t * gm (σ ≫ b) y _ (H.g (j 1) (j' 1)) ^ (-1 : ℤ) :=
  (gm_linComb H ![a, b] ![t, -1] σ y j j' hj hj').trans (Fin.prod_univ_two _)

theorem twist_pair : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (W X : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of S)) (H : LB X) (a b : W ⟶ X) (n : ℕ) (s : Fin (n + 1) → LB.Sec (H.pull a)), H.IsLB → VeryAmpleBy f (H.pull a) s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → (∀ (W₁ : Scheme.{0}) (σ : W ⟶ W₁) (a₁ b₁ : W₁ ⟶ X), σ ≫ a₁ = a → σ ≫ b₁ = b → FirstCohomologyVanishes ((LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ)) ∧ ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1])), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  intro S _ _ W X f H a b n s hH hs
  have hM : (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)).IsLB := LB.isLB_linComb hH _ _
  have hA : (H.pull a).IsLB := LB.isLB_pull hH a
  obtain ⟨t₁, h₁⟩ := GlobalTheory.T.serre_vanishing_very_ample.1 S W f _ n s hA hs _ hM
  obtain ⟨t₂, h₂⟩ := GlobalTheory.TwistGen.twist_generated S W f _ n s hA hs _ hM
  refine ⟨max t₁ t₂, fun t ht => ⟨?_, ?_⟩⟩
  · rintro W₁ σ a₁ b₁ rfl rfl
    have le : ∀ J : PUnit → Fin 2 → H.ι, ((LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ).U J ≤
        (tw (LB.LinComb H (K := PUnit) (fun _ => σ ≫ b₁) (fun _ => -1)) (H.pull (σ ≫ a₁)) t).U
          (fun _ => J PUnit.unit 1, fun _ => J PUnit.unit 0) := fun J y hy =>
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (mem_pull.1 hy) 1,
        Set.mem_iInter.2 fun _ => Set.mem_iInter.1 (mem_pull.1 hy) 0⟩
    refine firstCohomologyVanishes_of_refines (M := (LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ) _ le
      (fun J J' => unit_ext fun y hy => ?_) (h₁ t (le_of_max_le_left ht))
    have p := mem_pull.1 hy.1
    have p' := mem_pull.1 hy.2
    refine (gm_pull_g _ σ (𝟙 W) y J J' hy.1 hy.2).trans (Eq.trans ?_ (gm_res (𝟙 W) y _ hy _).symm)
    rw [Category.id_comp]
    exact (gm_pair H a₁ b₁ t σ y _ _ p p').trans (gm_tw H (σ ≫ a₁) (σ ≫ b₁) t y _ _ _ _
      (Set.mem_iInter.1 p 0) (Set.mem_iInter.1 p 1) (Set.mem_iInter.1 p' 0) (Set.mem_iInter.1 p' 1)).symm
  · obtain ⟨m, u, hu⟩ := h₂ t (le_of_max_le_right ht)
    have le : ∀ J : Fin 2 → H.ι, (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]).U J ≤
        (tw (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (H.pull a) t).U
          (fun _ => J 1, fun _ => J 0) := fun J y hy =>
      ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 1,
        Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy 0⟩
    have hg : ∀ J J' : Fin 2 → H.ι, (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]).g J J' =
        res (inf_le_inf (le J) (le J'))
          ((tw (LB.LinComb H (K := PUnit) (fun _ => b) (fun _ => -1)) (H.pull a) t).g
            (fun _ => J 1, fun _ => J 0) (fun _ => J' 1, fun _ => J' 0)) := fun J J' =>
      unit_ext fun y hy => by
        refine (gm_pair H a b t (𝟙 W) y _ _ hy.1 hy.2).trans (Eq.trans ?_ (gm_res (𝟙 W) y _ hy _).symm)
        rw [Category.id_comp, Category.id_comp]
        exact (gm_tw H a b t y _ _ _ _ (Set.mem_iInter.1 hy.1 0) (Set.mem_iInter.1 hy.1 1)
          (Set.mem_iInter.1 hy.2 0) (Set.mem_iInter.1 hy.2 1)).symm
    refine ⟨m, fun i => secRefine (M := LB.LinComb H (K := Fin 2) ![a, b] ![t, -1]) _ le hg (u i),
      top_unique ?_⟩
    rw [← hu]
    exact iSup_mono fun i => nonzeroLocus_le_secRefine _ le hg (LB.isLB_linComb hH _ _) (u i)

end GlobalTheory.TwistPair
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsH1VanishesGeneratedPullbackPowTensorDualStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_h1Vanishes_generated_pullbackPow_tensor_dual : ∀ (S : Type) [CommRing S] [IsNoetherianRing S] (W X : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of S)) (H : LB X) (a b : W ⟶ X) (n : ℕ) (s : Fin (n + 1) → LB.Sec (H.pull a)), H.IsLB → VeryAmpleBy f (H.pull a) s → ∃ t₀ : ℤ, ∀ t, t₀ ≤ t → (∀ (W₁ : Scheme.{0}) (σ : W ⟶ W₁) (a₁ b₁ : W₁ ⟶ X), σ ≫ a₁ = a → σ ≫ b₁ = b → FirstCohomologyVanishes ((LB.LinComb H (K := Fin 2) ![a₁, b₁] ![t, -1]).pull σ)) ∧ ∃ (m : ℕ) (u : Fin (m + 1) → LB.Sec (LB.LinComb H (K := Fin 2) ![a, b] ![t, -1])), ⨆ i, nonzeroLocus (u i) = ⊤ := by
  first | exact @GlobalTheory.TwistPair.twist_pair | exact GlobalTheory.TwistPair.twist_pair | (intros; apply GlobalTheory.TwistPair.twist_pair <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionLiftBaseChangeH1VanishingTestRing

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecLift
open GlobalTheory.CompleteBaseExpansion

theorem exists_lift : ∀ (A A' S : Type) [CommRing A] [CommRing A'] [CommRing S] (g' : A →+* A') (g : A →+* S), (∀ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) A) (D₁ : Matrix (Fin c) (Fin b) A), D₁ * D₀ = 0 → (∀ w : Fin b → S, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) → ∀ v' : Fin a → A', (D₀.map g').mulVec v' = 0 → ∃ v, D₀.mulVec v = 0 ∧ ∀ k, g' (v k) = v' k) → ∀ (X X' XS : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (fS : XS ⟶ Spec (CommRingCat.of S)) (β : X' ⟶ X) (σ : XS ⟶ X), Smooth f → IsProjBy f → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → IsPullback σ fS f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (X ⟶ W)) (φ' : K → (X' ⟶ W)) (ε : K → ℤ), L.IsLB → (∀ k, β ≫ φ k = φ' k) → FirstCohomologyVanishes ((LB.LinComb L φ ε).pull σ) → ∀ s' : LB.Sec (LB.LinComb L φ' ε), ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ z J, Good L z J → sval s β z J = sval s' (𝟙 _) z J := by
  intro A A' S _ _ _ g' g hlift X X' XS f f' fS β σ hs hp pb' pbS W L K _ φ φ' ε hL hφ hH s'
  obtain rfl : (fun k => β ≫ φ k) = φ' := funext hφ
  have hN := DVR.linComb_isLB L hL φ ε
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj A X f hs hp _ hN
  have pb₀ : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id A))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  obtain ⟨E₀, H₀⟩ := P.sec A (RingHom.id A) X (𝟙 _) f pb₀
  obtain ⟨E, H⟩ := P.sec A' g' X' β f' pb'
  obtain ⟨t', ht'⟩ := exists_in (φ := φ) β s'
  obtain ⟨v, hv, hv'⟩ := hlift P.a P.b P.c P.D₀ P.D₁ P.comp (P.exact S g XS σ fS pbS hH) _ (E.symm t').2
  have hv₀ : (P.D₀.map (RingHom.id A)).mulVec v = 0 := hv
  have hs' := (GlobalTheory.SecAlg.sval_eq_iff (P := P) hN H₀ H g' (RingHom.comp_id _) β (Category.comp_id _) pb'.w
    (E₀ ⟨v, hv₀⟩) t').2 (fun k => by rw [E₀.symm_apply_apply]; exact hv' k)
  obtain ⟨s₁, hs₁⟩ := exists_out (𝟙 _) (E₀ ⟨v, hv₀⟩)
  obtain ⟨s, hs⟩ := exists_sec hL (φ' := φ) (ε' := ε) (fun U _ h => by simp only [Category.id_comp]) s₁
  refine ⟨s, fun z J hJ => (hs _ _ z J hJ).trans ((hs₁ _ _ z _ (hJ.mem _ _)).trans ?_)⟩
  have hG : Good (LB.LinComb L φ ε) z (fun ψ i => J (ψ ≫ φ i)) := fun ψ => hJ.mem _ ψ
  refine Eq.trans ?_ ((hs' z _ hG).trans ((ht' _ _ z _ (hG.mem (fun _ : PUnit => β) _)).trans ?_))
  · exact (sval_of (E₀ ⟨v, hv₀⟩) _ z _ _ (fun _ => funext fun i => congrArg J (Category.assoc _ _ _))).symm
  · exact (sval_of s' _ z J _ (fun i => congrArg J (Category.assoc _ _ _).symm)).symm

end GlobalTheory.SecLift
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSectionLiftBaseChangeH1VanishingTestRingStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_section_lift_baseChange_h1Vanishing_testRing : ∀ (A A' S : Type) [CommRing A] [CommRing A'] [CommRing S] (g' : A →+* A') (g : A →+* S), (∀ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) A) (D₁ : Matrix (Fin c) (Fin b) A), D₁ * D₀ = 0 → (∀ w : Fin b → S, (D₁.map g).mulVec w = 0 → ∃ v, (D₀.map g).mulVec v = w) → ∀ v' : Fin a → A', (D₀.map g').mulVec v' = 0 → ∃ v, D₀.mulVec v = 0 ∧ ∀ k, g' (v k) = v' k) → ∀ (X X' XS : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A')) (fS : XS ⟶ Spec (CommRingCat.of S)) (β : X' ⟶ X) (σ : XS ⟶ X), Smooth f → IsProjBy f → IsPullback β f' f (Spec.map (CommRingCat.ofHom g')) → IsPullback σ fS f (Spec.map (CommRingCat.ofHom g)) → ∀ (W : Scheme.{0}) (L : LB W) (K : Type) [Fintype K] (φ : K → (X ⟶ W)) (φ' : K → (X' ⟶ W)) (ε : K → ℤ), L.IsLB → (∀ k, β ≫ φ k = φ' k) → FirstCohomologyVanishes ((LB.LinComb L φ ε).pull σ) → ∀ s' : LB.Sec (LB.LinComb L φ' ε), ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ z J, Good L z J → sval s β z J = sval s' (𝟙 _) z J := by
  first | exact @GlobalTheory.SecLift.exists_lift | exact GlobalTheory.SecLift.exists_lift | (intros; apply GlobalTheory.SecLift.exists_lift <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompatibleGeneratingSectionsAllThickenings

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SecTower

theorem exists_veryAmpleBy_pullback {R R' : Type} [CommRing R] [CommRing R'] (g : R →+* R') {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} {n : ℕ} {s : Fin (n + 1) → LB.Sec H} (hH : H.IsLB)
    (hs : VeryAmpleBy f H s) :
    ∃ s' : Fin (n + 1) → LB.Sec (H.pull (pullback.fst f (Spec.map (CommRingCat.ofHom g)))),
      VeryAmpleBy (pullback.snd f (Spec.map (CommRingCat.ofHom g)))
        (H.pull (pullback.fst f (Spec.map (CommRingCat.ofHom g)))) s' := by
  have hL := LB.isLB_pull hH (pullback.fst f (Spec.map (CommRingCat.ofHom g)))
  have hw := CubePf.idIsoL_isGen hL
  choose s' hs' using fun j => GlobalTheory.SecPullIso.exists_pull _ H (H.pull _) _ hH hL hw (s j)
  refine ⟨s', GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull R X f H n s hH hs R' g _ _ _ pullback.condition ?_ _ _ s' hL hw
    hs'⟩
  rw [pullback.lift_fst_snd]
  infer_instance

theorem exists_test_maps {R S : Type} [CommRing R] [CommRing S] (I : Ideal R) (g : R →+* S) (hg : ∀ x ∈ I, g x = 0)
    (Y : Over (Spec (CommRingCat.of R))) :
    ∃ (g' : ∀ e : ℕ, R ⧸ I ^ (e + 1) →+* S)
      (σ : ∀ e : ℕ, pullback Y.hom (Spec.map (CommRingCat.ofHom g)) ⟶ (thickObj R I e Y).left),
      (∀ e, (g' e).comp (Ideal.Quotient.mk _) = g) ∧
      (∀ e, IsPullback (σ e) (pullback.snd _ _) (thickObj R I e Y).hom (Spec.map (CommRingCat.ofHom (g' e)))) ∧
      (∀ e, σ e ≫ pullback.fst Y.hom (thick R I e) = pullback.fst _ _) ∧
      ∀ e, σ e ≫ thickMap R I e Y = σ (e + 1) := by
  let g' : ∀ e : ℕ, R ⧸ I ^ (e + 1) →+* S := fun e =>
    Ideal.Quotient.lift _ g fun x hx => hg x (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
  have hg' : ∀ e, (g' e).comp (Ideal.Quotient.mk _) = g := fun e => RingHom.ext fun x => rfl
  have hc : ∀ e, Spec.map (CommRingCat.ofHom (g' e)) ≫ thick R I e = Spec.map (CommRingCat.ofHom g) := fun e => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  have ht : ∀ e, Spec.map (CommRingCat.ofHom (g' e)) ≫ thickTrans R I e =
      Spec.map (CommRingCat.ofHom (g' (e + 1))) := fun e => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    rfl
  refine ⟨g', fun e => pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (g' e)))
    (by rw [Category.assoc, hc]; exact pullback.condition), hg', fun e => ?_, fun e => pullback.lift_fst _ _ _,
    fun e => ?_⟩
  · refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick R I e)) (h₂₂ := thick R I e)
      (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [hc, pullback.lift_fst]
    exact IsPullback.of_hasPullback _ _
  · apply pullback.hom_ext
    · erw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst]
    · erw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc, pullback.lift_snd,
        Category.assoc, ht]

theorem isPullback_thickMap {R : Type} [CommRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R))) (e : ℕ) :
    IsPullback (thickMap R I e Y) (thickObj R I e Y).hom (thickObj R I (e + 1) Y).hom (thickTrans R I e) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst Y.hom (thick R I (e + 1))) (h₂₂ := thick R I (e + 1))
    (v₁₃ := Y.hom) ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [thickTrans_comp, pullback.lift_fst, Category.comp_id]
  exact IsPullback.of_hasPullback _ _

theorem exists_tower : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R))) (H : LB Y.left) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), Smooth Y.hom → H.IsLB → VeryAmpleBy Y.hom H s → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Y.left, (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ (t : ℤ) (m : ℕ) (u : ∀ e, Fin (m + 1) → LB.Sec (LB.LinComb H (Y := (thickObj R I e Y).left) (K := Fin 2) ![pullback.fst Y.hom (thick R I e), f e] ![t, -1])), (⨆ i, nonzeroLocus (u 0 i) = ⊤) ∧ ∀ e i z J, Good H z J → sval (u (e + 1) i) (thickMap R I e Y) z J = sval (u e i) (𝟙 _) z J := by
  intro R _ _ I Y H n s hsm hH hs f hf
  obtain ⟨S, _, g, hS, hg, hker⟩ := GlobalTheory.exists_graded_ring_kernel_lift R I
  obtain ⟨g', σ, hg', hσ, hσa, hσt⟩ := exists_test_maps I g hg Y
  have hσb : ∀ e, σ e ≫ f e = σ 0 ≫ f 0 := fun e => by
    induction e with
    | zero => rfl
    | succ e ih => rw [← hσt, Category.assoc, hf, ih]
  obtain ⟨sS, hsS⟩ := exists_veryAmpleBy_pullback g Y.hom hH hs
  have hva := fun e : ℕ => exists_veryAmpleBy_pullback (Ideal.Quotient.mk (I ^ (e + 1))) Y.hom hH hs
  obtain ⟨t₁, h₁⟩ := GlobalTheory.T.exists_h1Vanishes_generated_pullbackPow_tensor_dual S _ _ _ H _ (σ 0 ≫ f 0) n sS hH hsS
  obtain ⟨s₀, hs₀⟩ := hva 0
  obtain ⟨t₂, h₂⟩ := GlobalTheory.T.exists_h1Vanishes_generated_pullbackPow_tensor_dual _ _ _ _ H _ (f 0) n s₀ hH hs₀
  obtain ⟨m, u₀, hu₀⟩ := (h₂ (max t₁ t₂) (le_max_right _ _)).2
  have hZ := (h₁ (max t₁ t₂) (le_max_left _ _)).1
  have step : ∀ (e : ℕ) (v : LB.Sec (LB.LinComb H (Y := (thickObj R I e Y).left) (K := Fin 2)
      ![pullback.fst Y.hom (thick R I e), f e] ![max t₁ t₂, -1])),
      ∃ v' : LB.Sec (LB.LinComb H (Y := (thickObj R I (e + 1) Y).left) (K := Fin 2)
        ![pullback.fst Y.hom (thick R I (e + 1)), f (e + 1)] ![max t₁ t₂, -1]),
        ∀ z J, Good H z J → sval v' (thickMap R I e Y) z J = sval v (𝟙 _) z J := fun e v => by
    obtain ⟨s₁, hs₁⟩ := hva (e + 1)
    refine GlobalTheory.T.exists_section_lift_baseChange_h1Vanishing_testRing _ _ S _ (g' (e + 1)) (hker e (g' (e + 1)) (hg' _)) _ _ _ (thickObj R I (e + 1) Y).hom
      (thickObj R I e Y).hom _ (thickMap R I e Y) (σ (e + 1))
      (inferInstanceAs (Smooth (pullback.snd Y.hom (thick R I (e + 1))))) ⟨_, LB.isLB_pull hH _, n, s₁, hs₁⟩
      (isPullback_thickMap I Y e) (hσ (e + 1)) _ H (Fin 2) _ _ _ hH (fun k => ?_)
      (hZ _ (σ (e + 1)) _ _ (hσa _) (hσb _)) v
    fin_cases k
    · exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    · exact hf e
  choose F hF using step
  exact ⟨max t₁ t₂, m, fun e => Nat.rec (motive := fun e => Fin (m + 1) → LB.Sec (LB.LinComb H
      (Y := (thickObj R I e Y).left) (K := Fin 2) ![pullback.fst Y.hom (thick R I e), f e] ![max t₁ t₂, -1]))
    u₀ (fun e v i => F e (v i)) e, hu₀, fun e i => hF e _⟩

end GlobalTheory.SecTower
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompatibleGeneratingSectionsAllThickeningsStatement

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_compatible_generatingSections_all_thickenings : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R))) (H : LB Y.left) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), Smooth Y.hom → H.IsLB → VeryAmpleBy Y.hom H s → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Y.left, (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ (t : ℤ) (m : ℕ) (u : ∀ e, Fin (m + 1) → LB.Sec (LB.LinComb H (Y := (thickObj R I e Y).left) (K := Fin 2) ![pullback.fst Y.hom (thick R I e), f e] ![t, -1])), (⨆ i, nonzeroLocus (u 0 i) = ⊤) ∧ ∀ e i z J, Good H z J → sval (u (e + 1) i) (thickMap R I e Y) z J = sval (u e i) (𝟙 _) z J := by
  first | exact @GlobalTheory.SecTower.exists_tower | exact GlobalTheory.SecTower.exists_tower | (intros; apply GlobalTheory.SecTower.exists_tower <;> assumption)
end
end
