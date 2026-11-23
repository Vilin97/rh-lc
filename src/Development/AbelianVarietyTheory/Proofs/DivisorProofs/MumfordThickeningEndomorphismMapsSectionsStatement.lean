module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingClosedFibreOfThreeLeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartExpOn
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordMultiplierThickeningChartSectionsStatement
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameExpansionThickeningOpen

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumMult

theorem map_map_homOfLE {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h2).op).hom ((X.presheaf.map (homOfLE h1).op).hom x) =
      (X.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem map_res_homOfLE {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (u : Γ(X, U)ˣ) :
    (X.presheaf.map (homOfLE h2).op).hom (res h1 u).val = (res (h2.trans h1) u).val :=
  map_map_homOfLE h1 h2 u.val

theorem sum_attach_eq_sum_of_subset {β M : Type*} [AddCommMonoid M] {S S' : Finset β} (hS : S ⊆ S') (F : β → M)
    (T : S → M) (hT : ∀ x, T x = F x) (hz : ∀ α ∈ S', α ∉ S → F α = 0) :
    ∑ x ∈ S.attach, T x = ∑ α ∈ S', F α := by
  rw [← Finset.sum_subset hS hz, ← Finset.sum_attach S F]
  exact Finset.sum_congr rfl fun x _ => hT x

theorem eq_of_expandsAt_of_chartExpOn : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens) (hW : W ≤ (fstG I e G).left ⁻¹ᵁ secChart U.LG.L i') (g : Γ((thickObj R I e G).left, W)), U.ExpandsAt e k σ f → GlobalTheory.MumMult.ChartExpOn U e k i' W g f → ((thickObj R I e G).left.presheaf.map (homOfLE hW).op).hom (((fstG I e G).left.app (secChart U.LG.L i')).hom (σ.f i')) = g := by
  intro R _ _ I D A G _ _ U e k σ f i' W hW g hE hC
  classical
  obtain ⟨S₁, h1v, E1⟩ := hE
  obtain ⟨S₂, h2v, E2⟩ := hC
  have hex : ∀ x : D.toPre.P.A.left, ∃ i, x ∈ D.toPre.P.L.U i := fun x => by
    have hx : x ∈ (⨆ i, D.toPre.P.L.U i) := by rw [D.toPre.P.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 hx
  choose idx0 hidx0 using hex
  have key : ∀ y ∈ W, ∃ (V : (thickObj R I e G).left.Opens) (hV : V ≤ W), y ∈ V ∧
      ((thickObj R I e G).left.presheaf.map (homOfLE hV).op).hom
        (((thickObj R I e G).left.presheaf.map (homOfLE hW).op).hom
          (((fstG I e G).left.app (secChart U.LG.L i')).hom (σ.f i'))) =
      ((thickObj R I e G).left.presheaf.map (homOfLE hV).op).hom g := by
    intro y hy
    let idx : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun φ => idx0 (φ.base y)
    have hidx : ∀ φ, φ.base y ∈ D.toPre.P.L.U (idx φ) := fun φ => hidx0 _
    let p : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) :=
      (fun _ => idx (U.gt e).pG.left, fun _ => i' 0)
    let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α κ => idx ((U.gt e).pG.left ≫ D.toPre.famφB α κ)
    let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α κ => idx (D.toPre.Oφ (U.gt e).pG α κ)
    have hcoh : ∀ S : Finset D.toPre.X, CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt e).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt e).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt e).pG a.1.1 a.2)))
        (Sum.elim (fun _ => p.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
      intro S a b hab
      rcases a with a | a | a <;> rcases b with b | b | b <;> exact congrArg idx hab
    have hmem : ∀ S, y ∈ U.expW e p i' S jf jt := by
      intro S
      refine ⟨⟨⟨Set.mem_iInter.2 fun _ => hidx _, Set.mem_iInter.2 fun _ => ?_⟩, hW hy⟩, ?_⟩
      · exact Set.mem_iInter.1 (hW hy) 0
      · refine Finset.inf_induction (p := fun O : (thickObj R I e G).left.Opens => y ∈ O) trivial
          (fun a ha b hb => ⟨ha, hb⟩) ?_
        intro α _
        exact ⟨Set.mem_iInter.2 fun κ => hidx ((U.gt e).pG.left ≫ D.toPre.famφB α κ),
          Set.mem_iInter.2 fun κ => hidx _⟩

    have hV1 : U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W ≤ U.expW e p i' S₁ jf jt :=
      inf_le_left.trans (inf_le_inf_left _ (Finset.inf_mono Finset.subset_union_left))
    have hV2 : U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W ≤ U.expW e p i' S₂ jf jt ⊓ W :=
      inf_le_inf_right _ (inf_le_inf_left _ (Finset.inf_mono Finset.subset_union_right))
    have E1V := congrArg ((thickObj R I e G).left.presheaf.map (homOfLE hV1).op).hom
      (E1 p i' jf jt rfl (hcoh S₁))
    have E2V := congrArg ((thickObj R I e G).left.presheaf.map (homOfLE hV2).op).hom
      (E2 p jf jt rfl (hcoh S₂))

    simp only [map_mul, map_pow, map_sum, map_res_homOfLE, map_map_homOfLE] at E1V E2V
    let tV : ∀ α, α ∈ S₁ ∪ S₂ → Γ((thickObj R I e G).left, U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W) :=
      fun α h => ((thickObj R I e G).left.presheaf.map
          (homOfLE (inf_le_left.trans (U.expW_le_f e p i' jf jt h))).op).hom
          (((U.gt e).pG.left.app _).hom ((f α).f (jf α))) *
        (res (inf_le_left.trans (U.expWeight_le_chart_weight e p i' jf jt h)) (((U.gt e).t α).s (jt α))).val
    let F : D.toPre.X → Γ((thickObj R I e G).left, U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W) :=
      fun α => if h : α ∈ S₁ ∪ S₂ then tV α h else 0
    have hz1 : ∀ α ∈ S₁ ∪ S₂, α ∉ S₁ → F α = 0 := by
      intro α h hn
      have h0 : ((U.gt e).pG.left.app (LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α))).hom
          ((f α).f (jf α)) = 0 := h1v α hn (jf α)
      simp only [F, dif_pos h, tV]
      rw [h0, map_zero, zero_mul]
    have hz2 : ∀ α ∈ S₁ ∪ S₂, α ∉ S₂ → F α = 0 := by
      intro α h hn
      have h0 : ((U.gt e).pG.left.app (LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α))).hom
          ((f α).f (jf α)) = 0 := h2v α hn (jf α)
      simp only [F, dif_pos h, tV]
      rw [h0, map_zero, zero_mul]
    rw [sum_attach_eq_sum_of_subset Finset.subset_union_left F _ (fun x => ?_) hz1] at E1V
    rw [sum_attach_eq_sum_of_subset Finset.subset_union_right F _ (fun x => ?_) hz2] at E2V
    rotate_left
    · simp only [F, dif_pos (Finset.mem_union_right S₁ x.2), tV]
      congr 1 <;> first | rfl | exact map_res_homOfLE _ _ _ | exact map_map_homOfLE _ _ _
    · simp only [F, dif_pos (Finset.mem_union_left S₂ x.2), tV]
      congr 1 <;> first | rfl | exact map_res_homOfLE _ _ _ | exact map_map_homOfLE _ _ _
    refine ⟨U.expW e p i' (S₁ ∪ S₂) jf jt ⊓ W, inf_le_right, ⟨hmem _, hy⟩, ?_⟩
    rw [map_map_homOfLE]
    exact ((Units.isUnit _).pow k).mul_left_cancel (E1V.trans E2V.symm)
  choose V hVW hyV hEq using key
  refine TopCat.Sheaf.eq_of_locally_eq' (thickObj R I e G).left.sheaf (fun y : W => V y.1 y.2) W
    (fun y => homOfLE (hVW y.1 y.2)) ?_ _ _ fun y => hEq y.1 y.2
  intro y hy
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, hy⟩, hyV y hy⟩

end GlobalTheory.MumMult
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSameExpansionThickeningOpenStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.eq_of_same_expansion_thickening_open : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (i' : Fin 1 → U.LG.L.ι) (W : (thickObj R I e G).left.Opens) (hW : W ≤ (fstG I e G).left ⁻¹ᵁ secChart U.LG.L i') (g : Γ((thickObj R I e G).left, W)), U.ExpandsAt e k σ f → GlobalTheory.MumMult.ChartExpOn U e k i' W g f → ((thickObj R I e G).left.presheaf.map (homOfLE hW).op).hom (((fstG I e G).left.app (secChart U.LG.L i')).hom (σ.f i')) = g := by
  first | exact @GlobalTheory.MumMult.eq_of_expandsAt_of_chartExpOn | exact GlobalTheory.MumMult.eq_of_expandsAt_of_chartExpOn | (intros; apply GlobalTheory.MumMult.eq_of_expandsAt_of_chartExpOn <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformisedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_expandsAt_section_uniformised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G), IsSemiAbelian G → ∀ k : ℕ, 1 ≤ k → ∀ F : IntFam (maximalIdeal R) D.toPre k, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ F.f := by
  first | exact @GlobalTheory.Mum.IntFam.exists_expandsAt | exact GlobalTheory.Mum.IntFam.exists_expandsAt | (intros; apply GlobalTheory.Mum.IntFam.exists_expandsAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordSectionsMultiplierThickenings

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumMult

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, 3 ≤ k → ∃ S : H0 U.LG.L k → H0 U.LG.L (N * k), ∃ c : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i'), (∀ (e : ℕ) (s : H0 U.LG.L k) (i i' : Fin 1 → U.LG.L.ι), ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_right : ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i' ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i')).op).hom (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((S s).f i')) = c e i i' * ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_left : ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i' ≤ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom ((((b e).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s.f i))) ∧ ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (c 0 i i') := by
  have hA := GlobalTheory.T.mumfordMultiplier_thickening_chart_sections
  have hU := GlobalTheory.T.eq_of_same_expansion_thickening_open
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, m, hm, y, hy1, hy2⟩ := hA R hB D A G hG U a a' h h' hE b hb
  refine ⟨N, hN, fun k hk => ?_⟩
  choose F hF using hm k hk
  have hNk : 1 ≤ N * k := Nat.mul_pos hN (by omega)
  choose σ hσ using fun s => GlobalTheory.T.exists_expandsAt_section_uniformised R hB D A G U hG (N * k) hNk (F s)
  refine ⟨σ, fun e i i' => m e i i' ^ k, fun e s i i' => ?_, y, hy1, fun i i' hyW => ?_⟩
  · exact hU R _ D A G U.toUnifPre e (N * k) (σ s) (F s).f i' _ inf_le_right _ (hσ s e) (hF s e i i')
  · show y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i' ^ k)
    have hk0 : 0 < k := by omega
    first
      | (rw [Scheme.basicOpen_pow _ _ hk0]; exact hy2 i i' hyW)
      | (rw [Scheme.basicOpen_pow _ hk0]; exact hy2 i i' hyW)
      | (rw [Scheme.basicOpen_pow _ _ _ hk0]; exact hy2 i i' hyW)
      | (simpa [Scheme.basicOpen_pow, hk0] using hy2 i i' hyW)

end GlobalTheory.MumMult
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordSectionsMultiplierThickeningsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumfordSections_multiplier_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, 3 ≤ k → ∃ S : H0 U.LG.L k → H0 U.LG.L (N * k), ∃ c : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i'), (∀ (e : ℕ) (s : H0 U.LG.L k) (i i' : Fin 1 → U.LG.L.ι), ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_right : ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i' ≤ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i')).op).hom (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((S s).f i')) = c e i i' * ((thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE (inf_le_left : ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i' ≤ ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom ((((b e).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s.f i))) ∧ ∃ y : (thickObj R (maximalIdeal R) 0 G).left, (∃ i' : Fin 1 → U.LG.L.ι, y ∈ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i') ∧ ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓ (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' → y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (c 0 i i') := by
  first | exact @GlobalTheory.MumMult.main | exact GlobalTheory.MumMult.main | (intros; apply GlobalTheory.MumMult.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordThickeningEndomorphismMapsSections

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumSec

def zeroSec {X : Scheme.{0}} (L : LB X) : LB.Sec L where
  f := fun _ => 0
  compat := fun _ _ => by simp

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∃ S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) ∧ (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb
  obtain ⟨N, hN, hP⟩ := GlobalTheory.T.mumfordSections_multiplier_thickenings R hB D A G hG U a a' h h' hE b hb
  classical
  let S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k) := fun k =>
    if hk : 3 ≤ k then (hP k hk).choose else fun _ => zeroSec _
  refine ⟨N, hN, S, ?_, ?_⟩
  · intro k e s₁ s₂ i i'
    by_cases hk : 3 ≤ k
    · obtain ⟨c, hc, -⟩ := (hP k hk).choose_spec
      have e1 := hc e s₁ i i'
      have e2 := hc e s₂ i i'
      have hS : S k = (hP k hk).choose := dif_pos hk
      rw [hS, e1, e2]
      ring
    · have hS : S k = fun _ => zeroSec _ := dif_neg hk
      rw [hS]
      dsimp only [zeroSec]
      erw [map_zero, map_zero]
      simp only [map_zero, mul_zero]
  · intro k hk
    obtain ⟨c, hc, y, ⟨i', hi'⟩, hy⟩ := (hP k hk).choose_spec
    obtain ⟨s₀, i, hs⟩ := GlobalTheory.T.exists_section_nonvanishing_closedFibre_of_three_le R hB D A G hG U k hk ((b 0).left.base y)
    have hu : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
        ((((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left).app (secChart U.LG.L i)).hom (s₀.f i)) := by
      have h1 : y ∈ (b 0).left ⁻¹ᵁ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
          (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s₀.f i)) := hs
      rw [Scheme.preimage_basicOpen] at h1
      exact h1
    have hyW : y ∈ ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓
        (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' :=
      ⟨Scheme.basicOpen_le _ _ hu, hi'⟩
    have hS : S k = (hP k hk).choose := dif_pos hk
    refine ⟨s₀, y, i, i', hu, ?_⟩
    rw [hS]
    have key := hc 0 s₀ i i'
    have hprod : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (c 0 i i' *
        ((thickObj R (maximalIdeal R) 0 G).left.presheaf.map (homOfLE (inf_le_left :
          ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i ⊓
            (fstG (maximalIdeal R) 0 G).left ⁻¹ᵁ secChart U.LG.L i' ≤
            ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom
          ((((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left).app (secChart U.LG.L i)).hom (s₀.f i))) := by
      rw [Scheme.basicOpen_mul, Scheme.basicOpen_res]
      exact ⟨hy i i' hyW, hyW, hu⟩
    rw [← key, Scheme.basicOpen_res] at hprod
    exact hprod.2

end GlobalTheory.MumSec
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordThickeningEndomorphismMapsSectionsStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.mumford_thickening_endomorphism_maps_sections : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∃ N : ℕ, 1 ≤ N ∧ ∃ S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) ∧ (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) := by
  first | exact @GlobalTheory.MumSec.main | exact GlobalTheory.MumSec.main | (intros; apply GlobalTheory.MumSec.main <;> assumption)
end
end
