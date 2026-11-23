module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapsAtExpLeB
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianSchemeCubicalBundleExistsAndMaps
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalIsoTranslatedBundleLevelComparisonStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoUniformisationTranslateOrderTwo
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTranslateTorsion

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRatioTranslationTwistIsos

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumCmp.TwRatio

theorem exists_ratio_gen {X A : Scheme.{0}} {M : LB X} {L₀ : LB A} (hM : M.IsLB) (hL₀ : L₀.IsLB)
    {K : Type} [Fintype K] (φ : K → (A ⟶ X)) (ε : K → ℤ) (F : A ⟶ X)
    (w : LB.Iso L₀ (LB.LinComb M φ ε)) (hw : w.IsGen) (W : LB.Iso L₀ (M.pull F)) (hW : W.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb M (Sum.elim φ (fun _ : PUnit => F)) (Sum.elim ε (fun _ => -1))), τ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (J : (Z ⟶ X) → M.ι) (j' : L₀.ι), Good M z J → r z ∈ L₀.U j' →
        val τ r z J = gv w r z (fun k => J (r ≫ φ k)) j' * (gw W r z (J (r ≫ F)) j')⁻¹ := by
  classical
  have pW := (isGen_iff W).1 hW
  have l1 : ∀ (j : K ⊕ PUnit → M.ι) k, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤
      (LB.LinComb M φ ε).U (j ∘ Sum.inl) ⊓ L₀.U k := fun j k y hy =>
    ⟨Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy.1 (Sum.inl i), hy.2⟩
  have l2 : ∀ (j : K ⊕ PUnit → M.ι) k, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤
      (M.pull F).U (fun _ => j (Sum.inr PUnit.unit)) ⊓ L₀.U k := fun j k y hy =>
    ⟨Set.mem_iInter.2 fun _ => Set.mem_iInter.1 hy.1 (Sum.inr PUnit.unit), hy.2⟩
  let u : ∀ (j : K ⊕ PUnit → M.ι) k, Γ(A, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k)ˣ := fun j k =>
    res (l1 j k) (w.s (j ∘ Sum.inl, k)) * (res (l2 j k) (W.s (fun _ => j (Sum.inr PUnit.unit), k)))⁻¹
  have hu : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) j k, r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k →
      gm r z _ (u j k) = gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ :=
    fun Z r z j k hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _)
      ((map_inv _ _).trans (congrArg _ (gm_res r z _ hz _))))
  have rel : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) (j j' : K ⊕ PUnit → M.ι) (k k' : L₀.ι),
      r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j → r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j' →
      r z ∈ L₀.U k → r z ∈ L₀.U k' →
      gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ =
        trF (Sum.elim φ (fun _ : PUnit => F)) (Sum.elim ε (fun _ => -1)) r z j j' *
          (gv w r z (j' ∘ Sum.inl) k' * (gw W r z (j' (Sum.inr PUnit.unit)) k')⁻¹) := by
    intro Z r z j j' k k' hj hj' hk hk'
    have key : ∀ {G : Type} [CommGroup G] (a c d x y : G), a * c⁻¹ * x * (d * c⁻¹ * y)⁻¹ = a * d⁻¹ * (x * y⁻¹) :=
      fun a c d x y => by
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
    have a₁ : r z ∈ (LB.LinComb M φ ε).U (j ∘ Sum.inl) := Set.mem_iInter.2 fun i => Set.mem_iInter.1 hj (Sum.inl i)
    have a₂ : r z ∈ (LB.LinComb M φ ε).U (j' ∘ Sum.inl) := Set.mem_iInter.2 fun i => Set.mem_iInter.1 hj' (Sum.inl i)
    have b₁ : F (r z) ∈ M.U (j (Sum.inr PUnit.unit)) := Set.mem_iInter.1 hj (Sum.inr PUnit.unit)
    have b₂ : F (r z) ∈ M.U (j' (Sum.inr PUnit.unit)) := Set.mem_iInter.1 hj' (Sum.inr PUnit.unit)
    have e := gm_linComb M φ ε r z _ _ a₁ a₂
    rw [gm_isGen hw r z _ _ k k' a₁ a₂ hk hk', pW Z r z _ _ k k' b₁ b₂ hk hk']
    erw [e]
    rw [trF, Fintype.prod_sum_type]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, zpow_neg, zpow_one]
    exact key _ _ _ _ _
  have glue : ∀ j : K ⊕ PUnit → M.ι, ∃ s : Γ(A, LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j)ˣ,
      ∀ k, res (inf_le_left : LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k ≤ _) s = u j k := fun j =>
    glue_unit _ (fun k => LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j ⊓ L₀.U k) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨k, hk⟩ := exists_chart hL₀ y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hy, hk⟩) (u j)
      (fun k k' y hy => by
        rw [hu _ _ y j k hy.1, hu _ _ y j k' hy.2, rel _ (𝟙 A) y j j k k' hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hM _ _ (𝟙 A) y hy.1.1, _root_.one_mul])
  choose s hs using glue
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ A) (z : Z) j k, r z ∈ LB.wchart M (Sum.elim φ (fun _ : PUnit => F)) j →
      r z ∈ L₀.U k → gm r z _ (s j) = gv w r z (j ∘ Sum.inl) k * (gw W r z (j (Sum.inr PUnit.unit)) k)⁻¹ :=
    fun Z r z j k hj hk => (gm_res r z _ (show r z ∈ _ ⊓ L₀.U k from ⟨hj, hk⟩) (s j)).symm.trans
      ((congrArg (gm r z _) (hs j k)).trans (hu Z r z j k ⟨hj, hk⟩))
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z J j' hJ hj' => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL₀ y
    exact (hv _ (𝟙 A) y j k hj hk).trans ((rel _ (𝟙 A) y j j' k k hj hj' hk hk).trans
      (congrArg _ (hv _ (𝟙 A) y j' k hj' hk).symm))
  · exact hv Z r z _ j' (hJ.mem _ r) hj'

end GlobalTheory.MumCmp.TwRatio

namespace GlobalTheory.MumCmp.TwRatio

theorem exists_twist_ratio : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε)) (hw : w.IsGen)
    (W : LB.Iso D₀.P.L (D.P.L.pull (GlobalTheory.MumCmp.twφ D₀ D β b 0))) (hW : W.IsGen),
    ∃ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D₀.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (j' : D₀.P.L.ι),
        Geo.Tor.Good D.P.L z J → r z ∈ D₀.P.L.U j' →
        Geo.Tor.gv w r z (fun i => J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b i)) j' =
          Geo.Tor.gw W r z (J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b 0)) j' * Geo.Tor.val ν (r ≫ D₀.P.A.hom) z J := by
  intro R _ _ _ D₀ D β b w hw W hW
  classical
  obtain ⟨τ, hτ, vτ⟩ := exists_ratio_gen D.P.isLB D₀.P.isLB (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε
    (GlobalTheory.MumCmp.twφ D₀ D β b 0) w hw W hW
  obtain ⟨t₀, ht₀⟩ := DVR.exists_gen_of_local (V := R) D.P.L D.P.isLB (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]
  have hF : FormEq (Sum.elim (GlobalTheory.MumCmp.twφ D₀ D β b) (fun _ : PUnit => GlobalTheory.MumCmp.twφ D₀ D β b 0))
      (Sum.elim GlobalTheory.MumCmp.twε (fun _ => -1))
      (fun k => D₀.P.A.hom ≫ (![b.left, η[D.P.A].left] : Fin 2 → ((𝟙_ (Over (Sp R))).left ⟶ D.P.A.left)) k)
      ![-1, 1] := by
    intro U _ h
    have e1 : GlobalTheory.MumCmp.twφ D₀ D β b 1 = D₀.P.A.hom ≫ b.left := rfl
    have e2 : GlobalTheory.MumCmp.twφ D₀ D β b 2 = D₀.P.A.hom ≫ η[D.P.A].left := rfl
    rw [Fintype.prod_sum_type, Fin.prod_univ_three, Fin.prod_univ_two]
    simp only [Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr, e1, e2, GlobalTheory.MumCmp.twε, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zpow_neg, zpow_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨τ', hτ', vτ'⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen D.P.isLB hF τ hτ
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio D.P.isLB hτ' (DVR.pullGen_isGen _ _ _ t₀ ht₀ D₀.P.A.hom)
  have hG := GlobalTheory.globalFns_holds _ D₀.P.A D₀.P.isAb
  obtain ⟨c, hc⟩ := hG.2 a.val
  obtain ⟨c', hc'⟩ := hG.2 (a⁻¹).val
  have hcc : c * c' = 1 := hG.1 (by rw [map_mul, hc, hc', Units.mul_inv, map_one])
  let cu : Γ(Sp R, ⊤)ˣ := ⟨c, c', hcc, (mul_comm c' c).trans hcc⟩
  have hcu : pullU D₀.P.A.hom ⊤ cu = a := Units.ext hc
  obtain ⟨ν, hν, vν⟩ := GlobalTheory.TorsionTranslate.exists_scale t₀ ht₀ cu
  refine ⟨ν, hν, fun Z r z J j' hJ hj' => ?_⟩
  have e1 := vτ Z r z J j' hJ hj'
  have e2 := vτ' Z r z J hJ
  have e3 := ha Z r z J hJ
  have e4 := val_pull hJ t₀ D₀.P.A.hom r
  have e5 := vν Z (r ≫ D₀.P.A.hom) z J hJ
  have e6 : gm r z ⊤ a = gm (r ≫ D₀.P.A.hom) z ⊤ cu := by
    rw [← hcu]; exact gm_pull r D₀.P.A.hom z ⊤ trivial cu
  rw [e5, ← e6, ← e4, ← e3, e2, e1, mul_left_comm, mul_inv_cancel, _root_.mul_one]

end GlobalTheory.MumCmp.TwRatio
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRatioTranslationTwistIsosStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_generator_ratio_translationTwist_isos : ∀ {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D₀ D : DegPre R) (β : D₀.P.A ⟶ D.P.A) (b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (w : LB.Iso D₀.P.L (LB.LinComb D.P.L (GlobalTheory.MumCmp.twφ D₀ D β b) GlobalTheory.MumCmp.twε)) (hw : w.IsGen)
    (W : LB.Iso D₀.P.L (D.P.L.pull (GlobalTheory.MumCmp.twφ D₀ D β b 0))) (hW : W.IsGen),
    ∃ ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![b.left, η[D.P.A].left] ![-1, 1]), ν.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ D₀.P.A.left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) (j' : D₀.P.L.ι),
        Geo.Tor.Good D.P.L z J → r z ∈ D₀.P.L.U j' →
        Geo.Tor.gv w r z (fun i => J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b i)) j' =
          Geo.Tor.gw W r z (J (r ≫ GlobalTheory.MumCmp.twφ D₀ D β b 0)) j' * Geo.Tor.val ν (r ≫ D₀.P.A.hom) z J := by
  first | exact @GlobalTheory.MumCmp.TwRatio.exists_twist_ratio | exact GlobalTheory.MumCmp.TwRatio.exists_twist_ratio | (intros; apply GlobalTheory.MumCmp.TwRatio.exists_twist_ratio <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompPG

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp.LevelCmp

theorem lift_comp_pG {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal R) D A G) (a : 𝟙_ (Over (Sp R)) ⟶ G) (b : 𝟙_ (Over (Sp R)) ⟶ D.toPre.P.A)
    (hab : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ b.left)
    {A₂ : PolAV (Sp (FractionRing R))} {D₂ : DegData R (maximalIdeal R)} (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (β : D₂.toPre.P.A ≅ D.toPre.P.A) (hβ : ∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left)
    (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left) (hh' : h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left) :
    h ≫ (U.gt e).pG.left = (U₂.gt e).pG.left ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom b 0 := by
  classical
  haveI := GlobalTheory.TorsionTranslate.mono_fst (I := maximalIdeal R) e G
  have hs : (thick R (maximalIdeal R) e ≫ a.left) ≫ G.hom = 𝟙 (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, Over.w a]; simp
  let ae : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))))) ⟶ thickObj R (maximalIdeal R) e G :=
    Over.homMk (pullback.lift (thick R (maximalIdeal R) e ≫ a.left) (𝟙 (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))))).left) hs) (pullback.lift_snd _ _ _)
  have hae : ae.left ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left := pullback.lift_fst _ _ _
  have heq : h = (GlobalTheory.MumCmp.Transl.tr ae).left :=
    (cancel_mono (fstG (maximalIdeal R) e G).left).1 (by rw [hh', GlobalTheory.MumCmp.Transl.tr_fst hae])
  have h₁ := GlobalTheory.TorusCoord.im_mul (U.gt e) (toUnit (thickObj R (maximalIdeal R) e G) ≫ ae) (𝟙 (thickObj R (maximalIdeal R) e G))
  have h₂ : GlobalTheory.TorusCoord.im (U.gt e) (toUnit (thickObj R (maximalIdeal R) e G) ≫ ae) = toUnit _ ≫ b := by
    ext
    have := hab e ae.left (Over.w ae) hae
    simp [GlobalTheory.TorusCoord.im] at this ⊢
    rw [this]
  have h₃ : GlobalTheory.TorusCoord.im (U.gt e) (𝟙 (thickObj R (maximalIdeal R) e G)) = (U₂.gt e).pG ≫ β.hom := by
    ext
    have := (hβ e).symm
    simp [GlobalTheory.TorusCoord.im] at this ⊢
    exact this
  have h₅ : GlobalTheory.TorusCoord.im (U.gt e) (GlobalTheory.MumCmp.Transl.tr ae) = (U₂.gt e).pG ≫ (β.hom * (toUnit D₂.toPre.P.A ≫ b)) := by
    rw [GlobalTheory.MumCmp.Transl.tr, h₁, h₂, h₃, comp_mul, comp_toUnit_assoc, mul_comm]
  rw [heq]
  exact congrArg Over.Hom.left h₅

end GlobalTheory.MumCmp.LevelCmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelComparisonGeneratorOfUniformisation

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumCmp.LevelCmp

theorem exists_level_gen : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∃ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1]), ν.IsGen ∧ ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG (maximalIdeal R) e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  intro R _ _ _ hR D A G _ _ hG U g hg a ha hab A₂ D₂ U₂ wL hwL β hβm hβ w hw
  have hab' : ∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left :=
    fun e ae h1 h2 => (hab e ae h1 h2).1
  obtain ⟨W, hW, HW⟩ := GlobalTheory.T.exists_global_iso_translated_bundle_levelComparison hR hG U a ha g.b hab' U₂ wL hwL β hβ
  obtain ⟨ν, hν, Hν⟩ := GlobalTheory.T.exists_generator_ratio_translationTwist_isos D₂.toPre D.toPre β.hom g.b w hw W hW
  refine ⟨ν, hν, ?_⟩
  intro e h hh hh' Z r z J J' N N' hJ hJ' hN hN'
  have k0 := lift_comp_pG U a g.b hab' U₂ β hβ e h hh'
  have hm : r ≫ h ≫ (U.gt e).pG.left = (r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0 := by
    rw [k0, Category.assoc]
  have hf : r ≫ h ≫ (fstG (maximalIdeal R) e G).left = r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left := by
    rw [hh']
  have hs : (r ≫ (U₂.gt e).pG.left) ≫ D₂.toPre.P.A.hom = r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e := by
    rw [Category.assoc, Over.w]; rfl
  have k2 := Hν Z (r ≫ (U₂.gt e).pG.left) z J (J' (r ≫ (U₂.gt e).pG.left)) hJ (hJ' _)
  have m1 : (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U (J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b 0)) := by
    have m1' : (U.gt e).pG.left (h (r z)) ∈ D.toPre.P.L.U (J (r ≫ h ≫ (U.gt e).pG.left)) := by
      simpa using hJ (r ≫ h ≫ (U.gt e).pG.left)
    rw [hm] at m1'
    exact m1'
  have m2 : (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U (J' (r ≫ (U₂.gt e).pG.left)) := by
    simpa using hJ' (r ≫ (U₂.gt e).pG.left)
  have m3 : ((toUnit G ≫ a) * 𝟙 G).left ((fstG (maximalIdeal R) e G).left (r z)) ∈ U.LG.L.U (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) := by
    simpa using hN (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)
  have m4 : (fstG (maximalIdeal R) e G).left (r z) ∈ U₂.LG.L.U (N' (r ≫ (fstG (maximalIdeal R) e G).left)) := by
    simpa using hN' (r ≫ (fstG (maximalIdeal R) e G).left)
  have k1 := HW e h hh hh' Z r z _ _ _ _ m1 m2 m3 m4
  rw [k2, hs, mul_right_comm, k1, hm, hf]

end GlobalTheory.MumCmp.LevelCmp
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelComparisonGeneratorOfUniformisationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_levelComparison_generator_of_uniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (g : GtPt D.toPre (𝟙_ (Over (Sp R)))), (∃ z : GtPt D.toPre (𝟙_ (Over (Sp R))), z.IsZero ∧ GtPt.IsAdd g g z) → ∀ a : 𝟙_ (Over (Sp R)) ⟶ G, a ^ 2 = 1 → (∀ (e : ℕ) (ae : Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1))) ⟶ (thickObj R (maximalIdeal R) e G).left), ae ≫ (thickObj R (maximalIdeal R) e G).hom = 𝟙 _ → ae ≫ (fstG (maximalIdeal R) e G).left = thick R (maximalIdeal R) e ≫ a.left → ae ≫ (U.gt e).pG.left = thick R (maximalIdeal R) e ≫ g.b.left ∧ ∀ χ : D.toPre.X, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ae) (LB.pullGen D.toPre.P.L _ _ (g.s χ) (thick R (maximalIdeal R) e))) → ∀ (A₂ : PolAV (Sp (FractionRing R))) (D₂ : DegData R (maximalIdeal R)) (U₂ : Unif (maximalIdeal R) D₂ A₂ G) (wL : LB.Iso U₂.LG.L (U.LG.L.pull ((toUnit G ≫ a) * 𝟙 G).left)), wL.IsGen → ∀ β : D₂.toPre.P.A ≅ D.toPre.P.A, IsMonHom β.hom → (∀ e : ℕ, (U₂.gt e).pG.left ≫ β.hom.left = (U.gt e).pG.left) → ∀ w : LB.Iso D₂.toPre.P.L (LB.LinComb D.toPre.P.L (GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b) GlobalTheory.MumCmp.twε), w.IsGen → ∃ ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![g.b.left, η[D.toPre.P.A].left] ![-1, 1]), ν.IsGen ∧ ∀ (e : ℕ) (h : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left), h ≫ (thickObj R (maximalIdeal R) e G).hom = (thickObj R (maximalIdeal R) e G).hom → h ≫ (fstG (maximalIdeal R) e G).left = (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left → ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D₂.toPre.P.A.left) → D₂.toPre.P.L.ι) (N : (Z ⟶ G.left) → U.LG.L.ι) (N' : (Z ⟶ G.left) → U₂.LG.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D₂.toPre.P.L z J' → Geo.Tor.Good U.LG.L z N → Geo.Tor.Good U₂.LG.L z N' → Geo.Tor.gv w (r ≫ (U₂.gt e).pG.left) z (fun i => J ((r ≫ (U₂.gt e).pG.left) ≫ GlobalTheory.MumCmp.twφ D₂.toPre D.toPre β.hom g.b i)) (J' (r ≫ (U₂.gt e).pG.left)) * Geo.Tor.gw (U₂.w e) r z (J' (r ≫ (U₂.gt e).pG.left)) (fun _ => N' (r ≫ (fstG (maximalIdeal R) e G).left)) = Geo.Tor.gw (U.w e) (r ≫ h) z (J (r ≫ h ≫ (U.gt e).pG.left)) (fun _ => N (r ≫ h ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.gw wL (r ≫ (fstG (maximalIdeal R) e G).left) z (N (r ≫ (fstG (maximalIdeal R) e G).left ≫ ((toUnit G ≫ a) * 𝟙 G).left)) (N' (r ≫ (fstG (maximalIdeal R) e G).left)) * Geo.Tor.val ν (r ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e) z J := by
  first | exact @GlobalTheory.MumCmp.LevelCmp.exists_level_gen | exact GlobalTheory.MumCmp.LevelCmp.exists_level_gen | (intros; apply GlobalTheory.MumCmp.LevelCmp.exists_level_gen <;> assumption)
end
end
