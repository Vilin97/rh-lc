module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLeFinrankLa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusIdempotentImageSiegel
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
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Data.Nat.Choose.Multinomial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageRelationOfPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackOfIdempotentImagesAndActionPullbacStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenLocusIdempotentImageSiegelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.exists_open_locus_idempotent_image_siegel : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (U : S'.Opens) (c : SiegPre h M (zetaAway M) (U.ι ≫ t)) (w : SiegPre h' M (zetaAway M) (U.ι ≫ t)) (actw : O → (w.A ⟶ w.A)), SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(U.toScheme, ⊤)) ∧ w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act U.ι ∧ ZRel e jl o κ c w actw ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)), IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w' : SiegPre h' M (zetaAway M) (g ≫ t)) (actw' : O → (w'.A ⟶ w'.A)), ActPB w' actw' z act g ∧ ZRel e jl o κ c' w' actw') → Set.range g.base ⊆ (U : Set S') := by
  first | (exact @GlobalTheory.IdemLocus.exists_open_locus) | (exact GlobalTheory.IdemLocus.exists_open_locus) | (intros; apply GlobalTheory.IdemLocus.exists_open_locus  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelAdjointActionPullback

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UPel.HT

theorem siegPre_actPB_pullback : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (bar : O → O)
    (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B) (f : S' ⟶ S) (z : SiegPre h M ζ s)
    (act : O → (z.A ⟶ z.A)), f ≫ s = s' → z.Principal → IsRAct z.A act → Adj z.A z.P bar act →
    ∃ (w : SiegPre h M ζ s') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧
      Adj w.A w.P bar actw ∧ ActPB w actw z act f := by
  intro h M B _ ζ O _ bar S S' s s' f z act hs hz hR hA
  obtain ⟨⟨w, φ, φ₂, hφ, hsq, hP, hlev⟩, hpr⟩ := GlobalTheory.siegPre_pullback h M B ζ S S' s s' f z hs
  have hwP : w.Principal := hpr w ⟨φ, φ₂, hφ, hsq, hP, hlev⟩ hz
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hφ (isGrpPullback_pullback z.A f)
  haveI := he
  have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  let actw : O → (w.A ⟶ w.A) := fun a => e.hom ≫ (Over.pullback f).map (act a) ≫ e.inv
  have hv : ∀ a, (actw a).left ≫ φ = φ ≫ (act a).left := fun a => by
    have hm : ((Over.pullback f).map (act a)).left ≫ pullback.fst z.A.hom f =
        pullback.fst z.A.hom f ≫ (act a).left := pullback.lift_fst _ _ _
    rw [← heφ]
    simp only [actw, Over.comp_left, Category.assoc]
    rw [reassoc_of% hie, hm]
  have hRw : IsRAct w.A actw := ActUnr.isRAct_conj e _ (ActUnr.isRAct_pullback f z.A act hR)
  have lf : ∀ {T : Scheme.{0}} {X Y : Over T} (x y : X ⟶ Y), (lift x y).left ≫ (fst Y Y).left = x.left :=
    fun x y => by rw [← Over.comp_left, lift_fst]
  have ls : ∀ {T : Scheme.{0}} {X Y : Over T} (x y : X ⟶ Y), (lift x y).left ≫ (snd Y Y).left = y.left :=
    fun x y => by rw [← Over.comp_left, lift_snd]
  have hc1 : ∀ a, (lift (fst w.A w.A ≫ actw a) (snd w.A w.A)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst z.A z.A ≫ act a) (snd z.A z.A)).left := fun a => by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, hsq.1, ← Category.assoc, lf, Category.assoc, lf, Over.comp_left _ _ _ (fst w.A w.A) (actw a),
        Over.comp_left _ _ _ (fst z.A z.A) (act a), Category.assoc, hv, ← Category.assoc, ← hsq.1, Category.assoc]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ls, Category.assoc, ls, hsq.2]
  have hc2 : ∀ a, (lift (fst w.A w.A) (snd w.A w.A ≫ actw (bar a))).left ≫ φ₂ =
      φ₂ ≫ (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar a))).left := fun a => by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, hsq.1, ← Category.assoc, lf, Category.assoc, lf, hsq.1]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ls, Category.assoc, ls, Over.comp_left _ _ _ (snd w.A w.A) (actw (bar a)),
        Over.comp_left _ _ _ (snd z.A z.A) (act (bar a)), Category.assoc, hv, ← Category.assoc, ← hsq.2, Category.assoc]
  have hadj : Adj w.A w.P bar actw := fun a => by
    have h1 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP _ (hc1 a).symm
    have h2 := GlobalTheory.GenSpread.lbIso_pull_comp (L := z.P) (M := z.P) φ₂ rfl rfl (hA a)
    have h3 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP _ (hc2 a).symm
    exact LBIso.trans (pull_isLB w.isLB _) (pull_isLB z.isLB _) (pull_isLB w.isLB _)
      (LBIso.trans (pull_isLB w.isLB _) (pull_isLB z.isLB _) (pull_isLB z.isLB _) h1 h2) h3.symm
  exact ⟨w, actw, hwP, hRw, hadj, φ, φ₂, hφ, hsq, hP, hlev, hv⟩

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalSiegelAdjointActionPullbackStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.exists_principal_siegel_adjoint_action_pullback : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (bar : O → O) (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B) (f : S' ⟶ S) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)), f ≫ s = s' → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → ∃ (w : SiegPre h M ζ s') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act f := by
  first | (exact @GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (exact GlobalTheory.UPel.HT.siegPre_actPB_pullback) | (intros; apply GlobalTheory.UPel.HT.siegPre_actPB_pullback  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackWithActionCancellation

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem actPB_cancel : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (S S₁ S₂ : Scheme.{0})
    (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)) (g₁ : S₁ ⟶ S)
    (y : S₂ ⟶ S₁) (w₁ : SiegPre h M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (w₂ : SiegPre h M ζ s₂)
    (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₁ act₁ z act g₁ → ActPB w₂ act₂ z act (y ≫ g₁) → ActPB w₂ act₂ w₁ act₁ y := by
  intro h M B _ ζ O _ S S₁ S₂ s s₁ s₂ z act g₁ y w₁ act₁ w₂ act₂ m₁ m₂
  obtain ⟨φ₁, φ₁₂, h1, s1, p1, l1, a1⟩ := m₁
  obtain ⟨φ₂, φ₂₂, h2, s2, p2, l2, a2⟩ := m₂
  have hw : φ₂ ≫ z.A.hom = (w₂.A.hom ≫ y) ≫ g₁ := by rw [h2.1.w, Category.assoc]
  let ψ : w₂.A.left ⟶ w₁.A.left := h1.1.lift φ₂ (w₂.A.hom ≫ y) hw
  have hψ₁ : ψ ≫ φ₁ = φ₂ := h1.1.lift_fst _ _ _
  have hψ : ψ ≫ w₁.A.hom = w₂.A.hom ≫ y := h1.1.lift_snd _ _ _
  let ψ₂ : (G2 w₂.A).left ⟶ (G2 w₁.A).left := ActUnr.sqMap hψ
  have sψ : IsSquare ψ ψ₂ := ⟨ActUnr.sqMap_fst hψ, ActUnr.sqMap_snd hψ⟩
  have e₂ : φ₂₂ = ψ₂ ≫ φ₁₂ := by
    apply ActUnr.left_hom_ext
    · rw [s2.1, Category.assoc, s1.1, ← Category.assoc, sψ.1, Category.assoc, hψ₁]
    · rw [s2.2, Category.assoc, s1.2, ← Category.assoc, sψ.2, Category.assoc, hψ₁]
  have n : IsGrpPullback w₂.A z.A (y ≫ g₁) (ψ ≫ φ₁) := by rw [hψ₁]; exact h2
  refine ⟨ψ, ψ₂, IsGrpPullback.cancel h1 n hψ, sψ, ?_, fun a => ?_, fun o => ?_⟩
  · refine LBIso.trans w₂.isLB (pull_isLB z.isLB _) (pull_isLB w₁.isLB _) p2 ?_
    refine LBIso.trans (pull_isLB z.isLB _) (pull_isLB (pull_isLB z.isLB _) _) (pull_isLB w₁.isLB _)
      (GlobalTheory.GenSpread.lbIso_pull_pull z.isLB ψ₂ e₂) ?_
    exact GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm p1) ψ₂
  · apply h1.1.hom_ext
    · rw [Category.assoc, hψ₁, l2 a, Category.assoc, Category.assoc, l1 a]
    · rw [Category.assoc, hψ, ← Category.assoc, Over.w (w₂.lev a), Category.assoc, Over.w (w₁.lev a)]
      simp
  · apply h1.1.hom_ext
    · rw [Category.assoc, hψ₁, a2 o, Category.assoc, a1 o, ← Category.assoc, hψ₁]
    · rw [Category.assoc, hψ, ← Category.assoc, Over.w (act₂ o), Category.assoc, Over.w (act₁ o), hψ]

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPullbackWithActionCancellationStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.siegel_pullback_with_action_cancellation : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (S S₁ S₂ : Scheme.{0}) (s : S ⟶ Sp B) (s₁ : S₁ ⟶ Sp B) (s₂ : S₂ ⟶ Sp B) (z : SiegPre h M ζ s) (act : O → (z.A ⟶ z.A)) (g₁ : S₁ ⟶ S) (y : S₂ ⟶ S₁) (w₁ : SiegPre h M ζ s₁) (act₁ : O → (w₁.A ⟶ w₁.A)) (w₂ : SiegPre h M ζ s₂) (act₂ : O → (w₂.A ⟶ w₂.A)), ActPB w₁ act₁ z act g₁ → ActPB w₂ act₂ z act (y ≫ g₁) → ActPB w₂ act₂ w₁ act₁ y := by
  first | exact @GlobalTheory.UPel.HT.actPB_cancel | exact GlobalTheory.UPel.HT.actPB_cancel | (intros; apply GlobalTheory.UPel.HT.actPB_cancel <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyIdempotentImageOpenLocus

section

@[expose] public section

noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem idemImage_locus : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (Y : Scheme.{0}) (j : Y ⟶ S') (c : SiegPre h M (zetaAway M) (j ≫ t)), IsImmersion j ∧ QuasiCompact j ∧ SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(Y, ⊤)) ∧ (∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (y : T ⟶ Y) (c' : SiegPre h M (zetaAway M) t'), y ≫ j ≫ t = t' → SiegPB c' c y → ∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act (y ≫ j) ∧ ZRel e jl o κ c' w actw) ∧ ∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) t'), g ≫ t = t' → IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), ActPB w actw z act g ∧ ZRel e jl o κ c' w actw) → ∃! y : T ⟶ Y, y ≫ j = g ∧ SiegPB c' c y := by
  intro h h' M d O _ bar e jl n o κ S' _ t z act hh hM hodd hd hcop hpr hra hadj hee
  obtain ⟨U, c, wU, actU, hker, hunit, hwp, hwr, hwa, hwpb, hrel, hrange⟩ :=
    GlobalTheory.T.exists_open_locus_idempotent_image_siegel h h' M d O bar e jl n o κ S' t z act hh hM hodd hd hcop hpr hra hadj hee
  refine ⟨U.toScheme, U.ι, c, inferInstance, inferInstance, hker, hunit, ?_, ?_⟩
  · intro T t' y c' hyt hc'
    obtain ⟨w₂, act₂, hp₂, hr₂, ha₂, hpb₂⟩ :=
      GlobalTheory.T.exists_principal_siegel_adjoint_action_pullback h' M (cycAway M) (zetaAway M) O bar U.toScheme T (U.ι ≫ t) t' y wU actU hyt hwp hwr hwa
    exact ⟨w₂, act₂, hp₂, hr₂, ha₂, hpb₂.trans hwpb,
      GlobalTheory.T.idempotent_image_relation_of_pullback h h' M (cycAway M) (zetaAway M) O e jl n o κ U.toScheme T (U.ι ≫ t) t' y c wU actU c' w₂ act₂ hpb₂ hc' hrel⟩
  · intro T t' g c' hgt hdu hc' hex
    subst hgt
    have hr : Set.range g.base ⊆ (U : Set S') := hrange T g c' hdu hc' hex
    let y : T ⟶ U.toScheme := IsOpenImmersion.lift U.ι g (by rw [Scheme.Opens.range_ι]; exact hr)
    have hy : y ≫ U.ι = g := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨w', actw', hpb', hrel'⟩ := hex
    refine ⟨y, ⟨hy, ?_⟩, ?_⟩
    · have hpb'' : ActPB w' actw' z act (y ≫ U.ι) := by rw [hy]; exact hpb'
      exact GlobalTheory.T.siegel_pullback_of_idempotent_images_and_action_pullback h h' M (cycAway M) (zetaAway M) O e jl n o κ U.toScheme T (U.ι ≫ t) (g ≫ t) y c wU actU c' w' actw'
        (GlobalTheory.T.siegel_pullback_with_action_cancellation h' M (cycAway M) (zetaAway M) O S' U.toScheme T t (U.ι ≫ t) (g ≫ t) z act U.ι y wU actU w' actw' hwpb hpb'')
        hrel hrel'
    · rintro y' ⟨hy', -⟩
      exact (cancel_mono U.ι).1 (hy'.trans hy.symm)

end GlobalTheory.UPel.HT
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilyIdempotentImageOpenLocusStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

theorem _root_.GlobalTheory.T.siegel_family_idempotent_image_open_locus : ∀ (h h' M d : ℕ) (O : Type) [Ring O] (bar : O → O) (e : O) (jl : (Fin h ⊕ Fin h → ℤ) →+ (Fin h' ⊕ Fin h' → ℤ)) (n : ℕ) (o : Fin n → O) (κ : Fin n → (Fin h' ⊕ Fin h' → ℤ) →+ (Fin h ⊕ Fin h → ℤ)) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (z : SiegPre h' M (zetaAway M) t) (act : O → (z.A ⟶ z.A)), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d → z.Principal → IsRAct z.A act → Adj z.A z.P bar act → e * e = e → ∃ (Y : Scheme.{0}) (j : Y ⟶ S') (c : SiegPre h M (zetaAway M) (j ≫ t)), IsImmersion j ∧ QuasiCompact j ∧ SiegKerBy c d ∧ IsUnit ((d : ℕ) : Γ(Y, ⊤)) ∧ (∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (y : T ⟶ Y) (c' : SiegPre h M (zetaAway M) t'), y ≫ j ≫ t = t' → SiegPB c' c y → ∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧ Adj w.A w.P bar actw ∧ ActPB w actw z act (y ≫ j) ∧ ZRel e jl o κ c' w actw) ∧ ∀ (T : Scheme.{0}) (t' : T ⟶ Sp (cycAway M)) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) t'), g ≫ t = t' → IsUnit ((d : ℕ) : Γ(T, ⊤)) → SiegKerBy c' d → (∃ (w : SiegPre h' M (zetaAway M) t') (actw : O → (w.A ⟶ w.A)), ActPB w actw z act g ∧ ZRel e jl o κ c' w actw) → ∃! y : T ⟶ Y, y ≫ j = g ∧ SiegPB c' c y := by
  first | (exact @GlobalTheory.UPel.HT.idemImage_locus) | (exact GlobalTheory.UPel.HT.idemImage_locus) | (intros; apply GlobalTheory.UPel.HT.idemImage_locus  <;> assumption)
end
end
